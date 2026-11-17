import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { run } from '../src/cli';
import { TypesWriter } from '../src/writer';
import type { UsageInfo } from '../src/types';

/**
 * A run whose output differs from the files on disk only in the
 * `generatedAt` stamps writes nothing; any other difference rewrites every
 * file, all with fresh stamps (consumers compare stamps across files).
 */
describe('Unchanged output is not rewritten', () => {
	const snapshot = (dir: string): Map<string, string> => {
		const files = new Map<string, string>();
		for (const name of fs.readdirSync(dir).sort()) {
			files.set(name, fs.readFileSync(path.join(dir, name), 'utf-8'));
		}
		const result = files;
		return result;
	};

	const stampOf = (content: string): string | undefined => {
		const match = /^ {2}"generatedAt": "([^"]*)"/m.exec(content);
		const stamp = match ? match[ 1 ] : undefined;
		return stamp;
	};

	describe('TypesWriter run', () => {
		let outputDir: string;

		beforeEach(() => {
			outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-unchanged-writer-'));
		});

		afterEach(() => {
			fs.rmSync(outputDir, { recursive : true, force : true });
		});

		const usages = (location: string): Map<string, UsageInfo[]> => {
			const map = new Map<string, UsageInfo[]>([
				[ 'Widget', [ { location, kind : 'instantiation', code : 'new Widget()' } ] ],
			]);
			return map;
		};

		const writeRun = (writer: TypesWriter, location: string): boolean => {
			writer.begin();
			writer.writeUsagesFile(usages(location));
			writer.writeTo('hierarchy.txt', 'Widget\n');
			const written = writer.commit();
			return written;
		};

		it('writes a first run, skips an identical one, rewrites all files on a change', async () => {
			const writer = new TypesWriter(outputDir);
			expect(writeRun(writer, 'a.ts:1:1')).to.equal(true);
			const first = snapshot(outputDir);
			expect(Array.from(first.keys())).to.deep.equal([ 'hierarchy.txt', 'usages.json' ]);

			await new Promise(resolve => setTimeout(resolve, 5));
			expect(writeRun(writer, 'a.ts:1:1')).to.equal(false);
			expect(snapshot(outputDir)).to.deep.equal(first);

			await new Promise(resolve => setTimeout(resolve, 5));
			expect(writeRun(writer, 'a.ts:2:1')).to.equal(true);
			const changed = snapshot(outputDir);
			expect(changed.get('usages.json')).to.include('a.ts:2:1');
			expect(stampOf(changed.get('usages.json')!)).to.not.equal(stampOf(first.get('usages.json')!));
		});

		it('writes a run when a file of it is missing on disk', () => {
			const writer = new TypesWriter(outputDir);
			writeRun(writer, 'a.ts:1:1');
			fs.unlinkSync(path.join(outputDir, 'hierarchy.txt'));
			expect(writeRun(writer, 'a.ts:1:1')).to.equal(true);
			expect(fs.existsSync(path.join(outputDir, 'hierarchy.txt'))).to.equal(true);
		});

		it('writes at once outside a run', () => {
			const writer = new TypesWriter(outputDir);
			writer.writeTo('hierarchy.txt', 'Widget\n');
			expect(fs.readFileSync(path.join(outputDir, 'hierarchy.txt'), 'utf-8')).to.equal('Widget\n');
			// no run open, or an empty one: nothing to write, reported so
			expect(writer.commit()).to.equal(false);
			writer.begin();
			expect(writer.commit()).to.equal(false);
		});
	});

	describe('CLI', () => {
		it('leaves every file untouched when the project did not change', () => {
			const outputDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tactica-unchanged-cli-'));
			const project = path.join(__dirname, 'fixtures', 'usage-attribution', 'tsconfig.json');
			try {
				expect(run({ project, outputDir })).to.equal(0);
				const first = snapshot(outputDir);
				expect(stampOf(first.get('definitions.json')!)).to.be.a('string');

				expect(run({ project, outputDir })).to.equal(0);
				expect(snapshot(outputDir)).to.deep.equal(first);

				// any difference on disk rewrites the whole set, stamps included
				fs.writeFileSync(path.join(outputDir, 'hierarchy.txt'), 'tampered\n');
				expect(run({ project, outputDir })).to.equal(0);
				const rewritten = snapshot(outputDir);
				expect(rewritten.get('hierarchy.txt')).to.equal(first.get('hierarchy.txt'));
				expect(stampOf(rewritten.get('definitions.json')!))
					.to.not.equal(stampOf(first.get('definitions.json')!));
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		}).timeout(30000);
	});
});
