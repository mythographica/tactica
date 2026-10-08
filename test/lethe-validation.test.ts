'use strict';

// The lethe contract gate: tactica's fresh .tactica output must validate
// against the six @mnemonica/lethe tactica schemas (hierarchy, definitions,
// collections + the analysis files usages, flow, eds) shipped through the
// file:../lethe devDependency. A format drift fails this test instead of
// silently breaking every reader.
import { expect } from 'chai';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import Ajv2020 from 'ajv/dist/2020';
import { run } from '../src/cli';

const letheTacticaDir = path.join(
	__dirname, '..', 'node_modules', '@mnemonica', 'lethe', 'tactica'
);
const KINDS = [ 'hierarchy', 'definitions', 'collections', 'usages', 'flow', 'eds' ];

const compile = (kind: string) => {
	const schema = JSON.parse(
		fs.readFileSync(path.join(letheTacticaDir, `${kind}.schema.json`), 'utf-8')
	);
	const ajv = new Ajv2020({ allErrors : true, strict : true });
	const validate = ajv.compile(schema);
	return validate;
};

const fixtures = [ 'cli-collections', 'cli-eds' ];

describe('lethe schema validation of tactica output', () => {
	for (const fixture of fixtures) {
		it(`${fixture}: every emitted contract file validates against its lethe schema`, () => {
			const outputDir = fs.mkdtempSync(
				path.join(os.tmpdir(), `tactica-lethe-${fixture}-`)
			);
			try {
				run({
					project : path.join(__dirname, 'fixtures', fixture, 'tsconfig.json'),
					outputDir,
				});

				for (const kind of KINDS) {
					const file = path.join(outputDir, `${kind}.json`);
					if (!fs.existsSync(file)) {
						continue;
					}
					const validate = compile(kind);
					const data = JSON.parse(fs.readFileSync(file, 'utf-8'));
					const valid = validate(data);
					expect(valid, `${kind}.json: ${JSON.stringify(validate.errors)}`).to.be.true;
				}
			} finally {
				fs.rmSync(outputDir, { recursive : true, force : true });
			}
		});
	}

	it('emits format 1.1 with language "typescript" on every collection entry', () => {
		const outputDir = fs.mkdtempSync(
			path.join(os.tmpdir(), 'tactica-lethe-format-')
		);
		try {
			run({
				project : path.join(__dirname, 'fixtures', 'cli-collections', 'tsconfig.json'),
				outputDir,
			});

			const collections = JSON.parse(
				fs.readFileSync(path.join(outputDir, 'collections.json'), 'utf-8')
			);
			expect(collections.version).to.equal('1.1');
			expect(collections.collections.length).to.be.greaterThan(0);
			for (const entry of collections.collections) {
				expect(entry.language, `collection ${entry.name}`).to.equal('typescript');
			}

			for (const kind of [ 'hierarchy', 'definitions', 'usages', 'flow' ]) {
				const data = JSON.parse(
					fs.readFileSync(path.join(outputDir, `${kind}.json`), 'utf-8')
				);
				expect(data.version, `${kind}.json version`).to.equal('1.1');
			}
		} finally {
			fs.rmSync(outputDir, { recursive : true, force : true });
		}
	});
});
