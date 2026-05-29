'use strict';

import { expect } from 'chai';
import { parseArgs } from '../src/cli';

describe('parseArgs()', () => {
	it('should return empty options for empty args', () => {
		const opts = parseArgs([]);
		expect(opts).to.deep.equal({});
	});

	it('should parse --watch flag', () => {
		expect(parseArgs(['--watch']).watch).to.be.true;
		expect(parseArgs(['-w']).watch).to.be.true;
	});

	it('should parse --project flag', () => {
		const opts = parseArgs(['--project', './tsconfig.json']);
		expect(opts.project).to.equal('./tsconfig.json');
	});

	it('should parse -p shorthand for project', () => {
		const opts = parseArgs(['-p', './custom.tsconfig.json']);
		expect(opts.project).to.equal('./custom.tsconfig.json');
	});

	it('should parse --output flag', () => {
		const opts = parseArgs(['--output', '.out']);
		expect(opts.outputDir).to.equal('.out');
	});

	it('should parse -o shorthand for output', () => {
		const opts = parseArgs(['-o', './dist/types']);
		expect(opts.outputDir).to.equal('./dist/types');
	});

	it('should parse --include as comma-separated patterns', () => {
		const opts = parseArgs(['--include', 'src/**,lib/**']);
		expect(opts.include).to.deep.equal(['src/**', 'lib/**']);
	});

	it('should parse -i shorthand and accumulate multiple --include flags', () => {
		const opts = parseArgs(['-i', 'src/**', '-i', 'lib/**']);
		expect(opts.include).to.include('src/**');
		expect(opts.include).to.include('lib/**');
	});

	it('should parse --exclude flag', () => {
		const opts = parseArgs(['--exclude', 'node_modules/**,dist/**']);
		expect(opts.exclude).to.deep.equal(['node_modules/**', 'dist/**']);
	});

	it('should parse -e shorthand for exclude', () => {
		const opts = parseArgs(['-e', '**/*.spec.ts']);
		expect(opts.exclude).to.deep.equal(['**/*.spec.ts']);
	});

	it('should parse --module-augmentation as globalAugmentation:false', () => {
		const opts = parseArgs(['--module-augmentation']);
		expect(opts.globalAugmentation).to.be.false;
	});

	it('should parse -m shorthand for module-augmentation', () => {
		const opts = parseArgs(['-m']);
		expect(opts.globalAugmentation).to.be.false;
	});

	it('should parse --verbose flag', () => {
		expect(parseArgs(['--verbose']).verbose).to.be.true;
		expect(parseArgs(['-v']).verbose).to.be.true;
	});

	it('should parse --topologica as comma-separated dirs', () => {
		const opts = parseArgs(['--topologica', 'src/ai-types,src/types']);
		expect(opts.topologicaDirs).to.deep.equal(['src/ai-types', 'src/types']);
	});

	it('should parse -t shorthand for topologica', () => {
		const opts = parseArgs(['-t', 'ai-types']);
		expect(opts.topologicaDirs).to.deep.equal(['ai-types']);
	});

	it('should parse --esm flag', () => {
		expect(parseArgs(['--esm']).esm).to.be.true;
	});

	it('should parse --eds flag', () => {
		expect(parseArgs(['--eds']).eds).to.be.true;
	});

	it('should parse --no-eds flag', () => {
		expect(parseArgs(['--no-eds']).eds).to.be.false;
	});

	it('should parse --help flag', () => {
		expect(parseArgs(['--help']).help).to.be.true;
		expect(parseArgs(['-h']).help).to.be.true;
	});

	it('should parse multiple flags together', () => {
		const opts = parseArgs(['--watch', '--verbose', '--esm', '--output', '.out']);
		expect(opts.watch).to.be.true;
		expect(opts.verbose).to.be.true;
		expect(opts.esm).to.be.true;
		expect(opts.outputDir).to.equal('.out');
	});
});
