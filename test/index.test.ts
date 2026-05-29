'use strict';

import { expect } from 'chai';
import * as tactica from '../src/index';

describe('index.ts public exports', () => {
	it('should export MnemonicaAnalyzer', () => {
		expect(tactica.MnemonicaAnalyzer).to.be.a('function');
	});

	it('should export TopologicaAnalyzer', () => {
		expect(tactica.TopologicaAnalyzer).to.be.a('function');
	});

	it('should export TypeGraphImpl', () => {
		expect(tactica.TypeGraphImpl).to.be.a('function');
	});

	it('should export TypesGenerator', () => {
		expect(tactica.TypesGenerator).to.be.a('function');
	});

	it('should export TypesWriter', () => {
		expect(tactica.TypesWriter).to.be.a('function');
	});

	it('should export CLI functions', () => {
		expect(tactica.parseArgs).to.be.a('function');
		expect(tactica.run).to.be.a('function');
		expect(tactica.watch).to.be.a('function');
		expect(tactica.main).to.be.a('function');
	});

	it('should export VERSION string', () => {
		expect(tactica.VERSION).to.be.a('string');
		expect(tactica.VERSION).to.match(/^\d+\.\d+\.\d+/);
	});
});
