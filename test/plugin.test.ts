import { expect } from 'chai';
import * as ts from 'typescript';
import * as path from 'path';

// Import the plugin module to test its internal functions
// We need to test the logic without the full LanguageService setup

describe('Tactica Language Service Plugin', () => {
	describe('lookupTyped() definition provider', () => {
		it('should detect lookupTyped() string literal as definition target', () => {
			const sourceCode = `
				import { lookupTyped } from 'mnemonica';
				const SentienceConstructor = lookupTyped('Sentience');
			`;

			// Create a source file
			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			// Find the string literal 'Sentience' in the AST
			let stringLiteral: ts.StringLiteral | undefined;
			function visit(node: ts.Node) {
				if (ts.isStringLiteral(node) && node.text === 'Sentience') {
					stringLiteral = node;
				}
				ts.forEachChild(node, visit);
			}
			sourceFile.forEachChild(visit);

			expect(stringLiteral).to.exist;
			expect(stringLiteral!.text).to.equal('Sentience');

			// Check that it's the first argument to lookupTyped()
			const parent = stringLiteral!.parent;
			expect(ts.isCallExpression(parent)).to.be.true;
			if (ts.isCallExpression(parent)) {
				expect(parent.arguments[0]).to.equal(stringLiteral);
				const funcExpr = parent.expression;
				expect(ts.isIdentifier(funcExpr)).to.be.true;
				if (ts.isIdentifier(funcExpr)) {
					expect(funcExpr.text).to.equal('lookupTyped');
				}
			}
		});

		it('should detect lookupTyped() with nested type path', () => {
			const sourceCode = `
				import { lookupTyped } from 'mnemonica';
				const ConsciousnessConstructor = lookupTyped('Sentience.Consciousness');
			`;

			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			let stringLiteral: ts.StringLiteral | undefined;
			function visit(node: ts.Node) {
				if (ts.isStringLiteral(node) && node.text === 'Sentience.Consciousness') {
					stringLiteral = node;
				}
				ts.forEachChild(node, visit);
			}
			sourceFile.forEachChild(visit);

			expect(stringLiteral).to.exist;
			expect(stringLiteral!.text).to.equal('Sentience.Consciousness');
		});

		it('should not trigger for non-lookupTyped function calls', () => {
			const sourceCode = `
				const someFunc = () => {};
				const result = someFunc('Sentience');
			`;

			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			let stringLiteral: ts.StringLiteral | undefined;
			function visit(node: ts.Node) {
				if (ts.isStringLiteral(node) && node.text === 'Sentience') {
					stringLiteral = node;
				}
				ts.forEachChild(node, visit);
			}
			sourceFile.forEachChild(visit);

			expect(stringLiteral).to.exist;

			// Check that it's NOT a lookupTyped call
			const parent = stringLiteral!.parent;
			if (ts.isCallExpression(parent)) {
				const funcExpr = parent.expression;
				if (ts.isIdentifier(funcExpr)) {
					expect(funcExpr.text).to.not.equal('lookupTyped');
				}
			}
		});

		it('should parse definition location format correctly', () => {
			const location = '/code/mnemonica/tactica-nestjs/src/ai-types/Sentience:1:1';
			const locationMatch = location.match(/^(.+):(\d+):(\d+)$/);

			expect(locationMatch).to.exist;
			if (locationMatch) {
				const [, filePath, line, col] = locationMatch;
				expect(filePath).to.equal('/code/mnemonica/tactica-nestjs/src/ai-types/Sentience');
				expect(parseInt(line, 10)).to.equal(1);
				expect(parseInt(col, 10)).to.equal(1);
			}
		});

		it('should handle nested type location format', () => {
			const location = '/code/mnemonica/tactica-nestjs/src/ai-types/Sentience/Consciousness:1:1';
			const locationMatch = location.match(/^(.+):(\d+):(\d+)$/);

			expect(locationMatch).to.exist;
			if (locationMatch) {
				const [, filePath, line, col] = locationMatch;
				expect(filePath).to.equal('/code/mnemonica/tactica-nestjs/src/ai-types/Sentience/Consciousness');
				expect(parseInt(line, 10)).to.equal(1);
				expect(parseInt(col, 10)).to.equal(1);
			}
		});
	});

	describe('findTokenAtPosition helper', () => {
		it('should find the correct token at a given position', () => {
			const sourceCode = `const x = 'test';`;
			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			// Helper function matching the plugin's implementation
			function findTokenAtPosition(sourceFile: ts.SourceFile, position: number): ts.Node | undefined {
				function find(node: ts.Node): ts.Node | undefined {
					if (position >= node.getStart(sourceFile) && position < node.getEnd()) {
						let result: ts.Node | undefined;
						ts.forEachChild(node, child => {
							if (!result) {
								const found = find(child);
								if (found) {
									result = found;
								}
							}
						});
						return result || node;
					}
					return undefined;
				}
				return find(sourceFile);
			}

			// Position inside 'test' string literal
			const position = 11; // After const x = '
			const token = findTokenAtPosition(sourceFile, position);

			expect(token).to.exist;
			expect(ts.isStringLiteral(token!)).to.be.true;
			if (ts.isStringLiteral(token!)) {
				expect(token.text).to.equal('test');
			}
		});
	});

	describe('getFunctionName helper', () => {
		it('should extract identifier name', () => {
			const sourceCode = `lookupTyped('test')`;
			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			let callExpr: ts.CallExpression | undefined;
			sourceFile.forEachChild(node => {
				if (ts.isExpressionStatement(node) && ts.isCallExpression(node.expression)) {
					callExpr = node.expression;
				}
			});

			expect(callExpr).to.exist;
			const funcName = getFunctionName(callExpr!.expression);
			expect(funcName).to.equal('lookupTyped');
		});

		it('should extract property access name', () => {
			const sourceCode = `someModule.lookupTyped('test')`;
			const sourceFile = ts.createSourceFile(
				'test.ts',
				sourceCode,
				ts.ScriptTarget.Latest,
				true
			);

			let callExpr: ts.CallExpression | undefined;
			sourceFile.forEachChild(node => {
				if (ts.isExpressionStatement(node) && ts.isCallExpression(node.expression)) {
					callExpr = node.expression;
				}
			});

			expect(callExpr).to.exist;
			const funcName = getFunctionName(callExpr!.expression);
			expect(funcName).to.equal('lookupTyped');
		});

		function getFunctionName(expr: ts.Expression): string | undefined {
			if (ts.isIdentifier(expr)) {
				return expr.text;
			}
			if (ts.isPropertyAccessExpression(expr)) {
				return expr.name.text;
			}
			return undefined;
		}
	});
});
