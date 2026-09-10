'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypesWriter } from '../src/writer';
import { InstrumentationPoint, CreationGraph } from '../src/types';
import { TacticaPlugin } from '../src/plugins';

// Test-double plugin: supplies the framework vocabulary the analyzer
// matches. Tactica core ships NO vocabulary of its own — framework
// adapters provide a plugin like this one via the project config file.
const frameworkFixturePlugin: TacticaPlugin = {
	name                      : 'framework-fixture',
	instrumentationInterfaces : {
		NestInterceptor : 'interceptor',
		CanActivate     : 'guard',
		PipeTransform   : 'pipe',
		ExceptionFilter : 'filter',
		NestMiddleware  : 'middleware',
	},
	useDecorators : {
		UseGuards       : 'guard',
		UseInterceptors : 'interceptor',
		UsePipes        : 'pipe',
		Body            : 'pipe',
	},
	appTokens : {
		APP_GUARD       : 'guard',
		APP_PIPE        : 'pipe',
		APP_INTERCEPTOR : 'interceptor',
		APP_FILTER      : 'filter',
	},
	decoratorArgFactories : {
		forType   : { kind : 'pipe', targetArg : 0 },
		bindGuard : { kind : 'guard', targetArg : 1 },
	},
	middlewareWiring : true,
};

describe('MnemonicaAnalyzer - Instrumentation Points', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer(undefined, [ frameworkFixturePlugin ]);
	});

	describe('plugin gating', () => {
		it('should detect nothing without plugins (framework-blind core)', () => {
			const source = `
				export class LoggingInterceptor implements NestInterceptor {
					intercept (context: unknown, next: unknown) {
						return next;
					}
				}

				@UseGuards(AuthGuard)
				export class UserController {}

				const providers = [
					{ provide: APP_GUARD, useClass: GlobalAuthGuard },
				];

				export class AppModule {
					configure (consumer: unknown) {
						consumer.apply(LoggerMiddleware).forRoutes('users');
					}
				}
			`;

			const blind = new MnemonicaAnalyzer();
			blind.analyzeSource(source);
			const points = blind.getInstrumentationPoints();
			expect(points).to.deep.equal([]);
		});

		it('should skip middleware wiring when no plugin opts in', () => {
			const noWiring = new MnemonicaAnalyzer(undefined, [ {
				instrumentationInterfaces : { NestMiddleware : 'middleware' },
			} ]);
			const source = `
				export class LoggerMiddleware implements NestMiddleware {
					use (req: unknown, res: unknown, next: unknown) {
						return next;
					}
				}

				export class AppModule {
					configure (consumer: unknown) {
						consumer.apply(LoggerMiddleware).forRoutes('users');
					}
				}
			`;

			noWiring.analyzeSource(source);
			const points = noWiring.getInstrumentationPoints();
			// Only the heritage declaration point — no consumer.apply site
			expect(points).to.have.length(1);
			expect(points[ 0 ].scope).to.equal('module');
			expect(points[ 0 ].targets).to.deep.equal([]);
		});
	});

	describe('heritage detection', () => {
		it('should detect all five kinds via implements clauses', () => {
			const source = `
				import { NestInterceptor, CanActivate, PipeTransform, ExceptionFilter, NestMiddleware } from '@nestjs/common';

				export class LoggingInterceptor implements NestInterceptor {
					intercept (context: unknown, next: unknown) {
						return next;
					}
				}

				export class AuthGuard implements CanActivate {
					canActivate (context: unknown) {
						return true;
					}
				}

				export class TrimPipe implements PipeTransform {
					transform (value: unknown) {
						return value;
					}
				}

				export class HttpExceptionFilter implements ExceptionFilter {
					catch (exception: unknown, host: unknown) {
						return host;
					}
				}

				export class LoggerMiddleware implements NestMiddleware {
					use (req: unknown, res: unknown, next: unknown) {
						return next;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const byKind = (kind: string, className: string) => points.find(p => {
				return p.kind === kind && p.className === className;
			});

			const interceptor = byKind('interceptor', 'LoggingInterceptor');
			expect(interceptor).to.exist;
			expect(interceptor!.scope).to.equal('module');
			expect(interceptor!.targets).to.deep.equal([]);
			expect(interceptor!.location).to.match(/^temp\.ts:\d+:\d+$/);
			expect(interceptor!.code).to.include('class LoggingInterceptor implements NestInterceptor');

			expect(byKind('guard', 'AuthGuard')).to.exist;
			expect(byKind('pipe', 'TrimPipe')).to.exist;
			expect(byKind('filter', 'HttpExceptionFilter')).to.exist;
			expect(byKind('middleware', 'LoggerMiddleware')).to.exist;
		});

		it('should not emit declaration points for plain classes', () => {
			const source = `
				export class PlainService {
					doWork () {
						return 1;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();
			expect(points).to.have.length(0);
		});
	});

	describe('decorator application sites', () => {
		it('should detect @UseGuards on a controller class with targets', () => {
			const source = `
				import { CanActivate, UseGuards } from '@nestjs/common';

				export class AuthGuard implements CanActivate {
					canActivate () {
						return true;
					}
				}

				@UseGuards(AuthGuard)
				export class UserController {
					findAll () {
						return [];
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.scope === 'controller:UserController');
			expect(site).to.exist;
			expect(site!.kind).to.equal('guard');
			expect(site!.className).to.equal('AuthGuard');
			expect(site!.targets).to.deep.equal([ 'UserController' ]);
			// In-project class: location resolves to the class declaration
			const decl = points.find(p => p.className === 'AuthGuard' && p.scope === 'module');
			expect(decl).to.exist;
			expect(site!.location).to.equal(decl!.location);
		});

		it('should detect @UsePipes on a method with method scope', () => {
			const source = `
				import { UsePipes, ValidationPipe } from '@nestjs/common';

				export class UserController {
					@UsePipes(ValidationPipe)
					create (data: unknown) {
						return data;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'ValidationPipe');
			expect(site).to.exist;
			expect(site!.kind).to.equal('pipe');
			expect(site!.scope).to.equal('method:UserController.create');
			expect(site!.targets).to.deep.equal([ 'UserController' ]);
			// External class (not declared in-project): keeps the decorator site
			expect(site!.code).to.include('@UsePipes(ValidationPipe)');
		});

		it('should detect @UsePipes with an inline instance argument', () => {
			const source = `
				import { UsePipes, ValidationPipe } from '@nestjs/common';

				export class UserController {
					@UsePipes(new ValidationPipe({ transform: true }))
					createUser (data: unknown) {
						return data;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'ValidationPipe');
			expect(site).to.exist;
			expect(site!.kind).to.equal('pipe');
			expect(site!.scope).to.equal('method:UserController.createUser');
			expect(site!.targets).to.deep.equal([ 'UserController' ]);
			expect(site!.code).to.include('@UsePipes(new ValidationPipe(');
		});

		it('should detect @UseInterceptors with multiple referenced classes', () => {
			const source = `
				import { UseInterceptors } from '@nestjs/common';

				export class OrderController {
					@UseInterceptors(CacheInterceptor, TimeoutInterceptor)
					findAll () {
						return [];
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const interceptors = points.filter(p => p.kind === 'interceptor');
			expect(interceptors).to.have.length(2);
			const names = interceptors.map(p => p.className).sort();
			expect(names).to.deep.equal([ 'CacheInterceptor', 'TimeoutInterceptor' ]);
			for (const point of interceptors) {
				expect(point.scope).to.equal('method:OrderController.findAll');
				expect(point.targets).to.deep.equal([ 'OrderController' ]);
			}
		});
	});

	describe('decorator-arg factory calls', () => {
		it('should detect a plugin-listed factory call in a decorator arg (@UsePipes(mvp.forType(Dto)))', () => {
			const source = `
				import { UsePipes } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class CrateController {
					@UsePipes(mvp.forType(CrateDto))
					createCrate (data: unknown) {
						return data;
					}
				}

				export class CrateDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'CrateDto');
			expect(site).to.exist;
			expect(site!.kind).to.equal('pipe');
			expect(site!.scope).to.equal('method:CrateController.createCrate');
			expect(site!.targets).to.deep.equal([ 'CrateController' ]);
			// declared in-project: location/code resolve to the declaration
			// (CrateDto's declaration at line 12, not the decorator site at line 6)
			expect(site!.location).to.match(/temp\.ts:12:/);
		});

		it('should read the target from a non-zero factory argument position when configured', () => {
			const source = `
				import { UseGuards } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class GadgetController {
					@UseGuards(mvp.bindGuard('gadgets:write', GadgetGuard))
					replaceGadget () {
						return true;
					}
				}

				export class GadgetGuard {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'GadgetGuard');
			expect(site).to.exist;
			expect(site!.kind).to.equal('guard');
			expect(site!.scope).to.equal('method:GadgetController.replaceGadget');
		});

		it('should ignore factory calls whose method name is not plugin-listed', () => {
			const source = `
				import { UsePipes } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class TokenController {
					@UsePipes(mvp.unlisted(TokenDto))
					mintToken (data: unknown) {
						return data;
					}
				}

				export class TokenDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			expect(points.find(p => p.className === 'TokenDto')).to.equal(undefined);
		});

		it('should skip a listed factory whose configured target position is not an identifier', () => {
			const source = `
				import { UsePipes } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class HolderController {
					@UsePipes(mvp.forType(buildDto()))
					makeHolder (data: unknown) {
						return data;
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			expect(points.filter(p => p.scope === 'method:HolderController.makeHolder')).to.deep.equal([]);
		});

		it('should keep plain Identifier and new-expression args working alongside factory calls', () => {
			const source = `
				import { UsePipes } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class MixedController {
					@UsePipes(PlainPipe, new InlinePipe(), mvp.forType(FactoryDto))
					updateMixed () {
						return true;
					}
				}

				export class PlainPipe {}
				export class InlinePipe {}
				export class FactoryDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const byName = new Map(points.map(p => [ p.className, p ]));
			expect(byName.get('PlainPipe')?.kind).to.equal('pipe');
			expect(byName.get('InlinePipe')?.kind).to.equal('pipe');
			expect(byName.get('FactoryDto')?.kind).to.equal('pipe');
			expect(points.filter(p => p.scope === 'method:MixedController.updateMixed')).to.have.length(3);
		});
	});

	describe('parameter decorator parents', () => {
		it('should detect a parameter-decorated factory call (@Body(mvp.forType(Dto)) on a handler argument)', () => {
			const source = `
				import { Body } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export class InvoiceController {
					issueInvoice (@Body(mvp.forType(InvoiceDto)) data: unknown) {
						return data;
					}
				}

				export class InvoiceDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'InvoiceDto');
			expect(site).to.exist;
			expect(site!.kind).to.equal('pipe');
			expect(site!.scope).to.equal('method:InvoiceController.issueInvoice');
			expect(site!.targets).to.deep.equal([ 'InvoiceController' ]);
			// declared in-project: location/code resolve to the declaration
			expect(site!.location).to.match(/temp\.ts:11:/);
		});

		it('should detect a parameter-decorated plain listed decorator (no factory call)', () => {
			const source = `
				import { UsePipes } from '@nestjs/common';

				export class HolderController {
					updateHolder (@UsePipes(HolderPipe) data: unknown) {
						return data;
					}
				}

				export class HolderPipe {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const site = points.find(p => p.className === 'HolderPipe');
			expect(site).to.exist;
			expect(site!.kind).to.equal('pipe');
			expect(site!.scope).to.equal('method:HolderController.updateHolder');
			expect(site!.targets).to.deep.equal([ 'HolderController' ]);
		});

		it('should stay silent for a parameter decorator that is not plugin-listed', () => {
			const source = `
				import { Headers, Body } from '@nestjs/common';

				export class QuietController {
					ping (@Headers('x-token') token: string, @Body() data: unknown) {
						return data;
					}
				}

				export class QuietDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			expect(points.filter(p => p.scope === 'method:QuietController.ping')).to.deep.equal([]);
		});

		it('should stay silent for a parameter decorator on a non-method host (function parameter)', () => {
			const source = `
				import { Body } from '@nestjs/common';
				import { mvp } from '@mnemonica/nestjs';

				export function standalone (@Body(mvp.forType(StandaloneDto)) data: unknown) {
					return data;
				}

				export class StandaloneDto {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			expect(points.find(p => p.className === 'StandaloneDto')).to.equal(undefined);
		});
	});

	describe('APP_* global registrations', () => {
		it('should detect APP_GUARD / APP_PIPE / APP_INTERCEPTOR / APP_FILTER providers', () => {
			const source = `
				import { APP_GUARD, APP_PIPE, APP_INTERCEPTOR, APP_FILTER } from '@nestjs/core';

				const providers = [
					{ provide: APP_GUARD, useClass: GlobalAuthGuard },
					{ provide: APP_PIPE, useClass: GlobalValidationPipe },
					{ provide: APP_INTERCEPTOR, useClass: GlobalLoggingInterceptor },
					{ provide: APP_FILTER, useClass: GlobalExceptionFilter },
				];
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			expect(points).to.have.length(4);
			const kinds = points.map(p => p.kind).sort();
			expect(kinds).to.deep.equal([ 'filter', 'guard', 'interceptor', 'pipe' ]);
			for (const point of points) {
				expect(point.scope).to.equal('global');
				expect(point.targets).to.deep.equal([]);
			}
		});

		it('should skip useExisting / useFactory providers without a useClass', () => {
			const source = `
				import { APP_GUARD } from '@nestjs/core';

				const providers = [
					{ provide: APP_GUARD, useExisting: SomeToken },
					{ provide: APP_GUARD, useFactory: () => new DynamicGuard() },
				];
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();
			expect(points).to.have.length(0);
		});
	});

	describe('middleware wiring', () => {
		it('should detect consumer.apply().forRoutes() inside configure()', () => {
			const source = `
				import { NestMiddleware, MiddlewareConsumer } from '@nestjs/common';

				export class LoggerMiddleware implements NestMiddleware {
					use (req: unknown, res: unknown, next: unknown) {
						return next;
					}
				}

				export class UserController {}

				export class AppModule {
					configure (consumer: MiddlewareConsumer) {
						consumer.apply(LoggerMiddleware).forRoutes('users', UserController);
					}
				}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const middleware = points.filter(p => {
				return p.kind === 'middleware' && p.className === 'LoggerMiddleware';
			});
			// Heritage declaration and consumer.apply site share
			// (kind, className, location, scope) and merge into one point
			expect(middleware).to.have.length(1);
			expect(middleware[ 0 ].scope).to.equal('module');
			expect(middleware[ 0 ].targets).to.deep.equal([ 'users', 'UserController' ]);
			expect(middleware[ 0 ].code).to.include('class LoggerMiddleware implements NestMiddleware');
		});

		it('should ignore apply().forRoutes() outside configure()', () => {
			const source = `
				const consumer = makeConsumer();
				consumer.apply(StrayMiddleware).forRoutes('nowhere');
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();
			expect(points).to.have.length(0);
		});
	});

	describe('dedupe behavior', () => {
		it('should keep separate entries per scope for heritage + decorator', () => {
			const source = `
				import { CanActivate, UseGuards } from '@nestjs/common';

				export class AuthGuard implements CanActivate {
					canActivate () {
						return true;
					}
				}

				@UseGuards(AuthGuard)
				export class UserController {}

				@UseGuards(AuthGuard)
				export class AdminController {}
			`;

			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const authGuardPoints = points.filter(p => p.className === 'AuthGuard');
			// One 'module' declaration point + one point per controller scope
			expect(authGuardPoints).to.have.length(3);
			const scopes = authGuardPoints.map(p => p.scope).sort();
			expect(scopes).to.deep.equal([
				'controller:AdminController',
				'controller:UserController',
				'module',
			]);
		});

		it('should not duplicate points across repeated analysis passes (CLI runs two)', () => {
			const source = `
				import { NestInterceptor, UseInterceptors } from '@nestjs/common';

				export class TimingInterceptor implements NestInterceptor {
					intercept (context: unknown, next: unknown) {
						return next;
					}
				}

				@UseInterceptors(TimingInterceptor)
				export class UserController {}
			`;

			analyzer.analyzeSource(source);
			analyzer.analyzeSource(source);
			const points = analyzer.getInstrumentationPoints();

			const keys = points.map(p => `${p.kind}|${p.className}|${p.location}|${p.scope}`);
			expect(keys).to.have.length(new Set(keys).size);
			// declaration point + controller-scoped point
			expect(points).to.have.length(2);
		});
	});
});

describe('TypesWriter - instrumentation.json', () => {
	const testDir = path.join(__dirname, '.test-instrumentation');
	let writer: TypesWriter;

	beforeEach(() => {
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive : true });
		}
		writer = new TypesWriter(testDir);
	});

	afterEach(() => {
		if (fs.existsSync(testDir)) {
			fs.rmSync(testDir, { recursive : true });
		}
	});

	it('should write instrumentation.json with version 2 envelope', () => {
		const points: InstrumentationPoint[] = [
			{
				kind      : 'guard',
				className : 'AuthGuard',
				location  : '/abs/path/src/auth.guard.ts:3:14',
				code      : 'export class AuthGuard implements CanActivate {',
				scope     : 'controller:UserController',
				targets   : [ 'UserController' ],
			},
		];

		const outputPath = writer.writeInstrumentationFile(points);

		expect(fs.existsSync(outputPath)).to.be.true;
		const written = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
		expect(written.version).to.equal(2);
		expect(written.generatedAt).to.be.a('string');
		expect(written.points).to.deep.equal(points);
		// Without creation-graph data the key stays absent (library callers)
		expect(written).to.not.have.property('creationGraph');
	});

	it('should include the creation graph when provided (CLI always passes it)', () => {
		const creationGraph: CreationGraph = {
			nodes : [
				{
					scopeId  : '/abs/path/src/main.ts',
					name     : '/abs/path/src/main.ts',
					kind     : 'module',
					filePath : '/abs/path/src/main.ts',
					location : '/abs/path/src/main.ts:1:1',
					starter  : true,
				},
			],
			edges   : [],
			anchors : [
				{
					location      : '/abs/path/src/main.ts:5:16',
					holderScopeId : '/abs/path/src/main.ts',
					typePath      : 'Thing',
					rooted        : true,
				},
			],
		};

		const outputPath = writer.writeInstrumentationFile([], creationGraph);

		const written = JSON.parse(fs.readFileSync(outputPath, 'utf-8'));
		expect(written.version).to.equal(2);
		expect(written.creationGraph).to.deep.equal(creationGraph);
	});
});
