'use strict';

import { expect } from 'chai';
import * as fs from 'fs';
import * as path from 'path';
import { MnemonicaAnalyzer } from '../src/analyzer';
import { TypesWriter } from '../src/writer';
import { InstrumentationPoint } from '../src/types';

describe('MnemonicaAnalyzer - Instrumentation Points', () => {
	let analyzer: MnemonicaAnalyzer;

	beforeEach(() => {
		analyzer = new MnemonicaAnalyzer();
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

	it('should write instrumentation.json with version 1 envelope', () => {
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
		expect(written.version).to.equal(1);
		expect(written.generatedAt).to.be.a('string');
		expect(written.points).to.deep.equal(points);
	});
});
