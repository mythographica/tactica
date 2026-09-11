# @mnemonica/tactica

**Type definition generator for Mnemonica.**

Tactica is a CLI tool and Node library that statically analyzes TypeScript / JavaScript source code and generates type definitions, navigation metadata, and runtime-flow data for projects that use [mnemonica](https://github.com/wentout/mnemonica) — the instance-inheritance system that creates types dynamically at runtime through `define()` and `decorate()` calls.

Output lives in `.tactica/` and is consumed by:

- **`tsc`** — so TypeScript can understand `user.AdminType` after `UserType.define('AdminType', …)`.
- **`mnemonica.lookup<K>()`** — type-safe runtime lookup via the generated `TypeRegistry` module augmentation.
- **[mnemographica](https://github.com/mythographica/mnemographica)** (VS Code extension) — for Go to Definition, Find References, and the type-hierarchy graph view.

## The Problem

Mnemonica enables instance-level inheritance:

```ts
const UserType = define('UserType', function (this: { name: string }) {
    this.name = '';
});

const AdminType = UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});

const user = new UserType();
const admin = new user.AdminType(); // works at runtime
```

TypeScript can't infer that `user.AdminType` exists, because `UserType.define()` is a runtime operation.

## The Solution

Tactica parses your source, builds the type hierarchy, and emits `.tactica/types.ts` + `.tactica/registry.ts`. Once those files are part of your `tsc` compilation, TypeScript understands the full hierarchy — without runtime changes.

## Installation

```bash
npm install --save-dev @mnemonica/tactica
```

`mnemonica` is a peer dependency (>= 1.0.1).

## Usage

### CLI

```bash
# One-shot generation
npx tactica

# Watch mode (regenerate on file changes)
npx tactica --watch

# Custom output directory
npx tactica --output ./types/mnemonica

# Custom tsconfig
npx tactica --project ./src/tsconfig.json
```

### Library

```ts
import { MnemonicaAnalyzer, TypesGenerator, TypesWriter } from '@mnemonica/tactica';
import * as ts from 'typescript';

const program = ts.createProgram(['./src/index.ts'], {});
const analyzer = new MnemonicaAnalyzer(program);

for (const sourceFile of program.getSourceFiles()) {
    if (!sourceFile.isDeclarationFile) {
        analyzer.analyzeFile(sourceFile);
    }
}

const generator = new TypesGenerator(analyzer.getGraph());
const writer    = new TypesWriter('.tactica');

// Default mode — exportable type aliases in types.ts + a TypeRegistry augmentation in registry.ts.
writer.writeTypesFile(generator.generateTypesFile());
writer.writeTo('registry.ts', generator.generateTypeRegistry().content);

// Legacy mode — single global augmentation file index.d.ts.
// writer.writeGlobalAugmentation(generator.generateGlobalAugmentation());
```

### Project setup

After running `npx tactica`, add `.tactica` to your `tsconfig.json` so the generated files are part of the compilation:

```json
{
  "compilerOptions": {
    "paths": {
      "~tactica/*": ["./.tactica/*"]
    }
  },
  "include": ["src/**/*.ts", ".tactica/**/*.ts"]
}
```

Then use `lookup` for type-safe access (see "Type-Safe Lookup" below).

You should commit `.tactica/` if you want type information to flow through CI without re-running tactica; alternatively, add `.tactica/` to `.gitignore` and regenerate as part of your build. Tactica does **not** modify `.gitignore` for you.

## CLI Options

| Option | Short | Description |
|---|---|---|
| `--watch` | `-w` | Watch mode — regenerate on file changes |
| `--project <path>` | `-p` | Path to `tsconfig.json` (default: nearest ancestor) |
| `--output <dir>` | `-o` | Output directory (default: `.tactica`) |
| `--include <patterns>` | `-i` | Comma-separated include patterns |
| `--exclude <patterns>` | `-e` | Comma-separated exclude patterns |
| `--topologica <dirs>` | `-t` | Comma-separated Topologica directories to scan |
| `--module-augmentation` | `-m` | Legacy mode — emit a single global-augmentation `index.d.ts` instead of `types.ts` + `registry.ts` |
| `--esm` |  | Append `.js` extensions to relative imports in generated files (for ESM / NodeNext module resolution) |
| `--eds` |  | Force-enable EDS (Execution Data Storage) tracking |
| `--no-eds` |  | Force-disable EDS tracking |
| `--verbose` | `-v` | Verbose logging |
| `--help` | `-h` | Show help |

EDS tracking is **auto-enabled** when `@mnemonica/dive` is present in `package.json` dependencies; otherwise it is off. `--eds` / `--no-eds` override the auto-detection.

## Generated Files

Tactica writes everything under the `--output` directory (default `.tactica/`):

| File | When | Purpose |
|---|---|---|
| `types.ts` | default mode | Exportable type aliases — one per discovered type. Uses `ProtoFlat<Parent, Self>` for nested types. |
| `registry.ts` | default mode | `declare module 'mnemonica' { interface TypeRegistry { … } }` augmentation — powers `lookup<K>()`. |
| `index.ts` | default mode | Re-exports everything from `types.ts` and `registry.ts`. |
| `index.d.ts` | with `--module-augmentation` | Single global-augmentation file (legacy mode). |
| `definitions.json` | always | One entry per discovered type: `{ name, location, kind: 'define'\|'decorate', parent, strictChain, blockErrors }`. Consumed by `mnemographica`'s Go to Definition. |
| `usages.json` | always | One entry per type, value is an array of `{ location, kind, code, holderScopeId?, constructorText? }` records — where each type is instantiated, referenced, accessed, or looked up. `holderScopeId` points into `scopes.json` (the innermost scope holding the usage); `constructorText` (instantiations only) is the constructor expression text actually used. Consumed by `mnemographica`'s Find References. |
| `flow.json` | always | Native instance-flow patterns (property reads/writes, method calls, destructuring, returns, spreads, etc.) per type. |
| `instrumentation.json` | always | v2 envelope. `points`: framework lifecycle crossroads (interceptors, guards, pipes, filters, middleware) detected via **plugin-supplied vocabulary** — heritage declarations, decorator sites, provider-token registrations, `consumer.apply()` wiring. Syntactic only — no dive dependency; with no plugins loaded, `points` is `[]`. `creationGraph`: the inside-out walk from every instantiation site out to the starters — see "Creation graph" below. |
| `modules.json` | always | Module-scope graph: every module's `exportedBindings`/`importedBindings` (functions, classes, consts, types — not only mnemonica types), project-internal `dependencies`, `builtinSpecifiers` (Node builtins are skipped entirely — both `'path'` and `'node:path'` forms), `unresolvedSpecifiers`, circular-import `cycles`, and cross-module mnemonica-type `edges`. Resolution uses `ts.resolveModuleName` with the project's compilerOptions (tsconfig `paths`, extensionless imports, index files) — no type checker. Bindings resolved into `node_modules` are marked `external: true` and never enter `dependencies`. |
| `scopes.json` | always | Local-scope graph: function/method/arrow scopes only (no block scopes) plus one module scope per file; variables with `typePath` (mnemonica type when known), `isParameter`, `isMutable`, and `reassignments` — each reassignment of a mutable binding is a flow-termination point. `lookup()` initializers resolve through the same tier law as the analyzer (scope-chain receiver first, then the analyzer's source-relative/root law), so scopes metadata never disagrees with the hard-fail verdicts. |
| `eds.json` | when EDS enabled | Execution-flow patterns (`wrap`, `current`, `getFlow`, `attachHooks` lifecycle wiring). Consumed by tools that visualize execution chains. |

### Default mode (types.ts + registry.ts)

```ts
// .tactica/types.ts
export type UserType = {
    name: string;
    email: string;
    AdminType: new (data: { role: string }) => UserType_AdminType;
};

export type UserType_AdminType = ProtoFlat<UserType, {
    role: string;
    AdminType: undefined;
}>;
```

```ts
// .tactica/registry.ts
declare module 'mnemonica' {
    interface TypeRegistry {
        'UserType': new (data: { name: string; email: string }) => UserType;
        'UserType.AdminType': new (data: { role: string }) => UserType_AdminType;
    }
}
```

**Recommended for new projects.** Explicit imports, better tree-shaking, no global namespace pollution.

**Instance-type inheritance.** Nested instance types flatten the WHOLE ancestor chain: each nested type is `ProtoFlat<ParentInstance, Self>` (mnemonica's `ProtoFlat` keeps every parent key except the ones `Self` overrides), and the parent instance type is itself a `ProtoFlat` over its own parent — so the ROOT's own constructor-arg fields (`uuid` in `PaymentRoot`) are directly present on every descendant instance type, at any depth, alongside intermediate ancestors' fields. If a root field appears missing on a nested type, the usual cause is a stale `.tactica` — regenerate; the composition itself is transitive by construction.

### Legacy global-augmentation mode (`--module-augmentation`)

Emits one `.tactica/index.d.ts` whose contents live inside `declare global { … }`. Reference it from your code with:

```ts
/// <reference types="./.tactica/index" />
```

or by adding `./.tactica` to `compilerOptions.typeRoots`. Kept for backwards compatibility with older tactica integrations.

## Type-Safe Lookup with `lookup()`

Mnemonica core exposes `lookup<K>()` against an empty `TypeRegistry` interface. Tactica's `registry.ts` augments that interface with all of your discovered types:

```ts
// .tactica/registry.ts  (generated)
declare module 'mnemonica' {
    interface TypeRegistry {
        'UserType': new (data: { name: string; email: string }) => UserType;
        'UserType.AdminType': new (data: { role: string }) => UserType_AdminType;
    }
}
```

Once `registry.ts` is in your `tsc` compilation, the lookup is fully typed:

```ts
import { lookup } from 'mnemonica';
import './.tactica/registry'; // or via tsconfig "include"

const UserType  = lookup('UserType');
const AdminType = lookup('UserType.AdminType');

const user  = new UserType({ name: 'John', email: 'j@x.dev' });
const admin = new user.AdminType({ role: 'admin' });
```

No `as unknown as` casts required. See [`docs/lookup-pattern.md`](docs/lookup-pattern.md) for the consumer-side guide.

## What Gets Analyzed

### `define()` calls

```ts
const UserType  = define('UserType', function (this: { name: string }) {
    this.name = '';
});

const AdminType = UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});
```

Chained calls (`define('A').define('B')`) and nested calls via variable references (`const A = define('A', …); A.define('B', …)`) are both supported. A const holding a multi-hop initializer binds the LAST hop — `define()` returns the defined type's constructor, so `const Branch = Root.define('A', …).define('B', …)` makes `Branch` denote `Root.A.B` and `Branch.define('C', …)` nests C under B, exactly as the runtime does.

**Call-site ergonomics (recommended pattern):** annotate the root constructor's `this` with the generated instance type alias — `define('Widget', function (this: TWidgetInstance, data: …) {…})`, with `TWidgetInstance` imported from the generated types file. The common form is an intersection — `type TWidgetInstance = TWidgetArgs & TGeneratedRootInstance`. Tactica tolerates the self-reference: the annotation is never emitted into the generated type (so no circularity can form), and it is **ergonomic-only** — its members are never expanded, so the root's fields must be carried by the constructor body: `Object.assign(this, args)` (the identifier form extracts every field from the named args type) or explicit `this.x = …` assignments. Property extraction falls back to the body / data parameter whenever the alias is not analyzable (it lives in the excluded `.tactica/`). With the generated `types.ts`/`registry.ts` in place, `new (lookup('Widget'))(args)` — and `new Widget(args)` where the const merges with the generated type — is directly assignable to the instance type at call sites, zero casts. Regenerate `.tactica` after adding the annotation.

### `lazy()` definitions

```ts
const AdminType = UserType.lazy(() => class AdminType {
    role: string;
    constructor (role: string) {
        this.role = role;
    }
});
```

All forms are recognized: free `lazy('Name', getter)`, method `Type.lazy(...)`, and chained `define('A').lazy('B', getter)`. The getter is followed, and the returned constructor is analyzed like a direct `define()` handler — properties and constructor parameters are extracted and emitted in `types.ts` / `registry.ts` like any other type.

### Construction shapes beyond plain `new`

These usage shapes are recognized and attributed within the existing output contract (the `instantiation` usage kind and value-scope bindings — no new output fields):

- **Chain construction** — `new Root(...).Child(...)` and the single-await form `await new Root(...).A(...).B(...)`: the chain-tip call records an `instantiation` of the tip type (`Root.A.B`), supplying the creation-graph anchor, and the result variable binds to the TIP's type, not the root's. `await` is transparent everywhere on this page — `await call(...)`, `await apply(...)`, `await entry.fork(...)`, and async `bind` recognition all work identically.
- **`instance.fork(...)` / `instance.clone()`** (call forms) and **`instance.clone`** (the property form — core types it `readonly clone: this`) — runtime returns `this`, so the result variable binds to the source instance's type. Fork re-runs construction (hooks fire, a distinct instance on a distinct line), so these record an **`instantiation` usage** at the site — byte-indistinguishable from `new` until the deferred mechanism-kind revision; the result binding and the generic `methodCall`/`propertyRead` flow entries stay.
- **`utils.merge(a, b, ...)`** (also the direct named import, and the curried `utils.fork(instance)(...)`) — the result binds to **arg 0's type**: the runtime answer is a's lineage over b's context, and a's fullPath is the honest approximation within the contract. Merge is `fork(a)` over b's context, so it records an `instantiation` for a's type too; the curried `utils.fork` records at the invocation site, and the inner `utils.fork(instance)` binding line records its own entry — one per distinct source line.
- **`call(entity, Ctor, ...)` / `apply(entity, Ctor, args)`** — the mnemonica construction exports (import-aware: only actual `'mnemonica'` imports or members of a tracked module-object alias match; userland `call`/`apply` never do). The Ctor argument (arg 1) records an `instantiation`, and the result variable binds to the Ctor's type (runtime `InstanceResult<Merge<E, T>>` approximated by T). **Decorated classes resolve as the Ctor** through the same graph tiers — `@decorate() class C` is a known type, so `call(parent, C)` records and binds; an undecorated plain class has no graph entry, so the call binds nothing and records no usage (never a bare name). The free-call `decorate(Class)` form is not tracked (tactica recognizes the `@decorate` decorator syntax only).
- **`bind(entity, Ctor)`** — records no usage (it constructs nothing); the bound variable binds to the Ctor's type. Invoking the bound function later (`f(...)`, including `await f(...)`) is not followed.

Two boundaries stay deliberate: bindings surface only for references lexically AFTER the binding statement (a binding made inside a constructor body is not yet visible to that same handler's property extraction), and the mechanism distinction (`new` vs fork vs call) is not carried in the outputs — fork/clone/merge record as plain `instantiation` entries, byte-indistinguishable from `new`, until the deferred mechanism-kind contract revision lands. Consumers counting constructions should expect fork sites among them.

### Builder pattern on the imported module object

The analyzer also recognizes the chainable `mnemonica` module object and aliases of it:

```ts
import { mnemonica } from 'mnemonica';

const App = mnemonica
    .define('UserType', function (this: { name: string }) {
        this.name = '';
    })
    .define('AdminType', function (this: { role: string }) {
        this.role = 'admin';
    });

// Builder .lookup() results are followed
App.lookup('UserType').define('GuestType', function (this: { token: string }) {
    this.token = '';
});
```

It also recognizes the explicit-source APIs:

```ts
import { define, lookup } from 'mnemonica';

const AdminType = define(UserType, 'AdminType', function (this: { role: string }) {
    this.role = 'admin';
});

const AdminCtor = lookup(App, 'UserType.AdminType');
```

### Custom collections via `createTypesCollection()`

Types defined on a collection created with `createTypesCollection()` are tracked by the analyzer. By default they are **not** emitted in `.tactica/types.ts` and are **not** added to the global `mnemonica.TypeRegistry` augmentation because they live in an isolated runtime collection. Use the collection variable directly in your own code to get typed constructors.

All common import styles are recognized:

```ts
import { createTypesCollection } from 'mnemonica';

const AppCollection = createTypesCollection();

AppCollection.define('UserType', function (this: { name: string }) {
    this.name = '';
});
```

```ts
import { mnemonica } from 'mnemonica';

const AppCollection = mnemonica.createTypesCollection();
```

```ts
import * as mnemonica from 'mnemonica';

const AppCollection = mnemonica.createTypesCollection();
```

```ts
import { createTypesCollection as ctc } from 'mnemonica';

const AppCollection = ctc();
```

Subtypes defined from a collection type inherit the same collection membership:

```ts
const UserType = AppCollection.define('UserType', function (this: { name: string }) {
    this.name = '';
});

UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});
```

Two independent collections may define root types with the same name without colliding in the analyzer graph.

#### Option B — user-provided registry interface

To get fully typed `.lookup()` and `.decorate()` for a custom collection, export an empty interface and pass it to `createTypesCollection<Registry>()`:

```ts
import { createTypesCollection } from 'mnemonica';

export interface AppCollectionRegistry {}

const AppCollection = createTypesCollection<AppCollectionRegistry>();

const UserType = AppCollection.define('UserType', function (this: { name: string }) {
    this.name = '';
});

UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});
```

Tactica then emits:

- Prefixed instance types in `.tactica/types.ts`, e.g. `AppCollectionRegistry_UserType` and `AppCollectionRegistry_UserType_AdminType`.
- A `declare module '<relative path to this file>'` block in `.tactica/registry.ts` that augments `AppCollectionRegistry` with `'UserType'` and `'UserType.AdminType'` entries.

Once `.tactica/registry.ts` is part of your `tsc` compilation, `AppCollection.lookup('UserType')` and `AppCollection.lookup('UserType.AdminType')` are fully typed.

Custom collections also support `decorate()` for root types:

```ts
@AppCollection.decorate()
class UserType {
    name: string = '';
}
```

Decorated root types are included in the same per-collection augmentation.

```ts
@decorate()
class User {
    name: string = '';
}

@decorate(User)
class Admin {
    role: string = 'admin';
}

@decorate({ blockErrors: true, strictChain: false })
class Configurable {
    value: string = '';
}
```

Decorate-class instances need a cast to the generated instance type to access nested constructors at the type level:

```ts
const order = new Order() as Order_AugmentedOrder; // … or whatever your generated alias is
const sub   = new order.AugmentedOrder();
```

### `Object.assign(this, data)` pattern

```ts
const UserType = define('UserType', function (this: any, data: { name: string }) {
    Object.assign(this, data); // properties inferred from `data` type
});
```

### `TypeConstructor` casting (from mnemonica)

```ts
import { define } from 'mnemonica';
import type { TypeConstructor } from 'mnemonica';

const MyFn = function (this: any) {
    this.field = 123;
} as TypeConstructor<{ field: number }>;

const MyFnType = define('MyFnType', MyFn);
```

(In older mnemonica documentation this helper was called `ConstructorFunction`; the analyzer still recognizes that name in source code for back-compat.)

### Typeomatica integration

Tactica recognizes [typeomatica](https://github.com/wentout/typeomatica) patterns alongside mnemonica:

```ts
import { decorate } from 'mnemonica';
import { Strict, BaseClass } from 'typeomatica';

@decorate()
@Strict({ someProp: 123 })
class StrictDecorated {
    someProp!: number;
}

@decorate()
class MyBaseClass {
    base_field = 555;
}

Object.setPrototypeOf(MyBaseClass.prototype, new BaseClass({ strict: true }));
```

### Topologica directory structures

[Topologica](https://github.com/mythographica/topologica)-style directory hierarchies are scanned for handler files, and a type tree is built from the directory layout:

```
ai-types/
├── Sentience/
│   ├── index.ts            // exports SentienceHandler(this, data)
│   └── Consciousness/
│       └── index.ts        // exports ConsciousnessHandler(this, data)
```

Auto-discovered directories (relative to `tsconfig.json`): `./ai-types`, `./types`, `./topologica-types`, plus the same names under `./src/`.

Add custom directories with `--topologica`:

```bash
npx tactica --topologica ./src/ai-types,./custom/topologica
```

## Property Type Inference

The analyzer infers property types from constructor bodies and class members. Supported expression patterns:

| Pattern | Inferred type |
|---|---|
| `this.x = 'foo'` | `string` |
| `this.x = 123` | `number` |
| `this.x = true` | `boolean` |
| `this.x = []` / `new Array()` | `Array<…>` |
| `this.x = {}` | `object` |
| `this.x = new Date()` | `Date` |
| `this.x = new Map()` / `new Set()` | `Map<…>` / `Set<…>` |
| `this.x = Date.now()` | `number` |
| `this.x = parseInt(…)` / `parseFloat(…)` | `number` |
| `this.x = String(…)` / `Number(…)` / `Boolean(…)` | `string` / `number` / `boolean` |
| `this.x = a + b` (where `a, b: number`) | `number` |
| `` this.x = `${a} ${b}` `` | `string` |
| `this.x = data.field` | type of `data.field` from the parameter annotation |
| `this.x = data.field` where `data: SomeNamedType` (alias/interface/class) | type of the field from the resolved declaration — import-aware, inherited members included; a bare `this.x = data` keeps the full expanded shape |
| `this.x = data.field \|\| []` | type of the fallback expression |
| `this.x = data.field ? a : b` | type of the truthy branch |
| `Object.assign(this, data)` | all fields of `data`'s type annotation — inline literal or named alias/interface/class, resolved import-aware (F14 machinery) |
| `this.x = boundVar` where `boundVar` holds a construction result (`new`/`lookup()`/chain/fork/merge/call) | the bound type's instance type (value-scope binding) — bindings surface lexically AFTER the binding statement; within the same constructor body a fresh binding is not yet visible to the handler's own extraction |
| async / sync constructor functions | same rules |

An existing annotation always beats a weaker inference: `unknown` (and `unknown`-bearing guesses like `Array<unknown>`) never overwrites a known type — `Record<string, unknown>` IS a known type — and an overwrite never drops an optionality modifier.

When inference fails the property's type falls back to `unknown` (or `any` in some Topologica paths) — safe, and you can refine manually.

### Referenced types in constructor signatures

A constructor parameter that references a named type (`record: SharedShape`) resolves **through the importing file's own import statements** — relative and tsconfig-paths imports are followed to the declaration (chasing re-export barrels), and imported classes/interfaces/type aliases with extractable fields are expanded inline, **inherited members included**: `extends` chains are walked (depth-bounded, cycle-guarded) and parent fields merge with the declaration's own fields overriding on name clash. A field typed by a `typeof` query over a module-level const array (`status?: typeof statusList[number]`) expands to the element literal union (`status?: 'active' | 'closed'`); any other `typeof` source degrades that field to `unknown` — a bare `typeof name` is never emitted, since the generated file has no imports to resolve it against. An import is never shadowed by a same-named declaration elsewhere in the program. A reference that resolves not at all (a ghost name, declared nowhere) emits `unknown` — generated `.tactica/types.ts` carries no import statements of its own, so a bare unresolvable name is never emitted. A reference that resolves *ambiguously* — several of your project's files declare the name and no import chooses between them — is **fatal** like the mnemonica-graph identity law below: tactica prints the reference site and every declaration site, exits non-zero, and writes no output. An import anchoring the reference is never ambiguity (the import wins, duplicate declarations or not), and package-declared same-named types never count — a user-local declaration always wins over a node_modules `.d.ts`. Two same-named interfaces in one file are legal TypeScript merging, not ambiguity (see Known Limitations for the last-wins caveat).

**Ambiguous plain-TypeScript reference — fails, and how to fix it.** Two plain interfaces named `SharedShape` exist in different files, and a third file references a bare `SharedShape` with nothing anchoring it:

```ts
// a.ts                              // b.ts
export interface SharedShape {      export interface SharedShape {
	a: string;                       	b: number;
}                                    }

// consumer.ts — FATAL: which SharedShape?
import { define } from 'mnemonica';

export const Crate = define('Crate', function (this: Crate, data: SharedShape) {
	this.item = data;
});
```

```
tactica: Ambiguous reference to type 'SharedShape': 2 declarations share the name and no import disambiguates — import the one you mean
  at src/consumer.ts:6:67
  at /abs/path/src/a.ts:1:1
  at /abs/path/src/b.ts:1:1
tactica: aborting — 1 resolution failure(s); no .tactica output written
```

Fix it by importing the declaration you mean — the file's own import wins over every other tier:

```ts
// consumer.ts — OK: the import anchors SharedShape → a.ts
import { define } from 'mnemonica';
import { SharedShape } from './a';

export const Crate = define('Crate', function (this: Crate, data: SharedShape) {
	this.item = data; // item: { a: string }
});
```

Qualified references through a namespace import resolve one level per segment: `models.SharedShape` finds the declaration in the namespace import's module; multi-level paths (`holders.Inner.Crate`, `barrel.Deep.Gadget`) descend through namespace declarations, `export * as ns from '…'` barrels, and named re-exports of namespaces — each segment disambiguates, so two namespaces may declare the same name without colliding. What is *not* followed: ambient string-named modules (`declare module '…'`), default-export shapes behind a namespace segment, and type-only constructs with no extractable fields (unions of literals, mapped types) — those emit `unknown` like any other unresolvable reference.

References to **mnemonica graph types** (types declared via `define()`, as opposed to plain TypeScript declarations) follow the runtime lookup law instead: the file's own value bindings and imports anchor the name first, then the defining type's own chain relative-first, then its collection's roots, then a program-wide search that must be unique. Same-namespace duplicate definitions (which the mnemonica runtime rejects with `ALREADY_DECLARED`) and graph references that stay ambiguous or unresolved are fatal: tactica prints every location, exits non-zero, and writes no `.tactica` output at all.

**Ambiguous reference — fails, and how to fix it.** Two types named `Token` exist under different parents, and a third file references a bare `Token` with nothing anchoring it:

```ts
// defs.ts
export const Holder = define('Holder', function (this: Holder) { /* … */ });
export const Token = Holder.define('Token', function (this: Token, data: { mark: string }) { /* … */ });

// other.ts
export const Other = define('Other', function (this: Other) { /* … */ });
Other.define('Token', function (this: Token, data: { hue: string }) { /* … */ });

// consumer.ts — FATAL: which Token?
export const Crate = define('Crate', function (this: Crate, data: Token) {
	this.item = data;
});
```

```
tactica: Ambiguous reference to mnemonica type 'Token': 2 types share the name and neither the parent chain nor the imports disambiguate
  at src/consumer.ts:7:67
  at src/defs.ts:8:29
  at src/other.ts:9:7
tactica: aborting — 1 resolution failure(s); no .tactica output written
```

Fix it by anchoring the reference — either import the constructor you mean (the import wins over every other tier), or use the full generated name:

```ts
// consumer.ts — OK: the import anchors Token → Holder.Token
import { Token } from './defs';
export const Crate = define('Crate', function (this: Crate, data: Token) {
	this.item = data;
});

// or — OK: fully-qualified generated type name
export const Crate = define('Crate', function (this: Crate, data: Holder_Token) {
	this.item = data;
});
```

**Duplicate in one namespace — fails, and there is only one fix.** Two types with the same name under the same parent (or two same-named roots) are what the mnemonica runtime rejects with `ALREADY_DECLARED`; tactica fails the generation instead of emitting a wrong graph:

```ts
// dup-a.ts                     // dup-b.ts
export const A = define(        export const B = define(
	'DupRoot', …);              	'DupRoot', …);
```

```
tactica: Duplicate definition of 'DupRoot' in one namespace — the mnemonica runtime would throw ALREADY_DECLARED
  at src/dup-a.ts:3:22
  at src/dup-b.ts:6:23
tactica: aborting — 1 resolution failure(s); no .tactica output written
```

Rename one of them. Same-named types under **different** parents (`User.Address` and `Company.Address`) are legal mnemonica and never reported.

**Unresolved `lookup()` path — fails, with a did-you-mean.** Literal `lookup()` paths are validated against the complete graph after analysis. A path matching no type is what the runtime answers with `undefined` — the `TypeError` arrives one line later at the `new` — so it is fatal too, and same-named types elsewhere in the graph are listed as candidates:

```ts
// consumer.ts — FATAL: no root 'Token'; Holder.Token and Other.Token exist
const TokenCtor = lookup('Token');
export const instance = new TokenCtor({ mark: 'x' });
```

```
tactica: Unresolved lookup of mnemonica type 'Token': the runtime would return undefined — 2 graph type(s) carry the name off-root (Holder.Token, Other.Token); use the full dotted path
  at src/consumer.ts:6:19
  at src/defs.ts:8:29
  at src/other.ts:9:7
tactica: aborting — 1 resolution failure(s); no .tactica output written
```

```ts
// OK: dotted absolute path, or receiver-relative resolution
const ByPath     = lookup('Holder.Token');
const ByReceiver = Holder.lookup('Token');
```

Non-literal lookup arguments (computed strings) stay best-effort and are not validated.

## API Reference

### `MnemonicaAnalyzer`

```ts
class MnemonicaAnalyzer {
    constructor(program?: ts.Program, plugins?: TacticaPlugin[]);

    analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult;
    analyzeSource(sourceCode: string, fileName?: string): AnalyzeResult;

    resetUsages(): void;                    // call between definition pass and usage pass
    addTopologicaType(fullPath: string, node: TypeNode): void;

    getGraph(): TypeGraphImpl;
    getDefinitions(): Map<string, DefinitionInfo>;
    getUsages():      Map<string, UsageInfo[]>;
    getEDSUsages():   Map<string, EDSInfo[]>;
    getFlowUsages():  Map<string, FlowInfo[]>;
    getInstrumentationPoints(): InstrumentationPoint[];
    getResolutionErrors(): ResolutionError[];  // fatal duplicate/ambiguous graph + plain-TS references (hard-fail law)
}
```

### `TopologicaAnalyzer`

```ts
class TopologicaAnalyzer {
    analyzeDirectory(directoryPath: string): { types: Map<string, TypeNode>; errors: string[] };
    getGraph(): TypeGraphImpl;
    getErrors(): string[];
}
```

### `TypeGraphImpl`

```ts
class TypeGraphImpl implements TypeGraph {
    roots:    Map<string, TypeNode>;
    allTypes: Map<string, TypeNode>;

    addRoot(node: TypeNode): void;
    addChild(parent: TypeNode, child: TypeNode): void;
    findType(fullPath: string): TypeNode | undefined;
    findTypeByName(name: string): TypeNode | undefined;
    getAllTypes(): TypeNode[];
    clear(): void;

    *bfs(): Generator<TypeNode>;
    *dfs(node?: TypeNode): Generator<TypeNode>;

    static createNode(name, parent, sourceFile, line, column, collectionId?): TypeNode;
}
```

### `TypesGenerator`

```ts
class TypesGenerator {
    constructor(graph: TypeGraphImpl, esm?: boolean);

    generateTypesFile():           GeneratedTypes; // default mode → types.ts
    generateTypeRegistry():        GeneratedTypes; // default mode → registry.ts
    generateGlobalAugmentation():  GeneratedTypes; // legacy mode  → index.d.ts
    generateSingleType(node: TypeNode): string;
}
```

### `ModuleGraphBuilder`

Module-scope walker. Tracks every export/import binding of every module —
generically, not only mnemonica types — and resolves specifiers with
`ts.resolveModuleName` driven by the program's compilerOptions
(no `getTypeChecker()`).

```ts
class ModuleGraphBuilder {
    constructor(program?: ts.Program, compilerOptions?: ts.CompilerOptions);

    addFile(sourceFile: ts.SourceFile): ModuleInfo;   // call per file (definitions pass)
    build(definedTypesByFile?: Map<string, string[]>): ModuleGraph;
}
```

`ModuleGraph` = `{ modules: Map<absPath, ModuleInfo>, edges: CrossModuleUsage[], cycles: string[][] }`.
Each `ModuleBinding` carries `{ name, kind: 'function'|'class'|'const'|'type'|'unknown',
sourceModule (resolved absolute path), importKind?, importAlias?, isReExport, external? }`.
Node.js builtins (`'path'`, `'node:fs'`, …) are skipped entirely and recorded
only in the module's `builtinSpecifiers`; bindings resolved into `node_modules`
carry `external: true` and never enter `dependencies`. Re-export chains
(barrels, `export * from`) are chased to the origin module when producing
`edges`; circular imports are recorded in `cycles`, never treated as errors.
Unused-export detection is internal only — nothing about it is emitted.

### `LocalScopeWalker`

Local-scope walker. Tracks function/method/arrow scopes only (no block
scopes), plus one synthetic module scope per file. Variables carry
`isParameter`, `isMutable` (const vs let/var; `this` parameters are
immutable), and `reassignments` — every reassignment site of a mutable
binding is a flow-termination point where downstream walking stops.

```ts
class LocalScopeWalker {
    addFile(sourceFile: ts.SourceFile): void;         // call per file
    build(resolver?: ScopeTypeResolver): ScopeAnalysis;
    findHolderScopeId(location: string): string | undefined;

    static attachHolderScopeIds(usages: Map<string, UsageInfo[]>, walker: LocalScopeWalker): void;
}

interface ScopeTypeResolver {
    resolveByName(name: string): string | undefined;  // bare name → mnemonica fullPath
    hasPath(fullPath: string): boolean;
}
```

`ScopeAnalysis` = `{ scopes: Map<scopeId, ScopeInfo>, variables: Map<'scopeId#name', ScopeVariable> }`.
Scope ids: module scope = file path; function scopes = `file:line:col`.
Labels: functions by name, methods as `Class.method`, arrows by the binding
they are assigned to, anonymous holders as `file:line`. Never relies on
`node.parent` (program files can be unbound).

### `TypesWriter`

```ts
class TypesWriter {
    constructor(outputDir?: string);

    writeTypesFile(generated: GeneratedTypes): string;          // → outputDir/types.ts
    writeGlobalAugmentation(generated: GeneratedTypes): string; // → outputDir/index.d.ts
    writeTo(filename: string, content: string): string;         // → outputDir/<filename>

    writeDefinitionsFile(map: Map<string, DefinitionInfo>): string; // → outputDir/definitions.json
    writeUsagesFile     (map: Map<string, UsageInfo[]>):    string; // → outputDir/usages.json
    writeEDSFile        (map: Map<string, EDSInfo[]>):      string; // → outputDir/eds.json
    writeFlowFile       (map: Map<string, FlowInfo[]>):     string; // → outputDir/flow.json
    writeInstrumentationFile(points: InstrumentationPoint[], creationGraph?: CreationGraph): string; // → outputDir/instrumentation.json
    writeModulesFile      (graph: ModuleGraph):             string; // → outputDir/modules.json
    writeScopesFile       (analysis: ScopeAnalysis):        string; // → outputDir/scopes.json

    write(generated: GeneratedTypes): string; // legacy alias for writeTypesFile
    clean(): void;
    getOutputDir(): string;
}
```

### Types

`TacticaConfig`, `TypeNode`, `TypeGraph`, `PropertyInfo`, `ConstructorParamInfo`, `AnalyzeResult`, `AnalyzeError`, `GeneratedTypes`, `DefinitionInfo`, `UsageInfo`, `UsagesJson`, `DefinitionsJson`, `EDSInfo`, `EDSJson`, `EDSKind`, `FlowInfo`, `FlowJson`, `FlowKind`, `InstrumentationKind`, `InstrumentationScope`, `InstrumentationPoint`, `InstrumentationJson`, `ModuleBindingKind`, `ModuleImportKind`, `ModuleBinding`, `ModuleInfo`, `CrossModuleUsage`, `ModuleGraph`, `ModulesJson`, `ScopeKind`, `ScopeInfo`, `ScopeVariable`, `ScopeAnalysis`, `ScopesJson`, `CreationGraphNode`, `CreationGraphEdge`, `CreationAnchor`, `CreationGraph`, `TacticaPlugin`, `InstrumentationVocabulary` — all exported from `@mnemonica/tactica`. See [`src/types.ts`](src/types.ts) for the full schema. The `mergeTacticaPlugins(plugins)` helper merges plugin vocabulary the same way the analyzer does.

## EDS (Execution Data Storage) Tracking

When enabled, tactica detects execution-flow patterns alongside type definitions. Each detection emits a record into `.tactica/eds.json`.

| Function | EDS kind | Description |
|---|---|---|
| `wrap(fn)`, `wrapConstructorArg(fn, parent)`, `upgradeConstructorArg(arg, inst)`, `wrapInstanceMethods(obj)` | `wrap` | Wrap a function / constructor argument / instance methods for context propagation and tracing (`@mnemonica/dive`) |
| `current()`, `getErrorInstance(err)`, `getFlow(target?)` | `contextConsume` | Read the current context, the error-pinned instance, or the recorded flow (`@mnemonica/dive`) |
| `attachHooks(collection)` | `hookAttach` | Wire a TypesCollection to dive's lifecycle tracing (`@mnemonica/otel`) |

`eds.json` structure:

```json
{
    "version": "1.0",
    "generatedAt": "2026-05-22T…",
    "eds": {
        "UserEntity": [
            {
                "location": "/project/src/queue.ts:45:12",
                "kind": "wrap",
                "code": "wrap(process)",
                "targetType": "UserEntity"
            }
        ]
    }
}
```

`wrap` entries additionally carry graph-join fields (all optional, additive):

- `label` — the label string literal of `wrap(fn, …, 'label')` when statically visible.
- `callbackScopeId` — the scopeId (scopes.json) of the wrapped callback's own scope; the callback is what the wrapper runs, so graph consumers join on it first.
- `instanceArg` — the identifier passed as the instance/context argument (`user` in `wrap(fn, user)`), when it is one.
- `scopeId` — the scopeId of the scope holding the wrap call site (fallback join).
- `wrapsTypePath` — the mnemonica fullPath of the instance argument, resolved through the scope-variable chain (innermost binding wins; an untyped local shadows a typed outer one rather than being guessed).
- `via` — the location of the enclosing wrap site when the call is nested inside another wrapped body (or returns a function): the wrappers-graph generation chain is built from it.
- `scope` — the enclosing mnemonica type path. Lexical scoping (the owning `define()`/`lazy()` handler or `@decorate()`-ed class) wins; a wrap site outside any handler — the fire-and-forget-wrapper shape — is attributed through its instance/context argument (a tracked assignment like `const holder = new Holder(…)`, the enclosing function's parameter annotation resolved through the graph law, or a `let`/`var`/`const` declaration with an EXPLICIT type annotation like `let updateCommitted: LedgerUpdate;` — declaration-site typing only, no flow analysis), and nested sites (function-valued returns, lexically nested wraps) inherit the causing wrap site's scope down the `via` chain. An UNANNOTATED `let`/`var` still buckets under `unknown` (the analyzer does not track assignments flow-sensitively) — a `const` with an analyzable initializer stays the recommended discipline. Sites attributable to nothing stay under the `unknown` key with `scope` absent.

## Instrumentation Points

Tactica statically detects framework lifecycle crossroads — interceptors, guards, pipes, exception filters, middleware — purely syntactically (no type checker), and always emits `.tactica/instrumentation.json`. **Tactica core ships no framework vocabulary**: detection is driven entirely by plugins, so with no plugins loaded `points` is `[]`. Framework adapters ship a plugin; projects enable it through a `.tactica.js` (or `tactica.config.js`) config file next to `tsconfig.json`:

```js
// .tactica.js
module.exports = {
    plugins: [ '@mnemonica/example-adapter/tactica' ],
};
```

Plugin entries are module specifiers (required relative to the config file) or inline plugin objects. A plugin is a plain object:

```ts
interface TacticaPlugin {
    name?: string;
    // `implements X` heritage matches: interface identifier -> kind
    instrumentationInterfaces?: Record<string, InstrumentationKind>;
    // `@X(Impl)` decorator sites: decorator identifier -> kind
    useDecorators?: Record<string, InstrumentationKind>;
    // `{ provide: TOKEN, useClass: Impl }` registrations: token identifier -> kind
    appTokens?: Record<string, InstrumentationKind>;
    // factory calls inside listed decorators' args: factory method name ->
    // kind + which factory-call argument holds the target class (default 0)
    decoratorArgFactories?: Record<string, { kind: InstrumentationKind; targetArg?: number }>;
    // opt in to shape-based `consumer.apply(Mw).forRoutes(...)` detection
    middlewareWiring?: boolean;
}
```

Programmatic callers pass plugins directly: `new MnemonicaAnalyzer(program, plugins)` or `run({ …, plugins })`; config-file plugins append after programmatic ones, and later plugins override earlier ones on the same identifier key. Detection covers:

- **Heritage** — `class X implements <plugin-listed interface>` (matched by interface identifier name). Bare declarations carry scope `module` (attachment statically unknown).
- **Decorator sites** — plugin-listed decorators on classes, methods, or method parameters, including inline instances (`@Register(new Impl(…))`). One point per referenced class; scope is `controller:<Name>` or `method:<Class>.<method>` (parameter-decorated sites take the enclosing method's scope — the attachment is the handler, not the argument name).
- **Decorator-arg factories** — a `CallExpression` argument of the form `<anything>.<factory>(…)` inside a listed decorator's args (class, method, or parameter position), e.g. `@UsePipes(mvp.forType(Dto))` and the parameter form `@Body(mvp.forType(Entity, Dto))`: when `<factory>` is plugin-listed, a point of the configured `kind` is emitted with the class in `targetArg` (default 0) as the target. Factory calls whose method name is not listed are ignored, as are listed factories whose configured position is not an identifier. Points resolve `location`/`code` to the target's declaration and dedupe exactly like other decorator sites.
- **Global providers** — `{ provide: <plugin-listed token>, useClass: X }` object literals → scope `global`. `useExisting`/`useFactory` without `useClass` are skipped.
- **Middleware wiring** — `consumer.apply(Mw).forRoutes(...)` inside a class's `configure()` method → scope `module`, targets from `forRoutes` arguments when statically readable. Requires `middlewareWiring: true` from any loaded plugin.

When a referenced class is declared in the analyzed project, the point's `location`/`code` resolve to the class declaration; external classes keep the registration site. Points are deduped by `(kind, className, location, scope)` with `targets` merged — a class seen via both heritage and a decorator yields separate entries per scope, with the bare declaration carrying scope `module`.

`instrumentation.json` structure (v2):

```json
{
    "version": 2,
    "generatedAt": "2026-09-04T…",
    "points": [
        {
            "kind": "pipe",
            "className": "PayloadPipe",
            "location": "/project/src/user.controller.ts:49:2",
            "code": "@RegisterPipe(new PayloadPipe({ transform: true }))",
            "scope": "method:UserController.createUser",
            "targets": ["UserController"]
        }
    ],
    "creationGraph": {
        "nodes": [
            {
                "scopeId": "/project/src/main.ts",
                "name": "/project/src/main.ts",
                "kind": "module",
                "filePath": "/project/src/main.ts",
                "location": "/project/src/main.ts:1:1",
                "starter": true
            }
        ],
        "edges": [
            { "caller": "/project/src/main.ts", "callee": "/project/src/user.service.ts:26:2" }
        ],
        "anchors": [
            {
                "location": "/project/src/user.service.ts:29:24",
                "holderScopeId": "/project/src/user.service.ts:26:2",
                "typePath": "UserEntity.UserResponse",
                "constructorText": "user.UserResponse",
                "variable": "userResponse"
            }
        ]
    }
}
```

## Creation graph (inside-out walk)

The `creationGraph` key is the third phase of the instrumentation walker: it starts at the certain points — every `usages.json` `instantiation` entry (each carries a `holderScopeId` into `scopes.json`) — and walks **outward**: who invokes or references the holder function, crossing files through `modules.json` (re-export barrels chased to the origin module), until no callers remain. Terminals are the **starters** (application entry points); the walk never assumes a linear type Trie (mnemonica `strictChain: false` permits cycles and out-of-order construction), so traversal is cycle-guarded and every anchor records the constructor expression actually used.

- **Nodes** are scopes (`module` / `function` / `method` / `arrow`), labeled like `scopes.json`; `starter: true` marks nodes with no discovered callers.
- **Edges** point `caller → callee`, where the callee is closer to the creation site.
- **Anchors** pin each creation site to its holder scope: `typePath`, the `constructorText` used, `rooted: true` for module-scope creations (a legitimate root or a developer error — labeled, not policed), and a `variable`/`terminatedAt` pair from a documented heuristic: the variable declared in the holder scope on the same line as the creation (typePath must match when known), with `terminatedAt` being that variable's first reassignment site — the flow-termination point where the walk stops following the binding.

Deliberate approximations (name-based, no type checker): namespace imports count any reference to the alias once the namespace's module exposes the holder's export; method holders bind to their **class** name (that is what callers reference); any non-declaration identifier counts as a reference. Export wiring alone (`export { f }`, `export default f`) is not a caller — an importer's usage creates the edge.

## How It Works

1. **Parse** — load `tsconfig.json`, build a `ts.Program`, walk each source file's AST.
2. **Detect** — find `define()` and `@decorate()` calls, plus `lookup` lookups, `new` expressions, and EDS / flow patterns.
3. **Graph** — build a Trie of types in `TypeGraphImpl`, with parent links via the chain of `.define()` calls and `@decorate(Parent)` references.
4. **Generate** — emit `types.ts`, `registry.ts`, `index.ts` (default mode) or `index.d.ts` (legacy mode), plus `definitions.json`, `usages.json` (with `holderScopeId`), `flow.json`, `instrumentation.json`, `modules.json`, `scopes.json`, `hierarchy.json`/`hierarchy.txt`, and optionally `eds.json`.
5. **Write** — files land in the output directory (default `.tactica/`).

```
Type Hierarchy (Trie)
├── UserType
│   ├── properties: { name: string }
│   └── AdminType
│       ├── properties: { role: string }
│       └── SuperAdminType
│           └── properties: { permissions: string[] }
└── OrderType
    └── properties: { items: Item[] }
```

## Known Limitations

### Rest / spread parameters with tuple types

The analyzer cannot extract property types from rest parameters that use tuple types:

```ts
// ❌ Property types resolve to unknown
export const UserEntity = define('UserEntity', function (
    this: UserEntityInstance,
    ...args: [{ id: string; email: string; name: string }, ...unknown[]]
) {
    const data = args[0];
    Object.assign(this, data);
});
```

**Workaround:** use a direct parameter with the same type annotation.

### Deep nested property access

Multi-level property access in constructors falls back to `unknown`:

```ts
// ⚠️ this.name's inferred type is unknown
const UserType = define('UserType', function (this: any, data: { profile: { name: string } }) {
    this.name = data.profile.name;
});
```

**Workaround:** flatten the data structure or use a direct parameter.

### `exposeInstanceMethods` is not parsed

Mnemonica accepts the `exposeInstanceMethods` option at runtime, but tactica's `extractConfig()` only parses `strictChain` and `blockErrors` from `define()` options today. The runtime behavior is unaffected.

### Single-pass analysis without binding

The analyzer does not use `ts.Program.getTypeChecker()` for resolution. Plain TypeScript references in constructor signatures resolve through the importing file's import statements first, then its local declarations, and only then a unique same-named declaration across the scanned files — so a reference whose name is genuinely absent (or lives behind unresolvable specifiers) resolves to `unknown`, while a name several of your own files declare with no import to disambiguate fails hard (see above). References to mnemonica graph types follow the path-aware lookup law described above and fail hard instead of degrading to `unknown`.

Two expansion boundaries stay name-based and deliberate: **heritage** — `extends` chains are walked through the same import-aware machinery (depth-capped, cycle-guarded), but bases that resolve to an external/node_modules declaration or to a non-identifier expression (mixin calls like `extends mixin(X)`) are not followed — their inherited fields simply stay absent, same as before the walk existed. And **`typeof` fields** — only module-level const arrays with statically visible literal elements expand to the literal union, with the index suffix consumed entirely (`typeof statusList[number]` emits exactly `'active' | 'not_active' | 'hold'`, never `'hold'[number]`). Any assertion spelling is tracked (`[…] as const`, `satisfies`, `<const>[…]`), and signed numeric literals keep their sign (`-1 | 1`). Cross-file only when the const is imported by the declaring file. Every other `typeof` source — and any indexed-access target that fails to resolve — degrades the whole expression to `unknown`: an index suffix glued onto a fallback type (`unknown[number]`) is invalid TypeScript and is never emitted.

### Same-file interface merging is last-wins

Two same-named interfaces in ONE module are legal TypeScript declaration merging, and tactica does not treat them as ambiguity (the fatal class is same-named declarations across several files, unanchored by an import). Resolution keeps a single declaration per name per file, and it is the last one — members from earlier declarations are not combined:

```ts
// merged.ts — resolves to { b: number }; the `a: string` member is not picked up
export interface SharedShape { a: string; }
export interface SharedShape { b: number; }
```

**Workaround:** declare the merged shape once, or split the interfaces under distinct names and import the one you mean.

### Custom collection name conflicts

Custom collection types are isolated in the analyzer by their collection identity: each collection root lives under a `collectionId::`-prefixed full path, so two collections may both define a root type with the same name (e.g., both defining `'User'`) without overwriting each other — in the graph, in traversal, in `hierarchy.json`, and in generated output. By default custom-collection types are not emitted in `.tactica/types.ts` at all; with Option B they are emitted prefixed by their registry interface name, so they stay distinct there too.

## Troubleshooting

**Generated types are missing properties** — make sure the constructor function has either an explicit `this:` type annotation, or that the data parameter has an inline / aliased type (`{ id: string }` or `Foo` where `type Foo = { id: string }`). Property inference walks one level of indirection.

**`new user.AdminType()` shows red squiggles** — confirm `.tactica/types.ts` is in your `tsconfig.json` `include`. If you use `lookup`, also import `.tactica/registry.ts` somewhere.

**`mnemographica` (VS Code extension) shows no graph** — confirm `.tactica/definitions.json` and `.tactica/types.ts` exist; run `npx tactica --verbose` to see what was discovered.

**`@mnemonica/dive` users**: EDS data should appear in `.tactica/eds.json`. If it's missing, run with `--eds --verbose` to force-enable and check the log.

## Testing

```bash
npm test                  # mocha + chai, all suites
npm run test:coverage     # nyc text report
npm run test:coverage:html  # nyc html report
```

## Related Projects

- [mnemonica](https://github.com/wentout/mnemonica) — the instance-inheritance runtime that this generator targets
- [typeomatica](https://github.com/wentout/typeomatica) — companion runtime type guards (`@Strict`, `BaseClass`)
- [@mnemonica/topologica](https://github.com/mythographica/topologica) — filesystem-based type discovery (consumed by tactica's `--topologica` mode)
- [mnemographica](https://github.com/mythographica/mnemographica) — VS Code extension that consumes tactica's `.tactica/` output for IDE features

## License

MIT
