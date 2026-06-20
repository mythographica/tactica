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
| `usages.json` | always | One entry per type, value is an array of `{ location, kind, code }` records — where each type is instantiated, referenced, accessed, or looked up. Consumed by `mnemographica`'s Find References. |
| `flow.json` | always | Native instance-flow patterns (property reads/writes, method calls, destructuring, returns, spreads, etc.) per type. |
| `eds.json` | when EDS enabled | Execution-flow patterns (`wrap`, `link`, `getLastContext`, hook attachment, framework adapters). Consumed by tools that visualize execution chains. |

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

Chained calls (`define('A').define('B')`) and nested calls via variable references (`const A = define('A', …); A.define('B', …)`) are both supported.

### `@decorate()` decorator

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
| `this.x = data.field \|\| []` | type of the fallback expression |
| `this.x = data.field ? a : b` | type of the truthy branch |
| `Object.assign(this, data)` | all fields of `data`'s type annotation |
| async / sync constructor functions | same rules |

When inference fails the property's type falls back to `unknown` (or `any` in some Topologica paths) — safe, and you can refine manually.

## API Reference

### `MnemonicaAnalyzer`

```ts
class MnemonicaAnalyzer {
    constructor(program?: ts.Program);

    analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult;
    analyzeSource(sourceCode: string, fileName?: string): AnalyzeResult;

    resetUsages(): void;                    // call between definition pass and usage pass
    addTopologicaType(fullPath: string, node: TypeNode): void;

    getGraph(): TypeGraphImpl;
    getDefinitions(): Map<string, DefinitionInfo>;
    getUsages():      Map<string, UsageInfo[]>;
    getEDSUsages():   Map<string, EDSInfo[]>;
    getFlowUsages():  Map<string, FlowInfo[]>;
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

    static createNode(name, parent, sourceFile, line, column): TypeNode;
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

    write(generated: GeneratedTypes): string; // legacy alias for writeTypesFile
    clean(): void;
    getOutputDir(): string;
}
```

### Types

`TacticaConfig`, `TypeNode`, `TypeGraph`, `PropertyInfo`, `ConstructorParamInfo`, `AnalyzeResult`, `AnalyzeError`, `GeneratedTypes`, `DefinitionInfo`, `UsageInfo`, `UsagesJson`, `DefinitionsJson`, `EDSInfo`, `EDSJson`, `EDSKind`, `FlowInfo`, `FlowJson`, `FlowKind` — all exported from `@mnemonica/tactica`. See [`src/types.ts`](src/types.ts) for the full schema.

## EDS (Execution Data Storage) Tracking

When enabled, tactica detects execution-flow patterns alongside type definitions. Each detection emits a record into `.tactica/eds.json`.

| Function | EDS kind | Description |
|---|---|---|
| `wrap(fn)`, `wrapArgs(fn)`, `wrapInstanceMethods(obj)` | `wrap` | Wrap a function / arguments / instance methods for context propagation |
| `link(parent, child)`, `runWithInstance(inst, fn)` | `link` | Link two instances in the EDS chain |
| `getLastContext()`, `getErrorInstance(err)` | `contextConsume` | Read the current / error-attached EDS context |
| `enrichError(err, inst)` | `errorEnrich` | Attach an instance to an error |
| `attachHooks(types)` | `hookAttach` | Install hooks on the given types |
| `createDiveInterceptor()` | `adapterUse` | NestJS interceptor adapter |
| `createDivePlugin()` | `adapterUse` | Fastify plugin adapter |
| `createDiveMiddleware()` | `adapterUse` | Express middleware adapter |

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

## How It Works

1. **Parse** — load `tsconfig.json`, build a `ts.Program`, walk each source file's AST.
2. **Detect** — find `define()` and `@decorate()` calls, plus `lookup` lookups, `new` expressions, and EDS / flow patterns.
3. **Graph** — build a Trie of types in `TypeGraphImpl`, with parent links via the chain of `.define()` calls and `@decorate(Parent)` references.
4. **Generate** — emit `types.ts`, `registry.ts`, `index.ts` (default mode) or `index.d.ts` (legacy mode), plus `definitions.json`, `usages.json`, `flow.json`, and optionally `eds.json`.
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

The analyzer does not use `ts.Program.getTypeChecker()` for resolution, so cross-file type references in unusual shapes may resolve to `unknown`.

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
