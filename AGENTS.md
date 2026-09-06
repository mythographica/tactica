# AGENTS.md

Guidance for AI agents working in this repository. Keep responses tight, prefer code over prose.

## What tactica is (and isn't)

**Is:** a CLI tool + Node library that statically analyzes TypeScript/JavaScript source and generates type definitions plus navigation metadata for Mnemonica's dynamic types. Output lives in `.tactica/`.

**Isn't:** a TypeScript Language Service Plugin. There is no `create(info)` factory, nothing for `tsserver` to load. IDE features (Go to Definition, Find References, graph visualization) are provided by the **mnemographica** VS Code extension, which consumes tactica's `.tactica/*.json` output. If you find docs or tests that imply a plugin exists in this repo, they are stale — please correct them.

## Role in the ecosystem

```
┌───────────────────────────────────────┐
│   User code (TS/JS using mnemonica)   │
└────────────────┬──────────────────────┘
                 │ parsed by
                 ▼
┌───────────────────────────────────────┐
│            tactica (this repo)        │
│   CLI + library — code generator      │
└────────────────┬──────────────────────┘
                 │ writes to disk
                 ▼
┌───────────────────────────────────────┐
│   .tactica/  output (contract below)  │
└───┬─────────────────┬─────────────────┘
    │                 │
    │ imported by tsc │ read by mnemographica (VS Code extension)
    ▼                 ▼
typed mnemonica   Go to Def · Find Refs · Graph view
```

## Build / Test

```bash
npm run build              # rm -rf lib && tsc && chmod +x lib/cli.js
npm test                   # mocha + chai
npm run test:coverage      # nyc text + text-summary
npm run test:coverage:html # nyc html report
npm run watch              # tsc -w
npm run lint               # eslint --fix src
```

Local-vs-public dependency switching:

```bash
npm run use:public  # peer/dev/dep → 'latest' from npm
npm run use:local   # peer/dev/dep → file:../core, file:../typeomatica
```

`use:public` is the right state for any release work. `use:local` is for ecosystem-wide development.

## Source layout

```
src/
├── index.ts                # public exports (analyzer, generator, writer, CLI, types)
├── types.ts                # all interface / type definitions
├── analyzer.ts             # AST analyzer for define()/decorate() + usage/EDS/flow collection
├── module-graph.ts         # Module-scope walker: import/export bindings, resolution, cycles → modules.json
├── scopes.ts               # Local-scope walker: function/method/arrow scopes, variables, reassignments → scopes.json
├── creation-graph.ts       # Inside-out creation walker: instantiation anchors → caller chains → starters → instrumentation.json creationGraph
├── plugins.ts              # TacticaPlugin interface + mergeTacticaPlugins — framework instrumentation vocabulary
├── topologica-analyzer.ts  # AST analyzer for Topologica directory structures
├── graph.ts                # Trie-based TypeGraphImpl
├── generator.ts            # generates types.ts / registry.ts / index.d.ts
├── writer.ts               # writes .tactica/* files
└── cli.ts                  # CLI entry point, parseArgs, run, watch, main
```

## Framework vocabulary is plugin-supplied

Tactica core is **framework-blind**: it ships no instrumentation vocabulary of its own. The analyzer's four detection channels (heritage interfaces, decorator sites, provider tokens, middleware wiring) read a merged plugin vocabulary (`src/plugins.ts`); with no plugins loaded, `instrumentation.json` carries `points: []`. Framework adapter packages ship a plugin; projects enable it via a `.tactica.js` / `tactica.config.js` config file next to their tsconfig (`module.exports = { plugins: [ 'adapter-package/tactica' ] }` — string specifiers are required relative to the config file; inline objects also work). The CLI appends config plugins after programmatic `run({ plugins })` entries. Never hardcode framework identifier names into `src/` — they belong in adapter packages.

## Code style

- **Tabs** for indentation, size 4.
- **Space before `(`** in function declarations: `function foo ()`, not `function foo()`.
- TypeScript strict mode is on (`noUnusedLocals`, `noUnusedParameters`, `isolatedModules`).
- Prefer intermediate variables before return for debuggability:
  ```ts
  const result = this.service.doSomething();
  return result;
  ```

## Output contract (consumed by downstream tools)

Tactica writes to `--output` (default `.tactica/`). The contract below is what **mnemographica** and other consumers depend on. Do not break these field names or the file naming without coordinated changes in mnemographica.

### `types.ts` (default mode)

```ts
import type { ProtoFlat } from 'mnemonica';

export type UserType = {
    name: string;
    AdminType: new (data: { role: string }) => UserType_AdminType;
};

export type UserType_AdminType = ProtoFlat<UserType, {
    role: string;
    AdminType: undefined;
}>;
```

- One `export type` per discovered type, named `<DottedPath>` with `.` → `_`.
- Nested types use `ProtoFlat<Parent, Self>` so overridden parent properties are excluded.
- Each nested type emits its own constructor name as `undefined` (strict-chain marker) and similar for siblings.
- Source: `TypesGenerator.generateTypesFile()` → `TypesWriter.writeTypesFile()`.

### `registry.ts` (default mode)

```ts
import type { UserType, UserType_AdminType } from './types';

declare module 'mnemonica' {
    interface TypeRegistry {
        'UserType': new (data: { name: string }) => UserType;
        'UserType.AdminType': new (data: { role: string }) => UserType_AdminType;
    }
}

import type { TypeRegistry } from 'mnemonica';
export type { TypeRegistry };
```

- Module augmentation of `mnemonica.TypeRegistry`.
- Keys are full dotted paths (`'A.B.C'`); values are typed constructors that return the corresponding instance type.
- Source: `TypesGenerator.generateTypeRegistry()` → `TypesWriter.writeTo('registry.ts', …)`.

### `index.ts` (default mode)

```ts
export * from './types';
export * from './registry';
```

In ESM mode (`--esm`) the imports gain `.js` extensions.

### `index.d.ts` (legacy `--module-augmentation` mode)

```ts
import type { ProtoFlat } from 'mnemonica';
export {};
declare global {
    interface UserType { … }        // all types, merges with @decorate classes
    type UserType_AdminType = ProtoFlat<UserType, { … }>; // nested types only
}
```

Single file; types are global. Consumed via tsconfig `include` (typeRoots does
not pick it up — `.tactica` is not a package folder). Root types are declared
ONLY as interfaces: a same-named `type` alias would collide with the merging
interface in the same global scope (TS2300). Nested types keep their
`ProtoFlat` aliases (interfaces cannot express computed types) and carry their
children's constructor signatures, same as `types.ts`. Source:
`TypesGenerator.generateGlobalAugmentation()` → `TypesWriter.writeGlobalAugmentation()`.

### `hierarchy.json` (always)

```json
{
    "version": "1.0",
    "generatedAt": "2026-05-22T…",
    "roots": [
        {
            "name": "UserType",
            "fullPath": "UserType",
            "location": "/abs/path/src/users.ts:10:7",
            "children": [
                {
                    "name": "AdminType",
                    "fullPath": "UserType.AdminType",
                    "location": "/abs/path/src/users.ts:20:7",
                    "children": []
                }
            ]
        }
    ]
}
```

- Structured Trie representation of the type graph. Each node carries the same `name`, `fullPath`, and `location` data as `definitions.json`, but organized as parent/children.
- **Consumed by:** downstream graph visualizations and by agents that need to understand the mnemonica hierarchy without parsing ASCII art.
- Source: `TypeGraphImpl.toHierarchy()` → `TypesWriter.writeHierarchyFile()`.

### `hierarchy.txt` (always)

ASCII tree rendering of the same Trie that `cli.ts` prints under `--verbose`. Saved to disk so it can be read, diffed, or committed independently of terminal output.

### `definitions.json` (always)

```json
{
    "version": "1.0",
    "generatedAt": "2026-05-22T…",
    "definitions": {
        "UserType": {
            "name": "UserType",
            "location": "/abs/path/src/users.ts:10:7",
            "kind": "define",
            "parent": null,
            "strictChain": true,
            "blockErrors": false
        },
        "UserType.AdminType": { … }
    }
}
```

- `kind` is `"define" | "decorate"`.
- `location` is `<file>:<1-based-line>:<1-based-column>`.
- `parent` is the parent's full path or `null` for root types.
- **Consumed by:** `mnemographica/src/providers/definitionProvider.ts` (Go to Definition), `mnemographica/src/models/Registry.ts` (registry view).

### `usages.json` (always)

```json
{
    "version": "1.0",
    "generatedAt": "2026-05-22T…",
    "usages": {
        "UserType": [
            { "location": "/abs/path/src/main.ts:3:7", "kind": "instantiation", "code": "new UserType({…})" },
            { "location": "/abs/path/src/main.ts:5:9", "kind": "propertyAccess", "code": "user.AdminType" }
        ]
    }
}
```

- `kind` is one of `'instantiation' | 'typeAnnotation' | 'propertyAccess' | 'lookup' | 'reference'`.
- `holderScopeId` (optional, additive) is the innermost local scope holding the usage — the scopeId from `scopes.json` (module scope = file path; function scopes = file:line:col). Present for every usage inside a tracked file.
- `constructorText` (optional, additive; instantiations only) is the constructor expression text actually used (`'Thing'`, `'user.AdminEntity'`, a lookup alias name) — feeds the creation graph's anchors.
- **Consumed by:** `mnemographica/src/providers/referenceProvider.ts` (Find All References).

### `flow.json` (always)

Native-instance flow patterns (property reads/writes, method calls, destructures, returns, spreads, reassignments, instantiations, conditional and element access). Same shape as `usages.json` but keyed by `FlowKind`.

### `eds.json` (when EDS enabled)

```json
{
    "version": "1.0",
    "generatedAt": "2026-05-22T…",
    "eds": {
        "UserEntity": [
            { "location": "/abs/path/src/queue.ts:45:12", "kind": "wrap", "code": "wrap(process)", "targetType": "UserEntity" }
        ]
    }
}
```

`kind ∈ 'wrap' | 'contextConsume' | 'hookAttach'`. Auto-enabled when `@mnemonica/dive` is in `package.json` dependencies; `--eds` / `--no-eds` override.

`wrap` entries also carry the wrappers-graph join fields (all optional, additive): `label` (the string-literal label arg), `callbackScopeId` (the wrapped callback's own scopeId — the preferred creation-graph join), `instanceArg` (the instance/context identifier text), `scopeId` (the scope holding the wrap call site — fallback join), `wrapsTypePath` (the instance argument's mnemonica fullPath, resolved through the scope-variable chain — innermost binding wins, untyped shadowing stays untyped), `via` (the enclosing wrap site's location for textually nested wraps and function-valued returns — the generation chain), and `fn` (the wrap-family function name — `wrap`/`wrapConstructorArg`/`upgradeConstructorArg`/`wrapInstanceMethods`; return-chain entries are `fn: 'wrap'` — joins the call site to dive's engine knot in graph consumers). `scopeId`/`wrapsTypePath` are a CLI post-pass (`attachWrapJoinData` in `src/cli.ts`); the rest come from the analyzer's wrap branch.

### `instrumentation.json` (always)

```json
{
    "version": 2,
    "generatedAt": "2026-09-04T…",
    "points": [
        {
            "kind": "pipe",
            "className": "ValidationPipe",
            "location": "/abs/path/src/user.controller.ts:49:2",
            "code": "@UsePipes(new ValidationPipe({ transform: true }))",
            "scope": "method:UserController.createUser",
            "targets": ["UserController"]
        }
    ],
    "creationGraph": {
        "nodes": [
            {
                "scopeId": "/abs/path/src/main.ts",
                "name": "/abs/path/src/main.ts",
                "kind": "module",
                "filePath": "/abs/path/src/main.ts",
                "location": "/abs/path/src/main.ts:1:1",
                "starter": true
            }
        ],
        "edges": [
            { "caller": "/abs/path/src/main.ts", "callee": "/abs/path/src/user.service.ts:26:2" }
        ],
        "anchors": [
            {
                "location": "/abs/path/src/user.service.ts:29:24",
                "holderScopeId": "/abs/path/src/user.service.ts:26:2",
                "typePath": "UserEntity.UserResponse",
                "constructorText": "user.UserResponse",
                "variable": "userResponse"
            }
        ]
    }
}
```

- **Points (v1 contract, unchanged):** framework lifecycle crossroads detected syntactically (no type checker, no dive dependency), driven by the merged plugin vocabulary: heritage (`implements` a plugin-listed interface), decorator sites (plugin-listed decorators, incl. `new X(...)` args), provider-token object literals (`{ provide: TOKEN, useClass: X }`, scope `global`), and `consumer.apply(Mw).forRoutes(...)` inside `configure()` (scope `module`; requires a plugin with `middlewareWiring: true`). No plugins → `points: []`.
- `scope` ∈ `'global' | 'module' | 'controller:<Name>' | 'method:<Class>.<method>'`; a bare heritage declaration carries scope `'module'` (attachment statically unknown).
- Points referencing a class declared in the analyzed project resolve `location`/`code` to the class declaration; external classes keep the registration site. Deduped by `(kind, className, location, scope)` with `targets` merged — heritage + decorator for the same class yields separate entries per scope (documented on `InstrumentationPoint` in `src/types.ts`).
- **`creationGraph` (v2, always present from the CLI):** the inside-out walk — anchors are the `instantiation` usages (each pinned to its `holderScopeId`), edges point `caller → callee` (callee closer to the creation site), nodes with no discovered callers are `starter: true`. Module-scope creations are `rooted: true` anchors (labeled, not policed). Module scopes end the invocation walk, but a terminal module gains its IMPORTERS as callers (the exports-and-usage bridge): entry modules hand classes to frameworks as values — a bootstrap call receiving the root module — which no call-walk can see, so the import relation connects them to the center instead. `constructorText` records the constructor expression actually used (decision 1: `strictChain: false` permits non-linear construction); `variable`/`terminatedAt` come from the same-line variable heuristic, `terminatedAt` being the first reassignment site (decision 6 flow termination). Deliberate approximations: namespace imports count any alias reference; method holders bind to their class name; any non-declaration identifier counts as a reference; export wiring alone creates no edge.
- **Consumed by:** mnemographica's creation graph layer — holder scopes render as diamond knots tangent to their created type's sphere (the v1-points diamond rendering was reverted; diamonds carry creation semantics now). `loadInstrumentation()` ignores `version` and unknown top-level keys, so v2 is backward compatible.
- Source: points from `MnemonicaAnalyzer.getInstrumentationPoints()`, creation graph from `CreationGraphBuilder` (`src/creation-graph.ts`) → `TypesWriter.writeInstrumentationFile(points, creationGraph)`.

### `modules.json` (always)

```json
{
    "version": "1.0",
    "generatedAt": "2026-09-03T…",
    "modules": {
        "/abs/path/src/fake-queue.ts": {
            "filePath": "/abs/path/src/fake-queue.ts",
            "definedTypes": [],
            "exportedBindings": [
                { "name": "consumeMessage", "kind": "function", "sourceModule": "/abs/path/src/fake-queue.ts", "isReExport": false }
            ],
            "importedBindings": [
                { "name": "Thing", "kind": "class", "sourceModule": "/abs/path/src/defs.ts", "importKind": "named", "isReExport": false }
            ],
            "dependencies": ["/abs/path/src/defs.ts"],
            "unresolvedSpecifiers": []
        }
    },
    "edges": [
        { "typePath": "Thing", "definitionModule": "/abs/path/src/defs.ts", "usageModule": "/abs/path/src/consumer.ts", "usageLocation": "/abs/path/src/consumer.ts:1:10" }
    ],
    "cycles": [["/abs/a.ts", "/abs/b.ts"]]
}
```

- Module-scope graph: every module's **generic** import/export wiring — functions, classes, consts, types — not only mnemonica types. Function bindings (`kind: "function"`) are the holder-function wiring the inside-out walker follows.
- `definedTypes` holds the mnemonica type fullPaths defined in that module; `edges` records cross-module usages of those types (import binding chased through re-export barrels to the origin module).
- `sourceModule` on imports is resolved via `ts.resolveModuleName` with the program's compilerOptions (tsconfig `paths`, extensionless imports, index files) — module resolution, NOT the type checker; the no-`getTypeChecker()` precedent stays.
- **Node.js builtins are skipped entirely** (both `'path'` and `'node:path'` forms, matched against `node:module`'s `builtinModules`): no bindings, no dependencies, no edges — they appear only in the module's `builtinSpecifiers: string[]` honesty list.
- **External packages** (specifiers resolved with `isExternalLibraryImport`, i.e. node_modules) keep their resolved `.d.ts` path in `sourceModule` and are marked `external: true` on the binding; they never enter `dependencies` (project-internal only) and are never walked. Genuinely unresolvable specifiers stay raw in `sourceModule` and are listed in `unresolvedSpecifiers`.
- `cycles` records circular import chains as data — never an error (mnemonica `strictChain: false` permits non-linear construction; the walker must not assume a linear Trie). Unused-export detection is internal only — nothing about it is emitted (linter territory).
- Source: `ModuleGraphBuilder` (`src/module-graph.ts`; `addFile()` during the CLI definitions pass, `build(definedTypesByFile)` after) → `TypesWriter.writeModulesFile()`.

### `scopes.json` (always)

```json
{
    "version": "1.0",
    "generatedAt": "2026-09-03T…",
    "scopes": {
        "/abs/path/src/fake-queue.ts": {
            "scopeId": "/abs/path/src/fake-queue.ts",
            "name": "/abs/path/src/fake-queue.ts",
            "kind": "module",
            "filePath": "/abs/path/src/fake-queue.ts",
            "location": "/abs/path/src/fake-queue.ts:1:1"
        },
        "/abs/path/src/fake-queue.ts:30:1": {
            "scopeId": "/abs/path/src/fake-queue.ts:30:1",
            "name": "consumeMessage",
            "kind": "function",
            "parentScopeId": "/abs/path/src/fake-queue.ts",
            "filePath": "/abs/path/src/fake-queue.ts",
            "location": "/abs/path/src/fake-queue.ts:30:1"
        }
    },
    "variables": [
        {
            "name": "early",
            "scopeId": "/abs/path/src/fake-queue.ts:30:1",
            "typePath": "UserEntity",
            "inferredType": "UserEntity",
            "declaration": "/abs/path/src/fake-queue.ts:32:8",
            "isParameter": false,
            "isMutable": false,
            "reassignments": []
        }
    ]
}
```

- Local-scope graph: **function/method/arrow scopes ONLY — no block scopes** (decision: block-level granularity rejected after the module PoC showed function-granular holders suffice). One synthetic `kind: "module"` scope per file roots the tree, so module-level instance creations are labeled as rooted instances instead of disappearing.
- Scope labeling: functions by name, methods as `Class.method`, arrows/function-expressions take the variable or property they are bound to, anonymous holders are labeled `file:line`.
- Variables carry `isParameter`, `isMutable` (`const` = false; `let`/`var` and parameters = true — parameters are reassignable; `this` parameters of mnemonica handlers are recorded as immutable), and `reassignments`: every reassignment site of the binding. A reassignment is a **flow-termination point** — the inside-out walker stops following that binding there. Property writes (`x.prop = …`) are not reassignments; only rebindings (all assignment operators plus `++`/`--`).
- `typePath` is the mnemonica fullPath when knowable without the type checker: `new KnownType(…)`, `new instance.Sub.Type(…)` chained through a tracked variable's typePath, an underscore annotation (`UserEntity_UserResponse` → dotted), or a `lookup('Path')` initializer (literal paths only; `receiver.lookup('Sub')` resolves receiver-relative first, then root fallback — mirroring the analyzer). Ambiguous names resolve to nothing rather than guessing.
- Implementation detail: program source files can be unbound (no `node.parent`); the walker never relies on parent pointers (declaration-list flags and a bound-name map instead).
- Source: `LocalScopeWalker` (`src/scopes.ts`; `addFile()` per file, `build(resolver)` once definitions are known) → `TypesWriter.writeScopesFile()`. `LocalScopeWalker.attachHolderScopeIds(usages, walker)` decorates usages before `usages.json` is written.

## Key classes (quick reference)

### `MnemonicaAnalyzer`

Parses TS/JS source via the TS compiler API; populates a `TypeGraphImpl` and four usage maps.

- `analyzeFile(sourceFile)` — analyze one `ts.SourceFile`.
- `analyzeSource(code, fileName?)` — analyze a string of source code.
- `resetUsages()` — clear usage/EDS/flow maps before the second pass (the CLI runs definitions first, then usages).
- `addTopologicaType(fullPath, node)` — inject a topologica-discovered type into the graph + definitions.
- Getters: `getGraph`, `getDefinitions`, `getUsages`, `getEDSUsages`, `getFlowUsages`, `getInstrumentationPoints`.

JavaScript files work when `allowJs: true` is in the user's `tsconfig.json`. The same AST visitors run on JS — type inference is naturally weaker without annotations.

### `TopologicaAnalyzer`

Scans a directory tree where each subdirectory represents a type and `index.ts` / `index.js` / `index.mjs` exports a handler function. Extracts properties from `this.x = …` assignments and `Object.assign(this, …)` patterns, with a small literal-type inference table.

- `analyzeDirectory(path)` → `{ types: Map<string, TypeNode>, errors: string[] }`.
- `getGraph()`, `getErrors()`.

### `TypeGraphImpl`

Trie-based hierarchy. `roots` (top-level) and `allTypes` (by full dotted path). Helpers: `addRoot`, `addChild`, `findType`, `findTypeByName`, `getAllTypes`, `clear`, `*bfs()`, `*dfs()`, and the static `createNode(name, parent, sourceFile, line, column)` factory.

### `TypesGenerator`

- `generateTypesFile()` → default-mode `types.ts` content.
- `generateTypeRegistry()` → default-mode `registry.ts` content.
- `generateGlobalAugmentation()` → legacy-mode `index.d.ts` content.
- `generateSingleType(node)` → one type's text.
- Constructor takes `(graph, esm = false)`; `esm: true` appends `.js` to relative imports.

### `TypesWriter`

Thin filesystem wrapper. One method per output file:

- `writeTypesFile`, `writeGlobalAugmentation`, `writeDefinitionsFile`, `writeUsagesFile`, `writeEDSFile`, `writeFlowFile`, `writeInstrumentationFile`, `writeModulesFile`, `writeScopesFile`, `writeHierarchyFile`, `writeTo(filename, content)`.
- `write(generated)` is a legacy alias for `writeTypesFile`.
- `clean()` empties the output directory; `getOutputDir()` returns the configured path.

### `CreationGraphBuilder`

Inside-out creation walker (instrumentation walker plan, Phase 3).

- Constructor: `(moduleGraph, scopeAnalysis, scopeWalker, sourceFilesByPath)` — the BUILT module graph, the BUILT scope analysis, the walker (for `findHolderScopeId`), and program source files keyed by `path.resolve(fileName)`.
- `build(usages)` → `CreationGraph` (nodes / edges / anchors; empty arrays when nothing instantiates a tracked type). Expects `holderScopeId` already attached (`LocalScopeWalker.attachHolderScopeIds`).
- Caller search is parent-pointer-free (program files can be unbound): identifier references are bucketed per file with a NODE skip-set for import/export specifiers, declaration names, property-access `.name`, and property-assignment keys. Shorthand properties count as references.
- Cross-file chase mirrors `ModuleGraphBuilder.resolveOrigin` (barrels, `export *`, aliases), run over the built graph.

## CLI options

```
-w, --watch                 Watch mode
-p, --project <path>        Path to tsconfig.json (default: nearest ancestor)
-o, --output <dir>          Output directory (default: .tactica)
-i, --include <patterns>    Comma-separated include patterns
-e, --exclude <patterns>    Comma-separated exclude patterns
-t, --topologica <dirs>     Comma-separated Topologica directories
-m, --module-augmentation   Legacy mode — emit single .tactica/index.d.ts
    --esm                   Append .js to relative imports (NodeNext ESM)
    --eds                   Force-enable EDS tracking
    --no-eds                Force-disable EDS tracking
-v, --verbose               Verbose logging
-h, --help                  Show help
```

**Mode behavior:**

- Default (no `--module-augmentation`): writes `types.ts` + `registry.ts` + `index.ts` (always + `definitions.json`, `usages.json`, `flow.json`, `instrumentation.json`, `modules.json`, `scopes.json`, `hierarchy.json`, `hierarchy.txt`; optional `eds.json`).
- With `--module-augmentation`: writes `index.d.ts` (+ same JSONs). Default mode is the recommended path.

**Exclusion behavior:** the project-conventional `.tactica/` directory (next to the tsconfig) is ALWAYS excluded from analysis, even when `--output` points elsewhere — generated files are never project source. When `--output` is used, that output directory is excluded too. No env variable; the flag is enough.

The flag name `--module-augmentation` is historical; what it actually does is emit a **global**-augmentation single file. Renaming would be a breaking change to existing scripts.

## Testing

Mocha + chai, files in `test/**/*.test.ts`. `tsconfig.test.json` extends the main tsconfig but disables `noUnusedLocals/noUnusedParameters` and sets `noEmit`.

**Hard rule:** never use `node -e`. Write a real test file in `test/` and run with `npm test` or `node /tmp/foo.js`. `node -e` blocks waiting for stdin in automation.

After changing analyzer behavior:

1. Run `npm test` and `npm run test:coverage`.
2. Re-read the "What Gets Analyzed" / "Property Type Inference" sections of `README.md`.
3. If new capabilities or new limitations exist, update both README and this file in the same commit.

## Supported patterns (the analyzer recognizes these)

- `define('TypeName', handler)` — root or nested via `Parent.define(…)` or chained `define(…).define(…)`.
- `lazy('TypeName', getter)` — all forms: free `lazy(...)`, method `Type.lazy(...)`, and chained `define('A').lazy('B', getter)`. The getter is followed and the returned constructor is analyzed like a direct `define()` handler (properties and constructor parameters extracted).
- Builder pattern on the imported `mnemonica` module object: `mnemonica.define('A').define('B')`, `const App = mnemonica; App.define('C')`, `App.lookup('A').define('D')`. Module object aliases from imports (`import { mnemonica as m }`, `import * as mnemonica`, default import) and variable aliases are tracked.
- Explicit-source APIs: `define(source, 'TypeName', handler)` and `lookup(source, 'TypeName')`, where `source` is a module object, custom collection, or type variable.
- Custom collections: `createTypesCollection()` results are tracked. Types defined on a collection live in the graph under a `collectionId::`-prefixed full path; they are **not** emitted in `.tactica/types.ts` and **not** added to the global `TypeRegistry` augmentation unless the collection declares a registry interface (Option B, `createTypesCollection<Registry>()`) — then they emit prefixed with the interface name plus a per-collection augmentation. Subtypes inherit the collection from their parent.
- `@decorate()`, `@decorate(Parent)`, `@decorate({…options})`, `@decorate(Parent, {…options})`.
  - `Parent` is resolved through the variable map, so aliases work: `const User = define('UserEntity', …); @decorate(User)` produces `UserEntity.<ClassName>`.
  - Options are reflected in `definitions.json` (`strictChain`, `blockErrors`).
  - Constructor parameters are extracted from decorated classes and emitted in `registry.ts` / `types.ts` signatures.
- `Object.assign(this, data)` (extracts from `data`'s type annotation).
- Direct parameter access (`this.name = name`) and one-level data access (`this.id = data.id`).
- Arithmetic, template literals, built-in calls (`Date.now`, `parseInt`, `String`, …), `new` expressions on built-ins, ternary, logical-OR fallback.
- Async constructor functions.
- `as TypeConstructor<{…}>` casting (and `as ConstructorFunction<{…}>` legacy alias) for plain function constructors.
- Typeomatica `@Strict` decorator alongside `@decorate`; `Object.setPrototypeOf(MyType.prototype, new BaseClass(…))`.

Falls back to `unknown` when inference fails.

## Known limitations

- Rest/tuple parameters, deep nested property access, and `exposeInstanceMethods` parsing — see README.md.
- Same-name roots in different custom collections are fully isolated (graph roots are keyed by the `collectionId::`-prefixed full path; fixed 2026-08 — they used to collide and silently drop a subtree from generation and hierarchy output).

## Common contribution patterns

### Add a new analyzer feature

```ts
// In analyzer.ts visitNode():
if (this.isNewPattern(node)) {
    this.processNewPattern(node as ts.CallExpression, sourceFile);
}

private isNewPattern (node: ts.Node): boolean { /* detection */ }
private processNewPattern (call: ts.CallExpression, sf: ts.SourceFile): void { /* extract + add to graph */ }
```

### Work with the type graph

```ts
const graph = new TypeGraphImpl();
const root  = TypeGraphImpl.createNode('UserType', undefined, 'file.ts', 1, 1);
graph.addRoot(root);

const child = TypeGraphImpl.createNode('AdminType', root, 'file.ts', 5, 1);
graph.addChild(root, child);

for (const node of graph.bfs()) {
    console.log(node.fullPath);
}
```

### Generate output

```ts
const generator = new TypesGenerator(graph);
const writer    = new TypesWriter('.tactica');

writer.writeTypesFile(generator.generateTypesFile());
writer.writeTo('registry.ts', generator.generateTypeRegistry().content);
```

## Known limitations

- **Rest/tuple parameters** — `...args: [Data, ...unknown[]]` and then `args[0]` is not tracked. Use a direct named parameter.
- **Multi-level property access** — `this.x = data.profile.name` resolves `this.x` to `unknown`. Flatten or use a direct parameter.
- **No `getTypeChecker()` binding** — cross-file resolution uses name-based heuristics, not the real symbol table.
- **`exposeInstanceMethods` is not parsed** from `define()` options. Mnemonica accepts it at runtime; tactica ignores it.

## Related projects

- **mnemonica** (`../core`) — the inheritance runtime tactica targets.
- **typeomatica** (`../typeomatica`) — companion runtime type guards.
- **topologica** — filesystem-based type discovery (tactica's `--topologica` flag consumes this convention).
- **mnemographica** (`../mnemographica`) — VS Code extension; consumes `.tactica/*.json`.

## Resources

- [TypeScript Compiler API](https://github.com/microsoft/TypeScript/wiki/Using-the-Compiler-API)
- mnemonica README: `../core/README.md`
- mnemographica README: `../mnemographica/README.md`
