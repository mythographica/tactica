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
├── topologica-analyzer.ts  # AST analyzer for Topologica directory structures
├── graph.ts                # Trie-based TypeGraphImpl
├── generator.ts            # generates types.ts / registry.ts / index.d.ts
├── writer.ts               # writes .tactica/* files
└── cli.ts                  # CLI entry point, parseArgs, run, watch, main
```

No `plugin.ts`. There is no plugin code anywhere.

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
    type UserType = { … };
    interface UserType { … } // declaration-merging shape for @decorate classes
}
```

Single file; types are global. Consumed via triple-slash reference or `typeRoots`. Source: `TypesGenerator.generateGlobalAugmentation()` → `TypesWriter.writeGlobalAugmentation()`.

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

`kind ∈ 'wrap' | 'link' | 'contextConsume' | 'errorEnrich' | 'hookAttach' | 'adapterUse'`. Auto-enabled when `@mnemonica/dive` is in `package.json` dependencies; `--eds` / `--no-eds` override.

## Key classes (quick reference)

### `MnemonicaAnalyzer`

Parses TS/JS source via the TS compiler API; populates a `TypeGraphImpl` and four usage maps.

- `analyzeFile(sourceFile)` — analyze one `ts.SourceFile`.
- `analyzeSource(code, fileName?)` — analyze a string of source code.
- `resetUsages()` — clear usage/EDS/flow maps before the second pass (the CLI runs definitions first, then usages).
- `addTopologicaType(fullPath, node)` — inject a topologica-discovered type into the graph + definitions.
- Getters: `getGraph`, `getDefinitions`, `getUsages`, `getEDSUsages`, `getFlowUsages`.

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

- `writeTypesFile`, `writeGlobalAugmentation`, `writeDefinitionsFile`, `writeUsagesFile`, `writeEDSFile`, `writeFlowFile`, `writeTo(filename, content)`.
- `write(generated)` is a legacy alias for `writeTypesFile`.
- `clean()` empties the output directory; `getOutputDir()` returns the configured path.

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

- Default (no `--module-augmentation`): writes `types.ts` + `registry.ts` + `index.ts` (+ `definitions.json`, `usages.json`, `flow.json`, optional `eds.json`).
- With `--module-augmentation`: writes `index.d.ts` (+ same JSONs). Default mode is the recommended path.

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
- `@decorate()`, `@decorate(Parent)`, `@decorate({…options})`, `@decorate(Parent, {…options})`.
- `Object.assign(this, data)` (extracts from `data`'s type annotation).
- Direct parameter access (`this.name = name`) and one-level data access (`this.id = data.id`).
- Arithmetic, template literals, built-in calls (`Date.now`, `parseInt`, `String`, …), `new` expressions on built-ins, ternary, logical-OR fallback.
- Async constructor functions.
- `as TypeConstructor<{…}>` casting (and `as ConstructorFunction<{…}>` legacy alias) for plain function constructors.
- Typeomatica `@Strict` decorator alongside `@decorate`; `Object.setPrototypeOf(MyType.prototype, new BaseClass(…))`.

Falls back to `unknown` when inference fails.

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
