---
name: mnemonica-tactica
description: |
  Static type generator for mnemonica projects. Use when a project uses
  mnemonica and needs typed lookup(), TypeRegistry augmentation, or
  generated instance types; when `define()`/`lazy()`/`@decorate()` calls
  should become visible to TypeScript; or when the user mentions tactica,
  .tactica output, types.ts / registry.ts generation, or type-safe
  mnemonica navigation.
metadata:
  tags: [mnemonica, typescript, codegen, type-system, ast, nodejs]
---

# tactica — usage skill for agents

tactica reads TypeScript/JavaScript source that uses mnemonica and
generates the types TypeScript cannot infer from runtime calls:
`.tactica/types.ts` (instance types), `.tactica/registry.ts` (module
augmentation of mnemonica's `TypeRegistry`), plus JSON metadata
(definitions, usages, hierarchy, scopes, modules, flow, instrumentation)
consumed by editor extensions and other tools.

## When to use

- The project depends on `mnemonica` and calls `define()`, `lazy()`, or
  uses `@decorate()`
- Code calls `lookup('Some.Type')` and you want the result typed
- A constructor or subtype type-errors and the fix belongs upstream
  (regenerate `.tactica` before reaching for a cast)
- TypeScript 6 declaration emit fails with TS2883 ("cannot be named
  without a reference to 'GlobalRegistry'") — the project exports free
  `define()` results without a registry merge; tactica is one of the
  right fixes. Full story:
  [mnemonica docs/typed-lookup.md — Declaration emit on TypeScript 6](https://github.com/wentout/mnemonica/blob/master/docs/typed-lookup.md#declaration-emit-on-typescript-6-the-ts2883-symptom)

## How to run

```bash
npx tactica                     # nearest tsconfig, writes .tactica/
npx tactica -p tsconfig.json    # explicit project
npx tactica --esm               # NodeNext ESM: .js import extensions
npx tactica -w                  # watch mode
```

The generated `types.ts` + `registry.ts` are imported by application
code; the JSON files are consumed by tooling (graph views, go-to
definition). Custom types collections are tracked too — with a
user-declared registry interface (Option B) they emit their own
augmented interface instead of the global `TypeRegistry`.

## What it types

- **Derived types:** an exported builder value on the default collection
  (`export const App = mnemonica.define(…).define(…)`,
  `export const Sessions = App.lookup('User').define(…)`) or an exported
  free `define` result is not re-extracted: `registry.ts` extends its
  `RegistryOf<typeof X>` (or uses `typeof X`), and `types.ts` reads the
  instances back with `LookedUpInstance<TypeRegistry, 'Path'>`. The
  builder and tactica then give the same type for the same runtime type.
- **Extracted types:** everything else (inline or unexported `define`,
  `@decorate`, handlers that use a generated `.tactica` type, topologica,
  Option B) is written out in core's vocabulary: registry entries are
  `RegistryEntry<X, 'Path', Parent, [args]>`, subtype fields
  `LookedUpConstructor<TypeRegistry, 'Path', true>`, so extracted and
  derived instances are assignable both ways.
- One `export type` per discovered type, named by dotted path with `_`
  separators; nested extracted types are `ProtoFlat<Parent, Self>`, so
  ancestor fields are present on descendants by construction.
- **An annotated `this` is the type:** `function (this: Shape, …)` gives
  `Shape`, and assignments beyond it add nothing (`this: any` gives
  `any`). Only a handler without a `this` annotation is typed from its
  body.
- Handlers held in a const (`const h = function …; define('X', h)`) are
  followed like inline ones.
- Looped defines over a const object's keys enter hierarchy and
  definitions only; their types come from the builder value.

## Async constructors

When a construct handler is an `async function` (or async arrow), `new`
resolves to a Promise at runtime. Extracted async types are registered as
`AsyncRegistryEntry<X, …>` (mnemonica ≥ 1.4.7), so construction is typed
`Promise<X>` and `await` yields `X` with its own subtypes; derived async
types get the same typing from mnemonica's builder.

A class constructor returning a Promise cannot be written in typed code
(TypeScript rejects it, TS2409), so async **classes** stay typed as the
plain instance.

## Avoid arrow handlers — use the ESLint plugin

mnemonica construct handlers must be regular functions or classes so the
instance can be substituted as `this`:

- Sync arrow handlers are rejected by mnemonica core at `define()` time
  with a readable error.
- Async arrow handlers **cannot be detected at runtime** — they look
  identical to `async function` — and they never receive the instance:
  `this` inside an arrow is the outer lexical `this`, so fields land on
  the wrong object and the construction fails later, far from the cause.

The early guard is the ESLint plugin `eslint-plugin-no-arrow-this`,
which flags `this` inside arrow functions before the code runs:

```javascript
// eslint.config.js (flat) or .eslintrc
plugins: ['eslint-plugin-no-arrow-this'],
rules: {
  // default: warn on `this` inside ANY arrow function
  'no-arrow-this/no-arrow-this': 'warn',
  // or restrict to the global/window capture case:
  // 'no-arrow-this/no-arrow-this': ['warn', { onlyGlobals: true }],
},
```

Recommended in every mnemonica project, especially where handlers are
written by contributors who have not internalized the rule.

## Example

```typescript
import { mnemonica } from 'mnemonica';

export const App = mnemonica
	.define('Widget', function (this: { id: string }, data: { id: string }) {
		this.id = data.id;
	})
	.define('Gadget', async function (this: { serial: number }, data: { serial: number }) {
		this.serial = await register(data.serial);
		return this;
	});
```

After `npx tactica`, `App` is derived, and the free `lookup('Widget')` is
typed exactly as `App.lookup('Widget')`. `new widget.Gadget({ serial: 1 })`
is a `Promise` — a forgotten `await` is a type error at the call site
instead of a silent `undefined` at runtime.
