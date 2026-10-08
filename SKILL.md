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

- One `export type` per discovered type, named by dotted path with `_`
  separators; nested types are `ProtoFlat<Parent, Self>`, so ancestor
  fields are present on descendants by construction.
- Every parent instance type carries its subtype constructors:
  `Child: { new (args): Child; (args): Child }` — the construct form
  and the chain-tip call form.
- `registry.ts` augments mnemonica's `TypeRegistry` so the free
  `lookup('Parent.Child')` returns the typed constructor.

## Async constructors

When a construct handler is an `async function` (or async arrow),
tactica emits `Promise<X>` for both constructor shapes — the subtype
property and the registry entry — because `new` resolves to a Promise
at runtime. The instance type `X` itself is unchanged, so
`await new` yields `X`.

Async **classes** (a class constructor returning a Promise) are NOT
detected — the syntactic shape carries no reliable signal without a
type checker — and stay typed as the plain instance type. Type them in
userland when `Promise<X>` is needed there.

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
	.define('Widget', function (this: Widget, data: { id: string }) {
		this.id = data.id;
	})
	.define('Gadget', async function (this: Gadget, data: { serial: number }) {
		this.serial = await register(data.serial);
		return this;
	});
```

After `npx tactica`, `lookup('App.Gadget')` is typed
`new (data: { serial: number }) => Promise<Gadget>` — a forgotten
`await` is now a type error at the call site instead of a silent
`undefined` at runtime.
