# Tactica: the chicken-egg problem and a way out

> **Status:** items 1, 2, 3 implemented (`define<TInstance, TArgs>`
> convention documented; `ts.Program` + `TypeChecker` wired into
> `MnemonicaAnalyzer`; drift detector emits warnings and
> `.tactica/drift.txt`). Items 4 (manifest mode) and 5 (LS plugin)
> remain as follow-ups.

## What "chicken-egg" actually is — two distinct loops

Tactica conflates two problems that have different solutions:

**Inner loop (same-file authoring).** While writing
`define('UserType', function(this, data) { … })`, what helps me type
`this` and `data`? Tactica today is a *post-hoc inferrer*: it scans the
finished body to derive properties. So the body must already be written
(usually with `any`) before tactica can produce types. By the time the
types appear, you've already typed the body blindly. Result: in the
*same file*, tactica gives you nothing.

**Outer loop (cross-file consumption).** At a `lookupTyped('UserType')`
call site in another file, what's the returned constructor signature?
Here tactica works well — `generateTypeRegistry()`
(`src/generator.ts:267-329`) emits a
`declare module 'mnemonica' { interface TypeRegistry { … } }`
augmentation with concrete `new (data: {…}) => UserTypeInstance`
entries.

The egg loop only feels broken because tactica is asked to do both with
the *same* mechanism (AST scan of finished code). Splitting the problem
is the fix.

## Why the current direction is structurally wrong

`src/analyzer.ts:608-622` privileges the `this:` annotation over
inferred `this.x = …` assignments — but if there is no annotation,
properties come from the body, and there is no validation that body
matches annotation. So:

- A user who declares `function(this: { name: string }, data)` and then
  writes `this.name = data.id` (number) gets a registry that says
  `name: string` while the runtime stores a number. Silent drift.
- A user who declares nothing gets `unknown` for anything tactica can't
  statically reduce (`README.md:681`, deep access; `README.md:654-660`,
  rest/spread).
- Cross-file alias resolution requires the TS Type Checker, but tactica
  uses parser-only `ts.createSourceFile` (`src/analyzer.ts:43`) without
  `ts.Program` bindings, so imported interfaces don't fully resolve
  (`AGENTS.md:610` confirms).
- The Language Service plugin promised in `PLAN.md:1-41` is not
  implemented — there is no `src/plugin.ts`. So the inner loop has no
  real-time signal at all.

## The fix: invert authority — declared types are canonical

Make user-declared TypeScript interfaces the source of truth, not the
constructor body. Tactica becomes a *lifter* (interfaces → registry)
and a *validator* (interfaces vs. body), not an inferrer. This kills
the chicken-egg: interfaces don't depend on runtime, and runtime
doesn't dictate interfaces.

Three concrete changes, smallest first.

### 1. `define<TInstance, TArgs>` as the canonical typed entry

mnemonica's `define` already accepts generic params
(`mnemonica/src/index.ts:50-68`); this is purely a documentation +
scanner convention. The recommended pattern becomes:

```ts
// src/schemas.ts — pure types, no runtime
export interface UserType { name: string; email: string; }
export interface UserTypeArgs { name: string; email: string; }

// src/types.ts — runtime; types are imported, not inferred
import { define } from 'mnemonica';
import type { UserType, UserTypeArgs } from './schemas';

export const UserType = define<UserType, UserTypeArgs>(
  'UserType',
  function (this, data) {            // ← `this` and `data` typed by the generic
    Object.assign(this, data);
  },
);
```

In this layout the inner loop is solved by **TypeScript itself** the
moment you save — no codegen needed for type-of-`this`. Tactica becomes
irrelevant to authoring.

### 2. Declared-type mode in tactica (analyzer change)

Add a second analysis path that reads the *declared* generic arguments
of `define<…>(…)` instead of inferring from the body. This needs:

- **Switch from parse-only to full `ts.Program` + `TypeChecker`** in
  `src/analyzer.ts:43`.
  `ts.createProgram(rootNames, compilerOptions).getTypeChecker()`
  resolves type aliases, imports, and generics across files. The
  current parse-only mode is the root cause of the cross-file fragility
  flagged in `AGENTS.md:610`.
- **At each `define()` call, prefer in this priority order:**
  1. Explicit generic arguments (`define<T, U>(…)`) — resolved via
     `TypeChecker.getTypeFromTypeNode(call.typeArguments[i])`.
  2. `this:` parameter annotation — resolved via `TypeChecker` instead
     of the textual matcher in `extractThisParamProperties`.
  3. (Existing fallback) inference from `this.x = …` assignments —
     kept but emitted as a *warning* (drift risk).
- Emit registry entries from #1/#2 directly, not from the inferred
  property list. `generateConstructorSignature`
  (`src/generator.ts:335-349`) already accepts a `constructorParams`
  array — feed it from declared `TArgs` instead of the inferred map.

This single change collapses three current limitations: cross-file
aliases work, generics work (`PLAN.md:262`), and rest/spread tuples
(`README.md:654-660`) work because the TypeChecker normalizes them.

### 3. Drift detector as a separate pass

Once #2 lands, tactica has both the *declared* shape (from generics /
annotations) and the *inferred* shape (from `this.x = …`). Diff them
and emit a `.tactica/drift.txt` (or fail CI) when they disagree:

```
warning: src/types.ts:14 — UserType declares `name: string`
         but constructor assigns this.name = data.id (number)
```

This is what makes type-first authoring trustworthy: if a body silently
breaks the contract, you find out at codegen time, not at runtime.

### 4. (Optional) Manifest mode for pure type-first

For users who want to design the whole tree before writing any
constructors:

```ts
// src/tactica.manifest.ts
import type {
  UserType, UserTypeArgs,
  AdminType, AdminTypeArgs,
} from './schemas';

export type Manifest = {
  'UserType':           { instance: UserType;              args: [UserTypeArgs]; };
  'UserType.AdminType': { instance: UserType & AdminType;  args: [AdminTypeArgs]; };
};
```

Tactica reads the manifest first, generates `registry.ts` from it, and
*then* (when constructors appear) verifies each `define('UserType', …)`
call matches the manifest entry. The egg loop is broken because the
registry exists before any constructor.

### 5. Real-time inner loop — the missing LS plugin

`PLAN.md:1-41` promises a Language Service plugin; the directory has no
`plugin.ts`. Add one (TypeScript LS plugins are a known shape:
`create(info: ts.server.PluginCreateInfo)` exporting
`getCompletionsAtPosition`, `getDefinitionAtPosition`, etc.). With the
plugin:

- `lookupTyped('▮')` autocompletes registered names in real time, no
  save-and-rerun.
- `instance.▮` after `new someType.SubType()` resolves through the
  registry without a build step.
- `define('UserType', …)` shows the declared `TInstance`/`TArgs` as the
  contract being signed.

The plugin shares analyzer code; per-keystroke latency is fine because
`ts.Program` is incremental.

## Priority and risk

| Change | Lines of work | Risk | Win |
|---|---|---|---|
| Document `define<TInstance, TArgs>` convention | ~50 lines docs | none | inner loop solved without codegen |
| `ts.Program` + `TypeChecker` in `analyzer.ts` | ~200 LOC refactor | medium (re-test all fixtures) | cross-file/generic/spread all work |
| Drift detector pass | ~120 LOC new | low | catches the silent-mismatch class of bugs |
| Manifest mode | ~150 LOC + 1 reader | low | unlocks pure type-first projects |
| LS plugin (`src/plugin.ts`) | ~400 LOC | medium | closes the loop to zero-latency authoring |

**Recommended order**: doc the generic convention first (one-day task,
immediate effect), then refactor analyzer onto `TypeChecker`, then
drift detector, then manifest, then plugin. Each step is independently
shippable; each lowers the chicken-egg cost without breaking existing
users.

## The deeper reframing

Tactica should not infer types from runtime — it should **lift declared
types into a runtime-addressable registry, and shout when runtime
drifts from declared.** That reframing makes the "which comes first"
question dissolve: declared types come first, runtime references them
by name, tactica is the bridge.
