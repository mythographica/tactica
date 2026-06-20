# Historical design plan

> **Status:** historical. This document captures the original design plan from the project's inception.
> It does **not** describe the current state of the codebase. For current docs see [`README.md`](./README.md)
> and [`AGENTS.md`](./AGENTS.md).
>
> Notably: the early plan assumed tactica would be implemented as a **TypeScript Language Service Plugin**.
> In practice tactica ships as a **CLI + Node library code generator**; the IDE-side features the plan
> envisioned (Go to Definition, Find References, etc.) are provided by the separate
> [mnemographica](https://github.com/mythographica/mnemographica) VS Code extension, which consumes
> tactica's `.tactica/` output.

---

## Original goal

Help TypeScript understand Mnemonica's runtime-created nested constructors.

```ts
const FirstType  = define('FirstType',  function (this: { first: string })  { this.first = ''; });
const SecondType = FirstType.define('SecondType', function (this: { second: string }) { this.second = ''; });

const first  = new FirstType();
const second = new first.SecondType(); // runs fine, but TS doesn't know about .SecondType
```

The chosen approach: parse the source statically, build a Trie of types, generate `.d.ts` (later `types.ts` + `registry.ts`) that teach TS about the hierarchy.

## What actually shipped

- **CLI + library:** see [`README.md`](./README.md). `npx tactica` parses the project, emits `.tactica/types.ts` + `.tactica/registry.ts` + a set of JSON metadata files.
- **TypeRegistry pattern:** `lookup()` in mnemonica core is augmented by the generated `registry.ts`, giving fully-typed runtime lookups without casts.
- **Topologica integration:** scans directory hierarchies (`ai-types/`, `types/`, `topologica-types/`) and reads `index.ts/.js/.mjs` handlers.
- **EDS tracking:** detects `wrap`, `link`, `getLastContext`, hook attachment, and framework adapter calls when `@mnemonica/dive` is in dependencies.
- **Flow tracking:** native-instance flow patterns (property access, method calls, destructures, etc.) emitted to `flow.json`.
- **Two output modes:** default (`types.ts` + `registry.ts`) and legacy (`--module-augmentation` → single `index.d.ts`).

## What did *not* ship

- **A TypeScript Language Service Plugin.** No `create(info)` factory in this repo. IDE features live in [mnemographica](https://github.com/mythographica/mnemographica).
- **Auto-modification of `.gitignore`.** The user decides whether to commit `.tactica/` or regenerate per build.

## Where the IDE features moved

Mnemographica (VS Code extension) provides:

- `MnemonicaDefinitionProvider` — reads `.tactica/definitions.json` for Go to Definition on `lookup('Foo')` strings.
- `MnemonicaReferenceProvider` — reads `.tactica/usages.json` for Find All References.
- Graph view, tree view, and registry inspector — all built on tactica's generated metadata.

The output contract is documented in [`AGENTS.md`](./AGENTS.md) under "Output contract (consumed by downstream tools)".

## Future work

See [`AGENTS.md`](./AGENTS.md) "Known limitations" for the live list. Original future-work items that remain open:

- Better cross-file resolution using `ts.Program.getTypeChecker()`.
- Generic type parameters in mnemonica types.
- Webpack / Vite plugin for build-time generation.
