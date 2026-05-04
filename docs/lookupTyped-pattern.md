# Consuming tactica Output: The lookupTyped Pattern

> **For application developers using tactica-generated types.**
> If you generated `.tactica/types.ts` and `.tactica/registry.ts` but still write `as unknown as` casts, read this.

---

## The Mistake Everyone Makes

You run tactica. It generates the files. You import the types. You still cast.

```typescript
// ❌ WRONG — you generated the types but didn't use them properly
import { RequestData } from './collections/requestTypes.js';
import type { RequestData as RequestDataT } from '../../.tactica/types.js';

const requestData = new RequestData({ ... }) as unknown as RequestDataT;
```

This is the most common failure mode. The types exist. The registry exists. But you're bridging them with a cast instead of using `lookupTyped`.

---

## The Correct Way

```typescript
// ✅ CORRECT — lookupTyped uses the TypeRegistry augmentation
import { lookupTyped } from 'mnemonica';

const RequestData = lookupTyped('RequestData');
const requestData = new RequestData({ ... });
const routeData = new requestData.RouteData({ ... });
```

`lookupTyped('RequestData')` returns the constructor **typed through the registry**. TypeScript knows:
- The constructor signature
- The instance properties
- That the instance has `.RouteData`, `.PageData`, etc.

No cast needed. The registry does the work.

---

## Why Importing the Type Is Not Enough

`tactica` generates two files:

1. `.tactica/types.ts` — exports like `export type RequestData = {...}`
2. `.tactica/registry.ts` — augments `mnemonica.TypeRegistry`

Importing from `types.ts` gives you the **instance shape**. It does NOT give you the **constructor type** with sub-constructors.

The registry augmentation is what teaches TypeScript that `lookupTyped('RequestData')` returns a constructor whose instances have `.RouteData`. Without `lookupTyped`, you're just importing shapes and casting between them.

---

## Module-Level Usage

`lookupTyped` is a runtime lookup, but it's safe to call at module level:

```typescript
// ✅ Safe and correct
const RequestData = lookupTyped('RequestData');
const EngineRequest = lookupTyped('EngineRequest');

app.get('/', async () => {
	const requestData = new RequestData({ ... });
});
```

The returned constructor is the same object every time. There is no per-request overhead.

---

## For Decoration (Fastify, Express, etc.)

Use the same `lookupTyped` result for decoration:

```typescript
const RequestData = lookupTyped('RequestData');

app.decorate('RequestData', RequestData);

// Later in a route handler:
const requestData = new RequestData({ ... });
```

No need to import the raw constructor separately. `lookupTyped` gives you the runtime object AND the type.

---

## Checklist

After running `tactica`:

- [ ] `.tactica/` directory exists with `types.ts` and `registry.ts`
- [ ] `tsconfig.json` includes `.tactica/**/*` in `include`
- [ ] You use `lookupTyped('TypeName')` instead of direct imports
- [ ] You do NOT write `as unknown as` with mnemonica types
- [ ] You run `tsc --noEmit` to verify types resolve

If any box is unchecked, the integration is incomplete.

---

## See Also

- **Agent guide:** `mnemonica/core/.ai/TACTICA.md`
- **Comprehensive technical guide:** `mnemonica/MNEMONICA-TACTICA-PATTERN.md`
- **Human-friendly explanation:** `mnemonica/core/docs/tactica-pattern.md`
