# AGENTS.md

This file provides guidance to agents when working with code in this repository.

## Project Overview

**@mnemonica/tactica** is a TypeScript Language Service Plugin that generates type definitions for Mnemonica's dynamic nested constructors. It enables TypeScript to understand runtime type hierarchies created through `define()` and `decorate()` calls.

### Role in the Ecosystem

Tactica serves three key purposes:

1. **Type Generation**: Generates `.tactica/types.ts` with TypeScript interfaces for Mnemonica types
2. **Hierarchy Tracking**: Provides type information for nested constructors that TypeScript can't infer
3. **Location Data**: Tracks where `define()`/`decorate()` are called and where instances are created

This location data feeds into **Mnemonica Graphica** for visualization and navigation.

### AI Agent Context

Tactica enables AI agents to:
- Understand the complete type hierarchy without executing code
- Navigate between type definitions and usage sites
- Provide intelligent suggestions based on the inheritance graph

## Build/Test Commands

All commands run from the `tactica/` directory:

```bash
# Build the project
npm run build

# Run tests
npm run test

# Run tests with coverage
npm run test:coverage

# Watch mode for development
npm run watch
```

## Code Style

### Indentation
- **Tabs** for indentation (not spaces)
- See `.editorconfig`: `indent_style = tab`, `indent_size = 4`

### Function Spacing
- **Always** space before function parentheses:
  ```typescript
  function myFunc () { }  // ✓ correct
  function myFunc() { }   // ✗ wrong
  ```

### TypeScript Strictness
- `strict: true` enabled
- `noImplicitAny: true`
- `noUnusedLocals: true` - unused variables cause errors
- `noUnusedParameters: true` - unused parameters cause errors
- `isolatedModules: true` - each file must be independently transpilable

### Return Statement Pattern
- **Always** use intermediate variable before return for debugging support:
  ```typescript
  // ✓ correct - allows setting breakpoint on the variable
  const result = this.service.doSomething();
  return result;
  
  // ✗ wrong - cannot set breakpoint on return value
  return this.service.doSomething();
  ```

## Architecture

### Core Components

```
src/
├── index.ts          # Main exports: analyzer, generator, writer, CLI, plugin
├── types.ts          # TypeScript type definitions
├── analyzer.ts       # AST analyzer for define()/decorate() calls
├── topologica-analyzer.ts  # Analyzer for Topologica directory structures
├── graph.ts          # Trie-based type hierarchy graph
├── generator.ts      # TypeScript .d.ts file generator
├── writer.ts         # File writer for .tactica/ folder
├── plugin.ts         # TypeScript Language Service Plugin entry
└── cli.ts            # Standalone CLI tool
```

### Key Classes

#### MnemonicaAnalyzer
Parses TypeScript and JavaScript source files to find Mnemonica type definitions.
- `analyzeFile(sourceFile)` - Analyze a TS/JS source file
- `analyzeSource(sourceCode)` - Analyze source code string
- `getGraph()` - Get the type graph

**JavaScript Support Note:** The analyzer uses [`ts.createProgram()`](tactica/src/analyzer.ts) which can parse JavaScript files when `allowJs: true` is configured in tsconfig.json. This enables analyzing projects that use Mnemonica in JavaScript rather than TypeScript. See the JavaScript Support section in README.md for details.

#### TypeGraphImpl
Trie-based data structure representing type hierarchy.
- `roots` - Root types (defined at module level)
- `allTypes` - All types indexed by full path
- `addRoot()`, `addChild()` - Build the hierarchy
- `bfs()`, `dfs()` - Traverse the graph

#### TypesGenerator
Generates TypeScript declaration files from the type graph.
- `generateTypesFile()` - Generate exportable type aliases (default mode, outputs `types.ts`)
- `generateGlobalAugmentation()` - Generate global type declarations (legacy mode, outputs `index.d.ts`)
- `generateSingleType(node)` - Generate single type

#### TypesWriter
Writes generated types to `.tactica/` directory.
- `writeTypesFile(generated)` - Write exportable types to `types.ts` (default mode)
- `writeGlobalAugmentation(generated)` - Write global declarations to `index.d.ts` (module augmentation mode)
- `writeTo(filename, content)` - Write custom file
- `clean()` - Clear output directory

#### TopologicaAnalyzer
Analyzes Topologica-style directory structures to extract type hierarchies from filesystem organization.
- `analyzeDirectory(directoryPath)` - Scan a directory structure for type definitions
- `getGraph()` - Get the type graph with extracted properties
- `getErrors()` - Get parsing errors

**Property Extraction:** Uses TypeScript AST parsing to extract:
- `this.property = value` assignments from handler functions
- `Object.assign(this, data)` patterns
- Inferred types from initializers (string literals → `string`, `Date.now()` → `number`, etc.)

**Supported File Formats:**
- `.ts` - TypeScript files with full type annotations
- `.js` - JavaScript files (parsed with TypeScript compiler)
- `.mjs` - ES Module JavaScript files

**Auto-discovery:** The CLI automatically scans standard directories (`ai-types`, `types`, `topologica-types`) in both project root and `src/` subdirectory.

**Custom directories:** Use the `--topologica` CLI option:
```bash
npx tactica --topologica ./src/ai-types,./custom/topologica
```

### How It Works

1. **Parse**: TypeScript AST is parsed to find `define()` and `decorate()` calls
2. **Analyze**: The analyzer extracts type names, properties, and hierarchy
3. **Graph**: A Trie (tree) structure represents the type hierarchy
4. **Generate**: TypeScript declarations are generated
   - Default mode: Exportable type aliases in `types.ts`
   - Global mode: Global declarations in `index.d.ts`
5. **Output**: Files are written to `.tactica/` directory

### Triple-Slash References

For global augmentation mode, use triple-slash reference directives:

```typescript
// At the top of your entry file (e.g., src/index.ts)
/// <reference types="./.tactica/index" />

// Or from project root
/// <reference types="../.tactica/index" />
```

This makes global types available without explicit imports.

### Type-Safe Lookup with lookupTyped()

Mnemonica core provides `lookupTyped()` for type-safe type retrieval. This works through TypeScript's module augmentation of the `TypeRegistry` interface.

#### How It Works

1. **Mnemonica exports an empty TypeRegistry interface**:
```typescript
// In mnemonica core
export interface TypeRegistry {
	[key: string]: new (...args: unknown[]) => unknown;
}

export function lookupTyped<K extends keyof TypeRegistry>(
	path: K
): TypeRegistry[K] | undefined;
```

2. **Tactica generates a registry file** that augments this interface:
```typescript
// .tactica/registry.ts (generated by tactica)
import 'mnemonica';

declare module 'mnemonica' {
	export interface TypeRegistry {
		'UserType': new (data: { name: string; email: string }) => UserType;
		'UserType.AdminType': new (data: { role: string; permissions: string[] }) => UserType_AdminType;
		// ... all discovered types
	}
}
```

3. **Projects import the registry** to enable type-safe lookup:
```typescript
// main.ts
import './.tactica/registry'; // Augments mnemonica's TypeRegistry
import { lookupTyped } from 'mnemonica';

const UserType = lookupTyped('UserType'); // Fully typed!
const user = new UserType({ name: 'John' });
```

#### Registry Generation

To generate the registry file:
```bash
npx tactica --registry
```

Or enable it in tsconfig.json plugin options:
```json
{
	"compilerOptions": {
		"plugins": [{
			"name": "@mnemonica/tactica",
			"outputDir": ".tactica",
			"generateRegistry": true
		}]
	}
}
```

#### Implementation Notes

- The registry uses TypeScript's declaration merging (module augmentation)
- Types are referenced using `typeof` to get the constructor type
- The augmentation is additive - it doesn't replace the default TypeRegistry
- Falls back to `unknown` if the registry is not augmented

### Type Casting for @decorate() Classes

When using `@decorate()` on classes, TypeScript may not recognize the decorated class as a valid constructor. Use type casting:

```typescript
import { decorate, type ConstructorFunction } from 'mnemonica';

@decorate()
class MyClass {
    name: string = '';
}

// Cast to ConstructorFunction for define()
const MyType = define('MyType', MyClass as ConstructorFunction<{ name: string }>);

// Or when creating instances
const instance = new (MyClass as ConstructorFunction<{ name: string }>)();
```

## Testing

Tests are in `test/` directory using Mocha + Chai:

```bash
# Run all tests
npm run test

# Run tests with coverage report
npm run test:coverage
```

### Testing Rules (CRITICAL)

**NEVER use `node -e` for testing.** Instead:
- Write proper test files in the `test/` directory
- Or create a temporary test file and run with `node <filename>`
- Or use the existing test infrastructure (Mocha + Chai)

**Why?** `node -e` commands require interactive terminal input and cannot be automated. They block waiting for user interaction that will never come in automated environments.

**Correct approach:**
```bash
# ✅ CORRECT - Write a test file
echo "console.log(require('./lib').something)" > /tmp/test.js && node /tmp/test.js

# ✅ CORRECT - Use existing test infrastructure
npm test -- --grep "specific test"

# ❌ WRONG - Never use node -e for testing
node -e "console.log(require('./lib').something)"
```

### Test Suites

| File | Description |
|------|-------------|
| `analyzer.test.ts` | Unit tests for AST analyzer |
| `generator.test.ts` | Unit tests for code generator |
| `writer.test.ts` | Unit tests for file writer |
| `integration.test.ts` | Integration tests for core/test-ts patterns |
| `examples.test.ts` | Tests for tactica-test example files |
| `typeomatica.test.ts` | Combined mnemonica + typeomatica patterns |

### After Modifying Tests

**IMPORTANT**: After adding or modifying tests, you **MUST** compare the tested features with the documentation:

1. **Review the tests** - What new capabilities are being tested?
2. **Check README.md** - Is the "Known Limitations" section still accurate?
3. **Check README.md** - Are the "Supported Patterns" documented?
4. **Check AGENTS.md** - Do the "Supported Patterns" examples match?
5. **Update documentation** if tests reveal new capabilities or changed behavior

Example workflow:
```
Add new tests for feature X → Run tests → Verify they pass →
Compare with README/AGENTS → Update documentation if needed
```

This ensures documentation stays in sync with actual analyzer capabilities.

## Supported Patterns

### 1. define() Calls

```typescript
// Root type
const UserType = define('UserType', function (this: any) {
    this.name = '';
});

// Nested type (subtypes)
const AdminType = UserType.define('AdminType', function (this: any) {
    this.role = 'admin';
});
```

### 2. @decorate() Decorator

```typescript
// Basic decorator
@decorate()
class User {
    name: string = '';
}

// With parent class
@decorate(ParentClass)
class Child {
    childProp: string = '';
}

// With options
@decorate({
    blockErrors: true,
    strictChain: false,
    exposeInstanceMethods: true
})
class Configurable {
    value: string = '';
}

// Both parent and options
@decorate(ParentClass, { strictChain: false })
class ChildWithOptions {
    prop: string = '';
}
```

### 3. Object.assign Pattern

```typescript
const UserType = define('UserType', function (this: any, data: any) {
    Object.assign(this, data);
});
```

### 4. Typeomatica Integration

Tactica works with Typeomatica patterns without breaking:

```typescript
import { Strict, BaseClass } from 'typeomatica';
import { decorate } from 'mnemonica';

// @Strict decorator alongside @decorate
@decorate()
@Strict({ someProp: 123 })
class StrictEntity {
    someProp!: number;
}

// BaseClass with Object.setPrototypeOf
@decorate()
class MyBase {
    baseField = 555;
}

Object.setPrototypeOf(MyBase.prototype, new BaseClass({ strict: true }));
```

### 5. ConstructorFunction Pattern

```typescript
import { ConstructorFunction } from 'mnemonica';

const MyFn = function (this: any) {
    this.field = 123;
} as ConstructorFunction<{ field: number }>;

const MyFnType = define('MyFnType', MyFn);
```

### 6. Configuration Options

```typescript
// exposeInstanceMethods option
const HiddenType = define('HiddenType', function (this: any) {
    this.data = 'hidden';
}, {
    exposeInstanceMethods: false,
});

// Shorthand syntax (same as above)
const HiddenShorthand = define('HiddenShorthand', function (this: any) {
    this.data = 'shorthand';
}, false);
```

### 7. Type Inference from Expressions

The analyzer infers types from various expression patterns:

```typescript
// Arithmetic operations → number
const CalcType = define('CalcType', function (this: any, data: { x: number; y: number }) {
    this.sum = data.x + data.y;      // number
    this.diff = data.x - data.y;     // number
    this.product = data.x * data.y;  // number
    this.quotient = data.x / data.y; // number
});

// Built-in function calls
const TimeType = define('TimeType', function (this: any) {
    this.now = Date.now();           // number
    this.parsed = parseInt('123');   // number
    this.str = String(123);          // string
    this.bool = Boolean(1);          // boolean
});

// Template literals → string
const UserType = define('UserType', function (this: any, data: { first: string; last: string }) {
    this.fullName = `${data.first} ${data.last}`; // string
});

// new Expressions
const ContainerType = define('ContainerType', function (this: any) {
    this.created = new Date();       // Date
    this.items = new Array();        // Array
    this.cache = new Map();          // Map
});

// Direct parameter assignment
const DirectType = define('DirectType', function (this: any, name: string, count: number) {
    this.name = name;    // string
    this.count = count;  // number
});

// Data parameter property access
const DataType = define('DataType', function (this: any, data: { id: string; items: string[] }) {
    this.id = data.id;       // string
    this.items = data.items; // Array<string>
});

// Async constructors
const AsyncType = define('AsyncType', async function (this: any, data: { value: number }) {
    this.value = data.value;
    this.computed = data.value * 2;  // number
    this.timestamp = Date.now();     // number
});
```

## Common Patterns

### Adding a New Analyzer Feature

```typescript
// 1. Add detection in visitNode()
if (this.isNewPattern(node)) {
    this.processNewPattern(node as ts.CallExpression, sourceFile);
}

// 2. Implement detection method
private isNewPattern(node: ts.Node): boolean {
    // Detection logic
}

// 3. Implement processing method
private processNewPattern(call: ts.CallExpression, sourceFile: ts.SourceFile): void {
    // Extract info and add to graph
}
```

### Working with the Type Graph

```typescript
const graph = new TypeGraphImpl();

// Create nodes
const root = TypeGraphImpl.createNode('UserType', undefined, 'file.ts', 1, 1);
graph.addRoot(root);

const child = TypeGraphImpl.createNode('AdminType', root, 'file.ts', 5, 1);
graph.addChild(root, child);

// Traverse
for (const node of graph.bfs()) {
    console.log(node.fullPath);
}
```

### Generating Types

```typescript
const generator = new TypesGenerator(graph);

// Default mode: generate exportable type aliases (types.ts)
const generatedTypes = generator.generateTypesFile();
// generatedTypes.content - the types.ts file content
// generatedTypes.types - array of generated type names

// Global mode: generate global type declarations (index.d.ts)
const generatedGlobal = generator.generateGlobalAugmentation();
// generatedGlobal.content - the index.d.ts file content
// generatedGlobal.types - array of generated type names

// Generate single type
const singleType = generator.generateSingleType(node);
```

## Configuration

### tsconfig.json Plugin Config

```json
{
  "compilerOptions": {
    "plugins": [
      {
        "name": "@mnemonica/tactica",
        "outputDir": ".tactica",
        "include": ["src/**/*.ts"],
        "exclude": ["**/*.test.ts"]
      }
    ]
  }
}
```

### CLI Options

```bash
npx tactica [options]
  -w, --watch                 Watch for file changes
  -p, --project               Path to tsconfig.json
  -o, --output                Output directory (default: .tactica)
  -i, --include               File patterns to include
  -e, --exclude               File patterns to exclude
  -t, --topologica            Topologica directories to scan (comma-separated)
  -m, --module-augmentation   Generate global augmentation (index.d.ts) instead of exportable types
  -v, --verbose               Enable verbose logging
  -h, --help                  Show help
```

**Output Modes:**

- **Default mode** (no flags): Generates `.tactica/types.ts` with exportable type aliases
  - Import types explicitly: `import type { UserTypeInstance } from './.tactica/types'`
  - Recommended for new projects - explicit imports work better with tree-shaking

- **Global mode** (`--module-augmentation`): Generates `.tactica/index.d.ts` with global declarations
  - Types available without imports via global augmentation
  - Use triple-slash reference: `/// <reference types="./.tactica/index" />`
  - Legacy behavior, useful for gradual migration

**Examples:**

```bash
# Default mode - generate types.ts
npx tactica

# Global mode - generate index.d.ts
npx tactica --module-augmentation

# Watch mode with default output
npx tactica --watch

# Watch mode with global augmentation
npx tactica --watch --module-augmentation

# Exclude test files
npx tactica --exclude "**/*.test.ts" --exclude "**/*.spec.ts"

# Custom project path
npx tactica --project ./tsconfig.json

# Scan custom topologica directories
npx tactica --topologica ./src/ai-types,./custom/topologica
```

## Known Limitations

1. **Single-pass analysis**: Without a full TypeScript program, parent-child relationships may not be fully resolved. Using `ts.Program` provides better binding.

2. **Deep nested property access**: Property access like `data.nested.prop` returns `unknown` - only single-level access (`data.prop`) is fully supported.

3. **Complex property definitions**: While arithmetic operations, template literals, and common built-in functions are supported, complex expressions may fall back to `unknown`.

4. **Decorator support**: `@decorate()` is detected, but complex decorator patterns may need enhancement.

## Type Inference Capabilities

The analyzer can infer property types from various expression patterns:

### Supported Patterns

```typescript
// Arithmetic operations → number
const CalcType = define('CalcType', function (this: any, data: { x: number; y: number }) {
	this.sum = data.x + data.y;      // number
	this.diff = data.x - data.y;     // number
	this.product = data.x * data.y;  // number
	this.quotient = data.x / data.y; // number
});

// Built-in function calls
const TimeType = define('TimeType', function (this: any) {
	this.now = Date.now();           // number
	this.parsed = parseInt('123');   // number
	this.str = String(123);          // string
	this.bool = Boolean(1);          // boolean
});

// Template literals → string
const UserType = define('UserType', function (this: any, data: { first: string; last: string }) {
	this.fullName = `${data.first} ${data.last}`; // string
});

// new Expressions
const ContainerType = define('ContainerType', function (this: any) {
	this.created = new Date();       // Date
	this.items = new Array();        // Array
	this.cache = new Map();          // Map
});

// Direct parameter assignment
const DirectType = define('DirectType', function (this: any, name: string, count: number) {
	this.name = name;    // string
	this.count = count;  // number
});

// Data parameter property access
const DataType = define('DataType', function (this: any, data: { id: string; items: string[] }) {
	this.id = data.id;       // string
	this.items = data.items; // Array<string>
});
```

### Fallback Behavior

When type cannot be inferred, the analyzer falls back to `unknown`. This is safe and allows manual type annotation if needed.

## Related Projects

- **mnemonica** (core/) - Instance inheritance system
- **topologica** - Filesystem-based type discovery

## Resources

- [TypeScript Compiler API](https://github.com/Microsoft/TypeScript/wiki/Using-the-Compiler-API)
- [TypeScript Language Service Plugin Docs](https://github.com/microsoft/TypeScript/wiki/Writing-a-Language-Service-Plugin)
- Mnemonica README: `core/README.md`
