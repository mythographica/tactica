# @mnemonica/tactica

**TypeScript Language Service Plugin for Mnemonica**

Tactica generates type definitions for Mnemonica's dynamic nested constructors, enabling TypeScript to understand runtime type hierarchies created through `define()` and `decorate()` calls.

## The Problem

Mnemonica enables powerful instance-level inheritance:

```typescript
const UserType = define('UserType', function (this: { name: string }) {
    this.name = '';
});

const AdminType = UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});

const user = new UserType();
const admin = new user.AdminType(); // Works at runtime!
```

But TypeScript doesn't know that `user.AdminType` exists because `UserType.define()` is a runtime operation.

## The Solution

Tactica analyzes your TypeScript source files and generates declaration files that tell TypeScript about the nested constructor hierarchy.

## Installation

```bash
npm install --save-dev @mnemonica/tactica
```

## Usage

### 1. As a TypeScript Language Service Plugin (Recommended)

Add to your `tsconfig.json`:

```json
{
  "compilerOptions": {
    "plugins": [
      {
        "name": "@mnemonica/tactica",
        "outputDir": ".tactica",
        "include": ["src/**/*.ts"],
        "exclude": ["**/*.test.ts", "**/*.spec.ts"]
      }
    ]
  }
}
```

Then include the generated types in your project:

```json
{
  "compilerOptions": {
    "typeRoots": ["./node_modules/@types", "./.tactica"]
  }
}
```

### 2. As a CLI Tool

Generate types once:

```bash
npx tactica
```

Watch mode for development:

```bash
npx tactica --watch
```

With custom options:

```bash
npx tactica --project ./src/tsconfig.json --output ./types/mnemonica
```

### 3. As a Module

```typescript
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

// Generate types.ts (exportable type aliases - default mode)
const generatedTypes = generator.generateTypesFile();
const writer = new TypesWriter('.tactica');
writer.writeTypesFile(generatedTypes);

// Or generate index.d.ts (global augmentation - legacy mode)
const generatedGlobal = generator.generateGlobalAugmentation();
writer.writeGlobalAugmentation(generatedGlobal);
```

## Configuration Options

### Plugin Options (tsconfig.json)

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `outputDir` | string | `.tactica` | Directory for generated types |
| `include` | string[] | `['**/*.ts']` | File patterns to include |
| `exclude` | string[] | `['**/*.d.ts']` | File patterns to exclude |
| `verbose` | boolean | `false` | Enable verbose logging |

### JavaScript Support

Tactica can analyze JavaScript files in addition to TypeScript by leveraging TypeScript's `allowJs` compiler option. This enables type generation for projects using Mnemonica in JavaScript.

**Enabling JavaScript Support in tsconfig.json:**

```json
{
  "compilerOptions": {
    "allowJs": true
  },
  "tactica": {
    "include": ["**/*.ts", "**/*.js"]
  }
}
```

**Enabling via CLI --include flag:**

```bash
# Analyze both TypeScript and JavaScript files
npx tactica --include "**/*.ts,**/*.js"

# Analyze only JavaScript files
npx tactica --include "**/*.js"
```

**How It Works:**

Tactica uses TypeScript's [`ts.createProgram()`](tactica/src/analyzer.ts) API to parse source files. When `allowJs: true` is configured in your tsconfig.json, TypeScript can parse JavaScript files and provide AST information that Tactica uses to detect `define()` and `decorate()` calls.

**Limitations:**

- **No type annotations**: JavaScript lacks TypeScript's type annotations, so inferred property types may be less precise
- **Harder property inference**: Without explicit type annotations, property types are inferred from assignments, which may result in `any` or broader types
- **JSDoc support**: TypeScript's `allowJs` does support JSDoc type annotations, so adding JSDoc comments to your JavaScript can improve type inference
- **ESM/CJS detection**: Ensure your tsconfig.json `module` setting matches your JavaScript module format

### CLI Options

| Option | Short | Description |
|--------|-------|-------------|
| `--watch` | `-w` | Watch mode - regenerate on file changes |
| `--project` | `-p` | Path to tsconfig.json |
| `--output` | `-o` | Output directory (default: `.tactica`) |
| `--include` | `-i` | Include patterns (comma-separated) |
| `--exclude` | `-e` | Exclude patterns (comma-separated) |
| `--topologica` | `-t` | Topologica directories to scan (comma-separated) |
| `--module-augmentation` | `-m` | Generate global augmentation (legacy mode) |
| `--verbose` | `-v` | Enable verbose logging |
| `--help` | `-h` | Show help message |

**Examples:**

```bash
# Default mode - generates .tactica/types.ts
npx tactica

# Global augmentation mode - generates .tactica/index.d.ts
npx tactica --module-augmentation

# Watch mode with custom output directory
npx tactica --watch --output ./custom-types

# Exclude test files
npx tactica --exclude "*.test.ts,*.spec.ts"

# Scan custom topologica directories
npx tactica --topologica ./src/ai-types,./custom/topologica
```

## Generated Output

By default, Tactica generates `.tactica/types.ts` with exported type aliases:

```typescript
// Generated by @mnemonica/tactica - DO NOT EDIT
export type UserType = {
    name: string;
    email: string;
    AdminType: new (data: { role: string; permissions: string[] }) => UserType_AdminType;
}

export type UserType_AdminType = ProtoFlat<UserType, {
    role: string;
    permissions: string[];
    AdminType: undefined;
}>
```

### Output Modes

**Default mode** (`npx tactica`):
- Generates `.tactica/types.ts` - Exportable type aliases
- Import types explicitly: `import type { UserTypeInstance } from './.tactica/types'`
- Include in tsconfig.json: `"include": ["src/**/*.ts", ".tactica/types.ts"]`
- **Recommended for new projects** - explicit imports, better tree-shaking

**Global mode** (`npx tactica --module-augmentation`):
- Generates `.tactica/index.d.ts` - Global type declarations
- Types are available without imports (via `declare global`)
- Add to tsconfig.json: `"typeRoots": ["./node_modules/@types", "./.tactica"]`
- Use triple-slash reference: `/// <reference types="./.tactica/index" />`

**Choosing a mode:**
- Use **Default mode** for new projects - explicit imports are clearer and work better with tree-shaking
- Use **Global mode** if you want types available without imports (legacy behavior)

## What Gets Analyzed

### 1. define() Calls

```typescript
// Root type
const UserType = define('UserType', function (this: { name: string }) {
    this.name = '';
});

// Nested type
const AdminType = UserType.define('AdminType', function (this: { role: string }) {
    this.role = 'admin';
});
```

### 2. @decorate() Decorator

```typescript
@decorate()
class User {
    name: string = '';
}

@decorate(User)
class Admin {
    role: string = 'admin';
}
```

#### Why Type Casting is Necessary for @decorate()

When using `@decorate()` on classes, TypeScript cannot automatically infer that instances have nested type constructors (like `user.Admin`). This is because:

1. **`define()` types work automatically**: When you use `define()`, the returned constructor has the correct type signature with nested constructors.

2. **`@decorate()` classes need casting**: When you decorate a class, TypeScript sees the class itself, not the augmented type that mnemonica creates at runtime.

**The Solution:** Cast to the instance type to access nested constructors:

```typescript
@decorate()
class Order {
    orderId: string = '';
    total: number = 0;
}

@decorate(Order)
class AugmentedOrder {
    addition: string = 'extra';
}

// Cast to OrderInstance to access AugmentedOrder constructor
const order = new Order() as OrderInstance;
const augmented = new order.AugmentedOrder(); // ✅ Works!

// The 'augmented' variable is automatically typed as AugmentedOrderInstance
console.log(augmented.orderId);  // From Order
console.log(augmented.addition); // From AugmentedOrder
```

Generated types (like `OrderInstance`, `AugmentedOrderInstance`) are automatically available globally - no imports needed!

#### @decorate() with Options

```typescript
@decorate({
    blockErrors: true,
    strictChain: false,
    exposeInstanceMethods: true
})
class ConfigurableClass {
    value: string = '';
}
```

### 3. Object.assign Pattern

```typescript
const UserType = define('UserType', function (this: any, data: any) {
    Object.assign(this, data);
});
```

### 4. Typeomatica Integration

Tactica works seamlessly with Typeomatica patterns:

```typescript
import { decorate } from 'mnemonica';
import { Strict, BaseClass } from 'typeomatica';

// @Strict decorator alongside @decorate
@decorate()
@Strict({ someProp: 123 })
class StrictDecorated {
    someProp!: number;
}

// BaseClass with Object.setPrototypeOf
@decorate()
class MyBaseClass {
    base_field = 555;
}

Object.setPrototypeOf(MyBaseClass.prototype, new BaseClass({ strict: true }));
```

### 5. ConstructorFunction Pattern

```typescript
import { define, ConstructorFunction } from 'mnemonica';

const MyFn = function (this: any) {
    this.field = 123;
} as ConstructorFunction<{ field: number }>;

const MyFnType = define('MyFnType', MyFn);
```

### 5. Topologica Directory Structures

Tactica can analyze [Topologica](https://github.com/mythographica/topologica)-style directory structures to generate types:

```
ai-types/
├── Sentience/
│   ├── index.ts          # export function SentienceHandler(this, data)
│   ├── Consciousness/
│   │   ├── index.ts
│   │   ├── Curiosity/
│   │   │   └── index.ts
│   │   └── Empathy/
│   │       └── index.ts
│   └── Memory/
│       └── index.ts
```

**Handler file format:**

```typescript
// ai-types/Sentience/index.ts
export interface SentienceData {
    awareness?: string;
    identity?: string;
}

export interface SentienceInstance {
    awareness: string;
    timestamp: number;
    identity: string;
    sentience: boolean;
}

export function SentienceHandler(
    this: SentienceInstance,
    data: SentienceData
): void {
    this.awareness = data?.awareness || 'awake';
    this.timestamp = Date.now();
    this.identity = data?.identity || 'AI Agent';
    this.sentience = true;
}
```

**Auto-discovery:** Tactica automatically scans these directories:
- `./ai-types`
- `./types`
- `./topologica-types`
- `./src/ai-types`
- `./src/types`
- `./src/topologica-types`

**Custom directories:** Use the `--topologica` CLI option:

```bash
npx tactica --topologica ./src/ai-types,./custom/topologica
```

**Property extraction:** The analyzer parses handler files and extracts:
- `this.property = value` assignments
- `Object.assign(this, data)` patterns
- Inferred types from initializers (`Date.now()` → `number`, string literals → `string`, etc.)

Generated types include all extracted properties with proper TypeScript types.

## CLI Features

### Tree Output

The CLI displays type hierarchy as a tree:

```bash
$ npx tactica

Type Hierarchy (Trie):
└── UserTypeInstance
    └── AdminTypeInstance
        └── SuperAdminTypeInstance
└── ProductTypeInstance
    ├── DigitalProductTypeInstance
    └── PhysicalProductTypeInstance
```

### Code Coverage

Run tests with coverage:

```bash
npm run test:coverage
```

## Integration with Your Workflow

### .gitignore

Tactica automatically adds `.tactica/` to your `.gitignore` if not already present.

### IDE Support

With the Language Service Plugin:
- **VS Code**: Automatic type updates on file save
- **WebStorm**: Works with TypeScript service
- **Vim/Neovim**: Works with coc.nvim, nvim-lspconfig

## Type-Safe Lookup with `lookupTyped()`

Mnemonica core provides a `lookupTyped()` function that enables type-safe type retrieval when combined with tactica-generated types:

```typescript
import { lookupTyped } from 'mnemonica';

// Get a type-safe reference to a type
const UserType = lookupTyped('UserType');
const user = new UserType({ name: 'John' }); // Fully typed!

// Works with nested types too
const SubType = lookupTyped('Parent.SubType');
```

### How It Works

The `lookupTyped()` function uses TypeScript's module augmentation pattern through the `TypeRegistry` interface:

1. **Default TypeRegistry** (in mnemonica core):
```typescript
// mnemonica exports an empty TypeRegistry interface
export interface TypeRegistry {
	[key: string]: new (...args: unknown[]) => unknown;
}
```

2. **Tactica generates the augmentation** in `.tactica/registry.ts`:
```typescript
// Generated by tactica
import 'mnemonica';

declare module 'mnemonica' {
	export interface TypeRegistry {
		'UserType': new (data: { name: string; email: string }) => UserType;
		'UserType.AdminType': new (data: { role: string; permissions: string[] }) => UserType_AdminType;
		// ... all discovered types
	}
}
```

3. **Your project includes the augmentation**:
```typescript
// In your main entry point or types file
import './.tactica/registry'; // Augments mnemonica's TypeRegistry
import { lookupTyped } from 'mnemonica';

// Now lookupTyped returns properly typed constructors
const UserType = lookupTyped('UserType'); // new (data: { name: string; email: string }) => UserType
```

### Configuration

To enable type-safe lookup in your project:

1. **Generate types with tactica**:
```bash
npx tactica --registry
```

2. **Include the registry in your tsconfig.json**:
```json
{
	"compilerOptions": {
		"typeRoots": ["./node_modules/@types", "./.tactica"]
	},
	"include": ["src/**/*", ".tactica/**/*"]
}
```

3. **Import the registry once** in your entry point:
```typescript
// main.ts or index.ts
import './.tactica/registry';
// ... rest of your imports
```

### Using lookupTyped with Custom Types Collections

When using named types collections, the same pattern applies:

```typescript
import { createTypesCollection, lookupTyped } from 'mnemonica';
import type { MyProjectTypeRegistry } from './.tactica/registry';

const myCollection = createTypesCollection('MyProject');

// Type-safe lookup within a specific collection
const UserType = lookupTyped.call(
	myCollection as unknown as { lookup: (path: string) => unknown },
	'UserType' as keyof MyProjectTypeRegistry
);
```

## API Reference

### MnemonicaAnalyzer

```typescript
class MnemonicaAnalyzer {
    constructor(program?: ts.Program);
    analyzeFile(sourceFile: ts.SourceFile): AnalyzeResult;
    analyzeSource(sourceCode: string, fileName?: string): AnalyzeResult;
    getGraph(): TypeGraphImpl;
}
```

### TypeGraphImpl

```typescript
class TypeGraphImpl implements TypeGraph {
    roots: Map<string, TypeNode>;
    allTypes: Map<string, TypeNode>;
    addRoot(node: TypeNode): void;
    addChild(parent: TypeNode, child: TypeNode): void;
    findType(fullPath: string): TypeNode | undefined;
    getAllTypes(): TypeNode[];
    *bfs(): Generator<TypeNode>;
    *dfs(node?: TypeNode): Generator<TypeNode>;
}
```

### TypesGenerator

```typescript
class TypesGenerator {
    constructor(graph: TypeGraphImpl);
    generate(): GeneratedTypes;
    generateSingleType(node: TypeNode): string;
}
```

### TypesWriter

```typescript
class TypesWriter {
    constructor(outputDir?: string);
    write(generated: GeneratedTypes): string;
    writeTo(filename: string, content: string): string;
    clean(): void;
    getOutputDir(): string;
}
```

## How It Works

1. **Parse**: TypeScript AST is parsed to find `define()` and `decorate()` calls
2. **Analyze**: The analyzer extracts type names, properties, and hierarchy
3. **Graph**: A Trie (tree) structure represents the type hierarchy
4. **Generate**: TypeScript declarations are generated from the graph
5. **Output**: Files are written to `.tactica/` directory

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

## Troubleshooting

### Types not updating

1. Check that the plugin is loaded in `tsconfig.json`
2. Restart TypeScript service (VS Code: Command Palette → "TypeScript: Restart TS Server")
3. Verify file patterns in `include`/`exclude` config

### Generated types have errors

1. Ensure all mnemonica types have explicit type annotations
2. Check that `define()` calls use string literals for type names
3. Verify property types are valid TypeScript

### Plugin not working

```bash
# Test with CLI first
npx tactica --verbose

# Check for parsing errors
npx tactica --verbose 2>&1 | grep -i error
```

## Known Limitations

### Rest/Spread Parameters with Tuple Types

The analyzer currently cannot extract property types from rest parameters using tuple types:

```typescript
// ❌ NOT SUPPORTED - Property types will be `unknown`
export const UserEntity = define('UserEntity', function (
	this: UserEntityInstance,
	...args: [{ id: string; email: string; name: string }, ...unknown[]]
) {
	const data = args[0];  // Analyzer cannot track this assignment
	Object.assign(this, data);
});
```

**Workaround**: Use direct parameter access with proper type annotations:

```typescript
// ✅ SUPPORTED - Use direct parameter instead of rest args
export const UserEntity = define('UserEntity', function (
	this: UserEntityInstance,
	data: { id: string; email: string; name: string }
) {
	Object.assign(this, data);
});
```

### Deep Nested Property Access

Property access through multiple levels returns `unknown`:

```typescript
// ⚠️ PARTIAL - nested access returns unknown
const UserType = define('UserType', function (this: any, data: { profile: { name: string } }) {
	this.name = data.profile.name;  // Type: unknown (not string)
});
```

**Workaround**: Flatten your data structure or use direct parameter:

```typescript
// ✅ SUPPORTED - direct parameter or flat structure
const UserType = define('UserType', function (this: any, profileName: string) {
	this.name = profileName;  // Type: string
});
```

## Supported Patterns

### 1. Direct Single Parameter
```typescript
const MyType = define('MyType', function (this: MyTypeInstance, data: { name: string }) {
	Object.assign(this, data);
});
```

### 2. Multiple Parameters
```typescript
const MyType = define('MyType', function (
	this: MyTypeInstance,
	data: { name: string },
	config: { enabled: boolean }
) {
	Object.assign(this, data, config);
});
```

### 3. Renamed Parameters
```typescript
const MyType = define('MyType', function (this: MyTypeInstance, userData: { name: string }) {
	Object.assign(this, userData);
});
```

### 4. Fallback Patterns
```typescript
const MyType = define('MyType', function (this: MyTypeInstance, data: { items?: string[] }) {
	this.items = data.items || [];  // Fallback to empty array
});
```

### 5. Arithmetic Operations
```typescript
const CalcType = define('CalcType', function (this: any, data: { x: number; y: number }) {
	this.sum = data.x + data.y;      // number
	this.diff = data.x - data.y;     // number
	this.product = data.x * data.y;  // number
});
```

### 6. Built-in Function Calls
```typescript
const TimeType = define('TimeType', function (this: any) {
	this.timestamp = Date.now();     // number
	this.parsed = parseInt('123');   // number
	this.str = String(123);          // string
	this.bool = Boolean(1);          // boolean
});
```

### 7. Template Literals
```typescript
const UserType = define('UserType', function (this: any, data: { first: string; last: string }) {
	this.fullName = `${data.first} ${data.last}`;  // string
});
```

### 8. New Expressions
```typescript
const ContainerType = define('ContainerType', function (this: any) {
	this.created = new Date();       // Date
	this.items = new Array();        // Array
	this.cache = new Map();          // Map
});
```

### 9. Async Constructors
```typescript
const AsyncType = define('AsyncType', async function (this: any, data: { value: number }) {
	this.value = data.value;
	this.computed = data.value * 2;  // number
	this.timestamp = Date.now();     // number
});
```

## Related Projects

- [mnemonica](https://github.com/wentout/mnemonica) - Instance inheritance system
- [@mnemonica/topologica](https://github.com/mythographica/topologica) - Filesystem-based type discovery
- [typeomatica](https://github.com/wentout/typeomatica) - Runtime type checking with `@Strict` decorator and `BaseClass`

## Testing

Tactica includes comprehensive test coverage:

```bash
# Run all tests
npm test

# Run with coverage
npm run test:coverage
```

Test suites include:
- **Analyzer tests** - Core AST parsing functionality
- **Generator tests** - TypeScript declaration generation
- **Writer tests** - File I/O operations
- **Integration tests** - End-to-end workflows
- **Example tests** - Patterns from `tactica-test/` project
- **Typeomatica tests** - Combined mnemonica + typeomatica patterns

## License

MIT

## Contributing

Contributions welcome! Please read the [Contributing Guide](CONTRIBUTING.md) for details.
