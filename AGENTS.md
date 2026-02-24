# AGENTS.md

This file provides guidance to agents when working with code in this repository.

## Project Overview

**@mnemonica/tactica** is a TypeScript Language Service Plugin that generates type definitions for Mnemonica's dynamic nested constructors. It enables TypeScript to understand runtime type hierarchies created through `define()` and `decorate()` calls.

## Build/Test Commands

All commands run from the `tactica/` directory:

```bash
# Build the project
npm run build

# Run tests
npm run test

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

## Architecture

### Core Components

```
src/
├── index.ts          # Main exports: analyzer, generator, writer, CLI, plugin
├── types.ts          # TypeScript type definitions
├── analyzer.ts       # AST analyzer for define()/decorate() calls
├── graph.ts          # Trie-based type hierarchy graph
├── generator.ts      # TypeScript .d.ts file generator
├── writer.ts         # File writer for .mnemonica/ folder
├── plugin.ts         # TypeScript Language Service Plugin entry
└── cli.ts            # Standalone CLI tool
```

### Key Classes

#### MnemonicaAnalyzer
Parses TypeScript source files to find Mnemonica type definitions.
- `analyzeFile(sourceFile)` - Analyze a TS source file
- `analyzeSource(sourceCode)` - Analyze source code string
- `getGraph()` - Get the type graph

#### TypeGraphImpl
Trie-based data structure representing type hierarchy.
- `roots` - Root types (defined at module level)
- `allTypes` - All types indexed by full path
- `addRoot()`, `addChild()` - Build the hierarchy
- `bfs()`, `dfs()` - Traverse the graph

#### TypesGenerator
Generates TypeScript declaration files from the type graph.
- `generate()` - Generate complete .d.ts content
- `generateSingleType(node)` - Generate single type

#### TypesWriter
Writes generated types to `.mnemonica/types.d.ts`.
- `write(generated)` - Write to default location
- `writeTo(filename, content)` - Write custom file
- `clean()` - Clear output directory

### How It Works

1. **Parse**: TypeScript AST is parsed to find `define()` and `decorate()` calls
2. **Analyze**: The analyzer extracts type names, properties, and hierarchy
3. **Graph**: A Trie (tree) structure represents the type hierarchy
4. **Generate**: TypeScript declarations are generated with module augmentations
5. **Output**: Files are written to `.mnemonica/` directory

## Testing

Tests are in `test/` directory using Mocha + Chai:

```bash
# Run all tests
npm run test

# Tests include:
# - analyzer.test.ts - Unit tests for AST analyzer
# - generator.test.ts - Unit tests for code generator
# - writer.test.ts - Unit tests for file writer
# - integration.test.ts - Integration tests for test-example.ts pattern
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
const generated = generator.generate();

// generated.content - the .d.ts file content
// generated.types - array of generated type names
```

## Configuration

### tsconfig.json Plugin Config

```json
{
  "compilerOptions": {
    "plugins": [
      {
        "name": "@mnemonica/tactica",
        "outputDir": ".mnemonica",
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
  -w, --watch          Watch for file changes
  -p, --project        Path to tsconfig.json
  -o, --output         Output directory (default: .mnemonica)
  -i, --include        File patterns to include
  -e, --exclude        File patterns to exclude
  -v, --verbose        Enable verbose logging
```

## Known Limitations

1. **Single-pass analysis**: Without a full TypeScript program, parent-child relationships may not be fully resolved. Using `ts.Program` provides better binding.

2. **Property extraction**: Currently supports `Object.assign(this, { ... })` and `this.prop = value` patterns. Complex property definitions may need manual type annotations.

3. **Decorator support**: `@decorate()` is detected, but complex decorator patterns may need enhancement.

## Related Projects

- **mnemonica** (core/) - Instance inheritance system
- **topologica** - Filesystem-based type discovery

## Resources

- [TypeScript Compiler API](https://github.com/Microsoft/TypeScript/wiki/Using-the-Compiler-API)
- [TypeScript Language Service Plugin Docs](https://github.com/microsoft/TypeScript/wiki/Writing-a-Language-Service-Plugin)
- Mnemonica README: `core/README.md`
