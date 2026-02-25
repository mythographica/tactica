# Tactica Agent Guidelines

This file provides AI agent guidance for working with the @mnemonica/tactica project.

## Quick Reference

```bash
# Build
npm run build

# Test
npm run test
npm run test:coverage

# Development
npm run watch
```

## Key Features

### 1. Mnemonica Pattern Detection

Tactica detects these patterns:

**define() Calls:**
```typescript
const Type = define('TypeName', function (this: any) {
    this.prop = value;
});

// Nested
const SubType = Type.define('SubType', function (this: any) {
    this.subProp = value;
});
```

**@decorate() Decorator:**
```typescript
@decorate()
class Basic { }

@decorate(ParentClass)
class Child { }

@decorate({ blockErrors: true, strictChain: false })
class WithOptions { }

@decorate(ParentClass, { exposeInstanceMethods: true })
class WithParentAndOptions { }
```

**Configuration Options:**
```typescript
// exposeInstanceMethods
const Type = define('Type', fn, { exposeInstanceMethods: false });
const Type = define('Type', fn, false); // shorthand

// strictChain, blockErrors
const Type = define('Type', fn, { strictChain: true, blockErrors: true });
```

### 2. Typeomatica Integration

Tactica works alongside Typeomatica without interference:

```typescript
import { Strict, BaseClass } from 'typeomatica';
import { decorate } from 'mnemonica';

@decorate()
@Strict({ value: 'default' })
class StrictType {
    value!: string;
}

// Object.setPrototypeOf with BaseClass
@decorate()
class MyClass {
    field = 123;
}

Object.setPrototypeOf(MyClass.prototype, new BaseClass(config));
```

### 3. CLI Tree Output

When running CLI, tactica displays type hierarchy:

```bash
$ npx tactica

Type Hierarchy (Trie):
└── UserTypeInstance
    └── AdminTypeInstance
        └── SuperAdminTypeInstance
```

## Architecture Overview

```
src/
├── index.ts      # Public API exports
├── types.ts      # TypeScript interfaces
├── analyzer.ts   # AST analysis (define/decorate detection)
├── graph.ts      # Trie-based type hierarchy
├── generator.ts  # .d.ts generation
├── writer.ts     # File I/O
├── plugin.ts     # TS Language Service Plugin
└── cli.ts        # Command line interface
```

## Working with the Analyzer

When adding new pattern detection:

1. **Add detection method** in `MnemonicaAnalyzer`:
```typescript
private isNewPattern(node: ts.Node): boolean {
    // Check node structure
    return ts.isCallExpression(node) && 
           ts.isIdentifier(node.expression) &&
           node.expression.text === 'patternName';
}
```

2. **Add processor method**:
```typescript
private processNewPattern(call: ts.CallExpression, sourceFile: ts.SourceFile): void {
    const typeName = this.extractTypeName(call);
    if (!typeName) return;
    
    const parent = this.findParentType(call);
    const properties = this.extractProperties(call);
    
    const node = TypeGraphImpl.createNode(
        typeName, parent, sourceFile.fileName,
        line, character, properties
    );
    
    if (parent) {
        this.graph.addChild(parent, node);
    } else {
        this.graph.addRoot(node);
    }
}
```

3. **Update visitNode** to call the processor:
```typescript
private visitNode(node: ts.Node, sourceFile: ts.SourceFile, currentClass?: ts.ClassDeclaration): void {
    if (this.isNewPattern(node)) {
        this.processNewPattern(node as ts.CallExpression, sourceFile);
    }
    // ... existing checks
}
```

## Testing Guidelines

Add tests for new patterns in `test/`:

```typescript
describe('New Pattern', () => {
    it('should detect pattern', () => {
        const code = `
            import { define } from 'mnemonica';
            const Type = define('Type', function() { });
        `;
        const analyzer = new MnemonicaAnalyzer();
        const result = analyzer.analyzeSource(code, 'test.ts');
        
        expect(result.errors).to.have.length(0);
        expect(result.types.map(t => t.name)).to.include('Type');
    });
});
```

## Common Tasks

### Adding Typeomatica Pattern Support

Typeomatica uses `@Strict`, `BaseClass`, and `Object.setPrototypeOf`. Tactica should:
1. Not crash when encountering these patterns
2. Continue detecting mnemonica types in the same file
3. Not treat pure Typeomatica classes as mnemonica types

See `test/typeomatica.test.ts` for examples.

### CLI Feature Addition

When adding CLI features:
1. Add option parsing in `parseArgs()` in `cli.ts`
2. Update `printHelp()` with new option
3. Pass option through to `run()` or `watch()`

### Code Coverage

Coverage report generated with `npm run test:coverage`:
- Statements: ~39%
- Branches: ~39%
- Functions: ~47%
- Lines: ~40%

Main uncovered areas: `cli.ts`, `plugin.ts`, `index.ts` (plugin entry)

## Related Files

- `tactica-test/` - Working example project
- `core/test-ts/test-example.ts` - Reference patterns from core
- `core/test/decorate.ts` - Decorator patterns
- `typeomatica/test/index.ts` - Typeomatica patterns
