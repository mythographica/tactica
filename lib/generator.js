'use strict';
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.TypesGenerator = void 0;
const path = __importStar(require("path"));
/**
 * TypeScript declaration file generator
 */
class TypesGenerator {
    constructor(graph, esm = false, outputDir = '.tactica', referenceResolver, builderValues = []) {
        this.graph = graph;
        this.referenceResolver = referenceResolver;
        this.builderValues = builderValues;
        this.resolutionErrors = [];
        this.esm = esm;
        this.outputDir = outputDir;
    }
    /**
     * Get import path with optional .js extension for ESM NodeNext
     */
    importPath(relative) {
        return this.esm ? `${relative}.js` : relative;
    }
    derivedTypePaths() {
        const result = new Set();
        for (const value of this.builderValues) {
            for (const root of this.graph.roots.values()) {
                for (const node of this.graph.dfs(root)) {
                    if (node.collectionId || node.metadataOnly) {
                        continue;
                    }
                    // RegistryOf carries the value's whole chain, ancestors
                    // included; a `typeof` entry types only its own path, so
                    // its ancestors stay extracted unless a value of their
                    // own derives them
                    const covered = value.kind === 'registryOf'
                        ? node.fullPath === value.fullPath || value.fullPath.startsWith(`${node.fullPath}.`)
                        : node.fullPath === value.fullPath;
                    if (covered) {
                        result.add(node.fullPath);
                    }
                }
            }
        }
        return result;
    }
    builderImportName(value) {
        const node = this.graph.findType(value.fullPath);
        const instanceName = node ? this.getInstanceTypeName(node) : '';
        const result = value.name === instanceName ? `${value.name}Ctor` : value.name;
        return result;
    }
    pushBuilderImports(lines) {
        const named = new Map();
        const defaults = new Map();
        const fromBuilder = [];
        for (const value of this.builderValues) {
            const group = value.defaultImport ? defaults : named;
            const importName = this.builderImportName(value);
            const names = group.get(value.sourceFile) ?? [];
            const binding = importName === value.name ? value.name : `${value.name} as ${importName}`;
            names.push(binding);
            group.set(value.sourceFile, names);
            if (value.kind === 'registryOf') {
                fromBuilder.push(`RegistryOf<typeof ${importName}>`);
            }
        }
        for (const [sourceFile, names] of named) {
            const modulePath = this.resolveModulePath(sourceFile);
            lines.push(`import type { ${names.join(', ')} } from '${modulePath}';`);
        }
        for (const [sourceFile, names] of defaults) {
            const modulePath = this.resolveModulePath(sourceFile);
            for (const name of names) {
                lines.push(`import type ${name} from '${modulePath}';`);
            }
        }
        if (fromBuilder.length > 0) {
            lines.push(`type FromBuilder = ${fromBuilder.join(' & ')};`);
            lines.push('');
        }
    }
    /**
        * Generate a types.ts file with complete instance interfaces
        * This includes all properties extracted from the constructors
        */
    generateTypesFile() {
        const lines = [];
        const generatedTypes = [];
        // Header
        lines.push('// Generated by @mnemonica/tactica - DO NOT EDIT');
        lines.push('// This file provides complete TypeScript interfaces for Mnemonica types');
        lines.push('');
        const derived = this.derivedTypePaths();
        let needsProtoFlat = false;
        let needsLookedUpConstructor = false;
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.metadataOnly) {
                    continue;
                }
                if (node.parent && !derived.has(node.fullPath)) {
                    needsProtoFlat = true;
                }
                const hasEmittedChildren = Array.from(node.children.values()).some(child => !child.metadataOnly);
                if (!node.collectionId && hasEmittedChildren && !derived.has(node.fullPath)) {
                    needsLookedUpConstructor = true;
                }
            }
        }
        const mnemonicaImports = [];
        if (needsProtoFlat) {
            mnemonicaImports.push('ProtoFlat');
        }
        if (needsLookedUpConstructor) {
            mnemonicaImports.push('LookedUpConstructor');
        }
        if (derived.size > 0) {
            mnemonicaImports.push('LookedUpInstance');
        }
        if (mnemonicaImports.length > 0) {
            lines.push(`import type { ${mnemonicaImports.join(', ')} } from 'mnemonica';`);
        }
        if (derived.size > 0 || needsLookedUpConstructor) {
            lines.push('import type { TypeRegistry } from \'./registry\';');
        }
        if (mnemonicaImports.length > 0 || derived.size > 0 || needsLookedUpConstructor) {
            lines.push('');
        }
        // Generate complete instance interfaces for default-collection types and
        // for custom collections that declare a user-provided registry interface
        // (Option B). Custom-collection types without a registry interface are
        // isolated at runtime and are not emitted. Computed loop definitions are
        // metadata-only in every collection.
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.metadataOnly || (node.collectionId && !node.registryInterfaceName)) {
                    continue;
                }
                const interfaceName = this.getInstanceTypeName(node);
                generatedTypes.push(interfaceName);
                if (derived.has(node.fullPath)) {
                    lines.push(`export type ${interfaceName} = LookedUpInstance<TypeRegistry, '${node.fullPath}'>;`);
                    lines.push('');
                }
                else {
                    this.generateCompleteInstanceInterface(node, lines);
                }
            }
        }
        return {
            content: lines.join('\n'),
            types: generatedTypes,
        };
    }
    /**
         * Generate a complete instance type alias with all properties
         * This is for the types.ts file that users import from
         */
    generateCompleteInstanceInterface(node, lines) {
        const typeName = this.getInstanceTypeName(node);
        if (node.instanceTypeOverride === 'any') {
            lines.push(`export type ${typeName} = any;`);
            lines.push('');
            return;
        }
        if (node.parent) {
            // Nested type: Use ProtoFlat to properly exclude overridden properties
            lines.push(`export type ${typeName} = ProtoFlat<${this.getInstanceTypeName(node.parent)}, {`);
        }
        else {
            // Root type: just the properties object
            lines.push(`export type ${typeName} = {`);
        }
        // Add instance properties extracted from the constructor
        for (const [propName, propInfo] of node.properties.entries()) {
            const optional = propInfo.optional ? '?' : '';
            const readonly = propInfo.readonly ? 'readonly ' : '';
            lines.push(`\t${readonly}${propName}${optional}: ${this.resolveTypeInString(propInfo.type, node)};`);
        }
        // Add nested constructor properties for non-leaf nodes
        // Leaf nodes (no children) don't get constructor properties
        // This follows mnemonica's strictChain behavior
        if (node.children.size > 0) {
            for (const child of node.children.values()) {
                this.pushChildConstructorField(lines, '', child);
            }
        }
        // For nested types, add this node's constructor and all siblings from same parent as undefined
        // This is needed for strict chain behavior - parent undefineds are inherited via ProtoFlat.
        // Optional on default-collection types so builder children can cross;
        // Option B keeps required markers.
        if (node.parent) {
            const optional = node.collectionId ? '' : '?';
            // Add this node's own constructor as undefined
            lines.push(`\t${node.name}${optional}: undefined;`);
            // Add all siblings (other children of the same parent) as undefined
            for (const sibling of node.parent.children.values()) {
                if (sibling.name !== node.name && !sibling.metadataOnly) {
                    lines.push(`\t${sibling.name}${optional}: undefined;`);
                }
            }
        }
        // Close the type properly - ProtoFlat uses }>; for nested, }; for root
        if (node.parent) {
            lines.push('}>;');
        }
        else {
            lines.push('};');
        }
        lines.push('');
    }
    /**
         * Emit one nested-ctor field. Default-collection children use core's
         * complete constructor surface. Option B uses dual signatures:
         * construct + the chain-tip CALL form, both resolving through
         * getConstructorResultType.
         */
    pushChildConstructorField(lines, indentStr, child) {
        if (child.metadataOnly) {
            return;
        }
        if (!child.collectionId) {
            const fullPath = this.getFullPath(child);
            lines.push(`${indentStr}\t${child.name}: LookedUpConstructor<TypeRegistry, '${fullPath}', true>;`);
            return;
        }
        const childInstanceType = this.getConstructorResultType(child);
        const constructorParams = this.generateConstructorParams(child);
        lines.push(`${indentStr}\t${child.name}: {`);
        lines.push(`${indentStr}\t\tnew ${constructorParams}: ${childInstanceType};`);
        lines.push(`${indentStr}\t\t${constructorParams}: ${childInstanceType};`);
        lines.push(`${indentStr}\t};`);
    }
    /**
     * The type a constructor invocation resolves to: the instance type, or
     * Promise<InstanceType> for async handlers (isAsync). The instance type
     * itself is never wrapped — only the constructor RESULT positions
     * (subtype property twins + registry entries).
     */
    getConstructorResultType(node) {
        const instanceType = this.getInstanceTypeName(node);
        const result = node.isAsync ? `Promise<${instanceType}>` : instanceType;
        return result;
    }
    /**
         * Generate a simple type declaration for a single type
         */
    generateSingleType(node) {
        const lines = [];
        this.generateCompleteInstanceInterface(node, lines);
        return lines.join('\n');
    }
    /**
         * Generate TypeRegistry interface for type-safe lookup() function
         * Augment mnemonica's TypeRegistry so lookup('TypeName') returns the typed constructor
         */
    generateTypeRegistry() {
        const lines = [];
        const generatedTypes = [];
        // Header
        lines.push('// Generated TypeRegistry for type-safe mnemonica.lookup()');
        lines.push('// This file augments mnemonica\'s TypeRegistry via declaration merging.');
        lines.push('//');
        lines.push('// Usage:');
        lines.push('//   import { lookup } from \'mnemonica\';');
        lines.push('//   import \'./.tactica/registry\';  // applies the augmentation');
        lines.push('//   const MyType = lookup(\'MyType\');');
        lines.push('//   // TypeScript knows: MyType is the typed constructor for MyType');
        lines.push('//   const instance = new MyType({ /* constructor args */ });');
        lines.push('//   // instance has full intellisense for the generated type');
        lines.push('');
        const derived = this.derivedTypePaths();
        this.pushBuilderImports(lines);
        const extractedSignatures = [];
        let needsRegistryEntry = false;
        let needsAsyncRegistryEntry = false;
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.metadataOnly ||
                    (node.collectionId && !node.registryInterfaceName) || derived.has(node.fullPath)) {
                    continue;
                }
                if (!node.collectionId) {
                    if (node.isAsync) {
                        needsAsyncRegistryEntry = true;
                    }
                    else {
                        needsRegistryEntry = true;
                    }
                }
                extractedSignatures.push(this.generateConstructorSignature(node));
                if (node.parent) {
                    extractedSignatures.push(this.getInstanceTypeName(node.parent));
                }
            }
        }
        // Import instance types from types.ts. Derived aliases are needed only
        // when an extracted constructor signature or RegistryEntry parent refers to them.
        // Skip custom-collection types that have no user-provided registry interface.
        lines.push('import type {');
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.metadataOnly || (node.collectionId && !node.registryInterfaceName)) {
                    continue;
                }
                const fullPath = this.getFullPath(node);
                const instanceTypeName = this.getInstanceTypeName(node);
                if (derived.has(fullPath)) {
                    const reference = new RegExp(`\\b${instanceTypeName}\\b`);
                    const used = extractedSignatures.some(signature => reference.test(signature));
                    if (!used) {
                        continue;
                    }
                }
                lines.push(`\t${instanceTypeName},`);
                generatedTypes.push(instanceTypeName);
            }
        }
        lines.push(`} from '${this.importPath('./types')}';`);
        lines.push('');
        // Generate module augmentation for mnemonica TypeRegistry
        lines.push('/**');
        lines.push(' * Type registry augmenting mnemonica\'s TypeRegistry interface');
        lines.push(' * This enables type-safe lookup() without explicit type arguments');
        lines.push(' *');
        lines.push(' * Usage: const SomeType = lookup(\'SomeType\'); // Fully typed!');
        lines.push(' */');
        lines.push('declare module \'mnemonica\' {');
        const fromBuilder = this.builderValues.some(value => value.kind === 'registryOf');
        lines.push(`\tinterface TypeRegistry ${fromBuilder ? 'extends FromBuilder ' : ''}{`);
        // Generate entries for all type paths that belong to the default/global collection.
        // Types that live in a custom collection (collectionId set) are isolated at runtime
        // and are not reachable through free lookup(), so they must not be added to the
        // global TypeRegistry augmentation.
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.collectionId || node.metadataOnly) {
                    continue;
                }
                const fullPath = this.getFullPath(node);
                if (derived.has(fullPath)) {
                    continue;
                }
                // Default extracted entries use core's complete constructor surface.
                // AsyncRegistryEntry owns the Promise result, so its F stays the
                // resolved instance for hooks and inheritance.
                const instanceType = this.getInstanceTypeName(node);
                const parentType = node.parent ? this.getInstanceTypeName(node.parent) : 'object';
                const constructorArgs = this.generateConstructorArgs(node);
                const entryKind = node.isAsync ? 'AsyncRegistryEntry' : 'RegistryEntry';
                const entry = `${entryKind}<${instanceType}, '${fullPath}', ${parentType}, ${constructorArgs}>`;
                lines.push(`\t\t'${fullPath}': ${entry};`);
            }
        }
        for (const value of this.builderValues) {
            if (value.kind === 'typeof') {
                const importName = this.builderImportName(value);
                lines.push(`\t\t'${value.fullPath}': typeof ${importName};`);
            }
        }
        lines.push('\t}');
        lines.push('}');
        lines.push('');
        // Generate per-collection registry augmentations for Option B
        // (user-provided registry interfaces).
        const collectionGroups = this.groupCollectionRegistryNodes();
        for (const [key, nodes] of collectionGroups) {
            const [registryInterfaceName, sourceFile] = key.split('::');
            const modulePath = this.resolveModulePath(sourceFile);
            lines.push(`declare module '${modulePath}' {`);
            lines.push(`\tinterface ${registryInterfaceName} {`);
            for (const node of nodes) {
                const fullPath = this.getFullPath(node);
                const instanceType = this.getConstructorResultType(node);
                const constructorSig = this.generateConstructorSignature(node);
                lines.push(`\t\t'${fullPath}': ${constructorSig} => ${instanceType};`);
            }
            lines.push('\t}');
            lines.push('}');
            lines.push('');
        }
        // Re-export for backward compatibility and explicit usage
        const registryImports = ['TypeRegistry'];
        if (fromBuilder) {
            registryImports.unshift('RegistryOf');
        }
        if (needsRegistryEntry) {
            registryImports.unshift('RegistryEntry');
        }
        if (needsAsyncRegistryEntry) {
            registryImports.unshift('AsyncRegistryEntry');
        }
        lines.push(`import type { ${registryImports.join(', ')} } from 'mnemonica';`);
        lines.push('export type { TypeRegistry };');
        return {
            content: lines.join('\n'),
            types: generatedTypes,
        };
    }
    /**
         * Generate constructor parameter list for a type node (the "(…)" part)
         */
    generateConstructorParams(node) {
        const params = node.constructorParams;
        if (!params || params.length === 0) {
            return '()';
        }
        const props = [];
        for (const param of params) {
            const optional = param.optional ? '?' : '';
            const rest = param.kind === 'rest' ? '...' : '';
            const arrayMatch = rest ? /^Array<(.+)>$/.exec(param.type) : undefined;
            const type = arrayMatch ? `${arrayMatch[1]}[]` : param.type;
            props.push(`${rest}${param.name}${optional}: ${type}`);
        }
        return `(${props.join(', ')})`;
    }
    generateConstructorArgs(node) {
        const params = this.generateConstructorParams(node);
        // Step 6 changes rest parameters here to [data: T, ...values: number[]].
        const result = `[${params.slice(1, -1)}]`;
        return result;
    }
    /**
         * Generate constructor signature for a type node
         * Uses constructorParams for TypeRegistry signature (not instance properties)
         */
    generateConstructorSignature(node) {
        return `new ${this.generateConstructorParams(node)}`;
    }
    /**
         * Get the full dotted path for a type node
         */
    getFullPath(node) {
        if (!node.parent) {
            return node.name;
        }
        return `${this.getFullPath(node.parent)}.${node.name}`;
    }
    /**
     * Get the instance type name for a node
     * Uses full path with underscores: Usages.UsageEntry -> Usages_UsageEntry
     * For Option B custom collections, prefixes with the registry interface name.
     */
    getInstanceTypeName(node) {
        const fullPath = this.getFullPath(node);
        const prefix = node.registryInterfaceName ? `${node.registryInterfaceName}_` : '';
        return `${prefix}${fullPath.replace(/\./g, '_')}`;
    }
    /**
     * Resolve a simple type name to its full path name
     * e.g., "DefinitionEntry" -> "Definitions_DefinitionEntry"
     *
     * With a referenceResolver installed (the CLI path), resolution is
     * path-aware per the graph identity law: the resolver returns the unique
     * type, 'ambiguous', or undefined — the latter two record a hard-fail
     * ResolutionError and emit `unknown` instead of silently picking a
     * first match. Without a resolver the legacy first-match scan stays.
     */
    resolveTypeName(simpleName, currentNode) {
        if (this.referenceResolver) {
            const resolved = this.referenceResolver(simpleName, currentNode);
            if (resolved && resolved !== 'ambiguous') {
                const instanceName = this.getInstanceTypeName(resolved);
                return instanceName;
            }
            const anchorLocation = `${currentNode.sourceFile}:${currentNode.line}:${currentNode.column}`;
            const ambiguousGenerationMessage = `Ambiguous reference to mnemonica type '${simpleName}' ` +
                `while generating '${this.getFullPath(currentNode)}'`;
            const unresolvedGenerationMessage = `Unresolved reference to mnemonica type '${simpleName}' ` +
                `while generating '${this.getFullPath(currentNode)}'`;
            const message = resolved === 'ambiguous'
                ? ambiguousGenerationMessage
                : unresolvedGenerationMessage;
            const error = { message, locations: [anchorLocation] };
            this.resolutionErrors.push(error);
            const unknownResult = 'unknown';
            return unknownResult;
        }
        // First check if it's the current node or its children
        if (currentNode.name === simpleName) {
            return this.getInstanceTypeName(currentNode);
        }
        for (const child of currentNode.children.values()) {
            if (child.name === simpleName) {
                return this.getInstanceTypeName(child);
            }
        }
        // Search all types in the graph
        for (const type of this.graph.getAllTypes()) {
            if (type.name === simpleName) {
                return this.getInstanceTypeName(type);
            }
        }
        return simpleName;
    }
    /**
     * Hard-fail graph reference errors recorded while generating (see
     * referenceResolver). The CLI prints every location and writes no output.
     */
    getResolutionErrors() {
        const result = [...this.resolutionErrors];
        return result;
    }
    /**
     * Resolve simple type names to full path names within a type string
     * Handles complex types like Array<UsageEntry>, Map<string, TypeEntry>, etc.
     */
    resolveTypeInString(typeStr, currentNode) {
        // Get all type names from the graph
        const allTypes = this.graph.getAllTypes();
        const typeNames = new Set();
        for (const type of allTypes) {
            typeNames.add(type.name);
        }
        // Sort by length (longest first) to avoid partial replacements
        const sortedNames = Array.from(typeNames).sort((a, b) => b.length - a.length);
        // Replace each simple type name with its full path version
        let result = typeStr;
        for (const name of sortedNames) {
            // Skip names that do not occur — with a referenceResolver installed,
            // resolving absent names would record spurious errors
            const occurs = new RegExp(`\\b${name}\\b`).test(result);
            if (!occurs) {
                continue;
            }
            // Use word boundary matching to avoid replacing partial names
            const regex = new RegExp(`\\b${name}\\b`, 'g');
            const fullTypeName = this.resolveTypeName(name, currentNode);
            if (fullTypeName !== name) {
                result = result.replace(regex, fullTypeName);
            }
        }
        return result;
    }
    /**
     * Group collection type nodes by their registry interface name and the
     * collection's home file (the module declaring the interface — the
     * augmentation target), NOT each type's own define file: multi-file
     * collections define types across many modules.
     * Returns a map keyed by `${registryInterfaceName}::${sourceFile}`.
     */
    groupCollectionRegistryNodes() {
        const groups = new Map();
        for (const root of this.graph.roots.values()) {
            for (const node of this.graph.dfs(root)) {
                if (node.metadataOnly || !node.registryInterfaceName) {
                    continue;
                }
                const homeFile = node.collectionSourceFile ?? node.sourceFile;
                const key = `${node.registryInterfaceName}::${homeFile}`;
                const existing = groups.get(key);
                if (existing) {
                    existing.push(node);
                }
                else {
                    groups.set(key, [node]);
                }
            }
        }
        return groups;
    }
    /**
     * Resolve a source file path to a module specifier relative to the output directory,
     * suitable for use in a `declare module '...'` block.
     */
    resolveModulePath(sourceFile) {
        const outputAbsolute = path.resolve(this.outputDir);
        const sourceAbsolute = path.resolve(sourceFile);
        let relative = path.relative(outputAbsolute, sourceAbsolute);
        // Remove .ts extension; keep .tsx if present
        if (relative.endsWith('.ts') && !relative.endsWith('.tsx')) {
            relative = relative.slice(0, -3);
        }
        // Convert Windows separators to POSIX
        const posixRelative = relative.replace(/\\/g, '/');
        return posixRelative;
    }
}
exports.TypesGenerator = TypesGenerator;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiZ2VuZXJhdG9yLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL2dlbmVyYXRvci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLDJDQUE2QjtBQWdCN0I7O0dBRUc7QUFDSCxNQUFhLGNBQWM7SUFLMUIsWUFDUyxLQUFvQixFQUM1QixHQUFHLEdBQUcsS0FBSyxFQUNYLFNBQVMsR0FBRyxVQUFVLEVBQ2QsaUJBQTBDLEVBQzFDLGdCQUFnQyxFQUFFO1FBSmxDLFVBQUssR0FBTCxLQUFLLENBQWU7UUFHcEIsc0JBQWlCLEdBQWpCLGlCQUFpQixDQUF5QjtRQUMxQyxrQkFBYSxHQUFiLGFBQWEsQ0FBcUI7UUFQbkMscUJBQWdCLEdBQXNCLEVBQUUsQ0FBQztRQVNoRCxJQUFJLENBQUMsR0FBRyxHQUFHLEdBQUcsQ0FBQztRQUNmLElBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO0lBQzVCLENBQUM7SUFFRDs7T0FFRztJQUNLLFVBQVUsQ0FBRSxRQUFnQjtRQUNuQyxPQUFPLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEdBQUcsUUFBUSxLQUFLLENBQUMsQ0FBQyxDQUFDLFFBQVEsQ0FBQztJQUMvQyxDQUFDO0lBRU8sZ0JBQWdCO1FBQ3ZCLE1BQU0sTUFBTSxHQUFHLElBQUksR0FBRyxFQUFVLENBQUM7UUFDakMsS0FBSyxNQUFNLEtBQUssSUFBSSxJQUFJLENBQUMsYUFBYSxFQUFFLENBQUM7WUFDeEMsS0FBSyxNQUFNLElBQUksSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLEtBQUssQ0FBQyxNQUFNLEVBQUUsRUFBRSxDQUFDO2dCQUM5QyxLQUFLLE1BQU0sSUFBSSxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7b0JBQ3pDLElBQUksSUFBSSxDQUFDLFlBQVksSUFBSSxJQUFJ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O1FBQ0YsQ0FBQztRQUNELE9BQU8sTUFBTSxDQUFDO0lBQ2YsQ0FBQztJQUVEOzs7T0FHRztJQUNLLGlCQUFpQixDQUFFLFVBQWtCO1FBQzVDLE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDO1FBQ3BELE1BQU0sY0FBYyxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7UUFDaEQsSUFBSSxRQUFRLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxjQUFjLEVBQUUsY0FBYyxDQUFDLENBQUM7UUFDN0QsNkNBQTZDO1FBQzdDLElBQUksUUFBUSxDQUFDLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxRQUFRLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQztZQUM1RCxRQUFRLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQztRQUNsQyxDQUFDO1FBQ0Qsc0NBQXNDO1FBQ3RDLE1BQU0sYUFBYSxHQUFHLFFBQVEsQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLEdBQUcsQ0FBQyxDQUFDO1FBQ25ELE9BQU8sYUFBYSxDQUFDO0lBQ3RCLENBQUM7Q0FDRDtBQTNtQkQsd0NBMm1CQyIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgcGF0aCBmcm9tICdwYXRoJztcbmltcG9ydCB7XG5cdFR5cGVOb2RlLCBHZW5lcmF0ZWRUeXBlcywgUmVzb2x1dGlvbkVycm9yLCBCdWlsZGVyVmFsdWUgXG59IGZyb20gJy4vdHlwZXMnO1xuaW1wb3J0IHsgVHlwZUdyYXBoSW1wbCB9IGZyb20gJy4vZ3JhcGgnO1xuXG4vKipcbiAqIFBhdGgtYXdhcmUgcmVzb2x2ZXIgZm9yIG1uZW1vbmljYSBncmFwaCB0eXBlIG5hbWVzIHJlZmVyZW5jZWQgaW5zaWRlIHR5cGVcbiAqIHN0cmluZ3Mgd2hpbGUgZ2VuZXJhdGluZyBvdXRwdXQuIFJldHVybnMgdGhlIHVuaXF1ZSB0eXBlLCAnYW1iaWd1b3VzJywgb3JcbiAqIHVuZGVmaW5lZCAocmVzb2x2ZXMgdG8gbm90aGluZykg4oCUIHNlZSByZXNvbHZlR3JhcGhUeXBlUmVmZXJlbmNlLlxuICovXG5leHBvcnQgdHlwZSBHcmFwaFJlZmVyZW5jZVJlc29sdmVyID0gKFxuXHRzaW1wbGVOYW1lOiBzdHJpbmcsXG5cdGN1cnJlbnROb2RlOiBUeXBlTm9kZVxuKSA9PiBUeXBlTm9kZSB8ICdhbWJpZ3VvdXMnIHwgdW5kZWZpbmVkO1xuXG4vKipcbiAqIFR5cGVTY3JpcHQgZGVjbGFyYXRpb24gZmlsZSBnZW5lcmF0b3JcbiAqL1xuZXhwb3J0IGNsYXNzIFR5cGVzR2VuZXJhdG9yIHtcblx0cHJpdmF0ZSBlc206IGJvb2xlYW47XG5cdHByaXZhdGUgb3V0cHV0RGlyOiBzdHJpbmc7XG5cdHByaXZhdGUgcmVzb2x1dGlvbkVycm9yczogUmVzb2x1dGlvbkVycm9yW10gPSBbXTtcblxuXHRjb25zdHJ1Y3RvciAoXG5cdFx0cHJpdmF0ZSBncmFwaDogVHlwZUdyYXBoSW1wbCxcblx0XHRlc20gPSBmYWxzZSxcblx0XHRvdXRwdXREaXIgPSAnLnRhY3RpY2EnLFxuXHRcdHByaXZhdGUgcmVmZXJlbmNlUmVzb2x2ZXI/OiBHcmFwaFJlZmVyZW5jZVJlc29sdmVyLFxuXHRcdHByaXZhdGUgYnVpbGRlclZhbHVlczogQnVpbGRlclZhbHVlW10gPSBbXVxuXHQpIHtcblx0XHR0aGlzLmVzbSA9IGVzbTtcblx0XHR0aGlzLm91dHB1dERpciA9IG91dHB1dERpcjtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgaW1wb3J0IHBhdGggd2l0aCBvcHRpb25hbCAuanMgZXh0ZW5zaW9uIGZvciBFU00gTm9kZU5leHRcblx0ICovXG5cdHByaXZhdGUgaW1wb3J0UGF0aCAocmVsYXRpdmU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMuZXNtID8gYCR7cmVsYXRpdmV9LmpzYCA6IHJlbGF0aXZlO1xuXHR9XG5cblx0cHJpdmF0ZSBkZXJpdmVkVHlwZVBhdGhzICgpOiBTZXQ8c3RyaW5nPiB7XG5cdFx0Y29uc3QgcmVzdWx0ID0gbmV3IFNldDxzdHJpbmc+KCk7XG5cdFx0Zm9yIChjb25zdCB2YWx1ZSBvZiB0aGlzLmJ1aWxkZXJWYWx1ZXMpIHtcblx0XHRcdGZvciAoY29uc3Qgcm9vdCBvZiB0aGlzLmdyYXBoLnJvb3RzLnZhbHVlcygpKSB7XG5cdFx0XHRcdGZvciAoY29uc3Qgbm9kZSBvZiB0aGlzLmdyYXBoLmRmcyhyb290KSkge1xuXHRcdFx0XHRcdGlmIChub2RlLmNvbGxlY3Rpb25JZCB8fCBub2RlLm1ldGFkYXRhT25seSkge1xuXHRcdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHRcdC8vIFJlZ2lzdHJ5T2YgY2FycmllcyB0aGUgdmFsdWUncyB3aG9sZSBjaGFpbiwgYW5jZXN0b3JzXG5cdFx0XHRcdFx0Ly8gaW5jbHVkZWQ7IGEgYHR5cGVvZmAgZW50cnkgdHlwZXMgb25seSBpdHMgb3duIHBhdGgsIHNvXG5cdFx0XHRcdFx0Ly8gaXRzIGFuY2VzdG9ycyBzdGF5IGV4dHJhY3RlZCB1bmxlc3MgYSB2YWx1ZSBvZiB0aGVpclxuXHRcdFx0XHRcdC8vIG93biBkZXJpdmVzIHRoZW1cblx0XHRcdFx0XHRjb25zdCBjb3ZlcmVkID0gdmFsdWUua2luZCA9PT0gJ3JlZ2lzdHJ5T2YnXG5cdFx0XHRcdFx0XHQ/IG5vZGUuZnVsbFBhdGggPT09IHZhbHVlLmZ1bGxQYXRoIHx8IHZhbHVlLmZ1bGxQYXRoLnN0YXJ0c1dpdGgoYCR7bm9kZS5mdWxsUGF0aH0uYClcblx0XHRcdFx0XHRcdDogbm9kZS5mdWxsUGF0aCA9PT0gdmFsdWUuZnVsbFBhdGg7XG5cdFx0XHRcdFx0aWYgKGNvdmVyZWQpIHtcblx0XHRcdFx0XHRcdHJlc3VsdC5hZGQobm9kZS5mdWxsUGF0aCk7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHRwcml2YXRlIGJ1aWxkZXJJbXBvcnROYW1lICh2YWx1ZTogQnVpbGRlclZhbHVlKTogc3RyaW5nIHtcblx0XHRjb25zdCBub2RlID0gdGhpcy5ncmFwaC5maW5kVHlwZSh2YWx1ZS5mdWxsUGF0aCk7XG5cdFx0Y29uc3QgaW5zdGFuY2VOYW1lID0gbm9kZSA/IHRoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShub2RlKSA6ICcnO1xuXHRcdGNvbnN0IHJlc3VsdCA9IHZhbHVlLm5hbWUgPT09IGluc3RhbmNlTmFtZSA/IGAke3ZhbHVlLm5hbWV9Q3RvcmAgOiB2YWx1ZS5uYW1lO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHRwcml2YXRlIHB1c2hCdWlsZGVySW1wb3J0cyAobGluZXM6IHN0cmluZ1tdKTogdm9pZCB7XG5cdFx0Y29uc3QgbmFtZWQgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Y29uc3QgZGVmYXVsdHMgPSBuZXcgTWFwPHN0cmluZywgc3RyaW5nW10+KCk7XG5cdFx0Y29uc3QgZnJvbUJ1aWxkZXI6IHN0cmluZ1tdID0gW107XG5cdFx0Zm9yIChjb25zdCB2YWx1ZSBvZiB0aGlzLmJ1aWxkZXJWYWx1ZXMpIHtcblx0XHRcdGNvbnN0IGdyb3VwID0gdmFsdWUuZGVmYXVsdEltcG9ydCA/IGRlZmF1bHRzIDogbmFtZWQ7XG5cdFx0XHRjb25zdCBpbXBvcnROYW1lID0gdGhpcy5idWlsZGVySW1wb3J0TmFtZSh2YWx1ZSk7XG5cdFx0XHRjb25zdCBuYW1lcyA9IGdyb3VwLmdldCh2YWx1ZS5zb3VyY2VGaWxlKSA/PyBbXTtcblx0XHRcdGNvbnN0IGJpbmRpbmcgPSBpbXBvcnROYW1lID09PSB2YWx1ZS5uYW1lID8gdmFsdWUubmFtZSA6IGAke3ZhbHVlLm5hbWV9IGFzICR7aW1wb3J0TmFtZX1gO1xuXHRcdFx0bmFtZXMucHVzaChiaW5kaW5nKTtcblx0XHRcdGdyb3VwLnNldCh2YWx1ZS5zb3VyY2VGaWxlLCBuYW1lcyk7XG5cdFx0XHRpZiAodmFsdWUua2luZCA9PT0gJ3JlZ2lzdHJ5T2YnKSB7XG5cdFx0XHRcdGZyb21CdWlsZGVyLnB1c2goYFJlZ2lzdHJ5T2Y8dHlwZW9mICR7aW1wb3J0TmFtZX0+YCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGZvciAoY29uc3QgWyBzb3VyY2VGaWxlLCBuYW1lcyBdIG9mIG5hbWVkKSB7XG5cdFx0XHRjb25zdCBtb2R1bGVQYXRoID0gdGhpcy5yZXNvbHZlTW9kdWxlUGF0aChzb3VyY2VGaWxlKTtcblx0XHRcdGxpbmVzLnB1c2goYGltcG9ydCB0eXBlIHsgJHtuYW1lcy5qb2luKCcsICcpfSB9IGZyb20gJyR7bW9kdWxlUGF0aH0nO2ApO1xuXHRcdH1cblx0XHRmb3IgKGNvbnN0IFsgc291cmNlRmlsZSwgbmFtZXMgXSBvZiBkZWZhdWx0cykge1xuXHRcdFx0Y29uc3QgbW9kdWxlUGF0aCA9IHRoaXMucmVzb2x2ZU1vZHVsZVBhdGgoc291cmNlRmlsZSk7XG5cdFx0XHRmb3IgKGNvbnN0IG5hbWUgb2YgbmFtZXMpIHtcblx0XHRcdFx0bGluZXMucHVzaChgaW1wb3J0IHR5cGUgJHtuYW1lfSBmcm9tICcke21vZHVsZVBhdGh9JztgKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0aWYgKGZyb21CdWlsZGVyLmxlbmd0aCA+IDApIHtcblx0XHRcdGxpbmVzLnB1c2goYHR5cGUgRnJvbUJ1aWxkZXIgPSAke2Zyb21CdWlsZGVyLmpvaW4oJyAmICcpfTtgKTtcblx0XHRcdGxpbmVzLnB1c2goJycpO1xuXHRcdH1cblx0fVxuXG5cdC8qKlxuXHRcdCogR2VuZXJhdGUgYSB0eXBlcy50cyBmaWxlIHdpdGggY29tcGxldGUgaW5zdGFuY2UgaW50ZXJmYWNlc1xuXHRcdCogVGhpcyBpbmNsdWRlcyBhbGwgcHJvcGVydGllcyBleHRyYWN0ZWQgZnJvbSB0aGUgY29uc3RydWN0b3JzXG5cdFx0Ki9cblx0Z2VuZXJhdGVUeXBlc0ZpbGUgKCk6IEdlbmVyYXRlZFR5cGVzIHtcblx0XHRjb25zdCBsaW5lczogc3RyaW5nW10gPSBbXTtcblx0XHRjb25zdCBnZW5lcmF0ZWRUeXBlczogc3RyaW5nW10gPSBbXTtcblxuXHRcdC8vIEhlYWRlclxuXHRcdGxpbmVzLnB1c2goJy8vIEdlbmVyYXRlZCBieSBAbW5lbW9uaWNhL3RhY3RpY2EgLSBETyBOT1QgRURJVCcpO1xuXHRcdGxpbmVzLnB1c2goJy8vIFRoaXMgZmlsZSBwcm92aWRlcyBjb21wbGV0ZSBUeXBlU2NyaXB0IGludGVyZmFjZXMgZm9yIE1uZW1vbmljYSB0eXBlcycpO1xuXHRcdGxpbmVzLnB1c2goJycpO1xuXG5cdFx0Y29uc3QgZGVyaXZlZCA9IHRoaXMuZGVyaXZlZFR5cGVQYXRocygpO1xuXHRcdGxldCBuZWVkc1Byb3RvRmxhdCA9IGZhbHNlO1xuXHRcdGxldCBuZWVkc0xvb2tlZFVwQ29uc3RydWN0b3IgPSBmYWxzZTtcblx0XHRmb3IgKGNvbnN0IHJvb3Qgb2YgdGhpcy5ncmFwaC5yb290cy52YWx1ZXMoKSkge1xuXHRcdFx0Zm9yIChjb25zdCBub2RlIG9mIHRoaXMuZ3JhcGguZGZzKHJvb3QpKSB7XG5cdFx0XHRcdGlmIChub2RlLm1ldGFkYXRhT25seSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGlmIChub2RlLnBhcmVudCAmJiAhZGVyaXZlZC5oYXMobm9kZS5mdWxsUGF0aCkpIHtcblx0XHRcdFx0XHRuZWVkc1Byb3RvRmxhdCA9IHRydWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgaGFzRW1pdHRlZENoaWxkcmVuID0gQXJyYXkuZnJvbShub2RlLmNoaWxkcmVuLnZhbHVlcygpKS5zb21lKGNoaWxkID0+ICFjaGlsZC5tZXRhZGF0YU9ubHkpO1xuXHRcdFx0XHRpZiAoIW5vZGUuY29sbGVjdGlvbklkICYmIGhhc0VtaXR0ZWRDaGlsZHJlbiAmJiAhZGVyaXZlZC5oYXMobm9kZS5mdWxsUGF0aCkpIHtcblx0XHRcdFx0XHRuZWVkc0xvb2tlZFVwQ29uc3RydWN0b3IgPSB0cnVlO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdGNvbnN0IG1uZW1vbmljYUltcG9ydHM6IHN0cmluZ1tdID0gW107XG5cdFx0aWYgKG5lZWRzUHJvdG9GbGF0KSB7XG5cdFx0XHRtbmVtb25pY2FJbXBvcnRzLnB1c2goJ1Byb3RvRmxhdCcpO1xuXHRcdH1cblx0XHRpZiAobmVlZHNMb29rZWRVcENvbnN0cnVjdG9yKSB7XG5cdFx0XHRtbmVtb25pY2FJbXBvcnRzLnB1c2goJ0xvb2tlZFVwQ29uc3RydWN0b3InKTtcblx0XHR9XG5cdFx0aWYgKGRlcml2ZWQuc2l6ZSA+IDApIHtcblx0XHRcdG1uZW1vbmljYUltcG9ydHMucHVzaCgnTG9va2VkVXBJbnN0YW5jZScpO1xuXHRcdH1cblx0XHRpZiAobW5lbW9uaWNhSW1wb3J0cy5sZW5ndGggPiAwKSB7XG5cdFx0XHRsaW5lcy5wdXNoKGBpbXBvcnQgdHlwZSB7ICR7bW5lbW9uaWNhSW1wb3J0cy5qb2luKCcsICcpfSB9IGZyb20gJ21uZW1vbmljYSc7YCk7XG5cdFx0fVxuXHRcdGlmIChkZXJpdmVkLnNpemUgPiAwIHx8IG5lZWRzTG9va2VkVXBDb25zdHJ1Y3Rvcikge1xuXHRcdFx0bGluZXMucHVzaCgnaW1wb3J0IHR5cGUgeyBUeXBlUmVnaXN0cnkgfSBmcm9tIFxcJy4vcmVnaXN0cnlcXCc7Jyk7XG5cdFx0fVxuXHRcdGlmIChtbmVtb25pY2FJbXBvcnRzLmxlbmd0aCA+IDAgfHwgZGVyaXZlZC5zaXplID4gMCB8fCBuZWVkc0xvb2tlZFVwQ29uc3RydWN0b3IpIHtcblx0XHRcdGxpbmVzLnB1c2goJycpO1xuXHRcdH1cblxuXHRcdC8vIEdlbmVyYXRlIGNvbXBsZXRlIGluc3RhbmNlIGludGVyZmFjZXMgZm9yIGRlZmF1bHQtY29sbGVjdGlvbiB0eXBlcyBhbmRcblx0XHQvLyBmb3IgY3VzdG9tIGNvbGxlY3Rpb25zIHRoYXQgZGVjbGFyZSBhIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlXG5cdFx0Ly8gKE9wdGlvbiBCKS4gQ3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgd2l0aG91dCBhIHJlZ2lzdHJ5IGludGVyZmFjZSBhcmVcblx0XHQvLyBpc29sYXRlZCBhdCBydW50aW1lIGFuZCBhcmUgbm90IGVtaXR0ZWQuIENvbXB1dGVkIGxvb3AgZGVmaW5pdGlvbnMgYXJlXG5cdFx0Ly8gbWV0YWRhdGEtb25seSBpbiBldmVyeSBjb2xsZWN0aW9uLlxuXHRcdGZvciAoY29uc3Qgcm9vdCBvZiB0aGlzLmdyYXBoLnJvb3RzLnZhbHVlcygpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IG5vZGUgb2YgdGhpcy5ncmFwaC5kZnMocm9vdCkpIHtcblx0XHRcdFx0aWYgKG5vZGUubWV0YWRhdGFPbmx5IHx8IChub2RlLmNvbGxlY3Rpb25JZCAmJiAhbm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUpKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0Y29uc3QgaW50ZXJmYWNlTmFtZSA9IHRoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShub2RlKTtcblx0XHRcdFx0Z2VuZXJhdGVkVHlwZXMucHVzaChpbnRlcmZhY2VOYW1lKTtcblx0XHRcdFx0aWYgKGRlcml2ZWQuaGFzKG5vZGUuZnVsbFBhdGgpKSB7XG5cdFx0XHRcdFx0bGluZXMucHVzaChgZXhwb3J0IHR5cGUgJHtpbnRlcmZhY2VOYW1lfSA9IExvb2tlZFVwSW5zdGFuY2U8VHlwZVJlZ2lzdHJ5LCAnJHtub2RlLmZ1bGxQYXRofSc+O2ApO1xuXHRcdFx0XHRcdGxpbmVzLnB1c2goJycpO1xuXHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdHRoaXMuZ2VuZXJhdGVDb21wbGV0ZUluc3RhbmNlSW50ZXJmYWNlKG5vZGUsIGxpbmVzKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiB7XG5cdFx0XHRjb250ZW50IDogbGluZXMuam9pbignXFxuJyksXG5cdFx0XHR0eXBlcyAgIDogZ2VuZXJhdGVkVHlwZXMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHRcdCAqIEdlbmVyYXRlIGEgY29tcGxldGUgaW5zdGFuY2UgdHlwZSBhbGlhcyB3aXRoIGFsbCBwcm9wZXJ0aWVzXG5cdFx0ICogVGhpcyBpcyBmb3IgdGhlIHR5cGVzLnRzIGZpbGUgdGhhdCB1c2VycyBpbXBvcnQgZnJvbVxuXHRcdCAqL1xuXHRwcml2YXRlIGdlbmVyYXRlQ29tcGxldGVJbnN0YW5jZUludGVyZmFjZSAobm9kZTogVHlwZU5vZGUsIGxpbmVzOiBzdHJpbmdbXSk6IHZvaWQge1xuXHRcdGNvbnN0IHR5cGVOYW1lID0gdGhpcy5nZXRJbnN0YW5jZVR5cGVOYW1lKG5vZGUpO1xuXG5cdFx0aWYgKG5vZGUuaW5zdGFuY2VUeXBlT3ZlcnJpZGUgPT09ICdhbnknKSB7XG5cdFx0XHRsaW5lcy5wdXNoKGBleHBvcnQgdHlwZSAke3R5cGVOYW1lfSA9IGFueTtgKTtcblx0XHRcdGxpbmVzLnB1c2goJycpO1xuXHRcdFx0cmV0dXJuO1xuXHRcdH1cblx0XHRpZiAobm9kZS5wYXJlbnQpIHtcblx0XHRcdC8vIE5lc3RlZCB0eXBlOiBVc2UgUHJvdG9GbGF0IHRvIHByb3Blcmx5IGV4Y2x1ZGUgb3ZlcnJpZGRlbiBwcm9wZXJ0aWVzXG5cdFx0XHRsaW5lcy5wdXNoKGBleHBvcnQgdHlwZSAke3R5cGVOYW1lfSA9IFByb3RvRmxhdDwke3RoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShub2RlLnBhcmVudCl9LCB7YCk7XG5cdFx0fSBlbHNlIHtcblx0XHRcdC8vIFJvb3QgdHlwZToganVzdCB0aGUgcHJvcGVydGllcyBvYmplY3Rcblx0XHRcdGxpbmVzLnB1c2goYGV4cG9ydCB0eXBlICR7dHlwZU5hbWV9ID0ge2ApO1xuXHRcdH1cblxuXHRcdC8vIEFkZCBpbnN0YW5jZSBwcm9wZXJ0aWVzIGV4dHJhY3RlZCBmcm9tIHRoZSBjb25zdHJ1Y3RvclxuXHRcdGZvciAoY29uc3QgWyBwcm9wTmFtZSwgcHJvcEluZm8gXSBvZiBub2RlLnByb3BlcnRpZXMuZW50cmllcygpKSB7XG5cdFx0XHRjb25zdCBvcHRpb25hbCA9IHByb3BJbmZvLm9wdGlvbmFsID8gJz8nIDogJyc7XG5cdFx0XHRjb25zdCByZWFkb25seSA9IHByb3BJbmZvLnJlYWRvbmx5ID8gJ3JlYWRvbmx5ICcgOiAnJztcblx0XHRcdGxpbmVzLnB1c2goYFxcdCR7cmVhZG9ubHl9JHtwcm9wTmFtZX0ke29wdGlvbmFsfTogJHt0aGlzLnJlc29sdmVUeXBlSW5TdHJpbmcocHJvcEluZm8udHlwZSwgbm9kZSl9O2ApO1xuXHRcdH1cblxuXHRcdC8vIEFkZCBuZXN0ZWQgY29uc3RydWN0b3IgcHJvcGVydGllcyBmb3Igbm9uLWxlYWYgbm9kZXNcblx0XHQvLyBMZWFmIG5vZGVzIChubyBjaGlsZHJlbikgZG9uJ3QgZ2V0IGNvbnN0cnVjdG9yIHByb3BlcnRpZXNcblx0XHQvLyBUaGlzIGZvbGxvd3MgbW5lbW9uaWNhJ3Mgc3RyaWN0Q2hhaW4gYmVoYXZpb3Jcblx0XHRpZiAobm9kZS5jaGlsZHJlbi5zaXplID4gMCkge1xuXHRcdFx0Zm9yIChjb25zdCBjaGlsZCBvZiBub2RlLmNoaWxkcmVuLnZhbHVlcygpKSB7XG5cdFx0XHRcdHRoaXMucHVzaENoaWxkQ29uc3RydWN0b3JGaWVsZChsaW5lcywgJycsIGNoaWxkKTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHQvLyBGb3IgbmVzdGVkIHR5cGVzLCBhZGQgdGhpcyBub2RlJ3MgY29uc3RydWN0b3IgYW5kIGFsbCBzaWJsaW5ncyBmcm9tIHNhbWUgcGFyZW50IGFzIHVuZGVmaW5lZFxuXHRcdC8vIFRoaXMgaXMgbmVlZGVkIGZvciBzdHJpY3QgY2hhaW4gYmVoYXZpb3IgLSBwYXJlbnQgdW5kZWZpbmVkcyBhcmUgaW5oZXJpdGVkIHZpYSBQcm90b0ZsYXQuXG5cdFx0Ly8gT3B0aW9uYWwgb24gZGVmYXVsdC1jb2xsZWN0aW9uIHR5cGVzIHNvIGJ1aWxkZXIgY2hpbGRyZW4gY2FuIGNyb3NzO1xuXHRcdC8vIE9wdGlvbiBCIGtlZXBzIHJlcXVpcmVkIG1hcmtlcnMuXG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHRjb25zdCBvcHRpb25hbCA9IG5vZGUuY29sbGVjdGlvbklkID8gJycgOiAnPyc7XG5cdFx0XHQvLyBBZGQgdGhpcyBub2RlJ3Mgb3duIGNvbnN0cnVjdG9yIGFzIHVuZGVmaW5lZFxuXHRcdFx0bGluZXMucHVzaChgXFx0JHtub2RlLm5hbWV9JHtvcHRpb25hbH06IHVuZGVmaW5lZDtgKTtcblxuXHRcdFx0Ly8gQWRkIGFsbCBzaWJsaW5ncyAob3RoZXIgY2hpbGRyZW4gb2YgdGhlIHNhbWUgcGFyZW50KSBhcyB1bmRlZmluZWRcblx0XHRcdGZvciAoY29uc3Qgc2libGluZyBvZiBub2RlLnBhcmVudC5jaGlsZHJlbi52YWx1ZXMoKSkge1xuXHRcdFx0XHRpZiAoc2libGluZy5uYW1lICE9PSBub2RlLm5hbWUgJiYgIXNpYmxpbmcubWV0YWRhdGFPbmx5KSB7XG5cdFx0XHRcdFx0bGluZXMucHVzaChgXFx0JHtzaWJsaW5nLm5hbWV9JHtvcHRpb25hbH06IHVuZGVmaW5lZDtgKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIENsb3NlIHRoZSB0eXBlIHByb3Blcmx5IC0gUHJvdG9GbGF0IHVzZXMgfT47IGZvciBuZXN0ZWQsIH07IGZvciByb290XG5cdFx0aWYgKG5vZGUucGFyZW50KSB7XG5cdFx0XHRsaW5lcy5wdXNoKCd9PjsnKTtcblx0XHR9IGVsc2Uge1xuXHRcdFx0bGluZXMucHVzaCgnfTsnKTtcblx0XHR9XG5cdFx0bGluZXMucHVzaCgnJyk7XG5cdH1cblxuXHQvKipcblx0XHQgKiBFbWl0IG9uZSBuZXN0ZWQtY3RvciBmaWVsZC4gRGVmYXVsdC1jb2xsZWN0aW9uIGNoaWxkcmVuIHVzZSBjb3JlJ3Ncblx0XHQgKiBjb21wbGV0ZSBjb25zdHJ1Y3RvciBzdXJmYWNlLiBPcHRpb24gQiB1c2VzIGR1YWwgc2lnbmF0dXJlczpcblx0XHQgKiBjb25zdHJ1Y3QgKyB0aGUgY2hhaW4tdGlwIENBTEwgZm9ybSwgYm90aCByZXNvbHZpbmcgdGhyb3VnaFxuXHRcdCAqIGdldENvbnN0cnVjdG9yUmVzdWx0VHlwZS5cblx0XHQgKi9cblx0cHJpdmF0ZSBwdXNoQ2hpbGRDb25zdHJ1Y3RvckZpZWxkIChcblx0XHRsaW5lczogc3RyaW5nW10sXG5cdFx0aW5kZW50U3RyOiBzdHJpbmcsXG5cdFx0Y2hpbGQ6IFR5cGVOb2RlXG5cdCk6IHZvaWQge1xuXHRcdGlmIChjaGlsZC5tZXRhZGF0YU9ubHkpIHtcblx0XHRcdHJldHVybjtcblx0XHR9XG5cdFx0aWYgKCFjaGlsZC5jb2xsZWN0aW9uSWQpIHtcblx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5nZXRGdWxsUGF0aChjaGlsZCk7XG5cdFx0XHRsaW5lcy5wdXNoKGAke2luZGVudFN0cn1cXHQke2NoaWxkLm5hbWV9OiBMb29rZWRVcENvbnN0cnVjdG9yPFR5cGVSZWdpc3RyeSwgJyR7ZnVsbFBhdGh9JywgdHJ1ZT47YCk7XG5cdFx0XHRyZXR1cm47XG5cdFx0fVxuXHRcdGNvbnN0IGNoaWxkSW5zdGFuY2VUeXBlID0gdGhpcy5nZXRDb25zdHJ1Y3RvclJlc3VsdFR5cGUoY2hpbGQpO1xuXHRcdGNvbnN0IGNvbnN0cnVjdG9yUGFyYW1zID0gdGhpcy5nZW5lcmF0ZUNvbnN0cnVjdG9yUGFyYW1zKGNoaWxkKTtcblx0XHRsaW5lcy5wdXNoKGAke2luZGVudFN0cn1cXHQke2NoaWxkLm5hbWV9OiB7YCk7XG5cdFx0bGluZXMucHVzaChgJHtpbmRlbnRTdHJ9XFx0XFx0bmV3ICR7Y29uc3RydWN0b3JQYXJhbXN9OiAke2NoaWxkSW5zdGFuY2VUeXBlfTtgKTtcblx0XHRsaW5lcy5wdXNoKGAke2luZGVudFN0cn1cXHRcXHQke2NvbnN0cnVjdG9yUGFyYW1zfTogJHtjaGlsZEluc3RhbmNlVHlwZX07YCk7XG5cdFx0bGluZXMucHVzaChgJHtpbmRlbnRTdHJ9XFx0fTtgKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBUaGUgdHlwZSBhIGNvbnN0cnVjdG9yIGludm9jYXRpb24gcmVzb2x2ZXMgdG86IHRoZSBpbnN0YW5jZSB0eXBlLCBvclxuXHQgKiBQcm9taXNlPEluc3RhbmNlVHlwZT4gZm9yIGFzeW5jIGhhbmRsZXJzIChpc0FzeW5jKS4gVGhlIGluc3RhbmNlIHR5cGVcblx0ICogaXRzZWxmIGlzIG5ldmVyIHdyYXBwZWQg4oCUIG9ubHkgdGhlIGNvbnN0cnVjdG9yIFJFU1VMVCBwb3NpdGlvbnNcblx0ICogKHN1YnR5cGUgcHJvcGVydHkgdHdpbnMgKyByZWdpc3RyeSBlbnRyaWVzKS5cblx0ICovXG5cdHByaXZhdGUgZ2V0Q29uc3RydWN0b3JSZXN1bHRUeXBlIChub2RlOiBUeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0Y29uc3QgaW5zdGFuY2VUeXBlID0gdGhpcy5nZXRJbnN0YW5jZVR5cGVOYW1lKG5vZGUpO1xuXHRcdGNvbnN0IHJlc3VsdCA9IG5vZGUuaXNBc3luYyA/IGBQcm9taXNlPCR7aW5zdGFuY2VUeXBlfT5gIDogaW5zdGFuY2VUeXBlO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0XHQgKiBHZW5lcmF0ZSBhIHNpbXBsZSB0eXBlIGRlY2xhcmF0aW9uIGZvciBhIHNpbmdsZSB0eXBlXG5cdFx0ICovXG5cdGdlbmVyYXRlU2luZ2xlVHlwZSAobm9kZTogVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGNvbnN0IGxpbmVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdHRoaXMuZ2VuZXJhdGVDb21wbGV0ZUluc3RhbmNlSW50ZXJmYWNlKG5vZGUsIGxpbmVzKTtcblx0XHRyZXR1cm4gbGluZXMuam9pbignXFxuJyk7XG5cdH1cblxuXHQvKipcblx0XHQgKiBHZW5lcmF0ZSBUeXBlUmVnaXN0cnkgaW50ZXJmYWNlIGZvciB0eXBlLXNhZmUgbG9va3VwKCkgZnVuY3Rpb25cblx0XHQgKiBBdWdtZW50IG1uZW1vbmljYSdzIFR5cGVSZWdpc3RyeSBzbyBsb29rdXAoJ1R5cGVOYW1lJykgcmV0dXJucyB0aGUgdHlwZWQgY29uc3RydWN0b3Jcblx0XHQgKi9cblx0Z2VuZXJhdGVUeXBlUmVnaXN0cnkgKCk6IEdlbmVyYXRlZFR5cGVzIHtcblx0XHRjb25zdCBsaW5lczogc3RyaW5nW10gPSBbXTtcblx0XHRjb25zdCBnZW5lcmF0ZWRUeXBlczogc3RyaW5nW10gPSBbXTtcblxuXHRcdC8vIEhlYWRlclxuXHRcdGxpbmVzLnB1c2goJy8vIEdlbmVyYXRlZCBUeXBlUmVnaXN0cnkgZm9yIHR5cGUtc2FmZSBtbmVtb25pY2EubG9va3VwKCknKTtcblx0XHRsaW5lcy5wdXNoKCcvLyBUaGlzIGZpbGUgYXVnbWVudHMgbW5lbW9uaWNhXFwncyBUeXBlUmVnaXN0cnkgdmlhIGRlY2xhcmF0aW9uIG1lcmdpbmcuJyk7XG5cdFx0bGluZXMucHVzaCgnLy8nKTtcblx0XHRsaW5lcy5wdXNoKCcvLyBVc2FnZTonKTtcblx0XHRsaW5lcy5wdXNoKCcvLyAgIGltcG9ydCB7IGxvb2t1cCB9IGZyb20gXFwnbW5lbW9uaWNhXFwnOycpO1xuXHRcdGxpbmVzLnB1c2goJy8vICAgaW1wb3J0IFxcJy4vLnRhY3RpY2EvcmVnaXN0cnlcXCc7ICAvLyBhcHBsaWVzIHRoZSBhdWdtZW50YXRpb24nKTtcblx0XHRsaW5lcy5wdXNoKCcvLyAgIGNvbnN0IE15VHlwZSA9IGxvb2t1cChcXCdNeVR5cGVcXCcpOycpO1xuXHRcdGxpbmVzLnB1c2goJy8vICAgLy8gVHlwZVNjcmlwdCBrbm93czogTXlUeXBlIGlzIHRoZSB0eXBlZCBjb25zdHJ1Y3RvciBmb3IgTXlUeXBlJyk7XG5cdFx0bGluZXMucHVzaCgnLy8gICBjb25zdCBpbnN0YW5jZSA9IG5ldyBNeVR5cGUoeyAvKiBjb25zdHJ1Y3RvciBhcmdzICovIH0pOycpO1xuXHRcdGxpbmVzLnB1c2goJy8vICAgLy8gaW5zdGFuY2UgaGFzIGZ1bGwgaW50ZWxsaXNlbnNlIGZvciB0aGUgZ2VuZXJhdGVkIHR5cGUnKTtcblx0XHRsaW5lcy5wdXNoKCcnKTtcblxuXHRcdGNvbnN0IGRlcml2ZWQgPSB0aGlzLmRlcml2ZWRUeXBlUGF0aHMoKTtcblx0XHR0aGlzLnB1c2hCdWlsZGVySW1wb3J0cyhsaW5lcyk7XG5cblx0XHRjb25zdCBleHRyYWN0ZWRTaWduYXR1cmVzOiBzdHJpbmdbXSA9IFtdO1xuXHRcdGxldCBuZWVkc1JlZ2lzdHJ5RW50cnkgPSBmYWxzZTtcblx0XHRsZXQgbmVlZHNBc3luY1JlZ2lzdHJ5RW50cnkgPSBmYWxzZTtcblx0XHRmb3IgKGNvbnN0IHJvb3Qgb2YgdGhpcy5ncmFwaC5yb290cy52YWx1ZXMoKSkge1xuXHRcdFx0Zm9yIChjb25zdCBub2RlIG9mIHRoaXMuZ3JhcGguZGZzKHJvb3QpKSB7XG5cdFx0XHRcdGlmIChub2RlLm1ldGFkYXRhT25seSB8fFxuXHRcdFx0XHRcdChub2RlLmNvbGxlY3Rpb25JZCAmJiAhbm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWUpIHx8IGRlcml2ZWQuaGFzKG5vZGUuZnVsbFBhdGgpKSB7XG5cdFx0XHRcdFx0Y29udGludWU7XG5cdFx0XHRcdH1cblx0XHRcdFx0aWYgKCFub2RlLmNvbGxlY3Rpb25JZCkge1xuXHRcdFx0XHRcdGlmIChub2RlLmlzQXN5bmMpIHtcblx0XHRcdFx0XHRcdG5lZWRzQXN5bmNSZWdpc3RyeUVudHJ5ID0gdHJ1ZTtcblx0XHRcdFx0XHR9IGVsc2Uge1xuXHRcdFx0XHRcdFx0bmVlZHNSZWdpc3RyeUVudHJ5ID0gdHJ1ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0ZXh0cmFjdGVkU2lnbmF0dXJlcy5wdXNoKHRoaXMuZ2VuZXJhdGVDb25zdHJ1Y3RvclNpZ25hdHVyZShub2RlKSk7XG5cdFx0XHRcdGlmIChub2RlLnBhcmVudCkge1xuXHRcdFx0XHRcdGV4dHJhY3RlZFNpZ25hdHVyZXMucHVzaCh0aGlzLmdldEluc3RhbmNlVHlwZU5hbWUobm9kZS5wYXJlbnQpKTtcblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdC8vIEltcG9ydCBpbnN0YW5jZSB0eXBlcyBmcm9tIHR5cGVzLnRzLiBEZXJpdmVkIGFsaWFzZXMgYXJlIG5lZWRlZCBvbmx5XG5cdFx0Ly8gd2hlbiBhbiBleHRyYWN0ZWQgY29uc3RydWN0b3Igc2lnbmF0dXJlIG9yIFJlZ2lzdHJ5RW50cnkgcGFyZW50IHJlZmVycyB0byB0aGVtLlxuXHRcdC8vIFNraXAgY3VzdG9tLWNvbGxlY3Rpb24gdHlwZXMgdGhhdCBoYXZlIG5vIHVzZXItcHJvdmlkZWQgcmVnaXN0cnkgaW50ZXJmYWNlLlxuXHRcdGxpbmVzLnB1c2goJ2ltcG9ydCB0eXBlIHsnKTtcblx0XHRmb3IgKGNvbnN0IHJvb3Qgb2YgdGhpcy5ncmFwaC5yb290cy52YWx1ZXMoKSkge1xuXHRcdFx0Zm9yIChjb25zdCBub2RlIG9mIHRoaXMuZ3JhcGguZGZzKHJvb3QpKSB7XG5cdFx0XHRcdGlmIChub2RlLm1ldGFkYXRhT25seSB8fCAobm9kZS5jb2xsZWN0aW9uSWQgJiYgIW5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lKSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGZ1bGxQYXRoID0gdGhpcy5nZXRGdWxsUGF0aChub2RlKTtcblx0XHRcdFx0Y29uc3QgaW5zdGFuY2VUeXBlTmFtZSA9IHRoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShub2RlKTtcblx0XHRcdFx0aWYgKGRlcml2ZWQuaGFzKGZ1bGxQYXRoKSkge1xuXHRcdFx0XHRcdGNvbnN0IHJlZmVyZW5jZSA9IG5ldyBSZWdFeHAoYFxcXFxiJHtpbnN0YW5jZVR5cGVOYW1lfVxcXFxiYCk7XG5cdFx0XHRcdFx0Y29uc3QgdXNlZCA9IGV4dHJhY3RlZFNpZ25hdHVyZXMuc29tZShzaWduYXR1cmUgPT4gcmVmZXJlbmNlLnRlc3Qoc2lnbmF0dXJlKSk7XG5cdFx0XHRcdFx0aWYgKCF1c2VkKSB7XG5cdFx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdFx0bGluZXMucHVzaChgXFx0JHtpbnN0YW5jZVR5cGVOYW1lfSxgKTtcblx0XHRcdFx0Z2VuZXJhdGVkVHlwZXMucHVzaChpbnN0YW5jZVR5cGVOYW1lKTtcblx0XHRcdH1cblx0XHR9XG5cdFx0bGluZXMucHVzaChgfSBmcm9tICcke3RoaXMuaW1wb3J0UGF0aCgnLi90eXBlcycpfSc7YCk7XG5cdFx0bGluZXMucHVzaCgnJyk7XG5cblx0XHQvLyBHZW5lcmF0ZSBtb2R1bGUgYXVnbWVudGF0aW9uIGZvciBtbmVtb25pY2EgVHlwZVJlZ2lzdHJ5XG5cdFx0bGluZXMucHVzaCgnLyoqJyk7XG5cdFx0bGluZXMucHVzaCgnICogVHlwZSByZWdpc3RyeSBhdWdtZW50aW5nIG1uZW1vbmljYVxcJ3MgVHlwZVJlZ2lzdHJ5IGludGVyZmFjZScpO1xuXHRcdGxpbmVzLnB1c2goJyAqIFRoaXMgZW5hYmxlcyB0eXBlLXNhZmUgbG9va3VwKCkgd2l0aG91dCBleHBsaWNpdCB0eXBlIGFyZ3VtZW50cycpO1xuXHRcdGxpbmVzLnB1c2goJyAqJyk7XG5cdFx0bGluZXMucHVzaCgnICogVXNhZ2U6IGNvbnN0IFNvbWVUeXBlID0gbG9va3VwKFxcJ1NvbWVUeXBlXFwnKTsgLy8gRnVsbHkgdHlwZWQhJyk7XG5cdFx0bGluZXMucHVzaCgnICovJyk7XG5cdFx0bGluZXMucHVzaCgnZGVjbGFyZSBtb2R1bGUgXFwnbW5lbW9uaWNhXFwnIHsnKTtcblx0XHRjb25zdCBmcm9tQnVpbGRlciA9IHRoaXMuYnVpbGRlclZhbHVlcy5zb21lKHZhbHVlID0+IHZhbHVlLmtpbmQgPT09ICdyZWdpc3RyeU9mJyk7XG5cdFx0bGluZXMucHVzaChgXFx0aW50ZXJmYWNlIFR5cGVSZWdpc3RyeSAke2Zyb21CdWlsZGVyID8gJ2V4dGVuZHMgRnJvbUJ1aWxkZXIgJyA6ICcnfXtgKTtcblxuXHRcdC8vIEdlbmVyYXRlIGVudHJpZXMgZm9yIGFsbCB0eXBlIHBhdGhzIHRoYXQgYmVsb25nIHRvIHRoZSBkZWZhdWx0L2dsb2JhbCBjb2xsZWN0aW9uLlxuXHRcdC8vIFR5cGVzIHRoYXQgbGl2ZSBpbiBhIGN1c3RvbSBjb2xsZWN0aW9uIChjb2xsZWN0aW9uSWQgc2V0KSBhcmUgaXNvbGF0ZWQgYXQgcnVudGltZVxuXHRcdC8vIGFuZCBhcmUgbm90IHJlYWNoYWJsZSB0aHJvdWdoIGZyZWUgbG9va3VwKCksIHNvIHRoZXkgbXVzdCBub3QgYmUgYWRkZWQgdG8gdGhlXG5cdFx0Ly8gZ2xvYmFsIFR5cGVSZWdpc3RyeSBhdWdtZW50YXRpb24uXG5cdFx0Zm9yIChjb25zdCByb290IG9mIHRoaXMuZ3JhcGgucm9vdHMudmFsdWVzKCkpIHtcblx0XHRcdGZvciAoY29uc3Qgbm9kZSBvZiB0aGlzLmdyYXBoLmRmcyhyb290KSkge1xuXHRcdFx0XHRpZiAobm9kZS5jb2xsZWN0aW9uSWQgfHwgbm9kZS5tZXRhZGF0YU9ubHkpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHRjb25zdCBmdWxsUGF0aCA9IHRoaXMuZ2V0RnVsbFBhdGgobm9kZSk7XG5cdFx0XHRcdGlmIChkZXJpdmVkLmhhcyhmdWxsUGF0aCkpIHtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXHRcdFx0XHQvLyBEZWZhdWx0IGV4dHJhY3RlZCBlbnRyaWVzIHVzZSBjb3JlJ3MgY29tcGxldGUgY29uc3RydWN0b3Igc3VyZmFjZS5cblx0XHRcdFx0Ly8gQXN5bmNSZWdpc3RyeUVudHJ5IG93bnMgdGhlIFByb21pc2UgcmVzdWx0LCBzbyBpdHMgRiBzdGF5cyB0aGVcblx0XHRcdFx0Ly8gcmVzb2x2ZWQgaW5zdGFuY2UgZm9yIGhvb2tzIGFuZCBpbmhlcml0YW5jZS5cblx0XHRcdFx0Y29uc3QgaW5zdGFuY2VUeXBlID0gdGhpcy5nZXRJbnN0YW5jZVR5cGVOYW1lKG5vZGUpO1xuXHRcdFx0XHRjb25zdCBwYXJlbnRUeXBlID0gbm9kZS5wYXJlbnQgPyB0aGlzLmdldEluc3RhbmNlVHlwZU5hbWUobm9kZS5wYXJlbnQpIDogJ29iamVjdCc7XG5cdFx0XHRcdGNvbnN0IGNvbnN0cnVjdG9yQXJncyA9IHRoaXMuZ2VuZXJhdGVDb25zdHJ1Y3RvckFyZ3Mobm9kZSk7XG5cdFx0XHRcdGNvbnN0IGVudHJ5S2luZCA9IG5vZGUuaXNBc3luYyA/ICdBc3luY1JlZ2lzdHJ5RW50cnknIDogJ1JlZ2lzdHJ5RW50cnknO1xuXHRcdFx0XHRjb25zdCBlbnRyeSA9IGAke2VudHJ5S2luZH08JHtpbnN0YW5jZVR5cGV9LCAnJHtmdWxsUGF0aH0nLCAke3BhcmVudFR5cGV9LCAke2NvbnN0cnVjdG9yQXJnc30+YDtcblx0XHRcdFx0bGluZXMucHVzaChgXFx0XFx0JyR7ZnVsbFBhdGh9JzogJHtlbnRyeX07YCk7XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0Zm9yIChjb25zdCB2YWx1ZSBvZiB0aGlzLmJ1aWxkZXJWYWx1ZXMpIHtcblx0XHRcdGlmICh2YWx1ZS5raW5kID09PSAndHlwZW9mJykge1xuXHRcdFx0XHRjb25zdCBpbXBvcnROYW1lID0gdGhpcy5idWlsZGVySW1wb3J0TmFtZSh2YWx1ZSk7XG5cdFx0XHRcdGxpbmVzLnB1c2goYFxcdFxcdCcke3ZhbHVlLmZ1bGxQYXRofSc6IHR5cGVvZiAke2ltcG9ydE5hbWV9O2ApO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRsaW5lcy5wdXNoKCdcXHR9Jyk7XG5cdFx0bGluZXMucHVzaCgnfScpO1xuXHRcdGxpbmVzLnB1c2goJycpO1xuXG5cdFx0Ly8gR2VuZXJhdGUgcGVyLWNvbGxlY3Rpb24gcmVnaXN0cnkgYXVnbWVudGF0aW9ucyBmb3IgT3B0aW9uIEJcblx0XHQvLyAodXNlci1wcm92aWRlZCByZWdpc3RyeSBpbnRlcmZhY2VzKS5cblx0XHRjb25zdCBjb2xsZWN0aW9uR3JvdXBzID0gdGhpcy5ncm91cENvbGxlY3Rpb25SZWdpc3RyeU5vZGVzKCk7XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgbm9kZXMgXSBvZiBjb2xsZWN0aW9uR3JvdXBzKSB7XG5cdFx0XHRjb25zdCBbIHJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSwgc291cmNlRmlsZSBdID0ga2V5LnNwbGl0KCc6OicpO1xuXHRcdFx0Y29uc3QgbW9kdWxlUGF0aCA9IHRoaXMucmVzb2x2ZU1vZHVsZVBhdGgoc291cmNlRmlsZSk7XG5cdFx0XHRsaW5lcy5wdXNoKGBkZWNsYXJlIG1vZHVsZSAnJHttb2R1bGVQYXRofScge2ApO1xuXHRcdFx0bGluZXMucHVzaChgXFx0aW50ZXJmYWNlICR7cmVnaXN0cnlJbnRlcmZhY2VOYW1lfSB7YCk7XG5cdFx0XHRmb3IgKGNvbnN0IG5vZGUgb2Ygbm9kZXMpIHtcblx0XHRcdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmdldEZ1bGxQYXRoKG5vZGUpO1xuXHRcdFx0XHRjb25zdCBpbnN0YW5jZVR5cGUgPSB0aGlzLmdldENvbnN0cnVjdG9yUmVzdWx0VHlwZShub2RlKTtcblx0XHRcdFx0Y29uc3QgY29uc3RydWN0b3JTaWcgPSB0aGlzLmdlbmVyYXRlQ29uc3RydWN0b3JTaWduYXR1cmUobm9kZSk7XG5cdFx0XHRcdGxpbmVzLnB1c2goYFxcdFxcdCcke2Z1bGxQYXRofSc6ICR7Y29uc3RydWN0b3JTaWd9ID0+ICR7aW5zdGFuY2VUeXBlfTtgKTtcblx0XHRcdH1cblx0XHRcdGxpbmVzLnB1c2goJ1xcdH0nKTtcblx0XHRcdGxpbmVzLnB1c2goJ30nKTtcblx0XHRcdGxpbmVzLnB1c2goJycpO1xuXHRcdH1cblxuXHRcdC8vIFJlLWV4cG9ydCBmb3IgYmFja3dhcmQgY29tcGF0aWJpbGl0eSBhbmQgZXhwbGljaXQgdXNhZ2Vcblx0XHRjb25zdCByZWdpc3RyeUltcG9ydHMgPSBbICdUeXBlUmVnaXN0cnknIF07XG5cdFx0aWYgKGZyb21CdWlsZGVyKSB7XG5cdFx0XHRyZWdpc3RyeUltcG9ydHMudW5zaGlmdCgnUmVnaXN0cnlPZicpO1xuXHRcdH1cblx0XHRpZiAobmVlZHNSZWdpc3RyeUVudHJ5KSB7XG5cdFx0XHRyZWdpc3RyeUltcG9ydHMudW5zaGlmdCgnUmVnaXN0cnlFbnRyeScpO1xuXHRcdH1cblx0XHRpZiAobmVlZHNBc3luY1JlZ2lzdHJ5RW50cnkpIHtcblx0XHRcdHJlZ2lzdHJ5SW1wb3J0cy51bnNoaWZ0KCdBc3luY1JlZ2lzdHJ5RW50cnknKTtcblx0XHR9XG5cdFx0bGluZXMucHVzaChgaW1wb3J0IHR5cGUgeyAke3JlZ2lzdHJ5SW1wb3J0cy5qb2luKCcsICcpfSB9IGZyb20gJ21uZW1vbmljYSc7YCk7XG5cdFx0bGluZXMucHVzaCgnZXhwb3J0IHR5cGUgeyBUeXBlUmVnaXN0cnkgfTsnKTtcblxuXHRcdHJldHVybiB7XG5cdFx0XHRjb250ZW50IDogbGluZXMuam9pbignXFxuJyksXG5cdFx0XHR0eXBlcyAgIDogZ2VuZXJhdGVkVHlwZXMsXG5cdFx0fTtcblx0fVxuXG5cdC8qKlxuXHRcdCAqIEdlbmVyYXRlIGNvbnN0cnVjdG9yIHBhcmFtZXRlciBsaXN0IGZvciBhIHR5cGUgbm9kZSAodGhlIFwiKOKApilcIiBwYXJ0KVxuXHRcdCAqL1xuXHRwcml2YXRlIGdlbmVyYXRlQ29uc3RydWN0b3JQYXJhbXMgKG5vZGU6IFR5cGVOb2RlKTogc3RyaW5nIHtcblx0XHRjb25zdCBwYXJhbXMgPSBub2RlLmNvbnN0cnVjdG9yUGFyYW1zO1xuXHRcdGlmICghcGFyYW1zIHx8IHBhcmFtcy5sZW5ndGggPT09IDApIHtcblx0XHRcdHJldHVybiAnKCknO1xuXHRcdH1cblx0XHRjb25zdCBwcm9wczogc3RyaW5nW10gPSBbXTtcblx0XHRmb3IgKGNvbnN0IHBhcmFtIG9mIHBhcmFtcykge1xuXHRcdFx0Y29uc3Qgb3B0aW9uYWwgPSBwYXJhbS5vcHRpb25hbCA/ICc/JyA6ICcnO1xuXHRcdFx0Y29uc3QgcmVzdCA9IHBhcmFtLmtpbmQgPT09ICdyZXN0JyA/ICcuLi4nIDogJyc7XG5cdFx0XHRjb25zdCBhcnJheU1hdGNoID0gcmVzdCA/IC9eQXJyYXk8KC4rKT4kLy5leGVjKHBhcmFtLnR5cGUpIDogdW5kZWZpbmVkO1xuXHRcdFx0Y29uc3QgdHlwZSA9IGFycmF5TWF0Y2ggPyBgJHthcnJheU1hdGNoWyAxIF19W11gIDogcGFyYW0udHlwZTtcblx0XHRcdHByb3BzLnB1c2goYCR7cmVzdH0ke3BhcmFtLm5hbWV9JHtvcHRpb25hbH06ICR7dHlwZX1gKTtcblx0XHR9XG5cdFx0cmV0dXJuIGAoJHtwcm9wcy5qb2luKCcsICcpfSlgO1xuXHR9XG5cblx0cHJpdmF0ZSBnZW5lcmF0ZUNvbnN0cnVjdG9yQXJncyAobm9kZTogVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGNvbnN0IHBhcmFtcyA9IHRoaXMuZ2VuZXJhdGVDb25zdHJ1Y3RvclBhcmFtcyhub2RlKTtcblx0XHQvLyBTdGVwIDYgY2hhbmdlcyByZXN0IHBhcmFtZXRlcnMgaGVyZSB0byBbZGF0YTogVCwgLi4udmFsdWVzOiBudW1iZXJbXV0uXG5cdFx0Y29uc3QgcmVzdWx0ID0gYFske3BhcmFtcy5zbGljZSgxLCAtMSl9XWA7XG5cdFx0cmV0dXJuIHJlc3VsdDtcblx0fVxuXG5cdC8qKlxuXHRcdCAqIEdlbmVyYXRlIGNvbnN0cnVjdG9yIHNpZ25hdHVyZSBmb3IgYSB0eXBlIG5vZGVcblx0XHQgKiBVc2VzIGNvbnN0cnVjdG9yUGFyYW1zIGZvciBUeXBlUmVnaXN0cnkgc2lnbmF0dXJlIChub3QgaW5zdGFuY2UgcHJvcGVydGllcylcblx0XHQgKi9cblx0cHJpdmF0ZSBnZW5lcmF0ZUNvbnN0cnVjdG9yU2lnbmF0dXJlIChub2RlOiBUeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIGBuZXcgJHt0aGlzLmdlbmVyYXRlQ29uc3RydWN0b3JQYXJhbXMobm9kZSl9YDtcblx0fVxuXG5cdC8qKlxuXHRcdCAqIEdldCB0aGUgZnVsbCBkb3R0ZWQgcGF0aCBmb3IgYSB0eXBlIG5vZGVcblx0XHQgKi9cblx0cHJpdmF0ZSBnZXRGdWxsUGF0aCAobm9kZTogVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdGlmICghbm9kZS5wYXJlbnQpIHtcblx0XHRcdHJldHVybiBub2RlLm5hbWU7XG5cdFx0fVxuXHRcdHJldHVybiBgJHt0aGlzLmdldEZ1bGxQYXRoKG5vZGUucGFyZW50KX0uJHtub2RlLm5hbWV9YDtcblx0fVxuXG5cdC8qKlxuXHQgKiBHZXQgdGhlIGluc3RhbmNlIHR5cGUgbmFtZSBmb3IgYSBub2RlXG5cdCAqIFVzZXMgZnVsbCBwYXRoIHdpdGggdW5kZXJzY29yZXM6IFVzYWdlcy5Vc2FnZUVudHJ5IC0+IFVzYWdlc19Vc2FnZUVudHJ5XG5cdCAqIEZvciBPcHRpb24gQiBjdXN0b20gY29sbGVjdGlvbnMsIHByZWZpeGVzIHdpdGggdGhlIHJlZ2lzdHJ5IGludGVyZmFjZSBuYW1lLlxuXHQgKi9cblx0cHJpdmF0ZSBnZXRJbnN0YW5jZVR5cGVOYW1lIChub2RlOiBUeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0Y29uc3QgZnVsbFBhdGggPSB0aGlzLmdldEZ1bGxQYXRoKG5vZGUpO1xuXHRcdGNvbnN0IHByZWZpeCA9IG5vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lID8gYCR7bm9kZS5yZWdpc3RyeUludGVyZmFjZU5hbWV9X2AgOiAnJztcblx0XHRyZXR1cm4gYCR7cHJlZml4fSR7ZnVsbFBhdGgucmVwbGFjZSgvXFwuL2csICdfJyl9YDtcblx0fVxuXG5cdC8qKlxuXHQgKiBSZXNvbHZlIGEgc2ltcGxlIHR5cGUgbmFtZSB0byBpdHMgZnVsbCBwYXRoIG5hbWVcblx0ICogZS5nLiwgXCJEZWZpbml0aW9uRW50cnlcIiAtPiBcIkRlZmluaXRpb25zX0RlZmluaXRpb25FbnRyeVwiXG5cdCAqXG5cdCAqIFdpdGggYSByZWZlcmVuY2VSZXNvbHZlciBpbnN0YWxsZWQgKHRoZSBDTEkgcGF0aCksIHJlc29sdXRpb24gaXNcblx0ICogcGF0aC1hd2FyZSBwZXIgdGhlIGdyYXBoIGlkZW50aXR5IGxhdzogdGhlIHJlc29sdmVyIHJldHVybnMgdGhlIHVuaXF1ZVxuXHQgKiB0eXBlLCAnYW1iaWd1b3VzJywgb3IgdW5kZWZpbmVkIOKAlCB0aGUgbGF0dGVyIHR3byByZWNvcmQgYSBoYXJkLWZhaWxcblx0ICogUmVzb2x1dGlvbkVycm9yIGFuZCBlbWl0IGB1bmtub3duYCBpbnN0ZWFkIG9mIHNpbGVudGx5IHBpY2tpbmcgYVxuXHQgKiBmaXJzdCBtYXRjaC4gV2l0aG91dCBhIHJlc29sdmVyIHRoZSBsZWdhY3kgZmlyc3QtbWF0Y2ggc2NhbiBzdGF5cy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVR5cGVOYW1lIChzaW1wbGVOYW1lOiBzdHJpbmcsIGN1cnJlbnROb2RlOiBUeXBlTm9kZSk6IHN0cmluZyB7XG5cdFx0aWYgKHRoaXMucmVmZXJlbmNlUmVzb2x2ZXIpIHtcblx0XHRcdGNvbnN0IHJlc29sdmVkID0gdGhpcy5yZWZlcmVuY2VSZXNvbHZlcihzaW1wbGVOYW1lLCBjdXJyZW50Tm9kZSk7XG5cdFx0XHRpZiAocmVzb2x2ZWQgJiYgcmVzb2x2ZWQgIT09ICdhbWJpZ3VvdXMnKSB7XG5cdFx0XHRcdGNvbnN0IGluc3RhbmNlTmFtZSA9IHRoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShyZXNvbHZlZCk7XG5cdFx0XHRcdHJldHVybiBpbnN0YW5jZU5hbWU7XG5cdFx0XHR9XG5cdFx0XHRjb25zdCBhbmNob3JMb2NhdGlvbiA9IGAke2N1cnJlbnROb2RlLnNvdXJjZUZpbGV9OiR7Y3VycmVudE5vZGUubGluZX06JHtjdXJyZW50Tm9kZS5jb2x1bW59YDtcblx0XHRcdGNvbnN0IGFtYmlndW91c0dlbmVyYXRpb25NZXNzYWdlID0gYEFtYmlndW91cyByZWZlcmVuY2UgdG8gbW5lbW9uaWNhIHR5cGUgJyR7c2ltcGxlTmFtZX0nIGAgK1xuXHRcdFx0XHRgd2hpbGUgZ2VuZXJhdGluZyAnJHt0aGlzLmdldEZ1bGxQYXRoKGN1cnJlbnROb2RlKX0nYDtcblx0XHRcdGNvbnN0IHVucmVzb2x2ZWRHZW5lcmF0aW9uTWVzc2FnZSA9IGBVbnJlc29sdmVkIHJlZmVyZW5jZSB0byBtbmVtb25pY2EgdHlwZSAnJHtzaW1wbGVOYW1lfScgYCArXG5cdFx0XHRcdGB3aGlsZSBnZW5lcmF0aW5nICcke3RoaXMuZ2V0RnVsbFBhdGgoY3VycmVudE5vZGUpfSdgO1xuXHRcdFx0Y29uc3QgbWVzc2FnZSA9IHJlc29sdmVkID09PSAnYW1iaWd1b3VzJ1xuXHRcdFx0XHQ/IGFtYmlndW91c0dlbmVyYXRpb25NZXNzYWdlXG5cdFx0XHRcdDogdW5yZXNvbHZlZEdlbmVyYXRpb25NZXNzYWdlO1xuXHRcdFx0Y29uc3QgZXJyb3I6IFJlc29sdXRpb25FcnJvciA9IHsgbWVzc2FnZSwgbG9jYXRpb25zIDogWyBhbmNob3JMb2NhdGlvbiBdIH07XG5cdFx0XHR0aGlzLnJlc29sdXRpb25FcnJvcnMucHVzaChlcnJvcik7XG5cdFx0XHRjb25zdCB1bmtub3duUmVzdWx0ID0gJ3Vua25vd24nO1xuXHRcdFx0cmV0dXJuIHVua25vd25SZXN1bHQ7XG5cdFx0fVxuXG5cdFx0Ly8gRmlyc3QgY2hlY2sgaWYgaXQncyB0aGUgY3VycmVudCBub2RlIG9yIGl0cyBjaGlsZHJlblxuXHRcdGlmIChjdXJyZW50Tm9kZS5uYW1lID09PSBzaW1wbGVOYW1lKSB7XG5cdFx0XHRyZXR1cm4gdGhpcy5nZXRJbnN0YW5jZVR5cGVOYW1lKGN1cnJlbnROb2RlKTtcblx0XHR9XG5cdFx0Zm9yIChjb25zdCBjaGlsZCBvZiBjdXJyZW50Tm9kZS5jaGlsZHJlbi52YWx1ZXMoKSkge1xuXHRcdFx0aWYgKGNoaWxkLm5hbWUgPT09IHNpbXBsZU5hbWUpIHtcblx0XHRcdFx0cmV0dXJuIHRoaXMuZ2V0SW5zdGFuY2VUeXBlTmFtZShjaGlsZCk7XG5cdFx0XHR9XG5cdFx0fVxuXHRcdC8vIFNlYXJjaCBhbGwgdHlwZXMgaW4gdGhlIGdyYXBoXG5cdFx0Zm9yIChjb25zdCB0eXBlIG9mIHRoaXMuZ3JhcGguZ2V0QWxsVHlwZXMoKSkge1xuXHRcdFx0aWYgKHR5cGUubmFtZSA9PT0gc2ltcGxlTmFtZSkge1xuXHRcdFx0XHRyZXR1cm4gdGhpcy5nZXRJbnN0YW5jZVR5cGVOYW1lKHR5cGUpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gc2ltcGxlTmFtZTtcblx0fVxuXG5cdC8qKlxuXHQgKiBIYXJkLWZhaWwgZ3JhcGggcmVmZXJlbmNlIGVycm9ycyByZWNvcmRlZCB3aGlsZSBnZW5lcmF0aW5nIChzZWVcblx0ICogcmVmZXJlbmNlUmVzb2x2ZXIpLiBUaGUgQ0xJIHByaW50cyBldmVyeSBsb2NhdGlvbiBhbmQgd3JpdGVzIG5vIG91dHB1dC5cblx0ICovXG5cdGdldFJlc29sdXRpb25FcnJvcnMgKCk6IFJlc29sdXRpb25FcnJvcltdIHtcblx0XHRjb25zdCByZXN1bHQgPSBbIC4uLnRoaXMucmVzb2x1dGlvbkVycm9ycyBdO1xuXHRcdHJldHVybiByZXN1bHQ7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBzaW1wbGUgdHlwZSBuYW1lcyB0byBmdWxsIHBhdGggbmFtZXMgd2l0aGluIGEgdHlwZSBzdHJpbmdcblx0ICogSGFuZGxlcyBjb21wbGV4IHR5cGVzIGxpa2UgQXJyYXk8VXNhZ2VFbnRyeT4sIE1hcDxzdHJpbmcsIFR5cGVFbnRyeT4sIGV0Yy5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZVR5cGVJblN0cmluZyAodHlwZVN0cjogc3RyaW5nLCBjdXJyZW50Tm9kZTogVHlwZU5vZGUpOiBzdHJpbmcge1xuXHRcdC8vIEdldCBhbGwgdHlwZSBuYW1lcyBmcm9tIHRoZSBncmFwaFxuXHRcdGNvbnN0IGFsbFR5cGVzID0gdGhpcy5ncmFwaC5nZXRBbGxUeXBlcygpO1xuXHRcdGNvbnN0IHR5cGVOYW1lcyA9IG5ldyBTZXQ8c3RyaW5nPigpO1xuXHRcdGZvciAoY29uc3QgdHlwZSBvZiBhbGxUeXBlcykge1xuXHRcdFx0dHlwZU5hbWVzLmFkZCh0eXBlLm5hbWUpO1xuXHRcdH1cblxuXHRcdC8vIFNvcnQgYnkgbGVuZ3RoIChsb25nZXN0IGZpcnN0KSB0byBhdm9pZCBwYXJ0aWFsIHJlcGxhY2VtZW50c1xuXHRcdGNvbnN0IHNvcnRlZE5hbWVzID0gQXJyYXkuZnJvbSh0eXBlTmFtZXMpLnNvcnQoKGEsIGIpID0+IGIubGVuZ3RoIC0gYS5sZW5ndGgpO1xuXG5cdFx0Ly8gUmVwbGFjZSBlYWNoIHNpbXBsZSB0eXBlIG5hbWUgd2l0aCBpdHMgZnVsbCBwYXRoIHZlcnNpb25cblx0XHRsZXQgcmVzdWx0ID0gdHlwZVN0cjtcblx0XHRmb3IgKGNvbnN0IG5hbWUgb2Ygc29ydGVkTmFtZXMpIHtcblx0XHRcdC8vIFNraXAgbmFtZXMgdGhhdCBkbyBub3Qgb2NjdXIg4oCUIHdpdGggYSByZWZlcmVuY2VSZXNvbHZlciBpbnN0YWxsZWQsXG5cdFx0XHQvLyByZXNvbHZpbmcgYWJzZW50IG5hbWVzIHdvdWxkIHJlY29yZCBzcHVyaW91cyBlcnJvcnNcblx0XHRcdGNvbnN0IG9jY3VycyA9IG5ldyBSZWdFeHAoYFxcXFxiJHtuYW1lfVxcXFxiYCkudGVzdChyZXN1bHQpO1xuXHRcdFx0aWYgKCFvY2N1cnMpIHtcblx0XHRcdFx0Y29udGludWU7XG5cdFx0XHR9XG5cdFx0XHQvLyBVc2Ugd29yZCBib3VuZGFyeSBtYXRjaGluZyB0byBhdm9pZCByZXBsYWNpbmcgcGFydGlhbCBuYW1lc1xuXHRcdFx0Y29uc3QgcmVnZXggPSBuZXcgUmVnRXhwKGBcXFxcYiR7bmFtZX1cXFxcYmAsICdnJyk7XG5cdFx0XHRjb25zdCBmdWxsVHlwZU5hbWUgPSB0aGlzLnJlc29sdmVUeXBlTmFtZShuYW1lLCBjdXJyZW50Tm9kZSk7XG5cdFx0XHRpZiAoZnVsbFR5cGVOYW1lICE9PSBuYW1lKSB7XG5cdFx0XHRcdHJlc3VsdCA9IHJlc3VsdC5yZXBsYWNlKHJlZ2V4LCBmdWxsVHlwZU5hbWUpO1xuXHRcdFx0fVxuXHRcdH1cblx0XHRyZXR1cm4gcmVzdWx0O1xuXHR9XG5cblx0LyoqXG5cdCAqIEdyb3VwIGNvbGxlY3Rpb24gdHlwZSBub2RlcyBieSB0aGVpciByZWdpc3RyeSBpbnRlcmZhY2UgbmFtZSBhbmQgdGhlXG5cdCAqIGNvbGxlY3Rpb24ncyBob21lIGZpbGUgKHRoZSBtb2R1bGUgZGVjbGFyaW5nIHRoZSBpbnRlcmZhY2Ug4oCUIHRoZVxuXHQgKiBhdWdtZW50YXRpb24gdGFyZ2V0KSwgTk9UIGVhY2ggdHlwZSdzIG93biBkZWZpbmUgZmlsZTogbXVsdGktZmlsZVxuXHQgKiBjb2xsZWN0aW9ucyBkZWZpbmUgdHlwZXMgYWNyb3NzIG1hbnkgbW9kdWxlcy5cblx0ICogUmV0dXJucyBhIG1hcCBrZXllZCBieSBgJHtyZWdpc3RyeUludGVyZmFjZU5hbWV9Ojoke3NvdXJjZUZpbGV9YC5cblx0ICovXG5cdHByaXZhdGUgZ3JvdXBDb2xsZWN0aW9uUmVnaXN0cnlOb2RlcyAoKTogTWFwPHN0cmluZywgVHlwZU5vZGVbXT4ge1xuXHRcdGNvbnN0IGdyb3VwcyA9IG5ldyBNYXA8c3RyaW5nLCBUeXBlTm9kZVtdPigpO1xuXHRcdGZvciAoY29uc3Qgcm9vdCBvZiB0aGlzLmdyYXBoLnJvb3RzLnZhbHVlcygpKSB7XG5cdFx0XHRmb3IgKGNvbnN0IG5vZGUgb2YgdGhpcy5ncmFwaC5kZnMocm9vdCkpIHtcblx0XHRcdFx0aWYgKG5vZGUubWV0YWRhdGFPbmx5IHx8ICFub2RlLnJlZ2lzdHJ5SW50ZXJmYWNlTmFtZSkge1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cdFx0XHRcdGNvbnN0IGhvbWVGaWxlID0gbm9kZS5jb2xsZWN0aW9uU291cmNlRmlsZSA/PyBub2RlLnNvdXJjZUZpbGU7XG5cdFx0XHRcdGNvbnN0IGtleSA9IGAke25vZGUucmVnaXN0cnlJbnRlcmZhY2VOYW1lfTo6JHtob21lRmlsZX1gO1xuXHRcdFx0XHRjb25zdCBleGlzdGluZyA9IGdyb3Vwcy5nZXQoa2V5KTtcblx0XHRcdFx0aWYgKGV4aXN0aW5nKSB7XG5cdFx0XHRcdFx0ZXhpc3RpbmcucHVzaChub2RlKTtcblx0XHRcdFx0fSBlbHNlIHtcblx0XHRcdFx0XHRncm91cHMuc2V0KGtleSwgWyBub2RlIF0pO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHRcdHJldHVybiBncm91cHM7XG5cdH1cblxuXHQvKipcblx0ICogUmVzb2x2ZSBhIHNvdXJjZSBmaWxlIHBhdGggdG8gYSBtb2R1bGUgc3BlY2lmaWVyIHJlbGF0aXZlIHRvIHRoZSBvdXRwdXQgZGlyZWN0b3J5LFxuXHQgKiBzdWl0YWJsZSBmb3IgdXNlIGluIGEgYGRlY2xhcmUgbW9kdWxlICcuLi4nYCBibG9jay5cblx0ICovXG5cdHByaXZhdGUgcmVzb2x2ZU1vZHVsZVBhdGggKHNvdXJjZUZpbGU6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0Y29uc3Qgb3V0cHV0QWJzb2x1dGUgPSBwYXRoLnJlc29sdmUodGhpcy5vdXRwdXREaXIpO1xuXHRcdGNvbnN0IHNvdXJjZUFic29sdXRlID0gcGF0aC5yZXNvbHZlKHNvdXJjZUZpbGUpO1xuXHRcdGxldCByZWxhdGl2ZSA9IHBhdGgucmVsYXRpdmUob3V0cHV0QWJzb2x1dGUsIHNvdXJjZUFic29sdXRlKTtcblx0XHQvLyBSZW1vdmUgLnRzIGV4dGVuc2lvbjsga2VlcCAudHN4IGlmIHByZXNlbnRcblx0XHRpZiAocmVsYXRpdmUuZW5kc1dpdGgoJy50cycpICYmICFyZWxhdGl2ZS5lbmRzV2l0aCgnLnRzeCcpKSB7XG5cdFx0XHRyZWxhdGl2ZSA9IHJlbGF0aXZlLnNsaWNlKDAsIC0zKTtcblx0XHR9XG5cdFx0Ly8gQ29udmVydCBXaW5kb3dzIHNlcGFyYXRvcnMgdG8gUE9TSVhcblx0XHRjb25zdCBwb3NpeFJlbGF0aXZlID0gcmVsYXRpdmUucmVwbGFjZSgvXFxcXC9nLCAnLycpO1xuXHRcdHJldHVybiBwb3NpeFJlbGF0aXZlO1xuXHR9XG59XG4iXX0=