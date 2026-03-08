'use strict';

import * as fs from 'fs';
import * as path from 'path';
import { TypeNode } from './types';
import { TypeGraphImpl } from './graph';

/**
 * Analyzer for Topologica directory-based type definitions
 * Scans directory structures to create type hierarchies like:
 * ai-types/Sentience/Consciousness/Empathy/Gratitude/
 */
export class TopologicaAnalyzer {
	private errors: string[] = [];
	private graph = new TypeGraphImpl();

	/**
	 * Analyze a directory structure for topologica type definitions
	 */
	analyzeDirectory(directoryPath: string): { types: Map<string, TypeNode>, errors: string[] } {
		this.errors = [];
		
		if (!fs.existsSync(directoryPath)) {
			this.errors.push(`Directory does not exist: ${directoryPath}`);
			return { types: this.graph.allTypes, errors: this.errors };
		}

		if (!fs.statSync(directoryPath).isDirectory()) {
			this.errors.push(`Path is not a directory: ${directoryPath}`);
			return { types: this.graph.allTypes, errors: this.errors };
		}

		this.scanDirectory(directoryPath, undefined, directoryPath);
		
		return {
			types: this.graph.allTypes,
			errors: this.errors,
		};
	}

	/**
	 * Recursively scan directory structure to build type hierarchy
	 */
	private scanDirectory(currentPath: string, parentNode: TypeNode | undefined, rootPath: string): void {
		try {
			const entries = fs.readdirSync(currentPath, { withFileTypes: true });
			
			for (const entry of entries) {
				if (entry.isDirectory()) {
					// Create type node for this directory
					const typeName = entry.name;
					const fullPath = parentNode ? `${parentNode.fullPath}.${typeName}` : typeName;
					
					// Create the type node
					const typeNode: TypeNode = {
						name: typeName,
						fullPath: fullPath,
						properties: new Map(),
						parent: parentNode,
						children: new Map(),
						sourceFile: currentPath,
						line: 0,
						column: 0,
						constructorName: typeName
					};
					
					// Add to graph
					if (parentNode) {
						this.graph.addChild(parentNode, typeNode);
					} else {
						// Add as root type
						this.graph.addRoot(typeNode);
					}
					
					// Scan children of this directory
					this.scanDirectory(path.join(currentPath, entry.name), typeNode, rootPath);
				}
			}
		} catch (error) {
			this.errors.push(`Error scanning directory ${currentPath}: ${(error as Error).message}`);
		}
	}

	/**
	 * Get the type graph
	 */
	getGraph(): TypeGraphImpl {
		return this.graph;
	}

	/**
	 * Get collected errors
	 */
	getErrors(): string[] {
		return this.errors;
	}
}