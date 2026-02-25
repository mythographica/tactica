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
exports.TypesWriter = void 0;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
/**
 * File writer for generated types
 */
class TypesWriter {
    constructor(outputDir = '.mnemonica') {
        this.outputDir = outputDir;
    }
    /**
     * Write generated types to file
     */
    write(generated) {
        // Ensure output directory exists
        this.ensureDirectory();
        const outputPath = path.join(this.outputDir, 'types.d.ts');
        // Write the file
        fs.writeFileSync(outputPath, generated.content, 'utf-8');
        // Update .gitignore if needed
        this.updateGitignore();
        return outputPath;
    }
    /**
     * Write types.ts file with complete interfaces
     */
    writeTypesFile(generated) {
        this.ensureDirectory();
        const outputPath = path.join(this.outputDir, 'types.ts');
        fs.writeFileSync(outputPath, generated.content, 'utf-8');
        return outputPath;
    }
    /**
     * Write types with custom filename
     */
    writeTo(filename, content) {
        this.ensureDirectory();
        const outputPath = path.join(this.outputDir, filename);
        fs.writeFileSync(outputPath, content, 'utf-8');
        return outputPath;
    }
    /**
     * Ensure output directory exists
     */
    ensureDirectory() {
        if (!fs.existsSync(this.outputDir)) {
            fs.mkdirSync(this.outputDir, { recursive: true });
        }
    }
    /**
     * Update .gitignore to exclude .mnemonica folder
     */
    updateGitignore() {
        const gitignorePath = path.join(process.cwd(), '.gitignore');
        if (!fs.existsSync(gitignorePath)) {
            // Create .gitignore
            fs.writeFileSync(gitignorePath, `${this.outputDir}/\n`, 'utf-8');
            return;
        }
        const content = fs.readFileSync(gitignorePath, 'utf-8');
        const lines = content.split('\n');
        // Check if already ignored
        const isIgnored = lines.some(line => line.trim() === this.outputDir ||
            line.trim() === `${this.outputDir}/`);
        if (!isIgnored) {
            // Add to .gitignore
            const newContent = content.endsWith('\n')
                ? `${content}${this.outputDir}/\n`
                : `${content}\n${this.outputDir}/\n`;
            fs.writeFileSync(gitignorePath, newContent, 'utf-8');
        }
    }
    /**
     * Clean the output directory
     */
    clean() {
        if (fs.existsSync(this.outputDir)) {
            const files = fs.readdirSync(this.outputDir);
            for (const file of files) {
                fs.unlinkSync(path.join(this.outputDir, file));
            }
        }
    }
    /**
     * Get the output directory path
     */
    getOutputDir() {
        return this.outputDir;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=writer.js.map