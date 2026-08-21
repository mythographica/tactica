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
 * Writes generated types to file system
 */
class TypesWriter {
    constructor(outputDir = '.tactica') {
        this.outputDir = outputDir;
    }
    /**
     * Legacy write method - delegates to writeTypesFile
     */
    write(generated) {
        return this.writeTypesFile(generated);
    }
    /**
     * Write types.ts file (exportable type aliases - default mode)
     */
    writeTypesFile(generated) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'types.ts');
        fs.writeFileSync(filePath, generated.content, 'utf-8');
        return filePath;
    }
    /**
     * Write global augmentation file (index.d.ts - module augmentation mode)
     */
    writeGlobalAugmentation(generated) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'index.d.ts');
        fs.writeFileSync(filePath, generated.content, 'utf-8');
        return filePath;
    }
    /**
     * Write to a custom filename
     */
    writeTo(filename, content) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, filename);
        fs.writeFileSync(filePath, content, 'utf-8');
        return filePath;
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
     * Get output directory
     */
    getOutputDir() {
        return this.outputDir;
    }
    /**
     * Write definitions.json file
     */
    writeDefinitionsFile(definitions) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'definitions.json');
        // Convert Map to plain object
        const definitionsObj = {};
        for (const [key, value] of definitions) {
            definitionsObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            definitions: definitionsObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write usages.json file
     */
    writeUsagesFile(usages) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'usages.json');
        // Convert Map to plain object
        const usagesObj = {};
        for (const [key, value] of usages) {
            usagesObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            usages: usagesObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write eds.json file
     */
    writeEDSFile(eds) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'eds.json');
        // Convert Map to plain object
        const edsObj = {};
        for (const [key, value] of eds) {
            edsObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            eds: edsObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write flow.json file
     */
    writeFlowFile(flow) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'flow.json');
        // Convert Map to plain object
        const flowObj = {};
        for (const [key, value] of flow) {
            flowObj[key] = value;
        }
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            flow: flowObj,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
    /**
     * Write hierarchy.json file
     */
    writeHierarchyFile(roots) {
        this.ensureDirectory();
        const filePath = path.join(this.outputDir, 'hierarchy.json');
        const json = {
            version: '1.0',
            generatedAt: new Date().toISOString(),
            roots,
        };
        fs.writeFileSync(filePath, JSON.stringify(json, null, 2), 'utf-8');
        return filePath;
    }
}
exports.TypesWriter = TypesWriter;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid3JpdGVyLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXMiOlsiLi4vc3JjL3dyaXRlci50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUViLHVDQUF5QjtBQUN6QiwyQ0FBNkI7QUFLN0I7O0dBRUc7QUFDSCxNQUFhLFdBQVc7SUFHdkIsWUFBYSxTQUFTLEdBQUcsVUFBVTtRQUNsQyxJQUFJLENBQUMsU0FBUyxHQUFHLFNBQVMsQ0FBQztJQUM1QixDQUFDO0lBRUQ7O09BRUc7SUFDSCxLQUFLLENBQUUsU0FBeUI7UUFDL0IsT0FBTyxJQUFJLENBQUMsY0FBYyxDQUFDLFNBQVMsQ0FBQyxDQUFDO0lBQ3ZDLENBQUM7SUFFRDs7T0FFRztJQUNILGNBQWMsQ0FBRSxTQUF5QjtRQUN4QyxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7UUFDdkIsTUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLFVBQVUsQ0FBQyxDQUFDO1FBQ3ZELEVBQUUsQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLFNBQVMsQ0FBQyxPQUFPLEVBQUUsT0FBTyxDQUFDLENBQUM7UUFDdkQsT0FBTyxRQUFRLENBQUM7SUFDakIsQ0FBQztJQUVEOztPQUVHO0lBQ0gsdUJBQXVCLENBQUUsU0FBeUI7UUFDakQsSUFBSSxDQUFDLGVBQWUsRUFBRSxDQUFDO1FBQ3ZCLE1BQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxZQUFZLENBQUMsQ0FBQztRQUN6RCxFQUFFLENBQUMsYUFBYSxDQUFDLFFBQVEsRUFBRSxTQUFTLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ3ZELE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILE9BQU8sQ0FBRSxRQUFnQixFQUFFLE9BQWU7UUFDekMs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eEIsQ0FBQztRQUVELE1BQU0sSUFBSSxHQUFhO1lBQ3RCLE9BQU8sRUFBTyxLQUFLO1lBQ25CLFdBQVcsRUFBRyxJQUFJLElBQUksRUFBRSxDQUFDLFdBQVcsRUFBRTtZQUN0QyxJQUFJLEVBQVUsT0FBTztTQUNyQixDQUFDO1FBRUYsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7SUFFRDs7T0FFRztJQUNILGtCQUFrQixDQUFFLEtBQXNCO1FBQ3pDLElBQUksQ0FBQyxlQUFlLEVBQUUsQ0FBQztRQUN2QixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsZ0JBQWdCLENBQUMsQ0FBQztRQUU3RCxNQUFNLElBQUksR0FBa0I7WUFDM0IsT0FBTyxFQUFPLEtBQUs7WUFDbkIsV0FBVyxFQUFHLElBQUksSUFBSSxFQUFFLENBQUMsV0FBVyxFQUFFO1lBQ3RDLEtBQUs7U0FDTCxDQUFDO1FBRUYsRUFBRSxDQUFDLGFBQWEsQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO1FBQ25FLE9BQU8sUUFBUSxDQUFDO0lBQ2pCLENBQUM7Q0FDRDtBQXBMRCxrQ0FvTEMiLCJzb3VyY2VzQ29udGVudCI6WyIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIGZzIGZyb20gJ2ZzJztcbmltcG9ydCAqIGFzIHBhdGggZnJvbSAncGF0aCc7XG5pbXBvcnQge1xuXHRHZW5lcmF0ZWRUeXBlcywgRGVmaW5pdGlvbkluZm8sIFVzYWdlSW5mbywgRURTSW5mbywgRmxvd0luZm8sIEZsb3dKc29uLCBIaWVyYXJjaHlOb2RlLCBIaWVyYXJjaHlKc29uIFxufSBmcm9tICcuL3R5cGVzJztcblxuLyoqXG4gKiBXcml0ZXMgZ2VuZXJhdGVkIHR5cGVzIHRvIGZpbGUgc3lzdGVtXG4gKi9cbmV4cG9ydCBjbGFzcyBUeXBlc1dyaXRlciB7XG5cdHByaXZhdGUgb3V0cHV0RGlyOiBzdHJpbmc7XG5cblx0Y29uc3RydWN0b3IgKG91dHB1dERpciA9ICcudGFjdGljYScpIHtcblx0XHR0aGlzLm91dHB1dERpciA9IG91dHB1dERpcjtcblx0fVxuXG5cdC8qKlxuXHQgKiBMZWdhY3kgd3JpdGUgbWV0aG9kIC0gZGVsZWdhdGVzIHRvIHdyaXRlVHlwZXNGaWxlXG5cdCAqL1xuXHR3cml0ZSAoZ2VuZXJhdGVkOiBHZW5lcmF0ZWRUeXBlcyk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMud3JpdGVUeXBlc0ZpbGUoZ2VuZXJhdGVkKTtcblx0fVxuXG5cdC8qKlxuXHQgKiBXcml0ZSB0eXBlcy50cyBmaWxlIChleHBvcnRhYmxlIHR5cGUgYWxpYXNlcyAtIGRlZmF1bHQgbW9kZSlcblx0ICovXG5cdHdyaXRlVHlwZXNGaWxlIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAndHlwZXMudHMnKTtcblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBnZW5lcmF0ZWQuY29udGVudCwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGdsb2JhbCBhdWdtZW50YXRpb24gZmlsZSAoaW5kZXguZC50cyAtIG1vZHVsZSBhdWdtZW50YXRpb24gbW9kZSlcblx0ICovXG5cdHdyaXRlR2xvYmFsQXVnbWVudGF0aW9uIChnZW5lcmF0ZWQ6IEdlbmVyYXRlZFR5cGVzKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaW5kZXguZC50cycpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGdlbmVyYXRlZC5jb250ZW50LCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdG8gYSBjdXN0b20gZmlsZW5hbWVcblx0ICovXG5cdHdyaXRlVG8gKGZpbGVuYW1lOiBzdHJpbmcsIGNvbnRlbnQ6IHN0cmluZyk6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgZmlsZW5hbWUpO1xuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIGNvbnRlbnQsICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxuXG5cdC8qKlxuXHQgKiBFbnN1cmUgb3V0cHV0IGRpcmVjdG9yeSBleGlzdHNcblx0ICovXG5cdHByaXZhdGUgZW5zdXJlRGlyZWN0b3J5ICgpOiB2b2lkIHtcblx0XHRpZiAoIWZzLmV4aXN0c1N5bmModGhpcy5vdXRwdXREaXIpKSB7XG5cdFx0XHRmcy5ta2RpclN5bmModGhpcy5vdXRwdXREaXIsIHsgcmVjdXJzaXZlIDogdHJ1ZSB9KTtcblx0XHR9XG5cdH1cblxuXHQvKipcblx0ICogQ2xlYW4gdGhlIG91dHB1dCBkaXJlY3Rvcnlcblx0ICovXG5cdGNsZWFuICgpOiB2b2lkIHtcblx0XHRpZiAoZnMuZXhpc3RzU3luYyh0aGlzLm91dHB1dERpcikpIHtcblx0XHRcdGNvbnN0IGZpbGVzID0gZnMucmVhZGRpclN5bmModGhpcy5vdXRwdXREaXIpO1xuXHRcdFx0Zm9yIChjb25zdCBmaWxlIG9mIGZpbGVzKSB7XG5cdFx0XHRcdGZzLnVubGlua1N5bmMocGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCBmaWxlKSk7XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0LyoqXG5cdCAqIEdldCBvdXRwdXQgZGlyZWN0b3J5XG5cdCAqL1xuXHRnZXRPdXRwdXREaXIgKCk6IHN0cmluZyB7XG5cdFx0cmV0dXJuIHRoaXMub3V0cHV0RGlyO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGRlZmluaXRpb25zLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVEZWZpbml0aW9uc0ZpbGUgKGRlZmluaXRpb25zOiBNYXA8c3RyaW5nLCBEZWZpbml0aW9uSW5mbz4pOiBzdHJpbmcge1xuXHRcdHRoaXMuZW5zdXJlRGlyZWN0b3J5KCk7XG5cdFx0Y29uc3QgZmlsZVBhdGggPSBwYXRoLmpvaW4odGhpcy5vdXRwdXREaXIsICdkZWZpbml0aW9ucy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCBkZWZpbml0aW9uc09iajogUmVjb3JkPHN0cmluZywgRGVmaW5pdGlvbkluZm8+ID0ge307XG5cdFx0Zm9yIChjb25zdCBbIGtleSwgdmFsdWUgXSBvZiBkZWZpbml0aW9ucykge1xuXHRcdFx0ZGVmaW5pdGlvbnNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGRlZmluaXRpb25zIDogZGVmaW5pdGlvbnNPYmosXG5cdFx0fTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgdXNhZ2VzLmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVVc2FnZXNGaWxlICh1c2FnZXM6IE1hcDxzdHJpbmcsIFVzYWdlSW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ3VzYWdlcy5qc29uJyk7XG5cblx0XHQvLyBDb252ZXJ0IE1hcCB0byBwbGFpbiBvYmplY3Rcblx0XHRjb25zdCB1c2FnZXNPYmo6IFJlY29yZDxzdHJpbmcsIFVzYWdlSW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgdXNhZ2VzKSB7XG5cdFx0XHR1c2FnZXNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdHVzYWdlcyAgICAgIDogdXNhZ2VzT2JqLFxuXHRcdH07XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGVkcy5qc29uIGZpbGVcblx0ICovXG5cdHdyaXRlRURTRmlsZSAoZWRzOiBNYXA8c3RyaW5nLCBFRFNJbmZvW10+KTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnZWRzLmpzb24nKTtcblxuXHRcdC8vIENvbnZlcnQgTWFwIHRvIHBsYWluIG9iamVjdFxuXHRcdGNvbnN0IGVkc09iajogUmVjb3JkPHN0cmluZywgRURTSW5mb1tdPiA9IHt9O1xuXHRcdGZvciAoY29uc3QgWyBrZXksIHZhbHVlIF0gb2YgZWRzKSB7XG5cdFx0XHRlZHNPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbiA9IHtcblx0XHRcdHZlcnNpb24gICAgIDogJzEuMCcsXG5cdFx0XHRnZW5lcmF0ZWRBdCA6IG5ldyBEYXRlKCkudG9JU09TdHJpbmcoKSxcblx0XHRcdGVkcyAgICAgICAgIDogZWRzT2JqLFxuXHRcdH07XG5cblx0XHRmcy53cml0ZUZpbGVTeW5jKGZpbGVQYXRoLCBKU09OLnN0cmluZ2lmeShqc29uLCBudWxsLCAyKSwgJ3V0Zi04Jyk7XG5cdFx0cmV0dXJuIGZpbGVQYXRoO1xuXHR9XG5cblx0LyoqXG5cdCAqIFdyaXRlIGZsb3cuanNvbiBmaWxlXG5cdCAqL1xuXHR3cml0ZUZsb3dGaWxlIChmbG93OiBNYXA8c3RyaW5nLCBGbG93SW5mb1tdPik6IHN0cmluZyB7XG5cdFx0dGhpcy5lbnN1cmVEaXJlY3RvcnkoKTtcblx0XHRjb25zdCBmaWxlUGF0aCA9IHBhdGguam9pbih0aGlzLm91dHB1dERpciwgJ2Zsb3cuanNvbicpO1xuXG5cdFx0Ly8gQ29udmVydCBNYXAgdG8gcGxhaW4gb2JqZWN0XG5cdFx0Y29uc3QgZmxvd09iajogUmVjb3JkPHN0cmluZywgRmxvd0luZm9bXT4gPSB7fTtcblx0XHRmb3IgKGNvbnN0IFsga2V5LCB2YWx1ZSBdIG9mIGZsb3cpIHtcblx0XHRcdGZsb3dPYmpbIGtleSBdID0gdmFsdWU7XG5cdFx0fVxuXG5cdFx0Y29uc3QganNvbjogRmxvd0pzb24gPSB7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRmbG93ICAgICAgICA6IGZsb3dPYmosXG5cdFx0fTtcblxuXHRcdGZzLndyaXRlRmlsZVN5bmMoZmlsZVBhdGgsIEpTT04uc3RyaW5naWZ5KGpzb24sIG51bGwsIDIpLCAndXRmLTgnKTtcblx0XHRyZXR1cm4gZmlsZVBhdGg7XG5cdH1cblxuXHQvKipcblx0ICogV3JpdGUgaGllcmFyY2h5Lmpzb24gZmlsZVxuXHQgKi9cblx0d3JpdGVIaWVyYXJjaHlGaWxlIChyb290czogSGllcmFyY2h5Tm9kZVtdKTogc3RyaW5nIHtcblx0XHR0aGlzLmVuc3VyZURpcmVjdG9yeSgpO1xuXHRcdGNvbnN0IGZpbGVQYXRoID0gcGF0aC5qb2luKHRoaXMub3V0cHV0RGlyLCAnaGllcmFyY2h5Lmpzb24nKTtcblxuXHRcdGNvbnN0IGpzb246IEhpZXJhcmNoeUpzb24gPSB7XG5cdFx0XHR2ZXJzaW9uICAgICA6ICcxLjAnLFxuXHRcdFx0Z2VuZXJhdGVkQXQgOiBuZXcgRGF0ZSgpLnRvSVNPU3RyaW5nKCksXG5cdFx0XHRyb290cyxcblx0XHR9O1xuXG5cdFx0ZnMud3JpdGVGaWxlU3luYyhmaWxlUGF0aCwgSlNPTi5zdHJpbmdpZnkoanNvbiwgbnVsbCwgMiksICd1dGYtOCcpO1xuXHRcdHJldHVybiBmaWxlUGF0aDtcblx0fVxufVxuIl19