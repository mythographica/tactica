import * as ts from 'typescript';
/**
 * Initialize the plugin
 */
declare function init(modules: {
    typescript: typeof ts;
}): ts.server.PluginModule;
export = init;
