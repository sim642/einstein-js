var path = require("path");
var nodeExternals = require("webpack-node-externals");
var isCoverage = process.env.NYC_CWD !== undefined;

module.exports = {
    output: {
        // use absolute paths in sourcemaps (important for debugging via IDE)
        devtoolModuleFilenameTemplate: "[absolute-resource-path]",
        devtoolFallbackModuleFilenameTemplate: "[absolute-resource-path]?[hash]"
    },

    target: "node", // webpack should compile node compatible code
    externals: [nodeExternals({
        whitelist: ["z3em/z3em.wasm"] // must be whitelisted to go through loaders since node natively can't import wasm
    })], // in order to ignore all modules in node_modules folder
    devtool: "inline-cheap-module-source-map",

    resolve: {
        extensions: [".webpack.js", ".web.js", ".ts", ".tsx", ".js"]
    },

    module: {
        // http://zinserjan.github.io/mocha-webpack/docs/guides/code-coverage.html
        rules: [].concat(
            isCoverage ? {
                test: /\.(js|ts)x?$/,
                include: path.resolve(__dirname, "src"), // instrument only testing sources with Istanbul, after ts-loader runs
                loader: "istanbul-instrumenter-loader",
                enforce: "post"
            }: [],
            {
                test: /\.tsx?$/,
                use: "ts-loader"
            },
            {
                test: /\.wasm$/,
                use: "file-loader"
            }
        )
    }
};