module.exports = {
    entry: "./src/index.ts",
    output: {
        filename: "./dist/bundle.js"
    },

    devtool: "source-map",

    module: {
        loaders: [
            {
                test: /\.ts$/,
                loader: "ts-loader"
            }
        ]
    }
};