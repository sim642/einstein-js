module.exports = {
    entry: "./src/index.ts",
    output: {
        filename: "./dist/bundle.js"
    },

    devtool: "source-map",

    resolve: {
        extensions: ['.webpack.js', '.web.js', '.ts', '.tsx', '.js']
    },

    module: {
        loaders: [
            {
                test: /\.tsx?$/,
                loader: "ts-loader"
            }
        ]
    }
};