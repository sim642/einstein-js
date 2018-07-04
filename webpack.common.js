var path = require("path");
var webpack = require("webpack");

var ExtractTextPlugin = require("extract-text-webpack-plugin");
var HtmlWebpackPlugin = require("html-webpack-plugin");
var CopyWebpackPlugin = require("copy-webpack-plugin");
var CleanWebpackPlugin = require("clean-webpack-plugin");

module.exports = {
    entry: {
        app: "./src/index.tsx"
    },

    output: {
        filename: "[name].js",
        path: path.resolve(__dirname, "dist")
    },

    devtool: "source-map",

    resolve: {
        extensions: [".webpack.js", ".web.js", ".ts", ".tsx", ".js"],
        alias: {
            "package.json$": path.resolve(__dirname, "package.json")
        }
    },

    node: {
        fs: "empty"
    },

    module: {
        rules: [
            {
                test: /\.tsx?$/,
                use: "ts-loader"
            },
            {
                test: /\.less$/,
                use: ExtractTextPlugin.extract({
                    fallback: {
                        loader: "style-loader",
                        options: {
                            sourceMap: true
                        }
                    },
                    use: [
                        {
                            loader: "css-loader",
                            options: {
                                sourceMap: true,
                                importLoaders: 1 // https://github.com/webpack-contrib/css-loader#importloaders
                            }
                        },
                        {
                            loader: "postcss-loader",
                            options: {
                                sourceMap: true
                            }
                        },
                        {
                            loader: "less-loader",
                            options: {
                                sourceMap: true
                            }
                        }
                    ]
                })
            },
            {
                test: /\.(png|svg|jpg|gif)$/,
                use: {
                    loader: "file-loader",
                    query: {
                        name: "[name].[ext]",
                        useRelativePath: true
                    }
                }
            },
            {
                test: /manifest\.json$/,
                use: {
                    loader: "file-loader",
                    query: {
                        name: "[name].[ext]"
                    }
                }
            },
            {
                test: /\.wasm$/,
                use: {
                    loader: "file-loader",
                    query: {
                        // always include hash for WASM cache invalidation in IndexedDB
                        name: "[name].[hash].[ext]"
                    }
                }
            }
        ]
    },

    plugins: [
        // https://webpack.js.org/guides/output-management/#cleaning-up-the-dist-folder
        new CleanWebpackPlugin(['dist']),

        // https://webpack.js.org/guides/code-splitting-libraries/#manifest-file
        new webpack.optimize.CommonsChunkPlugin({
            name: "vendor",
            minChunks: function (module) {
                // this assumes your vendor imports exist in the node_modules directory
                return module.context && module.context.indexOf("node_modules") !== -1;
            }
        }),
        //CommonChunksPlugin will now extract all the common modules from vendor and main bundles
        new webpack.optimize.CommonsChunkPlugin({
            name: "manifest" //But since there are no more common modules between them we end up with just the runtime code included in the manifest file
        }),

        new HtmlWebpackPlugin({
            title: "einstein-js",
            template: "./src/index.ejs",
            favicon: "./src/einstein.ico"
        }),

        new webpack.NamedChunksPlugin(),

        new CopyWebpackPlugin([
            {
                from: "./src/einstein-*.png", // TODO: don't hardcode icon png
                to: "./",
                flatten: true
            }
        ])
    ]
};