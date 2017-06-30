var Merge = require("webpack-merge");
var CommonConfig = require("./webpack.common.js");

var webpack = require("webpack");
var ChunkManifestPlugin = require("chunk-manifest-webpack-plugin");
var WebpackChunkHash = require("webpack-chunk-hash");
var ExtractTextPlugin = require("extract-text-webpack-plugin");
var OfflinePlugin = require('offline-plugin');

module.exports = Merge.smart(CommonConfig, {
    output: {
        filename: "[name].[chunkhash].js",
        hashDigestLength: 32 // MD5 actual length
    },

    module: {
        rules: [
            {
                test: /\.(png|svg|jpg|gif)$/,
                use: {
                    loader: "file-loader",
                    query: {
                        name: "[name].[hash].[ext]"
                    }
                }
            }
        ]
    },

    plugins: [
        new ExtractTextPlugin("[name].[contenthash].css"),

        // https://webpack.js.org/guides/caching/#deterministic-hashes
        new webpack.HashedModuleIdsPlugin(),
        new WebpackChunkHash(),

        new ChunkManifestPlugin({
            filename: "chunk-manifest.json",
            manifestVariable: "webpackManifest",
            inlineManifest: true
        }),

        // https://webpack.js.org/plugins/loader-options-plugin/
        new webpack.LoaderOptionsPlugin({
            minimize: true,
            debug: false
        }),

        // https://webpack.js.org/guides/production/#node-environment-variable
        new webpack.DefinePlugin({
            "process.env": {
                "NODE_ENV": JSON.stringify("production")
            }
        }),

        // https://webpack.js.org/guides/production/#minification
        new webpack.optimize.UglifyJsPlugin({
            sourceMap: true
        }),

        new OfflinePlugin({
            ServiceWorker: {
                cacheName: "einstein-js" // DO NOT CHANGE: https://github.com/NekR/offline-plugin/blob/master/docs/options.md#serviceworker-object--null--false
            }
        })
    ]
});