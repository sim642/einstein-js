var Merge = require("webpack-merge");
var CommonConfig = require("./webpack.common.js");

var webpack = require("webpack");
var ExtractTextPlugin = require("extract-text-webpack-plugin");

module.exports = Merge(CommonConfig, {
    output: {

    },

    plugins: [
        new ExtractTextPlugin("[name].css"),

        // https://webpack.js.org/guides/caching/#deterministic-hashes
        new webpack.NamedModulesPlugin()
    ]
});