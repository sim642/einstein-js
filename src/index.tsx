import {Component, h, render} from "preact";
import {AppComponent} from "./web/AppComponent";

import * as OfflinePluginRuntime from 'offline-plugin/runtime';
OfflinePluginRuntime.install();

// import "preact/devtools";

render(<AppComponent/>, document.body);

/*var width = (window.innerWidth > 0) ? window.innerWidth : screen.width;
alert(width);*/
