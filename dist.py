import http.server

PORT = 8000

class Handler(http.server.SimpleHTTPRequestHandler):
    pass

Handler.extensions_map[".wasm"] = "application/wasm" # needed for streaming WASM compilation

httpd = http.server.HTTPServer(("", PORT), Handler)

print("Serving at port", PORT)
httpd.serve_forever()