#!/usr/bin/env python3
"""Serve the same project-path UI; optionally supply actual COOP/COEP headers."""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--port', type=int, default=8012)
p.add_argument('--isolate', action='store_true')
p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[3])
a = p.parse_args()
root = a.root.resolve()
class Handler(SimpleHTTPRequestHandler):
    def end_headers(self):
        if a.isolate:
            self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
            self.send_header('Cross-Origin-Embedder-Policy', 'require-corp')
        super().end_headers()
server = ThreadingHTTPServer(('127.0.0.1', a.port), partial(Handler, directory=str(root)))
print(f'http://127.0.0.1:{a.port}/labs/linked-assurance/', flush=True)
server.serve_forever()
