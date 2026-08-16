#!/usr/bin/env python3
"""Assemble and serve the website together with the generated API pages."""

from __future__ import annotations

import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import shutil
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
WEBSITE = ROOT / "website"
API_DOCS = ROOT / "docbuild" / ".lake" / "build" / "doc"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Serve a local preview containing the website and doc-gen4 API pages."
    )
    parser.add_argument("--bind", default="127.0.0.1", help="address to bind (default: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8000, help="port to use (default: 8000)")
    parser.add_argument(
        "--check",
        action="store_true",
        help="assemble the preview and exit without starting a server",
    )
    return parser.parse_args()


def check_inputs() -> bool:
    if not (WEBSITE / "index.html").is_file():
        print(f"website entry point not found: {WEBSITE / 'index.html'}", file=sys.stderr)
        return False
    if not (API_DOCS / "index.html").is_file():
        print(
            "API documentation has not been built.  Run:\n\n"
            "  cd docbuild\n"
            "  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4\n"
            "  lake build QuotientSubmoduleEquidistribution:docs\n",
            file=sys.stderr,
        )
        return False
    return True


def assemble(destination: Path) -> None:
    shutil.copytree(WEBSITE, destination, dirs_exist_ok=True)
    shutil.copytree(API_DOCS, destination / "api", dirs_exist_ok=True)


def main() -> int:
    args = parse_args()
    if not check_inputs():
        return 1

    with tempfile.TemporaryDirectory(prefix="qse-site-") as temporary:
        site = Path(temporary)
        assemble(site)
        if args.check:
            print("local preview assembled successfully")
            return 0

        handler = partial(SimpleHTTPRequestHandler, directory=str(site))
        try:
            with ThreadingHTTPServer((args.bind, args.port), handler) as server:
                host = "localhost" if args.bind in {"127.0.0.1", "0.0.0.0", "::"} else args.bind
                port = server.server_address[1]
                print(f"Serving the complete site at http://{host}:{port}/")
                print("Press Ctrl+C to stop.")
                try:
                    server.serve_forever()
                except KeyboardInterrupt:
                    print()
        except OSError as error:
            print(f"could not start the preview server: {error}", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
