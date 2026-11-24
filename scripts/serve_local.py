#!/usr/bin/env python3
"""
Prove It — Safe Localhost-Only Preview Server (`127.0.0.1`)
Copyright (c) 2026 Indicogni LLC. MIT License.

Serves `site/` strictly on loopback (`127.0.0.1:8000` by default) with production
Content Security Policy and hardening headers so learners can preview the
interactive web course locally with zero network exposure.
"""

from __future__ import annotations

import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import sys
import threading
import urllib.request

CSP_POLICY = (
    "default-src 'self'; "
    "script-src 'self'; "
    "style-src 'self'; "
    "img-src 'self' data:; "
    "font-src 'self'; "
    "connect-src 'self'; "
    "object-src 'none'; "
    "base-uri 'self'; "
    "form-action 'self'; "
    "frame-ancestors 'none'"
)

SECURITY_HEADERS: tuple[tuple[str, str], ...] = (
    ("Content-Security-Policy", CSP_POLICY),
    ("X-Content-Type-Options", "nosniff"),
    ("X-Frame-Options", "DENY"),
    ("Referrer-Policy", "no-referrer"),
    ("Permissions-Policy", "camera=(), microphone=(), geolocation=()"),
    ("Cross-Origin-Opener-Policy", "same-origin"),
    ("Cross-Origin-Resource-Policy", "same-origin"),
    ("Cache-Control", "no-store"),
)

ALLOWED_LOOPBACK_HOSTS = frozenset({"127.0.0.1", "localhost"})


class HardenedSiteHandler(SimpleHTTPRequestHandler):
    """Static file handler for `site/` that injects strict CSP & security headers."""

    server_version = "ProveItLocalPreview/1.0"
    sys_version = ""

    def end_headers(self) -> None:
        for header_name, header_value in SECURITY_HEADERS:
            self.send_header(header_name, header_value)
        super().end_headers()


def run_self_test(site_dir: Path) -> int:
    """Start an ephemeral 127.0.0.1 server, verify security headers, and shut down."""
    handler = partial(HardenedSiteHandler, directory=str(site_dir))
    with ThreadingHTTPServer(("127.0.0.1", 0), handler) as httpd:
        host, port = httpd.server_address[:2]
        assert host == "127.0.0.1", f"Expected loopback bind, got {host}"
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        try:
            req = urllib.request.Request(f"http://127.0.0.1:{port}/", method="HEAD")
            try:
                with urllib.request.urlopen(req, timeout=3) as resp:
                    headers = {k.lower(): v for k, v in resp.headers.items()}
            except urllib.error.HTTPError as err:
                # Even if site/index.html is not generated yet (404), headers must be present
                headers = {k.lower(): v for k, v in err.headers.items()}

            csp = headers.get("content-security-policy", "")
            if "default-src 'self'" not in csp or "script-src 'self'" not in csp:
                print(f"[FAIL] Missing strict CSP header: {csp!r}", file=sys.stderr)
                return 1
            if headers.get("x-content-type-options") != "nosniff":
                print("[FAIL] Missing X-Content-Type-Options: nosniff", file=sys.stderr)
                return 1
        finally:
            httpd.shutdown()
            thread.join(timeout=2)

    print("[OK] serve_local.py --self-test verified loopback-only binding and strict CSP headers.")
    return 0


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    default_site = repo_root / "site"

    parser = argparse.ArgumentParser(
        description="Serve `site/` strictly on 127.0.0.1 with production CSP headers."
    )
    parser.add_argument(
        "--host",
        default="127.0.0.1",
        help="Loopback interface to bind (only 127.0.0.1 or localhost permitted)",
    )
    parser.add_argument(
        "--port",
        type=int,
        default=8000,
        help="TCP port on loopback interface (default: 8000)",
    )
    parser.add_argument(
        "--dir",
        type=Path,
        default=default_site,
        help="Static directory to serve (default: ./site)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Verify loopback binding and CSP headers on an ephemeral port and exit",
    )
    args = parser.parse_args()

    if args.host not in ALLOWED_LOOPBACK_HOSTS:
        print(
            f"ERROR: Refusing to bind non-loopback address `{args.host}`. "
            "Use `127.0.0.1` so the preview server is never exposed on a local network.",
            file=sys.stderr,
        )
        return 2

    site_dir = args.dir.resolve()
    if not site_dir.is_dir():
        print(f"ERROR: Site directory `{site_dir}` does not exist.", file=sys.stderr)
        return 2

    if args.self_test:
        return run_self_test(site_dir)

    handler = partial(HardenedSiteHandler, directory=str(site_dir))
    with ThreadingHTTPServer(("127.0.0.1", args.port), handler) as httpd:
        print(f"Prove It local preview serving `{site_dir.name}/` at http://127.0.0.1:{args.port}/")
        print(f"Strict CSP active: {CSP_POLICY}")
        print("Press Ctrl+C to stop.")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nShutting down local preview server.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
