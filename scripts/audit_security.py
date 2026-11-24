#!/usr/bin/env python3
"""
Prove It — Zero-PII, Git Identity, Supply-Chain & Web Security Auditor
Copyright (c) 2026 Indicogni LLC. MIT License.

Audits the repository for:
  1. Runtime-discovered local PII (current OS user, hostname, global git user/email)
     WITHOUT ever hardcoding any real PII string in source code.
  2. Hardcoded OS home paths (/home/<user>, /Users/<user>, C:\\Users\\<user>).
  3. Non-approved email addresses (only @indicogni.com and RFC 2606 @example.* allowed).
  4. Personal GitHub URLs outside approved upstream/project organizations
     (indicogni, leanprover, leanprover-community, devcontainers, actions).
  5. Accidental API tokens, cloud keys, or PEM private key headers.
  6. HTML & CSP safety across site/**/*.html (no inline <script>, no inline on*=
     event attributes, no external script/style/img trackers, no javascript: URLs,
     mandatory rel="noopener noreferrer" on target="_blank" links, no document.cookie).
  7. Git commit history author & committer enforcement:
     Every commit MUST use `Indicogni LLC <noreply@indicogni.com>`.
"""

from __future__ import annotations

import argparse
from html.parser import HTMLParser
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
from typing import Iterable

EXPECTED_GIT_NAME = "Indicogni LLC"
EXPECTED_GIT_EMAIL = "noreply@indicogni.com"
EXPECTED_GIT_IDENT = f"{EXPECTED_GIT_NAME} <{EXPECTED_GIT_EMAIL}>"

ALLOWED_EMAIL_DOMAINS = frozenset({
    "indicogni.com",
    "example.com",
    "example.org",
    "example.net",
})

ALLOWED_GITHUB_OWNERS = frozenset({
    "indicogni",
    "leanprover",
    "leanprover-community",
    "devcontainers",
    "actions",
})

# Generic container, CI, and OS service identifiers that are common English words
# or standard non-personal runtime environments (e.g., GitHub Actions USER=runner).
GENERIC_RUNTIME_TOKENS = frozenset({
    "runner",
    "vscode",
    "codespace",
    "codespaces",
    "root",
    "ubuntu",
    "debian",
    "alpine",
    "fedora",
    "nobody",
    "daemon",
    "git",
    "lean",
    "lake",
    "elan",
    "ci",
    "build",
    "builder",
    "docker",
    "container",
    "localhost",
    "localdomain",
    "user",
    "users",
    "admin",
    "default",
    "agent",
    "worker",
    "main",
    "test",
    "indicogni",
    "indicogni llc",
    "noreply@indicogni.com",
    "feedback@indicogni.com",
})

SKIP_DIRS = frozenset({
    ".git",
    ".lake",
    "build",
    "__pycache__",
    ".mypy_cache",
    ".pytest_cache",
    "node_modules",
})

BINARY_EXTENSIONS = frozenset({
    ".olean",
    ".ilean",
    ".trace",
    ".png",
    ".jpg",
    ".jpeg",
    ".gif",
    ".webp",
    ".ico",
    ".woff",
    ".woff2",
    ".ttf",
    ".otf",
    ".pdf",
    ".zip",
    ".tar",
    ".gz",
    ".wasm",
})

# Constructed via concatenation so this auditor never contains literal patterns that
# could look like paths or PEM headers under naive raw text scans.
HOME_PATH_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("Unix home path", re.compile(r"(?<![A-Za-z0-9_])/" + r"home/[A-Za-z0-9._-]+")),
    ("macOS home path", re.compile(r"(?<![A-Za-z0-9_])/" + r"Users/[A-Za-z0-9._-]+")),
    ("Windows home path", re.compile(r"\b[A-Za-z]:\\" + r"Users\\[A-Za-z0-9._-]+")),
]

EMAIL_RE = re.compile(
    r"(?<![A-Za-z0-9_/-])([A-Za-z0-9._%+-]+@([A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}))\b"
)

GITHUB_URL_RE = re.compile(
    r"https?://(?:www\.)?(?:github\.com|raw\.githubusercontent\.com)/([A-Za-z0-9_.-]+)"
)

SECRET_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("GitHub token", re.compile(r"\b(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9]{20,}\b")),
    ("GitHub fine-grained PAT", re.compile(r"\bgithub_pat" + r"_[A-Za-z0-9_]{20,}\b")),
    ("AWS access key ID", re.compile(r"\b(?:AKIA|ASIA)[0-9A-Z]{16}\b")),
    ("API secret key", re.compile(r"\bsk-(?:ant-|proj-)?[A-Za-z0-9_-]{24,}\b")),
    ("Slack token", re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{12,}\b")),
    ("Google API key", re.compile(r"\bAIza[0-9A-Za-z_-]{35}\b")),
    (
        "PEM private key",
        re.compile(r"-----BEGIN " + r"(?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----"),
    ),
]

JS_TRACKER_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("Cookie access (`document.cookie`)", re.compile(r"\bdocument\.cookie\b")),
    (
        "Third-party analytics SDK",
        re.compile(
            r"\b(?:google-analytics\.com|googletagmanager\.com|plausible\.io|posthog\.com|mixpanel\.com)\b",
            re.IGNORECASE,
        ),
    ),
]


class SiteHTMLSecurityParser(HTMLParser):
    """Strict CSP & DOM link-safety validator for static HTML files under site/."""

    def __init__(self, rel_path: str) -> None:
        super().__init__(convert_charrefs=False)
        self.rel_path = rel_path
        self.findings: list[str] = []

    def _record(self, message: str) -> None:
        line, col = self.getpos()
        self.findings.append(f"{self.rel_path}:{line}:{col}: {message}")

    @staticmethod
    def _is_external_url(url: str) -> bool:
        stripped = url.strip().lower()
        return (
            stripped.startswith("http://")
            or stripped.startswith("https://")
            or stripped.startswith("//")
        )

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag_lower = tag.lower()
        attr_map: dict[str, str] = {}

        for raw_name, raw_val in attrs:
            name = raw_name.lower()
            val = raw_val or ""
            attr_map[name] = val

            if name.startswith("on"):
                self._record(
                    f"Inline event handler `{raw_name}=` on <{tag_lower}> violates strict CSP"
                )

            if name in {"href", "src", "action", "formaction"}:
                if val.strip().lower().startswith("javascript:"):
                    self._record(f"Unsafe `javascript:` URL in `{raw_name}` on <{tag_lower}>")

        if tag_lower == "script":
            src = attr_map.get("src", "").strip()
            if not src:
                self._record(
                    "Inline <script> without local `src` violates strict `script-src 'self'` CSP"
                )
            elif self._is_external_url(src):
                self._record(
                    f"External <script src=\"{src}\"> violates offline/zero-tracker policy"
                )

        if tag_lower == "link":
            rel_tokens = set(attr_map.get("rel", "").lower().split())
            href = attr_map.get("href", "").strip()
            if ("stylesheet" in rel_tokens or "preconnect" in rel_tokens or "preload" in rel_tokens) and self._is_external_url(href):
                self._record(
                    f"External <link rel=\"{attr_map.get('rel', '')}\" href=\"{href}\"> violates offline CSP"
                )

        if tag_lower in {"img", "iframe", "audio", "video", "source", "embed", "object"}:
            src = attr_map.get("src", "").strip()
            if src and self._is_external_url(src):
                self._record(
                    f"External <{tag_lower} src=\"{src}\"> violates zero-tracker CSP"
                )

        if tag_lower == "a":
            target = attr_map.get("target", "").strip().lower()
            if target == "_blank":
                rel_tokens = set(attr_map.get("rel", "").lower().split())
                missing = {"noopener", "noreferrer"} - rel_tokens
                if missing:
                    missing_str = ", ".join(sorted(missing))
                    self._record(
                        f"<a target=\"_blank\"> missing `{missing_str}` in `rel` attribute"
                    )


def discover_runtime_pii_patterns() -> list[tuple[str, re.Pattern[str]]]:
    """Dynamically build regexes for the local environment's user/host/git identity."""
    raw_candidates: list[tuple[str, str]] = []

    for env_key in ("USER", "LOGNAME", "USERNAME"):
        val = os.environ.get(env_key, "").strip()
        if val:
            raw_candidates.append((f"env:{env_key}", val))

    try:
        hostname = socket.gethostname().strip()
        if hostname:
            raw_candidates.append(("hostname", hostname))
            short_host = hostname.split(".")[0].strip()
            if short_host and short_host != hostname:
                raw_candidates.append(("hostname-short", short_host))
    except OSError:
        pass

    for git_key in ("user.name", "user.email"):
        try:
            proc = subprocess.run(
                ["git", "config", "--global", "--get", git_key],
                capture_output=True,
                text=True,
                timeout=3,
                check=False,
            )
            if proc.returncode == 0:
                val = proc.stdout.strip()
                if val:
                    raw_candidates.append((f"global-git:{git_key}", val))
        except (OSError, subprocess.SubprocessError):
            pass

    compiled: list[tuple[str, re.Pattern[str]]] = []
    seen_values: set[str] = set()

    for source_label, token in raw_candidates:
        norm = token.lower()
        if len(norm) < 3 or norm in GENERIC_RUNTIME_TOKENS or norm in seen_values:
            continue
        seen_values.add(norm)
        # Match on non-alphanumeric boundaries so substrings inside unrelated hex SHAs do not collide
        pattern = re.compile(
            r"(?<![A-Za-z0-9])" + re.escape(token) + r"(?![A-Za-z0-9])",
            re.IGNORECASE,
        )
        compiled.append((f"Runtime local PII ({source_label})", pattern))

    return compiled


def iter_repo_files(repo_root: Path) -> Iterable[Path]:
    """Yield all non-ignored, non-binary repository files."""
    for dirpath, dirnames, filenames in os.walk(repo_root):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
        base = Path(dirpath)
        for filename in sorted(filenames):
            path = base / filename
            if path.suffix.lower() in BINARY_EXTENSIONS:
                continue
            if filename.startswith("NOTES.md.bak") or filename == ".prove_it_progress.json":
                continue
            yield path


def scan_text_content(
    rel_path: str,
    text: str,
    runtime_pii: list[tuple[str, re.Pattern[str]]],
) -> list[str]:
    """Scan a single file's text content for PII, forbidden URLs/emails, secrets, and web issues."""
    findings: list[str] = []

    for lineno, line in enumerate(text.splitlines(), start=1):
        for label, pii_re in runtime_pii:
            if pii_re.search(line):
                findings.append(f"{rel_path}:{lineno}: Detected {label} leak in repository text")

        for label, path_re in HOME_PATH_PATTERNS:
            match = path_re.search(line)
            if match:
                findings.append(
                    f"{rel_path}:{lineno}: Hardcoded {label} `{match.group(0)}` violates Zero-PII rule"
                )

        for email_match in EMAIL_RE.finditer(line):
            full_email = email_match.group(1)
            domain = email_match.group(2).lower()
            if domain not in ALLOWED_EMAIL_DOMAINS:
                findings.append(
                    f"{rel_path}:{lineno}: Non-approved email address `{full_email}` "
                    f"(allowed domains: {', '.join(sorted(ALLOWED_EMAIL_DOMAINS))})"
                )

        for gh_match in GITHUB_URL_RE.finditer(line):
            owner = gh_match.group(1)
            if owner.lower() not in ALLOWED_GITHUB_OWNERS:
                findings.append(
                    f"{rel_path}:{lineno}: GitHub URL owner `{owner}` outside approved organizations "
                    f"({', '.join(sorted(ALLOWED_GITHUB_OWNERS))})"
                )

        for label, secret_re in SECRET_PATTERNS:
            if secret_re.search(line):
                findings.append(f"{rel_path}:{lineno}: Potential {label} detected")

    normalized_rel = rel_path.replace("\\", "/")
    if normalized_rel.startswith("site/") and normalized_rel.endswith(".html"):
        parser = SiteHTMLSecurityParser(normalized_rel)
        parser.feed(text)
        findings.extend(parser.findings)

    if normalized_rel.startswith("site/") and normalized_rel.endswith(".js"):
        for lineno, line in enumerate(text.splitlines(), start=1):
            for label, js_re in JS_TRACKER_PATTERNS:
                if js_re.search(line):
                    findings.append(f"{normalized_rel}:{lineno}: Forbidden {label} in site JS")

    return findings


def audit_git_commits(repo_root: Path, check_staged_ident: bool) -> list[str]:
    """Verify git history and (optionally) upcoming commit author/committer identities."""
    findings: list[str] = []
    git_dir = repo_root / ".git"
    if not git_dir.exists():
        return findings

    if check_staged_ident:
        for var_name in ("GIT_AUTHOR_IDENT", "GIT_COMMITTER_IDENT"):
            proc = subprocess.run(
                ["git", "var", var_name],
                cwd=repo_root,
                capture_output=True,
                text=True,
                check=False,
            )
            if proc.returncode != 0:
                findings.append(f"git var {var_name} failed: {proc.stderr.strip()}")
                continue
            # Format: "Name <email> timestamp tz"
            raw = proc.stdout.strip()
            gt_idx = raw.find(">")
            ident_prefix = raw[: gt_idx + 1] if gt_idx != -1 else raw
            if ident_prefix != EXPECTED_GIT_IDENT:
                findings.append(
                    f"Upcoming commit {var_name} is `{ident_prefix}`, "
                    f"must be `{EXPECTED_GIT_IDENT}`"
                )

    head_check = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if head_check.returncode != 0:
        # Unborn HEAD (no commits yet in repository)
        return findings

    log_proc = subprocess.run(
        ["git", "log", "--all", "--format=%H\t%an <%ae>\t%cn <%ce>"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if log_proc.returncode != 0:
        findings.append(f"Unable to inspect git log: {log_proc.stderr.strip()}")
        return findings

    for row in log_proc.stdout.splitlines():
        parts = row.split("\t")
        if len(parts) != 3:
            continue
        commit_sha, author_ident, committer_ident = parts
        short_sha = commit_sha[:12]
        if author_ident != EXPECTED_GIT_IDENT:
            findings.append(
                f"git commit {short_sha}: author `{author_ident}` != `{EXPECTED_GIT_IDENT}`"
            )
        if committer_ident != EXPECTED_GIT_IDENT:
            findings.append(
                f"git commit {short_sha}: committer `{committer_ident}` != `{EXPECTED_GIT_IDENT}`"
            )

    return findings


def run_self_test() -> int:
    """Deterministic unit self-test verifying all scanner detectors catch violations."""
    dummy_pii = [("Runtime local PII (test)", re.compile(r"\bsynthetic_local_user_42\b"))]

    cases: list[tuple[str, str, str, bool]] = [
        ("clean.lean", "def x : Nat := 42\n-- Contact feedback@indicogni.com\n", "clean Lean", True),
        ("pii.md", "Path leak: synthetic_local_user_42 was here\n", "runtime PII", False),
        ("home.sh", "export DIR=/" + "home/jdoe/project\n", "Unix home path", False),
        ("email.md", "Reach me at personal.person" + "@gmail.com\n", "personal email", False),
        ("gh.md", "See https://github.com/" + "some-random-person/repo\n", "personal GitHub URL", False),
        ("gh_ok.md", "See https://github.com/indicogni/prove-it\n", "approved GitHub URL", True),
        ("tok.env", "TOKEN=ghp_" + "A" * 36 + "\n", "GitHub PAT", False),
        ("site/bad1.html", "<script>alert(1)</script>", "inline script", False),
        ("site/bad2.html", '<button onclick="go()">Run</button>', "inline onclick", False),
        (
            "site/bad3.html",
            '<a href="https://live.lean-lang.org/" target="_blank">Run</a>',
            "target _blank without noopener noreferrer",
            False,
        ),
        (
            "site/good.html",
            '<!doctype html><script src="./assets/app.js"></script>'
            '<a href="https://live.lean-lang.org/" target="_blank" rel="noopener noreferrer">Run</a>',
            "compliant site HTML",
            True,
        ),
    ]

    for rel_path, sample, desc, should_pass in cases:
        res = scan_text_content(rel_path, sample, dummy_pii)
        passed = len(res) == 0
        if passed != should_pass:
            print(f"[FAIL] audit_security --self-test failed on case `{desc}`: {res}", file=sys.stderr)
            return 1

    print("[OK] audit_security.py --self-test passed all 11 positive/negative security assertions.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prove It Zero-PII, Git Identity & Web Security Auditor"
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root directory",
    )
    parser.add_argument(
        "--check-staged-ident",
        action="store_true",
        help="Also verify `git var GIT_AUTHOR_IDENT` and `GIT_COMMITTER_IDENT` (used in pre-commit)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run built-in positive/negative detector unit tests",
    )
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()

    repo_root: Path = args.root.resolve()
    runtime_pii = discover_runtime_pii_patterns()
    all_findings: list[str] = []
    scanned_count = 0
    html_count = 0

    for file_path in iter_repo_files(repo_root):
        rel_path = file_path.relative_to(repo_root).as_posix()
        try:
            text = file_path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        scanned_count += 1
        if rel_path.startswith("site/") and rel_path.endswith(".html"):
            html_count += 1
        all_findings.extend(scan_text_content(rel_path, text, runtime_pii))

    all_findings.extend(audit_git_commits(repo_root, args.check_staged_ident))

    if all_findings:
        print("SECURITY & PRIVACY AUDIT FAILED:", file=sys.stderr)
        for item in all_findings:
            print(f"  - {item}", file=sys.stderr)
        print(
            f"\nFound {len(all_findings)} violation(s) across {scanned_count} audited files.",
            file=sys.stderr,
        )
        return 1

    print(
        f"[OK] Security & Zero-PII audit passed: {scanned_count} files ({html_count} HTML pages), "
        f"zero PII/token leaks, strict CSP compliance, clean git history."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
