# Contributing to Prove It

Thank you for helping improve **Prove It: Formally Verified Software in Lean 4**, maintained by **Indicogni LLC** (`https://github.com/indicogni/prove-it`).

---

## 1. Issues-First Workflow

Before spending time on a non-trivial pull request, **please open an issue first** (or write to `feedback@indicogni.com` for general course feedback):

- **Bug reports & errata:** Open an issue describing the chapter, Lean file, or interactive lab, along with exact reproduction steps and Lean toolchain output (`leanprover/lean4:v4.36.0`).
- **Security & VeriGate bypasses:** **Do not open a public issue.** Follow [`SECURITY.md`](SECURITY.md) (`feedback@indicogni.com` with `SECURITY` in the subject, or GitHub Private Vulnerability Reporting).
- **Curriculum or feature proposals:** Open an issue first so we can verify alignment with the course's zero-Mathlib dependency constraint, Socratic pedagogy, and Trusted Computing Base scope. Small typo fixes may be submitted directly.

---

## 2. Strict Zero-PII & Privacy Rules

Indicogni repositories enforce a strict **Zero-PII** invariant across all tracked files, test fixtures, comments, HTML/JS assets, and git history:

1. **No personal paths or machine metadata:** Never commit local filesystem paths (such as Linux/macOS user home directories or Windows user profile paths), machine hostnames, usernames, editor state, or local logs. Use repository-relative paths (`ProveIt/Ch01.lean`) or generic placeholders (`~/prove-it`) when explaining CLI commands.
2. **No personal emails or personal GitHub URLs in repository files:** Use RFC 2606 example domains (`alice@example.com`) in test fixtures and `Indicogni LLC` (`noreply@indicogni.com` / `feedback@indicogni.com`) in repository metadata. External GitHub links in repository code and docs are restricted to official project/upstream organizations (`indicogni`, `leanprover`, `leanprover-community`, `devcontainers`, `actions`).
3. **No external trackers, CDN dependencies, or inline scripts in `site/`:** All static site assets must work offline under strict Content Security Policy headers (`default-src 'self'`), use `rel="noopener noreferrer"` on `target="_blank"` links, and render untrusted/user inputs via safe DOM APIs (`textContent`).
4. **Git hooks & repository identity:** Enable the repository pre-commit hook immediately after cloning:
   ```sh
   git config core.hooksPath .githooks
   ```
   Official repository commits use `Indicogni LLC <noreply@indicogni.com>`, enforced by `.githooks/pre-commit` and `scripts/audit_security.py`.

---

## 3. Pre-Submission Verification Checklist

Every pull request must pass the full local verification suite cleanly with zero external network dependencies:

```sh
# 1. Security, Zero-PII, git identity, and HTML/CSP audit
python3 scripts/audit_security.py

# 2. Full Lean 4 build (Core/Std v4.36.0 only — zero external Lake packages)
lake build

# 3. Verify all model solutions have zero `sorry` and clean kernel axioms
lake exe check --solutions

# 4. Run VeriGate soundness & RedTeam regression suite
lake exe verigate --self-test

# 5. Run 200-workload polyglot differential fuzzing suite against Lean oracle
python3 scripts/fuzz_against_oracle.py
```

---

## 4. Architectural Invariants

- **Zero External Lake Dependencies:** Do not add Mathlib or third-party Lake packages to `lakefile.toml`. Every chapter in `ProveIt/` must compile standalone in `leanprover/lean4:v4.36.0` (including one-click runs on `live.lean-lang.org`) in seconds.
- **1-to-1 Starter / Solution Parity:** Any change to an exercise signature or theorem statement in `ProveIt/` must be mirrored identically in `Solutions/` and locked appropriately if covered by `Tools/VeriGate.lean`.

---

## 5. Contributor License Agreement (Inbound = Outbound)

By submitting a contribution to this repository, you certify that you have the right to submit it and agree that your code contributions are licensed under the **MIT License** ([`LICENSE`](LICENSE)) and your prose/diagram contributions are licensed under **CC BY 4.0** ([`LICENSE-TEXT`](LICENSE-TEXT)), consistent with [`NOTICE.md`](NOTICE.md).
