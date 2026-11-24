# Security Policy

Maintained by **Indicogni LLC** (`https://github.com/indicogni/prove-it`).

Security, proof soundness, and learner privacy are core engineering invariants of **Prove It**. Because this repository teaches engineers how to supervise untrusted AI code and proof generators using Lean 4, we treat both **operational/web vulnerabilities** and **verification-gate soundness bypasses** as security issues.

---

## Reporting a Vulnerability

**Please do not report undisclosed security vulnerabilities through public GitHub issues, discussions, or pull requests.**

Choose either private channel below:

1. **GitHub Private Vulnerability Reporting (Preferred):**
   Submit a confidential advisory directly at:
   `https://github.com/indicogni/prove-it/security/advisories/new`
2. **Email:**
   Send a report to **`feedback@indicogni.com`** with **`SECURITY`** in the subject line (for example, `SECURITY: VeriGate axiom check bypass`).

### What to Include
- The affected file(s) and commit hash (for example, `Tools/VeriGate.lean` or `site/assets/app.js`).
- Minimal deterministic reproduction steps (`lake exe ...` or `python3 scripts/...` command, or browser reproduction steps).
- Expected secure behavior versus actual behavior, and assessment of impact.

### Response Targets
- **Initial acknowledgment:** Within 72 hours.
- **Triage & severity assessment:** Within 7 calendar days.
- **Remediation & coordinated disclosure:** Fixes are developed privately and credited (or kept anonymous at the reporter's preference) upon release.

---

## Scope

### In Scope

| Component | Security Properties Enforced |
| :--- | :--- |
| **`Tools/VeriGate.lean`** | Deterministic specification hash locking, `#print axioms` / kernel environment auditing, and detection of unsoundness or specification-tampering vectors (`sorryAx`, custom `axiom`, `unsafe`, `@[implemented_by]`, `@[extern]`, `Lean.ofReduceBool` / `Lean.ofReduceNat` / `native_decide` compiler trust when disallowed, and missing non-vacuity witnesses). Any technique where an untrusted `Impl` module passes `Tools/VeriGate.lean` while violating locked `Spec` soundness is **in scope**. |
| **`Tools/Oracle.lean`** | Executable reference semantics for `CedarLite` and `FencingKV`, input parsing totality, and freedom from crashes or misclassifications on adversarial inputs. |
| **`Tools/Check.lean`** | Solution and exercise verification runner integrity; prevention of false-positive green builds on incomplete (`sorry`) or unsound exercise files. |
| **`scripts/`** | `scripts/audit_security.py` (Zero-PII, git identity, token, and HTML/CSP scanner), `scripts/serve_local.py` (strict `127.0.0.1` binding, path-traversal prevention, strict Content Security Policy headers), and `scripts/fuzz_against_oracle.py` (safe subprocess invocation without shell injection). |
| **`.devcontainer/` & `.github/workflows/`** | Non-root container execution (`vscode`), zero host credential mounts, pinned Lean toolchain (`leanprover/lean4:v4.36.0`), SHA-pinned GitHub Actions, `persist-credentials: false`, and least-privilege `permissions: contents: read`. |
| **`site/`** | Strict Content Security Policy compatibility (`default-src 'self'`, zero inline scripts or `on*=` event attributes), safe DOM rendering (`textContent` / DOM APIs rather than untrusted `innerHTML`), `rel="noopener noreferrer"` on external links (`target="_blank"`), and strict zero-tracking/zero-cookie guarantees. |

### Out of Scope (Intentional Pedagogical Artifacts)

This course teaches engineers to find bugs and defeat adversarial AI proof exploits by working against realistic examples. The following **intentionally defective or adversarial artifacts** are out of scope *unless* they unexpectedly bypass a tool designed to catch them:

1. **`RedTeam/`** — Contains intentionally adversarial Lean 4 modules (`sorry`, custom `axiom`s, `unsafe`, `@[implemented_by]`, `native_decide`, tautological specifications, and vacuous `False → ...` preconditions) used as negative regression suites for `lake exe verigate --self-test`. *(Note: If a new exploit added to `RedTeam/` passes `Tools/VeriGate.lean` undetected, that bypass **is** in scope.)*
2. **Seeded Bug-Hunts & Unsolved Starter Exercises (`ProveIt/`, `capstones/`)** — Starter files intentionally contain `sorry` placeholders, buggy state transitions (such as unfenced split-brain storage in Chapter 4 / `FencingKV` Gear 1, or crash-replay bugs in Checkpoint 2), or intentionally unprovable theorems (Chapter 7) as part of the Socratic curriculum.
3. **Intentional Differential-Fuzzing Fault Injection (`--demo-bug`)** — `python3 scripts/fuzz_against_oracle.py --demo-bug` intentionally activates a stale-fencing-token bug in the Python candidate service to demonstrate how `lake exe oracle` catches divergence.
4. **Upstream Toolchains & External Services** — Bugs inside the upstream Lean 4 compiler/kernel (`leanprover/lean4`) or the external [`live.lean-lang.org`](https://live.lean-lang.org/) playground should be reported to their respective upstream maintainers.

---

## Privacy & Zero-Tracking Guarantee

- **No telemetry, analytics, or cookies:** The interactive web course (`site/`) makes zero background network requests, loads zero third-party fonts or scripts, sets zero cookies, and stores learner progress solely in browser `localStorage` on your own device.
- **Zero-PII repository hygiene:** Automated pre-commit hooks (`.githooks/pre-commit`) and CI gates (`python3 scripts/audit_security.py`) continuously verify that no personal names, local filesystem paths, credentials, or personal email addresses enter repository files or commit metadata.
