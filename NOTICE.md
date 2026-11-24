# Notice, Dual Licensing & Disclosures

**Prove It: Formally Verified Software in Lean 4**
Copyright (c) 2026 Indicogni LLC (`https://github.com/indicogni/prove-it`)

---

## 1. Dual Licensing Structure

To maximize reuse for both working software teams and educators, this repository is dual-licensed by **Indicogni LLC**:

1. **Source Code & Formal Artifacts — MIT License ([`LICENSE`](LICENSE)):**
   All Lean 4 modules (`ProveIt/`, `Solutions/`, `RedTeam/`, `Tools/`), Python scripts (`scripts/`), JavaScript and CSS (`site/assets/`), HTML application scaffolding, shell scripts (`.githooks/`), CI workflows (`.github/`), and Dev Container configurations (`.devcontainer/`) are licensed under the **MIT License**.
2. **Course Prose, Guides & Diagrams — CC BY 4.0 ([`LICENSE-TEXT`](LICENSE-TEXT)):**
   All instructional prose, Socratic exercises, hint guides (`guides/`), architectural design notes (`capstones/*/`), and diagrams are licensed under the **Creative Commons Attribution 4.0 International License (CC BY 4.0)**, attributed to **Indicogni LLC**.

When extracting code snippets from Markdown or HTML files into software projects, you may use those code snippets under the MIT License.

---

## 2. AI-Assisted Authoring & Verification Disclosure

Consistent with Indicogni LLC's transparency standards across `indicogni.com`:

- Course prose, interactive web labs, starter exercises, and reference solutions in this repository were created by **Indicogni LLC** using AI-assisted authoring and code-generation workflows under human architectural direction and editorial review.
- Every formal proof, reference solution (`Solutions/`), red-team exploit (`RedTeam/`), soundness auditor (`Tools/VeriGate.lean`), and differential oracle (`Tools/Oracle.lean`) is deterministically checked by the **Lean 4 kernel (`leanprover/lean4:v4.36.0`)** and automated CI gates (`lake build`, `lake exe check --solutions`, `lake exe verigate --self-test`, and `python3 scripts/fuzz_against_oracle.py`).

---

## 3. Educational & Safety Disclaimer

The formal models, specifications, protocols, and scripts in **Prove It** (including `CedarLite`, `FencingKV`, `StackVM`, `VeriGate`, and `Oracle`) are simplified **educational and pedagogical reference designs** created to teach formal verification engineering.

- **Not Turnkey Production Infrastructure:** They are provided *"AS IS"* without warranty of any kind and are not audited drop-in replacements for production authorization engines, distributed consensus stores, cryptographic modules, or sandboxes.
- **Know Your Trusted Computing Base (TCB):** A machine-checked proof guarantees only that an implementation satisfies the stated mathematical specification relative to Lean's trusted kernel, axioms, and compilation/runtime assumptions. Real-world production safety still depends on specification completeness, non-vacuity, FFI/serialization boundaries, OS/hardware behavior, and operational security controls.
- **Adversarial Examples (`RedTeam/`):** Files under `RedTeam/` intentionally demonstrate unsound or deceptive proof techniques (`sorry`, custom axioms, `@[implemented_by]`, compiler-trust gadgets, and vacuous specifications) strictly so engineers learn how to detect and block them in CI. Never copy patterns from `RedTeam/` into production verification harnesses.

Feedback and inquiries: **`feedback@indicogni.com`** (for security issues, see [`SECURITY.md`](SECURITY.md)).
