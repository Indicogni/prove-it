# Prove It: Formally Verified Software in Lean 4

Don't hope the AI's code works. **Prove** it.

**Prove It** is a free, hands-on Indicogni course for working software and systems engineers. You learn Lean 4 from first principles and Socratic puzzles—not by proving ivory-tower Peano arithmetic (`0 + n = n`), and not by waiting on multi-gigabyte math library downloads, but by modeling, breaking, model-checking, and mathematically proving real software systems.

Every unit works in **two ways**:
1. **In your browser (zero setup):** Open the interactive web course (`site/index.html`, or hosted on Indicogni / GitHub Pages) to work through Socratic prediction gates, step through simulated Lean Infoview proof states, explore 6 interactive client-side labs, and launch any snippet in one click on [`live.lean-lang.org`](https://live.lean-lang.org/).
2. **On your computer or GitHub Codespaces:** Clone this repository (`https://github.com/indicogni/prove-it`), open it in VS Code with the Lean 4 extension (or a Dev Container / Codespace), solve starter exercises in `ProveIt/`, audit untrusted AI submissions with `lake exe verigate`, and differential-fuzz production code against `lake exe oracle`.

---

## Why Lean 4, and why now?

Software engineering has crossed an inflection point. Coding agents generate implementations and unit tests at 100x human speed—and share **correlated blind spots** when the same model writes both the code and the tests. Property tests sample finite ranges (`[0, 10^9]`) while `UInt64` overflows at `2^64 - 1`. Chaos tests run 10,000 short GC pauses and miss the one stale-epoch split-brain write that corrupts storage.

In this world, the engineer's highest-leverage job shifts from typing boilerplate to **owning the Trusted Computing Base (TCB)**:
- Designing crisp, total domain specifications (`Spec.lean`) that make illegal states unrepresentable.
- Running **Gear 1 (TLA+-style Bounded State Search)** inside Lean to catch shallow protocol bugs in milliseconds.
- Sealing **Gear 2 (Unbounded Inductive Invariants & Refinement Mappings)** in Lean's tiny trusted kernel across infinite execution traces, arbitrary message reorderings, and 64-bit hardware boundaries.
- Enforcing unforgeable CI verification gates (`lake exe verigate`) so AI agents can synthesize fast implementations and tactic scripts without sneaking `sorry`, custom `axiom`s, `native_decide`, `@[implemented_by]`, or vacuous preconditions past code review.

---

## Course Architecture

Zero external Lake dependencies. Pinning pure Core/`Std` Lean `v4.36.0` means `lake build` finishes in seconds offline and every single chapter file runs standalone in [`live.lean-lang.org`](https://live.lean-lang.org/).

### Part I · Executable Specifications & Gear 1 Model Checking
| Unit | Topic | Core Engineering Mechanism |
| :--- | :--- | :--- |
| **Ch 01** | `ProveIt/Ch01.lean` — *The Silent Truncation Bug* | Why `Nat` (`0 - 1 = 0`) breaks an AI rate-limiter; `Int`/`Option`, total functions, first proofs (`rfl`, `omega`). |
| **Ch 02** | `ProveIt/Ch02.lean` — *Illegal States & Domain Modeling* | Eliminating boolean-soup auth state via algebraic sum/product types and exhaustive pattern matching. |
| **Ch 03** | `ProveIt/Ch03.lean` — *Compile-Time Exhaustion & Boolean Reflection* | Finite RBAC matrices, `Decidable`, `decide`, and bridging `Bool` evaluators to `Prop` contracts (`↔`). |
| **Ch 04** | `ProveIt/Ch04.lean` — *Gear 1: A TLA+ Model Checker in 35 Lines* | `State`, `init`, `step`, and writing an executable BFS trace explorer that catches split-brain bugs automatically. |
| **CP 1** | `ProveIt/Checkpoints/Cp1.lean` — *Checkpoint 1: Zero-Panic Canary Router* | Closed-notes specification, determinism, and safety verification from scratch. |

### Part II · The Proof Engine & Gear 2 Inductive Invariants
| Unit | Topic | Core Engineering Mechanism |
| :--- | :--- | :--- |
| **Ch 05** | `ProveIt/Ch05.lean` — *Proofs Are Programs, Goals Are Stack Traces* | Reading the Infoview (`Objects`, `Hypotheses`, `⊢ Goal`); `→`, `∧`, `∨`, `¬`, `∀`, `∃` as API contracts. |
| **Ch 06** | `ProveIt/Ch06.lean` — *Control Flow, Rewriting & Linear Math* | Verifying retry/quota logic cleanly with `fun_cases`, `simp only`, `omega`, and `@[grind =]` / `grind`. |
| **Ch 07** | `ProveIt/Ch07.lean` — *Unprovable on Purpose* | Triage stuck Infoview goals into *(A) Buggy Code*, *(B) False Spec*, or *(C) Weak Invariant*; extract `#guard` counterexamples. |
| **Ch 08** | `ProveIt/Ch08.lean` — *Gear 2: Inductive Invariants & Strengthening* | TLA+ `Init`/`Next`/`Reachable`; why true safety properties fail on "Garden-of-Eden" states and how strengthening seals unbounded traces. |
| **CP 2** | `ProveIt/Checkpoints/Cp2.lean` — *Checkpoint 2: Idempotent Write-Ahead Ledger* | Repair a crash-replay double-credit bug and prove conservation of funds across arbitrary crash loops. |

### Part III · Precision Types, 64-Bit Hardware & Refinement
| Unit | Topic | Core Engineering Mechanism |
| :--- | :--- | :--- |
| **Ch 09** | `ProveIt/Ch09.lean` — *Packing Proofs into Types* | `Subtype` (`{ x // P x }`), `Fin n`, dependent `if h : P`, and zero-cost runtime proof erasure. |
| **Ch 10** | `ProveIt/Ch10.lean` — *64-Bit Hardware Truth (`UInt64` & `BitVec`)* | Catching `2^64 - 1` overflow blind spots with `bv_decide` and understanding LRAT certificate trust (`Lean.ofReduceBool`). |
| **Ch 11** | `ProveIt/Ch11.lean` — *Pure Effects & Termination as DoS Defense* | `Except`/`StateM` cores, `termination_by` / `decreasing_by` on overflow-free binary search & DAG resolution, `fun_induction`. |
| **Ch 12** | `ProveIt/Ch12.lean` — *Refinement Mappings & Stuttering Steps* | Proving an optimized log+cache KV store refines a 15-line abstract `SpecKV`, including compaction stuttering steps. |
| **CP 3** | `ProveIt/Checkpoints/Cp3.lean` — *Checkpoint 3: Verified Fixed-Capacity Ring Buffer* | Prove bounds safety and FIFO refinement against an abstract list queue. |

### Part IV · AI-Native Verification Engineering & Monday-Morning Transfer
| Unit | Topic | Core Engineering Mechanism |
| :--- | :--- | :--- |
| **Ch 13** | `ProveIt/Ch13.lean` — *How AI Cheats Formal Verification* | Defeating the 9 LLM exploit vectors: `sorry`, custom `axiom`, `native_decide`, `@[implemented_by]`, vacuous `False → ...` premises, and `#print axioms`. |
| **Ch 14** | `ProveIt/Ch14.lean` — *Spec-First Agentic Co-Design* | Locking human-owned `Spec` + mandatory non-vacuity witnesses (`∃ x, Valid x`) while delegating `Impl` & leaf tactics to AI. |
| **Ch 15** | `ProveIt/Ch15.lean` — *Verified Wire Formats (TLV Framing)* | Proving stream-safe binary packet round-trips: `decode (encode pkt ++ rest) = some (pkt, rest)`. |
| **Ch 16** | `ProveIt/Ch16.lean` — *Monday-Morning Transfer* | Connecting Lean 4 to Rust, Go, TypeScript, Python, and C++ services via differential fuzzing and typestate invariants. |
| **CP 4** | `ProveIt/Checkpoints/Cp4.lean` — *Checkpoint 4: Red-Team Audit of an AI Escrow Module* | Uncover 3 planted spec/soundness exploits, prove non-vacuity, and restore kernel soundness. |

---

## The 4 Production Capstones (`ProveIt/Capstones/` & `capstones/`)

Each capstone models an industrial verification domain with a starter module (`ProveIt/Capstones/*.lean`), an architectural brief (`capstones/*/README.md`), a 100% zero-`sorry` model solution (`Solutions/Capstones/*.lean`), and a proof-engineering commentary (`capstones/*/DESIGN.md`):

1. **`CedarLite` — Cloud Authorization & Policy Engine** (`capstones/cedar-lite/`)
   Inspired by AWS's Lean-verified Cedar engine. Model principals, actions, resources, and `permit`/`forbid` policies; prove **Default-Deny**, **Explicit-Forbid Overrides Permit**, and **Policy-Optimizer Equivalence**.
2. **`FencingKV` — Split-Brain Fencing Leases & Crash-Safe KV Store** (`capstones/fencing-kv/`)
   Full TLA+ Two-Gear verification: use Gear 1 BFS to catch GC-pause split-brain writes on unfenced storage, then prove Gear 2 unbounded inductive safety with monotonic fencing tokens plus tombstone-compaction refinement.
3. **`StackVM` — Verified Optimizing Expression Compiler & Stack VM** (`capstones/stack-vm/`)
   Build an arithmetic/conditional AST constant-folding optimizer and stack bytecode compiler; prove **Optimizer Soundness** and **Total Compiler Preservation** (`exec env (compile (optimize e) ++ rest) stk = some (eval env e :: stk)`).
4. **`VeriGate` & `Oracle` — AI Proof-Carrying Code Gate & Polyglot Differential Oracle** (`capstones/verigate/`, `Tools/`)
   Supervise untrusted coding agents in CI: `lake exe verigate` locks `Spec` hashes and audits axioms/attributes against all 9 cheat vectors (`RedTeam/`), while `lake exe oracle` + `scripts/fuzz_against_oracle.py` differential-fuzzes external code against verified Lean semantics.

---

## Getting Started (3 Ways)

### Way 1: In your browser (zero install)
Open `site/index.html` locally (via `python3 scripts/serve_local.py`, bound strictly to `127.0.0.1:8000`) or visit the hosted course page. Every chapter includes interactive Socratic prediction cards, simulated Lean Infoview steppers, 6 browser-native interactive labs (`site/labs/index.html`), and 1-click **Run on `live.lean-lang.org`** links.

### Way 2: Dev Container or GitHub Codespaces (recommended for full workspace)
Open this repository in VS Code Dev Containers or GitHub Codespaces. `.devcontainer/devcontainer.json` installs `elan` pinned to `leanprover/lean4:v4.36.0`, configures the `leanprover.lean4` extension, and prebuilds the workspace under a non-root user.

### Way 3: Local Lean 4 installation
1. Install [`elan`](https://lean-lang.org/install/) (Lean's toolchain manager, analogous to `rustup`).
2. Clone and build:
   ```sh
   git clone https://github.com/indicogni/prove-it.git
   cd prove-it
   lake build
   ```
3. Run your progress coach, the AI soundness gate, and the polyglot differential-fuzzing oracle:
   ```sh
   lake exe check
   lake exe check --solutions
   lake exe verigate --self-test
   lake exe oracle --demo
   python3 scripts/fuzz_against_oracle.py
   ```

---

## Where Hints & Model Solutions Live

- **Progressive Hints:** `guides/PART1_AND_2.md` and `guides/PART3_AND_4.md` give 3-tier Socratic nudges (*Goal-shape clue → Invariant/counterexample nudge → Tactic skeleton*) plus *Check your explanation* rubrics.
- **Model Solutions:** `Solutions/` mirrors `ProveIt/` 1-to-1 (`Solutions/Ch01.lean` through `Solutions/Ch16.lean`, `Solutions/Checkpoints/`, and `Solutions/Capstones/`), verified in CI with zero `sorry`s and strict kernel axiom checks.

---

## Disclaimer, Security & Licenses

Maintained by **Indicogni LLC**. See [`SECURITY.md`](SECURITY.md) to report security issues privately (`feedback@indicogni.com`), [`NOTICE.md`](NOTICE.md) for the educational/AI-authoring disclosure, [`LICENSE`](LICENSE) (MIT for code), and [`LICENSE-TEXT`](LICENSE-TEXT) (CC BY 4.0 for prose and diagrams). No cookies, no analytics, no telemetry.
