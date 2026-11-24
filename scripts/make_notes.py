#!/usr/bin/env python3
"""Generate or check the learner's NOTES.md Socratic synthesis workbook."""

from __future__ import annotations

import argparse
import pathlib
import shutil
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
NOTES_PATH = ROOT / "NOTES.md"

UNITS = [
    ("Ch 01", "The Silent Truncation Bug", "Why did `Nat` subtraction hide the rate-limiter bug, and when should a specification use `Int` or `Option` instead?"),
    ("Ch 02", "Illegal States & Domain Modeling", "How do algebraic sum/product types eliminate preconditions that would otherwise require theorem hypotheses?"),
    ("Ch 03", "Compile-Time Exhaustion & Boolean Reflection", "What does `Decidable P` bridge, and why prove `check x = true ↔ Safe x` instead of putting `Prop` inside runtime structs?"),
    ("Ch 04", "Gear 1: A TLA+ Model Checker in 35 Lines", "When does bounded BFS beat deductive proof, and where does state-space explosion force Gear 2?"),
    ("CP 01", "Checkpoint 1: Zero-Panic Canary Router", "Which invariant prevented routing traffic to a drained or zero-weight backend?"),
    ("Ch 05", "Proofs Are Programs, Goals Are Stack Traces", "How do `intro`, `apply`, `rcases`, and `constructor` correspond to constructing and pattern-matching ordinary data?"),
    ("Ch 06", "Control Flow, Rewriting & Linear Math", "Why should `simp only [...]` be preferred mid-proof while `grind` and `omega` close leaf goals?"),
    ("Ch 07", "Unprovable on Purpose", "Given a stuck Infoview goal, how do you tell apart (A) buggy code, (B) a false spec, and (C) a weak inductive hypothesis?"),
    ("Ch 08", "Gear 2: Inductive Invariants & Strengthening", "What is a 'Garden-of-Eden' state, and why can a true safety property fail naive one-step induction?"),
    ("CP 02", "Checkpoint 2: Idempotent Write-Ahead Ledger", "Which extra state invariant made crash-replay idempotency provable across arbitrary batch lengths?"),
    ("Ch 09", "Packing Proofs into Types", "Why do `Prop` fields inside `{ x // P x }` add zero runtime memory overhead after compilation?"),
    ("Ch 10", "64-Bit Hardware Truth (`UInt64` & `BitVec`)", "What additional component enters the Trusted Computing Base when switching from `omega` to `bv_decide`?"),
    ("Ch 11", "Pure Effects & Termination as DoS Defense", "Why did `(lo + hi) / 2` threaten both overflow and non-termination, and what measure proved termination?"),
    ("Ch 12", "Refinement Mappings & Stuttering Steps", "Why does background compaction need a stuttering clause `abs s' = abs s` in a refinement proof?"),
    ("CP 03", "Checkpoint 3: Fixed-Capacity Ring Buffer", "How does your `abs : RingBuffer α cap → List α` mapping distinguish full from empty?"),
    ("Ch 13", "How AI Cheats Formal Verification", "List three ways an untrusted agent can pass `lake build` without proving your intended property, and how `verigate` stops each."),
    ("Ch 14", "Spec-First Agentic Co-Design", "Why must every locked `Spec.lean` include a proven `∃ x, ValidInput x` non-vacuity witness?"),
    ("Ch 15", "Verified Wire Formats (TLV Framing)", "Why prove `decode (encode pkt ++ rest) = some (pkt, rest)` instead of `decode (encode pkt) = some (pkt, [])`?"),
    ("Ch 16", "Monday-Morning Transfer", "Where in your own team's stack would a 150-line Lean oracle (`lake exe oracle`) catch the highest-cost bugs?"),
    ("CP 04", "Checkpoint 4: Red-Team Batch Escrow Audit", "Which planted exploit in the escrow module was hardest to spot by human code review alone?"),
]


def render_workbook() -> str:
    lines = [
        "# Learner Synthesis Workbook (`NOTES.md`)",
        "",
        "Write two to four sentences in your own words after finishing each unit—**before** opening `Solutions/` or the *Check your explanation* rubric in `guides/`.",
        "Spaced retrieval schedule: revisit your notes at **+1 day**, **+7 days**, and **+21 days** without looking at the code.",
        "",
    ]
    for code, title, prompt in UNITS:
        lines.extend(
            [
                f"## {code} · {title}",
                "",
                f"**Prompt:** {prompt}",
                "",
                "**My synthesis:** _(write your answer here)_",
                "",
                "---",
                "",
            ]
        )
    return "\n".join(lines)


def has_learner_notes(text: str) -> bool:
    marker = "**My synthesis:** _(write your answer here)_"
    return text.count(marker) < len(UNITS)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify NOTES.md exists and contains all unit headers.")
    parser.add_argument("--force", action="store_true", help="Regenerate NOTES.md if untouched.")
    parser.add_argument("--discard-my-notes", action="store_true", help="Back up and overwrite even if edited.")
    args = parser.parse_args()

    expected = render_workbook()
    if args.check:
        if not NOTES_PATH.exists():
            print("ERROR: NOTES.md is missing.", file=sys.stderr)
            return 1
        current = NOTES_PATH.read_text(encoding="utf-8")
        missing = [f"## {c} · {t}" for c, t, _ in UNITS if f"## {c} · {t}" not in current]
        if missing:
            print(f"ERROR: NOTES.md is missing sections: {missing}", file=sys.stderr)
            return 1
        print("OK: NOTES.md verified.")
        return 0

    if NOTES_PATH.exists():
        current = NOTES_PATH.read_text(encoding="utf-8")
        if has_learner_notes(current) and not args.discard_my_notes:
            print("Refusing to overwrite edited NOTES.md without --discard-my-notes.", file=sys.stderr)
            return 1
        if not args.force and not args.discard_my_notes:
            print("NOTES.md already exists (pass --force to regenerate untouched template).")
            return 0
        bak = ROOT / "NOTES.md.bak"
        shutil.copy2(NOTES_PATH, bak)

    NOTES_PATH.write_text(expected, encoding="utf-8")
    print("Wrote NOTES.md.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
