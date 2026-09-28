#!/usr/bin/env bash
# Scan the Lean sources under Zeta2Lean/ and Solution.lean for forbidden constructs and remaining sorries.
# usage: bash scripts/audit.sh
# The definitive check is the `#print axioms` output at the end of Zeta2Lean/Window/Main.lean (printed by
# `lake build` or `lake env lean Zeta2Lean/Window/Main.lean`): every line must list only
# propext, Classical.choice, Quot.sound.  This grep is a fast census; it also catches declarations
# hidden behind modifiers/attributes (`private axiom`, `@[simp] axiom`, `noncomputable opaque`, ...).
# (`Challenge.lean` contains the one intended `sorry` of the Palomar statement.  The git-ignored scratch
# directory `Zeta2Lean/Scratch/` is skipped.)
cd "$(dirname "$0")/.." || exit 2
echo "== sorry / admit per file"
grep -rcE '\b(sorry|admit)\b' --include='*.lean' --exclude-dir=Scratch Zeta2Lean Solution.lean | grep -v ':0$' || echo "(none)"
echo "== forbidden constructs (axiom/opaque/unsafe declarations, also after modifiers or attributes; native_decide, implemented_by, extern, debug.skipKernelTC, ofReduceBool, trustCompiler)"
grep -rnE '^\s*(@\[[^]]*\]\s*)*((private|protected|noncomputable|partial|nonrec|scoped|local|unsafe)\s+)*(axiom|opaque|unsafe)\b|native_decide|implemented_by|@\[extern|debug\.skipKernelTC|Lean\.ofReduceBool|Lean\.trustCompiler' --include='*.lean' --exclude-dir=Scratch Zeta2Lean Solution.lean || echo "(none)"
