#!/usr/bin/env bash
# Replay, through the Lean kernel (leanchecker), the declarations of every project module in the
# import closure of a root module (default Solution, which imports Zeta2Lean.Window.Main), ONE module
# at a time (each run loads Mathlib, about 6-7 GB).  The modules must already be built
# (bash scripts/build.sh).
# usage: bash scripts/kernels.sh [Root.Module]
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2
TC=$(dirname "$(elan which lean)")
root="${1:-Solution}"
declare -A seen
queue=("$root")
while [ ${#queue[@]} -gt 0 ]; do
  m="${queue[0]}"; queue=("${queue[@]:1}")
  [ -n "${seen[$m]}" ] && continue
  seen[$m]=1
  f="${m//.//}.lean"
  for i in $(grep -E '^(public )?import Zeta2Lean' "$f" | awk '{print $NF}'); do queue+=("$i"); done
done
MODS=$(printf '%s\n' "${!seen[@]}" | sort)
echo "modules: $(echo "$MODS" | wc -l)"
fail=0
for m in $MODS; do
  start=$(date +%s)
  out=$( { /usr/bin/time -f 'maxrss_kb=%M' lake env "$TC/leanchecker" "$m"; } 2>&1 )
  code=$?
  rss=$(echo "$out" | grep -o 'maxrss_kb=[0-9]*' | tail -1)
  echo "$m exit=$code sec=$(( $(date +%s) - start )) $rss $(echo "$out" | grep -v maxrss | tail -2 | tr '\n' ' ')"
  [ $code -ne 0 ] && fail=1
done
echo "ALL_DONE fail=$fail"
