#!/usr/bin/env bash
# One-command J-8 demo.  Run from the repo root, no arguments.
#   tracegen (genJ8) -> Fiat-Shamir transcript (Tip5, FSJ8) -> stored files -> independent verify.
set -u
cd "$(dirname "$0")/.."
LAKE="${LAKE:-lake}"
EXE=.lake/build/bin/nockvm-j8check
if [ ! -x "$EXE" ]; then echo "== building nockvm-j8check (missing) =="; "$LAKE" build nockvm-j8check || exit 2; fi
OUT=.demo-out; mkdir -p "$OUT"
now() { date +%s.%N; }
step() { echo; echo "=== $1 ==="; T0=$(now); }
tdone() { awk -v a="$T0" -v b="$(now)" 'BEGIN{printf "    wall time: %.1f s\n", b-a}'; }
FAIL=0
expect() {
  want=$1; rc=$2
  if [ "$want" = ACCEPT ] && [ "$rc" = 0 ]; then echo "    VERDICT: ACCEPT (as expected)";
  elif [ "$want" = REJECT ] && [ "$rc" != 0 ]; then echo "    VERDICT: REJECT (as expected, rc=$rc)";
  else echo "    VERDICT: UNEXPECTED (wanted $want, rc=$rc)"; FAIL=1; fi
}
honest() { "$EXE" drive --prog "$1" --mode fs --out "$2" || return $?; "$EXE" verify --prog "$1" --dir "$2"; }

step "(a) J-8 honest run accepted: prog add, drive --mode fs, then verify"
honest add "$OUT/add"; expect ACCEPT $?; tdone

step "(b) tamper rejected: one committed column entry changed in the stored files, verify"
mkdir -p "$OUT/tamper"; cp "$OUT"/add/* "$OUT/tamper/"
f=$(ls "$OUT"/tamper/*.rows | head -1)
awk 'NR==1{$1=($1+1)} {print}' "$f" > "$f.new" && mv "$f.new" "$f"
echo "    edited first entry of $(basename "$f")"
"$EXE" verify --prog add --dir "$OUT/tamper"; expect REJECT $?; tdone

step "(c) false claim rejected: claimed result changed in pub.txt, verify"
mkdir -p "$OUT/claim"; cp "$OUT"/add/* "$OUT/claim/"
awk '{l[NR]=$0} END{n=split(l[NR],a," "); a[2]=a[2]+1; s=a[1]; for(i=2;i<=n;i++) s=s" "a[i]; l[NR]=s; for(i=1;i<=NR;i++) print l[i]}' "$OUT/add/pub.txt" > "$OUT/claim/pub.txt"
echo "    last line of pub.txt (claim): $(tail -1 "$OUT/add/pub.txt") -> $(tail -1 "$OUT/claim/pub.txt")"
"$EXE" verify --prog add --dir "$OUT/claim"; expect REJECT $?; tdone

step "(d) jetted 2x2 matmul accepted (prog mat, J present; checkFast)"
"$EXE" check --prog mat --fast; expect ACCEPT $?; tdone

step "(e) big atom accepted (eq5: op 5 on equal big atoms p+1 = p+1; FS drive + verify)"
honest eq5 "$OUT/eq5"; expect ACCEPT $?; tdone
step "(e') big atom accepted (ne5: p vs p+1, atom walk present)"
honest ne5 "$OUT/ne5"; expect ACCEPT $?; tdone

step "(f) J-9 B big-atom CLAIM: *[[(p+5) 0] [0 2]] = p+5 accepted via checkJ9; false claim p+6 rejected"
J9=.lake/build/bin/nockvm-j9dump
if [ ! -x "$J9" ]; then "$LAKE" build nockvm-j9dump || exit 2; fi
"$J9" > /dev/null 2> "$OUT/j9.log"; cut -c1-120 "$OUT/j9.log"
grep -q '^native checkJ9: true' "$OUT/j9.log" && echo "    VERDICT: ACCEPT (true claim, as expected)" || { echo "    VERDICT: UNEXPECTED"; FAIL=1; }
grep -q '^FALSE CLAIM.*checkJ9 false' "$OUT/j9.log" && echo "    VERDICT: REJECT (false big-atom claim, as expected)" || { echo "    VERDICT: UNEXPECTED"; FAIL=1; }
tdone

step "(g) six end-to-end programs through the J-8 pipeline (toy1 add dec mul fib ack)"
# the six programs are independent: run them in parallel (one core each), print in order
run_one() { p=$1; L="$OUT/s-$p.log"
  s=$(now); timeout "${CAP:-3600}" "$EXE" drive --prog "$p" --mode fs --out "$OUT/s-$p" > "$L" 2>&1; r1=$?; m=$(now)
  if [ "$r1" = 124 ]; then r2=124; echo "    $p: NOT FINISHED within ${CAP:-3600} s" >> "$L"
  else "$EXE" verify --prog "$p" --dir "$OUT/s-$p" >> "$L" 2>&1; r2=$?; fi
  e=$(now)
  awk -v s="$s" -v m="$m" -v e="$e" -v p="$p" -v a="$r1" -v b="$r2" 'BEGIN{printf "    %s: gen+FS %.1f s, verify %.1f s, rc=%s/%s\n", p, m-s, e-m, a, b}' >> "$L"
  echo "$r1 $r2" > "$OUT/s-$p.rc"; }
for p in toy1 add dec mul fib ack; do run_one "$p" & done
wait
for p in toy1 add dec mul fib ack; do
  echo "--- $p"; grep -vE '^\s+(recomputed|public)|^events' "$OUT/s-$p.log" | cut -c1-160
  read -r a b < "$OUT/s-$p.rc"
  if [ "$a" != 0 ] || [ "$b" != 0 ]; then echo "    $p: NOT ACCEPTED (rc $a/$b)"; FAIL=1; fi
done
tdone

echo; if [ "$FAIL" = 0 ]; then echo "DEMO RESULT: all steps as expected"; else echo "DEMO RESULT: some step UNEXPECTED"; fi
exit $FAIL
