#!/usr/bin/env bash
# bench.sh <runs> <outdir> [<name> <family> <dir> [<prog>]]
#
# Benchmark of the executed prover / verifier of this tree.
#   programs : add (family j9al) and jp (family j9alj, prover flag --reg-catj)
#   steps    : prove (nockvm-e2e-j9al-prove; also writes the fixed-column proof, which is part of its wall time),
#              vk-setup, fix-prove, verify (nockvm-e2e-verify-fam; verify uses the proof, vk and fix proof of the same run)
#   each run : [$BENCH_CAPPED] /usr/bin/time -v -o <file> timeout $BENCH_TIMEOUT <exe> <args>
#              -> wall seconds ("Elapsed") and peak RSS ("Maximum resident set size") from /usr/bin/time -v.
#   outputs  : <outdir>/header.txt   machine, commit, date, load average at start/end, exact command lines
#              <outdir>/results.csv  prog,step,run,wall_s,maxrss_kb,exit,inputs
#              <outdir>/sizes.csv    prog,run,file,json_bytes,field_elems,digests,binary_bytes
#              <outdir>/summary.md   median / min / max per (prog, step) + proof sizes
#              <outdir>/raw/         the /usr/bin/time -v file and the stdout/stderr of every run
#
# Third program (optional): `<name> <family: j9al|j9alj> <dir> [<prog>]`
#   with <prog>: <dir> is a chips directory and <prog> a program name known to nockvm-e2e-j9al-prove
#                (DriveJ9AL.progOf); all four steps are measured (prover flags via BENCH_PROG3_FLAGS, e.g. "--reg-catj").
#   without <prog>: <dir> holds <name>.inst.json, <name>.proof.json, <name>.fix.json (the instance names its chip files as
#                out3/<name>/<file>, so the chip files must be in <dir> too); prove is skipped, the other three steps are measured.
#
# Environment: BENCH_CHIPS (chips dir for prove, default ${TMPDIR:-/tmp}/nockvm-bench/chips: j8_*.json, j9a_*.json, j9al_aluChipJ9.json),
#              BENCH_TIMEOUT (seconds per run, default 2400), BENCH_CAPPED (command prefix that caps memory, default none).
#
# Binary proof size (no new serializer): count the JSON numbers of the file, minus the single `"version":1`;
#   digests D  = (numbers inside "roots" + numbers inside "sibs") / 5      (a Tip5 digest = 5 limbs)
#   field elements F = all numbers - 1 - 5*D   (K3 = 3 elements; query positions, leaf values and, in the proof file, the z vector
#                                               count as one element each)
#   binary bytes = F * 8 + D * 40
set -u
RUNS=${1:?usage: bench.sh <runs> <outdir> [<name> <family> <dir> [<prog>]]}
OUT=${2:?outdir}
P3=("${@:3}")
SELF=$(readlink -f "$0")
ROOT=$(dirname "$(dirname "$SELF")")
E2E=$ROOT/nockvm-e2e
CAPPED=${BENCH_CAPPED:-}   # optional command prefix that caps memory, e.g. a cgroup wrapper
TMO=${BENCH_TIMEOUT:-2400}
CHIPS=${BENCH_CHIPS:-${TMPDIR:-/tmp}/nockvm-bench/chips}
EXEP=$E2E/.lake/build/bin/nockvm-e2e-j9al-prove
EXEV=$E2E/.lake/build/bin/nockvm-e2e-verify-fam

mkdir -p "$OUT/raw" "$OUT/work/out3" || exit 2
OUT=$(readlink -f "$OUT")
W=$OUT/work
RAW=$OUT/raw
: > "$OUT/commands.txt"
echo "prog,step,run,wall_s,maxrss_kb,exit,inputs" > "$OUT/results.csv"
echo "prog,run,file,json_bytes,field_elems,digests,binary_bytes" > "$OUT/sizes.csv"
for x in "$EXEP" "$EXEV"; do [ -x "$x" ] || { echo "missing exe $x (build nockvm-e2e-j9al-prove nockvm-e2e-verify-fam first)" >&2; exit 2; }; done

# program table: name|family|mode(prove|fixture)|prove-prog|prove-flags|dir
PROGS=("add|j9al|prove|add||$CHIPS" "jp|j9alj|prove|jp|--reg-catj|$CHIPS")
if [ ${#P3[@]} -ge 3 ]; then
  if [ ${#P3[@]} -ge 4 ]; then PROGS+=("${P3[0]}|${P3[1]}|prove|${P3[3]}|${BENCH_PROG3_FLAGS:-}|${P3[2]}")
  else PROGS+=("${P3[0]}|${P3[1]}|fixture|||$(readlink -f "${P3[2]}")"); fi
fi

# size_of <file>  ->  "json_bytes F D binary"
size_of() {
  local f=$1 jb n r s d fe
  jb=$(wc -c < "$f")
  n=$(grep -oE '[0-9]+' "$f" | wc -l)
  r=$(grep -oE '"roots":\[(\[[0-9,]*\],?)*\]' "$f" | grep -oE '[0-9]+' | wc -l)
  s=$(grep -oE '"sibs":\[(\[[0-9,]*\],?)*\]' "$f" | grep -oE '[0-9]+' | wc -l)
  d=$(( (r + s) / 5 )); fe=$(( n - 1 - 5 * d ))
  echo "$jb $fe $d $(( fe * 8 + d * 40 ))"
}

# run_step <prog> <step> <run> <inputs> <cmd...>   (cwd = $W); appends to results.csv, returns the exit code
run_step() {
  local prog=$1 step=$2 run=$3 inputs=$4; shift 4
  local tf=$RAW/$prog-$step-$run.time of=$RAW/$prog-$step-$run.out rc wall rss
  echo "[$prog $step run $run] $CAPPED /usr/bin/time -v -o $tf timeout $TMO $*" >> "$OUT/commands.txt"
  rm -f "$tf"
  $CAPPED /usr/bin/time -v -o "$tf" timeout "$TMO" "$@" > "$of" 2>&1
  rc=$?
  if { [ "$step" = verify ] || [ "$step" = verify-online ]; } && [ $rc -eq 0 ] && ! grep -q '^ACCEPT' "$of"; then rc=99; fi
  wall=NA; rss=NA
  if [ -s "$tf" ]; then
    wall=$(awk -F': ' '/Elapsed \(wall clock\)/{n=split($NF,a,":"); s=0; for(i=1;i<=n;i++) s=s*60+a[i]; print s}' "$tf")
    rss=$(awk '/Maximum resident set size/{print $NF}' "$tf")
  fi
  echo "$prog,$step,$run,$wall,$rss,$rc,$inputs" >> "$OUT/results.csv"
  echo "  $prog $step run $run: wall ${wall}s rss ${rss}kB exit $rc"
  return $rc
}

{
  echo "# bench.sh header"
  echo "date (UTC)        : $(date -u '+%Y-%m-%d %H:%M:%S')"
  echo "host              : $(hostname)"
  echo "nproc             : $(nproc)"
  echo "cpu model         : $(awk -F': ' '/model name/{print $2; exit}' /proc/cpuinfo)"
  echo "RAM               : $(awk '/MemTotal/{printf "%.1f GB (%s kB)", $2/1048576, $2}' /proc/meminfo)"
  echo "commit            : $(cd "$ROOT" && git rev-parse HEAD) ($(cd "$ROOT" && git branch --show-current))"
  echo "tracked changes   : $(cd "$ROOT" && git status --short | grep -vc '^??')"
  echo "runs              : $RUNS     cap prefix: ${CAPPED:-none}     per-run timeout: ${TMO}s"
  echo "load avg at start : $(cut -d' ' -f1-3 /proc/loadavg)   (1/5/15 min; busy dev = not a measurement)"
  echo "programs          : $(for s in "${PROGS[@]}"; do printf '%s ' "${s%%|*}"; done)"
  echo "chips dir (prove) : $CHIPS"
  echo "command lines     : see commands.txt; per run, from cwd $W:"
  echo "  prove     : $EXEP [--reg-catj] $CHIPS <prog> out3/<prog>"
  echo "  vk-setup  : $EXEV vk-setup --family <fam> out3/<prog>/<prog>.inst.json <prog>.vk.json"
  echo "  fix-prove : $EXEV fix-prove --family <fam> out3/<prog>/<prog>.inst.json out3/<prog>/<prog>.proof.json <prog>.fix.json"
  echo "  verify    : $EXEV verify --family <fam> --vk <prog>.vk.json out3/<prog>/<prog>.inst.json out3/<prog>/<prog>.proof.json <prog>.fix.json"
  echo "  index     : $EXEV index --family <fam> out3/<prog>/<prog>.inst.json <prog>.vkon.json <prog>.pub.json   (j9a/j9alj only)"
  echo "  verify-online : $EXEV verify-online --family <fam> <prog>.vkon.json <prog>.pub.json out3/<prog>/<prog>.proof.json <prog>.fix.json   (j9a/j9alj only; j9al: n/a)"
  echo "  (each wrapped as: $CAPPED /usr/bin/time -v -o <time> timeout $TMO <cmd>)"
} > "$OUT/header.txt"

cd "$W" || exit 2
for spec in "${PROGS[@]}"; do
  IFS='|' read -r prog fam mode pprog pflags dir <<< "$spec"
  echo "== $prog ($fam, $mode)"
  for run in $(seq 1 "$RUNS"); do
    inputs=fresh
    rm -rf "$W/out3/$prog" "$W/$prog.vk.json" "$W/$prog.fix.json" "$W/$prog.vkon.json" "$W/$prog.pub.json"
    if [ "$mode" = prove ]; then
      # shellcheck disable=SC2086
      if ! run_step "$prog" prove "$run" fresh "$EXEP" $pflags "$dir" "$pprog" "out3/$prog"; then
        echo "  prove failed (see $RAW/$prog-prove-$run.out); the other steps use the committed fixture if there is one"
        FX=$E2E/fixtures/$([ "$prog" = add ] && echo j9al-add || echo j9alj-jp)
        if [ -d "$FX" ]; then rm -rf "$W/out3/$prog"; ln -sfn "$FX" "$W/out3/$prog"; inputs=fixture
        else continue; fi
      fi
    else
      ln -sfn "$dir" "$W/out3/$prog"
    fi
    pf=out3/$prog/$prog.proof.json; inst=out3/$prog/$prog.inst.json; fx=out3/$prog/$prog.fix.json
    if [ "$inputs" = fresh ] && [ -s "$pf" ]; then
      echo "$prog,$run,proof,$(size_of "$pf" | tr ' ' ',')" >> "$OUT/sizes.csv"
      [ -s "$fx" ] && echo "$prog,$run,prove-fix,$(size_of "$fx" | tr ' ' ',')" >> "$OUT/sizes.csv"
    fi
    run_step "$prog" vk-setup "$run" "$inputs" "$EXEV" vk-setup --family "$fam" "$inst" "$prog.vk.json"
    run_step "$prog" fix-prove "$run" "$inputs" "$EXEV" fix-prove --family "$fam" "$inst" "$pf" "$prog.fix.json"
    [ -s "$prog.fix.json" ] && echo "$prog,$run,fix,$(size_of "$prog.fix.json" | tr ' ' ',')" >> "$OUT/sizes.csv"
    # verification key: the vk-setup file (root + full instance, used by `verify --vk`) and, where the family has an online path,
    # the one-time-preprocessed online key from `index` (root + pubDigest + instance stripped of the private part) and the public input file
    [ -s "$prog.vk.json" ] && echo "$prog,$run,vk,$(size_of "$prog.vk.json" | tr ' ' ',')" >> "$OUT/sizes.csv"
    fxv=$prog.fix.json; [ -s "$fxv" ] || fxv=$fx
    run_step "$prog" verify "$run" "$inputs" "$EXEV" verify --family "$fam" --vk "$prog.vk.json" "$inst" "$pf" "$fxv"
    # verify-online: the verifier trusts the preprocessed vk file and reads only the public input (no instance recomputation).
    # c57e5023 has `index`/`verify-online` for j9a and j9alj only; for j9al (add) there is no such command: recorded as n/a.
    case "$fam" in
      j9a|j9alj)
        run_step "$prog" index "$run" "$inputs" "$EXEV" index --family "$fam" "$inst" "$prog.vkon.json" "$prog.pub.json"
        [ -s "$prog.vkon.json" ] && echo "$prog,$run,vk-online,$(size_of "$prog.vkon.json" | tr ' ' ',')" >> "$OUT/sizes.csv"
        [ -s "$prog.pub.json" ] && echo "$prog,$run,pub,$(size_of "$prog.pub.json" | tr ' ' ',')" >> "$OUT/sizes.csv"
        run_step "$prog" verify-online "$run" "$inputs" "$EXEV" verify-online --family "$fam" "$prog.vkon.json" "$prog.pub.json" "$pf" "$fxv" ;;
      *) echo "$prog,verify-online,$run,NA,NA,NA,n/a: no online command for family $fam" >> "$OUT/results.csv" ;;
    esac
  done
done
echo "load avg at end   : $(cut -d' ' -f1-3 /proc/loadavg)   ($(date -u '+%H:%M:%S') UTC)" >> "$OUT/header.txt"

# summary
stat3() { sort -n | awk '{a[NR]=$1} END{if(NR==0){print "NA NA NA 0"; exit} m=(NR%2)?a[(NR+1)/2]:(a[NR/2]+a[NR/2+1])/2; printf "%.2f %.2f %.2f %d", m, a[1], a[NR], NR}'; }
{
  cat "$OUT/header.txt"
  echo
  echo "## Time and memory (runs with exit 0; n = successful runs; inputs = fresh|fixture)"
  echo
  echo "| prog | step | n | wall median s | wall min | wall max | RSS median MB | RSS min | RSS max | inputs |"
  echo "|---|---|---|---|---|---|---|---|---|---|"
  for spec in "${PROGS[@]}"; do
    prog=${spec%%|*}
    for step in prove vk-setup fix-prove verify index verify-online; do
      w=$(awk -F, -v p="$prog" -v s="$step" '$1==p&&$2==s&&$6==0&&$4!="NA"{print $4}' "$OUT/results.csv" | stat3)
      m=$(awk -F, -v p="$prog" -v s="$step" '$1==p&&$2==s&&$6==0&&$5!="NA"{printf "%.1f\n", $5/1024}' "$OUT/results.csv" | stat3)
      inp=$(awk -F, -v p="$prog" -v s="$step" '$1==p&&$2==s{print $7}' "$OUT/results.csv" | sort -u | tr '\n' '/')
      bad=$(awk -F, -v p="$prog" -v s="$step" '$1==p&&$2==s&&$6!=0&&$6!="NA"{c++} END{print c+0}' "$OUT/results.csv")
      [ -n "$inp" ] || continue
      set -- $w $m
      echo "| $prog | $step | $4 (failed: $bad) | $1 | $2 | $3 | $5 | $6 | $7 | ${inp%/} |"
    done
  done
  echo
  echo "## Proof and key sizes (first run; binary = field elements x 8 + digests x 40, an estimate; vk = vk-setup file, vk-online = index file, pub = public input)"
  echo
  echo "| prog | file | JSON bytes | field elems | digests | binary bytes |"
  echo "|---|---|---|---|---|---|"
  awk -F, 'NR>1 && !seen[$1 FS $3]++ {print "| " $1 " | " $3 " | " $4 " | " $5 " | " $6 " | " $7 " |"}' "$OUT/sizes.csv"
  echo
  echo "Failures (exit != 0): $(awk -F, 'NR>1&&$6!=0&&$6!="NA"' "$OUT/results.csv" | wc -l) of $(( $(wc -l < "$OUT/results.csv") - 1 )) runs (exit 137 = killed (memory cap), 124 = timeout, 99 = verify without ACCEPT; rows with exit NA are n/a steps, not failures)"
} > "$OUT/summary.md"
echo "summary: $OUT/summary.md"
