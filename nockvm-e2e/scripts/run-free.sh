#!/usr/bin/env bash
# run-free.sh LABEL --subject S --formula F [--prims id:op,...] [--fuel N]
#
# The whole chain for YOUR Nock program, ending in `verify` ACCEPT (family j9al):
#   emit (j9alemit2: trace/chip/inst dump + the ALU chip doc)  ->  nockvm-e2e-j9al-prove (FS proof + fixed-column proof)
#   ->  vk-setup  ->  fix-prove  ->  verify-fam verify
# Run from nockvm-e2e/ after `lake build nockvm-e2e-verify-fam nockvm-e2e-j9alemit2 nockvm-e2e-j9al-prove`.
#
# env:  WORK   output root (default ${TMPDIR:-/tmp}/nockvm-free); everything goes to $WORK/LABEL
#       CAPPED command prefix that caps memory (default none; e.g. a cgroup or ulimit wrapper)
#       BIN    exe directory (default .lake/build/bin)
# Exit: 0 = ACCEPT; 3 = a side condition / missing chip literal was reported before proving (nothing proved); other = failure.
set -u
LABEL=${1:?usage: run-free.sh LABEL --subject S --formula F [--prims id:op,...] [--fuel N]}
shift
WORK=${WORK:-${TMPDIR:-/tmp}/nockvm-free}
BIN=${BIN:-.lake/build/bin}
CAPPED=${CAPPED:-}
W=$WORK/$LABEL
HERE=$(pwd)
now() { date +%s; }
T0=$(now)
mkdir -p "$W/emit" "$W/docs" "$W/out"

echo "== 1/5 emit  (j9alemit2 $LABEL $*)"
$CAPPED $BIN/nockvm-e2e-j9alemit2 "$W/emit" "$@" "$LABEL" || { echo "emit failed (see ERROR lines above)"; exit 3; }
T1=$(now)

# the prover's chip-doc directory: the static docs (chipdocs/) + this run's ALU doc
for f in "$HERE"/chipdocs/*.json; do ln -sfn "$f" "$W/docs/$(basename "$f")"; done
ln -sfn "$W/emit/j9al_aluChipJ9.json" "$W/docs/j9al_aluChipJ9.json"

echo "== 2/5 prove (nockvm-e2e-j9al-prove)"
$CAPPED $BIN/nockvm-e2e-j9al-prove "$@" "$W/docs" "$LABEL" "$W/out"; rc=$?
[ $rc -eq 0 ] || { echo "prove failed rc=$rc"; exit $rc; }
T2=$(now)

V=$BIN/nockvm-e2e-verify-fam
echo "== 3/5 vk-setup"
$CAPPED $V vk-setup --family j9al "$W/out/$LABEL.inst.json" "$W/$LABEL.vk.json" || exit 4
echo "== 4/5 fix-prove"
$CAPPED $V fix-prove --family j9al "$W/out/$LABEL.inst.json" "$W/out/$LABEL.proof.json" "$W/$LABEL.fix.json" || exit 5
T3=$(now)
echo "== 5/5 verify"
$CAPPED $V verify --family j9al --vk "$W/$LABEL.vk.json" "$W/out/$LABEL.inst.json" "$W/out/$LABEL.proof.json" "$W/$LABEL.fix.json" | tee "$W/verify.txt"
vr=${PIPESTATUS[0]}
T4=$(now)
echo "times: emit $((T1-T0))s, prove $((T2-T1))s, vk-setup+fix-prove $((T3-T2))s, verify $((T4-T3))s, total $((T4-T0))s"
exit $vr
