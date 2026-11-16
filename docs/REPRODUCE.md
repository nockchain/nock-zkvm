# Reproduce

The source is public at https://github.com/nockchain/nock-zkvm, tag `rel5.4`.

Nothing here is new: this page collects the commands of `../README.md` and `../nockvm-e2e/README.md` in one order.
Verdicts of executables are executed results, not kernel facts (`SPEC.md` §0).

1. **Library build.** `../README.md`, section Build (toolchain, the 48 GB module and the subset that avoids it).
2. **Axiom check (library).** `lake env lean scripts/delivery-axioms.lean`; the expected lines are in `THEOREMS.md`, each labelled with its source (E, L or R, `SPEC.md` §11.2). Every headline has one except `Nock.Jet.HoldsN`, a definition; the other cited declarations without a recorded line are listed in `theorems-unrecorded.tsv` (no axioms are claimed for them).
3. **Library demo.** `LAKE=lake scripts/demo-candidate.sh` (`../README.md`, section Demo).
4. **End-to-end build.** `../nockvm-e2e/README.md`, section Build; the certified verifier reproducibly with
   `bash nockvm-e2e/scripts/build-certified.sh <outdir>`.
5. **Axiom check (end to end).** A build of `NockvmE2E` prints one `depends on axioms` line per checked declaration
   (`../nockvm-e2e/README.md`, section Axiom check).
6. **Fixtures.** `../nockvm-e2e/README.md`, section Running the fixtures (`add`, family `j9al`; `jp`, family `j9alj`).
7. **An arbitrary program.** `nockvm-e2e/scripts/run-free.sh` (`../nockvm-e2e/README.md`, section Running an arbitrary program).
8. **Benchmark.** `scripts/bench.sh <runs> <outdir>` (`SPEC.md` §10.4).
9. **Regenerate the theorem index.** `python3 docs/gen/theorem_index.py --root . --rev <commit> --headlines docs/gen/headlines.txt --cited docs/SPEC.md --log LABEL=<build log> …`
