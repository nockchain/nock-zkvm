# LIMITS: trusted base and stated gaps

This file covers both packages. The end-to-end release headlines are `nock_e2e_J9AL_succinct_B` and
`nock_e2e_J9ALJ_succinct_B` (and their base forms `nock_e2e_J9AL_succinct`, `nock_e2e_J9ALJ_succinct`); the library's own
scope and assumptions are `SPEC.md` §11.1.

## The library (J-8 to J-9 AL)

The library proves, for every staged prover and faithful jet registry, a soundness bound `< 2^-155` for the NockVM
arithmetization (J-9 AL included), with ideal coins: no commitment scheme, no low-degree test, no Fiat–Shamir theorem
(`SPEC.md` §4, §6.6, §11.1). Its executable checkers (`checkJ8`, `checkJ9ALX`) are related to the predicates by kernel theorems
(`checkJ8_iff`, `checkJ9ALX_iff`); the native executables' agreement with those functions is not kernel-checked.

## The end-to-end package (`nockvm-e2e/`)

Status column: **K** kernel-checked, **R** checked at run time by the executable, **T** trusted (assumed or read).
Lean paths are under `nockvm-e2e/NockvmE2E/`; `scripts/…` and `CERTIFIED.md` are under `nockvm-e2e/`.

### What an ACCEPT run trusts

| # | component | status | what is claimed |
|---|---|---|---|
| 1 | Lean 4.35 kernel | T | every **K** row rests on it; theorems use only `propext`, `Classical.choice`, `Quot.sound` |
| 2 | Lean compiler and runtime; C toolchain | T | the verifier executable is compiled code, not a kernel fact; the gates and the verdict run through compiled `Decidable` instances. For `nockvm-e2e-verify-cert` the Lean-emitted C and the binary are produced and hashed by `scripts/build-certified.sh` (reproducible; see `CERTIFIED.md`); the C compiler that turns that C into the binary is trusted |
| 3 | `main`: file I/O only | T (read; a few lines) | **`nockvm-e2e-verify-cert`** (`Exec/VerifyCertMain.lean`): `main` reads the vk, instance, the chip documents the instance names, proof and fix files, passes the bytes to the pure `Cert.verifyReport` and prints its line (exit 0 iff ACCEPT); nothing else. Kernel (`Exec/CertSound.lean`, `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): `verifyBytesL_sound` / `verifyBytesLJ_sound`: `verifyBytes* vk inst chips proof fix = .ok c` implies that the bytes parse (`Cert.parseInputs`) to some `XI0 root z π πF`, that `verdict9LVS` / `verdict9LJVS` is `.ok c` on them, and the conclusion of `nock_e2e_J9AL_succinct_S` / `nock_e2e_J9ALJ_succinct_S` at that `XI0`. So with this executable the trusted base is main's file I/O, the Lean compiler and runtime, and the C toolchain (rows 1-2). For the `verify --vk` arms of `Exec/VerifyFamMain.lean` (covered by the `_S` theorems, not certified), `main` is trusted to pass the loaded instance, the vk file's root, the proof and the printed claim to `verdict9LVS` (`--family j9al`) or `verdict9LJVS` (`--family j9alj`) unchanged. `verify-online --family j9alj` runs `verdict9LJVOB` and is not covered: it prints `ACCEPT-UNCOVERED` (row 8). `verdict9LVS_sound` / `verdict9LJVS_sound` (kernel) turn an accept into the hypotheses of the `_B` headlines, `verdict9LVB ... = .ok c` / `verdict9LJVB ... = .ok c`; the `_S` corollaries `nock_e2e_J9AL_succinct_S` / `nock_e2e_J9ALJ_succinct_S` state the headlines at the executed verdicts directly |
| 4 | JSON parser and loader | untrusted; **K** for `verify-cert` (no parser correctness needed), **R** for the `verify-fam` arms | `_S` quantifies over every parsed value, so `verifyBytes*_sound` holds for whatever `Json.parse` / `parseInputs` return (`Json.parse` and `Tr.parseEx` are `partial`, opaque to the kernel, and irrelevant to the proof). The instance the bytes parse to is the statement: a misparse can make the executable prove a different statement, not a false one; `parseInputs` is the small named function to read. The instance is also re-checked at run time: shape gate, `l = 170`, claim re-encoding, the datum link gate |
| 5 | claim decoder, emitter, prover | untrusted | the decoded claim is re-encoded and compared by the gate |
| 6 | shape, constraint and mask gates; `setupGates` | **R** | executed checks of kernel-defined functions; sound through rows 2 and 3 |
| 7 | chip files | untrusted; **R** | untrusted input, like row 4. The executed gate `chipsOkF` (inside the verdict) requires every loaded chip to equal (`chipEqB`) one of a fixed list of Lean literals (`Exec/J8ChipsK_*`, `Exec/J9AChipsK_*`, `Exec/J9ALChipsK_alu`), each tied to its table specification by a kernel theorem (`tie_*`, e.g. `tie_walkJ8_3`). The `_B` headlines hold for every loaded instance and carry `chipsOkF ... = true` in what they use (`hops9L_of_chips`), so nothing is assumed about the chip files, `Json.parse` or the chip loader (`verify-cert` parses them with the pure `Cert.chipOfJson`, inside `parseInputs`): the only trust is the compiled gate (rows 2-3). The chip files of the shipped fixtures all pass it (verify ACCEPT). Not covered (completeness, not soundness): an honestly emitted chip with no literal, e.g. a table size not in the list, is rejected; there is no generic emitter-correctness theorem. The phrase "chip files trusted" in the headline docstrings means exactly this |
| 8 | verification key | **R** (`verify --vk`); T (reproducible) for `verify-online` | `verify --vk` recomputes the VK with `setupData'` from the loaded instance (the same deterministic function `vk-setup` runs: fixed columns plus a Tip5 Merkle root, no randomness, no secret) and rejects unless the vk file's root equals it. `verdict9LVS_sound` / `verdict9LJVS_sound` (kernel) show the executed online check is then `verifyOnline'` at the honest VK `(mkVKData' XI hFixT).vk`, which is the headline's `vkSide` with the side oracle at the executable's Tip5 (`vkSide_eq`, `rfl`; row 9). `verify-online` loads only the stripped public instance and cannot recompute: there the VK is trusted as the indexer's output, reproducible by re-running `index` / `vk-setup` and comparing. `verify-online` (and `verify` without `--vk`) print `ACCEPT-UNCOVERED`: no end-to-end theorem covers their accept |
| 9 | random-oracle model | T | Fiat–Shamir and Tip5 are modelled as random oracles; the Tip5 in the executable is the package's own copy, with no equivalence theorem to any deployed hash |
| 10 | per-instance bounds | T (statement) | query budgets, table sizes and the named hypotheses `hnum`, `hTb`; the bound `2^-82 + (bfriErr + mcROM + coll)` holds only within them |
| 11 | non-adaptive scope | T (scope) | non-adaptive theorem; statement-binding verifier. The `j9al` and `j9alj` verdicts bind the full public input into the Fiat–Shamir transcript (the jet-free `j9a` path does not, `SPEC.md` §9.3) (a proof verifies only for the public input it was produced for), but the kernel-checked theorem is stated for a public input fixed before the oracle ("for every fixed file"), not chosen after querying |
| 12 | datum and statement side conditions | **K** via the gate | discharged for the executed instances by kernel-checked witness theorems |

### Gaps (not claimed)

- **Template jets.** The `j9al` path rejects instances with a template-jet table. The `j9alj` path and `nock_e2e_J9ALJ_succinct_B` cover template jets for the fixed catalogue `catJ` only; a new jet needs a new catalogue, a new kernel proof and a new verification key.
- **Zero-knowledge.** The prover is Reed-Solomon plus FRI with no masking. Soundness holds; the witness is not hidden.
- **Adaptive adversaries.** The executable absorbs the public input into the transcript; the adaptive bound is not proved, and the kernel-checked theorems are non-adaptive.
- **Cost clause.** Only the jet-free twin has one: `nock_e2e_J9A_succinct_SC` (`J9A/E2ESuccinctCost.lean:67`) is the statement of `nock_e2e_J9A_succinct` together with `costModel ≤ 6000·S⁶` for the accepted run; `nock_e2e_J9A_succinct` itself and the J-9 AL headlines have no cost clause.
- **Completeness.** Completeness of the compiled protocol in the random-oracle experiment is not an end-to-end theorem.
- **Table restriction.** Not a gap of the headlines, listed for completeness: The release headlines construct the table restriction at the loaded instance's tables (`J9AL/InstJ9ALW.lean::RJ9AL`, via `TabRestr.ofSigma`). The gate-form theorem `exec_e2e_J9ALV` takes it as a binder, pinned by its hypotheses to those tables up to the order of the constraint enumeration.
- **Tip5.** No theorem equates the executable's Tip5 with a deployed implementation.
- **Query positions.** The executable derives each query position by reducing a Tip5 output in `[0, p)` modulo `2^nD`; the theorems sample positions exactly uniformly. Since `p ≡ 1 (mod 2^nD)`, each position is within statistical distance `2^-64` of uniform; no theorem bounds the effect of this gap on the soundness error.
- **Underlying library.** The NockVM library's own trusted base (executable checkers, the Lean compiler, build-time receipts) applies as stated in its documentation.

