# CERTIFIED: the certified verifier (`nockvm-e2e-verify-cert`)

A kernel theorem states that the verifier's ACCEPT **on the bytes it reads** implies the conclusion of `nock_e2e_J9AL_succinct_S` /
`nock_e2e_J9ALJ_succinct_S` for the statement those bytes denote, so that, of the executable's code, only `main`'s file I/O, the Lean
compiler and runtime and the C toolchain are trusted; rows 1 and 9–11 of `../docs/LIMITS.md` (the kernel, the random-oracle model,
the bounds and the scope) still apply. Specification: `../docs/SPEC.md` §10.2.

## What sits between the bytes and the verdict in the `verify --family j9al|j9alj --vk ...` arms of `Exec/VerifyFamMain.lean`

| step | function | pure? | `partial`? |
|---|---|---|---|
| read file | `readJson` (IO) | no | no |
| bytes → JSON | `Lean.Json.parse` (core) | yes | core parser, `partial`/opaque to the kernel |
| chip file | `Tr.loadChip` (IO) → `Tr.parseEx` | IO + pure | `parseEx` is `partial` |
| instance | `FlatFam.loadInstF` → `FlatF.parseInstF` (+ `natE/limbE/natsE/k3E/pubInE`) | yes (the wrapper is IO) | no |
| proof / fix | `FlatProof.ofJson`, `natsE "z"`, `FixProof.ofJson` | yes | no |
| verdict | `verdict9LVS` / `verdict9LJVS` | yes | no (kernel theorems `verdict9LVS_sound`, `_S` corollaries) |

## Design: one pure function of the bytes

`Exec/CertBytes.lean`: `verifyBytesL` / `verifyBytesLJ : ByteArray (vk) → ByteArray (inst) → List ByteArray (chip documents) → ByteArray (proof) → ByteArray (fix) → Except String P8PublicClaim`,
`parseInputs` (bytes → `XI0, root, z, π, πF`; `String.fromUTF8?`, `Json.parse`, `parseInstF`, the `ofJson` decoders, `chipOfJson` = pure twin of `loadChip`),
then `verdict9LVS` / `verdict9LJVS` at the executable's Tip5 oracles. The chip documents are extra inputs because the instance names them by path (`chipPaths inst`
lists them; `main` reads them); they are untrusted: `chipsOkF` inside the verdict compares each with the family's Lean literal.
`Exec/VerifyCertMain.lean`: `main := print ∘ verifyReport ∘ readFiles` (`verifyReport` = family dispatch, `verifyBytes*`, one printed line; exit 0 iff ACCEPT).

**Soundness needs no parser correctness and no total twins.** `Exec/CertSound.lean`: `verifyBytesL_sound` / `verifyBytesLJ_sound`:
`verifyBytes* ... = .ok c → ∃ XI0 root z π πF, parseInputs ... = .ok (XI0,root,z,π,πF) ∧ verdict9LVS XI0 root ... = .ok c ∧ <conclusion of nock_e2e_J9AL(J)_succinct_S at XI0>`.
The proof is `verifyBytes*_spec` (unfold the `do`) plus the `_S` theorem, which quantifies over every `XI0/root/z/π/πF`. The partial/opaque parsers
(`Json.parse`, `parseEx`) are therefore irrelevant to the proof: whatever they return, the verdict was computed on it.

## What the statement says about the bytes

The instance the bytes parse to (`parseInputs`, a named function of the bytes) IS the statement: the headline is about `XI170 XI0`, and `c`, the claim printed
by the executable, is `d.c` for the datum linked to that instance's public input. A reader who wants "the bytes mean what I think" must read `parseInputs` (small,
all `Except`); a misparse changes which statement the ACCEPT is about; the soundness bound applies to that statement. Labels unchanged: non-adaptive, not zero-knowledge, RO model, `hnum`/`hTb` hypotheses.

## Trusted base

`main`'s file reads and `IO.println`/exit code; the Lean compiler and runtime (compiled `Decidable`/`verdict`); the C toolchain that compiles the emitted C. The kernel theorems use
`propext`, `Classical.choice`, `Quot.sound` only. Reproducible build: `scripts/build-certified.sh`.
