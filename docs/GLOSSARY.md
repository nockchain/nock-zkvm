# Glossary

## Release labels

| label | descriptive name | specified in |
|---|---|---|
| J-8 | the base arithmetization of full Nock: atoms of any size in the computation, claim atoms `< p`, op-0 / op-10 axes `< p` | `SPEC.md` §3, §4 |
| J-9 B | J-8 with claim atoms of any size | `SPEC.md` §3.6, §4.1.3, §4.3.2 |
| J-9 A | J-9 B with op-0 / op-10 axes of up to 62 limbs of `2^32` (axis chip, split chip, twin compute chip) | `SPEC.md` §5 |
| J-9 AL | J-9 A with primitive jets (`add sub lt mul div mod` on big atoms) checked by an ALU chip | `SPEC.md` §6 |
| `j9alj` | J-9 AL with template jets from the fixed checked registry `catJ` (an end-to-end family, not a revision) | `SPEC.md` §9 |
| `j8`, `j9a`, `j9al`, `j9alj` | values of the executables' `--family` flag | `SPEC.md` §10 |
| REL-5.4 | the release this documentation describes | — |

## Name prefixes (opaque)

| name | meaning |
|---|---|
| `Nock.NockVMROM.Thm54` | namespace prefix of the library's main development |
| `VclL` | the memory design: validated cells keyed by content and round-0 serial, linked by LogUp |
| `Handle` | the compute chip refers to cells by handle (round-0 serial); `Handle.` abbreviates the namespace `Nock.NockVMROM.Thm54.VclL.Handle.` |
| `HQ`, `HQK`, `HQKW`, `HX`, `VCLHX` | chip revision suffixes; the chips in force are named in `SPEC.md` §3.3 |
| `Nock.RedTeam.BatchNNNN` | namespaces in modules `Nock.RedTeam.BatchNNNN<Suffix>`; the number is a sequence index |
| `P8` (`P8PublicClaim`) | the claim type `⟨subject, formula, result⟩` |
| `Z38` | the `nockvm-e2e` directory of the `j9alj` template-jet twins |
| `demo-candidate.sh`, `delivery-axioms.lean` | the library demo and the axioms script |

## Terms

| term | meaning |
|---|---|
| headline | a theorem listed in `THEOREMS.md`; the release headlines are `nock_e2e_J9AL_succinct_B` and `nock_e2e_J9ALJ_succinct_B` |
| base / `_B` / `_S` / gate form | the four forms of an end-to-end theorem, by the verdict their hypothesis names (`SPEC.md` §9.1) |
| covered accept | an executable's `ACCEPT` whose verdict is the hypothesis of an end-to-end theorem; other accepts print `ACCEPT-UNCOVERED` (`SPEC.md` §10.1) |
| primitive jet | a big-atom arithmetic operation registered at `primSpec` and checked by the ALU chip |
| template jet | a jet compiled from the template language (`Nock/Jet/Autogen.lean`) and checked by the J chip |
| `zBind` | the statement-binding gate: the Fiat–Shamir statement starts with the encoding of the public input (`SPEC.md` §9.3) |
| eps(Q) | the main-proof numbers term as a function of the Fiat–Shamir query budget, `rapFriEps_le_Q` (`SPEC.md` §9.4) |
