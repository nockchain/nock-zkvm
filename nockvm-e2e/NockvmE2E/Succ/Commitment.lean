/-
SUCC-0, part 1: the commitment slot of `rap_succinct_sound`.

The opening relation is ArkLib's functional-commitment one (`ArkLib/Commitments/Functional/Basic.lean`):
committed data `β` with an `OracleInterface β` (the "function": query → response; for a univariate column
`evalOI toPoly`, query = point, response = value, `Succ/ArkLib.lean`; for Hachi, ArkLib's
`multilinearEvalOracleInterface`). A claim is `(column, query, response)`; `SatClaims O tr cl` is ArkLib's
consistency `O.answer d q = r` for every claim. The extractability failure `ExtFail` is ArkLib's
`extractabilityExperiment` condition `accept ∧ O.answer (E cm) q ≠ r`, batched over the claims.

This is a THIN slot, not ArkLib's `Commitment.Scheme` itself (see `Succ/ArkLib.lean` and the report for
why): commitments and openings are pure (the composed Fiat–Shamir experiment supplies all randomness),
openings are batched over many columns and queries, and the extractor reads the commitment only
(ArkLib's `StraightlineExtractor` also reads the commit-phase query log). `ε_CS` is NOT a field: it is a
bound on `Pr[accepted ∧ ExtFail]` in the composed experiment (hypothesis `hCS` of `rap_succinct_sound`).
`PerfectlyExtractable` is the error-free case (`ε_CS = 0`).
-/
import ArkLib.OracleReduction.OracleInterface

set_option autoImplicit false

namespace NockvmE2E.Succ

/-- ArkLib's oracle answer, with the interface passed explicitly. -/
abbrev ans {β : Type} (O : OracleInterface β) (b : β) (q : O.Query) : @OracleInterface.Response β O q :=
  @OracleInterface.answer β O b q

/-- Claims on an `ι`-tuple of committed data: `(column, query, response)`. -/
abbrev Claims {β : Type} (O : OracleInterface β) (ι : Type) :=
  List (ι × (q : O.Query) × @OracleInterface.Response β O q)

/-- A tuple satisfies the claims (ArkLib's `O.answer d q = r`, for every claim). -/
def SatClaims {β ι : Type} (O : OracleInterface β) (tr : ι → β) (cl : Claims O ι) : Prop :=
  ∀ c ∈ cl, ans O (tr c.1) c.2.1 = c.2.2

/-- **The commitment slot** (per column, batched oracle openings, straight-line extractor). A typeclass
a concrete scheme (DEEP + FRI + Merkle, a lattice PCS) plugs in as an instance on its data
type and oracle interface; `iopCS` below is a `def` so that it does not shadow them. -/
class CommitScheme (β : Type) (O : OracleInterface β) where
  /-- Commitments (what the prover sends instead of a column). -/
  Com : Type
  /-- Opening proofs (for a batch of claims on a committed tuple). -/
  Pf : Type
  /-- Honest commitment. -/
  commit : β → Com
  /-- The extractor: a function of the commitment alone. -/
  ext : Com → β
  /-- Binding on honest commitments. -/
  ext_commit : ∀ b, ext (commit b) = b
  /-- Honest opening. -/
  prove : {ι : Type} → (ι → β) → Claims O ι → Pf
  /-- The verifier's opening check. -/
  verify : {ι : Type} → (ι → Com) → Claims O ι → Pf → Prop
  /-- Opening completeness: true claims on honestly committed columns verify. -/
  complete : ∀ {ι : Type} (tr : ι → β) (cl : Claims O ι),
    SatClaims O tr cl → verify (fun j => commit (tr j)) cl (prove tr cl)

variable {β : Type} {O : OracleInterface β}

/-- The extraction failure event: an accepted opening whose claims the extracted tuple violates. -/
def CommitScheme.ExtFail (CS : CommitScheme β O) {ι : Type} (coms : ι → CS.Com)
    (cl : Claims O ι) (π : CS.Pf) : Prop :=
  CS.verify coms cl π ∧ ¬ SatClaims O (fun j => CS.ext (coms j)) cl

/-- Error-free extractability: every accepted opening is satisfied by the extracted tuple. -/
def CommitScheme.PerfectlyExtractable (CS : CommitScheme β O) : Prop :=
  ∀ {ι : Type} (coms : ι → CS.Com) (cl : Claims O ι) (π : CS.Pf),
    CS.verify coms cl π → SatClaims O (fun j => CS.ext (coms j)) cl

theorem CommitScheme.not_extFail {CS : CommitScheme β O} (h : CS.PerfectlyExtractable)
    {ι : Type} (coms : ι → CS.Com) (cl : Claims O ι) (π : CS.Pf) : ¬ CS.ExtFail coms cl π :=
  fun hf => hf.2 (h coms cl π hf.1)

/-- **The IOP instance ("honest oracle access")**: the commitment IS the data (the verifier has oracle
access to it), the proof is trivial, the check is the claim itself. `ε_CS = 0`. -/
abbrev iopCS (O : OracleInterface β) : CommitScheme β O where
  Com := β
  Pf := Unit
  commit := id
  ext := id
  ext_commit _ := rfl
  prove _ _ := ()
  verify coms cl _ := SatClaims O coms cl
  complete _ _ h := h

theorem iopCS_perfect (O : OracleInterface β) : (iopCS O).PerfectlyExtractable := fun _ _ _ h => h

/-- **Optional uniqueness / non-malleability slot** (restated for ungrindability).
Two fields only; there is NO `εuniq` field. `Collide` / `CollidePf` are predicates on the commitments / proofs
that occur on two accepted paths; the probability that two accepted paths of the composed single-salt experiment
have `Collide`/`CollidePf` events is a HYPOTHESIS of the end-to-end theorem (`Ung/Defs.lean`: `UniqFailAt`,
`HUniq`), exactly like `ε_CS` / `hCS` for extraction. DEFINED ONLY — no instance except `iopCS` (`Ung/Defs.lean`).
* `unique_com`: the extracted data determines the commitment, except on `Collide`;
* `unique_pf`: two accepting openings of the same commitments and claims are equal, except on `CollidePf`.
For Merkle-over-words with succinct proximity testing, `unique_com` is FALSE for every `Collide` of
negligible probability (`Ung/MerkleNegative.lean`). -/
class UniqueCommitment (β : Type) (O : OracleInterface β) [CS : CommitScheme β O] where
  Collide : CS.Com → CS.Com → Prop
  unique_com : ∀ c c' : CS.Com, CS.ext c = CS.ext c' → c = c' ∨ Collide c c'
  CollidePf : {ι : Type} → (ι → CS.Com) → Claims O ι → CS.Pf → CS.Pf → Prop
  unique_pf : ∀ {ι : Type} (coms : ι → CS.Com) (cl : Claims O ι) (π π' : CS.Pf),
    CS.verify coms cl π → CS.verify coms cl π' → π = π' ∨ CollidePf coms cl π π'

end NockvmE2E.Succ
