/-
the ungrindability definition over the succinct protocol `sRounds`
of `Succ/Statement.lean`, and the restated uniqueness slot.

**Definition**. `proj z p := (x, c₁, …, c_k)`: the statement together with the round-0 message
and EVERY commitment the prover sent before the final message (the final message — openings — is dropped).
A non-interactive argument `(V, proj)` is `ε_uniq`-ungrindable if for every adversary with ≤ Q fresh
random-oracle keys
  Pr[ A → (x, π, π′) : V(x,π) = V(x,π′) = 1 ∧ proj(x,π) ≠ proj(x,π′) ] ≤ ε_uniq(Q).

**Modelling.** QD's `SingleSaltAdversary` outputs one proof; its `Witness` type is free, so a two-proof
adversary is a `SingleSaltAdversary Statement GlobalSalt (SaltedProof GlobalSalt sRounds)` whose witness
is the second proof `π′ = (salt′, messages′)` for the SAME statement `x` (the salt may differ: the salt
is the FS nonce). `twoAcceptExecution` is QD's `singleSaltExecution` (which FS-verifies π with the public
stopped verifier) followed by the same public stopped verification of π′ — a new definition from QD's pieces,
no QD or `Succ` statement is changed. Acceptance of both is `sAccept` (the pure terminal check) on both
paths. The query bound is the one of `rap_succinct_sound` (fresh keys of the adversary phase).
-/
import NockvmE2E.Succ.Statement

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Ung

open NockvmE2E.Rap NockvmE2E.Succ

section Defs

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)

/-- **The projection**: round-0 message (the statement's public part) and every commitment of the path.
The key's statement component `x` is carried separately (it is equal on the two paths). -/
def proj (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) :
    R.M0 × Tr ι CS.Com :=
  (path.1, (sFinal R CS plan I0 I Ifin nb path).1)

/-- Two-proof adversary: the witness is the second proof (salt and messages) for the same statement. -/
abbrev TwoProofAdversary (Statement GlobalSalt : Type) :=
  SingleSaltAdversary Statement GlobalSalt (SaltedProof GlobalSalt (sRounds R CS plan I0 I Ifin nb))
    (sRounds R CS plan I0 I Ifin nb)

variable {Statement GlobalSalt : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- **The two-acceptance experiment**: QD's `singleSaltExecution` for π, then the public stopped FS
verification of π′ against the same lazy random oracle. Returns the two (FS-verified) paths. -/
noncomputable def twoAcceptExecution
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) :
    OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
      (Option (((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) ×
        ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath))) := do
  let r ← singleSaltExecution (sRounds R CS plan I0 I Ifin nb) guards adversary
  match r.1 with
  | none => pure none
  | some (z, p, (salt', msgs')) =>
      let p' ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
        (publicStoppedVerify (sRounds R CS plan I0 I Ifin nb) guards (z.1, salt') msgs')
      pure (p'.map fun q => ((z, p), ((z.1, salt'), q)))

/-- **`TwoAcceptDistinctProj`**: both proofs pass FS verification and the terminal check `sAccept` on the
same statement, and their projections differ. -/
def TwoAcceptDistinctProj
    (res : Option (((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) ×
      ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath))) : Prop :=
  ∃ z p z' p', res = some ((z, p), (z', p')) ∧ z.1 = z'.1 ∧
    sAccept R CS plan I0 I Ifin nb z p = true ∧ sAccept R CS plan I0 I Ifin nb z' p' = true ∧
    proj R CS plan I0 I Ifin nb p ≠ proj R CS plan I0 I Ifin nb p'

/-- **ε_uniq-ungrindability** of the succinct argument `(sAccept, proj)` for the FS guards `guards`:
every two-proof adversary with ≤ Q fresh keys produces two accepted proofs with distinct projections
with probability ≤ `ε Q`. -/
def Ungrindable
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) (Q : ℕ),
    (∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) →
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
        TwoAcceptDistinctProj R CS plan I0 I Ifin nb joint.1.1] ≤ ε Q

/-- Ungrindability is monotone in the bound. -/
theorem Ungrindable.mono
    {guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb)}
    {ε ε' : ℕ → ℝ≥0∞} (h : Ungrindable R CS plan I0 I Ifin nb guards ε) (hle : ∀ Q, ε Q ≤ ε' Q) :
    Ungrindable R CS plan I0 I Ifin nb guards ε' :=
  fun adv Q hQ => (h adv Q hQ).trans (hle Q)

/-! ### The restated uniqueness slot as an event of the composed experiment -/

/-- The uniqueness failure on two accepted paths, for a `UniqueCommitment` instance: some commitment pair
is in `Collide`, or the final openings of the two paths are two different accepted proofs of the same
claims (`CollidePf`). -/
def UniqFailAt [UC : UniqueCommitment β O (CS := CS)]
    (p p' : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  (∃ j, UC.Collide ((sFinal R CS plan I0 I Ifin nb p).1 j) ((sFinal R CS plan I0 I Ifin nb p').1 j)) ∨
  ((sFinal R CS plan I0 I Ifin nb p).1 = (sFinal R CS plan I0 I Ifin nb p').1 ∧
   plan.claims p.1 (sFinal R CS plan I0 I Ifin nb p).2.2 (sFinal R CS plan I0 I Ifin nb p).2.1 =
     plan.claims p'.1 (sFinal R CS plan I0 I Ifin nb p').2.2 (sFinal R CS plan I0 I Ifin nb p').2.1 ∧
   UC.CollidePf (sFinal R CS plan I0 I Ifin nb p).1
     (plan.claims p.1 (sFinal R CS plan I0 I Ifin nb p).2.2 (sFinal R CS plan I0 I Ifin nb p).2.1)
     (plan.pf (sFinal R CS plan I0 I Ifin nb p).2.2) (plan.pf (sFinal R CS plan I0 I Ifin nb p').2.2))

/-- **`HUniq`** (the hypothesis `huniq` of the future `rap_succinct_unique`, the analogue of `hCS`): the
probability that the composed experiment yields two accepted paths with a `Collide`/`CollidePf` event is
≤ `εuniq`. -/
def HUniq [UniqueCommitment β O (CS := CS)]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) (εuniq : ℝ≥0∞) : Prop :=
  Pr{let joint ← (randomOracleLoggedRun
      (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
      ∃ z p z' p', joint.1.1 = some ((z, p), (z', p')) ∧
        sAccept R CS plan I0 I Ifin nb z p = true ∧ sAccept R CS plan I0 I Ifin nb z' p' = true ∧
        UniqFailAt R CS plan I0 I Ifin nb p p'] ≤ εuniq

end Defs

/-! ### The one instance: the IOP form -/

/-- `iopCS` (the commitment IS the data, trivial proofs) is a unique commitment with `Collide = CollidePf = False`
(the first field is `ext = id`, the second is `Unit`-valued). -/
def iopUnique {β : Type} (O : OracleInterface β) : UniqueCommitment β O (CS := iopCS O) :=
  @UniqueCommitment.mk β O (iopCS O) (fun _ _ => False) (fun _ _ h => Or.inl h)
    (fun _ _ _ _ => False) (fun _ _ π π' _ _ => Or.inl (Unit.ext (x := π) (y := π')))

end NockvmE2E.Ung
