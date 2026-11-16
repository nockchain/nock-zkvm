import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

/-!
The builders (`BuildablePackage.buildFullPackageFromPins`, `buildFullPackage`,
`buildFullPackageWith`, `GenericHonestPackage.packageOf`) take them as the hypotheses
`hgenF : ClaimGenerated K claim Λ` and `hF : PrimeFieldElems F`.
-/

namespace Nock.NockVMROM.Thm54
namespace GeneratedField

open Nock Nock.Walk

def ClaimGenerated (K : Type) [Field K] (claim : P8PublicClaim) (Λ : ℕ) : Prop :=
  ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ) (r : Noun),
    TraceGen.genComputeSkeleton (K := K) gfuel claim.subject claim.formula = .ok (G, R) ∧
      FieldEmbedding.evalGBy (ringChar K) fuel claim.subject claim.formula = some r ∧
      TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ

def PrimeFieldElems (F : Type) [Field F] : Prop :=
  ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x

/-- `primeField` at `F = ZMod p` (the production twin of `Batch1250.hF_zmod`). -/
theorem primeFieldElems_zmod (p : ℕ) [Fact p.Prime] : PrimeFieldElems (ZMod p) := by
  intro x
  refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
  rw [ZMod.ringChar_zmod_n]
  exact ZMod.val_lt x

/-- `ClaimGenerated` from a generator run, a guarded run and the window, at the claim's nouns. -/
theorem claimGenerated_of_run {K : Type} [Field K] {claim : P8PublicClaim} {Λ : ℕ}
    {gfuel fuel : ℕ} {G : NTree (TraceGen.GenComputeRow K)} {R r : Noun}
    (hgen : TraceGen.genComputeSkeleton (K := K) gfuel claim.subject claim.formula = .ok (G, R))
    (hG : FieldEmbedding.evalGBy (ringChar K) fuel claim.subject claim.formula = some r)
    (hΛ : TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ) :
    ClaimGenerated K claim Λ :=
  ⟨gfuel, G, R, fuel, r, hgen, hG, hΛ⟩

/-- `ClaimGenerated` at a claim whose subject and formula are known nouns. -/
theorem claimGenerated_of_eq {K : Type} [Field K] {claim : P8PublicClaim} {Λ : ℕ} {s f : Noun}
    (hs : claim.subject = s) (hf : claim.formula = f)
    (h : ∃ (gfuel : ℕ) (G : NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ) (r : Noun),
      TraceGen.genComputeSkeleton (K := K) gfuel s f = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K) fuel s f = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ) :
    ClaimGenerated K claim Λ := by
  unfold ClaimGenerated
  rw [hs, hf]
  exact h

/-- Monotonicity in the window. -/
theorem ClaimGenerated.mono {K : Type} [Field K] {claim : P8PublicClaim} {Λ Λ' : ℕ}
    (h : ClaimGenerated K claim Λ) (hle : Λ ≤ Λ') : ClaimGenerated K claim Λ' := by
  obtain ⟨gfuel, G, R, fuel, r, h1, h2, h3⟩ := h
  exact ⟨gfuel, G, R, fuel, r, h1, h2, h3.trans hle⟩

/-! ## The fixture discharge (fixture census, verbatim) -/

theorem generated_of {K : Type} [Field K] (q : ℕ) (s f : Noun) (Λ gfuel fuel : ℕ)
    (hg : match TraceGen.genComputeSkeleton (K := K) gfuel s f with
      | .ok (G, _) => TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ
      | .error _ => False)
    (he : (FieldEmbedding.evalGBy q fuel s f).isSome) :
    ∃ (gfuel : ℕ) (G : NTree (TraceGen.GenComputeRow K)) (R : Noun) (fuel : ℕ) (r : Noun),
      TraceGen.genComputeSkeleton (K := K) gfuel s f = .ok (G, R) ∧
        FieldEmbedding.evalGBy q fuel s f = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ := by
  revert hg
  cases hx : TraceGen.genComputeSkeleton (K := K) gfuel s f with
  | error e => intro h; exact h.elim
  | ok p =>
    obtain ⟨G, R⟩ := p
    intro hg
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp he
    exact ⟨gfuel, G, R, fuel, r, hx, hr, hg⟩

/-- The exact leaf-bound value, as a match statement (no `∃`). -/
def LeafIs {K : Type} [Field K] (gfuel : ℕ) (s f : Noun) (n : ℕ) : Prop :=
  match TraceGen.genComputeSkeleton (K := K) gfuel s f with
  | .ok (G, _) => TraceGen.programLeafBound (TraceGen.airReorder G) = n
  | .error _ => False

theorem le_of_leafIs {K : Type} [Field K] {g : ℕ} {s f : Noun} {n Λ : ℕ}
    (h : LeafIs (K := K) g s f n) (hn : n ≤ Λ) :
    match TraceGen.genComputeSkeleton (K := K) g s f with
      | .ok (G, _) => TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ
      | .error _ => False := by
  unfold LeafIs at h
  revert h
  cases TraceGen.genComputeSkeleton (K := K) g s f with
  | error e => intro h; exact h.elim
  | ok p => obtain ⟨G, R⟩ := p; intro h; simpa [h] using hn

/-- Negative control: a bound strictly below the measured value is refuted. -/
theorem not_le_of_leafIs {K : Type} [Field K] {g : ℕ} {s f : Noun} {n Λ : ℕ}
    (h : LeafIs (K := K) g s f n) (hn : Λ < n) :
    ¬ (match TraceGen.genComputeSkeleton (K := K) g s f with
      | .ok (G, _) => TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ
      | .error _ => False) := by
  unfold LeafIs at h
  revert h
  cases TraceGen.genComputeSkeleton (K := K) g s f with
  | error e => intro h; exact h.elim
  | ok p => obtain ⟨G, R⟩ := p; intro h; simp [h]; omega

end GeneratedField
end Nock.NockVMROM.Thm54

macro "gen_simp" : tactic => `(tactic| simp [Nock.NockVMROM.Thm54.GeneratedField.LeafIs,
  Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton,
  Nock.NockVMROM.Thm54.TraceGen.programLeafBound, Nock.NockVMROM.Thm54.TraceGen.airReorder,
  Nock.NockVMROM.Thm54.TraceGen.airNeedsSwap, Nock.NockVMROM.Thm54.TraceGen.swapPair,
  Nock.NockVMROM.Thm54.TraceGen.bfsRows, Nock.Walk.bfsForest, Nock.Walk.NTree.children,
  Nock.Walk.NTree.label,
  Nock.NockVMROM.Thm54.TraceGen.rowNounsBound, Nock.NockVMROM.Thm54.TraceGen.skelNode,
  Nock.NockVMROM.Thm54.TraceGen.formulaOpcode,
  Nock.NockVMROM.Thm54.TraceGen.genSkelOp0, Nock.NockVMROM.Thm54.TraceGen.genSkelOp1,
  Nock.NockVMROM.Thm54.TraceGen.genSkelOp2, Nock.NockVMROM.Thm54.TraceGen.genSkelOp3,
  Nock.NockVMROM.Thm54.TraceGen.genSkelOp4, Nock.NockVMROM.Thm54.TraceGen.genSkelOp5,
  Nock.NockVMROM.Thm54.TraceGen.genSkelOp6, Nock.NockVMROM.Thm54.TraceGen.genSkelOp7,
  Nock.NockVMROM.Thm54.TraceGen.genSkelOp8, Nock.NockVMROM.Thm54.TraceGen.genSkelOp9,
  Nock.NockVMROM.Thm54.TraceGen.genSkelCons,
  Nock.Noun.leaves, Nock.Noun.slot, Nock.Noun.lus, Nock.Noun.tis, Nock.Noun.wut])

macro "eval_simp" : tactic => `(tactic| simp [Nock.FieldEmbedding.evalGBy,
  Nock.FieldEmbedding.lusGBy, Nock.Noun.slot, Nock.Noun.tis, Nock.Noun.wut])

/-- Default discharge of a builder's `hF : PrimeFieldElems F`: a hypothesis in scope, else
`F = ZMod p` at a prime `p`. -/
macro "prime_field_elems" : tactic => `(tactic| first
  | assumption
  | exact Nock.NockVMROM.Thm54.GeneratedField.primeFieldElems_zmod _)

set_option hygiene false in
/-- Default discharge of a builder's `hgenF : ClaimGenerated …`: a hypothesis in scope; else, at
the generated carrier (`TraceGen.genDataOfProgram`), the chain's own guarded run (`hG`, or the ROM
antecedent `hgrom` through `evalGRom_le_evalGBy`) by `TraceGen.genDataOfProgram_claimGenerated`.
Nothing else is tried: a hand-built fixture supplies its claim lemma explicitly.  (Unhygienic:
the chain lemmas are declared above this module and are resolved at the use site.) -/
macro "claim_generated" : tactic => `(tactic| first
  | assumption
  | exact Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_claimGenerated (by assumption)
  | exact Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_claimGenerated
      (Nock.NockVMROM.Thm54.TraceGen.evalGRom_le_evalGBy (by assumption))
  | exact Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_claimGeneratedD (by assumption)
  | exact Nock.NockVMROM.Thm54.TraceGen.genDataOfProgram_claimGeneratedD
      (Nock.NockVMROM.Thm54.TraceGen.evalGRom_le_evalGBy (by assumption))
  | fail "no `hgenF : ClaimGenerated …` in scope")
