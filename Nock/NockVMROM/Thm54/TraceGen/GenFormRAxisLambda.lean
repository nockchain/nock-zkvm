/-
  Nock/NockVMROM/Thm54/TraceGen/GenFormRAxisLambda.lean

  **The Form R axis-leaf bound `FormRAxisBound` is λ-independent.**

  `OptimizedComputeFinalTrace.FormRAxisBound A b` reads, at every compute row `i`, only
  `axisLeafCoord A b i` and `axisLeafK A i`.  Both read the encoded row's base (only its state)
  and the formula-decomposition extension roles `41` / `44`
  (`coreExtensionValue … ⟨41,_⟩ = decFingerprint dec 1` coordinate `2`, `⟨44,_⟩ =
  decFingerprint dec 2` coordinate `2`; `OptimizedComputeCodec.encodeExtension`).  The sampled
  overlay (`OptimizedComputeSampledTrace.overlayAt`, which does read `cfg.challenges.lam` in its
  Form R denominators and `ioAcc`) writes only `.inl` columns, so it is never read here.  Hence
  the bound is a property of the problem's compute rows alone (`formRAxisBound_iff_rows`), and
  compute rows specialize at `α` alone (`ExactExecutionTemplate.specialize_computeRows`).
-/
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.NockVMROM.Thm54.TraceGen.GenBuildableAssembly
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.TraceGen.GenGenericAxisRange
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenFormRAxisLambda
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

open Classical
open Nock Nock.Walk
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Row-level axis leaf coordinate (the value `axisLeafCoord` reads at a row). -/
def rowAxisLeafCoord (b : Basis (Fin 3) F K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Option F :=
  match row.2.2.1.state with
  | .s0 => some (coord b (fpCoordinate (decFingerprint row.2.2.2 1) 2) 0)
  | .s9 => some (coord b (fpCoordinate (decFingerprint row.2.2.2 2) 2) 0)
  | _ => none

/-- Row-level `𝕂` axis leaf (the value `axisLeafK` reads at a row). -/
def rowAxisLeafK (row : ComputeTable.State × ComputeTable.DTcomp K) : K :=
  match row.2.2.1.state with
  | .s0 => fpCoordinate (decFingerprint row.2.2.2 1) 2
  | .s9 => fpCoordinate (decFingerprint row.2.2.2 2) 2
  | _ => 0

/-- **The λ-free object.**  `FormRAxisBound` stated on a list of compute rows. -/
def RowsFormRAxisBound (b : Basis (Fin 3) F K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) : Prop :=
  ∀ row ∈ rows, ∀ L : F, rowAxisLeafCoord b row = some L →
    ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ a < 2 ^ 64 ∧ (a : F) = L ∧
      ((a : ℕ) : K) = rowAxisLeafK row

variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

theorem axisLeafCoord_eq_row (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (i : Fin R.problem.cfg.compRows) :
    axisLeafCoord A b i = rowAxisLeafCoord b (R.problem.exec.computeRowAt i) := by
  unfold axisLeafCoord rowAxisLeafCoord
  simp only [OptimizedComputeSampledTrace.encodedRowAt, OptimizedComputeOverlay.sampledEncode,
    decodeState_encodeBase]
  rfl

theorem axisLeafK_eq_row (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    axisLeafK A i = rowAxisLeafK (R.problem.exec.computeRowAt i) := by
  unfold axisLeafK rowAxisLeafK
  simp only [OptimizedComputeSampledTrace.encodedRowAt, OptimizedComputeOverlay.sampledEncode,
    decodeState_encodeBase]
  rfl

/-- **`FormRAxisBound` reads the compute rows only.** -/
theorem formRAxisBound_iff_rows (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) :
    FormRAxisBound A b ↔ RowsFormRAxisBound b R.problem.exec.computeRows := by
  constructor
  · intro h row hrow L hL
    obtain ⟨j, hj⟩ := List.get_of_mem hrow
    let i : Fin R.problem.cfg.compRows := Fin.cast R.problem.exec.computeRows_length j
    have hi : R.problem.exec.computeRowAt i = row := by
      rw [← hj]; rfl
    have hc : axisLeafCoord A b i = some L := by rw [axisLeafCoord_eq_row, hi]; exact hL
    obtain ⟨a, h0, hp, h64, hL', hK⟩ := h i L hc
    exact ⟨a, h0, hp, h64, hL', by rw [hK, axisLeafK_eq_row, hi]⟩
  · intro h i L hL
    rw [axisLeafCoord_eq_row] at hL
    have hmem : R.problem.exec.computeRowAt i ∈ R.problem.exec.computeRows := List.get_mem _ _
    obtain ⟨a, h0, hp, h64, hL', hK⟩ := h _ hmem L hL
    exact ⟨a, h0, hp, h64, hL', by rw [hK, axisLeafK_eq_row]⟩

/-- **λ-irrelevance, general form.**  Two assignments over problems with the same compute rows
satisfy the same Form R axis bound, whatever their configurations' `λ`. -/
theorem formRAxisBound_congr_rows {R₁ R₂ : PlusIOSegmentedFamily F K}
    (A₁ : SampledIOSameExecutionAssignment R₁ p) (A₂ : SampledIOSameExecutionAssignment R₂ p)
    (b : Basis (Fin 3) F K)
    (h : R₁.problem.exec.computeRows = R₂.problem.exec.computeRows) :
    FormRAxisBound A₁ b ↔ FormRAxisBound A₂ b := by
  rw [formRAxisBound_iff_rows, formRAxisBound_iff_rows, h]

open Nock.NockVMROM.Thm54.SemanticTimestampStrategy in
/-- **λ-irrelevance over a template.**  If the two problems are the template's specializations at
`(α, λ₁)` and `(α, λ₂)` (compute rows: `E.specialize_computeRows`, which reads `α` only), the
Form R axis bound holds at one iff at the other. -/
theorem formRAxisBound_specialize_lambda_irrel {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (α lmb₁ lmb₂ : K)
    {R₁ R₂ : PlusIOSegmentedFamily F K}
    (A₁ : SampledIOSameExecutionAssignment R₁ p) (A₂ : SampledIOSameExecutionAssignment R₂ p)
    (b : Basis (Fin 3) F K)
    (h₁ : R₁.problem.exec.computeRows = (E.specialize α lmb₁).computeRows)
    (h₂ : R₂.problem.exec.computeRows = (E.specialize α lmb₂).computeRows) :
    FormRAxisBound A₁ b ↔ FormRAxisBound A₂ b :=
  formRAxisBound_congr_rows A₁ A₂ b (by
    rw [h₁, h₂, ExactExecutionTemplate.specialize_computeRows,
      ExactExecutionTemplate.specialize_computeRows])

section Package

variable [Fintype F] [DecidableEq F] [CharP K (ringChar K)]
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage

/-- **At a built package**, `FormRAxisBound` of the package's sampled assignment is the λ-free
row bound on the carrier's compute rows, at the inputs' basis. -/
theorem buildFullPackage_formRAxisBound_iff
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    {hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ}
    {hF : GeneratedField.PrimeFieldElems F} :
    FormRAxisBound (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis ↔
      RowsFormRAxisBound I.basis E.exec.computeRows :=
  formRAxisBound_iff_rows _ _

end Package

section Generated

/-- The generated carrier's compute rows: `genComputeRows z α t` with the coins set, and no `λ`
(the challenge vector `chal`, and so `chal.lam`, does not occur on the right). -/
theorem genBuildableOfProgram_exec_computeRows {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤
      2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K} :
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.computeRows =
      (bfsRows (genComputeRows z α t)).map (fun g => setRowCoins a b c g.row) :=
  genExactExecution_computeRows (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem

end Generated

/-! ## `hax` discharged on the generated rows

Every generated `s0` row's committed axis leaf is `encC z (atom ax)`'s leaf, i.e. `(ax : 𝕂)`, with
`1 ≤ ax` (the served lookup succeeded, `NodeAxisInFormula`) and `ax < q` (the formula is
`q`-bounded, `axisRange_of_axisInFormula`); `s9` reads the formula-tail head the same way.  With
`q = ringChar F < 2^64` and a basis extending `{1}` (`FormRBasis`), this is `RowsFormRAxisBound`. -/

section Discharge

theorem encC_atom_leaf (z : K) (a : ℕ) : (encC z (.atom a)).leaf = (a : K) := by
  simp [encC, NPR.leafF, Noun.leafList, hornerLE]

theorem coord_natCast_of_formRBasis {b : Basis (Fin 3) F K} (hb : FormRBasis b) (n : ℕ) :
    coord b ((n : ℕ) : K) 0 = (n : F) := by
  have hsmul : ((n : ℕ) : K) = (n : F) • (1 : K) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 := hb.1
  unfold coord at h1 ⊢
  rw [hsmul, map_smul, Finsupp.smul_apply, smul_eq_mul, h1, mul_one]

/-- **`hax`, discharged.**  For every program the generator accepts on `q`-bounded subject and
formula with a successful guarded run, at `q = ringChar F < 2^64` and a basis extending `{1}`, the
generated compute rows (at any seed, `α` and coins) satisfy the Form R axis bound. -/
theorem genComputeRows_rowsFormRAxisBound {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hqF : q = ringChar F) (hq64 : q < 2 ^ 64)
    {b : Basis (Fin 3) F K} (hb : FormRBasis b) (z α a' b' c' : K) :
    RowsFormRAxisBound b
      ((bfsRows (genComputeRows z α t)).map (fun g => setRowCoins a' b' c' g.row)) := by
  intro row hrow L hL
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hrow
  unfold genComputeRows at hg
  rw [bfsRows_renderRows] at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  unfold bfsRows at hg0
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg0
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hr
  subst hr
  have hshape := genComputeSkeleton_assigned_inTree_axisInFormula h n hin
  have hrange := axisRange_of_axisInFormula hshape
    (genComputeSkeleton_assigned_inTree_bounded hq hs hf hG h n hin).1
  set g := n.label with hgdef
  have hK : ∀ row' : ComputeTable.State × ComputeTable.DTcomp K,
      rowAxisLeafK (setRowCoins a' b' c' row') = rowAxisLeafK row' := fun _ => rfl
  have hC : ∀ row' : ComputeTable.State × ComputeTable.DTcomp K,
      rowAxisLeafCoord b (setRowCoins a' b' c' row') = rowAxisLeafCoord b row' := fun _ => rfl
  rw [hC] at hL
  rw [hK]
  by_cases h0 : g.skel.state = .s0
  · obtain ⟨hs0, hft⟩ := renderNode_row_s0 z α g h0
    obtain ⟨hd, hfm⟩ := hshape.1 h0
    have hpos := hshape.2.2.1 h0
    have hlt := hrange.1 h0
    set ax := P8Census.skeletonMemoryAxis g.skel 1
    have hleaf : fpCoordinate (decFingerprint (renderNode z α g).row.2.2.2 1) 2 = (ax : K) := by
      show (renderNode z α g).row.2.2.2.f_t.leaf = _
      rw [hft, hfm]
      exact encC_atom_leaf z ax
    simp only [rowAxisLeafCoord, hs0, hleaf, coord_natCast_of_formRBasis hb] at hL
    refine ⟨ax, hpos, hqF ▸ hlt, lt_trans hlt hq64, Option.some_injective _ hL, ?_⟩
    simp only [rowAxisLeafK, hs0, hleaf]
  by_cases h9 : g.skel.state = .s9
  · obtain ⟨hs9, hfth⟩ := renderNode_row_s9 z α g h9
    obtain ⟨hd, tt, hfm⟩ := hshape.2.1 h9
    have hpos := hshape.2.2.2 h9
    have hlt := hrange.2 h9
    set ax := P8Census.skeletonMemoryAxis g.skel 2
    have hleaf : fpCoordinate (decFingerprint (renderNode z α g).row.2.2.2 2) 2 = (ax : K) := by
      show (renderNode z α g).row.2.2.2.f_th.leaf = _
      rw [hfth, hfm]
      exact encC_atom_leaf z ax
    simp only [rowAxisLeafCoord, hs9, hleaf, coord_natCast_of_formRBasis hb] at hL
    refine ⟨ax, hpos, hqF ▸ hlt, lt_trans hlt hq64, Option.some_injective _ hL, ?_⟩
    simp only [rowAxisLeafK, hs9, hleaf]
  · exfalso
    have hst := renderNode_row_state z α g
    unfold rowAxisLeafCoord at hL
    revert hL
    rw [hst]
    cases hc : g.skel.state <;> simp_all

/-- **`FormRWidth` is a lemma**, not a premise: `3 < p` and `p < 2^64` give
`Nat.size p ≤ 64`, `0 < Nat.size p` and `3 < p`. -/
theorem FormRWidth_of_hp64 {F' : Type*} [Field F'] (h3 : 3 < ringChar F')
    (hp64 : ringChar F' < 2 ^ 64) : FormRWidth F' :=
  ⟨Nat.size_le.2 hp64, Nat.size_pos.2 (by omega), h3⟩

end Discharge

end

end Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.formRAxisBound_iff_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.formRAxisBound_specialize_lambda_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.FormRWidth_of_hp64
