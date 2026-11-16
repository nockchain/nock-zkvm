import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.VclL.Compute.RootBindsVCL

/-!
`CoordGather F K` abstracts what the VCL decoders read
of a physical row: the `Env309 F K` decode and the `K`-valued challenge / public slot readers.
`ChipDataG` is `ChipData` with the basis replaced by a gather; `ChipData.toG` is the 3-limb bridge
(also registered as a coercion, so the 3-limb statements are the generic ones at `D.toG`).
`oneHot_of_base15G` is `oneHot_of_base15` at any gather.  The generic row-index helpers
`firstRowG`, `lastRowG`, `rowOfG` mirror `SVCompute.firstRowD` / `lastRowD` / `rowOfD` (which read only `N`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace WalkQ7

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.ComputeTable Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.DeployedComputeRows Nock.NockVMROM.Thm54.VclL.Compute.LnRead

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-- The `K` value of limbs `3q..3q+2` of a raw vector. -/
def slotK {F K : Type} [Field F] [Field K] [Algebra F K] (b : Basis (Fin 3) F K) (v : ℕ → F) (q : ℕ) : K :=
  ∑ k : Fin 3, v (3 * q + (k : ℕ)) • b k

/-- **The abstract coordinate gather**: the `Env309` decode of a physical row and the `𝕂`-valued
challenge / public slot readers, with the laws the decoders use. -/
structure CoordGather (F K : Type) [Field F] [Field K] [Algebra F K] where
  env309 : Env F → Env309 F K
  chalSlot : (ℕ → F) → ℕ → K
  pubSlot : (ℕ → F) → ℕ → K
  chal_eq : ∀ (e : Env F) (i : Fin 12), (env309 e).base.chal i = chalSlot e.chal i
  pub_eq : ∀ (e : Env F) (i : Fin 3), (env309 e).base.extensionPublic i = pubSlot e.pub i
  /-- the base columns are the raw `F` trace -/
  base_eq : ∀ (e : Env F) (i : Fin 13), (env309 e).base.baseTrace i = e.trace i
  baseNext_eq : ∀ (e : Env F) (i : Fin 13), (env309 e).base.baseTraceNext i = e.traceNext i
  /-- the compute exponent carrier is the raw `F` column `302` -/
  expCol_eq : ∀ (e : Env F), (env309 e).base.expCol = e.trace 302
  /-- the scalar publics are the raw `F` publics `20..41` -/
  scalarPublic_eq : ∀ (e : Env F) (i : Fin 22), (env309 e).base.scalarPublic i = e.pub (20 + (i : ℕ))
  /-- the gather commutes with shifting the trace to the next row -/
  shift : ∀ (e e' : Env F), (∀ c, e'.trace c = e.traceNext c) →
    (env309 e').base.extTrace = (env309 e).base.extTraceNext ∧ (env309 e').walk = (env309 e).walkNext

section Inst
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The 3-limb instance. -/
def CoordGather.ofBasis (b : Basis (Fin 3) F K) : CoordGather F K where
  env309 := gather309 b
  chalSlot := slotK b
  pubSlot := slotK b
  chal_eq _ _ := rfl
  pub_eq _ _ := rfl
  base_eq _ _ := rfl
  baseNext_eq _ _ := rfl
  expCol_eq _ := rfl
  scalarPublic_eq _ _ := rfl
  shift e e' h := by
    refine ⟨?_, ?_⟩ <;> funext j <;>
      simp [gather309, gatherCorrectedFinalTypedEnv, h]

theorem CoordGather.ofBasis_env309 (b : Basis (Fin 3) F K) (e : Env F) :
    (CoordGather.ofBasis b).env309 e = gather309 b e := rfl


/-- **The one-hot selector from the base gates**, at any gather (`oneHot_of_base15` generalized;
only the base-trace law is used). -/
theorem oneHot_of_base15G {F K : Type} [Field F] [Field K] [Algebra F K] (G : CoordGather F K)
    (n : ℕ) (envF : Env F)
    (hb : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    ∃ st : State, OneHotSelector (G.env309 envF).base.toSourceEnv st := by
  set env := (G.env309 envF).base
  have hbase : ∀ k : ℕ, (hk : k < 13) → env.baseTrace ⟨k, hk⟩ = envF.trace k :=
    fun k hk => G.base_eq envF ⟨k, hk⟩
  have hbool : ∀ (k : ℕ) (hk : k < 11),
      env.baseTrace ⟨k, by omega⟩ = 0 ∨ env.baseTrace ⟨k, by omega⟩ = 1 := by
    intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hsum : env.baseTrace ⟨0, by norm_num⟩ + env.baseTrace ⟨1, by norm_num⟩ +
      env.baseTrace ⟨2, by norm_num⟩ + env.baseTrace ⟨3, by norm_num⟩ +
      env.baseTrace ⟨4, by norm_num⟩ + env.baseTrace ⟨5, by norm_num⟩ +
      env.baseTrace ⟨6, by norm_num⟩ + env.baseTrace ⟨7, by norm_num⟩ +
      env.baseTrace ⟨8, by norm_num⟩ + env.baseTrace ⟨9, by norm_num⟩ +
      env.baseTrace ⟨10, by norm_num⟩ = 1 := by
    have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    rw [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega),
      hbase 4 (by omega), hbase 5 (by omega), hbase 6 (by omega), hbase 7 (by omega),
      hbase 8 (by omega), hbase 9 (by omega), hbase 10 (by omega)]
    linear_combination hg
  obtain ⟨s, hs⟩ : ∃ s, rowSelector env = Nock.ComputeTable.opSel s := by
    apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
    · intro st
      rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
      · left; simp [rowSelector, h]
      · right; simp [rowSelector, h]
    · have hK := congrArg (algebraMap F K) hsum
      simp only [map_add, map_one] at hK
      simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
      linear_combination hK
  refine ⟨s, fun t => ?_⟩
  have ht : env.toSourceEnv.trace (opCol t) = opSel s t := by
    rw [source_trace_base _ (opCol t) (by cases t <;> decide)]
    simpa [rowSelector] using congrFun hs t
  simpa [OneHotSelector, opSel] using ht

/-- The 3-limb statement is recovered. -/
theorem oneHot_of_base15_viaG {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F)
    (hb : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    ∃ st : State, OneHotSelector (gatherCorrectedFinalTypedEnv b envF).toSourceEnv st :=
  oneHot_of_base15G (CoordGather.ofBasis b) n envF hb hchar


/-- **The patched row of a Q7-obligated row is `V_comp`**, at any gather (`q7_obligations_vcomp`). -/
theorem q7_obligations_vcompG [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    (G : CoordGather F K) (n : ℕ) (envF : Env F)
    (h : VclSourceObligationsQ7 n (G.env309 envF) envF)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hzZ : (zZinvExpr.subst computeSubst).eval (G.env309 envF).base.toSourceEnv = 0) :
    VcompAt (lnPatch (G.env309 envF).base) := by
  obtain ⟨st, hone⟩ := oneHot_of_base15G G n envF h.base15 hchar
  exact vcompAt_of_rowLocal _ st (oneHot_lnPatch _ st hone)
    ((zZinv_lnPatch _).trans hzZ)
    (paperPackingRowLocal_eval_zero_of_core (env := lnPatch309 (G.env309 envF))
      (core_lt72_of_q7 h))

end Inst

/-- `ChipData` with the basis replaced by an abstract gather. -/
structure ChipDataG (F K : Type) [Field F] [Field K] [Algebra F K] (h : ℕ) where
  N : ℕ
  hN : 0 < N
  nodes : Fin N → F
  G : CoordGather F K
  orbit : StrictExtension.StrictOrbitDomain F 3 h
  claim : P8PublicClaim
  pub : ℕ → F
  chal : ℕ → F

/-- The 3-limb bridge. -/
def _root_.Nock.NockVMROM.Thm54.SVCompute.ChipData.toG {F K : Type} [Field F] [Field K] [Algebra F K]
    {h : ℕ} (D : SVCompute.ChipData F K h) : ChipDataG F K h :=
  ⟨D.N, D.hN, D.nodes, CoordGather.ofBasis D.basis, D.orbit, D.claim, D.pub, D.chal⟩

instance {F K : Type} [Field F] [Field K] [Algebra F K] {h : ℕ} :
    CoeOut (SVCompute.ChipData F K h) (ChipDataG F K h) := ⟨SVCompute.ChipData.toG⟩

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] {h : ℕ} (D : ChipDataG F K h)

/-- First row (`SVCompute.firstRowD`). -/
abbrev firstRowG : Fin D.N := ⟨0, D.hN⟩
/-- Last row (`SVCompute.lastRowD`). -/
abbrev lastRowG : Fin D.N := ⟨D.N - 1, Nat.sub_lt D.hN (by omega)⟩
/-- Row `i - 1` for `1 ≤ i ≤ D.N` (`SVCompute.rowOfD`). -/
def rowOfG (i : ℕ) : Fin D.N := if h : i - 1 < D.N then ⟨i - 1, h⟩ else firstRowG D

theorem rowOf_succG (k : ℕ) (hk : k < D.N) : rowOfG D (k + 1) = ⟨k, hk⟩ := by
  simp [rowOfG, hk]

theorem rowOf_oneG : rowOfG D 1 = firstRowG D := by
  rw [rowOf_succG D 0 D.hN]

theorem rowOf_rowsG : rowOfG D (D.N) = lastRowG D := by
  have hpos : 0 < D.N := D.hN
  have h : D.N - 1 < D.N := Nat.sub_lt hpos (by omega)
  apply Fin.ext
  simp [rowOfG, h]

/-- The row-adjacency premise (`ChipData.Adjacent`). -/
def ChipDataG.Adjacent : Prop :=
  ∀ (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N), D.nodes ⟨(i : ℕ) + 1, hi⟩ = D.orbit.ω * D.nodes i

/-- The row-injectivity premise (`ChipData.Injective`). -/
def ChipDataG.Injective : Prop := Function.Injective D.nodes

end Rows

end

end WalkQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
