/-
  Nock/RedTeam/Batch1060Thm54RepairIIMemoryReadSet.lean

`k2_unread` was `decide` at `ZMod 5` over
  `paperKGates` only. Here:

  * `mixedRawSlots col0 e g` over-approximates the raw challenge slots any coordinate of
    `mixedCompile b col0 g` reads; `chalSlots_mixedCompile_subset` is its soundness, by induction
    through `mulVec` / `powVec` (`Batch265.chalSlots_mulVec` / `chalSlots_powVec`).
  * `mixed_slots_decided` is the whole committed mixed bucket (`mixedTransitionGates b` =
    `paperKGates ++ [haltAtomMixed]`, 50 gates) evaluated by the kernel with `F`, `K`, `b` FREE
    (`rfl`: the gate bodies branch on no field value), so the fact is generic, not at `ZMod 5`.
  * `memory_allGates_off_slot2`: the template's other buckets are the coin-free base gates
    (`Batch357.paperBaseGates_chalSlots`, `readRootVerGate`) and three empty lists.
  * `namedFinalMemoryRAP_congr`: the RAP's only chalVal-dependent field is
    `C i := coeffToMv chalVal pubVal (gates.get i)` (`expandChipTail`), so
    `Batch265.coeffToMv_congr_of_chalSlots` gives chip EQUALITY, through an explicit constructor
    (`mkNamed`, `padNamed`) because the proof fields depend on the RAP.

  -- the paper
-/
import Nock.RedTeam.Batch265Thm54DeadChallenge36
import Nock.RedTeam.Batch357Thm54DeployedReadSet
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1060

open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.RedTeam.Batch265 (chalSlots chalSlots_mulVec chalSlots_powVec coeffToMv_congr_of_chalSlots)
open Module
open scoped Polynomial

section Instrument

variable {F : Type} [Field F]

/-- Raw challenge slots a mixed `𝕂` gate can reach once coordinate-compiled at `col0`, `e`. -/
def mixedRawSlots (col0 : VarKind → ℕ → ℕ) (e : ℕ) : MixedExpr F → List ℕ
  | .Var .challenge idx => (List.range e).map (fun k => col0 .challenge idx + k)
  | .Var .traceCur _ => []
  | .Var .traceNext _ => []
  | .Var .publicVal _ => []
  | .Lift g => chalSlots g
  | .Scale g u => chalSlots g ++ mixedRawSlots col0 e u
  | .Const _ => []
  | .Add x y => mixedRawSlots col0 e x ++ mixedRawSlots col0 e y
  | .Sub x y => mixedRawSlots col0 e x ++ mixedRawSlots col0 e y
  | .Neg x => mixedRawSlots col0 e x
  | .Mul x y => mixedRawSlots col0 e x ++ mixedRawSlots col0 e y
  | .Pow x _ => mixedRawSlots col0 e x

end Instrument

section Compiler

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Soundness of the instrument**: every raw slot a compiled coordinate reads is listed. -/
theorem chalSlots_mixedCompile_subset {e : ℕ} (b : Basis (Fin e) F K)
    (col0 : VarKind → ℕ → ℕ) :
    ∀ (g : MixedExpr F) (k : Fin e) (s : ℕ),
      s ∈ chalSlots (mixedCompile b col0 g k) → s ∈ mixedRawSlots col0 e g
  | .Var kind idx, k, s, hs => by
      cases kind <;> simp [mixedCompile, chalSlots, mixedRawSlots] at hs ⊢
      exact ⟨k, k.isLt, hs.symm⟩
  | .Lift g, k, s, hs => by
      simpa [mixedCompile, chalSlots, mixedRawSlots] using hs
  | .Scale g u, k, s, hs => by
      simp only [mixedCompile, chalSlots, List.mem_append, mixedRawSlots] at hs ⊢
      rcases hs with h | h
      · exact Or.inl h
      · exact Or.inr (chalSlots_mixedCompile_subset b col0 u k s h)
  | .Const _, k, s, hs => by
      simp [mixedCompile, chalSlots] at hs
  | .Add x y, k, s, hs => by
      simp only [mixedCompile, chalSlots, List.mem_append, mixedRawSlots] at hs ⊢
      rcases hs with h | h
      · exact Or.inl (chalSlots_mixedCompile_subset b col0 x k s h)
      · exact Or.inr (chalSlots_mixedCompile_subset b col0 y k s h)
  | .Sub x y, k, s, hs => by
      simp only [mixedCompile, chalSlots, List.mem_append, mixedRawSlots] at hs ⊢
      rcases hs with h | h
      · exact Or.inl (chalSlots_mixedCompile_subset b col0 x k s h)
      · exact Or.inr (chalSlots_mixedCompile_subset b col0 y k s h)
  | .Neg x, k, s, hs => by
      simp only [mixedCompile, chalSlots, mixedRawSlots] at hs ⊢
      exact chalSlots_mixedCompile_subset b col0 x k s hs
  | .Mul x y, k, s, hs => by
      simp only [mixedRawSlots, List.mem_append]
      rcases chalSlots_mulVec b _ _ k s hs with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl (chalSlots_mixedCompile_subset b col0 x i s hi)
      · exact Or.inr (chalSlots_mixedCompile_subset b col0 y j s hj)
  | .Pow x n, k, s, hs => by
      simp only [mixedRawSlots]
      obtain ⟨j, hj⟩ := chalSlots_powVec b _ n k s hs
      exact chalSlots_mixedCompile_subset b col0 x j s hj

end Compiler

section Memory

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The slot-2 block: raw memory challenge slots `12..14` (`6 + 3·2 + k`). -/
def slot2 (s : ℕ) : Prop := 12 ≤ s ∧ s < 15

/-- **Decided once, for every `F`**: no mixed gate of the deployed memory chip can reach a raw
slot of the `𝕂` slot-2 block (table `γ`).  The gate bodies branch on no field value, so the
kernel evaluates the instrument with `F`, `K`, `b` free. -/
theorem mixed_slots_decided (b : Basis (Fin 3) F K) :
    ((mixedTransitionGates b).flatMap (mixedRawSlots memoryCol0 3)).all
      (fun s => !(decide (12 ≤ s ∧ s < 15))) = true :=
  rfl

/-- The memory template's `col0` is the deployed `memoryCol0`. -/
theorem memorySourceTemplate_col0 (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).col0 3 = memoryCol0 := by
  funext kind idx
  simp [ChipTemplate.col0, ChipTemplate.baseCols, memorySourceTemplate, memoryCol0] <;> rfl

theorem readRootVerGate_chalSlots (b : Basis (Fin 3) F K) :
    chalSlots (readRootVerGate b) = [] := by
  simp [readRootVerGate, bcur, extCoord, chalSlots]

theorem memorySourceTemplate_baseTransition (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).baseTransition = paperBaseGates ++ [readRootVerGate b] := rfl
theorem memorySourceTemplate_extTransition (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).extTransition = [] := rfl
theorem memorySourceTemplate_extDeg1 (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).extDeg1 = [] := rfl
theorem memorySourceTemplate_extDeg3 (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).extDeg3 = [] := rfl
theorem memorySourceTemplate_equalityChecks (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).equalityChecks = [] := rfl

/-- **The whole deployed memory chip reads no raw slot of the slot-2 block.** -/
theorem memory_allGates_off_slot2 (b : Basis (Fin 3) F K) :
    ∀ g ∈ (memorySourceTemplate b).allGates b, ∀ s ∈ chalSlots g, ¬ slot2 s := by
  intro g hg s hs
  have hnil : expandList b memoryCol0 ([] : List Expr) = [] := rfl
  unfold ChipTemplate.allGates ChipTemplate.transitionGates ChipTemplate.deg1Gates
    ChipTemplate.deg3Gates ChipTemplate.equalityGates at hg
  rw [memorySourceTemplate_baseTransition b, memorySourceTemplate_extTransition b,
    memorySourceTemplate_extDeg1 b, memorySourceTemplate_extDeg3 b,
    memorySourceTemplate_equalityChecks b, memorySourceTemplate_mixedTransition (F := F) (K := K) b,
    memorySourceTemplate_col0 b, hnil, List.append_nil, List.append_nil, List.append_nil,
    List.append_nil, List.mem_append, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hp | rfl) | hmixed
  · rw [Nock.RedTeam.Batch357.paperBaseGates_chalSlots (F := F) (K := K) g hp] at hs
    simp at hs
  · rw [readRootVerGate_chalSlots] at hs
    simp at hs
  · obtain ⟨g', hg', k, rfl⟩ := (mem_mixedExpandList _ _ _ _).1 hmixed
    have hraw := chalSlots_mixedCompile_subset b memoryCol0 g' k s hs
    have hall := mixed_slots_decided b
    rw [List.all_eq_true] at hall
    have hmem : s ∈ (mixedTransitionGates b).flatMap (mixedRawSlots memoryCol0 3) :=
      List.mem_flatMap.2 ⟨g', hg', hraw⟩
    have := hall s hmem
    intro hh
    simp at this
    rcases hh with ⟨h1, h2⟩
    omega

/-! ## Transport: equal chips off the unread block -/

/-- Two chalVals agreeing off the slot-2 block give the same source RAP. -/
theorem sourceMemoryRAP_congr {h : ℕ} (b : Basis (Fin 3) F K) (cv cv' pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (hagree : ∀ s, ¬ slot2 s → cv' s = cv s) :
    sourceMemoryRAP b cv' pv orbit H = sourceMemoryRAP b cv pv orbit H := by
  have hC : ∀ i : Fin ((memorySourceTemplate b).allGates b).length,
      coeffToMv (w := (memorySourceTemplate b).width 3 + 2) cv' pv
          (((memorySourceTemplate b).allGates b).get i) =
        coeffToMv (w := (memorySourceTemplate b).width 3 + 2) cv pv
          (((memorySourceTemplate b).allGates b).get i) := by
    intro i
    apply coeffToMv_congr_of_chalSlots
    intro s hs
    exact hagree s (memory_allGates_off_slot2 b _ (List.get_mem _ _) s hs)
  unfold sourceMemoryRAP expandChipTail
  congr 1
  funext i
  exact hC i

/-- The named source RAP as an explicit function of its `RAP`, its preprocessing map and the two
fingerprint facts the proof fields need (`k = 1`, round-0 width `182`).  `namedSourceMemoryRAP`
is this at `sourceMemoryRAP` (`rfl`, proof irrelevance), which makes the congruence a `subst`. -/
noncomputable def mkNamed (pre : Fin 4 → F[X]) (R : RAP F) (hk : 0 < R.k)
    (hw : R.wRAP (R.firstRound hk) = 182) : FixedPreprocessingRAP F where
  rap := R
  rounds_pos := hk
  fixedCount := 4
  preprocessingIndex :=
    { toFun := fun j =>
        if h3 : (j : ℕ) = 3 then ⟨154, by rw [hw]; omega⟩
        else if h2 : (j : ℕ) = 2 then ⟨153, by rw [hw]; omega⟩
        else ⟨4 + (j : ℕ), by
          rw [hw]
          have hj : (j : ℕ) < 4 := j.isLt
          omega⟩
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first | rfl | cases hij }
  preprocessing := pre

theorem namedSourceMemoryRAP_eq_mkNamed {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    namedSourceMemoryRAP hn nodes b cv pv orbit kMem =
      mkNamed (namedSourceMemoryRAP hn nodes b cv pv orbit kMem).preprocessing
        (sourceMemoryRAP b cv pv orbit (rowNodeSet nodes))
        (namedSourceMemoryRAP hn nodes b cv pv orbit kMem).rounds_pos rfl := rfl

theorem mkNamed_congr (pre : Fin 4 → F[X]) {R R' : RAP F} (hR : R = R')
    (hk : 0 < R.k) (hw : R.wRAP (R.firstRound hk) = 182)
    (hk' : 0 < R'.k) (hw' : R'.wRAP (R'.firstRound hk') = 182) :
    mkNamed pre R hk hw = mkNamed pre R' hk' hw' := by
  subst hR
  rfl

theorem namedSourceMemoryRAP_congr {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv cv' pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ)
    (hagree : ∀ s, ¬ slot2 s → cv' s = cv s) :
    namedSourceMemoryRAP hn nodes b cv' pv orbit kMem =
      namedSourceMemoryRAP hn nodes b cv pv orbit kMem := by
  have hpre : (namedSourceMemoryRAP hn nodes b cv' pv orbit kMem).preprocessing =
      (namedSourceMemoryRAP hn nodes b cv pv orbit kMem).preprocessing := rfl
  rw [namedSourceMemoryRAP_eq_mkNamed hn nodes b cv' pv orbit kMem,
    namedSourceMemoryRAP_eq_mkNamed hn nodes b cv pv orbit kMem, hpre]
  exact mkNamed_congr _ (sourceMemoryRAP_congr b cv cv' pv orbit (rowNodeSet nodes) hagree)
    _ _ _ _

/-- The final chip as a function of the named source chip alone. -/
noncomputable def padNamed (S : FixedPreprocessingRAP F) : FixedPreprocessingRAP F :=
  RAPPadding.padFixedPreprocessing S
    (RAPPadding.firstRoundExtra S.rap S.rounds_pos (RAPPadding.memoryResidualColumns 3))
    (RAPPadding.memoryResidualTransitionGates 3)

theorem namedFinalMemoryRAP_eq_padNamed {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    namedFinalMemoryRAP hn nodes b cv pv orbit kMem =
      padNamed (namedSourceMemoryRAP hn nodes b cv pv orbit kMem) := rfl

/-- **Transport.**  Two memory chalVals agreeing off the slot-2 block give the SAME deployed
memory chip (`namedFinalMemoryRAP`), hence the same acceptance. -/
theorem namedFinalMemoryRAP_congr {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv cv' pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ)
    (hagree : ∀ s, ¬ slot2 s → cv' s = cv s) :
    namedFinalMemoryRAP hn nodes b cv' pv orbit kMem =
      namedFinalMemoryRAP hn nodes b cv pv orbit kMem := by
  rw [namedFinalMemoryRAP_eq_padNamed, namedFinalMemoryRAP_eq_padNamed,
    namedSourceMemoryRAP_congr hn nodes b cv cv' pv orbit kMem hagree]

end Memory

end Nock.RedTeam.Batch1060

#print axioms Nock.RedTeam.Batch1060.chalSlots_mixedCompile_subset
#print axioms Nock.RedTeam.Batch1060.mixed_slots_decided
#print axioms Nock.RedTeam.Batch1060.memory_allGates_off_slot2
#print axioms Nock.RedTeam.Batch1060.namedFinalMemoryRAP_congr
