/-
  Nock/NockVMROM/Thm54/P8Core/PartAReWalkChip.lean

  Below the statement.

  * The read instrument `mixedKReads` / `mixedFReads` / `coeffReads` with its soundness
    (`mixed_congr`, `coeff_congr`), and the decided census `mixed_census`: of the fifty landed
    memory mixed gates exactly the nine walk positions `27..33, 47, 48` read a re-walked role
    (`31` `ln`, `32` `count`, `33` `acc`, `55` `walk_inv`), the walk-α slot `3` or the
    `initial_count` public; the base bucket reads none (`base_quiet`).
  * `forestVecBFT_isForestFullBFT`: `ForestVecBFT V Cv` gives the full-BFT polynomial identity of
    the `RLC^γ`-images at EVERY `γ`.
  * `forest_at_view`: from `AcceptanceAt309` and the twelve-coin event alone,
    tiling, `BFSValidF` and `ForestVecBFT` at the memory view `walkView11 c` (walk coin `αW`).
  * `reWalk P Qm c`: the memory trace with the walk limbs `99..107`, `171..173` re-filled by the
    honest walk at the timestamp coin `α = alphaM c.1` over the labels decoded at the view.
  * `memory_transfer`: the generic transfer (quiet gates move, loud gates are checked).
  * `memory_satisfies_at_alpha`: the landed memory chip at `forget12 c` (walk coin `α`) accepts
    `reWalk P Qm c` — from acceptance, `c ∉ consumedFailureEvent309` (summands 7, 9, 10 at `αW`
    for the forest; summand 15 for the order of `α`; summand 14 for `α ≠ 0`).

  Scope: `repartitionedChronology` and the parallel package; nothing here is about
  `deployedChronology`.  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartAReWalk
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
import Nock.NockVMROM.Thm54.P8Core.Batch501Thm54MemoryTopology
import Nock.NockVMROM.Thm54.P8Core.Batch824Thm54R4Bridge
import Nock.NockVMROM.Thm54.Unhosted309Insensitive

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 20000

namespace Nock.NockVMROM.Thm54.PartAReWalk

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Walk Nock.MemoryTable
open Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler.MixedExpr (ofExpr)
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.Unhosted309 (varVal)

noncomputable section

/-! ## 1. The read instrument -/

/-- Base-field reads of a `CoeffExpr`. -/
def coeffReads {F : Type} : CoeffExpr F → List (VarKind × ℕ)
  | .const _ => []
  | .var k i => [(k, i)]
  | .add a b => coeffReads a ++ coeffReads b
  | .sub a b => coeffReads a ++ coeffReads b
  | .mul a b => coeffReads a ++ coeffReads b
  | .neg a => coeffReads a
  | .pow a _ => coeffReads a

/-- `𝕂`-level reads of a mixed gate. -/
def mixedKReads {F : Type} : MixedExpr F → List (VarKind × ℕ)
  | .Var k i => [(k, i)]
  | .Lift _ => []
  | .Scale _ u => mixedKReads u
  | .Const _ => []
  | .Add x y => mixedKReads x ++ mixedKReads y
  | .Sub x y => mixedKReads x ++ mixedKReads y
  | .Mul x y => mixedKReads x ++ mixedKReads y
  | .Neg x => mixedKReads x
  | .Pow x _ => mixedKReads x

/-- Base-field reads inside the `Lift` / `Scale` leaves of a mixed gate. -/
def mixedFReads {F : Type} : MixedExpr F → List (VarKind × ℕ)
  | .Var _ _ => []
  | .Lift c => coeffReads c
  | .Scale c u => coeffReads c ++ mixedFReads u
  | .Const _ => []
  | .Add x y => mixedFReads x ++ mixedFReads y
  | .Sub x y => mixedFReads x ++ mixedFReads y
  | .Mul x y => mixedFReads x ++ mixedFReads y
  | .Neg x => mixedFReads x
  | .Pow x _ => mixedFReads x

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem coeff_congr : ∀ (g : CoeffExpr F) {E E' : Env F},
    (∀ q ∈ coeffReads g, varVal E q.1 q.2 = varVal E' q.1 q.2) → g.eval E = g.eval E'
  | .const _, _, _, _ => rfl
  | .var k i, E, E', h => by
      have := h (k, i) (by simp [coeffReads])
      cases k <;> simpa [varVal, CoeffExpr.eval] using this
  | .add a b, _, _, h => by
      simp only [coeffReads, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_congr a (fun q hq => h q (Or.inl hq)),
        coeff_congr b (fun q hq => h q (Or.inr hq))]
  | .sub a b, _, _, h => by
      simp only [coeffReads, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_congr a (fun q hq => h q (Or.inl hq)),
        coeff_congr b (fun q hq => h q (Or.inr hq))]
  | .mul a b, _, _, h => by
      simp only [coeffReads, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_congr a (fun q hq => h q (Or.inl hq)),
        coeff_congr b (fun q hq => h q (Or.inr hq))]
  | .neg a, _, _, h => by simp only [coeffReads] at h; simp only [CoeffExpr.eval, coeff_congr a h]
  | .pow a _, _, _, h => by simp only [coeffReads] at h; simp only [CoeffExpr.eval, coeff_congr a h]

theorem mixed_congr : ∀ (g : MixedExpr F) {eK eK' : Env K} {eF eF' : Env F},
    (∀ q ∈ mixedKReads g, varVal eK q.1 q.2 = varVal eK' q.1 q.2) →
    (∀ q ∈ mixedFReads g, varVal eF q.1 q.2 = varVal eF' q.1 q.2) →
    g.eval eK eF = g.eval eK' eF'
  | .Var k i, eK, eK', _, _, hK, _ => by
      have := hK (k, i) (by simp [mixedKReads])
      cases k <;> simpa [varVal, MixedExpr.eval] using this
  | .Lift c, _, _, _, _, _, hF => by
      simp only [mixedFReads] at hF
      simp only [MixedExpr.eval, coeff_congr c hF]
  | .Scale c u, _, _, _, _, hK, hF => by
      simp only [mixedKReads] at hK
      simp only [mixedFReads, List.mem_append] at hF
      simp only [MixedExpr.eval, coeff_congr c (fun q hq => hF q (Or.inl hq)),
        mixed_congr u hK (fun q hq => hF q (Or.inr hq))]
  | .Const _, _, _, _, _, _, _ => rfl
  | .Add x y, _, _, _, _, hK, hF => by
      simp only [mixedKReads, mixedFReads, List.mem_append] at hK hF
      simp only [MixedExpr.eval,
        mixed_congr x (fun q hq => hK q (Or.inl hq)) (fun q hq => hF q (Or.inl hq)),
        mixed_congr y (fun q hq => hK q (Or.inr hq)) (fun q hq => hF q (Or.inr hq))]
  | .Sub x y, _, _, _, _, hK, hF => by
      simp only [mixedKReads, mixedFReads, List.mem_append] at hK hF
      simp only [MixedExpr.eval,
        mixed_congr x (fun q hq => hK q (Or.inl hq)) (fun q hq => hF q (Or.inl hq)),
        mixed_congr y (fun q hq => hK q (Or.inr hq)) (fun q hq => hF q (Or.inr hq))]
  | .Mul x y, _, _, _, _, hK, hF => by
      simp only [mixedKReads, mixedFReads, List.mem_append] at hK hF
      simp only [MixedExpr.eval,
        mixed_congr x (fun q hq => hK q (Or.inl hq)) (fun q hq => hF q (Or.inl hq)),
        mixed_congr y (fun q hq => hK q (Or.inr hq)) (fun q hq => hF q (Or.inr hq))]
  | .Neg x, _, _, _, _, hK, hF => by
      simp only [mixedKReads, mixedFReads] at hK hF
      simp only [MixedExpr.eval, mixed_congr x hK hF]
  | .Pow x _, _, _, _, _, hK, hF => by
      simp only [mixedKReads, mixedFReads] at hK hF
      simp only [MixedExpr.eval, mixed_congr x hK hF]

end Congr

/-! ## 2. The bad sets of the re-walk, and the census -/

/-- The re-walked `𝕂` roles: `31` (`ln`), `32` (`count`), `33` (`acc`), `55` (`walk_inv`). -/
def walkRoleB (r : ℕ) : Bool := r == 31 || r == 32 || r == 33 || r == 55

/-- Their physical limbs: `99..107` and `171..173`. -/
def walkPhysB (j : ℕ) : Bool := decide (99 ≤ j ∧ j < 108) || decide (171 ≤ j ∧ j < 174)

/-- A `𝕂` read the re-walk may change: a re-walked role, the walk-α slot `3`, `initial_count`. -/
def badK : VarKind × ℕ → Bool
  | (.traceCur, r) => walkRoleB r
  | (.traceNext, r) => walkRoleB r
  | (.challenge, i) => i == 3
  | (.publicVal, i) => i == 0

/-- A base read the re-walk may change: a walk limb, the raw walk-α limbs, the raw
`initial_count` limbs. -/
def badF : VarKind × ℕ → Bool
  | (.traceCur, j) => walkPhysB j
  | (.traceNext, j) => walkPhysB j
  | (.challenge, j) => decide (15 ≤ j ∧ j < 18)
  | (.publicVal, j) => decide (6 ≤ j ∧ j < 9)

/-- A mixed gate that reads nothing the re-walk changes. -/
def quietM {F : Type} (g : MixedExpr F) : Bool :=
  (mixedKReads g).all (fun q => !badK q) && (mixedFReads g).all (fun q => !badF q)

/-- A base gate that reads nothing the re-walk changes. -/
def quietC {F : Type} (g : CoeffExpr F) : Bool := (coeffReads g).all (fun q => !badF q)

theorem raw_good_of_badK (k : VarKind) (r : ℕ) (hr : badK (k, r) = false) (j : Fin 3) :
    badF (k, memoryCol0 k r + (j : ℕ)) = false := by
  have hj := j.isLt
  cases k <;> simp [badK, badF, walkRoleB, walkPhysB, memoryCol0] at hr ⊢ <;> first | omega | (refine ⟨decide_eq_false ?_, decide_eq_false ?_⟩ <;> omega) | (apply decide_eq_false; omega)

section Transfer
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem gather_congr (b : Module.Basis (Fin 3) F K) {E E' : Env F}
    (h : ∀ q, badF q = false → varVal E q.1 q.2 = varVal E' q.1 q.2) :
    ∀ q, badK q = false →
      varVal (gatherEnv b memoryCol0 E) q.1 q.2 = varVal (gatherEnv b memoryCol0 E') q.1 q.2 := by
  rintro ⟨k, r⟩ hq
  have hraw : ∀ j : Fin 3, varVal E k (memoryCol0 k r + (j : ℕ)) =
      varVal E' k (memoryCol0 k r + (j : ℕ)) := fun j => h _ (raw_good_of_badK k r hq j)
  cases k <;> simp only [varVal, gatherEnv] at hraw ⊢ <;>
    exact Finset.sum_congr rfl fun j _ => by rw [hraw j]

theorem quietM_eval (b : Module.Basis (Fin 3) F K) (g : MixedExpr F) (hg : quietM g = true)
    {E E' : Env F} (h : ∀ q, badF q = false → varVal E q.1 q.2 = varVal E' q.1 q.2) :
    g.eval (gatherEnv b memoryCol0 E) E = g.eval (gatherEnv b memoryCol0 E') E' := by
  simp only [quietM, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  exact mixed_congr g (fun q hq => gather_congr b h q (hg.1 q hq)) (fun q hq => h q (hg.2 q hq))

theorem quietC_eval (g : CoeffExpr F) (hg : quietC g = true)
    {E E' : Env F} (h : ∀ q, badF q = false → varVal E q.1 q.2 = varVal E' q.1 q.2) :
    g.eval E = g.eval E' := by
  simp only [quietC, List.all_eq_true, Bool.not_eq_true'] at hg
  exact coeff_congr g (fun q hq => h q (hg q hq))

set_option maxHeartbeats 4000000 in
/-- **The census** (decided at every `F`, `K`, basis): of the fifty landed memory mixed gates,
exactly the nine walk positions `27..33` (the seven walk gates) and `47, 48` (the two queue
gates) are loud; the other forty-one read no re-walked column, neither the walk-α slot nor
`initial_count`. -/
theorem mixed_census (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b).map quietM =
      (List.range 50).map (fun i => !(decide (27 ≤ i ∧ i < 34) || i == 47 || i == 48)) := rfl

/-- The base bucket is quiet. -/
theorem base_quiet (b : Module.Basis (Fin 3) F K) : (baseTransitionGates b).all quietC = true := rfl

/-- Pointwise form of the census. -/
theorem quietM_get (b : Module.Basis (Fin 3) F K) (k : ℕ)
    (hk : k < (mixedTransitionGates (F := F) (K := K) b).length) :
    quietM ((mixedTransitionGates (F := F) (K := K) b)[k]) =
      !(decide (27 ≤ k ∧ k < 34) || k == 47 || k == 48) := by
  have hk' : k < ((mixedTransitionGates (F := F) (K := K) b).map quietM).length := by simpa using hk
  have h1 : ((mixedTransitionGates (F := F) (K := K) b).map quietM)[k]'hk' =
      quietM ((mixedTransitionGates (F := F) (K := K) b)[k]) := List.getElem_map ..
  refine h1.symm.trans ((List.getElem_of_eq (mixed_census b) hk').trans ?_)
  simp

/-- A loud gate sits at one of the nine walk positions. -/
theorem loud_pos (b : Module.Basis (Fin 3) F K) (g : MixedExpr F)
    (hg : g ∈ mixedTransitionGates (F := F) (K := K) b) (hq : quietM g = false) :
    ∃ (k : ℕ) (hk : k < (mixedTransitionGates (F := F) (K := K) b).length),
      (mixedTransitionGates (F := F) (K := K) b)[k] = g ∧
        ((27 ≤ k ∧ k < 34) ∨ k = 47 ∨ k = 48) := by
  obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
  refine ⟨k, hk, hkg, ?_⟩
  have hc := quietM_get b k hk
  rw [hkg, hq] at hc
  by_contra hn
  simp only [not_or, not_and, not_lt] at hn
  have h1 : decide (27 ≤ k ∧ k < 34) = false := by
    simp only [decide_eq_false_iff_not, not_and, not_lt]; exact hn.1
  have h2 : (k == 47) = false := by simpa using hn.2.1
  have h3 : (k == 48) = false := by simpa using hn.2.2
  rw [h1, h2, h3] at hc
  simp at hc

end Transfer

/-! ## 3. `ForestVecBFT` gives the full-BFT identity of the `RLC`-images at every `γ` -/

section Forest
variable {K : Type} [Field K] {n : ℕ}


theorem forestVecBFT_isForestFullBFT (γ : K) {V : ℕ → Fin n → K} {Cv : ℕ → ℕ → Fin n → K}
    {fo : ℕ → ℕ} {kroots h : ℕ} (hb : ForestVecBFT V Cv fo kroots h) :
    IsForestFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h := by
  unfold IsForestFullBFT
  rw [nodeListP_eq_lpoly_gen, forestQueueP_eq_lpoly, curVals_rlc, curVals_rlc, flatBlks_rlc,
    ← List.map_append]
  unfold ForestVecBFT at hb
  rw [hb]

end Forest

/-! ## 4. The forest at the memory view -/

section View

open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch501

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- Landed memory satisfaction at the memory view (P3). -/
theorem memSat_at_view (hacc : AcceptanceAt309 P Qc Qm c) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 c))
      (familyQm P (walkView11 c) Qm) :=
  (Pkg12.memoryChipAt12_satisfies_iff P c Qm).1 hacc.memory_satisfies

/-- Summands 7, 9, 10 at the view: 7 and 10 on `walkJoint c` (`αW`), 9 on the shared `γ` (P3). -/
theorem view_events (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    (walkView11 c).1 ∉ P.memoryTilingEventOf Qm ∧
    (walkView11 c).1 ∉ P.memoryPrefixGammaEventOf Qm ∧
    (walkView11 c).1 ∉ P.memoryForestAlphaEventOf Qm := by
  have hn := Pkg12.notMem_consumedFailureEvent12 P (truncQc P Qc) Qm c hgood
  refine ⟨hn.2.2.2.2.2.2.1, ?_, hn.2.2.2.2.2.2.2.2.2.1⟩
  have h9 := hn.2.2.2.2.2.2.2.2.1
  intro hmem
  apply h9
  simp only [OptimizedFullStrictNockVMROMPackage.memoryPrefixGammaEventOf,
    memoryPrefixGammaEventOfEnvs, mem_memoryPrefixGammaEvent_iff] at hmem ⊢
  exact hmem

/-- **The forest facts at the memory view**. -/
theorem forest_at_view (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) (hchar : MemStateTagChar F) :
    let t := walkView11 c
    (kMemP P + Sf (foW P t (familyQm P t Qm)) (memRowsP P) = memRowsP P) ∧
    BFSValidF (kMemP P) (foW P t (familyQm P t Qm)) (memRowsP P) ∧
    ForestVecBFT (VdM P t Qm) (CvdM P t Qm) (foM P Qm t) (kMemP P) (memRowsP P) ∧
    ForestVecBFT (fun i => encPT (lblM P Qm t i))
      (fun i l => encPT (clabOfMem (lblM P Qm t) i l))
      (foM P Qm t) (kMemP P) (memRowsP P) := by
  intro t
  have hsatM := memSat_at_view P Qc Qm c hacc
  obtain ⟨h7, h9, h10⟩ := view_events P Qc Qm c hgood
  have htileα : t.1 ∉ WalkTilingEvents.memoryTilingEvent (foW P t (familyQm P t Qm))
      (kMemP P) (memRowsP P) := by
    rwa [← memoryTilingEventOf_eq_foWmem P t Qm]
  have htile : kMemP P + Sf (foW P t (familyQm P t Qm)) (memRowsP P) = memRowsP P :=
    deployed_tiling_memory P t (familyQm P t Qm) hsatM hchar htileα
  have hvalid : BFSValidF (kMemP P) (foW P t (familyQm P t Qm)) (memRowsP P) :=
    deployed_bfsValid_memory P t (familyQm P t Qm) hsatM hchar
  have hγ : gamma t.1 ∉ forestPrefixBadGammas (VdM P t Qm) (CvdM P t Qm)
      (foM P Qm t) (kMemP P) (memRowsP P) := by
    rw [← forestPrefixBadGammas_VdM_eq_committed P t Qm]
    exact hγM_of_priced P t Qm h9
  have htile' : kMemP P + Sf (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm))
      (memRowsP P) = memRowsP P := by
    rw [Sf_foOfMem_eq_foWmem P t Qm]; exact htile
  have hmem : alphaM t.1 ∉ walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) (gamma t.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm)) (gamma t.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm)) (kMemP P) (memRowsP P) :=
    (mem_memoryForestAlphaEventOfEnvs_of_tiling
      (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) (kMemP P) htile' t.1).mpr.mt
      (by simpa [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf] using h10)
  have heq : walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) (gamma t.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm)) (gamma t.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm)) (kMemP P) (memRowsP P) =
      walkForestPrefixAlphaEvent
        (curW P t (familyQm P t Qm)) (chldW P t (familyQm P t Qm))
        (foW P t (familyQm P t Qm)) (kMemP P) (memRowsP P) := by
    refine WalkForestPrefixAlphaEvents.walkForestPrefixAlphaEvent_congr_on
      (kMem_le_memRows P) ?_ ?_ ?_
    · intro i h1 h2
      simp only [curOfMem]
      have hV := VdM_eq_committed P t Qm i h1 h2
      have hcur : curW P t (familyQm P t Qm) i = rlc (gamma t.1) (VdM P t Qm i) := rfl
      rw [hV, hcur]
    · intro i l h1 h2
      simp only [chldOfMem]
      have hC := CvdM_eq_committed P t Qm i l h1 h2
      have hch : chldW P t (familyQm P t Qm) i l = rlc (gamma t.1) (CvdM P t Qm i l) := rfl
      rw [hC, hch]
    · intro i h1 h2
      exact foOfMem_eq_foWmem P t Qm i h1 h2
  have hα : alphaM t.1 ∉ walkForestPrefixAlphaEvent
      (curW P t (familyQm P t Qm)) (chldW P t (familyQm P t Qm))
      (foW P t (familyQm P t Qm)) (kMemP P) (memRowsP P) := by
    rwa [heq] at hmem
  exact ⟨htile, hvalid, deployed_forestVecBFT P t Qm hsatM hchar hγ hα htileα,
    deployed_forestVecBFT_pt P t Qm hsatM hchar hγ hα htileα⟩

/-- The view's walk coin is `αW`, and nothing above identified it with `α` (P3). -/
theorem view_walk_coin : alphaM (walkView11 c).1 = walkAlphaOf c := rfl

/-- **The full-BFT identity of the view's walk operands** (`curW`/`chldW`/`foW` at the view), at
the shared `γ`, from `ForestVecBFT` of the hosted vectors. -/
theorem view_isForestFullBFT (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) (hchar : MemStateTagChar F) :
    IsForestFullBFT (curW P (walkView11 c) (familyQm P (walkView11 c) Qm))
      (chldW P (walkView11 c) (familyQm P (walkView11 c) Qm))
      (foW P (walkView11 c) (familyQm P (walkView11 c) Qm)) (kMemP P) (memRowsP P) := by
  obtain ⟨_, _, hV, _⟩ := forest_at_view P Qc Qm c hacc hgood hchar
  have hfo : foW P (walkView11 c) (familyQm P (walkView11 c) Qm) = foM P Qm (walkView11 c) := by
    funext i
    have h := foW_eq_foM_all P (walkView11 c) (familyQm P (walkView11 c) Qm) i
    rw [MemoryWalkDeployed.Qmh, WalkQueueDeployed.honestQm_familyQm P (walkView11 c) Qm] at h
    exact h
  have h := forestVecBFT_isForestFullBFT (gamma (walkView11 c).1) hV
  rw [← hfo] at h
  exact h

end View

/-! ## 5. The re-walked trace -/

section ReWalk

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.RedTeam.Batch501

/-- Interpolation of node values. -/
def interpN {F : Type} [Field F] {n : ℕ} (nodes : Fin n → F) (f : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes f

theorem interpN_eval {F : Type} [Field F] {n : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (f : Fin n → F) (i : Fin n) :
    (interpN nodes f).eval (nodes i) = f i :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

/-- The four re-walked `𝕂` roles. -/
def walkRoleOf : Fin 4 → ℕ
  | 0 => 31
  | 1 => 32
  | 2 => 33
  | 3 => 55

/-- The walk slot of a physical memory column: `(role index, limb)`. -/
def walkSlot (j : ℕ) : Option (Fin 4 × Fin 3) :=
  if h : 99 ≤ j ∧ j < 108 then some (⟨(j - 99) / 3, by omega⟩, ⟨(j - 99) % 3, by omega⟩)
  else if h' : 171 ≤ j ∧ j < 174 then some (3, ⟨j - 171, by omega⟩)
  else none

theorem walkSlot_eq_none {j : ℕ} (h : walkPhysB j = false) : walkSlot j = none := by
  simp only [walkPhysB, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  unfold walkSlot
  rw [dif_neg h.1, dif_neg h.2]

theorem walkSlot_role (q : Fin 4) (k : Fin 3) :
    walkSlot (memoryCol0 .traceCur (walkRoleOf q) + (k : ℕ)) = some (q, k) := by
  have hk := k.isLt
  fin_cases q <;> simp only [walkRoleOf, memoryCol0, walkSlot] <;>
    (split_ifs <;> first | omega | ((first | erw [dif_pos (by omega)] | erw [dif_neg (by omega), dif_pos (by omega)]); simp only [Option.some.injEq, Prod.mk.injEq]; constructor <;>
      apply Fin.ext <;> (try simp) <;> omega))

theorem walkRoleOf_memoryCol0_lt (q : Fin 4) (k : Fin 3) :
    memoryCol0 .traceCur (walkRoleOf q) + (k : ℕ) < 182 := by
  have hk := k.isLt
  fin_cases q <;> simp [walkRoleOf, memoryCol0] <;> omega

/-- The honest walk values at 1-based index `m`: `ln`, `count`, `acc`, `walk_inv`. -/
def rewalkVal {K : Type} [Field K] (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K)
    (kMem : ℕ) : Fin 4 → ℕ → K
  | 0 => lnOf α
  | 1 => countOf fo α kMem
  | 2 => fun m => accInGate cur chld fo α (α ^ kMem) kMem m
  | 3 => invOf fo α kMem

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- The walk operands decoded at the memory view (labels, children, fanouts; coin `γ`). -/
abbrev curV : ℕ → K := curW P (walkView11 c) (familyQm P (walkView11 c) Qm)
abbrev chldV : ℕ → ℕ → K := chldW P (walkView11 c) (familyQm P (walkView11 c) Qm)
abbrev foV : ℕ → ℕ := foW P (walkView11 c) (familyQm P (walkView11 c) Qm)

/-- The re-walk values at the timestamp coin `α = alphaM c.1`. -/
def rewalkVals : Fin 4 → ℕ → K :=
  rewalkVal (curV P Qm c) (chldV P Qm c) (foV P Qm c) (alphaM c.1) (kMemP P)

/-- **The re-walked memory trace** (R-T step 4): the walk limbs `99..107` (`ln`, `count`, `acc`)
and `171..173` (`walk_inv`) interpolate the honest walk at the timestamp coin `α`, over the labels,
children and fanouts decoded at the memory view; every other column is `Qm`'s. -/
def reWalk : Fin P.memoryChip.rap.w → F[X] := fun j =>
  match walkSlot j with
  | some (q, k) => interpN P.optimized.memoryNodes
      (fun i => coord P.optimized.basis (rewalkVals P Qm c q ((i : ℕ) + 1)) k)
  | none => Qm j

theorem reWalk_off (j : Fin P.memoryChip.rap.w) (h : walkPhysB j = false) :
    reWalk P Qm c j = Qm j := by
  unfold reWalk; rw [walkSlot_eq_none h]

/-- The re-walk changes only round-2 columns (`newMemoryColRound`, the walk limbs). -/
theorem reWalk_round2 : ∀ j ∈ (List.range 182).filter (fun j => walkPhysB j),
    RepartitionedStaging.newMemoryColRound j = 2 := by decide

/-- The constant memory chip is `205` wide. -/
theorem memoryChip_w : P.memoryChip.rap.w = 205 :=
  (finalMemoryRAP_fingerprint P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit P.optimized.family.problem.cfg.kMem).1

theorem projAt_apply (t : OptimizedProductionChallengeTuple K F) (X : Fin P.memoryChip.rap.w → F[X])
    (j : Fin 182) :
    projAt P t (familyQm P t X) j =
      X ⟨j, by have := j.isLt; have h := memoryChip_w P; omega⟩ := by
  simp only [projAt, familyQm]
  congr 1

theorem memorySourceTrace_apply (t : OptimizedProductionChallengeTuple K F)
    (X : Fin P.memoryChip.rap.w → F[X]) (j : Fin 182) :
    P.memorySourceTrace X j = X ⟨j, by have := j.isLt; have h := memoryChip_w P; omega⟩ := by
  have h := projAt_eq_memorySourceTrace P t (familyQm P t X)
  rw [WalkQueueDeployed.honestQm_familyQm] at h
  rw [← h, projAt_apply]

end ReWalk

/-! ## 6. The generic memory transfer -/

section MemTransfer

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem envOfTrace_agree {w : ℕ} (A A' : Fin w → F[X]) (ω x : F) (cv cv' pv pv' : ℕ → F)
    (hA : ∀ j : Fin w, walkPhysB j = false → A' j = A j)
    (hc : ∀ j, ¬ (15 ≤ j ∧ j < 18) → cv' j = cv j)
    (hp : ∀ j, ¬ (6 ≤ j ∧ j < 9) → pv' j = pv j) :
    ∀ q, badF q = false →
      varVal (envOfTrace A' ω x cv' pv') q.1 q.2 = varVal (envOfTrace A ω x cv pv) q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · simp only [badF] at hq
    simp only [varVal, envOfTrace]
    split_ifs with h
    · rw [hA ⟨j, h⟩ hq]
    · rfl
  · simp only [badF] at hq
    simp only [varVal, envOfTrace]
    split_ifs with h
    · rw [hA ⟨j, h⟩ hq]
    · rfl
  · simp only [badF, decide_eq_false_iff_not] at hq
    exact hc j hq
  · simp only [badF, decide_eq_false_iff_not] at hq
    exact hp j hq

/-- **The memory transfer**: a family memory trace accepted at `c`, and a second trace at `c'`
that agrees with it off the walk limbs, whose challenge / public vectors agree off the walk-α
slot and the `initial_count` block, and whose nine loud (walk) gates hold, is accepted at `c'`. -/
theorem memory_transfer (c c' : OptimizedProductionChallengeTuple K F)
    (Q : Fin (P.memoryChipAt c).rap.w → F[X]) (Q' : Fin (P.memoryChipAt c').rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Q)
    (hcols : ∀ j : Fin 182, walkPhysB j = false → projAt P c' Q' j = projAt P c Q j)
    (hchal : ∀ j, ¬ (15 ≤ j ∧ j < 18) →
      memoryChalValOfTuple P.optimized.basis c' j = memoryChalValOfTuple P.optimized.basis c j)
    (hpub : ∀ j, ¬ (6 ≤ j ∧ j < 9) → P.familyMemoryPublic c' j = P.familyMemoryPublic c j)
    (hwalk : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis, quietM g = false →
        g.eval (memorySourceEnvAt P c' (honestQm P c' Q') i)
          (memoryBaseEnvAt P c' (honestQm P c' Q') i) = 0) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c') Q' := by
  have hsrc := source_sat_at P c Q hsat
  have hraw : (sourceMemoryRAP P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).Satisfies
        (projAt P c Q) := hsrc.1
  rw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled] at hraw
  refine (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c')
    (P.familyMemoryPublic c') P.optimized.orbit
    P.optimized.family.problem.cfg.kMem Q').mpr ⟨?_, ?_⟩
  · show (sourceMemoryRAP P.optimized.basis (memoryChalValOfTuple P.optimized.basis c')
        (P.familyMemoryPublic c') P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).Satisfies
        (projAt P c' Q')
    rw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled]
    intro x hx
    obtain ⟨i, _, rfl⟩ :=
      (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ Finset.univ _).mp hx
    have hparts := hraw _ hx
    have hag := envOfTrace_agree (projAt P c Q) (projAt P c' Q') P.optimized.orbit.ω
      (P.optimized.memoryNodes i) _ _ _ _ hcols hchal hpub
    have hcol0 : (memorySourceTemplate P.optimized.basis).col0 3 = memoryCol0 := rfl
    rw [hcol0] at hparts ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      have hq : quietC g = true := List.all_eq_true.mp (base_quiet P.optimized.basis) g hg
      rw [quietC_eval g hq hag]
      exact hparts.1 g hg
    · intro g hg
      have : equalityChecks P.optimized.basis = ([] : List (CoeffExpr F)) := rfl
      rw [this] at hg; cases hg
    · intro g hg
      have : (memorySourceTemplate P.optimized.basis).extTransition ++
          (memorySourceTemplate P.optimized.basis).extDeg1 ++
          (memorySourceTemplate P.optimized.basis).extDeg3 = ([] : List Expr) := rfl
      rw [this] at hg; cases hg
    · intro g hg
      by_cases hq : quietM g = true
      · rw [quietM_eval P.optimized.basis g hq hag]
        exact hparts.2.2.2 g hg
      · have h := hwalk i g hg (by simpa using hq)
        have hF := envF_eq_base P c' Q' i
        simp only [memorySourceEnvAt] at h
        rw [← hF] at h
        simpa [memorySourceTemplate_col0] using h
  · intro j
    have hb := hsrc.2 j
    fin_cases j
    · show projAt P c' Q' ⟨4, by norm_num⟩ = _
      rw [hcols ⟨4, by norm_num⟩ (by decide)]; exact hb
    · show projAt P c' Q' ⟨5, by norm_num⟩ = _
      rw [hcols ⟨5, by norm_num⟩ (by decide)]; exact hb
    · show projAt P c' Q' ⟨153, by norm_num⟩ = _
      rw [hcols ⟨153, by norm_num⟩ (by decide)]; exact hb
    · show projAt P c' Q' ⟨154, by norm_num⟩ = _
      rw [hcols ⟨154, by norm_num⟩ (by decide)]; exact hb

end MemTransfer

/-! ## 7. The re-walked rows -/

section Rows

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.RedTeam.Batch501

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- The memory view and the landed tuple differ only in the `alphaM` coordinate: their memory
challenge vectors agree off the walk-α limbs `15..17`. -/
theorem chal_view_agree (j : ℕ) (hj : ¬ (15 ≤ j ∧ j < 18)) :
    memoryChalValOfTuple P.optimized.basis (forget12 c) j =
      memoryChalValOfTuple P.optimized.basis (walkView11 c) j := by
  unfold memoryChalValOfTuple
  split_ifs with h
  · have hq : (j - 6) / 3 ≠ 3 := by omega
    congr 1
    generalize hq' : (j - 6) / 3 = q at hq
    match q, hq with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | n + 9, _ => rfl
  · rfl

/-- ... and their memory publics agree off the `initial_count` block `6..8`. -/
theorem pub_view_agree (j : ℕ) (hj : ¬ (6 ≤ j ∧ j < 9)) :
    P.familyMemoryPublic (forget12 c) j = P.familyMemoryPublic (walkView11 c) j := by
  simp only [OptimizedFullStrictNockVMROMPackage.familyMemoryPublic, memoryPublicOfTuple, dif_neg hj]

/-- **Raw agreement**: the landed re-walked row and the view row agree on every base read off the
walk limbs, the walk-α limbs and `initial_count`. -/
theorem rw_agreeF (i : Fin (memRows P)) :
    ∀ q, badF q = false →
      varVal (envF P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i) q.1 q.2 =
        varVal (envF P (walkView11 c) (familyQm P (walkView11 c) Qm) i) q.1 q.2 := by
  intro q hq
  simp only [MemoryWalkDeployed.envF, MemoryWalkDeployed.Qmh]
  rw [← envF_eq_base, ← envF_eq_base]
  refine envOfTrace_agree _ _ _ _ _ _ _ _ ?_ (chal_view_agree P c) (pub_view_agree P c) q hq
  intro j hj
  rw [projAt_apply, projAt_apply, reWalk_off P Qm c _ hj]

/-- **`𝕂` agreement** off the re-walked roles, the walk-α slot and `initial_count`. -/
theorem rw_agreeK (i : Fin (memRows P)) :
    ∀ q, badK q = false →
      varVal (envK P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i) q.1 q.2 =
        varVal (envK P (walkView11 c) (familyQm P (walkView11 c) Qm) i) q.1 q.2 :=
  gather_congr P.optimized.basis (rw_agreeF P Qm c i)

/-- The re-walked roles carry the honest walk values on every row. -/
theorem rw_trace (i : Fin (memRows P)) (q : Fin 4) :
    (envK P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i).trace (walkRoleOf q) =
      rewalkVals P Qm c q ((i : ℕ) + 1) := by
  simp only [envK, Qmh, memorySourceEnvAt, gatherEnv, memoryBaseEnvAt, envOfTrace]
  rw [memorySourceTemplate_col0]
  have hlt : ∀ k : Fin 3, memoryCol0 .traceCur (walkRoleOf q) + (k : ℕ) < 182 :=
    fun k => walkRoleOf_memoryCol0_lt q k
  have hk : ∀ k : Fin 3,
      (if h : memoryCol0 .traceCur (walkRoleOf q) + (k : ℕ) < 182 then
        (P.memorySourceTrace (honestQm P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)))
          ⟨_, h⟩).eval (P.optimized.memoryNodes i) else 0) =
        coord P.optimized.basis (rewalkVals P Qm c q ((i : ℕ) + 1)) k := by
    intro k
    rw [dif_pos (hlt k), WalkQueueDeployed.honestQm_familyQm, memorySourceTrace_apply P (forget12 c)]
    simp only [reWalk, walkSlot_role q k]
    exact interpN_eval _ P.optimized.memoryNodes_injective _ i
  simp only [hk]
  exact reconstruct_coord P.optimized.basis _

/-- ... and on the successor row (`i + 1 < memRows`). -/
theorem rw_traceNext (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) (q : Fin 4) :
    (envK P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i).traceNext (walkRoleOf q) =
      rewalkVals P Qm c q ((i : ℕ) + 2) := by
  rw [envK_traceNext P (forget12 c) _ i hi, rw_trace P Qm c ⟨(i : ℕ) + 1, hi⟩ q]

end Rows


/-! ## 8. The readers of the re-walked rows, from the view -/

section Readers

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.RedTeam.Batch501

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- The landed re-walked base row (`forget12 c`). -/
abbrev eFt (i : Fin (memRows P)) : Env F :=
  envF P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i
/-- The landed re-walked `𝕂` row. -/
abbrev eKt (i : Fin (memRows P)) : Env K :=
  envK P (forget12 c) (familyQm P (forget12 c) (reWalk P Qm c)) i
/-- The view base row (`walkView11 c`). -/
abbrev eFv (i : Fin (memRows P)) : Env F := envF P (walkView11 c) (familyQm P (walkView11 c) Qm) i
/-- The view `𝕂` row. -/
abbrev eKv (i : Fin (memRows P)) : Env K := envK P (walkView11 c) (familyQm P (walkView11 c) Qm) i

theorem rw_base (i : Fin (memRows P)) (j : ℕ) (hj : walkPhysB j = false) :
    (eFt P Qm c i).trace j = (eFv P Qm c i).trace j :=
  rw_agreeF P Qm c i (.traceCur, j) hj

theorem rw_baseNext (i : Fin (memRows P)) (j : ℕ) (hj : walkPhysB j = false) :
    (eFt P Qm c i).traceNext j = (eFv P Qm c i).traceNext j :=
  rw_agreeF P Qm c i (.traceNext, j) hj

theorem mopCol_lt (st : MState) : mopCol st < 4 := by cases st <;> decide

theorem rw_selCur (i : Fin (memRows P)) (st : MState) :
    ((curReader (F := F)).sel st).eval (eFt P Qm c i) = ((curReader (F := F)).sel st).eval (eFv P Qm c i) := by
  rw [curReader_sel_eval, curReader_sel_eval]
  exact rw_base P Qm c i _ (by have := mopCol_lt st; simp [walkPhysB]; omega)

theorem rw_selNext (i : Fin (memRows P)) (st : MState) :
    ((nextReader (F := F)).sel st).eval (eFt P Qm c i) = ((nextReader (F := F)).sel st).eval (eFv P Qm c i) := by
  rw [nextReader_sel_eval, nextReader_sel_eval]
  exact rw_baseNext P Qm c i _ (by have := mopCol_lt st; simp [walkPhysB]; omega)

theorem rw_colCur (i : Fin (memRows P)) (r : ℕ) (hr : walkRoleB r = false) :
    ((curReader (F := F)).col r).eval (eKt P Qm c i) (eFt P Qm c i) =
      ((curReader (F := F)).col r).eval (eKv P Qm c i) (eFv P Qm c i) := by
  rw [curReader_col_eval, curReader_col_eval]
  exact rw_agreeK P Qm c i (.traceCur, r) hr

theorem rw_colNext (i : Fin (memRows P)) (r : ℕ) (hr : walkRoleB r = false) :
    ((nextReader (F := F)).col r).eval (eKt P Qm c i) (eFt P Qm c i) =
      ((nextReader (F := F)).col r).eval (eKv P Qm c i) (eFv P Qm c i) := by
  rw [nextReader_col_eval, nextReader_col_eval]
  exact rw_agreeK P Qm c i (.traceNext, r) hr

theorem cellRole_quiet (j : Fin 2) (k : Fin 5) : walkRoleB (cellBase j + (k : ℕ)) = false := by
  fin_cases j <;> fin_cases k <;> decide

theorem rw_alpha (i : Fin (memRows P)) :
    (walkAlphaChallenge (F := F)).eval (eKt P Qm c i) (eFt P Qm c i) = alphaM c.1 :=
  walkAlpha_eval P (forget12 c) _ i

theorem rw_gamma (i : Fin (memRows P)) :
    (walkGammaChallenge (F := F)).eval (eKt P Qm c i) (eFt P Qm c i) = gamma c.1 :=
  walkGamma_eval P (forget12 c) _ i

theorem rw_pub0 (i : Fin (memRows P)) : (eKt P Qm c i).pub 0 = alphaM c.1 ^ kMem P :=
  envK_pub0 P (forget12 c) _ i

variable (hsatV : RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 c))
  (familyQm P (walkView11 c) Qm)) (hchar : MemStateTagChar F)

include hsatV in
theorem rw_mask4 (i : Fin (memRows P)) : (eFt P Qm c i).trace 4 = (if (i : ℕ) = 0 then 1 else 0) := by
  rw [rw_base P Qm c i 4 (by decide)]; exact envF_trace4 P _ _ hsatV i

include hsatV in
theorem rw_mask5 (i : Fin (memRows P)) :
    (eFt P Qm c i).trace 5 = (if (i : ℕ) + 1 = memRows P then 1 else 0) := by
  rw [rw_base P Qm c i 5 (by decide)]; exact envF_trace5 P _ _ hsatV i

include hsatV in
theorem rw_mask154 (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    algebraMap F K ((eFt P Qm c i).trace 154) = deqCoeff (K := K) (kMem P) ((i : ℕ) + 2) := by
  rw [rw_base P Qm c i 154 (by decide)]; exact dequeue_eq_deqCoeff P _ _ hsatV i hi

include hsatV in
theorem rw_mask154_last (i : Fin (memRows P)) (hi : (i : ℕ) + 1 = memRows P) :
    (eFt P Qm c i).trace 154 = 0 := by
  rw [rw_base P Qm c i 154 (by decide), envF_trace154 P _ _ hsatV i]; simp [hi]

include hsatV hchar in
theorem rw_selectorCM_cur (i : Fin (memRows P)) :
    (selectorCM (curReader (F := F))).eval (eKt P Qm c i) (eFt P Qm c i) =
      alphaM c.1 ^ foV P Qm c ((i : ℕ) + 1) := by
  obtain ⟨st, hone⟩ := oneHot_at P _ _ hsatV hchar i
  have hst : (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) i).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P _ _ hchar i st hone]
  rw [selectorCM_eval (curReader (F := F)) _ _ (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) i)
    (alphaM c.1) (fun st' => by rw [rw_selCur, hsel_cur P _ _ hchar i st hone st', hst])
    (rw_alpha P Qm c i)]
  simp only [foV, foW, rowOf_succ P (i : ℕ) i.isLt]

include hsatV hchar in
theorem rw_selectorCM_next (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (selectorCM (nextReader (F := F))).eval (eKt P Qm c i) (eFt P Qm c i) =
      alphaM c.1 ^ foV P Qm c ((i : ℕ) + 2) := by
  obtain ⟨st, hone⟩ := oneHot_at P _ _ hsatV hchar ⟨(i : ℕ) + 1, hi⟩
  have hst : (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P _ _ hchar _ st hone]
  rw [selectorCM_eval (nextReader (F := F)) _ _
    (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩)
    (alphaM c.1) (fun st' => by rw [rw_selNext, hsel_next P _ _ hchar i hi st hone st', hst])
    (rw_alpha P Qm c i)]
  simp only [foV, foW, rowOf_succ P ((i : ℕ) + 1) hi]

include hsatV hchar in
theorem rw_childSum_cur (i : Fin (memRows P)) :
    (childSumCC (curReader (F := F))).eval (eKt P Qm c i) (eFt P Qm c i) =
      ∑ l ∈ Finset.Icc 1 (foV P Qm c ((i : ℕ) + 1)), alphaM c.1 ^ l * chldV P Qm c ((i : ℕ) + 1) l := by
  obtain ⟨st, hone⟩ := oneHot_at P _ _ hsatV hchar i
  have hst : (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) i).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P _ _ hchar i st hone]
  rw [childSumCC_eval (curReader (F := F)) _ _ (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) i)
    (alphaM c.1) (gamma c.1) (tagsAt P (walkView11 c) (familyQm P (walkView11 c) Qm) i)
    (fun st' => by rw [rw_selCur, hsel_cur P _ _ hchar i st hone st', hst])
    (fun j k => by rw [rw_colCur P Qm c i _ (cellRole_quiet j k)]; exact cur_child_cell P _ _ i j k)
    (rw_alpha P Qm c i) (rw_gamma P Qm c i)
    (fun j => by
      simp only [childTagHost]
      rw [rw_colCur P Qm c i _ (by fin_cases j <;> decide)]
      rfl)]
  simp only [foV, foW, chldV, chldW, rowOf_succ P (i : ℕ) i.isLt]
  rfl

include hsatV hchar in
theorem rw_childSum_next (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (childSumCC (nextReader (F := F))).eval (eKt P Qm c i) (eFt P Qm c i) =
      ∑ l ∈ Finset.Icc 1 (foV P Qm c ((i : ℕ) + 2)), alphaM c.1 ^ l * chldV P Qm c ((i : ℕ) + 2) l := by
  obtain ⟨st, hone⟩ := oneHot_at P _ _ hsatV hchar ⟨(i : ℕ) + 1, hi⟩
  have hst : (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P _ _ hchar _ st hone]
  rw [childSumCC_eval (nextReader (F := F)) _ _
    (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩)
    (alphaM c.1) (gamma c.1) (tagsAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩)
    (fun st' => by rw [rw_selNext, hsel_next P _ _ hchar i hi st hone st', hst])
    (fun j k => by rw [rw_colNext P Qm c i _ (cellRole_quiet j k)]; exact next_child_cell P _ _ i hi j k)
    (rw_alpha P Qm c i) (rw_gamma P Qm c i)
    (fun j => by
      simp only [childTagHost]
      rw [rw_colNext P Qm c i _ (by fin_cases j <;> decide), nextReader_col_eval,
        envK_traceNext P _ _ i hi]
      rfl)]
  simp only [foV, foW, chldV, chldW, rowOf_succ P ((i : ℕ) + 1) hi]
  rfl

include hsatV hchar in
theorem rw_label_next (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (labelRLC (nextReader (F := F))).eval (eKt P Qm c i) (eFt P Qm c i) =
      curV P Qm c ((i : ℕ) + 2) := by
  obtain ⟨st, hone⟩ := oneHot_at P _ _ hsatV hchar ⟨(i : ℕ) + 1, hi⟩
  have hst : (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P _ _ hchar _ st hone]
  rw [labelRLC_eval (nextReader (F := F)) _ _
    (pubAt P (walkView11 c) (familyQm P (walkView11 c) Qm) ⟨(i : ℕ) + 1, hi⟩) (gamma c.1)
    (fun st' => by rw [rw_selNext, hsel_next P _ _ hchar i hi st hone st', hst])
    (fun k => by
      rw [rw_colNext P Qm c i _ (by fin_cases k <;> decide)]; exact next_cell P _ _ i hi k)
    (rw_gamma P Qm c i)]
  simp only [curV, curW, rowOf_succ P ((i : ℕ) + 1) hi]
  rfl

end Readers

/-! ## 9. The nine loud gates vanish on the re-walked rows -/

section Loud

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.RedTeam.Batch501

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)
  (hsatV : RAP.SatisfiesWithPreprocessing (P.memoryChipAt (walkView11 c))
    (familyQm P (walkView11 c) Qm)) (hchar : MemStateTagChar F)

theorem algebraMap_ite (p : Prop) [Decidable p] :
    algebraMap F K (if p then 1 else 0) = if p then 1 else 0 := by split_ifs <;> simp

include hsatV hchar in
/-- **The nine walk gates vanish on every re-walked row**, given the corrected completeness
premises at the view's operands and the order premise at `α`. -/
theorem loud_zero
    (hbft : IsForestFullBFT (curV P Qm c) (chldV P Qm c) (foV P Qm c) (kMemP P) (memRowsP P))
    (htile : kMemP P + Sf (foV P Qm c) (memRowsP P) = memRowsP P)
    (hvalid : BFSValidF (kMemP P) (foV P Qm c) (memRowsP P))
    (hα : alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent (memRowsP P))
    (hα0 : alphaM c.1 ≠ 0)
    (i : Fin (memRows P)) (g : MixedExpr F)
    (hg : g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis) (hq : quietM g = false) :
    g.eval (eKt P Qm c i) (eFt P Qm c i) = 0 := by
  obtain ⟨ln, count, acc, inv, hw, hacc0, hqueue, htl, hln, hcount, haccE, hinvE⟩ :=
    walkCompleteness12 (curV P Qm c) (chldV P Qm c) (foV P Qm c) (alphaM c.1) (kMemP P)
      (memRowsP P) (MemoryWalkDeployed.kMem_pos P) (MemoryWalkDeployed.kMem_le P) hbft htile
      hvalid hα hα0
  have eln : ln = lnOf (alphaM c.1) := funext hln
  have ecount : count = countOf (foV P Qm c) (alphaM c.1) (kMemP P) := funext hcount
  have eacc : acc = fun m => accInGate (curV P Qm c) (chldV P Qm c) (foV P Qm c) (alphaM c.1)
      (alphaM c.1 ^ kMemP P) (kMemP P) m := funext haccE
  have einv : inv = invOf (foV P Qm c) (alphaM c.1) (kMemP P) := funext hinvE
  subst eln ecount eacc einv
  -- the row values
  have tln : (eKt P Qm c i).trace lnRole = lnOf (alphaM c.1) ((i : ℕ) + 1) := rw_trace P Qm c i 0
  have tcount : (eKt P Qm c i).trace countRole =
      countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) := rw_trace P Qm c i 1
  have tacc : (eKt P Qm c i).trace accRole = accInGate (curV P Qm c) (chldV P Qm c) (foV P Qm c)
      (alphaM c.1) (alphaM c.1 ^ kMemP P) (kMemP P) ((i : ℕ) + 1) := rw_trace P Qm c i 2
  have tinv : (eKt P Qm c i).trace walkInvRole =
      invOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) := rw_trace P Qm c i 3
  have hchal3 : (eKt P Qm c i).chal 3 = alphaM c.1 := envK_alpha P (forget12 c) _ i
  have h4 := rw_mask4 P Qm c hsatV i
  have h5 := rw_mask5 P Qm c hsatV i
  have hn := memRows_pos P
  obtain ⟨k, hk, hkg, hpos⟩ := loud_pos P.optimized.basis g hg hq
  subst hkg
  rcases hpos with ⟨h27, h34⟩ | h47 | h48
  · interval_cases k
    · -- 27: `first · (ln − α)`
      show (MixedExpr.Scale (bcur 4) (ofExpr (Trans.walkLn1.subst walkBoundarySubst)) :
        MixedExpr F).eval _ _ = 0
      rw [walkLn1InGate_eval, h4, tln, hchal3]
      by_cases h0 : (i : ℕ) = 0
      · simp [h0, lnOf]
      · simp [h0]
    · -- 28: `first · (count − ic·cm)`
      show (walkCount1InGate (F := F)).eval _ _ = 0
      rw [walkCount1InGate_eval, h4, tcount, rw_pub0, rw_selectorCM_cur P Qm c hsatV hchar i]
      by_cases h0 : (i : ℕ) = 0
      · simp only [h0, if_true, map_one, one_mul, countOf, zero_add, Sf_one]
        ring
      · simp [h0]
    · -- 29: `first · (acc − ic·cc)`
      show (walkAccInitInGate (F := F)).eval _ _ = 0
      rw [walkAccInitInGate_eval, h4, tacc, rw_pub0, rw_childSum_cur P Qm c hsatV hchar i]
      by_cases h0 : (i : ℕ) = 0
      · simp only [h0, if_true, map_one, one_mul, zero_add]
        rw [hw.accInit, Finset.mul_sum, sub_eq_zero]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      · simp [h0]
    · -- 30: `notLast · (ln' − α·ln)`
      show (MixedExpr.Scale (.sub (.const 1) (bcur 5))
        (ofExpr (Trans.walkLnStep.subst walkSubst)) : MixedExpr F).eval _ _ = 0
      rw [walkLnStepInGate_eval, h5, tln, hchal3]
      by_cases hl : (i : ℕ) + 1 = memRows P
      · simp [hl]
      · have hi : (i : ℕ) + 1 < memRows P := by have := i.isLt; omega
        rw [show lnRole = walkRoleOf 0 from rfl, rw_traceNext P Qm c i hi 0]
        simp only [hl, if_false, sub_zero, map_one, one_mul]
        show lnOf (alphaM c.1) ((i : ℕ) + 2) - alphaM c.1 * lnOf (alphaM c.1) ((i : ℕ) + 1) = 0
        simp only [lnOf]; ring
    · -- 31: `notLast · (count' − count·cm')`
      show (walkCountStepInGate (F := F)).eval _ _ = 0
      rw [walkCountStepInGate_eval, h5, tcount]
      by_cases hl : (i : ℕ) + 1 = memRows P
      · simp [hl]
      · have hi : (i : ℕ) + 1 < memRows P := by have := i.isLt; omega
        rw [show countRole = walkRoleOf 1 from rfl, rw_traceNext P Qm c i hi 1,
          rw_selectorCM_next P Qm c hsatV hchar i hi]
        simp only [hl, if_false, sub_zero, map_one, one_mul]
        show countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 2) -
          countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) *
            alphaM c.1 ^ foV P Qm c ((i : ℕ) + 2) = 0
        simp only [countOf, show (i : ℕ) + 2 = (i : ℕ) + 1 + 1 from rfl, Sf_succ, pow_add]
        ring
    · -- 32: `dequeue·ln'·cur' + notLast·(Δacc − count·cc')`
      show (walkAccStepInGate (F := F)).eval _ _ = 0
      rw [walkAccStepInGate_eval, h5, tacc, tcount]
      by_cases hl : (i : ℕ) + 1 = memRows P
      · simp [hl, MemoryWalkLabel.dequeueMaskCol, rw_mask154_last P Qm c hsatV i hl]
      · have hi : (i : ℕ) + 1 < memRows P := by have := i.isLt; omega
        rw [show lnRole = walkRoleOf 0 from rfl, show accRole = walkRoleOf 2 from rfl,
          rw_traceNext P Qm c i hi 0, rw_traceNext P Qm c i hi 2,
          show MemoryWalkLabel.dequeueMaskCol = 154 from rfl, rw_mask154 P Qm c hsatV i hi,
          rw_label_next P Qm c hsatV hchar i hi, rw_childSum_next P Qm c hsatV hchar i hi]
        simp only [hl, if_false, sub_zero, map_one, one_mul]
        have hstep := hw.accStep ((i : ℕ) + 1) (by omega) (by omega)
        show deqCoeff (K := K) (kMem P) ((i : ℕ) + 2) *
              (lnOf (alphaM c.1) ((i : ℕ) + 2) * curV P Qm c ((i : ℕ) + 2)) +
            (accInGate (curV P Qm c) (chldV P Qm c) (foV P Qm c) (alphaM c.1)
                (alphaM c.1 ^ kMemP P) (kMemP P) ((i : ℕ) + 2) -
              accInGate (curV P Qm c) (chldV P Qm c) (foV P Qm c) (alphaM c.1)
                (alphaM c.1 ^ kMemP P) (kMemP P) ((i : ℕ) + 1) -
              countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) *
                ∑ l ∈ Finset.Icc 1 (foV P Qm c ((i : ℕ) + 2)),
                  alphaM c.1 ^ l * chldV P Qm c ((i : ℕ) + 2) l) = 0
        rw [Finset.mul_sum]
        have e : (∑ l ∈ Finset.Icc 1 (foV P Qm c ((i : ℕ) + 2)),
            countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) *
              (alphaM c.1 ^ l * chldV P Qm c ((i : ℕ) + 2) l)) =
            ∑ l ∈ Finset.Icc 1 (foV P Qm c ((i : ℕ) + 1 + 1)),
              alphaM c.1 ^ l * countOf (foV P Qm c) (alphaM c.1) (kMemP P) ((i : ℕ) + 1) *
                chldV P Qm c ((i : ℕ) + 1 + 1) l :=
          Finset.sum_congr rfl fun l _ => by ring
        rw [e, ← hstep]
        simp only [lnOf]
        ring
    · -- 33: `last · acc`
      show (walkTerminal (F := F)).eval _ _ = 0
      simp only [walkTerminal, MixedExpr.eval, CoeffExpr.eval, bcur]
      rw [h5, show (33 : ℕ) = accRole from rfl, tacc]
      by_cases hl : (i : ℕ) + 1 = memRows P
      · simp only [hl, if_true, map_one, one_mul]; exact hacc0
      · simp [hl]
  · -- 47: `notLast · (inv·(count − ln) − 1)`
    subst h47
    show (walkQueueNonEmpty (F := F)).eval _ _ = 0
    rw [MemoryWalkLabel.walkQueueNonEmpty_eval, h5, tinv, tcount, tln]
    by_cases hl : (i : ℕ) + 1 = memRows P
    · simp [hl]
    · have hi : (i : ℕ) + 1 < memRows P := by have := i.isLt; omega
      simp only [hl, if_false, sub_zero, map_one, one_mul]
      rw [hqueue ((i : ℕ) + 1) (by omega) hi, sub_self]
  · -- 48: `last · (count − ln)`
    subst h48
    show (walkQueueTiling (F := F)).eval _ _ = 0
    rw [MemoryWalkLabel.walkQueueTiling_eval, h5, tcount, tln]
    by_cases hl : (i : ℕ) + 1 = memRows P
    · simp only [hl, if_true, map_one, one_mul]; rw [htl, sub_self]
    · simp [hl]

end Loud

/-! ## 10. **`memory_satisfies_at_alpha`** -/

section Main

open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.RedTeam.Batch501

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- Summands 14 and 15 of the twelve-coin event: `α ≠ 0` and `α ∉ TimestampCollisionEvent M`. -/
theorem alpha_order_of_good (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    alphaM c.1 ≠ 0 ∧
      alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent (memRowsP P) := by
  have hn := Pkg12.notMem_consumedFailureEvent12 P (truncQc P Qc) Qm c hgood
  have h14 := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h15 := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨fun h0 => h14 ?_, h15⟩
  rw [OptimizedFailureEventEv.mem_alphaZeroEvent_iff]; exact h0

/-- **The landed memory chip at `forget12 c` (walk coin `α`, the timestamp coin)
accepts the re-walked trace `reWalk P Qm c`**, from the parallel acceptance and
`c ∉ consumedFailureEvent309` alone: the forest facts come from summands 7, 9, 10 at the view
; the order premise of the corrected completeness lemma is summand 15,
`α ≠ 0` is summand 14.  The forty-one quiet mixed gates and the base bucket move from the view
(`mixed_census`, `base_quiet`); the nine walk gates are re-checked (`loud_zero`). -/
theorem memory_satisfies_at_alpha (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt (forget12 c))
      (familyQm P (forget12 c) (reWalk P Qm c)) := by
  have hchar : MemStateTagChar F := Nock.RedTeam.Batch824.memStateTagChar_of_package P
  have hsatV := memSat_at_view P Qc Qm c hacc
  obtain ⟨htile, hvalid, _, _⟩ := forest_at_view P Qc Qm c hacc hgood hchar
  have hbft := view_isForestFullBFT P Qc Qm c hacc hgood hchar
  obtain ⟨hα0, hα⟩ := alpha_order_of_good P Qc Qm c hgood
  refine memory_transfer P (walkView11 c) (forget12 c) (familyQm P (walkView11 c) Qm)
    (familyQm P (forget12 c) (reWalk P Qm c)) hsatV ?_ (chal_view_agree P c) (pub_view_agree P c) ?_
  · intro j hj
    rw [projAt_apply, projAt_apply, reWalk_off P Qm c _ hj]
  · intro i g hg hq
    exact loud_zero P Qm c hsatV hchar hbft htile hvalid hα hα0 i g hg hq

end Main

end

end Nock.NockVMROM.Thm54.PartAReWalk
