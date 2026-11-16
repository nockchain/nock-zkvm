/-
  Nock/RedTeam/Batch4880Thm54J9ACompX9.lean

* `srcX9` / `gatesHX9_src`: the twin's compiled gates are the coordinate expansions of its source gates
    (`CompX.SG`, `expandS`, `srcOK` reused verbatim).
  * `checkCompX9` (computable): every source gate at every row, read through `Env.viaPerm permX9` (the RAP's
    gates are `renC permX9` of the twin's: `ChipHX9.gatesHX9P_eval`), and the two mask columns `17`, `18`
    (fixed by `permX9`).
  * **`computeChipX9_iff`**: `SatisfiesWithPreprocessing (computeChipVCLHX9 …) P ↔ checkCompX9 T = true` for an
    injective, `ω`-adjacent table whose trace is the row interpolants.
  * `liftX9 q`: a J-8 compute table (123 columns) lifted to the twin's RAP order — twin columns `0..68` and `69..122`
    copied (RAP `0..68`, `83..136`), the 14 new round-0 columns `123..136` (RAP `69..82`) all `0` (the new states
    `s0B s10B s10S` off).  `liftX9_old`: the lifted table read at `permX9 j` is the J-8 column `j`.
  * **`i9_X9 : checkCompX9 (tabX9A I9) = true`** (`decide +kernel`): the lifted demo row passes every twin gate
    at the J-9 publics `pubVJ9E` (the twin adds no gate that fires with the new state columns at `0`).
-/
import Nock.V1J9.CheckJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.RedTeam.Batch4810Thm54J9bNVData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4880

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (col0Id qGates)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (baseGatesFX9 slotPairsX9 walkGatesFX9 gatesHX9 gatesHX9P
  computeChipVCLHX9 permX9 renC Env.viaPerm gatesHX9P_eval)
open Nock.V1Check Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1J8.CompX (SG expandS srcOK srcOK_iff base_part mid_part walk_part firstMaskE lastMaskE ofFn_get_map
  mapC_id)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-! ## 1. Source gates of the twin -/

/-- **The twin's source gates**: base, the four `𝕂′` slot pairs, the 20-state walk gates (twin columns). -/
def srcX9 : List SG :=
  (baseGatesFX9 (F := ZMod p)).map SG.base ++
    (slotPairsX9 (ZMod p) deltaF).flatMap (fun q => [SG.mix q.1, SG.mix q.2]) ++
    (walkGatesFX9 (F := ZMod p)).map SG.mix

/-- **The twin's gate list is the expansion of its source gates.** -/
theorem gatesHX9_src : gatesHX9 powerBasis3 deltaF = srcX9.flatMap expandS := by
  unfold gatesHX9 srcX9
  rw [List.flatMap_append, List.flatMap_append, base_part, mid_part, walk_part]

/-- A row passes the RAP's (permuted) gates iff it passes every twin source gate read through `permX9`. -/
theorem rowOK9_iff (e : Env (ZMod p)) :
    srcX9.all (srcOK (Env.viaPerm permX9 e)) = true ↔ ∀ g ∈ gatesHX9P powerBasis3 deltaF, g.eval e = 0 := by
  rw [gatesHX9P_eval, gatesHX9_src, List.all_eq_true]
  simp only [List.mem_flatMap]
  constructor
  · rintro h g ⟨s, hs, hg⟩
    exact (srcOK_iff _ s).mp (h s hs) g hg
  · intro h s hs
    exact (srcOK_iff _ s).mpr fun g hg => h g ⟨s, hs, hg⟩

/-! ## 2. The twin table and its check -/

/-- **An executable twin compute table** (`137` columns, RAP order). -/
structure TabX9 (n : ℕ) where
  nodes : Fin n → ZMod p
  ω : ZMod p
  cols : ℕ → Fin n → ZMod p
  chal : ℕ → ZMod p
  pub : ℕ → ZMod p

/-- The table data with the RAP's (permuted) gates. -/
noncomputable def TabX9.toT {n : ℕ} (T : TabX9 n) : TableData (ZMod p) n :=
  ⟨137, T.nodes, T.ω, T.cols, gatesHX9P powerBasis3 deltaF, T.chal, T.pub,
    [(17, firstMaskE n), (18, lastMaskE n)]⟩

/-- The environment at row `i` (as `TableData.env`; computable). -/
def TabX9.env {n : ℕ} (T : TabX9 n) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < 137 then T.cols j i else 0
  traceNext := fun j => if j < 137 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩ else ∑ k, T.cols j k * lagW T.nodes (T.ω * T.nodes i) k)
    else 0
  chal := T.chal
  pub := T.pub

/-- The row environment of `T.toT` is that of `T` (definitionally). -/
theorem TabX9.env_eq {n : ℕ} (T : TabX9 n) (i : Fin n) : T.toT.env i = T.env i := rfl

/-- **The executable twin check**: every twin source gate at every row (through `permX9`); the two masks. -/
def checkCompX9 {n : ℕ} (T : TabX9 n) : Bool :=
  (List.finRange n).all (fun i => srcX9.all (srcOK (Env.viaPerm permX9 (T.env i)))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod p))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

/-- **The executable twin check is the table check**: `checkCompX9 T = true` iff `T.toT.checkTable = true`. -/
theorem checkCompX9_iff {n : ℕ} (T : TabX9 n) : checkCompX9 T = true ↔ T.toT.checkTable = true := by
  have key : ((List.finRange n).all fun i => srcX9.all (srcOK (Env.viaPerm permX9 (T.env i)))) = true ↔
      (T.toT.gates.all fun g => (List.finRange n).all fun i => decide (g.eval (T.toT.env i) = 0)) = true := by
    constructor
    · intro h
      refine List.all_eq_true.mpr fun g hg => List.all_eq_true.mpr fun i _ => decide_eq_true ?_
      exact (rowOK9_iff (T.env i)).mp (List.all_eq_true.mp h i (List.mem_finRange i)) g hg
    · intro h
      refine List.all_eq_true.mpr fun i _ => (rowOK9_iff (T.env i)).mpr fun g hg => ?_
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h g hg) i (List.mem_finRange i))
  unfold checkCompX9 TableData.checkTable
  rw [Bool.and_eq_true, Bool.and_eq_true, key]
  exact Iff.rfl

/-- **`computeChipX9_iff`: the J-9 A compute twin, finitely.** -/
theorem computeChipX9_iff {n h : ℕ} (T : TabX9 n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (computeChipVCLHX9 hn T.nodes powerBasis3 deltaF T.chal T.pub orbit).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn T.nodes powerBasis3 deltaF T.chal T.pub orbit) P ↔
      checkCompX9 T = true := by
  rw [checkCompX9_iff]
  refine satisfies_iff_checkTable (RingHom.id (ZMod p)) T.toT _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · show List.ofFn (fun i : Fin (gatesHX9P powerBasis3 deltaF).length =>
        coeffToMv T.chal T.pub ((gatesHX9P powerBasis3 deltaF).get i)) = _
    refine (ofFn_get_map (gatesHX9P powerBasis3 deltaF) _).trans ?_
    simp only [TabX9.toT, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, mapC_id]
    rfl
  · simp only [List.ofFn_succ, List.ofFn_zero, computeChipVCLHX9, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, TabX9.toT, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · show firstRowMask _ = _
      unfold firstRowMask
      congr 1
    · show lastRowMask hn _ = _
      unfold lastRowMask
      congr 1; funext i
      simp only [lastMaskE, Fin.ext_iff]
      have := i.2
      by_cases h : (i : ℕ) + 1 = n
      · simp [h]; omega
      · simp [h]; omega

/-! ## 3. Lifting a J-8 compute table to the twin -/

/-- The twin's RAP-order columns from J-8 columns: RAP `0..68` = J-8 `0..68`, RAP `69..82` = the new round-0
columns (`0`), RAP `83..136` = J-8 `69..122`. -/
def liftCols {n : ℕ} (cols : ℕ → Fin n → ZMod p) (c : ℕ) : Fin n → ZMod p :=
  if c < 69 then cols c else if c < 83 then fun _ => 0 else cols (c - 14)

/-- The lifted chip input (same height, rows, `ω`). -/
def liftX9 (q : ChipIn) : ChipIn := ⟨q.h, q.n, q.ω, liftCols q.cols⟩

/-- The lifted table read at `permX9 j` is the J-8 column `j` (`j < 123`). -/
theorem liftCols_perm {n : ℕ} (cols : ℕ → Fin n → ZMod p) (j : ℕ) (hj : j < 123) :
    liftCols cols (permX9 j) = cols j := by
  unfold liftCols permX9
  by_cases h1 : j < 69
  · simp [h1]
  · have h2 : ¬ j + 14 < 69 := by omega
    have h3 : ¬ j + 14 < 83 := by omega
    simp [h1, hj, h2, h3]

/-- The twin table of a J-8 input (the J-9 publics `pubVJ9E`). -/
def tabX9A (I : InJ8) : TabX9 I.X.n :=
  ⟨nodesOf I.X, I.X.ω.toZ, liftCols I.X.cols, fun j => (chalVJ8E I.χ j).toZ,
    Nock.V1J9.Check9.pubVJ9E I.c I.M.m I.M.ρ I.M.ρS I.χ⟩

open Nock.RedTeam.Batch4810 in
/-- **The lifted J-9 B demo row passes the twin** (kernel). -/
theorem i9_X9 : checkCompX9 (tabX9A I9) = true := by decide +kernel

end Nock.RedTeam.Batch4880

#print axioms Nock.RedTeam.Batch4880.gatesHX9_src
#print axioms Nock.RedTeam.Batch4880.computeChipX9_iff
#print axioms Nock.RedTeam.Batch4880.liftCols_perm
#print axioms Nock.RedTeam.Batch4880.i9_X9
