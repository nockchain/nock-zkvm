import Nock.NockVMROM.Thm54.VclL.Compute.ChipV
import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.VclL.Compute.CoordGatherQ7
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ComputeTree
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JoinUtil

/-!
# V4T item 2 : the hCF `tree` / `shape` / `tree_shape` / rounds at the VCL chip

.  The tree decoder of
`P8Core/SVWalk/ComputeTree.lean` (M0's package-free `computeTree` / `computeShape`, no Form R: it
reads the decoded row label and the round-0 carrier) instantiated at the VCL table:

* `tableVCLE hC` — the compute `TableSpec` (width `232`, `colRoundVCLE`);
* `envsV` — the gathered 309-shaped pull-back of every compute row (`RowDecode.pullEnv`);
* `treeV1` = `computeTree` over `envsV`; `shapeV1 V b` — read from the B0 columns ONLY, by type
  (`B0Cols F (tableVCLE hC)`): the base selectors `0..12` and the serial `220`
  (`selCol_round0`, `serialCol_round0`);
* **`treeV_shape`** : `shapeOfTree (treeV …) = shapeV V (b0 Q)` (the frame's `tree_shape`);
  **`shapeV_size_le`** (`shape_size`); **`treeV_round`** at `treeRound := 2` (every column is
  round `≤ 2`, `colRoundVCLE_le_two`; the tree depends on the trace and the challenge / public maps
  only).
* **** the frame's `treeV` / `shapeV` are `treeV1` / `shapeV1` relabelled
  by `(st, S) ↦ (st, 2·S)`: the carrier is `2 · serial`, addresses `2i+2` (OP0 read) / `2i+3` (OP9
  arm); the frame's `tree_shape` / `shape_size` / `tree_round` hold at the relabelled objects, and every
  node label is even (`treeV_label_even`).

The tree is generic in the fingerprint field: `computeTree` is stated over any `K`; the instance here
is pre-tower (fingerprints in the chip's `K`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module Nock.Walk
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open scoped Polynomial

noncomputable section

/-- **The VCL compute table** at height `hC`. -/
def tableVCLE (hC : ℕ) : TableSpec where
  width := 232
  colRound := fun j => colRoundVCLE j
  height := hC

theorem colRoundVCLE_le_two : ∀ c : Fin 232, colRoundVCLE c ≤ 2 := by
  unfold colRoundVCLE colRoundVCL RepartitionedStaging.newComputeColRound; decide +kernel

theorem selCol_round0 (k : ℕ) (hk : k < 13) : colRoundVCLE k = 0 := by
  interval_cases k <;> decide

theorem serialCol_round0 : colRoundVCLE 220 = 0 := by decide

/-- **A table wide enough to carry the VCL compute layout** (GEN-C4 width generalization): width at
least `232`, agreeing with `colRoundVCLE` on the first `232` columns, every column in a round
`≤ 2`.  `tableVCLE hC` is one (the instance below); the 409-wide tower table is another.  A class,
so every statement below reads at `tableVCLE hC` by instance search. -/
class WideTable (T : TableSpec) : Prop where
  hw : 232 ≤ T.width
  agree : ∀ (c : ℕ) (hc : c < 232), T.colRound ⟨c, lt_of_lt_of_le hc hw⟩ = colRoundVCLE c
  le_two : ∀ j : Fin T.width, T.colRound j ≤ 2

instance tableVCLE_wide (hC : ℕ) : WideTable (tableVCLE hC) where
  hw := by simp [tableVCLE]
  agree := fun c hc => rfl
  le_two := fun j => colRoundVCLE_le_two j

/-- A B0 column of a wide table (a round-0 column below `232`). -/
def b0ColT {T : TableSpec} [hT : WideTable T] (c : ℕ) (hc : c < 232) (h0 : colRoundVCLE c = 0) :
    {j : Fin T.width // T.colRound j = 0} :=
  ⟨⟨c, lt_of_lt_of_le hc hT.hw⟩, by rw [hT.agree c hc]; exact h0⟩

section tree
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [DecidableEq K']
  (G : WalkQ7.CoordGather F K') {T : TableSpec} {w : ℕ}

/-- **The gathered pull-back of compute row `i`, at any gather** (GEN-C2: the frame `V` fixes the
rows, the gather `G` reads the `K'`-valued side of the physical row). -/
def envsVG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) (i : Fin V.N) :
    CorrectedFinalTypedEnv F K' :=
  (G.env309 (pullEnv (envOfTrace Q V.orbitC.ω (V.computeNodes i) chalV pubVal))).base

/-- The `ln`-patched row at the gather. -/
def envsPG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) (i : Fin V.N) :
    CorrectedFinalTypedEnv F K' :=
  lnPatch (envsVG G V chalV pubVal Q i)

@[simp] theorem envsPG_baseTrace (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (i : Fin V.N) : (envsPG G V chalV pubVal Q i).baseTrace = (envsVG G V chalV pubVal Q i).baseTrace := rfl

@[simp] theorem envsPG_expCol (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (i : Fin V.N) : (envsPG G V chalV pubVal Q i).expCol = (envsVG G V chalV pubVal Q i).expCol := rfl

/-- The serial-labelled tree at the gather. -/
def treeV1G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    NTree ((State × DTcomp K') × ℕ) :=
  computeTree V.hN (envsPG G V chalV pubVal Q)

/-- A B0 column of the VCL table. -/
def b0Col (hC : ℕ) (c : ℕ) (hc : c < 232) (h0 : colRoundVCLE c = 0) :
    {j : Fin (tableVCLE hC).width // (tableVCLE hC).colRound j = 0} :=
  ⟨⟨c, hc⟩, h0⟩

/-- The serial-labelled shape, from the B0 columns only (by type), at the gather's field. -/
def shapeV1G (_G : WalkQ7.CoordGather F K') [hT : WideTable T] (V : VerifierData F K hC S) (b : B0Cols F T) :
    NTree (State × ℕ) :=
  shapeOfRows
    (at1 V.hN fun i => stateOfBase (fun k => if h : k < 13 then
      (b (b0ColT k (by omega) (selCol_round0 k h))).eval (V.computeNodes i) else 0))
    (at1 V.hN fun i => RecordCarrier.natLift (algebraMap F K'
      ((b (b0ColT 220 (by norm_num) serialCol_round0)).eval (V.computeNodes i))))
    V.N

theorem envsVG_base [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (k : ℕ) (hk : k < 13) :
    (envsVG G V chalV pubVal Q i).baseTrace ⟨k, hk⟩ = (Q ⟨k, by have := hT.hw; omega⟩).eval (V.computeNodes i) := by
  change (G.env309 (pullEnv (envOfTrace Q V.orbitC.ω (V.computeNodes i) chalV pubVal))).base.baseTrace ⟨k, hk⟩ = _
  rw [G.base_eq, pullEnv_trace_lt _ k (by omega)]
  simp [envOfTrace, show k < T.width by have := hT.hw; omega]

theorem envsVG_expCol [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) : (envsVG G V chalV pubVal Q i).expCol = (Q ⟨220, by have := hT.hw; omega⟩).eval (V.computeNodes i) := by
  change (G.env309 (pullEnv (envOfTrace Q V.orbitC.ω (V.computeNodes i) chalV pubVal))).base.expCol = _
  rw [G.expCol_eq]
  simp [pullEnv, vclCol, serialCol, envOfTrace, show 220 < T.width by have := hT.hw; omega]

/-- `tree_shape` at the serial carrier, at the gather. -/
theorem treeV1G_shape [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X]) :
    shapeOfTree (treeV1G G V chalV pubVal Q) = shapeV1G G V (b0 (T := T) Q) := by
  unfold treeV1G
  rw [computeTree_shape]
  unfold computeShape shapeV1G
  have hs : ∀ j : Fin V.N, (stateOfBase fun k => if h : k < 13 then (envsPG G V chalV pubVal Q j).baseTrace ⟨k, h⟩ else 0) =
      stateOfBase (fun k => if h : k < 13 then
        (b0 (T := T) Q (b0ColT k (by omega) (selCol_round0 k h))).eval (V.computeNodes j) else 0) := by
    intro j; congr 1; funext k; split_ifs with hk
    · exact envsVG_base G V chalV pubVal Q j k hk
    · rfl
  have hc : ∀ j : Fin V.N, rowCarrier (envsPG G V chalV pubVal Q j) = RecordCarrier.natLift (algebraMap F K'
      ((b0 (T := T) Q (b0ColT 220 (by norm_num) serialCol_round0)).eval (V.computeNodes j))) := by
    intro j
    show RecordCarrier.natLift (algebraMap F K' (envsPG G V chalV pubVal Q j).expCol) = _
    rw [envsPG_expCol, envsVG_expCol G]; rfl
  congr 1
  · funext i; unfold at1; split_ifs <;> exact hs _
  · funext i; unfold at1; split_ifs <;> exact hc _

/-- `shape_size` at the serial carrier. -/
theorem shapeV1G_size_le [hT : WideTable T] (V : VerifierData F K hC S) (b : B0Cols F T) :
    (shapeV1G G V b).size ≤ V.N :=
  shapeOfRows_size_le _ _ _ V.hN

/-- `tree_round` at `treeRound := 2` (the tree depends on the trace and the coin / public maps only). -/
theorem treeV1G_round [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q Q' : Fin T.width → F[X])
    (hQ : ∀ j : Fin T.width, T.colRound j ≤ 2 → Q j = Q' j) :
    treeV1G G V chalV pubVal Q = treeV1G G V chalV pubVal Q' := by
  have : Q = Q' := funext fun j => hQ j (hT.le_two j)
  rw [this]

end tree

section treeOld
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- The gathered pull-back of compute row `i` (3-limb gather; `rfl` at `envsVG (ofBasis V.basis)`). -/
def envsV (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) (i : Fin V.N) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv V.basis
    (pullEnv (envOfTrace Q V.orbitC.ω (V.computeNodes i) chalV pubVal))

theorem envsV_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) : envsV V chalV pubVal Q i = envsVG (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q i := rfl

def envsP (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) (i : Fin V.N) :
    CorrectedFinalTypedEnv F K :=
  lnPatch (envsV V chalV pubVal Q i)

theorem envsP_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) : envsP V chalV pubVal Q i = envsPG (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q i := rfl

@[simp] theorem envsP_baseTrace (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) : (envsP V chalV pubVal Q i).baseTrace = (envsV V chalV pubVal Q i).baseTrace := rfl

@[simp] theorem envsP_expCol (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) : (envsP V chalV pubVal Q i).expCol = (envsV V chalV pubVal Q i).expCol := rfl

/-- The serial-labelled tree: M0's `computeTree` over the (`ln`-patched) VCL rows (carrier = the
serial). -/
def treeV1 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    NTree ((State × DTcomp K) × ℕ) :=
  computeTree V.hN (envsP V chalV pubVal Q)

theorem treeV1_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    treeV1 V chalV pubVal Q = treeV1G (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q := rfl

/-- The serial-labelled shape, from the B0 columns only (by type): base selectors and the serial. -/
def shapeV1 (V : VerifierData F K hC S) (b : B0Cols F (tableVCLE hC)) : NTree (State × ℕ) :=
  shapeV1G (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V b

theorem envsV_base (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) (k : ℕ) (hk : k < 13) :
    (envsV V chalV pubVal Q i).baseTrace ⟨k, hk⟩ = (Q ⟨k, by omega⟩).eval (V.computeNodes i) :=
  envsVG_base (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q i k hk

theorem envsV_expCol (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) : (envsV V chalV pubVal Q i).expCol = (Q ⟨220, by norm_num⟩).eval (V.computeNodes i) :=
  envsVG_expCol (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q i

/-- `tree_shape` at the serial carrier. -/
theorem treeV1_shape (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    shapeOfTree (treeV1 V chalV pubVal Q) = shapeV1 V (b0 (T := tableVCLE hC) Q) :=
  treeV1G_shape (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q

/-- `shape_size` at the serial carrier. -/
theorem shapeV1_size_le (V : VerifierData F K hC S) (b : B0Cols F (tableVCLE hC)) :
    (shapeV1 V b).size ≤ V.N :=
  shapeV1G_size_le (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V b

/-- **`tree_round` at `treeRound := 2`**. -/
theorem treeV1_round (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q Q' : Fin 232 → F[X])
    (hQ : ∀ j : Fin 232, colRoundVCLE j ≤ 2 → Q j = Q' j) :
    treeV1 V chalV pubVal Q = treeV1 V chalV pubVal Q' :=
  treeV1G_round (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q Q' hQ

end treeOld

/-! The frame reads the key / axis oracles of a node labelled `S` at exactly `S + 2` (the OP0 read) and
`S + 3` (the OP9 arm).  At the serial carrier those address sets collide across adjacent rows
(`KeysQ7.keyOf_forces_collision`); **the carrier is `2 · serial`**, so row `i` owns the addresses
`2i + 2` / `2i + 3` (`KeysQ7.stride2_disjoint`). -/

/-- Relabelling twice is relabelling once (`ForestExponentWindow.mapNTree_comp`'s proof). -/
theorem mapNTree_comp' {A B C : Type} (f : A → B) (g : B → C) (t : NTree A) :
    mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t := by
  let P := fun t : NTree A => mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih
    simp only [P, mapNTree, List.map_map]
    refine congrArg (NTree.node (g (f lbl))) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

section tree2
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [DecidableEq K']
  (G : WalkQ7.CoordGather F K') {T : TableSpec} {w : ℕ}

/-- **The hCF `tree` at the gather**: `treeV1G` with the carrier doubled (node labels `2 · serial`). -/
def treeVG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    NTree ((State × DTcomp K') × ℕ) :=
  mapNTree (fun l => (l.1, 2 * l.2)) (treeV1G G V chalV pubVal Q)

/-- **The hCF `shape`** at the gather's field. -/
def shapeVG [hT : WideTable T] (V : VerifierData F K hC S) (b : B0Cols F T) : NTree (State × ℕ) :=
  mapNTree (fun l => (l.1, 2 * l.2)) (shapeV1G G V b)

theorem treeVG_shape [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X]) :
    shapeOfTree (treeVG G V chalV pubVal Q) = shapeVG G V (b0 (T := T) Q) := by
  unfold treeVG shapeVG shapeOfTree
  rw [← treeV1G_shape G, shapeOfTree, mapNTree_comp', mapNTree_comp']

theorem shapeVG_size_le [hT : WideTable T] (V : VerifierData F K hC S) (b : B0Cols F T) :
    (shapeVG G V b).size ≤ V.N := by
  unfold shapeVG; rw [size_mapNTree']; exact shapeV1G_size_le G V b

theorem treeVG_round [hT : WideTable T] (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q Q' : Fin T.width → F[X])
    (hQ : ∀ j : Fin T.width, T.colRound j ≤ 2 → Q j = Q' j) :
    treeVG G V chalV pubVal Q = treeVG G V chalV pubVal Q' := by
  unfold treeVG; rw [treeV1G_round G V chalV pubVal Q Q' hQ]

/-- Every node of `treeVG` carries an even label `2 · i`. -/
theorem treeVG_label_even (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (u : NTree ((State × DTcomp K') × ℕ)) (hu : InTree (treeVG G V chalV pubVal Q) u) :
    ∃ i, u.label.2 = 2 * i := by
  have key : ∀ (t : NTree ((State × DTcomp K') × ℕ)) (u : NTree ((State × DTcomp K') × ℕ)),
      InTree (mapNTree (fun l : (State × DTcomp K') × ℕ => (l.1, 2 * l.2)) t) u →
      ∃ i, u.label.2 = 2 * i := by
    intro t
    let P := fun t : NTree ((State × DTcomp K') × ℕ) => ∀ u,
      InTree (mapNTree (fun l : (State × DTcomp K') × ℕ => (l.1, 2 * l.2)) t) u →
      ∃ i, u.label.2 = 2 * i
    change P t
    apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
    · intro lbl children ih u hu
      simp only [mapNTree] at hu
      cases hu with
      | here => exact ⟨lbl.2, rfl⟩
      | sub hc hrec =>
          obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
          exact ih c0 hc0 u hrec
    · intro c hc; simp at hc
    · intro head tail ihHead ihTail c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ihHead
      · exact ihTail c hc
  exact key _ u hu

end tree2

section tree2Old
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- **The hCF `tree`**: `treeV1` with the carrier doubled (node labels `2 · serial`). -/
def treeV (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    NTree ((State × DTcomp K) × ℕ) :=
  mapNTree (fun l => (l.1, 2 * l.2)) (treeV1 V chalV pubVal Q)

theorem treeV_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    treeV V chalV pubVal Q = treeVG (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q := rfl

/-- **The hCF `shape`**: `shapeV1` with the carrier doubled (B0 by type, as `shapeV1`). -/
def shapeV (V : VerifierData F K hC S) (b : B0Cols F (tableVCLE hC)) : NTree (State × ℕ) :=
  mapNTree (fun l => (l.1, 2 * l.2)) (shapeV1 V b)

/-- **`tree_shape`** at the VCL table (stride-2 carrier). -/
theorem treeV_shape (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    shapeOfTree (treeV V chalV pubVal Q) = shapeV V (b0 (T := tableVCLE hC) Q) :=
  treeVG_shape (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q

/-- **`shape_size`**: the label value never enters the size. -/
theorem shapeV_size_le (V : VerifierData F K hC S) (b : B0Cols F (tableVCLE hC)) :
    (shapeV V b).size ≤ V.N :=
  shapeVG_size_le (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V b

/-- **`tree_round` at `treeRound := 2`** (stride-2 carrier). -/
theorem treeV_round (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q Q' : Fin 232 → F[X])
    (hQ : ∀ j : Fin 232, colRoundVCLE j ≤ 2 → Q j = Q' j) :
    treeV V chalV pubVal Q = treeV V chalV pubVal Q' :=
  treeVG_round (T := tableVCLE hC) (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q Q' hQ

/-- Every node of `treeV` carries an even label `2 · i`. -/
theorem treeV_label_even (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u) :
    ∃ i, u.label.2 = 2 * i :=
  treeVG_label_even (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q u hu

end tree2Old

end

end VclL.Compute
end Nock.NockVMROM.Thm54
