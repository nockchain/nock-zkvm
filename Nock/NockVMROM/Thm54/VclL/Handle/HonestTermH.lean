/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestTermH.lean

  Additive.

  Over the honest datum `H` with `H.d = demandH2 rows` (`rows` the run's BFS rows):
  * the honest cell multiplicity `mhvH = mhH2` (compute + walk consumers) and child handles `kLvH …`
    (`HonestKeysH`);
  * `yHVS`: the walk's handle export-consume total `Σ_j 1 / recDen (expKey node_j)`;
  * `accSumX_eq` / `accSumP_eq`: the compute terminals `ρ₃ = accSumX`, `ρ₄ = accSumP` are the consumed
    totals over the run's rows (`consumedH2`, `consEntriesAll`);
  * `hpubX_honest`: `yH = Σ 1 / dX` (identification 2);
  * `hpubP_honest`: `Re ρ₄ = Σ mL / dL + mR / dR` (identification 3 + `compute_walk_balance`);
  * `hpubC_honest`: `Re ρ₃ + yH = Σ mh / den` (identification 1 + `export_total_link2`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestKeysH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Compute-side sums over the BFS rows -/

section Sums
variable {Kg : Type} [Field Kg]

theorem sum_flatMap_map {α β M : Type} [AddCommMonoid M] (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A sum over the chip rows `wRows W 0 … wRows W (|W| − 1)` is a sum over the forest's labels. -/
theorem sum_wRows {M : Type} [AddCommMonoid M] (W : List (NTree (GenComputeRow Kg))) (g : RowN → M) :
    ∑ j ∈ Finset.range W.length, g (wRows W j) =
      (W.map fun u => g (rowOfSkelH u.label.skel)).sum := by
  induction W with
  | nil => simp
  | cons a W ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have hs : ∀ j, wRows (a :: W) (j + 1) = wRows W j := by intro j; simp [wRows, rowAtW]
    have h0 : wRows (a :: W) 0 = rowOfSkelH a.label.skel := by simp [wRows, rowAtW]
    simp only [hs, ih, h0, List.map_cons, List.sum_cons]
    exact add_comm _ _

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

/-- **`ρ₃` is the compute side's consumed export total over the run's rows.** -/
theorem accSumX_eq (b : Basis (Fin 3) F K) (cells : List Noun) (chalV : ℕ → F)
    (t : NTree (GenComputeRow Kg)) :
    accSumX b cells (wRows (bfsForest [airReorder t])) chalV (bfsForest [airReorder t]).length =
      (((bfsRows (airReorder t)).flatMap fun g =>
          (exportEntries (rowOfSkelH g.skel)).map (entryRec (F := F) cells)).map fun k =>
        (recDen (limbVal b chalV ChipH.chalRhoL) (limbVal b chalV ChipH.chalGammaL) k)⁻¹).sum := by
  unfold accSumX
  refine (sum_wRows (bfsForest [airReorder t]) (fun r => ((exportEntries r).map fun x =>
    (recDen (limbVal b chalV ChipH.chalRhoL) (limbVal b chalV ChipH.chalGammaL)
      (entryRec (F := F) cells x))⁻¹).sum)).trans ?_
  rw [sum_flatMap_map, bfsRows, List.map_map]
  congr 1
  refine List.map_congr_left fun u _ => ?_
  simp [List.map_map, Function.comp_def]

/-- **`ρ₄` is the compute side's consumed path total over the run's rows.** -/
theorem accSumP_eq (b : Basis (Fin 3) F K) (cells : List Noun) (chalV : ℕ → F)
    (t : NTree (GenComputeRow Kg)) :
    accSumP b cells (wRows (bfsForest [airReorder t])) chalV (bfsForest [airReorder t]).length =
      ((consEntriesAll (bfsRows (airReorder t))).map fun x =>
        (recDenP (limbVal b chalV ChipH.chalRhoL) (limbVal b chalV ChipH.chalGammaL) (entRecP (F := F) cells x))⁻¹).sum := by
  unfold accSumP consEntriesAll
  refine (sum_wRows (bfsForest [airReorder t]) (fun r => ((consEntries (hn r)).map fun x =>
    (recDenP (limbVal b chalV ChipH.chalRhoL) (limbVal b chalV ChipH.chalGammaL)
      (entRecP (F := F) cells x))⁻¹).sum)).trans ?_
  rw [sum_flatMap_map, bfsRows, List.map_map]
  rfl

end Sums

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]

theorem limb_rhoL (b : Basis (Fin 3) F K) (χ : Coins frameVS K) : limbVal b (chalVH b χ) ChipH.chalRhoL = χ cRhoH := by
  have := limb_chalVH b χ 1 (by norm_num)
  simpa [coinH, ChipH.chalRhoL] using this

theorem limb_gammaL (b : Basis (Fin 3) F K) (χ : Coins frameVS K) : limbVal b (chalVH b χ) ChipH.chalGammaL = χ cGamH := by
  have := limb_chalVH b χ 0 (by norm_num)
  simpa [coinH, ChipH.chalGammaL] using this

end Coins

/-! ## 2. The honest values and the three terminals -/

section Terminals
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **The honest cell multiplicity column** (`mh`, col 129): `mhH2` of the row's noun. -/
def mhvH (rows : List (GenComputeRow Kg)) (i : Fin (H.V.memRows (tCW hT hP))) : F :=
  ((mhH2 (F := F) rows (H.d.cells.getD i (.atom 0)) : ℕ) : F)

/-- **The honest walk export-consume total** `yH`. -/
def yHVS (χ : Coins frameVS K) : K :=
  ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
    (recDen (χ cRhoH) (χ cGamH) (expKey (F := F) H.d.cells (wLbl H j).node))⁻¹

theorem sum_walkRows {M : Type} [AddCommMonoid M] (f : WN → M) :
    ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)), f (wLbl H j) =
      ((walkRows H.d.cells H.d.preads).map fun w => f w.label).sum := by
  rw [H.hW0]
  exact sum_range_getD (walkRows H.d.cells H.d.preads) (trie (.atom 0) (.atom 0) [] []) (fun w => f w.label)

/-- **`hpubX` at the honest values.** -/
theorem hpubX_honest (χ : Coins frameVS K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) :
    pubsWH δF ρ y (yHVS H χ) WalkHC.pubX = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y (yHVS H χ)) (walkColVS H χ)
        (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.xKeyH j)⁻¹ := by
  simp only [pubsWH, if_true]
  unfold yHVS
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [WalkTraceH.dN, dif_pos hj']
  rw [(walk_dRow_honest H χ _ ⟨j, hj'⟩).1]

/-- **`hpubP` at the honest values**, given the compute path terminal `Re ρ₄ = accSumP`. -/
theorem hpubP_honest (χ : Coins frameVS K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (yH : K) {t : NTree (GenComputeRow Kg)} (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hsem : ∀ g ∈ bfsRows (airReorder t), (rowOfSkel g.skel).Sem)
    (hρ4 : Quad.re _ (ρ 4) = accSumP H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH H.V.basis χ) (bfsForest [airReorder t]).length) :
    pubsWH δF ρ y yH WalkHC.pubP = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (algebraMap F K (WalkTraceH.cN j (walkColVS H χ WChip.mL)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) (walkColVS H χ)
            (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.recLH j)⁻¹ +
        algebraMap F K (WalkTraceH.cN j (walkColVS H χ WChip.mR)) *
          (WalkTraceH.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) (pubsWH δF ρ y yH) (walkColVS H χ)
            (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.recRH j)⁻¹) := by
  have hP : pubsWH δF ρ y yH WalkHC.pubP = Quad.re _ (ρ 4) := by
    simp [pubsWH, WalkHC.pubP, WalkHC.pubX]
  rw [hP, hρ4, accSumP_eq, limb_rhoL, limb_gammaL]
  have hcw := compute_walk_balance (F := F) (fun k => (recDenP (χ cRhoH) (χ cGamH) k)⁻¹) H.d.cells
    (bfsRows (airReorder t)) hsem
  have hpre : walkReadsH (bfsRows (airReorder t)) = H.d.preads := by rw [hd]; rfl
  rw [hcw, hpre, ← sum_walkRows H (fun w => provH (fun k => (recDenP (χ cRhoH) (χ cGamH) k)⁻¹) H.d.cells w)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  obtain ⟨-, eL, eR⟩ := walk_dRow_honest H χ (pubsWH δF ρ y yH) ⟨j, hj'⟩
  simp only [WalkTraceH.dN, WalkTraceH.cN, dif_pos hj', eL, eR, provH, nsmul_eq_mul]
  have hmL : walkColVS H χ WChip.mL ⟨j, hj'⟩ = (((wLbl H j).mL : ℕ) : F) := rfl
  have hmR : walkColVS H χ WChip.mR ⟨j, hj'⟩ = (((wLbl H j).mR : ℕ) : F) := rfl
  rw [hmL, hmR]
  simp

/-- **`hpubC` at the honest values**, given the compute export terminal `Re ρ₃ = accSumX`. -/
theorem hpubC_honest (χ : Coins frameVS K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (bs : List Noun) {t : NTree (GenComputeRow Kg)} (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hsem : ∀ g ∈ bfsRows (airReorder t), (rowOfSkel g.skel).Sem)
    (hpk : ∀ g ∈ bfsRows (airReorder t), PKS g)
    (hlen : H.d.cells.length < ringChar F)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hρ3 : Quad.re _ (ρ 3) = accSumX H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH H.V.basis χ) (bfsForest [airReorder t]).length) :
    pubsCH δF ρ y (yHVS H χ) CellH.pubH = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      algebraMap F K (CellTraceH.mN (mhvH H (bfsRows (airReorder t))) j) *
        (CellTraceH.dN δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
          (chalsVS δF χ) (pubsCH δF ρ y (yHVS H χ)) (cellColB H bs (toVCL χ))
          (mhvH H (bfsRows (airReorder t))) j)⁻¹ := by
  set rows := bfsRows (airReorder t) with hrows
  have hC : pubsCH δF ρ y (yHVS H χ) CellH.pubH = Quad.re _ (ρ 3) + yHVS H χ := by simp [pubsCH]
  have hcells : (demandH2 rows).cells = H.d.cells := by rw [hd]
  have hpreads : (demandH2 rows).preads = H.d.preads := by rw [hd]
  -- the walk total is the walk consumers' sum
  have hY : yHVS H χ = ((walkConsH2 (F := F) rows).map fun k => (recDen (χ cRhoH) (χ cGamH) k)⁻¹).sum := by
    unfold yHVS walkConsH2
    rw [sum_walkRows H (fun w => (recDen (χ cRhoH) (χ cGamH) (expKey (F := F) H.d.cells w.node))⁻¹),
      hcells, hpreads, List.map_map]
    rfl
  -- the compute total is the compute consumers' sum
  have hX : Quad.re _ (ρ 3) = ((consumedH2 (F := F) rows).map fun k => (recDen (χ cRhoH) (χ cGamH) k)⁻¹).sum := by
    rw [hρ3, accSumX_eq, limb_rhoL, limb_gammaL]
    unfold consumedH2
    rw [hcells]
  have hwn : ∀ w ∈ walkRows (demandH2 rows).cells (demandH2 rows).preads, w.label.node ∈ (demandH2 rows).cells := by
    rw [hcells, hpreads]; exact H.walkRows_node_mem hslot
  have hlink := export_total_link2_inv (F := F) rows hsem hpk (by rw [hcells]; exact hlen) hwn (χ cRhoH) (χ cGamH)
  rw [hC, hX, hY, hlink, hcells, ← sum_range_getD H.d.cells (.atom 0), ← H.hC0]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [CellTraceH.mN, CellTraceH.dN, dif_pos hj', mhvH]
  rw [cell_dRow_eq_recDen H bs χ _ _ ⟨j, hj'⟩]
  simp

end Terminals

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
