/-
  Nock/NockVMROM/Thm54/VclL/Handle/SumsVSQ.lean

  Additive.

  Row-level bridges between the re-fill modules (`RefillCQ / RefillMQ / RefillWQ`) and the coin-free
  record lists of `IOVS` / `ServeH` (any trace agreeing on the round-0 columns, any coin / public vector):
  * compute: `termXV_pub` / `termPV_pub` (the row terms ignore the publics), `sumX_eq` / `sumP_eq`
    (`Σ_j termXV / termPV = Σ_{compXReqs / compPReqs} compress⁻¹`), `memX` / `memP`;
  * cell: `sumC_eq` (`Σ_j mC·dC⁻¹ = Σ_{cellProvs} w·compress⁻¹`), `memC`;
  * walk: `dW_pub`, `sumWX_eq`, `sumWP_eq`, `memWX`, `memWP`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ
import Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ
import Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SumsVSQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServeH Nock.NockVMROM.Thm54.VclL.Handle.TeleH
open Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ
open Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-! ## 1. Compute -/

section Comp
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin 85 → F[X])

theorem termXV_pub (pubV pubV' : ℕ → F) (j : ℕ) :
    termXV nodes b chalV pubV orbit P j = termXV nodes b chalV pubV' orbit P j := by
  unfold termXV baseN
  split_ifs <;> (congr 2 <;> exact (rowReqs_congr (K := K) _ _ (fun c _ => rfl)).1)

theorem termPV_pub (pubV pubV' : ℕ → F) (j : ℕ) :
    termPV nodes b chalV pubV orbit P j = termPV nodes b chalV pubV' orbit P j := by
  unfold termPV baseN
  split_ifs <;> (congr 2 <;> exact (rowReqs_congr (K := K) _ _ (fun c _ => rfl)).2)

variable (pubV : ℕ → F) {w : ℕ} (P' : Fin w → F[X]) (cv pv : ℕ → F) (hw : 43 ≤ w)
  (hP : ∀ (c : ℕ) (h1 : c < 85) (h2 : c < w), c < 43 → P ⟨c, h1⟩ = P' ⟨c, h2⟩)
include hw hP

theorem rows_eq (i : Fin n) :
    (rowXReqs (baseN nodes chalV pubV orbit P i) : List (Fin 5 → K)) = rowXReqs (rEF nodes cv pv orbit P' i) ∧
      (rowPReqs (baseN nodes chalV pubV orbit P i) : List (Fin 5 → K)) = rowPReqs (rEF nodes cv pv orbit P' i) := by
  rw [baseN_lt]
  exact rowReqs_congr _ _ (envOfTrace_congrW 43 P P' (by norm_num) hw hP orbit.ω orbit.ω (nodes i) chalV pubV cv pv)

theorem sumX_eq :
    ∑ j ∈ Finset.range n, termXV nodes b chalV pubV orbit P j =
      ((compXReqs nodes cv pv orbit P').map fun r => (compress (coinsC b chalV) r)⁻¹).sum := by
  unfold compXReqs
  rw [map_flatMap_sum, Chips.ChipRAP.sum_finRange, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [termXV, (rows_eq (K := K) nodes chalV orbit P pubV P' cv pv hw hP i).1]

theorem sumP_eq :
    ∑ j ∈ Finset.range n, termPV nodes b chalV pubV orbit P j =
      ((compPReqs nodes cv pv orbit P').map fun r => (compress (coinsC b chalV) r)⁻¹).sum := by
  unfold compPReqs
  rw [map_flatMap_sum, Chips.ChipRAP.sum_finRange, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [termPV, (rows_eq (K := K) nodes chalV orbit P pubV P' cv pv hw hP i).2]

theorem memXP (i : Fin n) (r : Fin 5 → K)
    (hr : r ∈ (rowXReqs (baseN nodes chalV pubV orbit P i) ++ rowPReqs (baseN nodes chalV pubV orbit P i) :
      List (Fin 5 → K))) :
    r ∈ compXReqs nodes cv pv orbit P' ∨ r ∈ compPReqs nodes cv pv orbit P' := by
  obtain ⟨e1, e2⟩ := rows_eq (K := K) nodes chalV orbit P pubV P' cv pv hw hP i
  rcases List.mem_append.mp hr with h1 | h1
  · left; rw [e1] at h1; exact List.mem_flatMap.mpr ⟨i, List.mem_finRange _, h1⟩
  · right; rw [e2] at h1; exact List.mem_flatMap.mpr ⟨i, List.mem_finRange _, h1⟩

end Comp

/-! ## 2. Cell -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chalsQ pubsQ chals pubs : ℕ → K)
  (Q : Fin (cellChipHQ δF b hn nodes orbit chalsQ pubsQ).rap.w → F[X])
  {w : ℕ} (Q' : Fin w → F[X]) (cs ps : ℕ → K) (hw : 130 ≤ w)
  (hQ : ∀ (c : ℕ) (h1 : c < (cellChipHQ δF b hn nodes orbit chalsQ pubsQ).rap.w) (h2 : c < w), c < 130 →
    Q ⟨c, h1⟩ = Q' ⟨c, h2⟩)
include hw hQ

theorem rowC_eq (i : Fin n) :
    ∀ c < 130, (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i).trace c =
      (cEF b nodes orbit cs ps Q' i).trace c :=
  envOfTrace_congrW 130 Q Q' (by rw [cellChipHQ_width]; norm_num) hw hQ orbit.ω orbit.ω (nodes i) _ _ _ _

theorem sumC_eq :
    ∑ j ∈ Finset.range n, algebraMap F K (mC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j) *
        (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j)⁻¹ =
      ((cellProvs b nodes orbit cs ps Q').map fun q =>
        q.2 * (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1)⁻¹).sum := by
  unfold cellProvs
  rw [List.map_map, Chips.ChipRAP.sum_finRange, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := rowC_eq δF b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ i
  simp only [Function.comp_apply, mC, dC, dif_pos i.isLt, Fin.eta]
  rw [keyVec5_congr 130 _ keyH_read _ _ he, he CellH.mh (by decide)]

theorem memC (j : ℕ) (hj : j < n) :
    ∃ q ∈ cellProvs b nodes orbit cs ps Q',
      dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j = compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1 := by
  have he := rowC_eq δF b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ ⟨j, hj⟩
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange ⟨j, hj⟩), ?_⟩
  simp only [dC, dif_pos hj]
  rw [keyVec5_congr 130 _ keyH_read _ _ he]

end Cell

/-! ## 3. Walk -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chalsQ pubsQ chals pubs : ℕ → K)
  (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ).rap.w → F[X])

theorem dW_pub (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, rdOK 25 g = true) (pubs' : ℕ → K) (j : ℕ) :
    dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q l j =
      dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs' Q l j := by
  unfold dW
  split_ifs with hj
  · congr 1 <;> exact keyVec5_congr (K := K) 25 l hl _ _ (fun c _ => rfl)
  · rfl

variable {w : ℕ} (Q' : Fin w → F[X]) (cs ps : ℕ → K) (hw : 25 ≤ w)
  (hQ : ∀ (c : ℕ) (h1 : c < (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ).rap.w) (h2 : c < w), c < 25 →
    Q ⟨c, h1⟩ = Q' ⟨c, h2⟩)
include hw hQ

theorem rowW_eq (i : Fin n) :
    ∀ c < 25, (rowW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q i).trace c =
      (wEF b nodes orbit cs ps Q' i).trace c :=
  envOfTrace_congrW 25 Q Q' (by rw [walkChipHQ_width]; norm_num) hw hQ orbit.ω orbit.ω (nodes i) _ _ _ _

theorem sumWX_eq :
    ∑ j ∈ Finset.range n, (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH j)⁻¹ =
      ((walkXReqs b nodes orbit cs ps Q').map fun r =>
        (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ r)⁻¹).sum := by
  unfold walkXReqs
  rw [List.map_map, Chips.ChipRAP.sum_finRange, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := rowW_eq δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ i
  simp only [Function.comp_apply, dW, dif_pos i.isLt, Fin.eta]
  rw [keyVec5_congr 25 _ xKeyH_read _ _ he]

theorem sumWP_eq :
    ∑ j ∈ Finset.range n,
      (algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mL j) *
          (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH j)⁻¹ +
        algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mR j) *
          (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH j)⁻¹) =
      ((walkPProvs b nodes orbit cs ps Q').map fun q =>
        q.2 * (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1)⁻¹).sum := by
  simp only [walkPProvs, map_flatMap_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [Chips.ChipRAP.sum_finRange, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := rowW_eq δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ i
  simp only [cW, dW, dif_pos i.isLt, Fin.eta]
  rw [keyVec5_congr 25 _ recLH_read _ _ he, keyVec5_congr 25 _ recRH_read _ _ he,
    he WChip.mL (by decide), he WChip.mR (by decide)]

theorem memWX (j : ℕ) (hj : j < n) :
    ∃ r ∈ walkXReqs b nodes orbit cs ps Q',
      dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH j =
        compress ⟨chals CellH.hGam, chals CellH.hRho⟩ r := by
  have he := rowW_eq δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ ⟨j, hj⟩
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange ⟨j, hj⟩), ?_⟩
  simp only [dW, dif_pos hj]
  rw [keyVec5_congr 25 _ xKeyH_read _ _ he]

theorem memWP (j : ℕ) (hj : j < n) :
    (∃ q ∈ walkPProvs b nodes orbit cs ps Q',
      dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH j =
        compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1) ∧
    (∃ q ∈ walkPProvs b nodes orbit cs ps Q',
      dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH j =
        compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1) := by
  have he := rowW_eq δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q Q' cs ps hw hQ ⟨j, hj⟩
  refine ⟨⟨_, List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_finRange _, List.mem_cons_self⟩, ?_⟩,
    ⟨_, List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_finRange _, List.mem_cons_of_mem _ List.mem_cons_self⟩, ?_⟩⟩
  · simp only [dW, dif_pos hj]
    rw [keyVec5_congr 25 _ recLH_read _ _ he]
  · simp only [dW, dif_pos hj]
    rw [keyVec5_congr 25 _ recRH_read _ _ he]

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle.SumsVSQ
