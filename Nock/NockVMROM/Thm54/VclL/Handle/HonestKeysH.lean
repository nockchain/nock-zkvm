/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestKeysH.lean

  Additive.

  * `cell_dRow_eq_recDen`: on the honest cell twin over `cellColB`, row `i`'s handle-export denominator is
    `recDen ρH γH (expKey cells cells[i])` (the cell row's `keyH = (idx, wL, val_L, wR, val_R)` is the
    export key of its noun);
  * `walk_dRow_xKey_eq`: on the honest walk twin with the child handles `kLvH vLvH kRvH vRvH` (the
    handles of the node's two children, `hdl`), row `i`'s consumed-export denominator is
    `recDen ρH γH (expKey cells node_i)`;
  * `walk_dRow_recL_eq` / `walk_dRow_recR_eq`: the two provided walk-record denominators are
    `recDenP ρH γH (recLH cells label_i)` / `(recRH cells label_i)` (`provH`'s records);
  * `kLvH_bool` / `kRvH_bool`: the honest kind bits are boolean.
  The coins are the `𝕂` handle coins `χ cRhoH`, `χ cGamH` (`chalsVS` leaves `34`, `33`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSizeH

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
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The cell twin -/

section CellGeneric
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))

theorem cellE_trace (hinj : Function.Injective nodes) (mhv : Fin n → F) (iv av : Fin n → K) (i : Fin n)
    {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) :
    (CellTraceH.E δF b hn nodes orbit chals pubs (cellCol δF b vals) mhv iv av i).trace j =
      (vals i).base j := by
  have hw : j < (cellTemplateH δF).width 3 := by rw [CellTraceH.cellTemplateH_width]; omega
  unfold CellTraceH.E
  rw [env_trace hn nodes hinj _ _ _ _ i hw]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [fullCol, CellTraceH.colH, extColF, cellCol, h0, h1, hj, show j < 129 from hj]

/-- **The cell twin's handle denominator at a row, from the row's committed values.** -/
theorem cell_dRow_vals (hinj : Function.Injective nodes) (mhv : Fin n → F) (i : Fin n) :
    CellTraceH.dRow δF b hn nodes orbit chals pubs (cellCol δF b vals) mhv i =
      chals CellH.hRho + algebraMap F K (vals i).idx + chals CellH.hGam * algebraMap F K (vals i).wL +
        chals CellH.hGam ^ 2 * algebraMap F K ((vals i).wL * (vals i).idL + (1 - (vals i).wL) * (vals i).aL) +
        chals CellH.hGam ^ 3 * algebraMap F K (vals i).wR +
        chals CellH.hGam ^ 4 * algebraMap F K ((vals i).wR * (vals i).idR + (1 - (vals i).wR) * (vals i).aR) := by
  unfold CellTraceH.dRow
  rw [denKey_eval, CellTraceH.gather_chal δF b chals _ rfl, CellTraceH.gather_chal δF b chals _ rfl]
  have t := fun j (h2 : 2 ≤ j) (hj : j < 129) =>
    cellE_trace δF b hn nodes orbit chals pubs vals hinj mhv (fun _ => 0) (fun _ => 0) i h2 hj
  simp only [CellH.keyH, CellH.valE, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, CoeffExpr.eval, Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR, Cell.aL,
    Cell.aR]
  rw [t 2 (by omega) (by omega), t 5 (by omega) (by omega), t 3 (by omega) (by omega),
    t 7 (by omega) (by omega), t 6 (by omega) (by omega), t 4 (by omega) (by omega), t 8 (by omega) (by omega)]
  simp only [CellVals.base]
  norm_num
  ring

end CellGeneric

section CellKey
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- A child handle `(w, w·id + (1 − w)·a)` of the generated cell row is `hdl` of the child. -/
theorem childHdl_eq (cells : List Noun) (a : Noun) :
    ((if a.isCell then (1 : F) else 0),
      (if a.isCell then (1 : F) else 0) * (if a.isCell then (cells.idxOf a : F) else 0) +
        (1 - (if a.isCell then (1 : F) else 0)) * (match a with | .atom v => (v : F) | _ => 0)) =
      hdl cells a := by
  cases a with
  | atom v => simp [Noun.isCell, hdl]
  | cell x y => simp [Noun.isCell, hdl]

/-- **The generated cell row's handle-export denominator is `recDen` of its noun's export key.** -/
theorem cellRow0_den (ρ γ : K) (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (n : Noun) :
    ρ + algebraMap F K (cellRow0 δF z cells vcs xs0 xs1 n).idx +
        γ * algebraMap F K (cellRow0 δF z cells vcs xs0 xs1 n).wL +
        γ ^ 2 * algebraMap F K ((cellRow0 δF z cells vcs xs0 xs1 n).wL * (cellRow0 δF z cells vcs xs0 xs1 n).idL +
          (1 - (cellRow0 δF z cells vcs xs0 xs1 n).wL) * (cellRow0 δF z cells vcs xs0 xs1 n).aL) +
        γ ^ 3 * algebraMap F K (cellRow0 δF z cells vcs xs0 xs1 n).wR +
        γ ^ 4 * algebraMap F K ((cellRow0 δF z cells vcs xs0 xs1 n).wR * (cellRow0 δF z cells vcs xs0 xs1 n).idR +
          (1 - (cellRow0 δF z cells vcs xs0 xs1 n).wR) * (cellRow0 δF z cells vcs xs0 xs1 n).aR) =
      recDen ρ γ (expKey (F := F) cells n) := by
  unfold recDen expKey
  simp only [cellRow0]
  generalize hdN n = a
  generalize tlN n = c
  cases a <;> cases c <;> simp [Noun.isCell, hdl]

end CellKey

section CellHonest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr) (bs : List Noun)

/-- **Identification 1: the cell row's `keyH` is the export key of its noun.**  At the honest cell twin over
`cellColB`, row `i`'s handle denominator is `recDen ρH γH (expKey cells cells[i])`. -/
theorem cell_dRow_eq_recDen (χ : Coins frameVS K) (pubs : ℕ → K) (mhv : Fin (H.V.memRows (tCW hT hP)) → F)
    (i : Fin (H.V.memRows (tCW hT hP))) :
    CellTraceH.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        (chalsVS δF χ) pubs (cellColB H bs (toVCL χ)) mhv i =
      recDen (χ cRhoH) (χ cGamH) (expKey (F := F) H.d.cells (H.d.cells.getD i (.atom 0))) := by
  unfold cellColB
  rw [cell_dRow_vals δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    (chalsVS δF χ) pubs _ (H.hinj _) mhv i, chalsVS_hRho, chalsVS_hGam]
  exact cellRow0_den δF (χ cRhoH) (χ cGamH) (zC (toVCL χ)) H.d.cells (vcsOf H.d.cells bs) (xs0W H.d)
    (xs1W H.d) (H.d.cells.getD i (.atom 0))

end CellHonest

/-! ## 2. The walk twin -/

section WalkGeneric
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kr : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF))) (kLv vLv kRv vRv : Fin n → F)

theorem walkE_trace (hinj : Function.Injective nodes) (R : WalkTraceH.Roles n K) (i : Fin n)
    {j : ℕ} (h2 : 2 ≤ j) (hj : j < 25) :
    (WalkTraceH.E δF kr b hn nodes orbit chals pubs (walkCol δF b kr vals) kLv vLv kRv vRv R i).trace j =
      if j < 21 then (vals i).base kr i j else if j = 21 then kLv i else if j = 22 then vLv i
      else if j = 23 then kRv i else vRv i := by
  have hw : j < (walkTemplateH δF kr).width 3 := by rw [WalkTraceH.walkTemplateH_width]; omega
  unfold WalkTraceH.E
  rw [env_trace hn nodes hinj _ _ _ _ i hw]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  by_cases h21 : j < 21
  · simp [fullCol, WalkTraceH.colH, extColF, walkCol, h0, h1, h21]
  · have : j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [fullCol, WalkTraceH.colH, extColF, WalkTraceH.new]

/-- **The walk twin's denominators at a row, from the row's committed values.** -/
theorem walk_dRow_vals (hinj : Function.Injective nodes) (i : Fin n) :
    WalkTraceH.dRow δF kr b hn nodes orbit chals pubs WalkHC.xKeyH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      chals CellH.hRho + algebraMap F K (vals i).idx + chals CellH.hGam * algebraMap F K (kLv i) +
        chals CellH.hGam ^ 2 * algebraMap F K (vLv i) + chals CellH.hGam ^ 3 * algebraMap F K (kRv i) +
        chals CellH.hGam ^ 4 * algebraMap F K (vRv i) ∧
    WalkTraceH.dRow δF kr b hn nodes orbit chals pubs WalkHC.recLH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      chals CellH.hRho + algebraMap F K (vals i).ridx + chals CellH.hGam * algebraMap F K (2 * (vals i).pre) +
        chals CellH.hGam ^ 2 * algebraMap F K (kLv i) + chals CellH.hGam ^ 3 * algebraMap F K (vLv i) ∧
    WalkTraceH.dRow δF kr b hn nodes orbit chals pubs WalkHC.recRH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      chals CellH.hRho + algebraMap F K (vals i).ridx +
        chals CellH.hGam * algebraMap F K (2 * (vals i).pre + 1) +
        chals CellH.hGam ^ 2 * algebraMap F K (kRv i) + chals CellH.hGam ^ 3 * algebraMap F K (vRv i) := by
  have t := fun j (h2 : 2 ≤ j) (hj : j < 25) =>
    walkE_trace δF kr b hn nodes orbit chals pubs vals kLv vLv kRv vRv hinj WalkTraceH.zeroR i h2 hj
  have t3 := t 3 (by omega) (by omega)
  have t4 := t 4 (by omega) (by omega)
  have t5 := t 5 (by omega) (by omega)
  have t21 := t 21 (by omega) (by omega)
  have t22 := t 22 (by omega) (by omega)
  have t23 := t 23 (by omega) (by omega)
  have t24 := t 24 (by omega) (by omega)
  norm_num [WalkVals.base, WalkVals.named] at t3 t4 t5
  norm_num at t21 t22 t23 t24
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold WalkTraceH.dRow WalkTraceH.denAt
    rw [denKey_eval, WalkTraceH.gather_chal δF kr b chals _ rfl, WalkTraceH.gather_chal δF kr b chals _ rfl]
    simp only [WalkHC.xKeyH, WalkHC.recLH, WalkHC.recRH, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, CoeffExpr.eval, WChip.idx, WChip.pre, WChip.ridx,
      WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR, t3, t4, t5, t21, t22, t23, t24]
    try simp only [map_add, map_mul, map_one, map_ofNat]
    ring

end WalkGeneric

section WalkHonest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- The honest walk row's trie (`wTrie`, position `i` of the BFS walk rows). -/
abbrev wLbl (i : ℕ) : WN := (wTrie H.d.cells H.d.preads i).label

/-- **The honest child handles of the walk rows** (`kL vL kR vR`, columns `21..24`): the handles of the
node's two children. -/
def kLvH (i : Fin (H.V.memRows (tWW hT hP))) : F := (hdl H.d.cells (hdN (wLbl H i).node)).1
def vLvH (i : Fin (H.V.memRows (tWW hT hP))) : F := (hdl H.d.cells (hdN (wLbl H i).node)).2
def kRvH (i : Fin (H.V.memRows (tWW hT hP))) : F := (hdl H.d.cells (tlN (wLbl H i).node)).1
def vRvH (i : Fin (H.V.memRows (tWW hT hP))) : F := (hdl H.d.cells (tlN (wLbl H i).node)).2

theorem hdl_fst_bool (cells : List Noun) (a : Noun) : (hdl (F := F) cells a).1 = 0 ∨ (hdl (F := F) cells a).1 = 1 := by
  cases a <;> simp [hdl]

theorem kLvH_bool (i) : kLvH H i = 0 ∨ kLvH H i = 1 := hdl_fst_bool _ _
theorem kRvH_bool (i) : kRvH H i = 0 ∨ kRvH H i = 1 := hdl_fst_bool _ _

theorem walkVals_idx (χ : Coins frameVS K) (i : ℕ) :
    (H.wVals (toVCL χ) i).idx = ((H.d.cells.idxOf (wLbl H i).node : ℕ) : F) ∧
    (H.wVals (toVCL χ) i).pre = ((axisFold (wLbl H i).bits : ℕ) : F) ∧
    (H.wVals (toVCL χ) i).ridx = ((H.d.cells.idxOf (wLbl H i).root : ℕ) : F) := ⟨rfl, rfl, rfl⟩

/-- **Identifications 2 and 3 at the honest walk twin**: the consumed export denominator is `recDen` of the
node's export key, the two provided denominators are `recDenP` of `recLH` / `recRH` (`provH`'s records). -/
theorem walk_dRow_honest (χ : Coins frameVS K) (pubs : ℕ → K) (i : Fin (H.V.memRows (tWW hT hP))) :
    WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVS δF χ) pubs WalkHC.xKeyH (walkColVS H χ) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDen (χ cRhoH) (χ cGamH) (expKey (F := F) H.d.cells (wLbl H i).node) ∧
    WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVS δF χ) pubs WalkHC.recLH (walkColVS H χ) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDenP (χ cRhoH) (χ cGamH) (recLH (F := F) H.d.cells (wLbl H i)) ∧
    WalkTraceH.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVS δF χ) pubs WalkHC.recRH (walkColVS H χ) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDenP (χ cRhoH) (χ cGamH) (recRH (F := F) H.d.cells (wLbl H i)) := by
  obtain ⟨e1, e2, e3⟩ := walk_dRow_vals δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
    (H.V.orbitM (tWW hT hP)) (chalsVS δF χ) pubs (fun i' => H.wVals (toVCL χ) i')
    (kLvH H) (vLvH H) (kRvH H) (vRvH H) (H.hinj _) i
  obtain ⟨w1, w2, w3⟩ := walkVals_idx H χ i
  refine ⟨?_, ?_, ?_⟩
  · unfold walkColVS; rw [e1, chalsVS_hRho, chalsVS_hGam, w1]
    simp only [recDen, expKey, kLvH, vLvH, kRvH, vRvH]
  · unfold walkColVS; rw [e2, chalsVS_hRho, chalsVS_hGam, w2, w3]
    simp only [recDenP, Handle.recLH, kLvH, vLvH]
    push_cast; ring
  · unfold walkColVS; rw [e3, chalsVS_hRho, chalsVS_hGam, w2, w3]
    simp only [recDenP, Handle.recRH, kRvH, vRvH]
    push_cast; ring

end WalkHonest

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
