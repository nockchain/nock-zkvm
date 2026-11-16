/-
  Nock/NockVMROM/Thm54/VclL/Handle/CellTwinKW.lean

  **`cellChipHQKW`, the
  cell twin that PROVIDES the wire key `keyHK` (SPEC §2.1: kind entries `w + kb`).**  New module, additive.

  `cellChipHQK` (A-3r2) puts `keyH` (kind entries `w`) into the export balance (`WireKindJ8`).  This twin is
  `cellTemplateHQK` with the `𝕂′` export gates' provide inverse reading `denKeyQ keyHK`; nothing else
  changes: base columns `134`, `𝕂′` columns `36`, width **242** (`rfl`), every gate of degree `≤ 4`, the same
  coins and publics, the same IO summand (#5: one provide per row, same count).
  * `gatesQ` / `cellTemplateHQKW` / `cellChipHQKW` / `cellChipHQKW_width`;
  * `cellHQKW_inv`, `cellHQKW_telescope` (`Σ mh · invH′ = (pub₄, pub₅)`), `cellProvsW`, **`cellW_provs_sumQ`**
    (the providers' weighted `𝕂′` sum is the terminal), `cellW_provs_denQ`;
  * **`exportHKW_genuine`**: `TwoProviderQ.exportHK_genuine` on this twin (the provided key IS `recFK
    (exportRecK c)`, `c` a decoded row, grounded at all three kinds).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The gates and the template -/

section Gates
variable {F : Type} [Field F] [DecidableEq F]

/-- **The four `𝕂′` export gates at the wire key**: `CellHQ.gatesQ` with the provide inverse over `keyHK`. -/
def gatesQ (δF : F) : List (QE F) :=
  QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF keyHK)) QE.one :: (CellHQ.gatesQ δF).tail

def gates (δF : F) : List (MixedExpr F) := (gatesQ δF).flatMap QE.gates

theorem gates_deg_all (δF : F) : (gates δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, gatesQ, CellHQ.gatesQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ, keyHK, CellH.valE,
    QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul,
    QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem mixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF ++ gates δF, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact cellMixed_deg δF g hg
  · simpa using List.all_eq_true.mp (gates_deg_all δF) g hg

/-- **`cellTemplateHQKW`**: `cellTemplateHQK` with the wire-key export gates. -/
def cellTemplateHQKW (δF : F) : ChipTemplate F :=
  { CellTwinK.cellTemplateHQK δF with
    mixedTransition := Cell.mixedGates δF ++ gates δF
    mixedTransition_deg := mixed_deg δF }

theorem cellTemplateHQKW_baseCols (δF : F) : (cellTemplateHQKW δF).baseCols = 134 :=
  CellTwinK.cellTemplateHQK_baseCols δF
theorem cellTemplateHQKW_extCols (δF : F) : (cellTemplateHQKW δF).extCols = 36 :=
  CellTwinK.cellTemplateHQK_extCols δF

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

/-- **`cellChipHQKW`** (masks at `0`, `1`, as `cellChipHQK`). -/
noncomputable def cellChipHQKW (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateHQKW δF) b (slotVal b 134 chals) (slotVal b 134 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 134 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Width `242`**, by `rfl` (as `cellChipHQK`). -/
theorem cellChipHQKW_width : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w = 242 := rfl

theorem hqkwCell_shift : ∀ j < (cellTemplate δF).width 3,
    shiftCol 129 134 j < (cellTemplateHQKW δF).width 3 :=
  shift_lt _ _ 129 134 (cellTemplate_baseCols δF) (cellTemplateHQKW_baseCols δF) (by omega)
    (by rw [cellTemplate_extCols, cellTemplateHQKW_extCols]; omega)

/-- Restriction of a `cellChipHQKW` trace to `cellChip`'s `225` columns. -/
noncomputable def restrictHQKWCell
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 129 134 (hqkwCell_shift δF) Q

theorem cellChipHQKW_restrict_cell_sat
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q) := by
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateHQKW δF) 129 134 (cellTemplate_baseCols δF)
    (cellTemplateHQKW_baseCols δF)
    (by omega) (by rw [hR, cellTemplateHQKW_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl Q hsat

theorem cellChipHQKW_restrict_bind
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj

theorem hqkwEF_trace (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])
    (i : Fin n) {j : ℕ} (hj : j < 129) :
    (hqkEF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i).trace j := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : j < (cellChip δF b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : j < (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w := by
    rw [cellChipHQKW_width]; omega
  simp only [cellEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictHQKWCell, restrictQ]
  congr 2
  apply Fin.ext
  simp [shiftCol, hj]

theorem cellB0Of_hqkw (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])
    (i : Fin n) :
    cellB0Of (hqkEF b nodes orbit chals pubs Q i) =
      cellB0Of (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) := by
  simp only [cellB0Of, hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idx < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idL < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idR < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wL < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wR < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aL < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aR < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.lo < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hi < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loL < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiL < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loR < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiR < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.carry < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mv < 129),
    hqkwEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mx < 129)]

end Chip

/-! ## 2. The export telescope at the wire key -/

section Tele
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

abbrev wEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((cellTemplateHQKW δF).col0 3) (hqkEF b nodes orbit chals pubs Q' i)

theorem cellHQKW_qgates (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ gatesQ δF, e.ev δF (wEK δF b nodes orbit chals pubs Q i) (hqkEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (cellTemplateHQKW δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2.2.2 g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))

abbrev wInvQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((wEK δF b nodes orbit chals pubs Q' i).trace CellHQ.invHQ)
    ((wEK δF b nodes orbit chals pubs Q' i).trace (CellHQ.invHQ + 1))

abbrev wDenQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF (keyHK (F := F))).ev δF (wEK δF b nodes orbit chals pubs Q' i) (hqkEF b nodes orbit chals pubs Q' i)

abbrev wTermQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  liftQ δF ((hqkEF b nodes orbit chals pubs Q' i).trace CellH.mh) * wInvQ δF b nodes orbit chals pubs Q' i

theorem cellHQKW_inv (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    wDenQ δF b nodes orbit chals pubs Q i ≠ 0 ∧
      wInvQ δF b nodes orbit chals pubs Q i = (wDenQ δF b nodes orbit chals pubs Q i)⁻¹ := by
  have g := cellHQKW_qgates δF b hn nodes orbit chals pubs Q hsat i
    (QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF keyHK)) QE.one) (by simp [gatesQ])
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
  exact ⟨right_ne_zero_of_mul_eq_one g, eq_inv_of_mul_eq_one_left g⟩

theorem cellHQKW_masks (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (hqkEF b nodes orbit chals pubs Q i).trace Cell.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (hqkEF b nodes orbit chals pubs Q i).trace Cell.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w = 242 := cellChipHQKW_width δF b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem wEK_pub (i : Fin n) (idx : ℕ) : (wEK δF b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (cellTemplateHQKW δF) 134 (cellTemplateHQKW_baseCols δF) _ pubs rfl idx

theorem wEK_chal (i : Fin n) (idx : ℕ) : (wEK δF b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (cellTemplateHQKW δF) 134 (cellTemplateHQKW_baseCols δF) _ chals rfl idx

theorem wEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (hqkEF b nodes orbit chals pubs Q i).traceNext j = (hqkEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem wEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (wEK δF b nodes orbit chals pubs Q i).traceNext r = (wEK δF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (wEF_next δF b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The wire-key export telescope**: `Σ_i mhᵢ · invH′ᵢ = (pub₄, pub₅)`. -/
theorem cellHQKW_telescope (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wTermQ δF b nodes orbit chals pubs Q i = Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) := by
  have hg := cellHQKW_qgates δF b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (hqkEF b nodes orbit chals pubs Q i).trace Cell.isF)
    (fun i => (hqkEF b nodes orbit chals pubs Q i).trace Cell.isL)
    (fun i => Quad.mk _ ((wEK δF b nodes orbit chals pubs Q i).trace CellHQ.accHQ)
      ((wEK δF b nodes orbit chals pubs Q i).trace (CellHQ.accHQ + 1))) _ _
    (fun i => (cellHQKW_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (cellHQKW_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [gatesQ, CellHQ.gatesQ] : QE.scale (cv Cell.isF) (QE.sub (QE.var CellHQ.accHQ)
      (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ))) ∈ gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_scale, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [gatesQ, CellHQ.gatesQ] : QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next CellHQ.accHQ)
      (QE.var CellHQ.accHQ)) (QE.scale (nv CellH.mh) (QE.next CellHQ.invHQ))) ∈ gatesQ δF)
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_scale, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, wEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      wEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [wTermQ, wInvQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [gatesQ, CellHQ.gatesQ] : QE.scale (cv Cell.isL) (QE.sub (QE.var CellHQ.accHQ)
      (QE.pub CellHQ.pubHQ)) ∈ gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, wEK_pub, wEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

/-- The row denominator is `compress` at the `𝕂′` coins of the lifted WIRE key. -/
theorem wDenQ_eq (i : Fin n) :
    wDenQ δF b nodes orbit chals pubs Q i =
      compress ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩
        (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i))) := by
  rw [wDenQ, denKeyQ_ev δF _ _ _ (by simp [keyHK])]
  simp only [coinsQ, wEK_chal]

/-- **The wire-key providers**: per row, the provided key and its multiplicity `mh`. -/
def cellProvsW {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 5 → K) × K) :=
  (List.finRange n).map fun i =>
    (ServeH.keyVec5 (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q' i),
      algebraMap F K ((hqkEF b nodes orbit chals pubs Q' i).trace CellH.mh))

theorem cellW_provs_denQ (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ cellProvsW b nodes orbit chals pubs Q,
      compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  rw [← wDenQ_eq]
  exact (cellHQKW_inv δF b hn nodes orbit chals pubs Q hsat i).1

/-- **The wire-key providers' weighted `𝕂′` sum is the terminal `(pub₄, pub₅)`.** -/
theorem cellW_provs_sumQ (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((cellProvsW b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ : IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) := by
  rw [← cellHQKW_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [cellProvsW, List.map_map, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wTermQ, (cellHQKW_inv δF b hn nodes orbit chals pubs Q hsat i).2, wDenQ_eq]

end Tele

/-! ## 3. `exportHK_genuine` on the wire-key twin -/

section ExportW
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]

/-- **`exportHKW_genuine`** — `TwoProviderQ.exportHK_genuine` on `cellChipHQKW`: `exportH_genuine` re-proved for the wire kind `k = w + kb`.  On a trace accepted
by `cellChipHQK`, outside the two-provider validity IO event (the hypotheses of `cellTable_accepts2` on the
restriction) with atom-root external keys: at every row the wire key the chip provides (`keyHK`) is
`recFK (exportRecK c)` of the row's round-0 data `c`, `c` is a row of the decoded table, and the record is
grounded at all three kinds (`denK (1, idx) = [denK hK_L, denK hK_R]`). -/
theorem exportHKW_genuine (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW
      (reqs ++ cellVInternal δF b hn nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q))
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs
        (restrictHQKWCell δF b hn nodes orbit chals pubs Q)) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar F)
    (E : Noun → FP 𝕂′)
    (hcons : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar F) (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) E)
    (ext : ℕ → Option Noun) (hvp : AtomLeaves E vp ext) (i : Fin n) :
    let tb := (cellTableOf δF b nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).map (·.b0)
    let c := cellB0Of (hqkEF b nodes orbit chals pubs Q i)
    (keyHK : List (CoeffExpr F)).map (fun g => g.eval (hqkEF b nodes orbit chals pubs Q i)) =
        recFK (exportRecK c) ∧ c ∈ tb ∧
      ∃ L R, denK tb ext (1, c.idx) = some (.cell L R) ∧ denK tb ext (hK c .L) = some L ∧
        denK tb ext (hK c .R) = some R := by
  intro tb c
  set Q0 := restrictHQKWCell δF b hn nodes orbit chals pubs Q
  have hsat0 := cellChipHQKW_restrict_cell_sat δF b hn nodes orbit chals pubs Q hsat
  have hbind0 := cellChipHQKW_restrict_bind δF b hn nodes orbit chals pubs Q hbind
  have hacc := cellTable_accepts2 δF b hn nodes orbit chals pubs Q0 hF hq hz hsat0 hbind0 hinj hadj hnp
    γ ρ hok reqs xs hsum hout hxne hcount vp hx hvp0
  have hbase := ((expandChip_satisfies_iff_language _ b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)).1
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := F) →
      (hqkEF b nodes orbit chals pubs Q i).trace w = 0 ∨ (hqkEF b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ (List.mem_append_left _ hw)
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hkind : ∀ g ∈ (CellTwinK.kindGates (F := F)), g.eval (hqkEF b nodes orbit chals pubs Q i) = 0 :=
    fun g hg => hbase g (List.mem_append_right _ hg)
  have hc : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i) ∈ cellTableOf δF b nodes orbit chals pubs Q0 :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hcb : c = (cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i)).b0 := cellB0Of_hqkw δF b hn nodes orbit chals pubs Q i
  refine ⟨keyHK_eval hF (by omega) _ hkind (hbool Cell.wL (by simp [Cell.baseGates]))
      (hbool Cell.wR (by simp [Cell.baseGates])),
    by rw [hcb]; exact List.mem_map_of_mem hc, ?_⟩
  rw [hcb]
  exact exportRecK_grounded hq hcons hE hacc hvp hc

end ExportW

end

end Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
