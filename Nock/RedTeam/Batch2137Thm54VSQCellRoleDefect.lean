/-
  Nock/RedTeam/Batch2137Thm54VSQCellRoleDefect.lean

  After the fix those statements are false of the live objects, so the receipt now states the defect
  on a verbatim REPLICA of the old gate list / template / chip (`cellTemplateHQOld`, `cellChipHQOld`):

  * `cellChipHQOld_unsat` — the old chip accepts no trace;
  * `old_roles_out_of_range` / `fixed_roles_in_range` — the old roles `36 / 38` are outside the
    template's `36` roles, the fixed `32 / 34` (and their Im halves `33 / 35`) inside.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch2137

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

section Replica
variable {F : Type} [Field F]

def oldInvHQ : ℕ := 36
def oldAccHQ : ℕ := 38

/-- **Replica** of the old `CellHQ.gatesQ` (verbatim, at the old roles). -/
def oldGatesQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var oldInvHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one,
    QE.scale (cv Cell.isF) (QE.sub (QE.var oldAccHQ) (QE.scale (cv CellH.mh) (QE.var oldInvHQ))),
    QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next oldAccHQ) (QE.var oldAccHQ))
      (QE.scale (nv CellH.mh) (QE.next oldInvHQ))),
    QE.scale (cv Cell.isL) (QE.sub (QE.var oldAccHQ) (QE.pub CellHQ.pubHQ)) ]

def oldGates (δF : F) : List (MixedExpr F) := (oldGatesQ δF).flatMap QE.gates

theorem oldGates_deg_all (δF : F) : (oldGates δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [oldGates, oldGatesQ, oldInvHQ, oldAccHQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ,
    CellH.keyH, CellH.valE, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add,
    QE.sub, QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem oldMixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF ++ oldGates δF, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact cellMixed_deg δF g hg
  · simpa using List.all_eq_true.mp (oldGates_deg_all δF) g hg

/-- **Replica** of the old `cellTemplateHQ`. -/
def cellTemplateHQOld (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![130, 0, 0]
  extColsOf := ![0, 18, 18]
  baseTransition := Cell.baseGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ oldGates δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := cellBase_deg
  extTransition_deg := by simp
  mixedTransition_deg := oldMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem cellTemplateHQOld_baseCols (δF : F) : (cellTemplateHQOld δF).baseCols = 130 := by
  show (∑ r : Fin 3, (![130, 0, 0] : Fin 3 → ℕ) r) = 130
  decide
theorem cellTemplateHQOld_extCols (δF : F) : (cellTemplateHQOld δF).extCols = 36 := by
  show (∑ r : Fin 3, (![0, 18, 18] : Fin 3 → ℕ) r) = 36
  decide

/-- The old roles lie outside the template's `36` roles; the fixed ones (Re and Im) inside. -/
theorem old_roles_out_of_range (δF : F) :
    ¬ oldInvHQ < (cellTemplateHQOld δF).extCols ∧ ¬ oldAccHQ < (cellTemplateHQOld δF).extCols := by
  rw [cellTemplateHQOld_extCols]; decide

theorem fixed_roles_in_range (δF : F) :
    CellHQ.invHQ + 1 < (cellTemplateHQ δF).extCols ∧ CellHQ.accHQ + 1 < (cellTemplateHQ δF).extCols := by
  rw [cellTemplateHQ_extCols]; decide

end Replica

section Unsat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **Replica** of the old `cellChipHQ`. -/
noncomputable def cellChipHQOld (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateHQOld δF) b (slotVal b 130 chals) (slotVal b 130 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 130 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- The Re half of `invH′ · X − 1` is `−1` when roles `36 / 37` read `0`. -/
theorem key_eval (δF : F) (X : QE F) (eK : Env K) (eF : Env F) (h36 : eK.trace 36 = 0)
    (h37 : eK.trace 37 = 0) :
    (QE.sub (QE.mul δF (QE.var oldInvHQ) X) QE.one).re.eval eK eF = -1 := by
  simp only [QE.sub, QE.mul, QE.var, QE.one, oldInvHQ, MixedExpr.eval]
  rw [h36, h37]; simp

/-- **The old `cellChipHQ` accepts no trace.** -/
theorem cellChipHQOld_unsat (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
    (Q : Fin (cellChipHQOld δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    ¬ (cellChipHQOld δF b hn nodes orbit chals pubs).rap.Satisfies Q := by
  intro hsat
  have h := (expandChip_satisfies_iff_language _ b _ _ orbit _ Q).mp hsat (nodes ⟨0, hn⟩)
    ((mem_rowNodeSet_iff nodes _).mpr ⟨_, rfl⟩)
  have hg := h.2.2.2 (QE.sub (QE.mul δF (QE.var oldInvHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one).re (by
    show _ ∈ Cell.mixedGates δF ++ oldGates δF
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, List.mem_cons_self .., List.mem_cons_self ..⟩))
  have hz : ∀ r, 36 ≤ r → (gatherEnv b ((cellTemplateHQOld δF).col0 3)
      (Reify.envOfTrace Q orbit.ω (nodes ⟨0, hn⟩) (slotVal b 130 chals) (slotVal b 130 pubs))).trace r = 0 := by
    intro r hr
    simp only [gatherEnv, ChipTemplate.col0, cellTemplateHQOld_baseCols, Reify.envOfTrace]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [dif_neg]; · simp
    show ¬ (130 + 3 * r + (k : ℕ) < (cellTemplateHQOld δF).baseCols + (cellTemplateHQOld δF).extCols * 3)
    rw [cellTemplateHQOld_baseCols, cellTemplateHQOld_extCols]; omega
  have h1 := (key_eval δF (HQ.denKeyQ δF CellH.keyH) _
    (Reify.envOfTrace Q orbit.ω (nodes ⟨0, hn⟩) (slotVal b 130 chals) (slotVal b 130 pubs))
    (hz 36 le_rfl) (hz 37 (by omega))).symm.trans hg
  exact absurd h1 (by simp)

end Unsat

#print axioms old_roles_out_of_range
#print axioms fixed_roles_in_range
#print axioms cellChipHQOld_unsat

end Nock.RedTeam.Batch2137
