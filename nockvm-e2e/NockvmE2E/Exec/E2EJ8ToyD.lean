/-
(route (c)), part D: the DATUM and EXECUTED-check facts of the non-vacuity witness at the real regenerated toy1 instance `toy1X`
(Exec/Toy1X.lean), and the false-claim twin `toy1XF` (`*[0 [1 0]] = 0` claimed as `1`).
Nothing here edits an existing statement.
-/
import NockvmE2E.Exec.Toy1XOk
import NockvmE2E.J8.DatXOk
import NockvmE2E.J8.RVUJ8
import NockvmE2E.Exec.E2EJ8S

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EJ8ToyD
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8Shape NockvmE2E.Exec.Toy1X
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J8.InstJ8 NockvmE2E.J8.DatXOk

noncomputable section

/-- the false-claim twin: same instance, the public atom of the result is `1` -/
def toy1PubInF : PE.PubIn :=
  { claimCells := [{ key := 1, noun := [.cell, .atom 1, .atom 0], idx := 0, hi := 0, lo := 1 }], pins := [], atoms := [(0, 0), (2, 1)] }
def toy1XF : ExecInst := { toy1X with pubIn := toy1PubInF }
def toyClaimF : Nock.NockVMROM.Thm54.P8PublicClaim := ⟨.atom 0, .cell (.atom 1) (.atom 0), .atom 1⟩

theorem xi170 : XI170 toy1X = toy1X := rfl
theorem xi170F : XI170 toy1XF = toy1XF := rfl
theorem pubIn_eq : toy1PubIn = PE.toy1Claim := rfl

/-! ## the executed checks at both instances (pubIn is read by none of them: `rfl` for the twin) -/
theorem shape_F : j8ShapeOk toy1XF = j8ShapeOk toy1X := rfl
theorem shapeX_F : j8ShapeXOk toy1XF = j8ShapeXOk toy1X := rfl
theorem chips_F : chipsOk toy1XF = chipsOk toy1X := rfl
theorem mask_F : MaskOk.maskOk toy1XF = MaskOk.maskOk toy1X := rfl
theorem numeral_F : MaskOk.numeralOk toy1XF = MaskOk.numeralOk toy1X := rfl

theorem hsh : j8ShapeOk (XI170 toy1X) = true := by rw [xi170]; exact toy1X_shape
theorem hshX : j8ShapeXOk (XI170 toy1X) = true := by rw [xi170]; exact toy1X_shapeX
theorem hchips : chipsOk (XI170 toy1X) = true := by rw [xi170]; exact toy1X_chips
theorem hmask : MaskOk.maskOk (XI170 toy1X) = true := by rw [xi170]; exact toy1X_mask
theorem hnumeralOk : MaskOk.numeralOk (XI170 toy1X) = true := by rw [xi170]; exact toy1X_numeral

theorem hshF : j8ShapeOk (XI170 toy1XF) = true := by rw [xi170F, shape_F]; exact toy1X_shape
theorem hshXF : j8ShapeXOk (XI170 toy1XF) = true := by rw [xi170F, shapeX_F]; exact toy1X_shapeX
theorem hchipsF : chipsOk (XI170 toy1XF) = true := by rw [xi170F, chips_F]; exact toy1X_chips
theorem hmaskF : MaskOk.maskOk (XI170 toy1XF) = true := by rw [xi170F, mask_F]; exact toy1X_mask
theorem hnumeralOkF : MaskOk.numeralOk (XI170 toy1XF) = true := by rw [xi170F, numeral_F]; exact toy1X_numeral

/-! ## the datum -/
theorem hJ : hNof (XI170 toy1X) "jetChipJ8" = 0 := by rw [xi170]; decide +kernel
theorem hJF : hNof (XI170 toy1XF) "jetChipJ8" = 0 := by rw [xi170F]; decide +kernel
theorem hkW : 1 ≤ hNof (XI170 toy1X) "walkChipJ8" := by rw [xi170]; decide +kernel
theorem hkWF : 1 ≤ hNof (XI170 toy1XF) "walkChipJ8" := by rw [xi170F]; decide +kernel
theorem hV0 : (tabOf (XI170 toy1X) "walkChipHQK").isSome = true → 1 ≤ 0 ∧ 0 ≤ hNof (XI170 toy1X) "walkChipHQK" := by
  rw [xi170]; decide +kernel
theorem hV0F : (tabOf (XI170 toy1XF) "walkChipHQK").isSome = true → 1 ≤ 0 ∧ 0 ≤ hNof (XI170 toy1XF) "walkChipHQK" := by
  rw [xi170F]; decide +kernel

/-- the twin claim satisfies the claim side conditions -/
theorem claimOK_toyF : ClaimOK toyClaimF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v h; fin_cases k <;> simp [Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun, toyClaimF, P, Nock.Field.p] at h ⊢ <;> omega
  · intro k h; fin_cases k <;> simp [Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun, Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.isCellN, toyClaimF,
      Nock.Noun.internal, P, Nock.Field.p] at h ⊢
  · intro x hx
    simp [Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.claimCells, Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun,
      Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.isCellN, toyClaimF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    fin_cases a <;> simp at ha ⊢
    refine ⟨?_, ?_⟩
    · show 2 ≤ Nock.NockVMROM.Thm54.VclL.fuelChip
      unfold Nock.NockVMROM.Thm54.VclL.fuelChip; norm_num
    · intro v hv
      simp [Nock.Noun.leafList] at hv
      rcases hv with rfl | rfl <;> norm_num [P, Nock.Field.p]
  · rfl

def Dtoy : NockvmE2E.Exec.E2EJ8.J8X.DatX (XI170 toy1X) hsh := DX (XI170 toy1X) hsh hJ 1 0 NockvmE2E.J8.RVUJ8.toyClaim
def DtoyF : NockvmE2E.Exec.E2EJ8.J8X.DatX (XI170 toy1XF) hshF := DX (XI170 toy1XF) hshF hJF 1 0 toyClaimF

theorem dat_toy : DatumOK Dtoy.d ∧ StmtP Dtoy.d :=
  datX_ok (XI170 toy1X) hsh hJ 1 0 le_rfl hkW hV0 _ claimOK_toy
theorem dat_toyF : DatumOK DtoyF.d ∧ StmtP DtoyF.d :=
  datX_ok (XI170 toy1XF) hshF hJF 1 0 le_rfl hkWF hV0F _ claimOK_toyF

theorem hlink : NockvmE2E.J8.RVUJ8.InpLink Dtoy.d (XI170 toy1X).pubIn := by
  have h := NockvmE2E.J8.RVUJ8.inpLink_toy1 Dtoy.d rfl rfl
  rw [← pubIn_eq] at h; exact h

theorem hlinkF : NockvmE2E.J8.RVUJ8.InpLink DtoyF.d (XI170 toy1XF).pubIn := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem hids : ∀ id ∈ Dtoy.d.Pb.regs, id < P := by
  intro id h
  have e : Dtoy.d.Pb.regs = [] := rfl
  rw [e] at h; cases h
theorem hidsF : ∀ id ∈ DtoyF.d.Pb.regs, id < P := by
  intro id h
  have e : DtoyF.d.Pb.regs = [] := rfl
  rw [e] at h; cases h

/-- the false claim is false: `*[0 [1 0]] = 0`, not `1` -/
theorem not_holds_F : ¬ Nock.Jet.HoldsN DtoyF.d.c := by
  have e : DtoyF.d.c = toyClaimF := rfl
  rw [e]
  rintro ⟨f, h⟩
  cases f <;> simp [Nock.evalN, toyClaimF] at h

/-! ## the table restriction `R hT hσ hfree` and a table pointer `tp` (as in `inst_RJ8`) -/
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8) in
theorem toy1_R : ∃ (R : NockvmE2E.J8.TabRestr (J8 Dtoy.d dat_toy.1)) (hT : R.T' = (XI170 toy1X).tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 toy1X) (Fin.cast hT t)) (hfree : (J8 Dtoy.d dat_toy.1).AccOn R.q) (tp : Fin R.T'), True :=
  ⟨RJ8 (XI170 toy1X) Dtoy.d dat_toy.1, rfl, fun _ => rfl,
    hfree_J8 (XI170 toy1X) hsh (posX_of_shape hsh) Dtoy.kroots Dtoy.krootsV Dtoy.Rt Dtoy.regs Dtoy.ids Dtoy.idx Dtoy.rk Dtoy.lay Dtoy.d Dtoy.hd dat_toy.1,
    ⟨0, by show 0 < (XI170 toy1X).tabs.size; decide⟩, trivial⟩

open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8) in
theorem toy1_RF : ∃ (R : NockvmE2E.J8.TabRestr (J8 DtoyF.d dat_toyF.1)) (hT : R.T' = (XI170 toy1XF).tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 toy1XF) (Fin.cast hT t)) (hfree : (J8 DtoyF.d dat_toyF.1).AccOn R.q) (tp : Fin R.T'), True :=
  ⟨RJ8 (XI170 toy1XF) DtoyF.d dat_toyF.1, rfl, fun _ => rfl,
    hfree_J8 (XI170 toy1XF) hshF (posX_of_shape hshF) DtoyF.kroots DtoyF.krootsV DtoyF.Rt DtoyF.regs DtoyF.ids DtoyF.idx DtoyF.rk DtoyF.lay DtoyF.d DtoyF.hd dat_toyF.1,
    ⟨0, by show 0 < (XI170 toy1XF).tabs.size; decide⟩, trivial⟩

end

end NockvmE2E.Exec.E2EJ8ToyD

#print axioms NockvmE2E.Exec.E2EJ8ToyD.dat_toy
#print axioms NockvmE2E.Exec.E2EJ8ToyD.dat_toyF
#print axioms NockvmE2E.Exec.E2EJ8ToyD.hlink
#print axioms NockvmE2E.Exec.E2EJ8ToyD.hlinkF
#print axioms NockvmE2E.Exec.E2EJ8ToyD.hsh
#print axioms NockvmE2E.Exec.E2EJ8ToyD.hshF
#print axioms NockvmE2E.Exec.E2EJ8ToyD.not_holds_F
#print axioms NockvmE2E.Exec.E2EJ8ToyD.toy1_R
#print axioms NockvmE2E.Exec.E2EJ8ToyD.toy1_RF
