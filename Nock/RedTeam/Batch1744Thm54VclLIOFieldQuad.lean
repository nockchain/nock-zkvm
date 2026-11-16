/-
  Nock/RedTeam/Batch1744Thm54VclLIOFieldQuad.lean

  **Receipts for the VCL-L chips at `𝕂′` IO coins.**

  §A  `ioSpecVCL` at `Kio := Quad δ` (`mk := Quad.mk δ`, injective; `|Kio| = |𝕂|²`; four M2
      coins), and `epsilon_vcll_eq_quad`: R-V3b's `epsilon_vcll_eq` with `hI` / `hKio` DISCHARGED
      at `I := ioSpecVCLQuad δ'` — the closure of R-LC6's unconfirmed `Quad` instantiation.
  §B  The tower layouts: cell `128 / 54 / 36 = 218`, path `17 / 72 / 24 = 113`; records `5 / 10 / 8`
      at `𝕂′` entries (`= mVCL`); `mv`, `mx`, `m` round-0 `𝔽` columns with no range bits.
  §C  Degree: the `𝕂′` inverse gate, the weighted step and an `RLC′` term in `𝕂` coordinates
      (bilinear; degree `2` in the trace columns before masks).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.IOField
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1744

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Events

/-! ## §A  The IO coins in `Quad δ` -/

#print axioms quadMk_inj
#print axioms ioSpecVCLQuad_coins
#print axioms ioSpecVCLQuad_dep_card
#print axioms ioSpecVCLQuad_round
#print axioms ioSpecVCLQuad_card
#print axioms quad_charP

section Eps10
variable {F K Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp]
  (δ δ' : K) [Fact (¬ IsSquare δ)] [Fact (¬ IsSquare δ')] [DecidableEq (Quad δ')]
  {q : ℕ} {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ} {C : TableSpec}
  {R : RecordView F K (Quad δ') Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL10}
  {Z : SeedSpec frameVCL K Kfp}
  (CF : CompSoundnessFamily F K (Quad δ') Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z
    (ioSpecVCLQuad δ'))
  (MF : MemSoundnessFamily F K (Quad δ') Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z
    (ioSpecVCLQuad δ'))
  (Dc : VclB0Decode F C q hT hP wT wP rT rP)

theorem epsilon_vcll_eq_quad_w10 (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0)
    (hMF : MF.summands V y = vclMemSummands δ Dc V)
    (hCF : epsilonOf (CF.summands V x) = (computeWork V.N : ℚ) / (Fintype.card K : ℚ))
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a =
      totVCL V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) =
      boundVCL' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) :=
  epsilon_vcll_eq_w10 δ CF MF Dc V x y hMF hCF hZ hW (ioSpecVCLQuad_dep_card δ') (quad_card δ') hinl htot

end Eps10

#print axioms epsilon_vcll_eq_quad_w10

section Eps
variable {F K Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp]
  (δ δ' : K) [Fact (¬ IsSquare δ)] [Fact (¬ IsSquare δ')] [DecidableEq (Quad δ')]
  {q : ℕ} {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ} {C : TableSpec}
  {R : RecordView F K (Quad δ') Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL}
  {Z : SeedSpec frameVCL K Kfp}
  (CF : CompSoundnessFamily F K (Quad δ') Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z
    (ioSpecVCLQuad δ'))
  (MF : MemSoundnessFamily F K (Quad δ') Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z
    (ioSpecVCLQuad δ'))
  (Dc : VclB0Decode F C q hT hP wT wP rT rP)

theorem epsilon_vcll_eq_quad (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0)
    (hMF : MF.summands V y = vclMemSummands δ Dc V)
    (hCF : epsilonOf (CF.summands V x) = (computeWork V.N : ℚ) / (Fintype.card K : ℚ))
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a =
      totVCLS V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) =
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) :=
  epsilon_vcll_eq δ CF MF Dc V x y hMF hCF hZ hW (ioSpecVCLQuad_dep_card δ') (quad_card δ') hinl htot

end Eps

#print axioms epsilon_vcll_eq_quad

/-! ## §B  Layouts and record widths -/

#print axioms Cell.widthT_eq
#print axioms Cell.card_roundT0
#print axioms Cell.card_roundT1
#print axioms Cell.card_roundT2
#print axioms Cell.mult_round0
#print axioms Path.widthT_eq
#print axioms Path.card_roundT0
#print axioms Path.card_roundT1
#print axioms Path.card_roundT2
#print axioms Path.mult_round0
#print axioms record_widths_tower
#print axioms mVCL_eq_tower
#print axioms rank_entry_inj

/-! ## §C  Degree in coordinates -/

#print axioms inverse_gate_coords
#print axioms weighted_step_coords
#print axioms rlc_term_coords

/-! ## §D  `serves` and the consumer counts -/

#print axioms vcl_serves_of_count
#print axioms path_count_lt
#print axioms validity_count_lt
#print axioms validity_count_not_from_hrowsM
#print axioms export_count_not_derivable

end Nock.RedTeam.Batch1744
