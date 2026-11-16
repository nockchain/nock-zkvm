/-
 Nock/RedTeam/Batch4938Thm54TUP1Toy.lean

 **Non-vacuity toys** for `TraceUniqueP1Closed.trace_unique_prob_119`, with no extra chip or coin
 hypothesis. Two concrete claims, every claim-side binder of the headline discharged:
 * `*[[1 2] [0 2]] = 1` (`cT`, one `s0` row with a path read at axis 2): `fragT : P1FragC cT`,
 `okT : P1SizeOK Nock.Atoms.p cT` (`Rows31` and `RootsLeafOK` of the canonical data, through the perm facts of
 `ord8Canon` and small `decide`s), `runT : runP1 cT = some (tT, cT.result)` with `tT` explicit;
 * `*[[1 2] [[0 2] [0 3]]] = [1 2]` (`cC`, autocons, three rows, two path reads): `fragC`, `okC`, `runC`.
 `toy_trace_unique_119` / `toy_trace_unique_119_cons`: the headline at Goldilocks (`K = KC`, `δ = deltaF`,
 `b = powerBasis3`, `hpG = rfl`, `hcK = card_KC`); every instance (`CharP KC p`, `CharP 𝕂′ p`, the `ringChar`
 algebras) is constructed here, so the only binders left are the adversary `Q` and its staging `hQ : StJ8`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed
import Nock.TraceGenExe.K6
import Nock.TraceGenExe.PowerBasis

set_option autoImplicit false

namespace Nock.RedTeam.Batch4938

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1 (ord8Canon)

/-! ## 1. The toy `*[[1 2] [0 2]] = 1` -/

def sT : Noun := .cell (.atom 1) (.atom 2)
def fT : Noun := .cell (.atom 0) (.atom 2)
def rT : Noun := .atom 1
def cT : P8PublicClaim := ⟨sT, fT, rT⟩
def tT : NTree SkelX := mkX .s0 sT fT rT []

theorem genT : genX Nock.Jet.VerifiedRegistry.empty.R 3 sT fT = some (tT, rT) := by
  simp [genX, genComputeSkeletonX, sT, fT, tT, rT, Noun.slot]

theorem runT : runP1 cT = some (tT, cT.result) := genT

theorem fragT : P1FragC cT where
  ops := by simp [OpsP1, opsB, cT, fT]
  axes := by simp [axesB, cT, fT]
  small := by decide
  run := ⟨3, tT, by simp [genX, genComputeSkeletonX, cT, sT, fT, tT, rT, Noun.slot]⟩

theorem rowsT : ComplJ8Data.rowsOfT tT = #[rowOfSkelX tT.label] := by
  simp [ComplJ8Data.rowsOfT, bfsForest, tT, mkX]

theorem prT : Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tT) = [(sT, 2)] := by
  rw [rowsT]; decide

abbrev DT := DC Nock.Atoms.p runT

theorem readsT : DT.reads = [(sT, 2)] := by
  show ord8Canon.ordR _ (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tT)) = _
  have h := ord8Canon.permR DT.H (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tT))
  rw [prT] at h ⊢
  exact List.perm_singleton.mp h

theorem callsT : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tT) = [] := by rw [rowsT]; decide

theorem dcalls : DT.calls = [] := callsT

theorem rootsT : DT.roots = Nock.V1J8.Gen.rootsOf cT #[rowOfSkelX tT.label] := by
  show Nock.V1J8.Gen.rootsOf cT (ComplJ8Data.rowsOfT tT) ++ ComplJ8Data.jNounsP _ _ _ _ = _
  rw [callsT, rowsT]
  simp [ComplJ8Data.jNounsP]

theorem hleafT : ComplJ8Walk.RootsLeafOK DT.roots := by
  rw [rootsT]; unfold ComplJ8Walk.RootsLeafOK; decide

theorem cellsT : DT.cells.length = (Nock.V1J8.Gen.cellsOfRoots DT.roots).length :=
  (ord8Canon.permC _).length_eq

theorem cellsT2 : DT.cells.length ≤ 10 := by
  rw [cellsT, rootsT]; decide

theorem bigsT : DT.bigs = [] := by
  show ComplJ8Data.bigsP _ DT.roots (ComplJ8Data.rowsOfT tT) = []
  rw [rootsT, rowsT]
  unfold ComplJ8Data.bigsP
  rw [show List.filter _ _ = [] by decide]
  simp

theorem acsT : DT.acs.length ≤ 2 := by
  show (ComplJ8Data.acsP _ DT.bigs _).length ≤ 2
  rw [bigsT]
  simp [ComplJ8Data.acsP]
  decide

theorem preadsT : DT.preads = [] := by
  show ord8Canon.ordR _ (ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tT)) = []
  have : ∀ H pd, ComplJ8Data.pairReadsP H pd (ComplJ8Data.rowsOfT tT) = [] := by
    intro H pd
    rw [rowsT]
    simp [ComplJ8Data.pairReadsP, Nock.V1J8.FillX.isPairB, tT, mkX, rowOfSkelX]
  rw [this]; exact List.perm_nil.mp (ord8Canon.permR _ _)

theorem jrowsT : DT.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DT.calls).dedup DT.calls) _ = []
  rw [dcalls]; rfl

theorem walkT : (VclL.GenWalk.walkRows DT.cells DT.reads).length ≤ 2 ^ 31 := by
  have := VclL.GenWalk.walkRows_length_le DT.cells DT.reads
  rw [readsT] at this ⊢
  have h2 : VclL.pathReads [(sT, 2)] = [(sT, 2)] := by decide
  rw [h2] at this
  simp at this
  have hd : VclL.depthOf 2 ≤ 2 ^ 31 := by decide
  omega

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (sizesJ8 nVOf Rows31) in
theorem h31T : Rows31 DT := by
  intro x hx
  simp only [sizesJ8, nVOf, preadsT, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DT.t]).length = 1 := by
    show (bfsForest [tT]).length = 1
    simp [bfsForest, tT, mkX]
  have hC := cellsT2
  have hA := acsT
  have hW := walkT
  have hJ : DT.jrows.length = 0 := by rw [jrowsT]; rfl
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem okT : P1SizeOK Nock.Atoms.p cT := (P1SizeOK_of Nock.Atoms.p runT).2 ⟨h31T, hleafT⟩

open Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (StJ8)
open Nock.TraceGenExe (KC deltaF powerBasis3)

instance factRC : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
instance charPKC : CharP KC (ringChar (ZMod Nock.Field.p)) := by
  rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
noncomputable instance algRC : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra _ _

instance charPKCp : CharP KC Nock.Atoms.p :=
  charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _

instance charPQp : CharP (Quad (algebraMap (ZMod Nock.Atoms.p) KC deltaF)) Nock.Atoms.p :=
  charP_of_injective_algebraMap (algebraMap KC (Quad (algebraMap (ZMod Nock.Atoms.p) KC deltaF))).injective _

theorem card_KC : Fintype.card KC = VclL.Events.cK := by
  rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq]

open Classical in
/-- **`trace_unique_prob_119` at `*[[1 2] [0 2]] = 1`**, no claim-side or field hypothesis. -/
theorem toy_trace_unique_119
    (Q : Coins frameJ8 KC → TripP1 Nock.Atoms.p KC deltaF) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        AcceptsCanonP1 deltaF powerBasis3 rfl (szOfClaim Nock.Atoms.p) (canonPb rfl (szOfClaim Nock.Atoms.p) cT)
          Nock.Jet.VerifiedRegistry.empty.R cT χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb rfl (szOfClaim Nock.Atoms.p) cT)) 0 ∧
        Q χ ≠ canonOfP1 deltaF powerBasis3 rfl runT okT χ).card : ℚ) / Fintype.card (Coins frameJ8 KC)
      < 1 / (2 : ℚ) ^ 119 :=
  trace_unique_prob_119 deltaF powerBasis3 rfl fragT okT runT card_KC Q hQ

/-! ## 2. The autocons toy `*[[1 2] [[0 2] [0 3]]] = [1 2]` -/

def fC : Noun := .cell (.cell (.atom 0) (.atom 2)) (.cell (.atom 0) (.atom 3))
def rC : Noun := .cell (.atom 1) (.atom 2)
def cC : P8PublicClaim := ⟨sT, fC, rC⟩
def tL : NTree SkelX := mkX .s0 sT (.cell (.atom 0) (.atom 2)) (.atom 1) []
def tR : NTree SkelX := mkX .s0 sT (.cell (.atom 0) (.atom 3)) (.atom 2) []
def tC : NTree SkelX := mkX .cons sT fC rC [tL, tR]

theorem runC : runP1 cC = some (tC, cC.result) := by
  simp [runP1, fz, cC, fC, genX, genComputeSkeletonX, sT, tC, tL, tR, rC, Noun.slot]

theorem fragC : P1FragC cC where
  ops := by simp [OpsP1, opsB, cC, fC]
  axes := by simp [axesB, cC, fC]
  small := by decide
  run := ⟨fz fC, tC, runC⟩

theorem rowsC : ComplJ8Data.rowsOfT tC = #[rowOfSkelX tC.label, rowOfSkelX tL.label, rowOfSkelX tR.label] := by
  simp [ComplJ8Data.rowsOfT, bfsForest, tC, tL, tR, mkX]

theorem prC : Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tC) = [(sT, 2), (sT, 3)] := by
  rw [rowsC]; decide

abbrev DCc := DC Nock.Atoms.p runC

theorem walkC : (VclL.GenWalk.walkRows DCc.cells DCc.reads).length ≤ 2 ^ 31 := by
  have h := VclL.GenWalk.walkRows_length_le DCc.cells DCc.reads
  have hp : DCc.reads.Perm [(sT, 2), (sT, 3)] := by
    show (ord8Canon.ordR DCc.H (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tC))).Perm _
    rw [prC]; exact ord8Canon.permR _ _
  have hpp : (VclL.pathReads DCc.reads).Perm (VclL.pathReads [(sT, 2), (sT, 3)]) :=
    (hp.filter _).dedup
  rw [(hpp.map _).sum_eq] at h
  have h2 : ((VclL.pathReads [(sT, 2), (sT, 3)]).map fun r => VclL.depthOf r.2).sum ≤ 10 := by decide
  split_ifs at h <;> omega

theorem callsC : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tC) = [] := by rw [rowsC]; decide

theorem rootsC : DCc.roots = Nock.V1J8.Gen.rootsOf cC #[rowOfSkelX tC.label, rowOfSkelX tL.label, rowOfSkelX tR.label] := by
  show Nock.V1J8.Gen.rootsOf cC (ComplJ8Data.rowsOfT tC) ++ ComplJ8Data.jNounsP _ _ _ _ = _
  rw [callsC, rowsC]
  simp [ComplJ8Data.jNounsP]

theorem hleafC : ComplJ8Walk.RootsLeafOK DCc.roots := by
  rw [rootsC]; unfold ComplJ8Walk.RootsLeafOK; decide

theorem cellsC : DCc.cells.length ≤ 20 := by
  rw [show DCc.cells.length = (Nock.V1J8.Gen.cellsOfRoots DCc.roots).length from (ord8Canon.permC _).length_eq,
    rootsC]
  decide

theorem bigsC : DCc.bigs = [] := by
  show ComplJ8Data.bigsP _ DCc.roots (ComplJ8Data.rowsOfT tC) = []
  rw [rootsC, rowsC]
  unfold ComplJ8Data.bigsP
  rw [show List.filter _ _ = [] by decide]
  simp

theorem acsC : DCc.acs.length ≤ 2 := by
  show (ComplJ8Data.acsP _ DCc.bigs _).length ≤ 2
  rw [bigsC]
  simp [ComplJ8Data.acsP]
  decide

theorem preadsC : DCc.preads = [] := by
  show ord8Canon.ordR _ (ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tC)) = []
  have : ∀ H pd, ComplJ8Data.pairReadsP H pd (ComplJ8Data.rowsOfT tC) = [] := by
    intro H pd
    rw [rowsC]
    simp [ComplJ8Data.pairReadsP, Nock.V1J8.FillX.isPairB, tC, tL, tR, mkX, rowOfSkelX]
  rw [this]; exact List.perm_nil.mp (ord8Canon.permR _ _)

theorem jrowsC : DCc.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DCc.calls).dedup DCc.calls) _ = []
  rw [show DCc.calls = [] from callsC]; rfl

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (sizesJ8 nVOf Rows31) in
theorem h31C : Rows31 DCc := by
  intro x hx
  simp only [sizesJ8, nVOf, preadsC, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DCc.t]).length = 3 := by
    show (bfsForest [tC]).length = 3
    simp [bfsForest, tC, tL, tR, mkX]
  have hC := cellsC
  have hA := acsC
  have hW := walkC
  have hJ : DCc.jrows.length = 0 := by rw [jrowsC]; rfl
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem okC : P1SizeOK Nock.Atoms.p cC := (P1SizeOK_of Nock.Atoms.p runC).2 ⟨h31C, hleafC⟩

open Classical in
/-- **`trace_unique_prob_119` at the autocons claim `*[[1 2] [[0 2] [0 3]]] = [1 2]`**. -/
theorem toy_trace_unique_119_cons
    (Q : Coins frameJ8 KC → TripP1 Nock.Atoms.p KC deltaF) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        AcceptsCanonP1 deltaF powerBasis3 rfl (szOfClaim Nock.Atoms.p) (canonPb rfl (szOfClaim Nock.Atoms.p) cC)
          Nock.Jet.VerifiedRegistry.empty.R cC χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb rfl (szOfClaim Nock.Atoms.p) cC)) 0 ∧
        Q χ ≠ canonOfP1 deltaF powerBasis3 rfl runC okC χ).card : ℚ) / Fintype.card (Coins frameJ8 KC)
      < 1 / (2 : ℚ) ^ 119 :=
  trace_unique_prob_119 deltaF powerBasis3 rfl fragC okC runC card_KC Q hQ

end

end Nock.RedTeam.Batch4938

#print axioms Nock.RedTeam.Batch4938.fragT
#print axioms Nock.RedTeam.Batch4938.okT
#print axioms Nock.RedTeam.Batch4938.runT
#print axioms Nock.RedTeam.Batch4938.toy_trace_unique_119
#print axioms Nock.RedTeam.Batch4938.fragC
#print axioms Nock.RedTeam.Batch4938.okC
#print axioms Nock.RedTeam.Batch4938.runC
#print axioms Nock.RedTeam.Batch4938.toy_trace_unique_119_cons
