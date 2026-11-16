/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHProj.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStatic
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axReadsK9 axKeys9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX

def cJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : P8PublicClaim := ⟨s, f, Rn.res⟩
def rootsJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := rootsOf (cJ s f χe Rn) Rn.rows
def csJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := cellsOfRoots (rootsJ s f χe Rn)
def acsLJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  acsOfD (bigsOf (rootsJ s f χe Rn) Rn.rows) ((incOps Rn.rows).any fun x => x.1 + 1 = P)
def HJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := hdlB (csJ s f χe Rn) (acsLJ s f χe Rn)
def ptJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := ptrE (acsLJ s f χe Rn) (stopEdges Rn.rows)
def pdJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := HonestPairX.pdX (sxE (ptJ s f χe Rn))
def rows9J (s f : Noun) (χe : CoinsE) (Rn : RunX) := rowsOfT9 Rn.t
def W9J (s f : Noun) (χe : CoinsE) (Rn : RunX) := bfsForest [genX9T Rn.t]
def fxJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := fieldAx9 P (rows9J s f χe Rn)
def idOfJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  idOf9 P (acsLJ s f χe Rn).length (HJ s f χe Rn) (fxJ s f χe Rn)
def compJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  GenCompX9.compGenX9 (cJ s f χe Rn) (HJ s f χe Rn) (pdJ s f χe Rn) (idOfJ s f χe Rn) (W9J s f χe Rn) χe
def wsKrJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  walkGen ((csJ s f χe Rn).headD (.atom 0))
    (walkReadsX9 (rows9J s f χe Rn) ++ axChainReadsK9 (rows9J s f χe Rn))
def mvJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := mvCounts (csJ s f χe Rn) (cJ s f χe Rn)
def mxJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := mxCounts (csJ s f χe Rn) (wsKrJ s f χe Rn).1
def mx1J (s f : Noun) (χe : CoinsE) (Rn : RunX) := Array.replicate (csJ s f χe Rn).length 0
def mhJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  mhCountsX9E (csJ s f χe Rn) (compJ s f χe Rn).bases (wsKrJ s f χe Rn).1
def kJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := coOf χe
def alphaJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := chalsMJ8E χe 0
def gammaJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := chalsMJ8E χe 1
def cRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  cellGenB (kJ s f χe Rn) (yE χe) (HJ s f χe Rn) (bigIdOf (acsLJ s f χe Rn)) (csJ s f χe Rn)
    (mvJ s f χe Rn) (mxJ s f χe Rn) (mx1J s f χe Rn) (mhJ s f χe Rn)
def wRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  walkGenRowsB (kJ s f χe Rn) (yE χe) (alphaJ s f χe Rn) (gammaJ s f χe Rn) (HJ s f χe Rn)
    (idxN (csJ s f χe Rn)) HonestK8.certB8 (csJ s f χe Rn) (wsKrJ s f χe Rn).1 (wsKrJ s f χe Rn).2
def readsJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  pairReads (HJ s f χe Rn) (pdJ s f χe Rn) Rn.rows ++ axReadsK9 P (rows9J s f χe Rn)
def vsKrVJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  if (readsJ s f χe Rn).isEmpty then ([], 0) else walkGen padN (readsJ s f χe Rn)
def HAJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : Noun → ℕ × ℕ := Nock.V1J8.Gen.hdl (acsLJ s f χe Rn)
def rIAJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : Noun → ℕ :=
  fun n => if n = combP then lastIdxOf (acsLJ s f χe Rn) combP else idxN (acsLJ s f χe Rn) n
def aRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  atomGenE (ptJ s f χe Rn) χe (acsLJ s f χe Rn) (infoOfE (acsLJ s f χe Rn) (ptJ s f χe Rn) Rn.rows)
    (mbCounts9 (acsLJ s f χe Rn) (csJ s f χe Rn) (cJ s f χe Rn))
    (wCounts (rIAJ s f χe Rn) (acsLJ s f χe Rn) (vsKrVJ s f χe Rn).1)
    (wCounts (rIAJ s f χe Rn) (acsLJ s f χe Rn) (vsKrVJ s f χe Rn).1)
def vRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : Array (Array (ZMod P)) × (ℕ → K3) :=
  if (vsKrVJ s f χe Rn).2 = 0 then (#[Array.replicate 166 0], fun _ => 0)
  else walkGenRowsBE (ptJ s f χe Rn) (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1)
    (HAJ s f χe Rn) (rIAJ s f χe Rn) WalkJ8.certB (acsLJ s f χe Rn) (vsKrVJ s f χe Rn).1
    (vsKrVJ s f χe Rn).2
def axOnJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := !(axKeys9 (rows9J s f χe Rn)).isEmpty
def spOnJ (s f : Noun) (χe : CoinsE) (Rn : RunX) := !(fxJ s f χe Rn).isEmpty
def xRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  GenAxE.axGenOf χe (acsLJ s f χe Rn).length (HJ s f χe Rn) (rows9J s f χe Rn) (axOnJ s f χe Rn)
def sRPJ (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  if spOnJ s f χe Rn then
    GenSpE.spGenE χe (acsLJ s f χe Rn).length (GenSpE.vSE (rows9J s f χe Rn))
      (GenSpE.mSE (rows9J s f χe Rn) (GenSpE.vSE (rows9J s f χe Rn)))
  else (#[Array.replicate 90 0], fun _ => (0 : K3))
def mJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ :=
  max (compJ s f χe Rn).rows.size (max (cRPJ s f χe Rn).1.size (max (wRPJ s f χe Rn).1.size
    (max (aRPJ s f χe Rn).1.size (max (vRPJ s f χe Rn).1.size
      (max (xRPJ s f χe Rn).1.size (sRPJ s f χe Rn).1.size)))))
def BJ (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ := max 10 (2 * mJ s f χe Rn)

section fields
variable (s f : Noun) (χe : CoinsE) (Rn : RunX)

theorem rec_c : (recJ9AXRn s f χe Rn).c = cJ s f χe Rn := rfl
theorem rec_M_m : (recJ9AXRn s f χe Rn).M.m = mOf (cJ s f χe Rn) (HJ s f χe Rn) := rfl
theorem rec_M_ρ : (recJ9AXRn s f χe Rn).M.ρ = (compJ s f χe Rn).ρ := rfl
theorem rec_M_ρS : (recJ9AXRn s f χe Rn).M.ρS = (compJ s f χe Rn).ρS := rfl
theorem rec_M_pubsC : (recJ9AXRn s f χe Rn).M.pubsC = (cRPJ s f χe Rn).2 := rfl
theorem rec_M_pubsW : (recJ9AXRn s f χe Rn).M.pubsW = (wRPJ s f χe Rn).2 := rfl
theorem rec_M_pubsJ : (recJ9AXRn s f χe Rn).M.pubsJ = fun _ => 0 := rfl
theorem rec_M_pubsA : (recJ9AXRn s f χe Rn).M.pubsA = (aRPJ s f χe Rn).2 := rfl
theorem rec_M_pubsV : (recJ9AXRn s f χe Rn).M.pubsV = (vRPJ s f χe Rn).2 := rfl
theorem rec_χ : (recJ9AXRn s f χe Rn).χ = χe := rfl
theorem rec_r : (recJ9AXRn s f χe Rn).r = budget (mJ s f χe Rn) := rfl
theorem rec_g : (recJ9AXRn s f χe Rn).g = 0 := rfl
theorem rec_X : (recJ9AXRn s f χe Rn).X = chipOf (compJ s f χe Rn).rows := rfl
theorem rec_C : (recJ9AXRn s f χe Rn).C = chipOf (cRPJ s f χe Rn).1 := rfl
theorem rec_W : (recJ9AXRn s f χe Rn).W = chipOf (wRPJ s f χe Rn).1 := rfl
theorem rec_J_n : (recJ9AXRn s f χe Rn).J.n = 0 := rfl
theorem rec_A : (recJ9AXRn s f χe Rn).A = chipOf (aRPJ s f χe Rn).1 := rfl
theorem rec_V : (recJ9AXRn s f χe Rn).V = chipOf (vRPJ s f χe Rn).1 := rfl
theorem rec_kroots : (recJ9AXRn s f χe Rn).kroots = (wsKrJ s f χe Rn).2 := rfl
theorem rec_krootsV : (recJ9AXRn s f χe Rn).krootsV = (vsKrVJ s f χe Rn).2 := rfl
theorem rec_Rt : (recJ9AXRn s f χe Rn).Rt = Example.RtG := rfl
theorem rec_regs : (recJ9AXRn s f χe Rn).regs = [] := rfl
theorem rec_ids : (recJ9AXRn s f χe Rn).ids = [] := rfl
theorem rec_idx : (recJ9AXRn s f χe Rn).idx = fun _ => 0 := rfl
theorem rec_rk : (recJ9AXRn s f χe Rn).rk = fun _ => (0, 0) := rfl
theorem rec_AX : (recJ9AXRn s f χe Rn).AX = chipOf (xRPJ s f χe Rn).1 := rfl
theorem rec_SP : (recJ9AXRn s f χe Rn).SP = chipOf (sRPJ s f χe Rn).1 := rfl
theorem rec_pubsX : (recJ9AXRn s f χe Rn).pubsX = (xRPJ s f χe Rn).2 := rfl
theorem rec_pubsS : (recJ9AXRn s f χe Rn).pubsS = (sRPJ s f χe Rn).2 := rfl
theorem rec_axOn : (recJ9AXRn s f χe Rn).axOn = axOnJ s f χe Rn := rfl
theorem rec_spOn : (recJ9AXRn s f χe Rn).spOn = spOnJ s f χe Rn := rfl
theorem rec_rAX : (recJ9AXRn s f χe Rn).rAX = BJ s f χe Rn := rfl
theorem rec_rSP : (recJ9AXRn s f χe Rn).rSP = BJ s f χe Rn := rfl

theorem sRPJ_of_spOn (h : spOnJ s f χe Rn = true) :
    sRPJ s f χe Rn = GenSpE.spGenE χe (acsLJ s f χe Rn).length (GenSpE.vSE (rows9J s f χe Rn))
      (GenSpE.mSE (rows9J s f χe Rn) (GenSpE.vSE (rows9J s f χe Rn))) := by
  unfold sRPJ; rw [if_pos h]

theorem sRPJ_of_not_spOn (h : spOnJ s f χe Rn = false) :
    sRPJ s f χe Rn = (#[Array.replicate 90 0], fun _ => (0 : K3)) := by
  unfold sRPJ; rw [h]; rfl

theorem vRPJ_of_krV_zero (h : (vsKrVJ s f χe Rn).2 = 0) :
    vRPJ s f χe Rn = (#[Array.replicate 166 0], fun _ => 0) := by
  unfold vRPJ; rw [if_pos h]

theorem vRPJ_of_krV_ne (h : (vsKrVJ s f χe Rn).2 ≠ 0) :
    vRPJ s f χe Rn = walkGenRowsBE (ptJ s f χe Rn) (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1)
      (HAJ s f χe Rn) (rIAJ s f χe Rn) WalkJ8.certB (acsLJ s f χe Rn) (vsKrVJ s f χe Rn).1
      (vsKrVJ s f χe Rn).2 := by
  unfold vRPJ; rw [if_neg h]

theorem BJ_eq : BJ s f χe Rn = max 10 (2 * mJ s f χe Rn) := rfl

theorem staticHyp_rec :
    GenPortJ9AHStatic.StaticHyp (recJ9AXRn s f χe Rn) (mJ s f χe Rn) := by
  refine ⟨rec_r s f χe Rn, rec_g s f χe Rn, (rec_rAX s f χe Rn).trans (BJ_eq s f χe Rn),
    (rec_rSP s f χe Rn).trans (BJ_eq s f χe Rn), rec_J_n s f χe Rn, rec_regs s f χe Rn,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rec_X s f χe Rn]
    show (compJ s f χe Rn).rows.size ≤ mJ s f χe Rn
    exact le_max_left _ _
  · rw [rec_C s f χe Rn]
    show (cRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [rec_W s f χe Rn]
    show (wRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · rw [rec_A s f χe Rn]
    show (aRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  · rw [rec_V s f χe Rn]
    show (vRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  · rw [rec_AX s f χe Rn]
    show (xRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))))
  · rw [rec_SP s f χe Rn]
    show (sRPJ s f χe Rn).1.size ≤ mJ s f χe Rn
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))))

end fields

/-! ## `recJ9AX` versions -/

section recX
variable (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun)

/-- The run `recJ9AX` uses. -/
def RnOf (t : NTree SkelX) (r : Noun) : RunX := ⟨t, r, bfsForest [t], ComplJ8Data.rowsOfT t⟩

theorem recJ9AX_eq : recJ9AX s f χe t r = recJ9AXRn s f χe (RnOf t r) := rfl

theorem recX_c : (recJ9AX s f χe t r).c = cJ s f χe (RnOf t r) := rfl
theorem recX_M_m : (recJ9AX s f χe t r).M.m = mOf (cJ s f χe (RnOf t r)) (HJ s f χe (RnOf t r)) := rfl
theorem recX_M_ρ : (recJ9AX s f χe t r).M.ρ = (compJ s f χe (RnOf t r)).ρ := rfl
theorem recX_M_pubsC : (recJ9AX s f χe t r).M.pubsC = (cRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_M_pubsW : (recJ9AX s f χe t r).M.pubsW = (wRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_M_pubsA : (recJ9AX s f χe t r).M.pubsA = (aRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_M_pubsV : (recJ9AX s f χe t r).M.pubsV = (vRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_χ : (recJ9AX s f χe t r).χ = χe := rfl
theorem recX_r : (recJ9AX s f χe t r).r = budget (mJ s f χe (RnOf t r)) := rfl
theorem recX_g : (recJ9AX s f χe t r).g = 0 := rfl
theorem recX_X : (recJ9AX s f χe t r).X = chipOf (compJ s f χe (RnOf t r)).rows := rfl
theorem recX_C : (recJ9AX s f χe t r).C = chipOf (cRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_W : (recJ9AX s f χe t r).W = chipOf (wRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_J_n : (recJ9AX s f χe t r).J.n = 0 := rfl
theorem recX_A : (recJ9AX s f χe t r).A = chipOf (aRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_V : (recJ9AX s f χe t r).V = chipOf (vRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_kroots : (recJ9AX s f χe t r).kroots = (wsKrJ s f χe (RnOf t r)).2 := rfl
theorem recX_krootsV : (recJ9AX s f χe t r).krootsV = (vsKrVJ s f χe (RnOf t r)).2 := rfl
theorem recX_regs : (recJ9AX s f χe t r).regs = [] := rfl
theorem recX_AX : (recJ9AX s f χe t r).AX = chipOf (xRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_SP : (recJ9AX s f χe t r).SP = chipOf (sRPJ s f χe (RnOf t r)).1 := rfl
theorem recX_pubsX : (recJ9AX s f χe t r).pubsX = (xRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_pubsS : (recJ9AX s f χe t r).pubsS = (sRPJ s f χe (RnOf t r)).2 := rfl
theorem recX_axOn : (recJ9AX s f χe t r).axOn = axOnJ s f χe (RnOf t r) := rfl
theorem recX_spOn : (recJ9AX s f χe t r).spOn = spOnJ s f χe (RnOf t r) := rfl
theorem recX_rAX : (recJ9AX s f χe t r).rAX = BJ s f χe (RnOf t r) := rfl
theorem recX_rSP : (recJ9AX s f χe t r).rSP = BJ s f χe (RnOf t r) := rfl

theorem staticHyp_recX :
    GenPortJ9AHStatic.StaticHyp (recJ9AX s f χe t r) (mJ s f χe (RnOf t r)) :=
  staticHyp_rec s f χe (RnOf t r)

end recX

#print axioms rec_c
#print axioms rec_M_m
#print axioms rec_M_ρ
#print axioms rec_M_ρS
#print axioms rec_M_pubsC
#print axioms rec_M_pubsW
#print axioms rec_M_pubsJ
#print axioms rec_M_pubsA
#print axioms rec_M_pubsV
#print axioms rec_χ
#print axioms rec_r
#print axioms rec_g
#print axioms rec_X
#print axioms rec_C
#print axioms rec_W
#print axioms rec_J_n
#print axioms rec_A
#print axioms rec_V
#print axioms rec_kroots
#print axioms rec_krootsV
#print axioms rec_Rt
#print axioms rec_regs
#print axioms rec_ids
#print axioms rec_idx
#print axioms rec_rk
#print axioms rec_AX
#print axioms rec_SP
#print axioms rec_pubsX
#print axioms rec_pubsS
#print axioms rec_axOn
#print axioms rec_spOn
#print axioms rec_rAX
#print axioms rec_rSP
#print axioms sRPJ_of_spOn
#print axioms sRPJ_of_not_spOn
#print axioms vRPJ_of_krV_zero
#print axioms vRPJ_of_krV_ne
#print axioms staticHyp_rec
#print axioms recJ9AX_eq
#print axioms recX_c
#print axioms recX_M_m
#print axioms recX_M_ρ
#print axioms recX_M_pubsC
#print axioms recX_M_pubsW
#print axioms recX_M_pubsA
#print axioms recX_M_pubsV
#print axioms recX_χ
#print axioms recX_r
#print axioms recX_g
#print axioms recX_X
#print axioms recX_C
#print axioms recX_W
#print axioms recX_J_n
#print axioms recX_A
#print axioms recX_V
#print axioms recX_kroots
#print axioms recX_krootsV
#print axioms recX_regs
#print axioms recX_AX
#print axioms recX_SP
#print axioms recX_pubsX
#print axioms recX_pubsS
#print axioms recX_axOn
#print axioms recX_spOn
#print axioms recX_rAX
#print axioms recX_rSP
#print axioms staticHyp_recX

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
