/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHJRun.lean

  **Honest link: the run record of `genJ9ALXJ`, built from `genJ9AXJ`'s named pieces.**

  * `recJ9ALXJRn Rt prims s f χe Rn` / `recJ9ALXJ …`: the let-chain of `genJ9ALXJ` as named terms.  Every term that
    does not mention the J / ALU split is the `…K` term of `GenPortJ9AHJRun` (the generator's `jn` runs over all
    calls, so `cs acs H pd idOf comp ws idx` agree with `genJ9AXJ`'s by construction); only the overlay is new
    (`callsJLK regsJLK … lRPLK`);
  * `genJ9ALXJ_eq` (defeq unfold), `genJ9ALXJ_some`;
  * `toInJ9A_X/W/V/AX/SP/kroots/krootsV/c/χ/axOn/spOn`: the projections to the J9A record, by `rfl`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
import Nock.V1J9AL.GenJ9ALXJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf rows9J W9J fxJ axOnJ spOnJ)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX
open Nock.V1J9AL.CheckJ9AL
open Nock.V1J9AL.GenJ9ALXJ (genJ9ALXJ)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.Jet.Autogen (compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (jNounsP mvFixP pinsOfP hJd mhJP bumpAll)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (jCallsP aCallsP pcallsR primsC idxPOf rkPOf aluXL aluBL primPinL)
open Nock.Jet.Prim (PrimOp)

/-! ## 1. The overlay terms (the J layer and the ALU), over the shared `…K` terms -/

section defs

def callsJLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    List (ℕ × Noun) := jCallsP (prims.map Prod.fst) (callsK Rt s f χe Rn)
def idsJLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    List ℕ := (callsJLK Rt prims s f χe Rn).map Prod.fst
def regsJLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    List ℕ := (idsJLK Rt prims s f χe Rn).dedup
def psCLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    List (ℕ × PrimOp) := primsC prims (idsK Rt s f χe Rn)
def pcLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    List (ℕ × Noun × Noun) := pcallsR (prims.map Prod.fst) Rn.rows
def layLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  layoutJ8 Rt (regsJLK Rt prims s f χe Rn) (idsJLK Rt prims s f χe Rn)
def jrowsLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  mvFixP P (Nock.Jet.ChipJ8.honestJ8G (hJd P (csK Rt s f χe Rn) (acsK Rt s f χe Rn)) Rt
    (regsJLK Rt prims s f χe Rn) (callsJLK Rt prims s f χe Rn))
    (pinsOfP P (regsJLK Rt prims s f χe Rn) (idxK Rt s f χe Rn))
def jgLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  jGen χe (jrowsLK Rt prims s f χe Rn)
def mvLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  bumpAll (mvPins (mvCounts (csK Rt s f χe Rn) (cK Rt s f χe Rn)) (regsJLK Rt prims s f χe Rn) (idxK Rt s f χe Rn))
    (primPinL (csK Rt s f χe Rn) prims (idsK Rt s f χe Rn))
def mhLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  bumpAll (mhJP P (mhCountsX9E (csK Rt s f χe Rn) (compK Rt s f χe Rn).bases (wsKrK Rt s f χe Rn).1)
    (jrowsLK Rt prims s f χe Rn)) (aluXL (csK Rt s f χe Rn) (pcLK Rt prims s f χe Rn))
def cRPLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  cellGenB (coOf χe) (yE χe) (HK Rt s f χe Rn) (bigIdOf (acsK Rt s f χe Rn)) (csK Rt s f χe Rn)
    (mvLK Rt prims s f χe Rn) (mxK Rt s f χe Rn) (mx1K Rt s f χe Rn) (mhLK Rt prims s f χe Rn)
def mbLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  bumpAll (mbCounts9 (acsK Rt s f χe Rn) (csK Rt s f χe Rn) (cK Rt s f χe Rn))
    (aluBL P (acsK Rt s f χe Rn) (pcLK Rt prims s f χe Rn))
def aRPLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :=
  atomGenE (ptK Rt s f χe Rn) χe (acsK Rt s f χe Rn)
    (infoOfE (acsK Rt s f χe Rn) (ptK Rt s f χe Rn) Rn.rows)
    (mbLK Rt prims s f χe Rn)
    (wCounts (rIAK Rt s f χe Rn) (acsK Rt s f χe Rn) (vsKrVK Rt s f χe Rn).1)
    (wCounts (rIAK Rt s f χe Rn) (acsK Rt s f χe Rn) (vsKrVK Rt s f χe Rn).1)
def aluOnLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) : Bool :=
  !(pcLK Rt prims s f χe Rn).isEmpty
def lRPLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    Array (Array (ZMod P)) × (ℕ → K3) :=
  if aluOnLK Rt prims s f χe Rn then
    Nock.V1J9AL.GenAluE.aluGenE χe (csK Rt s f χe Rn) (HK Rt s f χe Rn) (psCLK Rt prims s f χe Rn)
      (idsK Rt s f χe Rn) (pcLK Rt prims s f χe Rn)
  else Nock.V1J9AL.GenAluE.zeroChip
def mLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ :=
  max (compK Rt s f χe Rn).rows.size (max (cRPLK Rt prims s f χe Rn).1.size (max (wRPK Rt s f χe Rn).1.size
    (max (aRPLK Rt prims s f χe Rn).1.size (max (vRPK Rt s f χe Rn).1.size (max (xRPK Rt s f χe Rn).1.size
      (max (sRPK Rt s f χe Rn).1.size (max (layLK Rt prims s f χe Rn).length (lRPLK Rt prims s f χe Rn).1.size)))))))
def BLK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) : ℕ :=
  max 10 (2 * mLK Rt prims s f χe Rn)

/-- **The J-9 A overlay of `genJ9ALXJ`**, generic in the J-9 A source record `I` (so every untouched field is a
variable projection, cheap for the kernel).  Only the cell / J / atom publics, the J layer and the budgets change. -/
def ovlJ (I : InJ9A) (pC pJ pA : ℕ → K3) (r : RowsJ8) (g : ℕ) (C J A : ChipIn)
    (lay : Fin J.n → Nock.Jet.ChipJ8.PRow) (regs ids : List ℕ) (rAX rSP : ℕ) : InJ9A :=
  { I with M := { I.M with pubsC := pC, pubsJ := pJ, pubsA := pA }, r := r, g := g, C := C, J := J, A := A,
           lay := lay, regs := regs, ids := ids, rAX := rAX, rSP := rSP }

/-- **The explicit record of `genJ9ALXJ`** over the run `Rn`: `ovlJ` over `recJ9AXJRn`, plus the ALU fields. -/
def recJ9ALXJRn (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE) (Rn : RunX) :
    InJ9AL :=
  { toInJ9A := ovlJ (recJ9AXJRn Rt s f χe Rn) (cRPLK Rt prims s f χe Rn).2 (jgLK Rt prims s f χe Rn).2
      (aRPLK Rt prims s f χe Rn).2 (budget (mLK Rt prims s f χe Rn)) (regsJLK Rt prims s f χe Rn).length
      (chipOf (cRPLK Rt prims s f χe Rn).1)
      ⟨hOf (layLK Rt prims s f χe Rn).length, (layLK Rt prims s f χe Rn).length,
        ωOf (hOf (layLK Rt prims s f χe Rn).length), colsOf (jgLK Rt prims s f χe Rn).1 (layLK Rt prims s f χe Rn).length⟩
      (chipOf (aRPLK Rt prims s f χe Rn).1) (layLK Rt prims s f χe Rn).get (regsJLK Rt prims s f χe Rn)
      (idsJLK Rt prims s f χe Rn) (BLK Rt prims s f χe Rn) (BLK Rt prims s f χe Rn)
    AL := chipOf (lRPLK Rt prims s f χe Rn).1
    pubsL := (lRPLK Rt prims s f χe Rn).2
    aluOn := aluOnLK Rt prims s f χe Rn
    prims := if aluOnLK Rt prims s f χe Rn then psCLK Rt prims s f χe Rn else []
    idxP := idxPOf (csK Rt s f χe Rn) prims
    rkP := rkPOf prims
    rAL := BLK Rt prims s f χe Rn }
end defs

/-- **`recJ9ALXJ Rt prims s f χe t r`**: the record over the run `⟨t, r, bfsForest [t], rowsOfT t⟩`. -/
def recJ9ALXJ (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE)
    (t : NTree SkelX) (r : Noun) : InJ9AL :=
  recJ9ALXJRn Rt prims s f χe (RnOf t r)

/-- `genJ9ALXJ` is `recJ9ALXJRn` on the run. -/
theorem genJ9ALXJ_eq (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp))
    (fuel : ℕ) (s f : Noun) (χe : CoinsE) :
    genJ9ALXJ R Rt prims fuel s f χe = (runX R fuel s f).map (recJ9ALXJRn Rt prims s f χe) := by
  unfold genJ9ALXJ
  cases runX R fuel s f with
  | none => rfl
  | some Rn => rfl

/-- **`genJ9ALXJ` succeeds only on a `genX` run, and its record is `recJ9ALXJ`.** -/
theorem genJ9ALXJ_some {R : Nock.Jet.Registry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    {fuel : ℕ} {s f : Noun} {χe : CoinsE} {I : InJ9AL} (h : genJ9ALXJ R Rt prims fuel s f χe = some I) :
    ∃ (t : NTree SkelX) (r : Noun), genX R fuel s f = some (t, r) ∧ I = recJ9ALXJ Rt prims s f χe t r := by
  rw [genJ9ALXJ_eq] at h
  have hr : runX R fuel s f = (genX R fuel s f).map fun tr =>
      (⟨tr.1, tr.2, bfsForest [tr.1], ComplJ8Data.rowsOfT tr.1⟩ : RunX) := by
    unfold runX; cases genX R fuel s f <;> rfl
  rw [hr] at h
  cases hg : genX R fuel s f with
  | none => rw [hg] at h; simp at h
  | some tr =>
    obtain ⟨t, r⟩ := tr
    rw [hg] at h
    simp only [Option.map_some] at h
    exact ⟨t, r, rfl, (Option.some.inj h).symm⟩

/-! ## 2. The J9A-side fields are `recJ9AXJ`'s, by `rfl` (generic in the source record) -/

section Ovl
variable (I : InJ9A) (pC pJ pA : ℕ → K3) (r : RowsJ8) (g : ℕ) (C J A : ChipIn)
  (lay : Fin J.n → Nock.Jet.ChipJ8.PRow) (regs ids : List ℕ) (rAX rSP : ℕ)

theorem ovlJ_X : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).X = I.X := rfl
theorem ovlJ_W : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).W = I.W := rfl
theorem ovlJ_V : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).V = I.V := rfl
theorem ovlJ_AX : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).AX = I.AX := rfl
theorem ovlJ_SP : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).SP = I.SP := rfl
theorem ovlJ_kroots : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).kroots = I.kroots := rfl
theorem ovlJ_krootsV : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).krootsV = I.krootsV := rfl
theorem ovlJ_c : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).c = I.c := rfl
theorem ovlJ_χ : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).χ = I.χ := rfl
theorem ovlJ_axOn : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).axOn = I.axOn := rfl
theorem ovlJ_spOn : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).spOn = I.spOn := rfl
theorem ovlJ_pubsX : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).pubsX = I.pubsX := rfl
theorem ovlJ_pubsS : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).pubsS = I.pubsS := rfl
theorem ovlJ_rho : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.ρ = I.M.ρ := rfl
theorem ovlJ_rhoS : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.ρS = I.M.ρS := rfl
theorem ovlJ_m : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.m = I.M.m := rfl
theorem ovlJ_pubsW : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.pubsW = I.M.pubsW := rfl
theorem ovlJ_pubsV : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.pubsV = I.M.pubsV := rfl
theorem ovlJ_Rt : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).Rt = I.Rt := rfl
theorem ovlJ_idx : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).idx = I.idx := rfl
theorem ovlJ_rk : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).rk = I.rk := rfl
end Ovl

section Proj
variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE)
  (t : NTree SkelX) (r : Noun)

theorem toInJ9A_X : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.X = (recJ9AXJ Rt s f χe t r).X := ovlJ_X _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_W : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.W = (recJ9AXJ Rt s f χe t r).W := ovlJ_W _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_V : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.V = (recJ9AXJ Rt s f χe t r).V := ovlJ_V _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_AX : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.AX = (recJ9AXJ Rt s f χe t r).AX := ovlJ_AX _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_SP : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.SP = (recJ9AXJ Rt s f χe t r).SP := ovlJ_SP _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_kroots : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.kroots = (recJ9AXJ Rt s f χe t r).kroots := ovlJ_kroots _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_krootsV : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.krootsV = (recJ9AXJ Rt s f χe t r).krootsV := ovlJ_krootsV _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_c : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.c = (recJ9AXJ Rt s f χe t r).c := ovlJ_c _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_χ : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.χ = (recJ9AXJ Rt s f χe t r).χ := ovlJ_χ _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_axOn : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.axOn = (recJ9AXJ Rt s f χe t r).axOn := ovlJ_axOn _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_spOn : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.spOn = (recJ9AXJ Rt s f χe t r).spOn := ovlJ_spOn _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_pubsX : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.pubsX = (recJ9AXJ Rt s f χe t r).pubsX := ovlJ_pubsX _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_pubsS : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.pubsS = (recJ9AXJ Rt s f χe t r).pubsS := ovlJ_pubsS _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_rho : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.M.ρ = (recJ9AXJ Rt s f χe t r).M.ρ := ovlJ_rho _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_rhoS : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.M.ρS = (recJ9AXJ Rt s f χe t r).M.ρS := ovlJ_rhoS _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_m : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.M.m = (recJ9AXJ Rt s f χe t r).M.m := ovlJ_m _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_pubsW : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.M.pubsW = (recJ9AXJ Rt s f χe t r).M.pubsW := ovlJ_pubsW _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_pubsV : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.M.pubsV = (recJ9AXJ Rt s f χe t r).M.pubsV := ovlJ_pubsV _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_Rt : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.Rt = (recJ9AXJ Rt s f χe t r).Rt := ovlJ_Rt _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_idx : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.idx = (recJ9AXJ Rt s f χe t r).idx := ovlJ_idx _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem toInJ9A_rk : (recJ9ALXJ Rt prims s f χe t r).toInJ9A.rk = (recJ9AXJ Rt s f χe t r).rk := ovlJ_rk _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Proj

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
