/-
  Nock/V1J8/Example.lean

  **The J-8 example's checker input, built from the module fills.**

  The example `*[[0 0] [0 1]] = [0 0]` (claim `c0`, message `mC0`) at any coin vector `χe`: compute by `FillX.colXE`
  (`= HonestCompX.colX`, B4750), cell by `FillMem.Cell` (`= trM0`, B4751), walk by `FillMem.Walk` (`= trW0`,
  B4752), atom by `FillMem.Atom` (`= trA0`, B4753), J absent (`n = 0`), atom walk absent (`krootsV = 0`, one zero
  row); honest multiplicities `μ0` (validity `(2, 1)`, fingerprint export `(1, 0)`, handle export `(1, 1)`, no path
  provide); orbit generator `ω6` (order 6, `h = 1`) on every chip; nodes `ω6^i`; empty registry.
  `inp χt χv`: traces and message filled at `χt`, checked at `χv`; `honest χ = inp χ χ`; `tampers χ`: ten one-change
  inputs.  Driven by the `nockvm-j8check` exe (`Nock/V1J8/Cli.lean`, `TraceDemo/J8CheckMain.lean`).
-/
import Nock.V1J8.FillX
import Nock.V1J8.FillWalk
import Nock.V1J8.FillAtom
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

set_option autoImplicit false

namespace Nock.V1J8.Example
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.MemX Nock.V1J8.FillMem
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base (c0 s0 f0 t0)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom (H0)
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0TowerFP

abbrev P : ℕ := Nock.Field.p

/-- The example's coin `χ0`: `0` at `χ₃ χ₆ χ₁₅ χ₁₈`, `1` elsewhere. -/
def χ0e : CoinsE := fun i => if (i : ℕ) = 3 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 15 ∨ (i : ℕ) = 18 then 0 else 1

/-! ## Compute (the module fill `FillX.colXE`, proved `= HonestCompX.colX` by `FillX.colXE_eq`) -/

def base0 (j : ℕ) : ZMod P :=
  FillX.colXE (H0 P) (HonestPairX.pdX InhabJ8Comp.sx0) (HonestWalkX.rowAtWX [t0] 1) 1 1 j

def chalE (χe : CoinsE) (j : ℕ) : ZMod P := (chalVJ8E χe j).toZ

def env0E (pub : ℕ → ZMod P) (χe : CoinsE) : Nock.Reified.Env (ZMod P) := ⟨base0, base0, chalE χe, pub⟩

def qE (e : Nock.Reified.Env (ZMod P)) (q : Q (ZMod P)) : K6 :=
  ⟨CompX.evalMZ (CompX.kenv e) e q.1, CompX.evalMZ (CompX.kenv e) e q.2⟩

def invE (e : Nock.Reified.Env (ZMod P)) (k : ℕ) : K6 :=
  let S := Nock.NockVMROM.Thm54.VclL.HonestTraceX.slotAt (F := ZMod P) k
  qE e (HonestSlotX.slotAQ (ZMod P) deltaF S) * (qE e (HonestSlotX.slotDQ (ZMod P) deltaF S))⁻¹

def colE (pub : ℕ → ZMod P) (χe : CoinsE) (c : ℕ) : ZMod P :=
  if c < 69 then base0 c
  else if c < 93 then
    let v := invE (env0E pub χe) ((c - 69) / 6)
    if (c - 69) % 6 < 3 then limbZ v.re ((c - 69) % 6) else limbZ v.im ((c - 69) % 6 - 3)
  else if c < 111 then 0
  else if c < 123 then
    let αW := χe ⟨13, by decide⟩
    let w : K3 := if (c - 111) / 3 = 0 then αW else if (c - 111) / 3 = 1 then αW else 0
    limbZ w ((c - 111) % 3)
  else 0

/-- The compute's `ρ₃` (closed form `ρC0_3`): the row consumes `f0`'s handle record `(H f0, 0, 0, 0, 1)`. -/
def vec5 (l : List Gold) : Fin 5 → K6 := fun c => g6 (l.getD c 0)
def recF0E : Fin 5 → K6 := vec5 [natG (H0 P f0).2, 0, 0, 0, 1]
def ρ3E (χe : CoinsE) : K6 := (compressE (γHE χe) (ρHE χe) recF0E)⁻¹
def ρE (χe : CoinsE) : Fin 5 → K6 := fun i => if (i : ℕ) = 3 then ρ3E χe else 0

def mC : FrameVS.ClaimMsgVS := InhabJ8Comp.mC0 (H0 P)

def colsX (χe : CoinsE) : ℕ → Fin 1 → ZMod P :=
  fun c _ => colE (pubVJ8E c0 mC (ρE χe) 0 χe) χe c


/-! ## Memory multiplicities `μ0` -/

def mv (j : ℕ) : ℕ := if j = 0 then 2 else 1
def mx (j : ℕ) : ℕ := if j = 0 then 1 else 0
def mx1 (_ : ℕ) : ℕ := 0
def mh (_ : ℕ) : ℕ := 1

/-! ## The input -/

def ω6g : Gold := Gold.ofU64 18446744065119617026

def RtG : ℕ → Nock.Jet.Autogen.Tpl := fun _ => ⟨0, Fin.elim0, Fin.elim0, .F, .const 0⟩

/-- The honest message at coin `χe` (publics from the chips' honest terminals). -/
def msg (χe : CoinsE) : MsgE where
  m := mC
  ρ := ρE χe
  ρS := 0
  pubsC := Cell.pubs (coOf χe) mv mx mx1 mh
  pubsW := Walk.pubs (coOf χe) 0 0
  pubsJ := fun _ => 0
  pubsA := fun _ => 0
  pubsV := fun _ => 0

/-- **The example's input**, traces and message filled at `χt`, checked at the coin `χv`. -/
def inp (χt χv : CoinsE) : InJ8 where
  c := c0
  M := msg χt
  χ := χv
  r := InhabJ8Main.rJ0
  g := 0
  X := ⟨1, 1, ω6g, colsX χt⟩
  C := ⟨1, 2, ω6g, Cell.cols (coOf χt) mv mx mx1 mh⟩
  W := ⟨1, 1, ω6g, Walk.cols (coOf χt) (chalsMJ8E χt 0) 0 0⟩
  J := ⟨1, 0, ω6g, fun _ => Fin.elim0⟩
  A := ⟨1, 1, ω6g, Atom.cols (coOfA χt) (zE χt)⟩
  V := ⟨1, 1, ω6g, fun _ _ => 0⟩
  kroots := 1
  krootsV := 0
  lay := Fin.elim0
  Rt := RtG
  regs := []
  ids := []
  idx := fun _ => 0
  rk := fun _ => (0, 0)

def honest (χe : CoinsE) : InJ8 := inp χe χe

/-- The component vector: valid, static, public equations, and the seven chips. -/
def parts (I : InJ8) : List (String × Bool) :=
  [("valid (row counts, heights, orbit orders)", validB I),
   ("static (domains, layout, claim, census, budgets)",
     if hv : validB I = true then checkStaticJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g else false),
   ("public equations (8, over K')",
     if hv : validB I = true then checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M else false),
   ("compute chip X", CompX.checkCompX (tabX I)), ("cell chip KW", checkCellKW (tabC I)),
   ("walk chip J8", checkWalkJ8 I.kroots (tabW I)), ("J chip (dispatch)", checkJOK (tabJ I)),
   ("atom chip HQ", checkAtomHQ (tabA I)), ("atom walk (dispatch)", checkAWOK I.krootsV (tabV I)),
   ("atom chip HQL", checkAtomHQL (tabA I))]

/-! ## Tampers (each changes one thing of the honest input) -/

def bump (χe : CoinsE) : CoinsE := fun i => if (i : ℕ) = 4 then χe i + g3 (natG 9) else χe i

def tampers (χe : CoinsE) : List (String × InJ8) :=
  let H := honest χe
  [("coin chi4 changed at the check (traces fixed)", inp χe (bump χe)),
   ("cell base column (row 1 right child)",
     { H with C := ⟨1, 2, ω6g, fun c i => if c = 8 ∧ (i : ℕ) = 1 then H.C.cols c i + 1 else H.C.cols c i⟩ }),
   ("compute rho3 public", { H with M := { msg χe with ρ := fun i => if (i : ℕ) = 3 then ρ3E χe + 1 else 0 } }),
   ("walk import public",
     { H with M := { msg χe with
        pubsW := (fun j => if j = 0 then Walk.pubs (coOf χe) 0 0 0 + 1 else Walk.pubs (coOf χe) 0 0 j) } }),
   ("atom column (mb inverse limb)",
     { H with A := ⟨1, 1, ω6g, fun c i => if c = 313 then H.A.cols c i + 1 else H.A.cols c i⟩ }),
   ("orbit generator of the wrong order", { H with C := ⟨1, 2, Gold.ofU64 7, H.C.cols⟩ }),
   ("zero row budget", { H with r := { InhabJ8Main.rJ0 with N := 0 } }),
   ("compute walk column (ln)",
     { H with X := ⟨1, 1, ω6g, fun c i => if c = 111 then H.X.cols c i + 1 else H.X.cols c i⟩ }),
   ("atom-walk dispatch krootsV = 1", { H with krootsV := 1 }),
   ("wrong claimed result", { H with c := ⟨s0, f0, f0⟩ })]

end Nock.V1J8.Example
