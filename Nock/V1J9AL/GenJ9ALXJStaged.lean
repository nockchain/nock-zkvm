/-
  No theorem here (the theorems are `H/GenPortJ9ALHStaged.lean`).

  * `gen0 R Rt prims fuel s f : Option (Block0Cols × St0)` runs the program and returns the round-0 columns of the
    nine chips (no coin);
  * `gen1 st coins0 : Block1Cols × St1` returns the round-1 columns at the round-0 coins `coins0 : Fin 13 → K3`,
    the coins of `frameJ8` with `sampledAfter = 0`, in the order `DriverJ8.TranscriptJ8.idxS0 = [2,3,8..18]`;
  * `gen2 st coins1 : Block2Cols × InJ9AL` returns the round-2 columns at `coins1 : Fin 6 → K3`
    (`idxS1 = [0,1,4,5,6,7]`) and the rest of the record (every chip's columns blanked);
  * `assembleI b0 b1 b2 rest` is the record; `runStaged` composes the three stages.
  Each stage evaluates the let-chain of `genJ9ALXJ` (`GenPortJ9ALHJRun.recJ9ALXJRn`) at `assemble 0 0`,
  `assemble coins0 0`, `assemble coins0 coins1` and keeps that round's columns (`blkOf`, thresholds `crC9 crM crW
  crJ crA crW crAX crSP crAL`).  A block keeps each chip's `h n ω`; the other rounds' columns read `0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
import Nock.DriverJ8.TranscriptJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9AL.GenJ9ALXJStaged

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun (recJ9ALXJRn)
open Nock.DriverJ8.TranscriptJ8 (idxS0 idxS1)
open Nock.V1J9AL.CheckJ9AL
open Nock.V1J8.FillMem
open Nock.V1J9A Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54 Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c2 c3)
open Nock.Jet.Prim (PrimOp)

/-! ## 1. Coins -/

abbrev Coins0 := Fin 13 → K3
abbrev Coins1 := Fin 6 → K3

def s0 (k : Fin 13) : Fin frameJ8.n :=
  ⟨idxS0.getD k 0 % 19, Nat.mod_lt _ (show 19 > 0 by decide)⟩
def s1 (k : Fin 6) : Fin frameJ8.n :=
  ⟨idxS1.getD k 0 % 19, Nat.mod_lt _ (show 19 > 0 by decide)⟩

def c0 (χe : CoinsE) : Coins0 := fun k => χe (s0 k)
def c1 (χe : CoinsE) : Coins1 := fun k => χe (s1 k)

def assemble (a : Coins0) (b : Coins1) : CoinsE := fun i =>
  if h : idxS0.idxOf i.val < 13 then a ⟨_, h⟩
  else b ⟨idxS1.idxOf i.val % 6, Nat.mod_lt _ (show 6 > 0 by decide)⟩

def coins0OfArray (a : Array K3) : Coins0 := fun k => a.getD k 0
def coins1OfArray (a : Array K3) : Coins1 := fun k => a.getD k 0

/-! ## 2. Blocks -/

/-- Round of column `c` for thresholds `a ≤ b`: `0` below `a`, `1` below `b`, else `2`. -/
def cr3 (a b c : ℕ) : ℕ := if c < a then 0 else if c < b then 1 else 2

/-- Entry `(c, i)` of a chip (`0` off its rows). -/
def getN (q : ChipIn) (c i : ℕ) : ZMod p := if h : i < q.n then q.cols c ⟨i, h⟩ else 0

/-- The chip `q` with only its round-`r` columns kept. -/
def maskC (a b r : ℕ) (q : ChipIn) : ChipIn :=
  ⟨q.h, q.n, q.ω, fun c i => if cr3 a b c = r then q.cols c i else 0⟩

def blankC (q : ChipIn) : ChipIn := ⟨q.h, q.n, q.ω, fun _ _ => 0⟩

/-- The columns merged from the three round blocks. -/
def mergeCols (a b : ℕ) (q0 q1 q2 : ChipIn) (n : ℕ) : ℕ → Fin n → ZMod p := fun c i =>
  if cr3 a b c = 0 then getN q0 c i else if cr3 a b c = 1 then getN q1 c i else getN q2 c i

def mergeC (a b : ℕ) (q0 q1 q2 base : ChipIn) : ChipIn :=
  ⟨base.h, base.n, base.ω, mergeCols a b q0 q1 q2 base.n⟩

/-- **One round's committed columns** of the nine chips (each keeps `h n ω`; the other rounds' columns are `0`). -/
structure BlkL where
  X : ChipIn
  C : ChipIn
  W : ChipIn
  J : ChipIn
  A : ChipIn
  V : ChipIn
  AX : ChipIn
  SP : ChipIn
  AL : ChipIn

abbrev Block0Cols := BlkL
abbrev Block1Cols := BlkL
abbrev Block2Cols := BlkL

/-- Round `r`'s block of a record (thresholds: `crC9 crM crW crJ crA crW crAX crSP crAL`). -/
def blkOf (r : ℕ) (I : InJ9AL) : BlkL :=
  ⟨maskC 83 137 r I.X, maskC 134 188 r I.C, maskC 25 97 r I.W, maskC 29 71 r I.J, maskC 205 259 r I.A,
   maskC 25 97 r I.V, maskC 22 22 r I.AX, maskC 72 72 r I.SP, maskC 94 148 r I.AL⟩

/-- A record with every chip's columns blanked (the `rest` of `gen2`). -/
def blankL (I : InJ9AL) : InJ9AL :=
  { I with X := blankC I.X, C := blankC I.C, W := blankC I.W, J := blankC I.J, A := blankC I.A,
           V := blankC I.V, lay := I.lay, AX := blankC I.AX, SP := blankC I.SP, AL := blankC I.AL }

/-- The record from `rest` and the three blocks. -/
def assembleI (b0 b1 b2 : BlkL) (rest : InJ9AL) : InJ9AL :=
  { rest with X := mergeC 83 137 b0.X b1.X b2.X rest.X, C := mergeC 134 188 b0.C b1.C b2.C rest.C,
              W := mergeC 25 97 b0.W b1.W b2.W rest.W, J := mergeC 29 71 b0.J b1.J b2.J rest.J,
              A := mergeC 205 259 b0.A b1.A b2.A rest.A, V := mergeC 25 97 b0.V b1.V b2.V rest.V,
              lay := rest.lay,
              AX := mergeC 22 22 b0.AX b1.AX b2.AX rest.AX, SP := mergeC 72 72 b0.SP b1.SP b2.SP rest.SP,
              AL := mergeC 94 148 b0.AL b1.AL b2.AL rest.AL }

/-! ## 3. The stages -/

structure St0 where
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  prims : List (ℕ × PrimOp)
  s : Noun
  f : Noun
  Rn : RunX

structure St1 extends St0 where
  coins0 : Coins0

/-- The record of the run at a coin vector (`genJ9ALXJ`'s let-chain, `recJ9ALXJRn`). -/
def recAt (st : St0) (χ : CoinsE) : InJ9AL := recJ9ALXJRn st.Rt st.prims st.s st.f χ st.Rn

/-- **Stage 0**: run the program; the round-0 columns (no coin). -/
def gen0 (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (fuel : ℕ)
    (s f : Noun) : Option (Block0Cols × St0) :=
  (runX R fuel s f).map fun Rn =>
    let st : St0 := ⟨Rt, prims, s, f, Rn⟩
    (blkOf 0 (recAt st (assemble 0 0)), st)

/-- **Stage 1**: the round-1 columns at the round-0 coins. -/
def gen1 (st : St0) (coins0 : Coins0) : Block1Cols × St1 :=
  (blkOf 1 (recAt st (assemble coins0 0)), ⟨st, coins0⟩)

/-- **Stage 2**: the round-2 columns and the rest of the record at all coins. -/
def gen2 (st : St1) (coins1 : Coins1) : Block2Cols × InJ9AL :=
  let I := recAt st.toSt0 (assemble st.coins0 coins1)
  (blkOf 2 I, blankL I)

/-- **The staged generator, composed.** -/
def runStaged (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (fuel : ℕ)
    (s f : Noun) (a : Coins0) (b : Coins1) : Option InJ9AL :=
  (gen0 R Rt prims fuel s f).map fun x =>
    let y := gen1 x.2 a
    let z := gen2 y.2 b
    assembleI x.1 y.1 z.1 z.2

/-! ## 4. The same for J-9 A (`genJ9AXJ`, no ALU) -/

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun (recJ9AXJRn)
open Nock.V1J9A.CheckJ9A (InJ9A)

/-- **One round's committed columns** of the eight J-9 A chips. -/
structure BlkA where
  X : ChipIn
  C : ChipIn
  W : ChipIn
  J : ChipIn
  A : ChipIn
  V : ChipIn
  AX : ChipIn
  SP : ChipIn

def blkOfA (r : ℕ) (I : InJ9A) : BlkA :=
  ⟨maskC 83 137 r I.X, maskC 134 188 r I.C, maskC 25 97 r I.W, maskC 29 71 r I.J, maskC 205 259 r I.A,
   maskC 25 97 r I.V, maskC 22 22 r I.AX, maskC 72 72 r I.SP⟩

def blankA (I : InJ9A) : InJ9A :=
  { I with X := blankC I.X, C := blankC I.C, W := blankC I.W, J := blankC I.J, A := blankC I.A,
           V := blankC I.V, lay := I.lay, AX := blankC I.AX, SP := blankC I.SP }

def assembleIA (b0 b1 b2 : BlkA) (rest : InJ9A) : InJ9A :=
  { rest with X := mergeC 83 137 b0.X b1.X b2.X rest.X, C := mergeC 134 188 b0.C b1.C b2.C rest.C,
              W := mergeC 25 97 b0.W b1.W b2.W rest.W, J := mergeC 29 71 b0.J b1.J b2.J rest.J,
              A := mergeC 205 259 b0.A b1.A b2.A rest.A, V := mergeC 25 97 b0.V b1.V b2.V rest.V,
              lay := rest.lay,
              AX := mergeC 22 22 b0.AX b1.AX b2.AX rest.AX, SP := mergeC 72 72 b0.SP b1.SP b2.SP rest.SP }

structure St0A where
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  s : Noun
  f : Noun
  Rn : RunX

structure St1A extends St0A where
  coins0 : Coins0

def recAtA (st : St0A) (χ : CoinsE) : InJ9A := recJ9AXJRn st.Rt st.s st.f χ st.Rn

def gen0A (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (fuel : ℕ) (s f : Noun) : Option (BlkA × St0A) :=
  (runX R fuel s f).map fun Rn =>
    let st : St0A := ⟨Rt, s, f, Rn⟩
    (blkOfA 0 (recAtA st (assemble 0 0)), st)

def gen1A (st : St0A) (coins0 : Coins0) : BlkA × St1A :=
  (blkOfA 1 (recAtA st (assemble coins0 0)), ⟨st, coins0⟩)

def gen2A (st : St1A) (coins1 : Coins1) : BlkA × InJ9A :=
  let I := recAtA st.toSt0A (assemble st.coins0 coins1)
  (blkOfA 2 I, blankA I)

def runStagedA (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (fuel : ℕ) (s f : Noun) (a : Coins0)
    (b : Coins1) : Option InJ9A :=
  (gen0A R Rt fuel s f).map fun x =>
    let y := gen1A x.2 a
    let z := gen2A y.2 b
    assembleIA x.1 y.1 z.1 z.2

end J9A

end Nock.V1J9AL.GenJ9ALXJStaged
