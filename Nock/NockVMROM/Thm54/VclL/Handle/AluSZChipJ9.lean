/-
  Nock/NockVMROM/Thm54/VclL/Handle/AluSZChipJ9.lean

  **The big-atom ALU `aluSZChipJ9`** — six primitive jets
  (add sub lt mul div mod) by a Schwartz–Zippel identity at the limb coin `y`.
  Everything here is a chip DEFINITION plus structural receipts (width, degree, instrument, disjointness).  The
  soundness of the gates (that an accepted block computes `primSem`) is not proved in this module; it is part of the
  J-9 AL soundness proof (`J9AL/SoundJ9AL.lean`, `J9AL/ProbJ9AL.lean::probJ9AL_final_clean`).

  ## Row kinds and blocks
  `preg` (`sP`, preprocessed with `pId`, `pOp`), `hdr` (`sH`, one per call), `lane` (`sL`, 32 bits);
  rows with `sP = sH = sL = 0` are padding.  One call = `hdr` + its slots; a slot = contiguous lane rows,
  `fst` on its first row, `eos` on its last.  Slot ROLES (one-hot): `ra rb rc` (operand a, operand b, result),
  `rd` (lt witness d), `rx` (div/mod: q), `ry` (div/mod: r), `rs` (div/mod: s); the two Q blocks have no role and
  are told by their MODE.  Slot MODES (one-hot): `mR` read-only (1 row, kind 2), `mS` split (2 rows, kind 0),
  `mV` view (≤ 62 rows, kind 2: read + 32-bit limbs with 16-bit halves), `mW` W-B witness (≤ 62 rows, no
  handle), `mQ1` packed 1-bit Q (32 carries per row, `y^t` coefficients), `mQM` 25-bit Q (one coefficient per row).
  Role sequences (forced by the successor gates `gSeq`):
    add/sub: `ra rb rc mQ1`   lt: `ra rb rd mQ1`   mul: `ra rb rc mQM`   div/mod: `ra rx rb ry rs mQM mQ1`.
  Per-op identities, as the block sums `S1`, `S2` of the per-slot contributions `D1 = cf1·L`,
  `D2 = cf2·L` (`L` = the slot's value at `y`; on a Q block `L = (y − B)·H`), the product slot `f2` contributing
  `RL·L + (y − B)·RO·HO` (`RL`, `RO` = the first factor's `L`, `HO`, latched at `f1`):
    add `La + Lb − Lc − (B − y)Hq`;   sub `Lb + Lc − La − (B − y)Hq`;
    lt  `(2·yes − 1)(La − Lb) + Ld + yes − (B − y)Hq`  (`yes = 1 − lb`, `lb` = the result loobean, `0` = yes);
    mul `La·Lb + (y − B)·Oa·Ob − Lc − (B − y)Hq`;
    div/mod `Lq·Ld + (y − B)·Oq·Od + Lr − La − (B − y)HK` and (`S2`) `Lr + Ls + 1 − Ld − (B − y)HK2`.
  Result slot: add/sub/mul `rc`; div `rx` (q); mod `ry` (r); lt: no slot, `vE = lb` on the hdr.

  ## GATE LIST (one line per gate group, with its purpose).  Base gates are `CoeffExpr`
  (degree ≤ 4), `𝕂′` gates are `QE` pairs (degree ≤ 4).  Counts (`baseGates_length`, `aluQ_length`,
  `aluMixed_length`): 180 base gates (170 arithmetic + 10 copies), 39 `𝕂′` equations = 78 mixed gates.
  ### Base (round 0)
  - gKind   booleanity of `sH sL`, of `sP + sH + sL` (≤ 1 kind), `isLT·(sH + sL) = 0` (last row is pad/preg),
            op one-hot booleans, `sH·(Σ op − 1)`, role / mode booleans, `sL = Σ roles + mQ1 + mQM`,
            `Σ roles = mR + mS + mV + mW`.                                              [selectors]
  - gSlot   `fst`, `eos` boolean and lane-only; after `hdr`/`eos` the next lane row is `fst`; inside a slot the
            next row is lane, not `fst`; a lane row follows only `hdr` or lane; `sH·(1 − ra′)` (the hdr is
            never the last row of its block: `hdr·isLastOfBlock = 0`); role and mode
            constant inside a slot.                                                   [role sequence + eos]
  - gSeq    successor gates at `eos`: the role sequences above; the terminal Q block is followed by a
            non-lane row.  (Every required slot occurs exactly once: no dropped / duplicated operand.)
  - gCompat mode ↔ role: witnesses (`rd rs`, `rx` in mod, `ry` in div) are `mW`; handle slots are not;
            factors (mul `ra rb`, div/mod `rx rb`) are not read-only; `mR` is one row; `mS` is two rows.
  - gFlag   `sf = fst·mS` (split head), `aV = fst·(mR + mV)` (validity read), `f1`, `f2` (first / second factor).
  - gCoef   `cf1`, `cf2` per (role, op) on `fst` rows: the coefficients of the identities above.
  - gHdr    lt result `kE = 0`, `vE = lb` (copy), `lb` boolean; **`sH·(kS − 1)`**; op code
            `opc = Σ k·op_k` on hdr, `opc = pOp`, `id = pId` on preg (the op record's source).
  - gConst  block constancy (lane rows copy the previous row): op one-hot, `lb`, `kA kB kE`, `vA vB vE`.
  - gBind   slot handle `(sk, sv)` = the role's block handle (`ra ↔ A`, `rb ↔ B`, `rc ↔ E`, div `rx ↔ E`,
            mod `ry ↔ E`); kind 2 on `mR`/`mV`, kind 0 on `mS`.                 [handle binding]
  - gBits   32 lane-bit booleanities; `mQM·b_t = 0` for `t ≥ 25` (25-bit `Q`).
  - gSplit  `sf·(V − ℓ − B·ℓ′)`, the **`< p` gate** `sf·ℓ·((ℓ′ − (B − 1))·invP − 1)`, `sv = V` (copy).
  - gCap    **the 6-bit length counter** `cn = Σ 2^i c_i`, `c_i` boolean, `cA = c0c1c2`, `cB = c3c4c5`,
            `cA·cB = 0` (`cn ≤ 62`, the s10S precedent `J9A/ChipHX9.lean:982`), `cn = 1` on the first row and
            `cn′ = cn + 1` inside every Horner value slot (`mS mV mW`): every mul/div view and every W-B witness
            block has ≤ 62 limbs (applied to all `mS/mV/mW` slots: a superset of the binding requirement).
  ### `𝕂′` (rounds 1 / 2)
  - qHorner `H = ℓ + y·H′` (`H = ℓ` at `eos`) and `HO = o + y·HO′` on `mS mV mW mQM` rows (`o` = high half).
  - qPacked Q-add rows: `H = Σ_t b_t·y^t + y^32·H′` (`y^t` read at the leaves `40 + 2t, 41 + 2t` of `chalsALJ8`).
  - qVal    `L = H` at the first row of `mS mV mW` slots (**the link `H32 = L` on views**);
            `L = (y − B)·H` on Q blocks.
  - qLatch  `RL = L`, `RO = HO` at `f1`; `RL`, `RO` constant along the block.
  - qContr  `D1 = RL·L + (y − B)·RO·HO` at `f2`; `D1 = cf1·L`, `D2 = cf2·L` on other first rows; `D = 0` on
            non-first lane rows; hdr `D1 = oLt·(1 − lb)`, `D2 = oDiv + oMod`.
  - qSum    `S = D` on hdr, `S′ = S + D′` on lane rows, `S = 0` where the next row is not lane: the identities.
  - qRead   validity consume `[z, 0, L, 0, sv]` on `aV` rows (**`z = zAt = QE.chal 37 38`**), `den` at
            `γ′ρ′`; accumulator, terminal `pubALv` (`𝕂′` publics `0 / 1`).
  - qServ   hdr consumes `keyRg (2, id, kc, vc)` and the **op record `(id, opc, 0,0,0,0,0, 6)`**,
            provides `keyJet (id, kc, vc, kS, vS, kE, vE, 3)` with multiplicity `m`; preg provides `keyRg` and
            the op record with multiplicity `mP`; handle coins; terminal `pubALs` (`2 / 3`).
  - qExp    hdr consumes `keyX (vS, kA, vA, kB, vB)` (the subject cell `[a b]`); terminal `pubALx` (`4 / 5`).

  ## Layout (MEASURED: base 94, `𝕂`-roles 34 (17 `𝕂′`), width `94 + 34·3 = 196` by `rfl`)
  Base: `0 isFT, 1 isLT, 2 sP, 3 pId, 4 pOp` (preprocessed) · `5 sH, 6 sL` · `7..12` ops · `13..19` roles ·
  `20..25` modes · `26 fst, 27 eos, 28 f1, 29 f2, 30 sf, 31 aV, 32 cf1, 33 cf2` · `34..65` lane bits ·
  `66 V, 67 invP, 68 sk, 69 sv` · `70 kA, 71 vA, 72 kB, 73 vB, 74 kE, 75 vE, 76 lb` ·
  `77 id, 78 kc, 79 vc, 80 opc, 81 kS, 82 vS, 83 m, 84 mP` · `85 cn, 86..91 c0..c5, 92 cA, 93 cB`.
  `𝕂′` round 1: `H 0, HO 2, L 4, D1 6, D2 8, S1 10, S2 12, RL 14, RO 16`;
  round 2: `invV 18, invR 20, invO 22, invJ 24, invX 26, accV 28, accS 30, accX 32`.
  (No hdr/lane column overlay, and two identity sums for div/mod.)

  ## Challenge vector
  `chalsALJ8` = `ChalsAZJ8.chalsAJ8Z` (y at leaves `2 / 3`, `z` at `37 / 38`, validity coins `5, 7, 11..32`,
  handle coins `33..36`) plus the verifier-computed powers `y^t`, `t ≤ 32`, at leaves `40 + 2t / 41 + 2t`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op SelG coinOnlyA)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Columns -/

def isFT : ℕ := 0
def isLT : ℕ := 1
def sP : ℕ := 2
def pId : ℕ := 3
def pOp : ℕ := 4
def sH : ℕ := 5
def sL : ℕ := 6
def oAdd : ℕ := 7
def oSub : ℕ := 8
def oLt : ℕ := 9
def oMul : ℕ := 10
def oDiv : ℕ := 11
def oMod : ℕ := 12
def ra : ℕ := 13
def rb : ℕ := 14
def rc : ℕ := 15
def rd : ℕ := 16
def rx : ℕ := 17
def ry : ℕ := 18
def rs : ℕ := 19
def mR : ℕ := 20
def mS : ℕ := 21
def mV : ℕ := 22
def mW : ℕ := 23
def mQ1 : ℕ := 24
def mQM : ℕ := 25
def fst : ℕ := 26
def eos : ℕ := 27
def f1 : ℕ := 28
def f2 : ℕ := 29
def sf : ℕ := 30
def aV : ℕ := 31
def cf1 : ℕ := 32
def cf2 : ℕ := 33
/-- Lane bits `34 .. 65`. -/
def bt0 : ℕ := 34
def Vc : ℕ := 66
def invP : ℕ := 67
def sk : ℕ := 68
def sv : ℕ := 69
def kA : ℕ := 70
def vA : ℕ := 71
def kB : ℕ := 72
def vB : ℕ := 73
def kE : ℕ := 74
def vE : ℕ := 75
def lb : ℕ := 76
def idc : ℕ := 77
def kc : ℕ := 78
def vc : ℕ := 79
def opc : ℕ := 80
def kS : ℕ := 81
def vS : ℕ := 82
def mJ : ℕ := 83
def mP : ℕ := 84
def cn : ℕ := 85
/-- Counter bits `86 .. 91`. -/
def cb0 : ℕ := 86
def cA : ℕ := 92
def cB : ℕ := 93

/-- Base width (round 0). -/
def baseW : ℕ := 94

/-- `𝕂′` roles (Re at `r`, Im at `r + 1`); round 1 `0 .. 17`, round 2 `18 .. 33`. -/
def H : ℕ := 0
def HO : ℕ := 2
def L : ℕ := 4
def D1 : ℕ := 6
def D2 : ℕ := 8
def S1 : ℕ := 10
def S2 : ℕ := 12
def RL : ℕ := 14
def RO : ℕ := 16
def invV : ℕ := 18
def invR : ℕ := 20
def invO : ℕ := 22
def invJ : ℕ := 24
def invX : ℕ := 26
def accV : ℕ := 28
def accS : ℕ := 30
def accX : ℕ := 32

/-- Terminal publics (`𝕂′` pairs): validity `0 / 1`, service `2 / 3`, export `4 / 5`. -/
def pubALv : ℕ := 0
def pubALs : ℕ := 2
def pubALx : ℕ := 4

/-- The op-record tag (tag `6` is unused in the J-9 A service balance). -/
def tagOp : ℕ := 6

/-- **The ALU keyRg tag**: a fresh tag, last (position 7), distinct from the J-9 A service tags
`2, 3, 4, 5` and the op-record tag `6`. -/
def tagRgP : ℕ := 7

def opCols : List ℕ := [oAdd, oSub, oLt, oMul, oDiv, oMod]
def roleCols : List ℕ := [ra, rb, rc, rd, rx, ry, rs]
def modeCols : List ℕ := [mR, mS, mV, mW, mQ1, mQM]

/-- The serial-capable columns (handle values). -/
def serialColsAL : List ℕ := [sv, vA, vB, vE, vc, vS]

theorem layout_tiles :
    [isFT, isLT, sP, pId, pOp, sH, sL] ++ opCols ++ roleCols ++ modeCols ++
      [fst, eos, f1, f2, sf, aV, cf1, cf2] ++ (List.range 32).map (bt0 + ·) ++
      [Vc, invP, sk, sv, kA, vA, kB, vB, kE, vE, lb, idc, kc, vc, opc, kS, vS, mJ, mP, cn] ++
      (List.range 6).map (cb0 + ·) ++ [cA, cB] = List.range baseW ∧
    [H, HO, L, D1, D2, S1, S2, RL, RO, invV, invR, invO, invJ, invX, accV, accS, accX] =
      (List.range 17).map (2 * ·) := by decide

/-! ## 2. Expression helpers -/

section Helpers
variable {F : Type} [Field F]

/-- `B = 2^32`. -/
def Bf : F := (2 : F) ^ 32

/-- Sum of current-row columns. -/
def sumC (l : List ℕ) : CoeffExpr F := CoeffExpr.sumList l fun j => cv j

/-- Sum of next-row columns. -/
def sumN (l : List ℕ) : CoeffExpr F := CoeffExpr.sumList l fun j => nv j

/-- A product of expressions. -/
def prod3 (a b c : CoeffExpr F) : CoeffExpr F := .mul (.mul a b) c

/-- The lane limb `ℓ = Σ_{t<32} 2^t b_t` (current row). -/
def lE : CoeffExpr F := bitSum bt0 32

/-- The lane limb of the next row. -/
def lN : CoeffExpr F := CoeffExpr.sumList (List.range 32) fun i => .mul (.const ((2 : F) ^ i)) (nv (bt0 + i))

/-- The high half `o = Σ_{t<16} 2^t b_{16+t}`. -/
def oE : CoeffExpr F := bitSum (bt0 + 16) 16

/-- The counter value `Σ 2^i c_i`. -/
def cnE : CoeffExpr F := bitSum cb0 6

/-- The op code `Σ k·op_k`, `add 1, sub 2, lt 3, mul 4, div 5, mod 6` (the `PrimOp` numbering of `Nock.Jet.PrimJ9`). -/
def opCode : CoeffExpr F :=
  CoeffExpr.sumList [(1, oAdd), (2, oSub), (3, oLt), (4, oMul), (5, oDiv), (6, oMod)]
    fun kj => .mul (.const ((kj.1 : ℕ) : F)) (cv kj.2)

/-- Horner value slots (counter-capped). -/
def hzV : CoeffExpr F := sumC [mS, mV, mW]
/-- Horner-active rows. -/
def hz : CoeffExpr F := sumC [mS, mV, mW, mQM]

end Helpers

/-! ## 3. Base gates -/

section Gates
variable {F : Type} [Field F]

def ar (g : CoeffExpr F) : AG F := .ar g

/-- **gKind**. -/
def gKind : List (AG F) :=
  [ ar (boolE (cv sH)), ar (boolE (cv sL)), ar (boolE (sumC [sP, sH, sL])),
    ar (.mul (cv isLT) (sumC [sH, sL])) ] ++
  opCols.map (fun j => ar (boolE (cv j))) ++
  [ ar (.mul (cv sH) (.sub (sumC opCols) (.const 1))) ] ++
  roleCols.map (fun j => ar (boolE (cv j))) ++
  modeCols.map (fun j => ar (boolE (cv j))) ++
  [ ar (.sub (cv sL) (sumC (roleCols ++ [mQ1, mQM]))),
    ar (.sub (sumC roleCols) (sumC [mR, mS, mV, mW])) ]

/-- `hdr` is never the last row of its block: the next row is the first slot `ra`. -/
def gHdrNotLast : CoeffExpr F := .mul (cv sH) (notE (nv ra))

/-- **gSlot**. -/
def gSlot : List (AG F) :=
  [ ar (boolE (cv fst)), ar (boolE (cv eos)), ar (.mul (cv fst) (notE (cv sL))),
    ar (.mul (cv eos) (notE (cv sL))),
    ar (.mul (.add (cv sH) (cv eos)) (.sub (nv sL) (nv fst))),
    ar (prod3 (cv sL) (notE (cv eos)) (nv fst)),
    ar (prod3 (cv sL) (notE (cv eos)) (notE (nv sL))),
    ar (.mul (.sub (notE (cv sH)) (cv sL)) (.mul (notE (cv isLT)) (nv sL))),
    ar gHdrNotLast ] ++
  (roleCols ++ modeCols).map (fun j => ar (prod3 (cv sL) (notE (cv eos)) (.sub (nv j) (cv j))))

/-- A successor gate `eos·r·σ·(1 − next.s)`. -/
def succ (r : ℕ) (σ : CoeffExpr F) (s : ℕ) : AG F := ar (.mul (prod3 (cv eos) (cv r) σ) (notE (nv s)))

/-- **gSeq**: the role sequences. -/
def gSeq : List (AG F) :=
  [ succ ra (sumC [oAdd, oSub, oLt, oMul]) rb, succ ra (sumC [oDiv, oMod]) rx,
    succ rx (.const 1) rb,
    succ rb (sumC [oAdd, oSub, oMul]) rc, succ rb (cv oLt) rd, succ rb (sumC [oDiv, oMod]) ry,
    succ rc (sumC [oAdd, oSub]) mQ1, succ rc (cv oMul) mQM,
    succ rd (.const 1) mQ1, succ ry (.const 1) rs, succ rs (.const 1) mQM,
    ar (.mul (prod3 (cv eos) (cv mQM) (cv oMul)) (nv sL)),
    succ mQM (sumC [oDiv, oMod]) mQ1,
    ar (prod3 (cv eos) (cv mQ1) (nv sL)) ]

/-- **gCompat**: mode ↔ role. -/
def gCompat : List (AG F) :=
  [ ar (.mul (cv mW) (sumC [ra, rb, rc])),
    ar (.mul (sumC [rd, rs]) (notE (cv mW))),
    ar (prod3 (cv rx) (cv oDiv) (cv mW)), ar (prod3 (cv rx) (cv oMod) (notE (cv mW))),
    ar (prod3 (cv ry) (cv oMod) (cv mW)), ar (prod3 (cv ry) (cv oDiv) (notE (cv mW))),
    ar (.mul (cv mR) (.add (.mul (cv oMul) (sumC [ra, rb])) (.mul (sumC [oDiv, oMod]) (sumC [rx, rb])))),
    ar (.mul (cv mR) (notE (cv eos))),
    ar (prod3 (cv fst) (cv mS) (cv eos)),
    ar (prod3 (cv fst) (cv mS) (notE (nv eos))) ]

/-- **gFlag**. -/
def gFlag : List (AG F) :=
  [ ar (.sub (cv sf) (.mul (cv fst) (cv mS))),
    ar (.sub (cv aV) (.mul (cv fst) (sumC [mR, mV]))),
    ar (.sub (cv f1) (.mul (cv fst) (.add (.mul (cv oMul) (cv ra)) (.mul (sumC [oDiv, oMod]) (cv rx))))),
    ar (.sub (cv f2) (prod3 (cv fst) (cv rb) (sumC [oMul, oDiv, oMod]))) ]

/-- `fst·r·(c − e)`. -/
def coef (r c : ℕ) (e : CoeffExpr F) : AG F := ar (prod3 (cv fst) (cv r) (.sub (cv c) e))

/-- `1 − 2·lb` (= `2·yes − 1`). -/
def sgnLt : CoeffExpr F := .sub (.const 1) (.mul (.const 2) (cv lb))

/-- **gCoef**: the identity coefficients. -/
def gCoef : List (AG F) :=
  [ coef ra cf1 (.sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod)),
    coef ra cf2 (.const 0),
    coef rb cf1 (.sub (.add (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)),
    coef rb cf2 (.neg (sumC [oDiv, oMod])),
    coef rc cf1 (.sub (.sub (cv oSub) (cv oAdd)) (cv oMul)), coef rc cf2 (.const 0),
    coef rd cf1 (.const 1), coef rd cf2 (.const 0),
    coef rx cf1 (.const 0), coef rx cf2 (.const 0),
    coef ry cf1 (.const 1), coef ry cf2 (.const 1),
    coef rs cf1 (.const 0), coef rs cf2 (.const 1),
    coef mQ1 cf1 (sumC [oAdd, oSub, oLt]), coef mQ1 cf2 (sumC [oDiv, oMod]),
    coef mQM cf1 (.const 1), coef mQM cf2 (.const 0) ]

/-- **F7**: `kS = 1` on the hdr. -/
def gKS : CoeffExpr F := .mul (cv sH) (.sub (cv kS) (.const 1))

/-- **gHdr**. -/
def gHdr : List (AG F) :=
  [ ar (prod3 (cv sH) (cv oLt) (cv kE)), .cp ⟨.mul (cv sH) (cv oLt), .cur vE, .cur lb⟩, ar (boolE (cv lb)),
    ar gKS, ar (.mul (cv sH) (.sub (cv opc) opCode)), ar (.mul (cv sP) (.sub (cv opc) (cv pOp))),
    ar (.mul (cv sP) (.sub (cv idc) (cv pId))) ]

/-- **gConst**: lane rows copy the block constants of the previous row. -/
def gConst : List (AG F) :=
  (opCols ++ [lb, kA, kB, kE]).map (fun j => ar (.mul (.mul (notE (cv isLT)) (nv sL)) (.sub (nv j) (cv j)))) ++
  [vA, vB, vE].map (fun j => .cp ⟨(.mul (notE (cv isLT)) (nv sL)), .nxt j, .cur j⟩)

/-- Handle binding of a role (selector `σ`) to the block handle `(k, v)`. -/
def bind (σ : CoeffExpr F) (k v : ℕ) : List (AG F) := [ar (.mul σ (.sub (cv sk) (cv k))), .cp ⟨σ, .cur sv, .cur v⟩]

/-- **gBind**. -/
def gBind : List (AG F) :=
  bind (.mul (cv fst) (cv ra)) kA vA ++ bind (.mul (cv fst) (cv rb)) kB vB ++ bind (.mul (cv fst) (cv rc)) kE vE ++
  bind (prod3 (cv fst) (cv rx) (cv oDiv)) kE vE ++ bind (prod3 (cv fst) (cv ry) (cv oMod)) kE vE ++
  [ ar (.mul (.mul (cv fst) (sumC [mR, mV])) (.sub (cv sk) (.const 2))), ar (.mul (cv sf) (cv sk)) ]

/-- **gBits**. -/
def gBits : List (AG F) :=
  (List.range 32).map (fun t => ar (boolE (cv (bt0 + t)))) ++
  (List.range 7).map (fun t => ar (.mul (cv mQM) (cv (bt0 + 25 + t))))

/-- **The `< p` gate**: `sf·ℓ·((ℓ′ − (B − 1))·invP − 1)`. -/
def gLtP : CoeffExpr F := .mul (.mul (cv sf) lE) (.sub (.mul (.sub lN (.const (Bf - 1))) (cv invP)) (.const 1))

/-- The split value `sf·(V − ℓ − B·ℓ′)`. -/
def gSplitV : CoeffExpr F := .mul (cv sf) (.sub (.sub (cv Vc) lE) (.mul (.const Bf) lN))

/-- **gSplit**. -/
def gSplit : List (AG F) := [ar gSplitV, ar gLtP, .cp ⟨cv sf, .cur sv, .cur Vc⟩]

/-- **gCap**: the 6-bit length counter. -/
def gCap : List (AG F) :=
  [ ar (.sub (cv cn) cnE) ] ++ (List.range 6).map (fun i => ar (boolE (cv (cb0 + i)))) ++
  [ ar (.sub (cv cA) (prod3 (cv cb0) (cv (cb0 + 1)) (cv (cb0 + 2)))),
    ar (.sub (cv cB) (prod3 (cv (cb0 + 3)) (cv (cb0 + 4)) (cv (cb0 + 5)))),
    ar (.mul (cv cA) (cv cB)),
    ar (prod3 (cv fst) hzV (.sub (cv cn) (.const 1))),
    ar (prod3 hzV (notE (cv eos)) (.sub (.sub (nv cn) (cv cn)) (.const 1))) ]

/-- The tagged base-gate list. -/
def baseAG : List (AG F) :=
  gKind ++ gSlot ++ gSeq ++ gCompat ++ gFlag ++ gCoef ++ gHdr ++ gConst ++ gBind ++ gBits ++ gSplit ++ gCap

/-- **The ALU's base gates.** -/
def baseGates : List (CoeffExpr F) := baseAG.map AG.gate

/-! ### Records -/

/-- The record entries of `ChipHX` (a column or a tag constant). -/
abbrev RE := Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.RE

/-- A record entry as a base expression. -/
def reE : RE → CoeffExpr F
  | .col i => cv i
  | .k c => .const (c : F)


/-- **The ALU `keyRg (id, kc, vc, 0,0,0,0, 7)`**, tag LAST at the fresh tag `tagRgP = 7`.  It is NOT the J
chip's tag-first `keyRg` shape (`ChipJ8.lean:151`): the verifier pin goes through `tlF` and is tag-last
(`PinJ8.lean:64,74`), and a width-8 key with its own tag cannot collide with the other service keys
(`keyRgAL_disjoint`). -/
def keyRgRE : List RE := [.col idc, .col kc, .col vc, .k 0, .k 0, .k 0, .k 0, .k tagRgP]
/-- **The op record `(id, opcode, 0,0,0,0,0, 6)`**, tag last (position 7). -/
def opRecRE : List RE := [.col idc, .col opc, .k 0, .k 0, .k 0, .k 0, .k 0, .k tagOp]
/-- `keyJet (id, kc, vc, kS, vS, kE, vE, 3)` (tag last, `ChipJ8.lean:155`). -/
def keyJetRE : List RE := [.col idc, .col kc, .col vc, .col kS, .col vS, .col kE, .col vE, .k 3]
/-- `keyX (vS, kA, vA, kB, vB)` (Cell3, `ChipJ8.lean:158`). -/
def keyXRE : List RE := [.col vS, .col kA, .col vA, .col kB, .col vB]

def keyRgE : List (CoeffExpr F) := keyRgRE.map reE
def opRecE : List (CoeffExpr F) := opRecRE.map reE
def keyJetE : List (CoeffExpr F) := keyJetRE.map reE
def keyXE : List (CoeffExpr F) := keyXRE.map reE

/-- **The validity key `[z, 0, L, 0, sv]`, `z = zAt = QE.chal 37 38`** (the shape of the atom
table's `mbKey`, `AtomChipHQ.lean:156`). -/
def valKey : List (QE F) := [AtomChipHQ.zAt, QE.zero, QE.var L, QE.zero, QE.base (cv sv)]

/-! ### The `𝕂′` gates -/

/-- The limb coin `y = (χ₂, χ₃)` of `chalsALJ8`. -/
def yQ : QE F := QE.chal 2 3
/-- `y^t`, read at the leaves `40 + 2t`, `41 + 2t` of `chalsALJ8` (verifier-computed powers). -/
def ypow (t : ℕ) : QE F := QE.chal (40 + 2 * t) (41 + 2 * t)
/-- `y − B`. -/
def yMB : QE F := QE.sub yQ (QE.base (.const Bf))

def sumQ (l : List (QE F)) : QE F := l.foldr QE.add QE.zero

/-- `Σ_{t<32} b_t·y^t`. -/
def packE : QE F := sumQ ((List.range 32).map fun t => QE.scale (cv (bt0 + t)) (ypow t))

/-- `σ·(a − b)` for `𝕂′`. -/
def qz (σ : CoeffExpr F) (a b : QE F) : QE F := QE.scale σ (QE.sub a b)

/-- **qHorner, qPacked, qVal, qLatch, qContr, qSum** (the identity machinery, round 1). -/
def identQ (δF : F) : List (QE F) :=
  [ qz (.mul hz (notE (cv eos))) (QE.var H) (QE.add (QE.base lE) (QE.mul δF yQ (QE.next H))),
    qz (.mul hz (cv eos)) (QE.var H) (QE.base lE),
    qz (.mul hz (notE (cv eos))) (QE.var HO) (QE.add (QE.base oE) (QE.mul δF yQ (QE.next HO))),
    qz (.mul hz (cv eos)) (QE.var HO) (QE.base oE),
    qz (.mul (cv mQ1) (notE (cv eos))) (QE.var H) (QE.add packE (QE.mul δF (ypow 32) (QE.next H))),
    qz (.mul (cv mQ1) (cv eos)) (QE.var H) packE,
    qz (.mul (cv fst) hzV) (QE.var L) (QE.var H),
    qz (.mul (cv fst) (sumC [mQ1, mQM])) (QE.var L) (QE.mul δF yMB (QE.var H)),
    qz (cv f1) (QE.var RL) (QE.var L), qz (cv f1) (QE.var RO) (QE.var HO),
    qz (.mul (notE (cv isLT)) (nv sL)) (QE.next RL) (QE.var RL), qz (.mul (notE (cv isLT)) (nv sL)) (QE.next RO) (QE.var RO),
    qz (cv f2) (QE.var D1)
      (QE.add (QE.mul δF (QE.var RL) (QE.var L)) (QE.mul δF yMB (QE.mul δF (QE.var RO) (QE.var HO)))),
    qz (.mul (cv fst) (notE (cv f2))) (QE.var D1) (QE.scale (cv cf1) (QE.var L)),
    qz (cv fst) (QE.var D2) (QE.scale (cv cf2) (QE.var L)),
    QE.scale (.mul (cv sL) (notE (cv fst))) (QE.var D1),
    QE.scale (.mul (cv sL) (notE (cv fst))) (QE.var D2),
    qz (cv sH) (QE.var D1) (QE.base (.mul (cv oLt) (notE (cv lb)))),
    qz (cv sH) (QE.var D2) (QE.base (sumC [oDiv, oMod])),
    qz (cv sH) (QE.var S1) (QE.var D1), qz (cv sH) (QE.var S2) (QE.var D2),
    qz (.mul (notE (cv isLT)) (nv sL)) (QE.next S1) (QE.add (QE.var S1) (QE.next D1)),
    qz (.mul (notE (cv isLT)) (nv sL)) (QE.next S2) (QE.add (QE.var S2) (QE.next D2)),
    QE.scale (notE (nv sL)) (QE.var S1), QE.scale (notE (nv sL)) (QE.var S2) ]

/-- `inv·den − 1` under an activity. -/
def invG (δF : F) (act : CoeffExpr F) (inv : ℕ) (d : QE F) : QE F :=
  QE.scale act (QE.sub (QE.mul δF (QE.var inv) d) QE.one)

/-- Accumulator init / step / terminal for a contribution `c` (read at the current / next row). -/
def accG (acc pubI : ℕ) (c : Bool → QE F) : List (QE F) :=
  [ QE.scale (cv isFT) (QE.sub (QE.var acc) (c true)),
    QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next acc) (QE.var acc)) (c false)),
    QE.scale (cv isLT) (QE.sub (QE.var acc) (QE.pub pubI)) ]

/-- The service weight of the keyRg / op-record inverses: `sH − sP·mP` (consume on hdr, provide on preg). -/
def wS (cur : Bool) : CoeffExpr F :=
  if cur then .sub (cv sH) (.mul (cv sP) (cv mP)) else .sub (nv sH) (.mul (nv sP) (nv mP))

def rdQ (cur : Bool) (r : ℕ) : QE F := if cur then QE.var r else QE.next r
def rdC (cur : Bool) (j : ℕ) : CoeffExpr F := if cur then cv j else nv j

/-- **qRead, qServ, qExp** (round 2). -/
def logupQ (δF : F) : List (QE F) :=
  [ invG δF (cv aV) invV (den δF valKey) ] ++
  accG accV pubALv (fun c => QE.scale (rdC c aV) (rdQ c invV)) ++
  [ invG δF (sumC [sH, sP]) invR (HQ.denKeyQ δF keyRgE),
    invG δF (sumC [sH, sP]) invO (HQ.denKeyQ δF opRecE),
    invG δF (cv sH) invJ (HQ.denKeyQ δF keyJetE) ] ++
  accG accS pubALs (fun c => QE.sub (QE.add (QE.scale (wS c) (rdQ c invR)) (QE.scale (wS c) (rdQ c invO)))
    (QE.scale (.mul (rdC c sH) (rdC c mJ)) (rdQ c invJ))) ++
  [ invG δF (cv sH) invX (HQ.denKeyQ δF keyXE) ] ++
  accG accX pubALx (fun c => QE.scale (rdC c sH) (rdQ c invX))

/-- **The ALU's `𝕂′` equations.** -/
def aluQ (δF : F) : List (QE F) := identQ δF ++ logupQ δF

def aluMixed (δF : F) : List (MixedExpr F) := (aluQ δF).flatMap QE.gates

end Gates

/-! ## 4. Degree -/

section Degree
variable {F : Type} [Field F]

theorem bitSum_deg' (base n : ℕ) : (bitSum base n : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem lN_deg : (lN : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem sumC_deg (l : List ℕ) : (sumC l : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem sumN_deg (l : List ℕ) : (sumN l : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem opCode_deg : (opCode : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem baseGates_deg_all : (baseGates (F := F)).all (fun g => decide (g.degree ≤ 4)) = true := by
  have h1 := bitSum_deg' (F := F) bt0 32
  have h2 := bitSum_deg' (F := F) (bt0 + 16) 16
  have h3 := bitSum_deg' (F := F) cb0 6
  have h4 := lN_deg (F := F)
  simp only [baseGates, baseAG, List.map_append, List.all_append, Bool.and_eq_true, List.all_map]
  simp [gKind, gSlot, gSeq, gCompat, gFlag, gCoef, gHdr, gConst, gBind, gBits, gSplit, gCap, gHdrNotLast, opCode,
    succ, coef, bind, ar, gKS, gLtP, gSplitV, sgnLt, prod3, hzV, lE, oE, cnE, AG.gate, CopyG.gate, Op.expr,
    CoeffExpr.degree, List.all_eq_true, opCols, roleCols, modeCols, Function.comp_def, sumC,
    CoeffExpr.sumList, decide_eq_true_eq]
  omega

theorem baseGates_deg : ∀ g ∈ (baseGates (F := F)), g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp baseGates_deg_all g hg

theorem sumQ_deg (d : ℕ) : ∀ l : List (QE F), (∀ e ∈ l, e.re.degree ≤ d ∧ e.im.degree ≤ d) →
    (sumQ l).re.degree ≤ d ∧ (sumQ l).im.degree ≤ d
  | [], _ => by simp [sumQ, QE.zero, MixedExpr.degree]
  | e :: l, h => by
      have ih := sumQ_deg d l fun x hx => h x (List.mem_cons_of_mem _ hx)
      have he := h e List.mem_cons_self
      simp only [sumQ, List.foldr_cons, QE.add, MixedExpr.degree] at ih ⊢
      exact ⟨max_le he.1 ih.1, max_le he.2 ih.2⟩

theorem packE_deg : (packE : QE F).re.degree ≤ 1 ∧ (packE : QE F).im.degree ≤ 1 :=
  sumQ_deg 1 _ fun e he => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp he
    simp [QE.scale, ypow, QE.chal, MixedExpr.degree, CoeffExpr.degree]

theorem aluMixed_deg_all (δF : F) : (aluMixed δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  have h1 := bitSum_deg' (F := F) bt0 32
  have h2 := bitSum_deg' (F := F) (bt0 + 16) 16
  have h3 := (packE_deg (F := F)).1
  have h4 := (packE_deg (F := F)).2
  simp only [List.all_eq_true, decide_eq_true_eq]
  simp [aluMixed, aluQ, identQ, logupQ, invG, accG, wS, rdQ, rdC, qz, ypow, yQ, yMB, valKey,
    keyRgE, opRecE, keyJetE, keyXE, keyRgRE, opRecRE, keyJetRE, keyXRE, reE, hz, hzV, lE, oE, sumC,
    CoeffExpr.sumList, AtomChipHQ.zAt, den, rQ, QE.rlc, QE.gpow, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ,
    HQ.rhoQ, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul,
    QE.scale, MixedExpr.degree, CoeffExpr.degree]
  omega

theorem aluMixed_deg (δF : F) : ∀ g ∈ aluMixed δF, g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp (aluMixed_deg_all δF) g hg

/-- Gate counts (base, `𝕂′` equations, mixed). -/
theorem baseGates_length : (baseGates (F := F)).length = 180 := by
  simp [baseGates, baseAG, gKind, gSlot, gSeq, gCompat, gFlag, gCoef, gHdr, gConst, gBind, gBits, gSplit, gCap,
    bind, opCols, roleCols, modeCols]

theorem aluQ_length (δF : F) : (aluQ δF).length = 39 := by
  simp [aluQ, identQ, logupQ, accG]

theorem aluMixed_length (δF : F) : (aluMixed δF).length = 78 := by
  simp [aluMixed, aluQ, identQ, logupQ, accG, QE.gates]

/-! ## 5. Template, chip, width -/

/-- **The ALU template**: three rounds, base `94 / 0 / 0`, `𝕂`-roles `0 / 18 / 16`. -/
def aluTemplateSZ (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![94, 0, 0]
  extColsOf := ![0, 18, 16]
  baseTransition := baseGates
  extTransition := []
  mixedTransition := aluMixed δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGates_deg
  extTransition_deg := by simp
  mixedTransition_deg := aluMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem aluTemplateSZ_baseCols (δF : F) : (aluTemplateSZ δF).baseCols = 94 := by
  show (∑ r : Fin 3, (![94, 0, 0] : Fin 3 → ℕ) r) = 94
  decide
theorem aluTemplateSZ_extCols (δF : F) : (aluTemplateSZ δF).extCols = 34 := by
  show (∑ r : Fin 3, (![0, 18, 16] : Fin 3 → ℕ) r) = 34
  decide

/-- **`aluSZGates_degree`: every base and every mixed gate of the template has degree `≤ 4`.** -/
theorem aluSZGates_degree (δF : F) :
    (∀ g ∈ (aluTemplateSZ δF).baseTransition, g.degree ≤ 4) ∧
      (∀ g ∈ (aluTemplateSZ δF).mixedTransition, g.degree ≤ 4) :=
  ⟨(aluTemplateSZ δF).baseTransition_deg, (aluTemplateSZ δF).mixedTransition_deg⟩

end Degree

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The preprocessing of column `j < 5`: masks at `0, 1`; the preg selector, id and op code at `2, 3, 4`. -/
def preOf {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (pre : Fin 3 → F[X]) (j : Fin 5) : F[X] :=
  if h0 : (j : ℕ) = 0 then firstRowMask nodes
  else if h1 : (j : ℕ) = 1 then lastRowMask hn nodes
  else pre ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩

/-- **`aluSZChipJ9`**: five verifier-fixed columns (`isFT`, `isLT`, and the preg layout `sP`, `pId`, `pOp`,
given by `pre`). -/
noncomputable def aluSZChipJ9 (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X]) :
    FixedPreprocessingRAP F where
  rap := expandChip (aluTemplateSZ δF) b (slotVal b 94 chals) (slotVal b 94 pubs) orbit (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 5
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 94 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing := preOf hn nodes pre

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X])

/-- **`aluSZ_width_eq`: `w = 196`** (`94 + 34·3`), by `rfl`. -/
theorem aluSZ_width_eq : (aluSZChipJ9 δF b hn nodes orbit chals pubs pre).rap.w = 196 := rfl

end Chip



/-! ## 6. The ALU challenge vector `chalsALJ8` (`z` AND `y`, plus the powers `y^t`) -/

section Vectors
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c2 c3 c4 c5 c6 c7)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- The coordinates of `(y₁ + y₂√δ)^t` (`Quad.mk_mul`, step by step). -/
def ypowC (y1 y2 : K) : ℕ → K × K
  | 0 => (1, 0)
  | t + 1 => ((ypowC y1 y2 t).1 * y1 + algebraMap (ZMod p) K δ * ((ypowC y1 y2 t).2 * y2),
      (ypowC y1 y2 t).1 * y2 + (ypowC y1 y2 t).2 * y1)

theorem ypowC_mk (y1 y2 : K) (t : ℕ) :
    Quad.mk (algebraMap (ZMod p) K δ) (ypowC δ y1 y2 t).1 (ypowC δ y1 y2 t).2 =
      (Quad.mk (algebraMap (ZMod p) K δ) y1 y2) ^ t := by
  induction t with
  | zero => simp [ypowC, Quad.mk_one']
  | succ t ih => rw [pow_succ, ← ih, Quad.mk_mul]; rfl

/-- **`chalsALJ8`**: `chalsAJ8Z` (limb coin `y` at leaves `2 / 3`, seed `z` at `37 / 38`, validity coins,
handle coins) with the verifier-computed powers `y^t` (`t ≤ 32`) at leaves `40 + 2t / 41 + 2t`. -/
def chalsALJ8 (χ : Coins frameJ8 K) (j : ℕ) : K :=
  if 40 ≤ j ∧ j < 106 then
    (if j % 2 = 0 then (ypowC δ (χ cY1) (χ cY2) ((j - 40) / 2)).1 else (ypowC δ (χ cY1) (χ cY2) ((j - 40) / 2)).2)
  else chalsAJ8Z δ χ j

theorem chalsALJ8_of_lt (χ : Coins frameJ8 K) {j : ℕ} (hj : j < 40) : chalsALJ8 δ χ j = chalsAJ8Z δ χ j := by
  simp [chalsALJ8, show ¬ 40 ≤ j by omega]

/-- The limb coin `y` at leaves `2 / 3`. -/
theorem chalsALJ8_y (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsALJ8 δ χ 2) (chalsALJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2) := by
  rw [chalsALJ8_of_lt δ χ (by omega), chalsALJ8_of_lt δ χ (by omega)]; exact chalsAJ8Z_y δ χ

/-- **The validity key's `z` (`zAt = QE.chal 37 38`) reads the fingerprint seed `z = (χ₂, χ₃)`**. -/
theorem chalsALJ8_zAt (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsALJ8 δ χ 37) (chalsALJ8 δ χ 38) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
  rw [chalsALJ8_of_lt δ χ (by omega), chalsALJ8_of_lt δ χ (by omega)]; exact chalsAJ8Z_zAt δ χ

/-- The validity coins `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ` (`ChalsOK … 11`, leaves `5, 7, 11 .. 32`). -/
theorem chalsALJ8_ok (χ : Coins frameJ8 K) :
    ChalsOK δ (chalsALJ8 δ χ) (Quad.mk _ (χ c4) (χ c6)) (Quad.mk _ (χ c5) (χ c7)) 11 := by
  have h := chalsAJ8Z_ok δ χ
  refine ⟨?_, fun i hi => ?_⟩
  · rw [chalsALJ8_of_lt δ χ (by omega), chalsALJ8_of_lt δ χ (by omega)]; exact h.1
  · rw [chalsALJ8_of_lt δ χ (by omega), chalsALJ8_of_lt δ χ (by omega)]; exact h.2 i hi

/-- The handle coins (leaves `33 .. 36`) agree with `chalsMJ8`. -/
theorem chalsALJ8_agree (χ : Coins frameJ8 K) : ∀ j, 33 ≤ j → j ≤ 36 → chalsALJ8 δ χ j = chalsMJ8 δ χ j := by
  intro j h1 h2
  rw [chalsALJ8_of_lt δ χ (by omega)]; exact chalsAJ8Z_agree δ χ j h1 h2

/-- **The packed-`Q` leaves carry `y^t`** (`t ≤ 32`). -/
theorem chalsALJ8_ypow (χ : Coins frameJ8 K) (t : ℕ) (ht : t ≤ 32) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsALJ8 δ χ (40 + 2 * t)) (chalsALJ8 δ χ (41 + 2 * t)) =
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) ^ t := by
  have e1 : (40 + 2 * t - 40) / 2 = t := by omega
  have e2 : (41 + 2 * t - 40) / 2 = t := by omega
  have p1 : (40 + 2 * t) % 2 = 0 := by omega
  have p2 : ¬ (41 + 2 * t) % 2 = 0 := by omega
  simp only [chalsALJ8, show 40 ≤ 40 + 2 * t ∧ 40 + 2 * t < 106 by omega,
    show 40 ≤ 41 + 2 * t ∧ 41 + 2 * t < 106 by omega, p1, p2, e1, e2, and_self, ite_true, ite_false]
  exact ypowC_mk δ _ _ t

end Vectors

/-! ## 7. The read-set instrument at the ALU (AxisChipJ9's, at the ALU serial set) -/

section Instrument
variable {F : Type} [Field F]

/-- No serial-capable column (handle value) is read. -/
def serialFreeAL (g : CoeffExpr F) : Bool := (colsOfB g).all fun i => !serialColsAL.contains i

/-- Arithmetic gates read no serial; copies / selects have a serial-free selector. -/
def okAL : AG F → Bool
  | .ar g => serialFreeAL g
  | .cp c => serialFreeAL c.σ
  | .sel s => !serialColsAL.contains s.σ

/-- `𝕂′` discipline: a serial is read only as an RLC key entry `c · lift(col)` with a coin-only `c`. -/
def keyOKAL : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => coinOnlyA x
  | .Var _ _ => true
  | .Lift g => serialFreeAL g
  | .Scale g u => serialFreeAL g && keyOKAL u
  | .Const _ => true
  | .Add x y => keyOKAL x && keyOKAL y
  | .Sub x y => keyOKAL x && keyOKAL y
  | .Mul x y => keyOKAL x && keyOKAL y
  | .Neg x => keyOKAL x
  | .Pow x _ => keyOKAL x

/-- **`serialFree` receipt** on every base gate. -/
theorem baseGates_serialFree : (baseAG (F := ℚ)).all okAL = true := by decide +kernel

/-- The serial-reading (copy) gates are exactly ten: the lt result, three block copies, five handle binds,
the split value. -/
theorem serial_readers_count :
    ((baseAG (F := ℚ)).filter fun g => !AxisChipJ9.AG.isAr g).length = 10 := by decide +kernel

/-- **`𝕂′` receipt**: no `𝕂′` gate reads a serial outside an RLC key entry (`δF = 7` on `ℚ`). -/
theorem aluMixed_keyOK : (aluMixed (F := ℚ) 7).all keyOKAL = true := by decide +kernel

/-- The base columns the `𝕂′` gates may read. -/
def mixedReadSet : List ℕ :=
  [mS, mV, mW, mQM, mQ1, eos, fst, f1, f2, sL, sH, sP, cf1, cf2, oLt, lb, oDiv, oMod, aV, sv, mP, mJ, idc, kc,
    vc, opc, kS, vS, kE, vE, kA, vA, kB, vB, isFT, isLT] ++ (List.range 32).map (bt0 + ·)

/-- **Read-set receipt**: the `𝕂′` gates read only the keys' columns, the slot flags, the lane bits and the
masks (in particular never `V`, `invP`, `sk`, the counter, the roles). -/
theorem aluMixed_reads :
    (aluMixed (F := ℚ) 7).all (fun g => (liftCols g).all fun c => mixedReadSet.contains c) = true := by
  decide +kernel

/-- **Positive control 1**: `serialFreeAL` flags a gate reading `sv` arithmetically. -/
theorem serialFreeAL_flags : serialFreeAL (F := ℚ) (.sub (cv sv) (cv Vc)) = false := by decide +kernel

/-- **Positive control 2**: the split copy mis-tagged as arithmetic is flagged; a copy with a serial
selector is flagged. -/
theorem flags_naive_arith :
    okAL (F := ℚ) (.ar (CopyG.gate ⟨cv sf, .cur sv, .cur Vc⟩)) = false ∧
      okAL (F := ℚ) (.cp ⟨cv vA, .cur sv, .cur vA⟩) = false := by decide +kernel

/-- **Positive control 3**: a denominator multiplied by a serial is flagged. -/
theorem keyOKAL_flags :
    ((QE.mul (7 : ℚ) (HQ.denKeyQ 7 keyXE) (QE.base (cv vS))).gates).all keyOKAL = false := by decide +kernel

/-- **Positive control 4**: the read-set instrument sees a column outside the set (`Vc`). -/
theorem aluMixed_reads_control :
    ((aluMixed (F := ℚ) 7 ++ (QE.mul (7 : ℚ) (QE.var invV) (QE.base (cv Vc))).gates).all
      (fun g => (liftCols g).all fun c => mixedReadSet.contains c)) = false := by decide +kernel

end Instrument

/-! ## 8. The op record is disjoint from every service key -/

section Disjoint
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd)

theorem opRec_coeff7 {F : Type} [Field F] (f : ℕ → F) : (keyP (opRecRE.map (RE.ev f))).coeff 7 = 6 := by
  rw [keyP_coeff]; simp [opRecRE, tagOp, RE.ev]

/-- **The op record `(id, opc, 0,0,0,0,0, 6)` vs the service keys** (coefficient of `γ⁷`): `TAG_inc` (5 entries),
`TAG_jet` (`3`), `TAG_ax` (`5`), the ALU's own `keyJet` (`3`), and every record of length `≤ 7` (`walkRecA`,
the limb consume, `keyRg`, `keyX`) — pairwise distinct polynomials in `γ` for ALL row values.  Needs `2, 3 ≠ 0`. -/
theorem opRec_disjoint9 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (f g : ℕ → F)
    (r : List RE) (hr : r.length ≤ 7) (a b c : Hd) :
    keyP (opRecRE.map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) ∧
    keyP (opRecRE.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
    keyP (opRecRE.map (RE.ev f)) ≠ keyP ((axRecX a b c).map (RE.ev g)) ∧
    keyP (opRecRE.map (RE.ev f)) ≠ keyP (keyJetRE.map (RE.ev g)) ∧
    keyP (opRecRE.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) := by
  have h6 : (6 : F) ≠ 0 := by
    have : (6 : F) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have c7 := opRec_coeff7 f
  have hr7 : (r.map (RE.ev g)).length ≤ 7 := by simp [hr]
  refine ⟨fun h => h6 ?_, fun h => h3 ?_, fun h => one_ne_zero (α := F) ?_, fun h => h3 ?_, fun h => h6 ?_⟩
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    rw [c7, keyP_coeff_ge _ 7 (by simp [incRecX])] at this; exact this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, jetRecX, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, axRecX, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, keyJetRE, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    rw [c7, keyP_coeff_ge _ 7 hr7] at this; exact this

theorem keyRgAL_coeff7 {F : Type} [Field F] (f : ℕ → F) : (keyP (keyRgRE.map (RE.ev f))).coeff 7 = 7 := by
  rw [keyP_coeff]; simp [keyRgRE, tagRgP, RE.ev]

/-- **`keyRgAL_disjoint`**: the ALU keyRg `(id, kc, vc, 0,0,0,0, 7)` is distinct, for ALL row values, from the J
`inc` (tag 4, 5 entries), J `keyJet`/`jetRecX` (tag 3), axis (tag 5), the ALU's `keyJet` (3), the op record (6),
and every record `r` whose entry 7 is `0` (`keyX`, the limb/walk/split keys; NOT the J chip's keyRg, which in the
balance is tag-last with entry 7 = 2, see `keyRgAL_disjoint_J`).
Needs `2, 7 ≠ 0`. -/
theorem keyRgAL_disjoint {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (h7 : (7 : F) ≠ 0)
    (f g : ℕ → F) (r : List RE) (hr : (r.map (RE.ev g)).getD 7 0 = 0) (a b c : Hd) :
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) ∧
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP ((axRecX a b c).map (RE.ev g)) ∧
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP (keyJetRE.map (RE.ev g)) ∧
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP (opRecRE.map (RE.ev g)) ∧
    keyP (keyRgRE.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) := by
  have c7 := keyRgAL_coeff7 f
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  refine ⟨fun h => h7 ?_, fun h => h4 ?_, fun h => h2 ?_, fun h => h4 ?_, fun h => h1 ?_, fun h => h7 ?_⟩
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    rw [c7, keyP_coeff_ge _ 7 (by simp [incRecX])] at this; exact this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, jetRecX, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, axRecX, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [c7, keyP_coeff, keyJetRE, List.map_cons, List.map_nil, List.getD_cons_succ,
      List.getD_cons_zero, RE.ev, Nat.cast_ofNat] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    rw [c7, opRec_coeff7] at this; linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    rw [c7, keyP_coeff, hr] at this; exact this

/-- **`keyRgAL_disjoint_J`**: the ALU keyRg vector `keyVecL 8 keyRgE eF` (entry 7 = tag 7), at ANY env, differs from
every tag-last `tlF l` whose entry 7 is `1`, `2` or `3`: the J chip's `keyV`, `keyRg`, `keyJet` as they enter the
tagged service balance (`consKT`/`provKT`, `RapJetJ8.lean:338-344`) and the verifier's template pins
(`pinKey`/`pinCons`, `PinJ8.lean:64,74`).  Needs `7 ≠ 1, 2, 3` in `F` (`6, 5, 4 ≠ 0`). -/
theorem keyRgAL_disjoint_J {F K : Type} [Field F] [Field K] [Algebra F K]
    (h6 : (6 : F) ≠ 0) (h5 : (5 : F) ≠ 0) (h4 : (4 : F) ≠ 0)
    (eF : Env F) (l : List F)
    (hl : (Nock.Jet.RapJetJ8.tlF l).getD 7 0 = 1 ∨ (Nock.Jet.RapJetJ8.tlF l).getD 7 0 = 2 ∨
      (Nock.Jet.RapJetJ8.tlF l).getD 7 0 = 3) :
    AxisChipJ9.keyVecL (K := K) 8 keyRgE eF ≠ Nock.Jet.RapJetJ8.keyK 8 (Nock.Jet.RapJetJ8.tlF l) := by
  intro h
  have h7 := congrFun h 7
  simp only [AxisChipJ9.keyVecL, Nock.Jet.RapJetJ8.keyK, keyRgE, keyRgRE, reE, CoeffExpr.eval, tagRgP] at h7
  have h7' := (algebraMap F K).injective h7
  simp [reE, CoeffExpr.eval] at h7'
  simp only [List.getD_eq_getElem?_getD] at hl
  rcases hl with hl | hl | hl <;> rw [hl] at h7'
  · exact h6 (by linear_combination h7')
  · exact h5 (by linear_combination h7')
  · exact h4 (by linear_combination h7')

/-- **`serviceKeysAL_disjoint`**: `serviceKeys_disjoint9` (`J9A/ChipHX9.lean:526`) extended by the op record. -/
theorem serviceKeysAL_disjoint {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (f g : ℕ → F) (r : List RE) (hr : r.length = 4) (a b c : Hd) :
    (keyP (incRecX.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) ∧
      keyP (jetRecX.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) ∧
      keyP (incRecX.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
      keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) ∧
      keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
      keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (r.map (RE.ev g))) ∧
    (keyP (opRecRE.map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) ∧
      keyP (opRecRE.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
      keyP (opRecRE.map (RE.ev f)) ≠ keyP ((axRecX a b c).map (RE.ev g)) ∧
      keyP (opRecRE.map (RE.ev f)) ≠ keyP (keyJetRE.map (RE.ev g)) ∧
      keyP (opRecRE.map (RE.ev f)) ≠ keyP (r.map (RE.ev g))) :=
  ⟨serviceKeys_disjoint9 h2 h3 h5 f g r hr a b c, opRec_disjoint9 h2 h3 f g r (by omega) a b c⟩

end Disjoint

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
