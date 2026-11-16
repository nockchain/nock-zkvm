/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluHonestRows.lean

  **Interface: the honest ALU block generator**
  for `AluSZChipJ9` (W-B witnesses).

  This is the stable interface the per-op satisfaction modules build on:
  * `BRow F` (the 94 base columns, grouped) with `BRow.col : ℕ → F` (the chip's column numbering, `col_*` simp
    lemmas for every named column), and `QRow Q` (the nine round-1 `𝕂′` roles `H HO L D1 D2 S1 S2 RL RO`) with
    `QRow.role`.
  * `CallL`: one primitive call (op, id, the subject serial, the three handles, the values `a b c`, the registry
    index `vc`).  `slotsOf` lays out its slots in the role sequence the chip forces (`gSeq`):
    `add/sub: ra rb rc mQ1`, `lt: ra rb rd mQ1`, `mul: ra rb rc mQM`, `div/mod: ra rx rb ry rs mQM mQ1`.
    A handle slot of a value `< p` is a 2-row split `mS` (`lo, hi`); a big value is a view `mV` (its 32-bit limbs)
    when it is a factor (mul `ra rb`, div/mod `rx rb`), else a one-row read `mR`; witnesses are `mW` lane rows
    (W-B); Q blocks carry the honest carries `CarrySZ.carr` of the op's coefficient list (`dsS1`, `dsS2`).
  * `blockB` (base rows: hdr + slot rows) and `blockQ y` (the `𝕂′` rows at the limb coin `y`; Horner `H`/`HO`
    per slot, `L`, the latch `RL`/`RO`, the contributions `D1`/`D2`, the running sums `S1`/`S2`).
  * `pregRow`, `padRow`.
  * `NextOK rows j nxt`: the successor of row `j` of a block is row `j + 1`, or — at the block's last row — any row
    with `sL = 0 ∧ fst = 0` (a hdr, a preg row or a padding row; the table-last row's virtual successor is a zero
    row, see the note below).

  **The block obligations** (`AluSatSpec`, stated here as `Prop`s, proved by the per-op modules):
  `BlockBaseSat cl` — every base gate at every row of `blockB cl` against every `NextOK` successor;
  `BlockIdentSat cl` — every `identQ` equation likewise, at the `𝕂′` rows `blockQ y cl`.

  **Note (written before the last-row mask of `docs/j8/SPEC.md` §15.2, which now multiplies the ALU's next-row gates
  by `1 − isLT`; the construction below does not rely on the mask): unmasked, the ALU's next-row gates are not guarded by `1 − isLT`** (`(1 − sH − sL)·sL′`,
  `gConst`, `qLatch`, `qSum`).  So the J-9 A pattern "every gate at the table-last row for EVERY next valuation"
  (`ComplJ9AAxisH.axisChipJ9_honest_sat`'s `hgate`) is false for the ALU.  It is not needed: `RAP.Satisfies` puts
  no degree bound on the trace polynomials (`expandChip_satisfies_iff_language`), so the honest `sL` polynomial is
  chosen to vanish at the last node's successor (a virtual zero row); every next-row gate is `sL′`-guarded or reads
  only rows inside a block.  That assembly is the assembly (not this interface's).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CarrySZ
import Nock.Atoms.Limbs
import Nock.Jet.PrimJ9
import Nock.NockVMROM.Thm54.VclL.Chips.QEval

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. Rows -/

/-- **An ALU base row**, the 94 columns grouped (`AluSZChipJ9` §1 numbering in `BRow.col`). -/
structure BRow (F : Type) where
  isFT : F
  isLT : F
  sP : F
  pId : F
  pOp : F
  sH : F
  sL : F
  op : ℕ → F     -- `7 + i`, `i < 6`: add sub lt mul div mod
  role : ℕ → F   -- `13 + i`, `i < 7`: ra rb rc rd rx ry rs
  mode : ℕ → F   -- `20 + i`, `i < 6`: mR mS mV mW mQ1 mQM
  fst : F
  eos : F
  f1 : F
  f2 : F
  sf : F
  aV : F
  cf1 : F
  cf2 : F
  bit : ℕ → F    -- `34 + t`, `t < 32`
  V : F
  invP : F
  sk : F
  sv : F
  kA : F
  vA : F
  kB : F
  vB : F
  kE : F
  vE : F
  lb : F
  idc : F
  kc : F
  vc : F
  opc : F
  kS : F
  vS : F
  mJ : F
  mP : F
  cn : F
  cb : ℕ → F     -- `86 + i`, `i < 6`
  cA : F
  cB : F

namespace BRow
variable {F : Type} [Zero F]

/-- The all-zero row. -/
def zero : BRow F :=
  ⟨0, 0, 0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, 0, 0⟩

/-- **The chip's column reading of a row** (`AluSZChipJ9` §1). -/
def col (r : BRow F) (j : ℕ) : F :=
  if j = 0 then r.isFT else if j = 1 then r.isLT else if j = 2 then r.sP else if j = 3 then r.pId
  else if j = 4 then r.pOp else if j = 5 then r.sH else if j = 6 then r.sL
  else if j < 13 then r.op (j - 7) else if j < 20 then r.role (j - 13) else if j < 26 then r.mode (j - 20)
  else if j = 26 then r.fst else if j = 27 then r.eos else if j = 28 then r.f1 else if j = 29 then r.f2
  else if j = 30 then r.sf else if j = 31 then r.aV else if j = 32 then r.cf1 else if j = 33 then r.cf2
  else if j < 66 then r.bit (j - 34)
  else if j = 66 then r.V else if j = 67 then r.invP else if j = 68 then r.sk else if j = 69 then r.sv
  else if j = 70 then r.kA else if j = 71 then r.vA else if j = 72 then r.kB else if j = 73 then r.vB
  else if j = 74 then r.kE else if j = 75 then r.vE else if j = 76 then r.lb else if j = 77 then r.idc
  else if j = 78 then r.kc else if j = 79 then r.vc else if j = 80 then r.opc else if j = 81 then r.kS
  else if j = 82 then r.vS else if j = 83 then r.mJ else if j = 84 then r.mP else if j = 85 then r.cn
  else if j < 92 then r.cb (j - 86) else if j = 92 then r.cA else if j = 93 then r.cB else 0

@[simp] theorem col_isFT (r : BRow F) : r.col AluSZChipJ9.isFT = r.isFT := rfl
@[simp] theorem col_isLT (r : BRow F) : r.col AluSZChipJ9.isLT = r.isLT := rfl
@[simp] theorem col_sP (r : BRow F) : r.col AluSZChipJ9.sP = r.sP := rfl
@[simp] theorem col_pId (r : BRow F) : r.col AluSZChipJ9.pId = r.pId := rfl
@[simp] theorem col_pOp (r : BRow F) : r.col AluSZChipJ9.pOp = r.pOp := rfl
@[simp] theorem col_sH (r : BRow F) : r.col AluSZChipJ9.sH = r.sH := rfl
@[simp] theorem col_sL (r : BRow F) : r.col AluSZChipJ9.sL = r.sL := rfl
@[simp] theorem col_oAdd (r : BRow F) : r.col AluSZChipJ9.oAdd = r.op 0 := rfl
@[simp] theorem col_oSub (r : BRow F) : r.col AluSZChipJ9.oSub = r.op 1 := rfl
@[simp] theorem col_oLt (r : BRow F) : r.col AluSZChipJ9.oLt = r.op 2 := rfl
@[simp] theorem col_oMul (r : BRow F) : r.col AluSZChipJ9.oMul = r.op 3 := rfl
@[simp] theorem col_oDiv (r : BRow F) : r.col AluSZChipJ9.oDiv = r.op 4 := rfl
@[simp] theorem col_oMod (r : BRow F) : r.col AluSZChipJ9.oMod = r.op 5 := rfl
@[simp] theorem col_ra (r : BRow F) : r.col AluSZChipJ9.ra = r.role 0 := rfl
@[simp] theorem col_rb (r : BRow F) : r.col AluSZChipJ9.rb = r.role 1 := rfl
@[simp] theorem col_rc (r : BRow F) : r.col AluSZChipJ9.rc = r.role 2 := rfl
@[simp] theorem col_rd (r : BRow F) : r.col AluSZChipJ9.rd = r.role 3 := rfl
@[simp] theorem col_rx (r : BRow F) : r.col AluSZChipJ9.rx = r.role 4 := rfl
@[simp] theorem col_ry (r : BRow F) : r.col AluSZChipJ9.ry = r.role 5 := rfl
@[simp] theorem col_rs (r : BRow F) : r.col AluSZChipJ9.rs = r.role 6 := rfl
@[simp] theorem col_mR (r : BRow F) : r.col AluSZChipJ9.mR = r.mode 0 := rfl
@[simp] theorem col_mS (r : BRow F) : r.col AluSZChipJ9.mS = r.mode 1 := rfl
@[simp] theorem col_mV (r : BRow F) : r.col AluSZChipJ9.mV = r.mode 2 := rfl
@[simp] theorem col_mW (r : BRow F) : r.col AluSZChipJ9.mW = r.mode 3 := rfl
@[simp] theorem col_mQ1 (r : BRow F) : r.col AluSZChipJ9.mQ1 = r.mode 4 := rfl
@[simp] theorem col_mQM (r : BRow F) : r.col AluSZChipJ9.mQM = r.mode 5 := rfl
@[simp] theorem col_fst (r : BRow F) : r.col AluSZChipJ9.fst = r.fst := rfl
@[simp] theorem col_eos (r : BRow F) : r.col AluSZChipJ9.eos = r.eos := rfl
@[simp] theorem col_f1 (r : BRow F) : r.col AluSZChipJ9.f1 = r.f1 := rfl
@[simp] theorem col_f2 (r : BRow F) : r.col AluSZChipJ9.f2 = r.f2 := rfl
@[simp] theorem col_sf (r : BRow F) : r.col AluSZChipJ9.sf = r.sf := rfl
@[simp] theorem col_aV (r : BRow F) : r.col AluSZChipJ9.aV = r.aV := rfl
@[simp] theorem col_cf1 (r : BRow F) : r.col AluSZChipJ9.cf1 = r.cf1 := rfl
@[simp] theorem col_cf2 (r : BRow F) : r.col AluSZChipJ9.cf2 = r.cf2 := rfl
theorem col_bit (r : BRow F) (t : ℕ) (ht : t < 32) : r.col (AluSZChipJ9.bt0 + t) = r.bit t := by
  show r.col (34 + t) = _
  rw [col, if_neg (show ¬ (34 + t = 0) by omega), if_neg (show ¬ (34 + t = 1) by omega), if_neg (show ¬ (34 + t = 2) by omega), if_neg (show ¬ (34 + t = 3) by omega), if_neg (show ¬ (34 + t = 4) by omega), if_neg (show ¬ (34 + t = 5) by omega), if_neg (show ¬ (34 + t = 6) by omega), if_neg (show ¬ (34 + t < 13) by omega), if_neg (show ¬ (34 + t < 20) by omega), if_neg (show ¬ (34 + t < 26) by omega), if_neg (show ¬ (34 + t = 26) by omega), if_neg (show ¬ (34 + t = 27) by omega), if_neg (show ¬ (34 + t = 28) by omega), if_neg (show ¬ (34 + t = 29) by omega), if_neg (show ¬ (34 + t = 30) by omega), if_neg (show ¬ (34 + t = 31) by omega), if_neg (show ¬ (34 + t = 32) by omega), if_neg (show ¬ (34 + t = 33) by omega), if_pos (show 34 + t < 66 by omega), show 34 + t - 34 = t by omega]
@[simp] theorem col_Vc (r : BRow F) : r.col AluSZChipJ9.Vc = r.V := rfl
@[simp] theorem col_invP (r : BRow F) : r.col AluSZChipJ9.invP = r.invP := rfl
@[simp] theorem col_sk (r : BRow F) : r.col AluSZChipJ9.sk = r.sk := rfl
@[simp] theorem col_sv (r : BRow F) : r.col AluSZChipJ9.sv = r.sv := rfl
@[simp] theorem col_kA (r : BRow F) : r.col AluSZChipJ9.kA = r.kA := rfl
@[simp] theorem col_vA (r : BRow F) : r.col AluSZChipJ9.vA = r.vA := rfl
@[simp] theorem col_kB (r : BRow F) : r.col AluSZChipJ9.kB = r.kB := rfl
@[simp] theorem col_vB (r : BRow F) : r.col AluSZChipJ9.vB = r.vB := rfl
@[simp] theorem col_kE (r : BRow F) : r.col AluSZChipJ9.kE = r.kE := rfl
@[simp] theorem col_vE (r : BRow F) : r.col AluSZChipJ9.vE = r.vE := rfl
@[simp] theorem col_lb (r : BRow F) : r.col AluSZChipJ9.lb = r.lb := rfl
@[simp] theorem col_idc (r : BRow F) : r.col AluSZChipJ9.idc = r.idc := rfl
@[simp] theorem col_kc (r : BRow F) : r.col AluSZChipJ9.kc = r.kc := rfl
@[simp] theorem col_vc (r : BRow F) : r.col AluSZChipJ9.vc = r.vc := rfl
@[simp] theorem col_opc (r : BRow F) : r.col AluSZChipJ9.opc = r.opc := rfl
@[simp] theorem col_kS (r : BRow F) : r.col AluSZChipJ9.kS = r.kS := rfl
@[simp] theorem col_vS (r : BRow F) : r.col AluSZChipJ9.vS = r.vS := rfl
@[simp] theorem col_mJ (r : BRow F) : r.col AluSZChipJ9.mJ = r.mJ := rfl
@[simp] theorem col_mP (r : BRow F) : r.col AluSZChipJ9.mP = r.mP := rfl
@[simp] theorem col_cn (r : BRow F) : r.col AluSZChipJ9.cn = r.cn := rfl
theorem col_cb (r : BRow F) (i : ℕ) (hi : i < 6) : r.col (AluSZChipJ9.cb0 + i) = r.cb i := by
  show r.col (86 + i) = _
  rw [col, if_neg (show ¬ (86 + i = 0) by omega), if_neg (show ¬ (86 + i = 1) by omega), if_neg (show ¬ (86 + i = 2) by omega), if_neg (show ¬ (86 + i = 3) by omega), if_neg (show ¬ (86 + i = 4) by omega), if_neg (show ¬ (86 + i = 5) by omega), if_neg (show ¬ (86 + i = 6) by omega), if_neg (show ¬ (86 + i < 13) by omega), if_neg (show ¬ (86 + i < 20) by omega), if_neg (show ¬ (86 + i < 26) by omega), if_neg (show ¬ (86 + i = 26) by omega), if_neg (show ¬ (86 + i = 27) by omega), if_neg (show ¬ (86 + i = 28) by omega), if_neg (show ¬ (86 + i = 29) by omega), if_neg (show ¬ (86 + i = 30) by omega), if_neg (show ¬ (86 + i = 31) by omega), if_neg (show ¬ (86 + i = 32) by omega), if_neg (show ¬ (86 + i = 33) by omega), if_neg (show ¬ (86 + i < 66) by omega), if_neg (show ¬ (86 + i = 66) by omega), if_neg (show ¬ (86 + i = 67) by omega), if_neg (show ¬ (86 + i = 68) by omega), if_neg (show ¬ (86 + i = 69) by omega), if_neg (show ¬ (86 + i = 70) by omega), if_neg (show ¬ (86 + i = 71) by omega), if_neg (show ¬ (86 + i = 72) by omega), if_neg (show ¬ (86 + i = 73) by omega), if_neg (show ¬ (86 + i = 74) by omega), if_neg (show ¬ (86 + i = 75) by omega), if_neg (show ¬ (86 + i = 76) by omega), if_neg (show ¬ (86 + i = 77) by omega), if_neg (show ¬ (86 + i = 78) by omega), if_neg (show ¬ (86 + i = 79) by omega), if_neg (show ¬ (86 + i = 80) by omega), if_neg (show ¬ (86 + i = 81) by omega), if_neg (show ¬ (86 + i = 82) by omega), if_neg (show ¬ (86 + i = 83) by omega), if_neg (show ¬ (86 + i = 84) by omega), if_neg (show ¬ (86 + i = 85) by omega), if_pos (show 86 + i < 92 by omega), show 86 + i - 86 = i by omega]
@[simp] theorem col_cA (r : BRow F) : r.col AluSZChipJ9.cA = r.cA := rfl
@[simp] theorem col_cB (r : BRow F) : r.col AluSZChipJ9.cB = r.cB := rfl

end BRow

/-- **The round-1 `𝕂′` roles of an ALU row** (`H HO L D1 D2 S1 S2 RL RO`; round 2 is the LogUp lane's). -/
structure QRow (Q : Type) where
  H : Q
  HO : Q
  L : Q
  D1 : Q
  D2 : Q
  S1 : Q
  S2 : Q
  RL : Q
  RO : Q

namespace QRow
variable {Q : Type} [Zero Q]

def zero : QRow Q := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The chip's `𝕂′`-role reading (`AluSZChipJ9` §1: `H 0, HO 2, L 4, D1 6, D2 8, S1 10, S2 12, RL 14, RO 16`). -/
def role (q : QRow Q) (r : ℕ) : Q :=
  if r = 0 then q.H else if r = 2 then q.HO else if r = 4 then q.L else if r = 6 then q.D1
  else if r = 8 then q.D2 else if r = 10 then q.S1 else if r = 12 then q.S2 else if r = 14 then q.RL
  else if r = 16 then q.RO else 0

end QRow

/-! ## 2. Calls and slots -/

/-- `B = 2^32` as a natural number. -/
abbrev Bn : ℕ := 2 ^ 32

/-- The chip's op index (`opCols` order: add sub lt mul div mod; `dec` has no ALU block, `hnoDec`). -/
def opIx : PrimOp → ℕ
  | .add => 0 | .sub => 1 | .lt => 2 | .mul => 3 | .div => 4 | .mod => 5 | .dec => 6

/-- **One primitive call** as the ALU sees it: op, registry id and index `vc`, the subject cell's serial `vS`, the
handles `(kA, vA) (kB, vB) (kE, vE)` of `a`, `b` and the result, and the values. -/
structure CallL where
  op : PrimOp
  id : ℕ
  vc : ℕ
  vS : ℕ
  kA : ℕ
  vA : ℕ
  kB : ℕ
  vB : ℕ
  kE : ℕ
  vE : ℕ
  a : ℕ
  b : ℕ
  c : ℕ

/-- The result loobean of a `lt` call (`c`), `0` otherwise. -/
def CallL.lbv (cl : CallL) : ℕ := if cl.op = .lt then cl.c else 0

/-- The `32`-bit words of a value (`Nock.Atoms.limbs`, at least one word). -/
def wordsOf (v : ℕ) : List ℕ := if v = 0 then [0] else Nock.Atoms.limbs v

/-- The two split words `lo, hi` of a value `< p`. -/
def splitOf (v : ℕ) : List ℕ := [v % Bn, v / Bn]

/-- **A slot**: its role (`none` for a Q block) and mode (indices into `BRow.role` / `BRow.mode`), lane words,
handle `(sk, sv)`, and identity coefficients `cf1 cf2` (`gCoef`). -/
structure SlotL where
  role : Option ℕ
  mode : ℕ
  words : List ℕ
  /-- The value's limbs (the identity reads `L = Σ vw_i y^i`): `= words` except on an `mR` read, whose value
  is the atom's limbs (its one lane row is `0`). -/
  vw : List ℕ
  sk : ℕ
  sv : ℕ
  cf1 : ℤ
  cf2 : ℤ

/-- The `gCoef` coefficients of role `r` (index) at op `o` with result loobean `lb` (`sgnLt = 1 − 2·lb`). -/
def coefOf (o : PrimOp) (lb : ℕ) : Option ℕ → ℤ × ℤ
  | some 0 => match o with
    | .add => (1, 0) | .sub => (-1, 0) | .lt => (1 - 2 * (lb : ℤ), 0) | .div => (-1, 0) | .mod => (-1, 0)
    | _ => (0, 0)
  | some 1 => match o with
    | .add => (1, 0) | .sub => (1, 0) | .lt => (-(1 - 2 * (lb : ℤ)), 0) | .div => (0, -1) | .mod => (0, -1)
    | _ => (0, 0)
  | some 2 => match o with
    | .add => (-1, 0) | .sub => (1, 0) | .mul => (-1, 0) | _ => (0, 0)
  | some 3 => (1, 0)
  | some 4 => (0, 0)
  | some 5 => (1, 1)
  | some 6 => (0, 1)
  | _ => (0, 0)

/-- Q-block coefficients (`coef mQ1`, `coef mQM`). -/
def coefQ1 (o : PrimOp) : ℤ × ℤ := match o with
  | .add => (1, 0) | .sub => (1, 0) | .lt => (1, 0) | .div => (0, 1) | .mod => (0, 1) | _ => (0, 0)

/-- Is role `r` a factor at op `o` (mul `ra rb`; div/mod `rx rb`)? -/
def isFactor (o : PrimOp) (r : ℕ) : Bool := match o with
  | .mul => r = 0 || r = 1
  | .div => r = 4 || r = 1
  | .mod => r = 4 || r = 1
  | _ => false

/-- **A handle slot** of value `v` with handle `(k, s)`: `mS` split if `v < p`, else a view (`mV`) for a factor or
a one-row read (`mR`). -/
def handleSlot (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) : SlotL :=
  let cf := coefOf o lb (some r)
  if v < p then ⟨some r, 1, splitOf v, splitOf v, 0, v, cf.1, cf.2⟩
  else if isFactor o r then ⟨some r, 2, Nock.Atoms.limbs v, Nock.Atoms.limbs v, k, s, cf.1, cf.2⟩
  else ⟨some r, 0, [0], Nock.Atoms.limbs v, k, s, cf.1, cf.2⟩

/-- **A W-B witness slot** (`mW`) of value `w`. -/
def witSlot (o : PrimOp) (lb r w : ℕ) : SlotL :=
  let cf := coefOf o lb (some r)
  ⟨some r, 3, wordsOf w, wordsOf w, 0, 0, cf.1, cf.2⟩

/-- Pack a carry list into 32-bit words (32 one-bit carries per word, low first). -/
def packQ1 : List ℕ → List ℕ
  | [] => []
  | q :: qs => ((((q :: qs).take 32).zipIdx).map fun x => x.1 * 2 ^ x.2).sum :: packQ1 ((q :: qs).drop 32)
termination_by qs => qs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- A Q block of the carries `qs` (`mQ1` packed, mode 4; `mQM` one per row, mode 5), at least one row. -/
def qSlot (o : PrimOp) (packed : Bool) (qs : List ℤ) : SlotL :=
  let ws := qs.map Int.toNat
  if packed then
    let cf := coefQ1 o
    ⟨none, 4, (if ws = [] then [0] else packQ1 ws), [], 0, 0, cf.1, cf.2⟩
  else ⟨none, 5, (if ws = [] then [0] else ws), [], 0, 0, 1, 0⟩

/-! ### The coefficient lists of the identities (as `ℤ`-lists, low first) -/

def zl (l : List ℕ) : List ℤ := l.map Int.ofNat

/-- Product of coefficient lists. -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, bs => addL (bs.map (a * ·)) (0 :: mulL as bs)

/-- The 16-bit high halves of words. -/
def hiL (l : List ℕ) : List ℕ := l.map (· / 2 ^ 16)

/-- `W = A·B + (X − B)·O_A·O_B` (the product slot's contribution). -/
def wL (A B : List ℕ) : List ℤ :=
  addL (mulL (zl A) (zl B)) (mulL [-(Bn : ℤ), 1] (mulL (zl (hiL A)) (zl (hiL B))))

/-- The lt witness `d` (`yes = [a < b]`: `d = b − a − 1`; else `d = a − b`). -/
def ltWit (a b : ℕ) : ℕ := if a < b then b - a - 1 else a - b

/-- **The slots of a call** in the chip's role sequence (role indices `ra 0 rb 1 rc 2 rd 3 rx 4 ry 5 rs 6`). -/
def slotsOf (p : ℕ) (cl : CallL) : List SlotL :=
  let o := cl.op
  let lb := cl.lbv
  let sA := handleSlot p o lb 0 cl.a cl.kA cl.vA
  let sB := handleSlot p o lb 1 cl.b cl.kB cl.vB
  match o with
  | .add =>
    let sC := handleSlot p o lb 2 cl.c cl.kE cl.vE
    [sA, sB, sC, qSlot o true (carr Bn 0 (addL (addL (zl sA.vw) (zl sB.vw)) (negL (zl sC.vw))))]
  | .sub =>
    let sC := handleSlot p o lb 2 cl.c cl.kE cl.vE
    [sA, sB, sC, qSlot o true (carr Bn 0 (addL (addL (zl sB.vw) (zl sC.vw)) (negL (zl sA.vw))))]
  | .lt =>
    let sD := witSlot o lb 3 (ltWit cl.a cl.b)
    let sg : ℤ := 1 - 2 * (lb : ℤ)
    let ds := addL (addL (addL ((zl sA.vw).map (sg * ·)) ((zl sB.vw).map (-sg * ·))) (zl sD.vw))
      [1 - (lb : ℤ)]
    [sA, sB, sD, qSlot o true (carr Bn 0 ds)]
  | .mul =>
    let sC := handleSlot p o lb 2 cl.c cl.kE cl.vE
    [sA, sB, sC, qSlot o false (carr Bn 0 (addL (wL sA.vw sB.vw) (negL (zl sC.vw))))]
  | .div =>
    let sX := handleSlot p o lb 4 cl.c cl.kE cl.vE
    let sY := witSlot o lb 5 (cl.a % cl.b)
    let sS := witSlot o lb 6 (cl.b - cl.a % cl.b - 1)
    [sA, sX, sB, sY, sS,
      qSlot o false (carr Bn 0 (addL (addL (wL sX.vw sB.vw) (zl sY.vw)) (negL (zl sA.vw)))),
      qSlot o true (carr Bn 0 (addL (addL (addL (zl sY.vw) (zl sS.vw)) [1]) (negL (zl sB.vw))))]
  | .mod =>
    let sX := witSlot o lb 4 (cl.a / cl.b)
    let sY := handleSlot p o lb 5 cl.c cl.kE cl.vE
    let sS := witSlot o lb 6 (cl.b - cl.c - 1)
    [sA, sX, sB, sY, sS,
      qSlot o false (carr Bn 0 (addL (addL (wL sX.vw sB.vw) (zl sY.vw)) (negL (zl sA.vw)))),
      qSlot o true (carr Bn 0 (addL (addL (addL (zl sY.vw) (zl sS.vw)) [1]) (negL (zl sB.vw))))]
  | .dec => []

/-! ## 3. Base rows -/

section Base
variable {F : Type} [Field F]

/-- The binary bit `t` of `w`. -/
def bitOf (w t : ℕ) : ℕ := w / 2 ^ t % 2

/-- The `[cond]` indicator in `F`. -/
def ind (c : Prop) [Decidable c] : F := if c then 1 else 0

/-- **The hdr row of a call** (block constants, the registry key `(id, 1, vc)`, `kS = 1`, `mJ = 1`). -/
def hdrRow (cl : CallL) : BRow F :=
  { (BRow.zero : BRow F) with
    sH := 1
    op := fun i => ind (i = opIx cl.op)
    lb := (cl.lbv : F)
    kA := (cl.kA : F), vA := (cl.vA : F), kB := (cl.kB : F), vB := (cl.vB : F)
    kE := (cl.kE : F), vE := (cl.vE : F)
    idc := (cl.id : F), kc := 1, vc := (cl.vc : F), opc := ((opIx cl.op + 1 : ℕ) : F), kS := 1,
    vS := (cl.vS : F), mJ := 1 }

/-- The flags of a slot's first row (`gFlag`, `gCoef`). -/
def isF1 (o : PrimOp) (s : SlotL) : Bool := s.role = some 0 && o = .mul || s.role = some 4 && (o = .div || o = .mod)
def isF2 (o : PrimOp) (s : SlotL) : Bool := s.role = some 1 && (o = .mul || o = .div || o = .mod)

/-- **Row `i` of slot `s`** of a call (`n = |words|` rows; lane bits = the word; the 6-bit counter `i + 1` on Horner
value slots `mS mV mW`; `V`, `invP` on the split head). -/
def slotRow (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : BRow F :=
  let n := s.words.length
  let w := s.words.getD i 0
  let first := decide (i = 0)
  let hv := decide (s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3)
  let lo := s.words.getD 0 0
  let hi := s.words.getD 1 0
  { (hdrRow (F := F) cl) with
    sH := 0, sL := 1
    role := fun j => ind (s.role = some j)
    mode := fun j => ind (j = s.mode)
    fst := ind (i = 0), eos := ind (i + 1 = n)
    f1 := ind (first ∧ isF1 cl.op s), f2 := ind (first ∧ isF2 cl.op s)
    sf := ind (first ∧ s.mode = 1), aV := ind (first ∧ (s.mode = 0 ∨ s.mode = 2))
    cf1 := if i = 0 then (s.cf1 : F) else 0, cf2 := if i = 0 then (s.cf2 : F) else 0
    bit := fun t => (bitOf w t : F)
    V := if first ∧ s.mode = 1 then ((lo + Bn * hi : ℕ) : F) else 0
    invP := if first ∧ s.mode = 1 ∧ lo ≠ 0 then ((hi : F) - ((Bn - 1 : ℕ) : F))⁻¹ else 0
    sk := (s.sk : F), sv := (s.sv : F)
    idc := 0, kc := 0, vc := 0, opc := 0, kS := 0, vS := 0, mJ := 0
    cn := if hv then ((i + 1 : ℕ) : F) else 0
    cb := fun j => if hv then (bitOf (i + 1) j : F) else 0
    cA := if hv then ((bitOf (i + 1) 0 * bitOf (i + 1) 1 * bitOf (i + 1) 2 : ℕ) : F) else 0
    cB := if hv then ((bitOf (i + 1) 3 * bitOf (i + 1) 4 * bitOf (i + 1) 5 : ℕ) : F) else 0 }

/-- The rows of one slot. -/
def slotRows (p : ℕ) (cl : CallL) (s : SlotL) : List (BRow F) :=
  (List.range s.words.length).map (slotRow p cl s)

/-- **The base rows of a call's block**: hdr, then its slots in order. -/
def blockB (p : ℕ) (cl : CallL) : List (BRow F) :=
  hdrRow cl :: (slotsOf p cl).flatMap (slotRows p cl)

/-- **A preg row** (preprocessed `sP = 1`, the id and op code; provides `keyRg (id, 1, vc)` and the op record with
multiplicity `mP`). -/
def pregRow (pid pcode pvc pm : ℕ) : BRow F :=
  { (BRow.zero : BRow F) with
    sP := 1
    pId := (pid : F)
    pOp := (pcode : F)
    idc := (pid : F)
    kc := 1
    vc := (pvc : F)
    opc := (pcode : F)
    mP := (pm : F) }

/-- A padding row. -/
def padRow : BRow F := BRow.zero

end Base

/-! ## 4. The `𝕂′` rows at the limb coin `y` -/

section KRows
variable {Q : Type} [CommRing Q]

/-- Horner of a word list at `y` (`Σ w_i y^i`). -/
def horner (y : Q) (ws : List ℕ) : Q := evR y (zl ws)

/-- Horner from position `i` (`H` at row `i` of a Horner slot: `Σ_{k ≥ i} w_k y^{k−i}`). -/
def hornerFrom (y : Q) (ws : List ℕ) (i : ℕ) : Q := horner y (ws.drop i)

/-- The packed-row value `Σ_t b_t y^t` of a word (`packE`). -/
def packV (y : Q) (w : ℕ) : Q := ((List.range 32).map fun t => ((bitOf w t : ℕ) : Q) * y ^ t).sum

/-- Horner of a packed `mQ1` block from row `i` (`H = packE + y^32·H′`). -/
def hornerQ1 (y : Q) : List ℕ → Q
  | [] => 0
  | w :: ws => packV y w + y ^ 32 * hornerQ1 y ws

/-- `H` at row `i` of a slot. -/
def slotH (y : Q) (s : SlotL) (i : ℕ) : Q :=
  if s.mode = 4 then hornerQ1 y (s.words.drop i)
  else if s.mode = 0 then 0 else hornerFrom y s.words i

/-- `HO` at row `i` of a slot (the high halves; Horner modes only). -/
def slotHO (y : Q) (s : SlotL) (i : ℕ) : Q :=
  if s.mode = 0 ∨ s.mode = 4 then 0 else hornerFrom y (hiL s.words) i

/-- The slot's value `L` at its first row: the Horner value (`mS mV mW`, and `mR`: the atom's leaf at `y`,
`Σ limbs y^i`), `(y − B)·H` on a Q block. -/
def slotL (y : Q) (s : SlotL) : Q :=
  if s.mode = 4 ∨ s.mode = 5 then (y - (Bn : Q)) * slotH y s 0 else horner y s.vw

/-- The latch `(RL, RO)` of a call: the first factor's `(L, HO)` (`0` without a factor). -/
def latchOf (p : ℕ) (y : Q) (cl : CallL) : Q × Q :=
  match (slotsOf p cl).find? (fun s => isF1 cl.op s) with
  | some s => (slotL y s, slotHO y s 0)
  | none => (0, 0)

/-- The contributions `(D1, D2)` of a slot's first row (`qContr`). -/
def slotD (p : ℕ) (y : Q) (cl : CallL) (s : SlotL) : Q × Q :=
  let L := slotL y s
  let lt := latchOf p y cl
  if isF2 cl.op s then (lt.1 * L + (y - (Bn : Q)) * (lt.2 * slotHO y s 0), (s.cf2 : Q) * L)
  else ((s.cf1 : Q) * L, (s.cf2 : Q) * L)

/-- The hdr contributions `(oLt·(1 − lb), oDiv + oMod)`. -/
def hdrD (cl : CallL) : Q × Q :=
  ((if cl.op = .lt then (1 - (cl.lbv : Q)) else 0), (if cl.op = .div ∨ cl.op = .mod then 1 else 0))

/-- The per-row `(D1, D2)` of a block's lane rows, in order. -/
def laneD (p : ℕ) (y : Q) (cl : CallL) : List (Q × Q) :=
  (slotsOf p cl).flatMap fun s => (List.range s.words.length).map fun i => if i = 0 then slotD p y cl s else (0, 0)

/-- Running sums `S_j = Σ_{k ≤ j} D_k` from an initial value. -/
def runSums : Q × Q → List (Q × Q) → List (Q × Q)
  | _, [] => []
  | acc, d :: ds => (acc.1 + d.1, acc.2 + d.2) :: runSums (acc.1 + d.1, acc.2 + d.2) ds

/-- The `(H, HO, L)` of the lane rows, in order. -/
def laneHL (y : Q) (cl : CallL) (p : ℕ) : List (Q × Q × Q) :=
  (slotsOf p cl).flatMap fun s => (List.range s.words.length).map fun i =>
    (slotH y s i, slotHO y s i, if i = 0 then slotL y s else 0)

/-- **The `𝕂′` rows of a call's block** (hdr first). -/
def blockQ (p : ℕ) (y : Q) (cl : CallL) : List (QRow Q) :=
  let lt := latchOf p y cl
  let d0 := hdrD (Q := Q) cl
  let ds := laneD p y cl
  let ss := runSums d0 ds
  ⟨0, 0, 0, d0.1, d0.2, d0.1, d0.2, lt.1, lt.2⟩ ::
    ((laneHL y cl p).zip (ds.zip ss)).map fun x =>
      ⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2, lt.1, lt.2⟩

end KRows

/-! ## 5. The block obligations -/

section Spec
variable {F : Type} [Field F]

/-- The base-gate environment of a row and a successor (base gates are coin-free). -/
def envB (cur nxt : ℕ → F) : Env F := ⟨cur, nxt, fun _ => 0, fun _ => 0⟩

/-- **The successor condition at row `j` of a block**: inside the block, the next block row; at the block's last
row, any row with `sL = 0` and `fst = 0` (a hdr, preg or padding row). -/
def NextOK (rows : List (BRow F)) (j : ℕ) (nxt : BRow F) : Prop :=
  (j + 1 < rows.length → nxt = rows.getD (j + 1) BRow.zero) ∧
    (rows.length ≤ j + 1 → nxt.sL = 0 ∧ nxt.fst = 0)

/-- **A call the ALU serves honestly**: a chip op (not `dec`); the result is `primSem`; operands/results small or
big as their handles say (`(0, v)` small, `(2, s)` big); every Horner value slot has `≤ 62` limbs. -/
structure CallOK (p : ℕ) (cl : CallL) : Prop where
  notDec : cl.op ≠ .dec
  sem : Nock.Jet.Prim.primSem cl.op cl.a cl.b = some cl.c
  hp : Bn < p
  kAok : (cl.a < p → cl.kA = 0 ∧ cl.vA = cl.a) ∧ (p ≤ cl.a → cl.kA = 2)
  kBok : (cl.b < p → cl.kB = 0 ∧ cl.vB = cl.b) ∧ (p ≤ cl.b → cl.kB = 2)
  kEok : cl.op ≠ .lt → (cl.c < p → cl.kE = 0 ∧ cl.vE = cl.c) ∧ (p ≤ cl.c → cl.kE = 2)
  kElt : cl.op = .lt → cl.kE = 0 ∧ cl.vE = cl.c
  vSok : cl.vS < p
  limbs62 : ∀ s ∈ slotsOf p cl, (s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3) → s.words.length ≤ 62

/-- **Block obligation, base**: every base gate at every row of the block, against every successor. -/
def BlockBaseSat (p : ℕ) (cl : CallL) : Prop :=
  ∀ j < (blockB (F := F) p cl).length, ∀ nxt : BRow F, NextOK (blockB p cl) j nxt →
    ∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)),
      g.eval (envB ((blockB p cl).getD j BRow.zero).col nxt.col) = 0

/-- **The `𝕂`-coordinates of a row's `𝕂′` roles** (role `r` even: `Re` at `r`, `Im` at `r + 1`; `QE.var r` reads
`Quad.mk (k r) (k (r + 1))`). -/
def kvec {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (q : QRow (Quad (algebraMap F K δ))) (j : ℕ) : K :=
  let z : K × K := (Quad.equiv (algebraMap F K δ)).symm (q.role (j - j % 2))
  if j % 2 = 0 then z.1 else z.2

/-- **Block obligation, `𝕂′` identities**: every `identQ` equation at every row of the block, at the limb coin `y`
(the challenge vector carries `y` at leaves `2 / 3` and `y^t` at `40 + 2t / 41 + 2t`, `chalsALJ8_y` /
`chalsALJ8_ypow`), against every successor (base `NextOK`; inside the block the next `𝕂′` row is the block's). -/
def BlockIdentSat {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (p : ℕ) (cl : CallL) : Prop :=
  ∀ (y : Quad (algebraMap F K δ)) (chal : ℕ → K),
    Quad.mk _ (chal 2) (chal 3) = y →
    (∀ t ≤ 32, Quad.mk _ (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t) →
    ∀ j < (blockB (F := F) p cl).length, ∀ nxt : BRow F, NextOK (blockB p cl) j nxt →
    ∀ nq : QRow (Quad (algebraMap F K δ)), (j + 1 < (blockB (F := F) p cl).length → nq = (blockQ p y cl).getD (j + 1) QRow.zero) →
    ∀ e ∈ AluSZChipJ9.identQ δ,
      e.ev δ ⟨kvec δ ((blockQ p y cl).getD j QRow.zero), kvec δ nq, chal, fun _ => 0⟩
        (envB ((blockB p cl).getD j BRow.zero).col nxt.col) = 0

/-! ### Splitting the obligations by gate group (for the split by gate group) -/

/-- **A group of base gates at every block row** (`GroupSat p cl AluSZChipJ9.gKind`, …). -/
def GroupSat (p : ℕ) (cl : CallL) (gs : List (AxisChipJ9.AG F)) : Prop :=
  ∀ j < (blockB (F := F) p cl).length, ∀ nxt : BRow F, NextOK (blockB p cl) j nxt →
    ∀ a ∈ gs, (AxisChipJ9.AG.gate a).eval (envB ((blockB p cl).getD j BRow.zero).col nxt.col) = 0

theorem groupSat_append (p : ℕ) (cl : CallL) (gs hs : List (AxisChipJ9.AG F)) :
    GroupSat (F := F) p cl (gs ++ hs) ↔ GroupSat (F := F) p cl gs ∧ GroupSat (F := F) p cl hs := by
  constructor
  · intro h
    exact ⟨fun j hj nxt hn a ha => h j hj nxt hn a (List.mem_append_left _ ha),
      fun j hj nxt hn a ha => h j hj nxt hn a (List.mem_append_right _ ha)⟩
  · rintro ⟨h1, h2⟩ j hj nxt hn a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h1 j hj nxt hn a ha
    · exact h2 j hj nxt hn a ha

/-- **The base obligation is the conjunction of the twelve groups** (`baseGates = baseAG.map AG.gate`,
`baseAG = gKind ++ gSlot ++ gSeq ++ gCompat ++ gFlag ++ gCoef ++ gHdr ++ gConst ++ gBind ++ gBits ++ gSplit ++
gCap`). -/
theorem blockBaseSat_iff (p : ℕ) (cl : CallL) :
    BlockBaseSat (F := F) p cl ↔ GroupSat (F := F) p cl AluSZChipJ9.baseAG := by
  constructor
  · intro h j hj nxt hn a ha
    exact h j hj nxt hn _ (List.mem_map_of_mem ha)
  · intro h j hj nxt hn g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact h j hj nxt hn a ha

/-- `GroupSat` of the twelve groups gives `BlockBaseSat`. -/
theorem blockBaseSat_of_groups (p : ℕ) (cl : CallL)
    (h1 : GroupSat (F := F) p cl AluSZChipJ9.gKind) (h2 : GroupSat (F := F) p cl AluSZChipJ9.gSlot)
    (h3 : GroupSat (F := F) p cl AluSZChipJ9.gSeq) (h4 : GroupSat (F := F) p cl AluSZChipJ9.gCompat)
    (h5 : GroupSat (F := F) p cl AluSZChipJ9.gFlag) (h6 : GroupSat (F := F) p cl AluSZChipJ9.gCoef)
    (h7 : GroupSat (F := F) p cl AluSZChipJ9.gHdr) (h8 : GroupSat (F := F) p cl AluSZChipJ9.gConst)
    (h9 : GroupSat (F := F) p cl AluSZChipJ9.gBind) (h10 : GroupSat (F := F) p cl AluSZChipJ9.gBits)
    (h11 : GroupSat (F := F) p cl AluSZChipJ9.gSplit) (h12 : GroupSat (F := F) p cl AluSZChipJ9.gCap) :
    BlockBaseSat (F := F) p cl := by
  rw [blockBaseSat_iff]
  unfold AluSZChipJ9.baseAG
  simp only [groupSat_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩

/-- **A list of `𝕂′` equations at every block row** (the `BlockIdentSat` shape for a sub-list `es`). -/
def QSat {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (p : ℕ) (cl : CallL) (es : List (QE F)) : Prop :=
  ∀ (y : Quad (algebraMap F K δ)) (chal : ℕ → K),
    Quad.mk _ (chal 2) (chal 3) = y →
    (∀ t ≤ 32, Quad.mk _ (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t) →
    ∀ j < (blockB (F := F) p cl).length, ∀ nxt : BRow F, NextOK (blockB p cl) j nxt →
    ∀ nq : QRow (Quad (algebraMap F K δ)), (j + 1 < (blockB (F := F) p cl).length → nq = (blockQ p y cl).getD (j + 1) QRow.zero) →
    ∀ e ∈ es,
      e.ev δ ⟨kvec δ ((blockQ p y cl).getD j QRow.zero), kvec δ nq, chal, fun _ => 0⟩
        (envB ((blockB p cl).getD j BRow.zero).col nxt.col) = 0

theorem qSat_append {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))] (p : ℕ) (cl : CallL) (es fs : List (QE F)) :
    QSat (K := K) δ p cl (es ++ fs) ↔ QSat (K := K) δ p cl es ∧ QSat (K := K) δ p cl fs := by
  constructor
  · intro h
    exact ⟨fun y c h1 h2 j hj nxt hn nq hq e he => h y c h1 h2 j hj nxt hn nq hq e (List.mem_append_left _ he),
      fun y c h1 h2 j hj nxt hn nq hq e he => h y c h1 h2 j hj nxt hn nq hq e (List.mem_append_right _ he)⟩
  · rintro ⟨h1, h2⟩ y c hy hp j hj nxt hn nq hq e he
    rcases List.mem_append.mp he with he | he
    · exact h1 y c hy hp j hj nxt hn nq hq e he
    · exact h2 y c hy hp j hj nxt hn nq hq e he

theorem blockIdentSat_iff {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F)
    [Fact (¬ IsSquare (algebraMap F K δ))] (p : ℕ) (cl : CallL) :
    BlockIdentSat (K := K) δ p cl ↔ QSat (K := K) δ p cl (AluSZChipJ9.identQ δ) := Iff.rfl

end Spec

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
