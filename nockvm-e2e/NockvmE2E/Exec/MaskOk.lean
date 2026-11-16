/-
  NockvmE2E/Exec/MaskOk.lean   (`hcur1` of the tie; Mathlib-free, total)

  `maskOk X`: for every table `t` of a J-8 chip other than the jet (whose registry columns stay TCB) and every preprocessed column `c ∈ preIdxJ8 id`
  (position `pos`), the coefficient array `pre[col0 + c]` has fewer than `hN_t` coefficients and its evaluations at the nodes `hGen^i`, `i < hN_t`, are the 0/1 pattern:
    pos 0 (firstRowMask):  i = 0;      pos 1 (lastRowMask):  i = hN_t - 1;      pos 2 (rootRowMask, walk chips):  i < kroots  (kroots := number of leading 1s; the rest 0).
  A polynomial of degree < hN_t is determined by its values at the hN_t distinct nodes (Lagrange: `eq_interpolate_of_eval_eq`), so `pre` IS the interpolant of the mask, i.e. nock's
  `firstRowMask` / `lastRowMask` / `rootRowMaskW`.  O(hN_t^2) field multiplications per column.
  `hop0Check X`: `chipsOk` (J8Chips) + `maskOk` + the numeral of each walk chip literal equals the `kroots` the root mask carries.
-/
import NockvmE2E.Exec.J8Chips
import NockvmE2E.Exec.J8ShapeB
set_option autoImplicit false

namespace NockvmE2E.Exec.MaskOk
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VF NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8Shape

/-- Horner evaluation of a coefficient array -/
def hor (x : G) : List G → G
  | [] => 0
  | c :: cs => VF.add (VF.mul (hor x cs) x) c

def peval (p : Array G) (x : G) : G := hor x p.toList

/-- `evalNodesAux p g k x acc`: push the values of `p` at `x, x·g, …, x·g^(k-1)` (structural; proved against `eval` in `MaskOkK`) -/
def evalNodesAux (p : Array G) (g : G) : Nat → G → Array G → Array G
  | 0, _, acc => acc
  | k + 1, x, acc => evalNodesAux p g k (VF.mul x g) (acc.push (peval p x))

/-- the values of `p` at `1, g, g², …, g^(n-1)` -/
def evalNodes (p : Array G) (g : G) (n : Nat) : Array G := evalNodesAux p g n 1 (Array.mkEmpty n)

/-- the 0/1 pattern `1^k 0^(n-k)` -/
def rootPat (n k : Nat) : Array G := (Array.range n).map (fun i => if i < k then (1 : G) else 0)

/-- last-row pattern -/
def lastPat (n : Nat) : Array G := (Array.range n).map (fun i => if i + 1 == n then (1 : G) else 0)

/-- number of leading ones; `none` unless the values are `1^k 0^(n-k)` (`k` = the number of ones) -/
def leadingOnes (v : Array G) : Option Nat :=
  let k := (v.toList.filter (· == 1)).length
  if v == rootPat v.size k then some k else none

/-- one mask column: `some kroots` (`0` for positions 0, 1) when its values are the pattern -/
def maskCol (X : ExecInst) (n : Nat) (pos : Nat) (p : Array G) : Option Nat :=
  if p.size > n then none else
  let v := evalNodes p X.hGen n
  if pos == 0 then (if v == rootPat n 1 then some 0 else none)
  else if pos == 1 then (if v == lastPat n then some 0 else none)
  else leadingOnes v

/-- the `kroots` of a table (`some 0` for non-walk tables), or `none` if some mask column is not the pattern; the jet is skipped -/
def tabMask (X : ExecInst) (t : TabInst) : Option Nat :=
  if t.chip.id == "jetChipJ8" then some 0 else
  (preIdxJ8 t.chip.id).toList.zipIdx.foldl (fun acc (c, pos) =>
    match acc, maskCol X t.hN pos (X.pre.getD (t.col0 + c) #[]) with
    | some a, some k => some (max a k)
    | _, _ => none) (some 0)

def maskOk (X : ExecInst) : Bool := X.tabs.all fun t => (tabMask X t).isSome

/-- numeral of a walk chip literal = the kroots of its root mask -/
def numeralOk (X : ExecInst) : Bool := X.tabs.all fun t =>
  if t.chip.id == "walkChipJ8" || t.chip.id == "walkChipHQK" then
    (chipNumeral t.chip).isSome && chipNumeral t.chip == tabMask X t
  else true

/-- the whole hop-0 + `hcur1` exe check, with a REJECT reason -/
def hop0Check (X : ExecInst) : Except String Unit :=
  if !chipsOk X then .error "a loaded chip is not the emitted J-8 chip (hop 0)"
  else if !maskOk X then .error "a preprocessed mask column is not the first/last/root-row pattern (hcur1)"
  else if !numeralOk X then .error "a walk chip's numeral differs from its root-mask kroots"
  else .ok ()

end NockvmE2E.Exec.MaskOk
