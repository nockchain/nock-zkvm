/-
  NockvmE2E/Exec/VKSpecExe.lean   (pcs (b),  section 2; executed, Mathlib-free, no proofs)

  The SPEC verifier key `vkSpec X Hf`: a total, loop-free, `partial`-free description of what `setup' X Hf` is supposed to compute.
    * fixed columns = `fixCols X` (pre columns, Z_H, one Zout per short table);
    * the committed word of column `j` at FRI-domain index `i` is the value of the column polynomial at `dShift * dGen^i`, evaluated
      by the base-field formulas of `verifyFlatE` (`hornerB`: Horner on the instance's coefficients; `zhG`/`zoutG`: the products);
    * the tree is the rag tree of `fxRagLevels` written as a structural recursion on a fuel (`specSub`, `specTop`).
  The kernel side (VKSpec.lean) proves these evaluate to the polynomials `f_j` and links them to `fixTrue`.  The deployed `setup'` (NTT,
  `while`, `partial`) is NOT proved equal to this; `specRootCheck`/`main` below run the comparison on real instances.
-/
import NockvmE2E.Exec.VKp
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J

/-- the instance-erased `X` (as in `setup`) -/
def eraseXS (X : ExecInst) : ExecInst := { X with pre := X.pre.map (fun _ => #[]) }

/-- Horner evaluation of a base-coefficient list at a base point, low coefficient first (the `G` shadow of `K3.hornerG`) -/
def hornerB (l : List G) (x : G) : G := l.foldr (fun c acc => VF.add (VF.mul acc x) c) 0

/-- `∏_{i<n} (x - start·hGen^i)` together with the running orbit point (the `G` shadow of `zhEval`/`zoutEval`) -/
def prodLinG (hGen x start : G) (n : Nat) : G × G :=
  (List.range n).foldl (fun (st : G × G) _ => (VF.mul st.1 (VF.sub x st.2), VF.mul st.2 hGen)) (1, start)

def zhG (X : ExecInst) (x : G) : G := (prodLinG X.hGen x X.hShift X.hN).1

def zoutG (X : ExecInst) (hNt : Nat) (x : G) : G :=
  (prodLinG X.hGen x (VF.mul X.hShift (VF.pow X.hGen hNt)) (X.hN - hNt)).1

/-- the spec value of fixed column `col` at the base point `x` -/
def colG (X : ExecInst) : FixCol → G → G
  | .pre c, x => hornerB X.pre[c]!.toList x
  | .zh, x => zhG X x
  | .zout t, x => zoutG X (tabHN X t) x

/-- the FRI-domain point of index `i`: `dShift * dGen^i` -/
def domPt (X : ExecInst) (i : Nat) : G := VF.mul X.dShift (VF.pow X.dGen i)

/-- the committed word of fixed column `col` at FRI-domain index `i` -/
def specWord (X : ExecInst) (col : FixCol) (i : Nat) : G := colG X col (domPt X i)

/-- root of the rag subtree over the `cnt` columns `lo ..` (the spec of `fxSubRoot`; fuel `≥ cnt`) -/
def specSub (Hf : HFn) (leafAt : Nat → G) : Nat → Nat → Nat → Nat → Dg5
  | 0, _, _, _ => []
  | f + 1, idx, cnt, lo =>
    if cnt == 1 then [(leafAt lo).toNat, 0, 0, 0, 0] else
    let L := (cnt + 1) / 2
    Hf ([tagNode, 0, idx] ++ specSub Hf leafAt f (2 * idx) L lo ++ specSub Hf leafAt f (2 * idx + 1) (cnt - L) (lo + L))

/-- the group node `half + g` of the rag tree: two column-subtrees (positions `g` and `g + half`) -/
def specGroup (X : ExecInst) (Hf : HFn) (cols : Array FixCol) (half g : Nat) : Dg5 :=
  let side (s : Nat) : Dg5 :=
    specSub Hf (fun r => specWord X cols[r]! (g + s * half)) cols.size (2 * (half + g) + s) cols.size 0
  Hf ([tagNode, 0, half + g] ++ side 0 ++ side 1)

/-- heap node `idx` of the top tree (fuel = levels left above the group level `2^m`) -/
def specTop (Hf : HFn) (grp : Nat → Dg5) (m : Nat) : Nat → Nat → Dg5
  | 0, idx => grp (idx - 2 ^ m)
  | f + 1, idx => Hf ([tagNode, 0, idx] ++ specTop Hf grp m f (2 * idx) ++ specTop Hf grp m f (2 * idx + 1))

def specRoot (X : ExecInst) (Hf : HFn) : Dg5 :=
  let cols := fixCols X
  let m := X.nD - 1
  specTop Hf (specGroup X Hf cols (2 ^ m)) m m 1

/-- **the spec VK** (total; no gates: `setup'` adds the gates) -/
def vkSpec (X : ExecInst) (Hf : HFn) : VK :=
  { X := eraseXS X, cols := fixCols X, root := specRoot X Hf }

/-- the executed check: the deployed `setup'` returns exactly the spec VK's data (root, columns, erased instance root-relevant fields) -/
def specRootCheck (X : ExecInst) (Hf : HFn) : Bool :=
  match setup' X Hf with
  | none => false
  | some vk => vk.root == (vkSpec X Hf).root && vk.cols == (vkSpec X Hf).cols

end NockvmE2E.Exec.V
