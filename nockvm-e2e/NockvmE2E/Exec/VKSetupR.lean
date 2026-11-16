/-
  NockvmE2E/Exec/VKSetupR.lean   (HSpec, ; executed, Mathlib-free, no proofs)

  Total, structurally recursive replacements for the setup arithmetic of `VK.lean`, so that `setup'` can be reasoned about in the kernel:
  a recursive radix-2 NTT (`nttR`, the text of `Field.lean` `NTT.ntt` over `VF`), the coset LDE on it (`cosetLdeR`, same output as
  `PF.cosetLde`, including the drop of coefficients past `2^ld`), and the linear-factor product `prodLinR` (same output as the old
  subproduct tree `prodLin`: the unique monic polynomial, canonical coefficients).
-/
import NockvmE2E.Exec.VField
import NockvmE2E.Exec.Verify
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF

def evensG : List G → List G
  | [] => [] | [a] => [a] | a :: _ :: t => a :: evensG t
def oddsG : List G → List G
  | [] => [] | [_] => [] | _ :: b :: t => b :: oddsG t

/-- recursive radix-2 NTT (the text of `Field.lean` `NTT.ntt`, over `VF`): entry `j` = Σ_i a_i w^(ij), `w` of order `2^k` -/
def nttR : Nat → G → List G → List G
  | 0, _, a => a
  | k + 1, w, a =>
    let e := nttR k (VF.mul w w) (evensG a)
    let o := nttR k (VF.mul w w) (oddsG a)
    let t := List.zipWith VF.mul ((List.range (2 ^ k)).map (VF.pow w ·)) o   -- NOT o.getD j (List.getD is O(j))
    List.zipWith VF.add e t ++ List.zipWith VF.sub e t

/-- values on `7·<g>` (size `2^ld`); same output as `PF.cosetLde`, including the drop of coefficients past `2^ld` -/
def cosetLdeR (coef : Array G) (ld : Nat) (g : G) : Array G :=
  (nttR ld g ((List.range (2 ^ ld)).map fun i => if i < coef.size then VF.mul coef[i]! (VF.pow VF.seven i) else 0)).toArray

/-- `a · (X - h)`, low coefficient first -/
def mulLin (a : Array G) (h : G) : Array G :=
  (Array.range (a.size + 1)).map fun i =>
    VF.sub (if i == 0 then 0 else a[i - 1]!) (VF.mul h (if i < a.size then a[i]! else 0))

/-- `∏_{i ∈ [lo, hi)} (X - pts[i])`, monic, O((hi-lo)^2) -/
def prodLinR (pts : Array G) (lo hi : Nat) : Array G :=
  (List.range' lo (hi - lo)).foldl (fun a i => mulLin a pts[i]!) #[1]

end NockvmE2E.Exec.V
