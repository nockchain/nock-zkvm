/-
  NockvmE2E/Exec/VField.lean   (executed, no proofs, Mathlib-free)

  Goldilocks `G = UInt64` (32-bit-limb multiplication, no `Nat` products) and the cubic extension `K3 = G[x]/(x^3-7)`.
  The multiplication/inverse formulas are the same text as `Exec/ProverField.lean` (`PF`) and `Exec/Field.lean` `K3`
  (`c0*d0 + 7(c1 d2 + c2 d1)`, ...).  The link to `Field.lean`'s `Gold`/`K3` is a later proof-side file (`VLink`).
-/
set_option autoImplicit false

namespace NockvmE2E.Exec.VF

abbrev G := UInt64
def P : UInt64 := 0xFFFFFFFF00000001
def EPS : UInt64 := 0xFFFFFFFF
def PN : Nat := 18446744069414584321

@[inline] def add (a b : G) : G :=
  let s := a + b
  let s := if s < a then s + EPS else s
  if s ≥ P then s - P else s
@[inline] def sub (a b : G) : G := if a ≥ b then a - b else (a - b) - EPS
@[inline] def neg (a : G) : G := if a == 0 then 0 else P - a
@[inline] def mul (a b : G) : G :=
  let a0 := a &&& EPS
  let a1 := a >>> 32
  let b0 := b &&& EPS
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := p01 + p10
  let midc : UInt64 := if mid < p01 then 1 else 0
  let lo := p00 + (mid <<< 32)
  let loc : UInt64 := if lo < p00 then 1 else 0
  let hi := p11 + (mid >>> 32) + (midc <<< 32) + loc
  let hh := hi >>> 32
  let hl := hi &&& EPS
  let t0 := if lo < hh then (lo - hh) - EPS else lo - hh
  let t1 := hl * EPS
  let r := t0 + t1
  let r := if r < t0 then r + EPS else r
  if r ≥ P then r - P else r

/-- square-and-multiply by structural recursion on a fuel (`powAux f b k r = r * b^k` when `k ≤ f`); each step halves `k`. -/
def powAux : Nat → G → Nat → G → G
  | 0, _, _, r => r
  | f + 1, b, k, r => if k == 0 then r else powAux f (mul b b) (k / 2) (if k % 2 == 1 then mul r b else r)
def pow (a : G) (e : Nat) : G := powAux (e + 1) a e 1
def inv (a : G) : G := pow a (PN - 2)
def seven : G := 7
/-- `x < p` -/
def based (x : Nat) : Bool := x < PN

structure K3 where
  c0 : G
  c1 : G
  c2 : G
  deriving Inhabited, BEq

namespace K3
def zero : K3 := ⟨0, 0, 0⟩
def one : K3 := ⟨1, 0, 0⟩
/-- the generator `x` -/
def gen : K3 := ⟨0, 1, 0⟩
@[inline] def ofG (x : G) : K3 := ⟨x, 0, 0⟩
@[inline] def add (x y : K3) : K3 := ⟨VF.add x.c0 y.c0, VF.add x.c1 y.c1, VF.add x.c2 y.c2⟩
@[inline] def sub (x y : K3) : K3 := ⟨VF.sub x.c0 y.c0, VF.sub x.c1 y.c1, VF.sub x.c2 y.c2⟩
@[inline] def neg (x : K3) : K3 := ⟨VF.neg x.c0, VF.neg x.c1, VF.neg x.c2⟩
@[inline] def smul (s : G) (x : K3) : K3 := ⟨VF.mul s x.c0, VF.mul s x.c1, VF.mul s x.c2⟩
@[inline] def mul (x y : K3) : K3 :=
  ⟨VF.add (VF.mul x.c0 y.c0) (VF.mul seven (VF.add (VF.mul x.c1 y.c2) (VF.mul x.c2 y.c1))),
   VF.add (VF.add (VF.mul x.c0 y.c1) (VF.mul x.c1 y.c0)) (VF.mul seven (VF.mul x.c2 y.c2)),
   VF.add (VF.add (VF.mul x.c0 y.c2) (VF.mul x.c1 y.c1)) (VF.mul x.c2 y.c0)⟩
def adj (x : K3) : K3 :=
  ⟨VF.sub (VF.mul x.c0 x.c0) (VF.mul seven (VF.mul x.c1 x.c2)),
   VF.sub (VF.mul seven (VF.mul x.c2 x.c2)) (VF.mul x.c0 x.c1),
   VF.sub (VF.mul x.c1 x.c1) (VF.mul x.c0 x.c2)⟩
def norm (x : K3) : G :=
  let A := adj x
  VF.add (VF.mul x.c0 A.c0) (VF.mul seven (VF.add (VF.mul x.c1 A.c2) (VF.mul x.c2 A.c1)))
/-- inverse; `inv 0 = 0` (callers test for zero where it matters) -/
def inv (x : K3) : K3 := smul (VF.inv (norm x)) (adj x)
def powAux : Nat → K3 → Nat → K3 → K3
  | 0, _, _, r => r
  | f + 1, b, k, r => if k == 0 then r else powAux f (mul b b) (k / 2) (if k % 2 == 1 then mul r b else r)
def pow (x : K3) (e : Nat) : K3 := powAux (e + 1) x e one
def isZero (x : K3) : Bool := x.c0 == 0 && x.c1 == 0 && x.c2 == 0
def isBase (x : K3) : Bool := x.c1 == 0 && x.c2 == 0
def limbs (x : K3) : List Nat := [x.c0.toNat, x.c1.toNat, x.c2.toNat]
def ofLimbs (l : List Nat) : K3 :=
  ⟨UInt64.ofNat (l.getD 0 0), UInt64.ofNat (l.getD 1 0), UInt64.ofNat (l.getD 2 0)⟩
/-- Horner evaluation of a `K3`-coefficient polynomial at a `K3` point (highest coefficient first) -/
def horner (coef : Array K3) (z : K3) : K3 :=
  coef.toList.foldr (fun c acc => add (mul acc z) c) zero
/-- Horner evaluation of a base-coefficient polynomial at a `K3` point -/
def hornerG (coef : Array G) (z : K3) : K3 :=
  coef.toList.foldr (fun c acc => add (mul acc z) (ofG c)) zero
end K3

end NockvmE2E.Exec.VF
