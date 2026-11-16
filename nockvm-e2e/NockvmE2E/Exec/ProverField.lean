/-
  NockvmE2E/Exec/ProverField.lean   (untrusted, executed, no proofs)

  Raw `UInt64` Goldilocks (`F`) with a 32-bit-limb multiplication (no `Nat`), the cubic extension `E3 = F[x]/(x^3-7)`
  (same multiplication formula as `Exec/Field.lean` `K3.mul`), and an array NTT.  Mathlib-free on purpose (see Tip5Core.lean).
  The self-test in ProverMain compares `mul` with `Nat` arithmetic and the NTT with a naive DFT.
-/
set_option autoImplicit false

namespace NockvmE2E.Exec.PF

abbrev F := UInt64
def P : UInt64 := 0xFFFFFFFF00000001
def EPS : UInt64 := 0xFFFFFFFF

@[inline] def add (a b : F) : F :=
  let s := a + b
  let s := if s < a then s + EPS else s
  if s ≥ P then s - P else s

@[inline] def sub (a b : F) : F := if a ≥ b then a - b else (a - b) - EPS

@[inline] def neg (a : F) : F := if a == 0 then 0 else P - a

/-- `a*b mod p` via 32-bit limbs and `2^64 ≡ 2^32-1`, `2^96 ≡ -1`. -/
@[inline] def mul (a b : F) : F :=
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

def pow (a : F) (e : Nat) : F := Id.run do
  let mut r : F := 1
  let mut b := a
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := mul r b
    b := mul b b
    k := k / 2
  return r

def inv (a : F) : F := pow a (P.toNat - 2)

def seven : F := 7

/-- A primitive `2^k`-th root of unity (`Exec/Field.lean` `NTT.root`): `(7^(2^32-1))^(2^(32-k))`. -/
def root (k : Nat) : F := pow (pow seven (2 ^ 32 - 1)) (2 ^ (32 - k))

/-! ### the cubic extension -/

structure E3 where
  a : F
  b : F
  c : F
  deriving Inhabited, BEq

namespace E3
def zero : E3 := ⟨0, 0, 0⟩
def one : E3 := ⟨1, 0, 0⟩
@[inline] def ofF (x : F) : E3 := ⟨x, 0, 0⟩
@[inline] def add (x y : E3) : E3 := ⟨PF.add x.a y.a, PF.add x.b y.b, PF.add x.c y.c⟩
@[inline] def sub (x y : E3) : E3 := ⟨PF.sub x.a y.a, PF.sub x.b y.b, PF.sub x.c y.c⟩
@[inline] def neg (x : E3) : E3 := ⟨PF.neg x.a, PF.neg x.b, PF.neg x.c⟩
@[inline] def smul (s : F) (x : E3) : E3 := ⟨PF.mul s x.a, PF.mul s x.b, PF.mul s x.c⟩
@[inline] def mul (x y : E3) : E3 :=
  ⟨PF.add (PF.mul x.a y.a) (PF.mul seven (PF.add (PF.mul x.b y.c) (PF.mul x.c y.b))),
   PF.add (PF.add (PF.mul x.a y.b) (PF.mul x.b y.a)) (PF.mul seven (PF.mul x.c y.c)),
   PF.add (PF.add (PF.mul x.a y.c) (PF.mul x.b y.b)) (PF.mul x.c y.a)⟩
def adj (x : E3) : E3 :=
  ⟨PF.sub (PF.mul x.a x.a) (PF.mul seven (PF.mul x.b x.c)),
   PF.sub (PF.mul seven (PF.mul x.c x.c)) (PF.mul x.a x.b),
   PF.sub (PF.mul x.b x.b) (PF.mul x.a x.c)⟩
def norm (x : E3) : F :=
  let A := adj x
  PF.add (PF.mul x.a A.a) (PF.mul seven (PF.add (PF.mul x.b A.c) (PF.mul x.c A.b)))
def inv (x : E3) : E3 := smul (PF.inv (norm x)) (adj x)
def pow (x : E3) (e : Nat) : E3 := Id.run do
  let mut r : E3 := one
  let mut b := x
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then r := mul r b
    b := mul b b
    k := k / 2
  return r
/-- the generator `x` of `E3` over `F` -/
def gen : E3 := ⟨0, 1, 0⟩
def gen2 : E3 := ⟨0, 0, 1⟩
def isBase (x : E3) : Bool := x.b == 0 && x.c == 0
def limbs (x : E3) : List Nat := [x.a.toNat, x.b.toNat, x.c.toNat]
end E3

/-! ### NTT -/

/-- `ntt a logn w`: entry `j` is `Σ_i a[i] w^(i j)` for `w` of order `2^logn` (iterative radix-2, in place). -/
def ntt (a0 : Array F) (logn : Nat) (w : F) : Array F := Id.run do
  let n := 2 ^ logn
  let mut a := a0
  let mut j := 0
  for i in [1:n] do
    let mut bit := n >>> 1
    while j &&& bit != 0 do
      j := j ^^^ bit
      bit := bit >>> 1
    j := j ^^^ bit
    if i < j then
      let t := a[i]!
      a := a.set! i a[j]!
      a := a.set! j t
  let mut tw : Array F := Array.mkEmpty (n / 2 + 1)
  let mut cur : F := 1
  for _ in [0:n / 2 + 1] do
    tw := tw.push cur
    cur := mul cur w
  let mut len := 2
  while len ≤ n do
    let half := len / 2
    let step := n / len
    let mut i := 0
    while i < n do
      for k in [0:half] do
        let u := a[i + k]!
        let v := mul a[i + k + half]! tw[k * step]!
        a := a.set! (i + k) (add u v)
        a := a.set! (i + k + half) (sub u v)
      i := i + len
    len := len * 2
  return a

/-- values on `<w>` (order `2^logn`) ↦ coefficients. -/
def intt (a : Array F) (logn : Nat) (w : F) : Array F :=
  let n := 2 ^ logn
  let ninv := inv (n.toUInt64)
  (ntt a logn (inv w)).map (mul ninv ·)

/-- coefficients (length `2^lh`) ↦ values on the coset `7·<g>` of size `2^ld` (`g` of order `2^ld`). -/
def cosetLde (coef : Array F) (ld : Nat) (g : F) : Array F := Id.run do
  let n := 2 ^ ld
  let mut a : Array F := Array.mkEmpty n
  let mut s : F := 1
  for i in [0:n] do
    if i < coef.size then
      a := a.push (mul coef[i]! s)
      s := mul s seven
    else a := a.push 0
  return ntt a ld g

/-- Horner evaluation of a base-coefficient polynomial at an `E3` point. -/
def horner (coef : Array F) (z : E3) : E3 := Id.run do
  let mut acc : E3 := E3.zero
  for i in [0:coef.size] do
    let c := coef[coef.size - 1 - i]!
    acc := E3.add (E3.mul acc z) (E3.ofF c)
  return acc

end NockvmE2E.Exec.PF
