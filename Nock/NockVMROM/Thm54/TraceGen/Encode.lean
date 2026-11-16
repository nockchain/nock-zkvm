/-
  Nock/NockVMROM/Thm54/TraceGen/Encode.lean

  A COMPUTABLE mirror of the NPR fingerprint
  `GlobalCarryRecognizer.enc`, which is `noncomputable` because it routes through
  Mathlib `Polynomial.eval` (`Polynomial` is `Finsupp`-backed).  The mirror `encC`
  evaluates the coefficient lists `NPR.dyckBits`/`NPR.leafF` by a little-endian Horner
  fold `hornerLE`, and `encC_eq` proves it equals `enc` at every seed, so downstream
  `#eval` / executable checking can use `encC` while every proof continues to cite `enc`.

  The fold MUST be `foldr`-shaped (constant term outermost): `NPR.listPoly` is
  little-endian (`NPR.listPoly_coeff`), so `hornerLE z l = (NPR.listPoly l).eval z`.
  A `foldl` would evaluate the reversed polynomial and `hornerLE_eq_eval` would be false.
-/
import Nock.NPR
import Nock.ComputeTable
import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Polynomial

variable {K : Type*} [Field K]

/-- Little-endian Horner evaluation of a dense coefficient list: `Σ_i l[i] · z^i`,
    computed constant-term-outermost.  Computable twin of `(NPR.listPoly l).eval z`. -/
def hornerLE (z : K) : List K → K
  | [] => 0
  | a :: l => a + z * hornerLE z l

@[simp] theorem hornerLE_nil (z : K) : hornerLE z ([] : List K) = 0 := rfl

@[simp] theorem hornerLE_cons (z a : K) (l : List K) :
    hornerLE z (a :: l) = a + z * hornerLE z l := rfl

/-- The Horner fold agrees with evaluating the little-endian `NPR.listPoly`. -/
theorem hornerLE_eq_eval (z : K) (l : List K) :
    hornerLE z l = (NPR.listPoly l).eval z := by
  induction l with
  | nil => simp [NPR.listPoly_nil]
  | cons a l ih =>
      rw [hornerLE_cons, NPR.listPoly_cons, eval_add, eval_C, eval_mul, eval_X, ih]

/-- **Computable NPR fingerprint** in field order `(size, dyck, leaf)`.  Field-order computable twin of
    `GlobalCarryRecognizer.enc`; computable because it avoids `Polynomial`. -/
def encC (z : K) (n : Noun) : ComputeTable.FP K where
  size := z ^ n.leaves
  dyck := hornerLE z (NPR.dyckBits n)
  leaf := hornerLE z (NPR.leafF n)

@[simp] theorem encC_size (z : K) (n : Noun) : (encC z n).size = z ^ n.leaves := rfl

@[simp] theorem encC_dyck (z : K) (n : Noun) :
    (encC z n).dyck = hornerLE z (NPR.dyckBits n) := rfl

@[simp] theorem encC_leaf (z : K) (n : Noun) :
    (encC z n).leaf = hornerLE z (NPR.leafF n) := rfl

/-- `encC` agrees with the noncomputable `GlobalCarryRecognizer.enc` at every seed and
    noun; the executable path uses `encC`, every proof continues to cite `enc`. -/
theorem encC_eq (z : K) (n : Noun) :
    encC z n = GlobalCarryRecognizer.enc z n := by
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · rw [encC_size, GlobalCarryRecognizer.enc_size]
  · rw [encC_dyck, GlobalCarryRecognizer.enc_dyck, hornerLE_eq_eval]
  · rw [encC_leaf, GlobalCarryRecognizer.enc_leaf, hornerLE_eq_eval]

end Nock.NockVMROM.Thm54.TraceGen
