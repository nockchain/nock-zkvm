/-
  Nock/NockVMROM/Thm54/P8Core/Batch1542Thm54T0TowerFP.lean

  **The parallel fingerprint objects over `𝕂′ = 𝕂(√δ)`.**
  `FP` / `NPR.fn` / `FP.cons` (`ComputeTable.lean`, `NPR.lean`) are
  NOT touched and keep their types; the tower objects have NEW names:

  * `FP2 K` — a fingerprint over `𝕂′` stored as `𝕂`-coordinates, `(Re, Im)` per slot (the
    column-level carrier: every noun slot is 6 `𝕂`-roles);
  * `FP2.toFP` / `FP2.ofFP` — the identification with `FP (Quad δ)` (the generic structure at the
    field `𝕂′`), `fn2` — `NPR.fn` at a seed `z′ ∈ 𝕂′` in coordinates, `FP2.cons` — `FP.cons`;
  * `fn2_cons`, `fn2_atom` — the NPR decomposition `Lem:NPR_decomp` at 𝕂′,
    transported from `GlobalCarryRecognizer.enc_cons` / `enc_atom` (field-generic);
  * the GATES: `Q F = MixedExpr F × MixedExpr F` is a `𝕂′`-valued expression as a `(Re, Im)` pair of
    `𝕂`-valued `MixedExpr`s whose only base-field datum is the constant `δ ∈ 𝔽`
    (`.Scale (.const δ)`).  `qmul` encodes `(a+b√δ)(c+d√δ) = (ac+δbd) + (ad+bc)√δ` (`qmul_val`).
    `consSize` / `consLeaf` / `consDyck` are `Φ₁` / `Φ₂` / `Φ₃`; `cons_gates_iff` says the six `𝕂`-equations hold iff the memory record is `FP.cons`
    of its children (soundness and completeness of the gate pair, `cons_gates_of_enc`);
  * the existing finrank-3 compiler (`mixedCompile`, `hK` untouched): `gate_zero_iff_compiled`
    and `gate_compiled_degree_le`, plus the exact degrees `consSize_degree = 2`,
    `consLeaf_degree = 2`, `consDyck_degree = 3`, `prov_consDyck_degree = 4`, `atomTest_degree = 2`.

  Column layout used for the degree figures is the probe's memory layout (re at `base`, `base+1`,
  `base+2`, im at `base'`, …); the theorems about values and zero-sets are role-generic.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54.T0TowerFP

open Nock Nock.Reified Nock.ComputeTable Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.CoordinateCompiler

/-! ## `FP2`: fingerprints over `𝕂′` as `𝕂`-coordinate pairs -/

/-- A `𝕂′`-fingerprint triple `(size′, dyck′, leaf′)`, each slot a `(Re, Im)` pair over `𝕂`. -/
structure FP2 (K : Type*) where
  size : K × K
  dyck : K × K
  leaf : K × K

namespace FP2

section Pairs
variable {K : Type} [Field K] (δ : K)

/-- `𝕂′`-arithmetic on coordinate pairs. -/
def padd (a b : K × K) : K × K := (a.1 + b.1, a.2 + b.2)
def pmul (a b : K × K) : K × K := (a.1 * b.1 + δ * (a.2 * b.2), a.1 * b.2 + a.2 * b.1)
def pinv (a : K × K) : K × K :=
  (a.1 / (a.1 * a.1 - δ * (a.2 * a.2)), -a.2 / (a.1 * a.1 - δ * (a.2 * a.2)))

theorem mk_padd (a b : K × K) : Quad.mk δ (padd a b).1 (padd a b).2 =
    Quad.mk δ a.1 a.2 + Quad.mk δ b.1 b.2 := by
  simp [padd, Quad.mk_add]

theorem mk_pmul (a b : K × K) : Quad.mk δ (pmul δ a b).1 (pmul δ a b).2 =
    Quad.mk δ a.1 a.2 * Quad.mk δ b.1 b.2 := by
  simp [pmul, Quad.mk_mul]

theorem mk_pinv [Fact (¬ IsSquare δ)] (a : K × K) (ha : a ≠ 0) :
    Quad.mk δ (pinv δ a).1 (pinv δ a).2 = (Quad.mk δ a.1 a.2)⁻¹ := by
  rw [Quad.mk_inv δ a.1 a.2 (fun h => ha (Prod.ext h.1 h.2))]
  rfl

end Pairs

section Maps
variable {K : Type} [Field K] (δ : K)

/-- `FP2 K → FP 𝕂′`. -/
noncomputable def toFP (x : FP2 K) : FP (Quad δ) :=
  ⟨Quad.mk δ x.size.1 x.size.2, Quad.mk δ x.dyck.1 x.dyck.2, Quad.mk δ x.leaf.1 x.leaf.2⟩

/-- `FP 𝕂′ → FP2 K`. -/
noncomputable def ofFP [Fact (¬ IsSquare δ)] [Fintype K] (x : FP (Quad δ)) : FP2 K :=
  ⟨(Quad.re δ x.size, Quad.im δ x.size), (Quad.re δ x.dyck, Quad.im δ x.dyck),
    (Quad.re δ x.leaf, Quad.im δ x.leaf)⟩

theorem toFP_ofFP [Fact (¬ IsSquare δ)] [Fintype K] (x : FP (Quad δ)) :
    toFP δ (ofFP δ x) = x := by
  simp [toFP, ofFP, Quad.mk_re_im]

theorem ofFP_toFP [Fact (¬ IsSquare δ)] [Fintype K] (x : FP2 K) :
    ofFP δ (toFP δ x) = x := by
  simp [toFP, ofFP, Quad.re_mk, Quad.im_mk]

theorem toFP_injective [Fact (¬ IsSquare δ)] [Fintype K] : Function.Injective (toFP δ) :=
  Function.LeftInverse.injective (ofFP_toFP δ)

/-- `FP.cons` in coordinates. -/
def cons (z : K × K) (a b : FP2 K) : FP2 K :=
  ⟨pmul δ a.size b.size,
   padd (padd (pmul δ z a.dyck) (pmul δ (pmul δ a.size a.size) (pinv δ z)))
     (pmul δ (pmul δ a.size a.size) b.dyck),
   padd a.leaf (pmul δ a.size b.leaf)⟩

/-- **`cons` in coordinates is `FP.cons` at `𝕂′`.** -/
theorem toFP_cons [Fact (¬ IsSquare δ)] (z : K × K) (hz : z ≠ 0) (a b : FP2 K) :
    toFP δ (cons δ z a b) = FP.cons (Quad.mk δ z.1 z.2) (toFP δ a) (toFP δ b) := by
  simp only [toFP, cons, FP.cons, mk_padd, mk_pmul, mk_pinv δ z hz]

/-- The atom fingerprint `(z′, 0, v′)`. -/
def atom (z v : K × K) : FP2 K := ⟨z, (0, 0), v⟩

theorem toFP_atom [Fact (¬ IsSquare δ)] (z v : K × K) :
    toFP δ (atom z v) = FP.atomFP (Quad.mk δ z.1 z.2) (Quad.mk δ v.1 v.2) := by
  simp [toFP, atom, FP.atomFP, Quad.mk_zero']

end Maps

end FP2

/-! ## `fn2`: the NPR fingerprint at a seed in `𝕂′` -/

section Fn2
variable {K : Type} [Field K] [Fintype K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **`fn` at the tower.**  `fn2 n z′` is `GlobalCarryRecognizer.enc z′ n = (z′^λ, F_w(z′), F_d(z′))`
(the `NPR.fn` triple in `FP` order) at the seed `z′ = z₁ + z₂√δ`, read in `𝕂`-coordinates. -/
noncomputable def fn2 (n : Noun) (z : K × K) : FP2 K :=
  FP2.ofFP δ (GlobalCarryRecognizer.enc (Quad.mk δ z.1 z.2) n)

theorem toFP_fn2 (n : Noun) (z : K × K) :
    FP2.toFP δ (fn2 δ n z) = GlobalCarryRecognizer.enc (Quad.mk δ z.1 z.2) n :=
  FP2.toFP_ofFP δ _

/-- `fn2` is `NPR.fn` at `𝕂′`, coordinatewise (size, leaf, dyck). -/
theorem toFP_fn2_eq_fn (n : Noun) (z : K × K) :
    FP2.toFP δ (fn2 δ n z) =
      ⟨(NPR.fn n (Quad.mk δ z.1 z.2)).1, (NPR.fn n (Quad.mk δ z.1 z.2)).2.2,
        (NPR.fn n (Quad.mk δ z.1 z.2)).2.1⟩ := by
  rw [toFP_fn2, GlobalCarryRecognizer.enc_eq_fn]

/-- **`Lem:NPR_decomp` at the tower**: `fn2 (cell x y) = FP2.cons (fn2 x) (fn2 y)` at a nonzero
seed. -/
theorem fn2_cons {z : K × K} (hz : z ≠ 0) (x y : Noun) :
    fn2 δ (Noun.cell x y) z = FP2.cons δ z (fn2 δ x z) (fn2 δ y z) := by
  apply FP2.toFP_injective δ
  have hz' : Quad.mk δ z.1 z.2 ≠ 0 := fun h => hz (Prod.ext
    ((Quad.mk_eq_zero_iff δ _ _).mp h).1 ((Quad.mk_eq_zero_iff δ _ _).mp h).2)
  rw [FP2.toFP_cons δ z hz, toFP_fn2, toFP_fn2, toFP_fn2,
    GlobalCarryRecognizer.enc_cons hz']

theorem fn2_atom (z : K × K) (k : ℕ) : fn2 δ (Noun.atom k) z = FP2.atom z ((k : K), 0) := by
  apply FP2.toFP_injective δ
  rw [FP2.toFP_atom, toFP_fn2, GlobalCarryRecognizer.enc_atom]
  congr 1
  simp [Quad.mk, map_natCast]

end Fn2

/-! ## The gates: `𝕂′`-valued expressions as `(Re, Im)` pairs of `MixedExpr` over `𝕂`-roles -/

section Gates
variable (F : Type)

/-- A `𝕂′` value as `(Re, Im)` over `𝕂`-roles. -/
abbrev Q := MixedExpr F × MixedExpr F

def qadd (a b : Q F) : Q F := (.Add a.1 b.1, .Add a.2 b.2)
def qsub (a b : Q F) : Q F := (.Sub a.1 b.1, .Sub a.2 b.2)
/-- `(a+b√δ)(c+d√δ)`, the base constant `δ ∈ 𝔽` as `.Scale (.const δ)`. -/
def qmul (δ : F) (a b : Q F) : Q F :=
  (.Add (.Mul a.1 b.1) (.Scale (.const δ) (.Mul a.2 b.2)), .Add (.Mul a.1 b.2) (.Mul a.2 b.1))
def qsmul (c : CoeffExpr F) (a : Q F) : Q F := (.Scale c a.1, .Scale c a.2)
def qdeg (a : Q F) : ℕ := max a.1.degree a.2.degree

/-- A `𝕂′`-valued column pair: `Re` at role `r`, `Im` at role `r'`. -/
def qcol (r r' : ℕ) : Q F := (.Var .traceCur r, .Var .traceCur r')

/-- A fingerprint over `𝕂′` as three `Q`-roles. -/
structure QFP where
  size : Q F
  dyck : Q F
  leaf : Q F

/-- The fingerprint at columns `re0, re0+1, re0+2` (Re) and `im0, im0+1, im0+2` (Im). -/
def colQFP (re0 im0 : ℕ) : QFP F :=
  ⟨qcol F re0 im0, qcol F (re0 + 1) (im0 + 1), qcol F (re0 + 2) (im0 + 2)⟩

variable (δ : F)

/-- `Φ₁`: `size′_P − size′_L · size′_R`. -/
def consSize (P L R : QFP F) : Q F := qsub F P.size (qmul F δ L.size R.size)
/-- `Φ₂` (`:1222`): `leaf′_P − (leaf′_L + size′_L · leaf′_R)`. -/
def consLeaf (P L R : QFP F) : Q F :=
  qsub F P.leaf (qadd F L.leaf (qmul F δ L.size R.leaf))
/-- `Φ₃` (`:1223`), cleared of `z′⁻¹`:
`z′·dyck′_P − z′²·dyck′_L − size′_L² − z′·size′_L²·dyck′_R`. -/
def consDyck (z : Q F) (P L R : QFP F) : Q F :=
  qsub F (qsub F (qsub F (qmul F δ z P.dyck) (qmul F δ (qmul F δ z z) L.dyck))
      (qmul F δ L.size L.size))
    (qmul F δ z (qmul F δ (qmul F δ L.size L.size) R.dyck))

/-- The seed `z′ = z₁ + z₂√δ`: `z₁` at challenge slot 3 (today's `z`), `z₂` at a new slot 12. -/
def zq : Q F := (.Var .challenge 3, .Var .challenge 12)

/-- The probe layout: memory `pt / lc / rc` fingerprint roles (Re at `0,1,2 | 5,6,7 | 10,11,12`,
Im at `58.. | 61.. | 64..`). -/
def ptQ : QFP F := colQFP F 0 58
def lcQ : QFP F := colQFP F 5 61
def rcQ : QFP F := colQFP F 10 64

def provCol : CoeffExpr F := .var .traceCur 187

theorem consSize_degree : qdeg F (consSize F δ (ptQ F) (lcQ F) (rcQ F)) = 2 := by rfl
theorem consLeaf_degree : qdeg F (consLeaf F δ (ptQ F) (lcQ F) (rcQ F)) = 2 := by rfl
theorem consDyck_degree : qdeg F (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F)) = 3 := by rfl
/-- With the provenance mask (`prov · Φ₃`): degree 4, the paper's transition budget. -/
theorem prov_consDyck_degree :
    qdeg F (qsmul F (provCol F) (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F))) = 4 := by rfl

/-- The atom test `q·(size′ − z′)`: two degree-2 `𝕂`-gates. -/
def atomTest (q : CoeffExpr F) (x : QFP F) : Q F := qsmul F q (qsub F x.size (zq F))
theorem atomTest_degree : qdeg F (atomTest F (.var .traceCur 3) (ptQ F)) = 2 := by rfl

end Gates

/-! ## Semantics: a gate pair is a `𝕂′` value -/

section Semantics
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The `𝕂′` value `a₁ + a₂√δ′` of a `(Re, Im)` pair of `𝕂`-expressions (`δ′ = algebraMap δ`). -/
noncomputable def Q.val (δ : F) (a : Q F) (eK : Env K) (eF : Env F) : Quad (algebraMap F K δ) :=
  Quad.mk _ (a.1.eval eK eF) (a.2.eval eK eF)

/-- The pair is `(0, 0)`: both `𝕂`-equations hold. -/
def Q.IsZero (a : Q F) (eK : Env K) (eF : Env F) : Prop :=
  a.1.eval eK eF = 0 ∧ a.2.eval eK eF = 0

/-- The fingerprint read off three `Q`-roles. -/
noncomputable def QFP.val (δ : F) (x : QFP F) (eK : Env K) (eF : Env F) :
    FP (Quad (algebraMap F K δ)) :=
  ⟨Q.val δ x.size eK eF, Q.val δ x.dyck eK eF, Q.val δ x.leaf eK eF⟩

variable (δ : F) (eK : Env K) (eF : Env F)

theorem Q.isZero_iff [Fact (¬ IsSquare (algebraMap F K δ))] (a : Q F) : Q.IsZero a eK eF ↔ Q.val δ a eK eF = 0 :=
  (Quad.mk_eq_zero_iff _ _ _).symm

theorem qadd_val (a b : Q F) :
    Q.val δ (qadd F a b) eK eF = Q.val δ a eK eF + Q.val δ b eK eF := by
  simp [Q.val, qadd, MixedExpr.eval, Quad.mk_add]

theorem qsub_val (a b : Q F) :
    Q.val δ (qsub F a b) eK eF = Q.val δ a eK eF - Q.val δ b eK eF := by
  simp [Q.val, qsub, MixedExpr.eval, Quad.mk_sub]

/-- **`qmul` is multiplication in `𝕂′`.** -/
theorem qmul_val (a b : Q F) :
    Q.val δ (qmul F δ a b) eK eF = Q.val δ a eK eF * Q.val δ b eK eF := by
  simp [Q.val, qmul, MixedExpr.eval, CoeffExpr.eval, Quad.mk_mul]

theorem qsmul_val (c : CoeffExpr F) (a : Q F) :
    Q.val δ (qsmul F c a) eK eF = algebraMap K (Quad (algebraMap F K δ))
      (algebraMap F K (c.eval eF)) * Q.val δ a eK eF := by
  simp only [Q.val, qsmul, MixedExpr.eval]
  exact (Quad.mk_smul _ _ _ _).symm

theorem consSize_val (P L R : QFP F) :
    Q.val δ (consSize F δ P L R) eK eF =
      Q.val δ P.size eK eF - Q.val δ L.size eK eF * Q.val δ R.size eK eF := by
  rw [consSize, qsub_val, qmul_val]

theorem consLeaf_val (P L R : QFP F) :
    Q.val δ (consLeaf F δ P L R) eK eF =
      Q.val δ P.leaf eK eF - (Q.val δ L.leaf eK eF + Q.val δ L.size eK eF * Q.val δ R.leaf eK eF) := by
  rw [consLeaf, qsub_val, qadd_val, qmul_val]

theorem consDyck_val (z : Q F) (P L R : QFP F) :
    Q.val δ (consDyck F δ z P L R) eK eF =
      Q.val δ z eK eF * Q.val δ P.dyck eK eF
        - Q.val δ z eK eF * Q.val δ z eK eF * Q.val δ L.dyck eK eF
        - Q.val δ L.size eK eF * Q.val δ L.size eK eF
        - Q.val δ z eK eF * (Q.val δ L.size eK eF * Q.val δ L.size eK eF * Q.val δ R.dyck eK eF) := by
  simp only [consDyck, qsub_val, qmul_val]

theorem atomTest_val (q : CoeffExpr F) (x : QFP F) :
    Q.val δ (atomTest F q x) eK eF = algebraMap K (Quad (algebraMap F K δ))
      (algebraMap F K (q.eval eF)) * (Q.val δ x.size eK eF - Q.val δ (zq F) eK eF) := by
  rw [atomTest, qsmul_val, qsub_val]

/-- **The six `𝕂`-equations of the three cons gates hold iff the parent record is `FP.cons` of its
children at the seed `z′`**. -/
theorem cons_gates_iff [Fact (¬ IsSquare (algebraMap F K δ))] (z : Q F) (P L R : QFP F) (hz : Q.val δ z eK eF ≠ 0) :
    (Q.IsZero (consSize F δ P L R) eK eF ∧ Q.IsZero (consLeaf F δ P L R) eK eF ∧
      Q.IsZero (consDyck F δ z P L R) eK eF) ↔
    QFP.val δ P eK eF = FP.cons (Q.val δ z eK eF) (QFP.val δ L eK eF) (QFP.val δ R eK eF) := by
  rw [Q.isZero_iff δ eK eF, Q.isZero_iff δ eK eF, Q.isZero_iff δ eK eF, consSize_val,
    consLeaf_val, consDyck_val]
  simp only [QFP.val, FP.cons]
  generalize Q.val δ z eK eF = Z at hz ⊢
  generalize Q.val δ P.size eK eF = Ps
  generalize Q.val δ P.dyck eK eF = Pd
  generalize Q.val δ P.leaf eK eF = Pl
  generalize Q.val δ L.size eK eF = Ls
  generalize Q.val δ L.dyck eK eF = Ld
  generalize Q.val δ L.leaf eK eF = Ll
  generalize Q.val δ R.size eK eF = Rs
  generalize Q.val δ R.dyck eK eF = Rd
  generalize Q.val δ R.leaf eK eF = Rl
  have hdy : Z * Pd - Z * Z * Ld - Ls * Ls - Z * (Ls * Ls * Rd) = 0 ↔
      Pd = Z * Ld + Ls * Ls * Z⁻¹ + Ls * Ls * Rd := by
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      rw [h]
      field_simp
      ring
  rw [sub_eq_zero, sub_eq_zero, hdy]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
  · intro h
    exact ⟨congrArg FP.size h, congrArg FP.leaf h, congrArg FP.dyck h⟩

/-- **Completeness of the gate pair**: the honest fingerprints `enc z′ (cell x y)`, `enc z′ x`,
`enc z′ y` (`fn2` in `𝕂′`-values) satisfy all six `𝕂`-equations (`z′ ≠ 0`). -/
theorem cons_gates_of_enc [Fact (¬ IsSquare (algebraMap F K δ))] (z : Q F) (P L R : QFP F)
    (hz : Q.val δ z eK eF ≠ 0) (x y : Noun)
    (hP : QFP.val δ P eK eF = GlobalCarryRecognizer.enc (Q.val δ z eK eF) (Noun.cell x y))
    (hL : QFP.val δ L eK eF = GlobalCarryRecognizer.enc (Q.val δ z eK eF) x)
    (hR : QFP.val δ R eK eF = GlobalCarryRecognizer.enc (Q.val δ z eK eF) y) :
    Q.IsZero (consSize F δ P L R) eK eF ∧ Q.IsZero (consLeaf F δ P L R) eK eF ∧
      Q.IsZero (consDyck F δ z P L R) eK eF := by
  refine (cons_gates_iff δ eK eF z P L R hz).mpr ?_
  rw [hP, hL, hR, GlobalCarryRecognizer.enc_cons hz]

end Semantics

/-! ## Through the existing finrank-3 compiler (`hK` untouched) -/

section Compiled
open Module
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- A `𝕂′`-gate is zero iff its `2 · e` compiled `𝔽`-coordinate equations are (the existing
`mixedCompile_zero_iff` on each of Re and Im). -/
theorem gate_zero_iff_compiled {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {eK : Env K} {eF : Env F} (h : IsCoordEnv b col0 eK eF) (g : Q F) :
    Q.IsZero g eK eF ↔
      (∀ k, (mixedCompile b col0 g.1 k).eval eF = 0) ∧
        ∀ k, (mixedCompile b col0 g.2 k).eval eF = 0 := by
  unfold Q.IsZero
  rw [mixedCompile_zero_iff b col0 h, mixedCompile_zero_iff b col0 h]

omit [FiniteDimensional F K] in
/-- Compiling a `𝕂′`-gate never raises the degree. -/
theorem gate_compiled_degree_le {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (g : Q F) (k : Fin e) :
    (mixedCompile b col0 g.1 k).degree ≤ qdeg F g ∧
      (mixedCompile b col0 g.2 k).degree ≤ qdeg F g :=
  ⟨le_trans (mixedCompile_degree_le b col0 g.1 k) (le_max_left _ _),
    le_trans (mixedCompile_degree_le b col0 g.2 k) (le_max_right _ _)⟩

/-- **Gate degrees after compilation at `finrank 𝔽 𝕂 = 3`**: every compiled coordinate equation of
the cons gates has degree `≤ 2 / 2 / 3`, and `≤ 4` under the provenance mask; the atom test `≤ 2`. -/
theorem cons_gates_compiled_degrees (b : Basis (Fin 3) F K) (col0 : VarKind → ℕ → ℕ) (δ : F)
    (k : Fin 3) :
    (∀ g ∈ [(consSize F δ (ptQ F) (lcQ F) (rcQ F)).1, (consSize F δ (ptQ F) (lcQ F) (rcQ F)).2,
        (consLeaf F δ (ptQ F) (lcQ F) (rcQ F)).1, (consLeaf F δ (ptQ F) (lcQ F) (rcQ F)).2],
      (mixedCompile b col0 g k).degree ≤ 2) ∧
    (∀ g ∈ [(consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F)).1,
        (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F)).2],
      (mixedCompile b col0 g k).degree ≤ 3) ∧
    (∀ g ∈ [(qsmul F (provCol F) (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F))).1,
        (qsmul F (provCol F) (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F))).2],
      (mixedCompile b col0 g k).degree ≤ 4) ∧
    (∀ g ∈ [(atomTest F (.var .traceCur 3) (ptQ F)).1, (atomTest F (.var .traceCur 3) (ptQ F)).2],
      (mixedCompile b col0 g k).degree ≤ 2) := by
  have h1 := gate_compiled_degree_le b col0 (consSize F δ (ptQ F) (lcQ F) (rcQ F)) k
  have h2 := gate_compiled_degree_le b col0 (consLeaf F δ (ptQ F) (lcQ F) (rcQ F)) k
  have h3 := gate_compiled_degree_le b col0 (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F)) k
  have h4 := gate_compiled_degree_le b col0
    (qsmul F (provCol F) (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F))) k
  have h5 := gate_compiled_degree_le b col0 (atomTest F (.var .traceCur 3) (ptQ F)) k
  rw [consSize_degree] at h1
  rw [consLeaf_degree] at h2
  rw [consDyck_degree] at h3
  rw [prov_consDyck_degree] at h4
  rw [atomTest_degree] at h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exacts [h1.1, h1.2, h2.1, h2.2]
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [h3.1, h3.2]
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [h4.1, h4.2]
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [h5.1, h5.2]

end Compiled

end Nock.NockVMROM.Thm54.T0TowerFP
