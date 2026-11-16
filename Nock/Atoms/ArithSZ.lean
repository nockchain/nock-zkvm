/-
  Lifts of the ALU's limb-polynomial identities from `𝔽_p` to `ℕ` (the length bound `m ≤ 62` is supplied by the
  length counter of `AluSZChipJ9`; `AluSZOps` discharges it).

  Every identity has the shape `Pos − Neg = (C B − X)·Q` over `𝔽_p` with `Pos, Neg, Q` limb
  polynomials (natural coefficients).  Rewritten as `Pos + X·Q = Neg + C B·Q`, both sides have
  natural coefficients; when both sides' coefficients are `< p` the `𝔽_p` identity is an `ℕ[X]`
  identity (`natPoly_eq_of_map_eq`), and evaluation at `X = B` gives the `ℕ` statement
  (`lift_core`).  The sufficient bound `Pos_k + qmax < p ∧ Neg_k + B·qmax < p` is slightly stronger
  than the bound "lifted integer range ⊂ (−p, p)" and holds for every operation:

  * `add_lift`, `sub_lift`, `lt_lift_yes`, `lt_lift_no` (`q ≤ 1`; limbs `< B`);
  * `link_lift` (+ `_getD`, `_val`, `_zipWith`): `E + 2^16·O = A` with halves `< 2^16`, `a < B`;
  * `W`, `W_eq` (`W = A·B + (X − C B)·O_a·O_b` under the links), `coeff_Wnat_le` (`W_k ≤ 2^55`
    for `m ≤ 62`; the coarser range argument gives `< 2^56`), `mul_lift_halves`, `mul_lift` (W form),
    `mul_lift_gate` (the product form of the `mul` gate of `AluSZChipJ9`; `q < 2^25`);
  * `div_lift`, `div_lift_gate` (`K < 2^25`, `K₂ ≤ 1`): `val a = val q·val d + val r ∧ val r < val d`.
  * Negative controls: `add_lift_nc` (2 limbs, `q = [B − 1]`: the identity holds, `val c = p ≠ 0`);
    `mul_unsplit_nc` (32-bit unsplit factors of length 2, `q < 2^25`: the product identity holds
    mod `p`, values differ).

  Statement choices where the statement is underspecified (for the per-op soundness): limb lists are arbitrary lists of
  naturals (padding allowed); halves lists' lengths need only be `≤ m` for the FIRST factor (the
  convolution has at most `m` terms); `link_lift`'s `zipWith` form needs equal lengths (with
  padding only the `getD`/`val` forms hold, and those are what `mul_lift` uses).
-/
import Nock.Atoms.Fingerprint

set_option autoImplicit false

namespace Nock.Atoms

open Polynomial

/-! ## Generic lift -/

theorem p_eq_num : p = 18446744069414584321 := by norm_num [Nock.Field.p]

theorem getD_le_of {l : List ℕ} {M : ℕ} (hl : ∀ a ∈ l, a ≤ M) (i : ℕ) : l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some a => simpa using hl a (List.mem_of_getElem? h)

theorem coeff_natPoly_le {l : List ℕ} {M : ℕ} (hl : ∀ a ∈ l, a ≤ M) (k : ℕ) :
    (natPoly l).coeff k ≤ M := by
  rw [coeff_natPoly]; exact getD_le_of hl k

theorem le_pred_of_forall_lt {l : List ℕ} {M : ℕ} (hl : ∀ a ∈ l, a < M) : ∀ a ∈ l, a ≤ M - 1 :=
  fun a ha => by have := hl a ha; omega

theorem coeff_X_mul_le (Q : ℕ[X]) (qmax : ℕ) (hQ : ∀ k, Q.coeff k ≤ qmax) (k : ℕ) :
    (X * Q).coeff k ≤ qmax := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_X_mul]; exact hQ k

/-- Two natural polynomials with coefficients `< p` and equal images in `𝔽_p[X]` are equal. -/
theorem natPoly_eq_of_map_eq {f g : ℕ[X]} (hf : ∀ k, f.coeff k < p) (hg : ∀ k, g.coeff k < p)
    (h : f.map (Nat.castRingHom Fp) = g.map (Nat.castRingHom Fp)) : f = g := by
  ext k
  have := congrArg (fun q => q.coeff k) h
  simp only [coeff_map, eq_natCast] at this
  exact natCast_inj_lt (hf k) (hg k) this

/-- **The lift.** `Pos − Neg = (C B − X)·Q` over `𝔽_p`, `Q_k ≤ qmax`, `Pos_k + qmax < p`,
`Neg_k + B·qmax < p` ⇒ `Pos(B) = Neg(B)` in `ℕ`. -/
theorem lift_core {P N Q : ℕ[X]} (qmax : ℕ) (hQ : ∀ k, Q.coeff k ≤ qmax)
    (hP : ∀ k, P.coeff k + qmax < p) (hN : ∀ k, N.coeff k + B * qmax < p)
    (h : P.map (Nat.castRingHom Fp) - N.map (Nat.castRingHom Fp) =
      (C (B : Fp) - X) * Q.map (Nat.castRingHom Fp)) :
    P.eval B = N.eval B := by
  have h2 : (P + X * Q).map (Nat.castRingHom Fp) = (N + C B * Q).map (Nat.castRingHom Fp) := by
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C, Nat.coe_castRingHom]
    linear_combination h
  have h3 := natPoly_eq_of_map_eq (f := P + X * Q) (g := N + C B * Q) ?_ ?_ h2
  · have := congrArg (eval B) h3
    simp only [eval_add, eval_mul, eval_X, eval_C] at this
    omega
  · intro k; rw [coeff_add]; have := coeff_X_mul_le Q qmax hQ k; have := hP k; omega
  · intro k
    rw [coeff_add, coeff_C_mul]
    have := hN k
    have : B * Q.coeff k ≤ B * qmax := Nat.mul_le_mul_left _ (hQ k)
    omega

theorem map_natPoly (l : List ℕ) : (natPoly l).map (Nat.castRingHom Fp) = limbPoly l := rfl

/-! ## add / sub / lt (one-bit carries) -/

/-- **add**: `A + B − C = (C B − X)·Q`, limbs `< B`, `q ≤ 1` ⇒ `val a + val b = val c`. -/
theorem add_lift {a b c q : List ℕ} (ha : ∀ x ∈ a, x < B) (hb : ∀ x ∈ b, x < B)
    (hc : ∀ x ∈ c, x < B) (hq : ∀ x ∈ q, x ≤ 1)
    (h : limbPoly a + limbPoly b - limbPoly c = (C (B : Fp) - X) * limbPoly q) :
    val a + val b = val c := by
  have hB := B_eq; have hp := p_eq_num
  have := lift_core (P := natPoly a + natPoly b) (N := natPoly c) (Q := natPoly q) 1
    (coeff_natPoly_le hq) (fun k => by
      rw [coeff_add]
      have := coeff_natPoly_le (le_pred_of_forall_lt ha) k
      have := coeff_natPoly_le (le_pred_of_forall_lt hb) k
      omega)
    (fun k => by have := coeff_natPoly_le (le_pred_of_forall_lt hc) k; omega)
    (by simpa only [Polynomial.map_add, map_natPoly] using h)
  simpa only [eval_add, ← val_eq_eval] using this

/-- **sub** (`add_lift` with roles permuted): `B + C − A = (C B − X)·Q` ⇒ `val c = val a − val b`
and `val b ≤ val a` (underflow is unsatisfiable). -/
theorem sub_lift {a b c q : List ℕ} (ha : ∀ x ∈ a, x < B) (hb : ∀ x ∈ b, x < B)
    (hc : ∀ x ∈ c, x < B) (hq : ∀ x ∈ q, x ≤ 1)
    (h : limbPoly b + limbPoly c - limbPoly a = (C (B : Fp) - X) * limbPoly q) :
    val b + val c = val a ∧ val b ≤ val a ∧ val c = val a - val b := by
  have := add_lift hb hc ha hq h
  omega

/-- **lt, yes branch** (with the `+1`): `A + D + 1 − B = (C B − X)·Q` ⇒ `val a + val d + 1 =
val b`, hence `val a < val b`. -/
theorem lt_lift_yes {a b d q : List ℕ} (ha : ∀ x ∈ a, x < B) (hb : ∀ x ∈ b, x < B)
    (hd : ∀ x ∈ d, x < B) (hq : ∀ x ∈ q, x ≤ 1)
    (h : limbPoly a + limbPoly d + 1 - limbPoly b = (C (B : Fp) - X) * limbPoly q) :
    val a + val d + 1 = val b ∧ val a < val b := by
  have hB := B_eq; have hp := p_eq_num
  have := lift_core (P := natPoly a + natPoly d + 1) (N := natPoly b) (Q := natPoly q) 1
    (coeff_natPoly_le hq) (fun k => by
      rw [coeff_add, coeff_add, coeff_one]
      have := coeff_natPoly_le (le_pred_of_forall_lt ha) k
      have := coeff_natPoly_le (le_pred_of_forall_lt hd) k
      split_ifs <;> omega)
    (fun k => by have := coeff_natPoly_le (le_pred_of_forall_lt hb) k; omega)
    (by simpa only [Polynomial.map_add, Polynomial.map_one, map_natPoly] using h)
  simp only [eval_add, eval_one, ← val_eq_eval] at this
  omega

/-- **lt, no branch**: `B + D − A = (C B − X)·Q` ⇒ `val b + val d = val a`, hence `val b ≤ val a`. -/
theorem lt_lift_no {a b d q : List ℕ} (ha : ∀ x ∈ a, x < B) (hb : ∀ x ∈ b, x < B)
    (hd : ∀ x ∈ d, x < B) (hq : ∀ x ∈ q, x ≤ 1)
    (h : limbPoly b + limbPoly d - limbPoly a = (C (B : Fp) - X) * limbPoly q) :
    val b + val d = val a ∧ val b ≤ val a := by
  have := add_lift hb hd ha hq h
  omega

/-! ## The link `E + 2^16·O = A` -/

/-- **link** (`ℕ[X]` form): `E + 2^16·O = A` over `𝔽_p`, halves `< 2^16`, `a < B` ⇒ the same
identity of natural polynomials. -/
theorem link_lift {e o a : List ℕ} (he : ∀ x ∈ e, x < 2 ^ 16) (ho : ∀ x ∈ o, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (h : limbPoly e + C (2 ^ 16 : Fp) * limbPoly o = limbPoly a) :
    natPoly e + C (2 ^ 16) * natPoly o = natPoly a := by
  have hB := B_eq; have hp := p_eq_num
  refine natPoly_eq_of_map_eq (fun k => ?_) (fun k => ?_) ?_
  · rw [coeff_add, coeff_C_mul]
    have := coeff_natPoly_le (le_pred_of_forall_lt he) k
    have := coeff_natPoly_le (le_pred_of_forall_lt ho) k
    omega
  · have := coeff_natPoly_le (le_pred_of_forall_lt ha) k; omega
  · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, map_natPoly, map_natPoly,
      map_natPoly, Nat.coe_castRingHom, Nat.cast_pow, Nat.cast_ofNat]
    exact h

theorem link_lift_getD {e o a : List ℕ} (he : ∀ x ∈ e, x < 2 ^ 16) (ho : ∀ x ∈ o, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (h : limbPoly e + C (2 ^ 16 : Fp) * limbPoly o = limbPoly a) (i : ℕ) :
    e.getD i 0 + 2 ^ 16 * o.getD i 0 = a.getD i 0 := by
  have := congrArg (fun q => q.coeff i) (link_lift he ho ha h)
  simpa only [coeff_add, coeff_C_mul, coeff_natPoly] using this

theorem link_lift_val {e o a : List ℕ} (he : ∀ x ∈ e, x < 2 ^ 16) (ho : ∀ x ∈ o, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (h : limbPoly e + C (2 ^ 16 : Fp) * limbPoly o = limbPoly a) :
    val e + 2 ^ 16 * val o = val a := by
  have := congrArg (eval B) (link_lift he ho ha h)
  simpa only [eval_add, eval_mul, eval_C, ← val_eq_eval] using this

/-- **link, literal form**: with equal lengths, `a = zipWith (· + 2^16 ·) e o`. -/
theorem link_lift_zipWith {e o a : List ℕ} (he : ∀ x ∈ e, x < 2 ^ 16) (ho : ∀ x ∈ o, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (hle : e.length = a.length) (hlo : o.length = a.length)
    (h : limbPoly e + C (2 ^ 16 : Fp) * limbPoly o = limbPoly a) :
    a = List.zipWith (fun x y => x + 2 ^ 16 * y) e o := by
  apply List.ext_getElem
  · simp [List.length_zipWith, hle, hlo]
  · intro i h1 h2
    have := link_lift_getD he ho ha h i
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)] at this
    rw [List.getElem_zipWith]
    exact this.symm

/-! ## mul: the 16-bit-halves rewrite `W` -/

/-- `W` over `ℕ`: `E_a E_b + 2^16 (E_a O_b + O_a E_b) + X·O_a O_b`. -/
noncomputable def Wnat (aE aO bE bO : List ℕ) : ℕ[X] :=
  natPoly aE * natPoly bE + C (2 ^ 16) * (natPoly aE * natPoly bO + natPoly aO * natPoly bE) +
    X * (natPoly aO * natPoly bO)

/-- `W` over `𝔽_p`. -/
noncomputable def W (aE aO bE bO : List ℕ) : Fp[X] :=
  limbPoly aE * limbPoly bE +
    C (2 ^ 16 : Fp) * (limbPoly aE * limbPoly bO + limbPoly aO * limbPoly bE) +
    X * (limbPoly aO * limbPoly bO)

theorem map_Wnat (aE aO bE bO : List ℕ) :
    (Wnat aE aO bE bO).map (Nat.castRingHom Fp) = W aE aO bE bO := by
  rw [Wnat, W]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    map_natPoly, Nat.coe_castRingHom, Nat.cast_pow, Nat.cast_ofNat]

theorem eval_Wnat (aE aO bE bO : List ℕ) :
    (Wnat aE aO bE bO).eval B = (val aE + 2 ^ 16 * val aO) * (val bE + 2 ^ 16 * val bO) := by
  simp only [Wnat, eval_add, eval_mul, eval_C, eval_X, ← val_eq_eval]
  rw [show B = 2 ^ 16 * 2 ^ 16 by norm_num [B]]
  ring

theorem C_B_eq : C (B : Fp) = C (2 ^ 16 : Fp) * C (2 ^ 16 : Fp) := by
  rw [← C_mul]; norm_num [B]

/-- **`W_eq`**: under the links `E + 2^16·O = A`, `W = A·B + (X − C B)·O_a·O_b`. -/
theorem W_eq {aE aO bE bO : List ℕ} {A Bp : Fp[X]}
    (ha : limbPoly aE + C (2 ^ 16 : Fp) * limbPoly aO = A)
    (hb : limbPoly bE + C (2 ^ 16 : Fp) * limbPoly bO = Bp) :
    W aE aO bE bO = A * Bp + (X - C (B : Fp)) * (limbPoly aO * limbPoly bO) := by
  subst ha hb
  rw [W, C_B_eq]
  ring

/-- Convolution bound: `(natPoly l * g)_k ≤ len l · F·G`. -/
theorem coeff_natPoly_mul_le (l : List ℕ) (g : ℕ[X]) (F G : ℕ) (hl : ∀ x ∈ l, x ≤ F)
    (hg : ∀ k, g.coeff k ≤ G) (k : ℕ) : (natPoly l * g).coeff k ≤ l.length * (F * G) := by
  induction l generalizing k with
  | nil => simp [natPoly]
  | cons a l ih =>
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have ha := hl a List.mem_cons_self
    simp only [natPoly, add_mul, coeff_add, coeff_C_mul, mul_assoc, List.length_cons]
    have h1 : a * g.coeff k ≤ F * G := Nat.mul_le_mul ha (hg k)
    have h2 : (X * (natPoly l * g)).coeff k ≤ l.length * (F * G) := coeff_X_mul_le _ _ ih' k
    calc _ ≤ F * G + l.length * (F * G) := Nat.add_le_add h1 h2
      _ = _ := by ring

/-- **The `W` coefficient bound** (`mul`, `m ≤ 62`): `W_k ≤ 2^55`. -/
theorem coeff_Wnat_le {aE aO bE bO : List ℕ} {m : ℕ} (hm : m ≤ 62) (hlE : aE.length ≤ m)
    (hlO : aO.length ≤ m) (haE : ∀ x ∈ aE, x < 2 ^ 16) (haO : ∀ x ∈ aO, x < 2 ^ 16)
    (hbE : ∀ x ∈ bE, x < 2 ^ 16) (hbO : ∀ x ∈ bO, x < 2 ^ 16) (k : ℕ) :
    (Wnat aE aO bE bO).coeff k ≤ 2 ^ 55 := by
  have hF : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ 16) → ∀ x ∈ l, x ≤ 65535 :=
    fun l hl x hx => by have := hl x hx; omega
  have h1 := coeff_natPoly_mul_le aE (natPoly bE) 65535 65535 (hF _ haE)
    (coeff_natPoly_le (hF _ hbE)) k
  have h2 := coeff_natPoly_mul_le aE (natPoly bO) 65535 65535 (hF _ haE)
    (coeff_natPoly_le (hF _ hbO)) k
  have h3 := coeff_natPoly_mul_le aO (natPoly bE) 65535 65535 (hF _ haO)
    (coeff_natPoly_le (hF _ hbE)) k
  have h4 := coeff_X_mul_le _ _ (coeff_natPoly_mul_le aO (natPoly bO) 65535 65535 (hF _ haO)
    (coeff_natPoly_le (hF _ hbO))) k
  have hE : aE.length * (65535 * 65535) ≤ 62 * (65535 * 65535) :=
    Nat.mul_le_mul_right _ (hlE.trans hm)
  have hO : aO.length * (65535 * 65535) ≤ 62 * (65535 * 65535) :=
    Nat.mul_le_mul_right _ (hlO.trans hm)
  simp only [Wnat, coeff_add, coeff_C_mul]
  omega

/-- **mul, halves form**: `W − C = (C B − X)·Q`, halves `< 2^16`, first factor's halves of length
`≤ m ≤ 62`, `c < B`, `q < 2^25` ⇒ `(E_a + 2^16 O_a)(B)·(E_b + 2^16 O_b)(B) = val c`. -/
theorem mul_lift_halves {aE aO bE bO c q : List ℕ} {m : ℕ} (hm : m ≤ 62) (hlE : aE.length ≤ m)
    (hlO : aO.length ≤ m) (haE : ∀ x ∈ aE, x < 2 ^ 16) (haO : ∀ x ∈ aO, x < 2 ^ 16)
    (hbE : ∀ x ∈ bE, x < 2 ^ 16) (hbO : ∀ x ∈ bO, x < 2 ^ 16) (hc : ∀ x ∈ c, x < B)
    (hq : ∀ x ∈ q, x < 2 ^ 25)
    (h : W aE aO bE bO - limbPoly c = (C (B : Fp) - X) * limbPoly q) :
    (val aE + 2 ^ 16 * val aO) * (val bE + 2 ^ 16 * val bO) = val c := by
  have hB := B_eq; have hp := p_eq_num
  have := lift_core (P := Wnat aE aO bE bO) (N := natPoly c) (Q := natPoly q) (2 ^ 25 - 1)
    (coeff_natPoly_le (le_pred_of_forall_lt hq))
    (fun k => by have := coeff_Wnat_le hm hlE hlO haE haO hbE hbO k; omega)
    (fun k => by have := coeff_natPoly_le (le_pred_of_forall_lt hc) k; omega)
    (by rw [map_Wnat, map_natPoly]; exact h)
  rw [eval_Wnat, ← val_eq_eval] at this
  exact this

/-- **mul_lift** (literal form, `W`): with the links `E_x + 2^16·O_x = X_x` for both factors. -/
theorem mul_lift {a b aE aO bE bO c q : List ℕ} {m : ℕ} (hm : m ≤ 62) (hlE : aE.length ≤ m)
    (hlO : aO.length ≤ m) (haE : ∀ x ∈ aE, x < 2 ^ 16) (haO : ∀ x ∈ aO, x < 2 ^ 16)
    (hbE : ∀ x ∈ bE, x < 2 ^ 16) (hbO : ∀ x ∈ bO, x < 2 ^ 16) (ha : ∀ x ∈ a, x < B)
    (hb : ∀ x ∈ b, x < B) (hc : ∀ x ∈ c, x < B) (hq : ∀ x ∈ q, x < 2 ^ 25)
    (hla : limbPoly aE + C (2 ^ 16 : Fp) * limbPoly aO = limbPoly a)
    (hlb : limbPoly bE + C (2 ^ 16 : Fp) * limbPoly bO = limbPoly b)
    (h : W aE aO bE bO - limbPoly c = (C (B : Fp) - X) * limbPoly q) :
    val a * val b = val c := by
  rw [← link_lift_val haE haO ha hla, ← link_lift_val hbE hbO hb hlb]
  exact mul_lift_halves hm hlE hlO haE haO hbE hbO hc hq h

/-- **mul, gate form** (`L_a·L_b + (y − B)·O_a(y)·O_b(y) − L_c − (B − y)·Q(y)`, as
polynomials): `A·B + (X − C B)·O_a·O_b − C = (C B − X)·Q` plus the links ⇒ `val a · val b = val c`. -/
theorem mul_lift_gate {a b aE aO bE bO c q : List ℕ} {m : ℕ} (hm : m ≤ 62) (hlE : aE.length ≤ m)
    (hlO : aO.length ≤ m) (haE : ∀ x ∈ aE, x < 2 ^ 16) (haO : ∀ x ∈ aO, x < 2 ^ 16)
    (hbE : ∀ x ∈ bE, x < 2 ^ 16) (hbO : ∀ x ∈ bO, x < 2 ^ 16) (ha : ∀ x ∈ a, x < B)
    (hb : ∀ x ∈ b, x < B) (hc : ∀ x ∈ c, x < B) (hq : ∀ x ∈ q, x < 2 ^ 25)
    (hla : limbPoly aE + C (2 ^ 16 : Fp) * limbPoly aO = limbPoly a)
    (hlb : limbPoly bE + C (2 ^ 16 : Fp) * limbPoly bO = limbPoly b)
    (h : limbPoly a * limbPoly b + (X - C (B : Fp)) * (limbPoly aO * limbPoly bO) - limbPoly c =
      (C (B : Fp) - X) * limbPoly q) :
    val a * val b = val c :=
  mul_lift hm hlE hlO haE haO hbE hbO ha hb hc hq hla hlb (by rw [W_eq hla hlb]; exact h)

/-! ## div / mod -/

/-- **div_lift** (literal form, `W_{q,d}`): `W_{q,d} + R − A = (C B − X)·K` and
`R + S + 1 − D = (C B − X)·K₂` (with the links of `q`, `d`) ⇒ `val a = val q·val d + val r ∧
val r < val d`. -/
theorem div_lift {a d q r s qE qO dE dO k k₂ : List ℕ} {m : ℕ} (hm : m ≤ 62)
    (hlE : qE.length ≤ m) (hlO : qO.length ≤ m) (hqE : ∀ x ∈ qE, x < 2 ^ 16)
    (hqO : ∀ x ∈ qO, x < 2 ^ 16) (hdE : ∀ x ∈ dE, x < 2 ^ 16) (hdO : ∀ x ∈ dO, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (hd : ∀ x ∈ d, x < B) (hq : ∀ x ∈ q, x < B) (hr : ∀ x ∈ r, x < B)
    (hs : ∀ x ∈ s, x < B) (hk : ∀ x ∈ k, x < 2 ^ 25) (hk₂ : ∀ x ∈ k₂, x ≤ 1)
    (hlq : limbPoly qE + C (2 ^ 16 : Fp) * limbPoly qO = limbPoly q)
    (hld : limbPoly dE + C (2 ^ 16 : Fp) * limbPoly dO = limbPoly d)
    (h₁ : W qE qO dE dO + limbPoly r - limbPoly a = (C (B : Fp) - X) * limbPoly k)
    (h₂ : limbPoly r + limbPoly s + 1 - limbPoly d = (C (B : Fp) - X) * limbPoly k₂) :
    val a = val q * val d + val r ∧ val r < val d := by
  have hB := B_eq; have hp := p_eq_num
  have e₁ := lift_core (P := Wnat qE qO dE dO + natPoly r) (N := natPoly a) (Q := natPoly k)
    (2 ^ 25 - 1) (coeff_natPoly_le (le_pred_of_forall_lt hk))
    (fun j => by
      rw [coeff_add]
      have := coeff_Wnat_le hm hlE hlO hqE hqO hdE hdO j
      have := coeff_natPoly_le (le_pred_of_forall_lt hr) j
      omega)
    (fun j => by have := coeff_natPoly_le (le_pred_of_forall_lt ha) j; omega)
    (by rw [Polynomial.map_add, map_Wnat, map_natPoly, map_natPoly, map_natPoly]; exact h₁)
  have e₂ := (lt_lift_yes hr hd hs hk₂ h₂).1
  rw [eval_add, eval_Wnat, ← val_eq_eval, ← val_eq_eval, link_lift_val hqE hqO hq hlq,
    link_lift_val hdE hdO hd hld] at e₁
  omega

/-- `div_lift` gives `val d ≠ 0` (division by zero is unsatisfiable). -/
theorem div_lift_ne_zero {a d q r s qE qO dE dO k k₂ : List ℕ} {m : ℕ} (hm : m ≤ 62)
    (hlE : qE.length ≤ m) (hlO : qO.length ≤ m) (hqE : ∀ x ∈ qE, x < 2 ^ 16)
    (hqO : ∀ x ∈ qO, x < 2 ^ 16) (hdE : ∀ x ∈ dE, x < 2 ^ 16) (hdO : ∀ x ∈ dO, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (hd : ∀ x ∈ d, x < B) (hq : ∀ x ∈ q, x < B) (hr : ∀ x ∈ r, x < B)
    (hs : ∀ x ∈ s, x < B) (hk : ∀ x ∈ k, x < 2 ^ 25) (hk₂ : ∀ x ∈ k₂, x ≤ 1)
    (hlq : limbPoly qE + C (2 ^ 16 : Fp) * limbPoly qO = limbPoly q)
    (hld : limbPoly dE + C (2 ^ 16 : Fp) * limbPoly dO = limbPoly d)
    (h₁ : W qE qO dE dO + limbPoly r - limbPoly a = (C (B : Fp) - X) * limbPoly k)
    (h₂ : limbPoly r + limbPoly s + 1 - limbPoly d = (C (B : Fp) - X) * limbPoly k₂) :
    val d ≠ 0 := by
  have := (div_lift hm hlE hlO hqE hqO hdE hdO ha hd hq hr hs hk hk₂ hlq hld h₁ h₂).2
  omega

/-- **div, gate form**: `Q·D + (X − C B)·O_q·O_d + R − A = (C B − X)·K` and
`R + S + 1 − D = (C B − X)·K₂` plus the links ⇒ `val a = val q·val d + val r ∧ val r < val d`. -/
theorem div_lift_gate {a d q r s qE qO dE dO k k₂ : List ℕ} {m : ℕ} (hm : m ≤ 62)
    (hlE : qE.length ≤ m) (hlO : qO.length ≤ m) (hqE : ∀ x ∈ qE, x < 2 ^ 16)
    (hqO : ∀ x ∈ qO, x < 2 ^ 16) (hdE : ∀ x ∈ dE, x < 2 ^ 16) (hdO : ∀ x ∈ dO, x < 2 ^ 16)
    (ha : ∀ x ∈ a, x < B) (hd : ∀ x ∈ d, x < B) (hq : ∀ x ∈ q, x < B) (hr : ∀ x ∈ r, x < B)
    (hs : ∀ x ∈ s, x < B) (hk : ∀ x ∈ k, x < 2 ^ 25) (hk₂ : ∀ x ∈ k₂, x ≤ 1)
    (hlq : limbPoly qE + C (2 ^ 16 : Fp) * limbPoly qO = limbPoly q)
    (hld : limbPoly dE + C (2 ^ 16 : Fp) * limbPoly dO = limbPoly d)
    (h₁ : limbPoly q * limbPoly d + (X - C (B : Fp)) * (limbPoly qO * limbPoly dO) +
      limbPoly r - limbPoly a = (C (B : Fp) - X) * limbPoly k)
    (h₂ : limbPoly r + limbPoly s + 1 - limbPoly d = (C (B : Fp) - X) * limbPoly k₂) :
    val a = val q * val d + val r ∧ val r < val d :=
  div_lift hm hlE hlO hqE hqO hdE hdO ha hd hq hr hs hk hk₂ hlq hld
    (by rw [W_eq hlq hld]; exact h₁) h₂

/-! ## Negative controls -/

theorem limbPoly_nil : limbPoly [] = 0 := by simp [limbPoly, natPoly]

theorem limbPoly_cons (a : ℕ) (l : List ℕ) : limbPoly (a :: l) = C (a : Fp) + X * limbPoly l := by
  simp [limbPoly, natPoly]

theorem natCast_pnum_Fp : ((18446744069414584321 : ℕ) : Fp) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).2 (by rw [p_eq_num])

theorem pnum_FpX : (18446744069414584321 : Fp[X]) = 0 := by
  have := congrArg C natCast_pnum_Fp
  rwa [Nat.cast_ofNat, map_ofNat, map_zero] at this

/-- **NC for `add_lift`**: without `q ≤ 1` the lift fails at 2 limbs.  `a = b = [0, 0]`,
`c = [1, B − 1]` (limbs `< B`), `q = [B − 1]` (`B − 1 = 4294967295`, so even `q < B` fails): the
`𝔽_p` identity holds (`B(B − 1) ≡ −1`), but `val c = p ≠ 0 = val a + val b`. -/
theorem add_lift_nc :
    limbPoly [0, 0] + limbPoly [0, 0] - limbPoly [1, 4294967295] =
        (C (B : Fp) - X) * limbPoly [4294967295] ∧
      (∀ x ∈ [1, 4294967295], x < B) ∧ (4294967295 < B) ∧
      val [0, 0] + val [0, 0] ≠ val [1, 4294967295] := by
  refine ⟨?_, ?_, by norm_num [B], by simp [B]⟩
  · simp only [limbPoly_cons, limbPoly_nil, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, map_zero,
      map_one, map_ofNat, mul_zero, add_zero, B, Nat.cast_pow, map_pow]
    linear_combination (-1 : Fp[X]) * pnum_FpX
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have := B_eq; omega

/-- **NC for `mul_lift`**: with 32-bit UNSPLIT factor limbs at length 2 (no halves, no `W`), the
product identity `A·B − C = (C B − X)·Q` holds over `𝔽_p` with `c < B`, `q < 2^25`, yet
`val a · val b ≠ val c` (the `X¹` coefficient `x₀y₁ + x₁y₀ = p + B − 256` wraps past `p`; over `ℤ`,
`A·B − C − (B − X)·Q = p·X`). -/
theorem mul_unsplit_nc :
    limbPoly [4294967295, 16777216] * limbPoly [256, 4294967295] -
        limbPoly [4294967040, 255, 4278190080, 16777215] =
        (C (B : Fp) - X) * limbPoly [255, 0, 16777215] ∧
      (∀ x ∈ [4294967295, 16777216], x < B) ∧ (∀ x ∈ [256, 4294967295], x < B) ∧
      (∀ x ∈ [4294967040, 255, 4278190080, 16777215], x < B) ∧
      (∀ x ∈ [255, 0, 16777215], x < 2 ^ 25) ∧
      val [4294967295, 16777216] * val [256, 4294967295] ≠
        val [4294967040, 255, 4278190080, 16777215] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp [B]⟩
  · simp only [limbPoly_cons, limbPoly_nil, Nat.cast_zero, Nat.cast_ofNat, map_zero, map_ofNat,
      mul_zero, add_zero, B, Nat.cast_pow, map_pow]
    linear_combination X * pnum_FpX
  all_goals
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have := B_eq; omega

/-! ## Axioms (expected: `[propext, Classical.choice, Quot.sound]` or a subset) -/

#print axioms lift_core
#print axioms add_lift
#print axioms sub_lift
#print axioms lt_lift_yes
#print axioms lt_lift_no
#print axioms link_lift
#print axioms link_lift_getD
#print axioms link_lift_val
#print axioms link_lift_zipWith
#print axioms W_eq
#print axioms coeff_Wnat_le
#print axioms mul_lift_halves
#print axioms mul_lift
#print axioms mul_lift_gate
#print axioms div_lift
#print axioms div_lift_ne_zero
#print axioms div_lift_gate
#print axioms add_lift_nc
#print axioms mul_unsplit_nc

end Nock.Atoms
