/-
  NockvmE2E/Exec/SoundFri.lean   (proof-only, not in the exe closure)

  L9 (and L8, below): the flat verifier's FRI checks imply the audited FRI acceptance `queryBad`.
  * Part A (ArkLib side): `fold2` (arity-2 `foldValue` = the verifier's `foldK3` formula), `verifyQueries_ne_none_of_pointwise`
    (from `eval_verifyQueries` + `eval_checkRound_iff_schedule`), `queryBad_of_pointwise`, `friAccepts_of_pointwise`.
  * Part B (index/point algebra of the verifier's domain `Y w g = c^(2^w) (γ^(2^w))^g`): the flat model `FlatFri` implies the pointwise fold equations.
  * Part C (`Hom`): the verifier's `K3` arithmetic read through a ring-hom record (VLink supplies the `toK_*`/`toZ_*` lemmas).
  * Part D (L8): the batched input word.
-/
import NockvmE2E.FriPort.Accepts
import NockvmE2E.Exec.Verify
import NockvmE2E.Succ.FriDeep

open OracleComp OracleSpec ProtocolSpec
open Fri.Spec Domain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SF

/-! ## Part A: ArkLib side -/

section A

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]

lemma neg_mem_dom {N : ℕ} [NeZero N] (D : SmoothCosetFftDomain N F) (u : F) (hu : u ∈ D.toFinset) :
    -u ∈ D.toFinset := by
  simpa using hu

/-- Arity-2 `foldValue` at a point `u^2`, `u` in the domain: `(f u + f (-u))/2 + α (f u - f (-u))/(2u)`. -/
theorem fold2 {N : ℕ} [NeZero N] (D : SmoothCosetFftDomain N F) (f : F → F) (u : F)
    (hu : u ∈ D.toFinset) (α : F) :
    ProximityGap.foldValue D (fun z => f (D z)) 1 α (u ^ 2) =
      (f u + f (-u)) / 2 + α * ((f u - f (-u)) / (2 * u)) := by
  have hu' : u ∈ D := CosetFftDomain.mem_toFinset_iff_mem.mp hu
  have hnu : -u ∈ D := CosetFftDomain.mem_toFinset_iff_mem.mp (neg_mem_dom D u hu)
  obtain ⟨j, hj⟩ := hu'
  obtain ⟨j', hj'⟩ := hnu
  have hne : u ≠ 0 := by rw [← hj]; exact CosetFftDomainClass.ne_zero D j
  have h2 : (2 : F) ≠ 0 := CosetFftDomainClass.domain_implies_2_ne_0 D
  have hjj : j ≠ j' := by
    intro h; subst h
    have : u = -u := hj.symm.trans hj'
    apply hne
    have : (2:F) * u = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2
  have hsq : D j ^ 2 = D.subdomain 1 (CosetFftDomainClass.sqFoldMapGen (i := 1) j) := by
    have := CosetFftDomainClass.subdomain_sqFoldMapGen_eq_pow_domain (ω := D) (i := 1) (j := j)
    simpa using this.symm
  have hsq' : D j' ^ 2 = D.subdomain 1 (CosetFftDomainClass.sqFoldMapGen (i := 1) j) := by
    rw [← hsq, hj', hj]; ring
  have := ProximityGap.foldWord_k_1_of_sq_roots (domain := D) (f := fun z => f (D z)) (α := α) hjj hsq hsq'
  have e : ProximityGap.foldValue D (fun z => f (D z)) 1 α
      (D.subdomain 1 (CosetFftDomainClass.sqFoldMapGen (i := 1) j)) =
      ProximityGap.foldWord D (fun z => f (D z)) 1 α (CosetFftDomainClass.sqFoldMapGen (i := 1) j) := rfl
  rw [← hj, hsq, e, this, hj', ← hj]

variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

/-- The pointwise (field-element) form of one fold check of the committed history `o` at the query point `x`:
round `i`, `u = x^(2^(prefix i))`, block `{u, -u}`, next point `u^2`. -/
def PtFold (o : ∀ j, FinalOracleStatement s ω j) (α : F) (i : Fin (k + 1)) (x : F) : Prop :=
  let u := x ^ 2 ^ foldingPrefix s i.castSucc
  (committedFunction s o i.castSucc u + committedFunction s o i.castSucc (-u)) / 2 +
      α * ((committedFunction s o i.castSucc u - committedFunction s o i.castSucc (-u)) / (2 * u)) =
    committedFunction s o i.succ (u ^ 2)

theorem checkRound_of_ptFold (hs : (∑ j, (s j).val) ≤ n) (hs1 : ∀ i, (s i).val = 1)
    (o : ∀ j, FinalOracleStatement s ω j) (α : F) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) (h : PtFold s o α i x.val) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (QueryRound.checkRound s hs (finalPolynomial s o) α i x)).run = true := by
  have hsucc : foldingPrefix s i.succ = foldingPrefix s i.castSucc + 1 := by
    rw [foldingPrefix_succ, hs1]
  have hlt : foldingPrefix s i.castSucc < n := by
    have := foldingPrefix_le s i.succ
    have h2 := foldingPrefix_le s i.succ
    omega
  have : NeZero (n - foldingPrefix s i.castSucc) := ⟨by omega⟩
  have hmem : x.val ^ 2 ^ foldingPrefix s i.castSucc ∈
      ((ω.subdomain (foldingPrefix s i.castSucc)).toFinset) :=
    CosetFftDomainClass.pow_mem_subdomain_of_mem_subdomain_0_toFinset (by omega) x.property
  have key := (QueryRound.eval_checkRound_iff_schedule s hs o α i x).mpr
  refine key ?_
  rw [hsucc, hs1, pow_succ, pow_mul]
  have := fold2 (ω.subdomain (foldingPrefix s i.castSucc))
    (fun y => committedFunction s o i.castSucc y) _ hmem α
  rw [this]
  simpa [PtFold, hsucc, pow_succ, pow_mul] using h

/-- **L9 core.** All `l` queries pass all `k+1` pointwise fold checks ⇒ the audited query verifier does not return `none`. -/
theorem verifyQueries_ne_none_of_pointwise (hs : (∑ j, (s j).val) ≤ n) (hs1 : ∀ i, (s i).val = 1)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) {l : ℕ}
    (xs : Fin l → (ω.subdomain 0).toFinset) (h : ∀ j i, PtFold s o (α i) i (xs j).val) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (QueryRound.verifyQueries s hs l α xs).run).run ≠ none := by
  rw [QueryRound.eval_verifyQueries]
  rw [if_pos (fun j i => checkRound_of_ptFold s hs hs1 o (α i) i (xs j) (h j i))]
  simp

end A

/-! ## Part B: index and point algebra of the verifier's domain -/

section B
variable {F : Type} [Field F]

/-- the verifier's domain point of word `w` at index `g`: `c^(2^w) · (γ^(2^w))^g` -/
def Yp (c γ : F) (w g : ℕ) : F := c ^ 2 ^ w * (γ ^ 2 ^ w) ^ g

def fold2F (a b y α : F) : F := (a + b) / 2 + α * ((a - b) / (2 * y))

lemma fold2F_swap (a b y α : F) : fold2F b a (-y) α = fold2F a b y α := by
  unfold fold2F
  have : (b - a) / (2 * -y) = (a - b) / (2 * y) := by rw [mul_neg, div_neg, ← neg_div, neg_sub]
  rw [this, add_comm b a]

lemma Yp_sq (c γ : F) (w g : ℕ) : Yp c γ w g ^ 2 = Yp c γ (w + 1) g := by
  unfold Yp; ring

lemma Yp_pow (c γ : F) (m g : ℕ) : (c * γ ^ g) ^ 2 ^ m = Yp c γ m g := by
  unfold Yp
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm g]

variable {c γ : F} {n : ℕ}

lemma Yp_half (hγ : γ ^ 2 ^ (n - 1) = -1) {w : ℕ} (hw : w + 1 ≤ n) (g : ℕ) :
    Yp c γ w (g + 2 ^ (n - w - 1)) = - Yp c γ w g := by
  have hk : (γ ^ 2 ^ w) ^ 2 ^ (n - w - 1) = -1 := by
    rw [← pow_mul, ← pow_add, show w + (n - w - 1) = n - 1 by omega]; exact hγ
  unfold Yp
  rw [pow_add (γ ^ 2 ^ w) g, hk]
  ring

lemma Yp_per (hγ : γ ^ 2 ^ (n - 1) = -1) {w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) :
    (γ ^ 2 ^ w) ^ 2 ^ (n - w) = 1 := by
  have h1 : γ ^ 2 ^ n = 1 := by
    rw [show n = (n - 1) + 1 by omega, pow_succ, pow_mul, hγ]; norm_num
  rw [← pow_mul, ← pow_add, show w + (n - w) = n by omega]; exact h1

lemma Yp_mod (hγ : γ ^ 2 ^ (n - 1) = -1) {w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) (g : ℕ) :
    Yp c γ w g = Yp c γ w (g % 2 ^ (n - w)) := by
  have hp := Yp_per hγ hn hw
  conv_lhs => rw [← Nat.mod_add_div g (2 ^ (n - w))]
  unfold Yp
  rw [pow_add, pow_mul, hp, one_pow, mul_one]


/-- `g` is a read index of word `w` for the query position `pos`. -/
def Rd (n pos w g : ℕ) : Prop := g < 2 ^ (n - w) ∧ g % 2 ^ (n - w - 1) = pos % 2 ^ (n - w - 1)

lemma sq_pt (hγ : γ ^ 2 ^ (n - 1) = -1) (hn : 1 ≤ n) {i : ℕ} (hi : i + 1 ≤ n) (pos : ℕ) :
    ((c * γ ^ pos) ^ 2 ^ i) ^ 2 = Yp c γ (i + 1) (pos % 2 ^ (n - i - 1)) := by
  rw [Yp_pow, Yp_sq, Yp_mod hγ hn hi pos, show n - i - 1 = n - (i + 1) by omega]

lemma level_fold (hγ : γ ^ 2 ^ (n - 1) = -1) (hn : 1 ≤ n) {i : ℕ} (hi : i + 1 ≤ n) (pos : ℕ)
    (W : ℕ → ℕ → F) (CF : F → F) (hR : ∀ g, Rd n pos i g → CF (Yp c γ i g) = W i g) (α Nx : F)
    (hfl : fold2F (W i (pos % 2 ^ (n - i - 1))) (W i (pos % 2 ^ (n - i - 1) + 2 ^ (n - i - 1)))
      (Yp c γ i (pos % 2 ^ (n - i - 1))) α = Nx) :
    (CF ((c * γ ^ pos) ^ 2 ^ i) + CF (-((c * γ ^ pos) ^ 2 ^ i))) / 2 +
      α * ((CF ((c * γ ^ pos) ^ 2 ^ i) - CF (-((c * γ ^ pos) ^ 2 ^ i))) / (2 * (c * γ ^ pos) ^ 2 ^ i)) = Nx := by
  have hM : 2 ^ (n - i) = 2 * 2 ^ (n - i - 1) := by
    rw [← pow_succ']; congr 1; omega
  set h := 2 ^ (n - i - 1) with hh
  have hpos : 0 < h := Nat.two_pow_pos _
  set g := pos % h with hg
  have hgh : g < h := Nat.mod_lt _ hpos
  have hu : (c * γ ^ pos) ^ 2 ^ i = Yp c γ i (pos % 2 ^ (n - i)) := by
    rw [Yp_pow, Yp_mod hγ hn (by omega : i ≤ n)]
  have hg0 : pos % 2 ^ (n - i) % h = g := by
    rw [hM]; exact Nat.mod_mod_of_dvd _ (Dvd.intro_left 2 rfl)
  have hg0lt : pos % 2 ^ (n - i) < 2 * h := by rw [← hM]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hRg : Rd n pos i g := ⟨by omega, by rw [← hh, hg]; exact Nat.mod_mod _ _⟩
  have hRgh : Rd n pos i (g + h) := ⟨by omega, by rw [← hh, Nat.add_mod_right, hg, Nat.mod_mod _ _]⟩
  rw [hu]
  have hneg : Yp c γ i (g + h) = - Yp c γ i g := Yp_half hγ hi g
  by_cases hlt : pos % 2 ^ (n - i) < h
  · have e0 : pos % 2 ^ (n - i) = g := by
      have := hg0; rwa [Nat.mod_eq_of_lt hlt] at this
    rw [e0]
    have hA := hR g hRg
    have hB := hR (g + h) hRgh
    rw [hneg] at hB
    rw [hA, hB]
    unfold fold2F at hfl
    exact hfl
  · have h1 : h ≤ pos % 2 ^ (n - i) := by omega
    have h2 := Nat.mod_eq_sub_mod h1
    have e0 : pos % 2 ^ (n - i) = g + h := by
      have h3 : (pos % 2 ^ (n - i) - h) % h = pos % 2 ^ (n - i) - h :=
        Nat.mod_eq_of_lt (by omega)
      omega
    rw [e0]
    have hA := hR g hRg
    have hB := hR (g + h) hRgh
    rw [hneg] at hB ⊢
    rw [neg_neg, hA, hB]
    rw [← fold2F_swap] at hfl
    unfold fold2F at hfl
    exact hfl

/-! ### the flat model -/

/-- the fold-partner offset of level `i`: `2^(n-i-1)` -/
abbrev hf (n i : ℕ) : ℕ := 2 ^ (n - i - 1)

/-- The index-level form of the verifier's checks for ONE query position `pos`: at every level `i ≤ k`, the fold of the two opened
values of word `i` (at the folded index `g = pos % 2^(n-i-1)` and its partner) equals the word `i+1` value at `g` (or, at `i = k`,
`pfinal` at the last domain point). `W w g` = the opened value of word `w` at index `g`; `P` = the final polynomial. -/
def FlatFri (c γ : F) (n k : ℕ) (W : ℕ → ℕ → F) (α : ℕ → F) (P : F → F) (pos : ℕ) : Prop :=
  ∀ i, i ≤ k →
    fold2F (W i (pos % hf n i)) (W i (pos % hf n i + hf n i)) (Yp c γ i (pos % hf n i)) (α i) =
      if i < k then W (i + 1) (pos % hf n i) else P (Yp c γ (k + 1) (pos % hf n i))

/-- The verifier's loop, as the recursion it executes (`prev`, `prevIdx`, the `a`/`b` selection, the final polynomial). -/
def walkGo (c γ : F) (n k : ℕ) (W : ℕ → ℕ → F) (α : ℕ → F) (P : F → F) (pos : ℕ) :
    ℕ → F → ℕ → ℕ → Prop
  | 0, prev, pI, _ => prev = P (Yp c γ (k + 1) pI)
  | r + 1, prev, pI, w =>
      prev = (if pI < hf n w then W w (pos % hf n w) else W w (pos % hf n w + hf n w)) ∧
      walkGo c γ n k W α P pos r
        (fold2F (W w (pos % hf n w)) (W w (pos % hf n w + hf n w)) (Yp c γ w (pos % hf n w)) (α w))
        (pos % hf n w) (w + 1)

def Walk (c γ : F) (n k : ℕ) (W : ℕ → ℕ → F) (α : ℕ → F) (P : F → F) (pos : ℕ) : Prop :=
  walkGo c γ n k W α P pos k
    (fold2F (W 0 (pos % hf n 0)) (W 0 (pos % hf n 0 + hf n 0)) (Yp c γ 0 (pos % hf n 0)) (α 0))
    (pos % hf n 0) 1

lemma sel_eq {n i : ℕ} (hi : i + 2 ≤ n) (pos : ℕ) (W : ℕ → ℕ → F) :
    (if pos % hf n i < hf n (i + 1) then W (i + 1) (pos % hf n (i + 1))
      else W (i + 1) (pos % hf n (i + 1) + hf n (i + 1))) = W (i + 1) (pos % hf n i) := by
  have e : hf n i = 2 * hf n (i + 1) := by
    unfold hf; rw [← pow_succ']; congr 1; omega
  have hpos : 0 < hf n (i + 1) := Nat.two_pow_pos _
  have hm : pos % hf n (i + 1) = pos % hf n i % hf n (i + 1) := by
    rw [e]; exact (Nat.mod_mod_of_dvd _ (Dvd.intro_left 2 rfl)).symm
  have hlt : pos % hf n i < 2 * hf n (i + 1) := by rw [← e]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  by_cases h : pos % hf n i < hf n (i + 1)
  · rw [if_pos h, hm, Nat.mod_eq_of_lt h]
  · rw [if_neg h, hm, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    congr 1; omega

theorem walkGo_sound {c γ : F} {n k : ℕ} (hk : k + 1 ≤ n) (W : ℕ → ℕ → F) (α : ℕ → F) (P : F → F) (pos : ℕ) :
    ∀ r i prev, i + 1 + r = k + 1 →
      prev = fold2F (W i (pos % hf n i)) (W i (pos % hf n i + hf n i)) (Yp c γ i (pos % hf n i)) (α i) →
      walkGo c γ n k W α P pos r prev (pos % hf n i) (i + 1) →
      ∀ j, i ≤ j → j ≤ k →
        fold2F (W j (pos % hf n j)) (W j (pos % hf n j + hf n j)) (Yp c γ j (pos % hf n j)) (α j) =
          if j < k then W (j + 1) (pos % hf n j) else P (Yp c γ (k + 1) (pos % hf n j)) := by
  intro r
  induction r with
  | zero =>
    intro i prev hik hprev hw j hij hjk
    have hi : i = k := by omega
    have hj : j = k := by omega
    subst hi; subst hj
    simp only [walkGo] at hw
    rw [if_neg (lt_irrefl _), ← hprev, hw]
  | succ r ih =>
    intro i prev hik hprev hw j hij hjk
    simp only [walkGo] at hw
    obtain ⟨hsel, hrest⟩ := hw
    have hik' := ih (i + 1) _ (by omega) rfl hrest
    by_cases hji : j = i
    · subst hji
      rw [if_pos (by omega), ← hprev, hsel]
      exact sel_eq (by omega) pos W
    · exact hik' j (by omega) hjk

theorem flat_of_walk {c γ : F} {n k : ℕ} (hk : k + 1 ≤ n) (W : ℕ → ℕ → F) (α : ℕ → F) (P : F → F) (pos : ℕ)
    (h : Walk c γ n k W α P pos) : FlatFri c γ n k W α P pos := fun j hj =>
  walkGo_sound hk W α P pos k 0 _ (by omega) rfl h j (Nat.zero_le _) hj

end B

/-! ## Part B': glue to the audited objects -/

section Glue

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

theorem foldingPrefix_eq (hs1 : ∀ i, (s i).val = 1) (i : Fin (k + 2)) : foldingPrefix s i = i.val := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [foldingPrefix_succ, hs1, ih]; simp

/-- The link between the audited committed history `o` / challenges `α` / query points `xs` and the flat data
`(W, P, αN, pos)` (the hypotheses VLink must discharge; every field is a statement about field elements). -/
structure Link (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) {l : ℕ}
    (xs : Fin l → (ω.subdomain 0).toFinset) (c γ : F) (pos : Fin l → ℕ) (W : ℕ → ℕ → F) (P : F → F)
    (αN : ℕ → F) : Prop where
  hγ : γ ^ 2 ^ (n - 1) = -1
  hx : ∀ j, (xs j).val = c * γ ^ pos j
  hα : ∀ i : Fin (k + 1), α i = αN i.val
  hCF : ∀ j (w : Fin (k + 2)), w.val ≤ k → ∀ g, Rd n (pos j) w.val g →
    committedFunction s o w (Yp c γ w.val g) = W w.val g
  hP : ∀ y, (finalPolynomial s o).eval y = P y

theorem ptFold_of_flat (hs1 : ∀ i, (s i).val = 1) (hk : k + 1 ≤ n)
    {o : ∀ j, FinalOracleStatement s ω j} {α : FinalStatement F k} {l : ℕ}
    {xs : Fin l → (ω.subdomain 0).toFinset} {c γ : F} {pos : Fin l → ℕ} {W : ℕ → ℕ → F} {P : F → F}
    {αN : ℕ → F} (L : Link s o α xs c γ pos W P αN) (j : Fin l)
    (hflat : FlatFri c γ n k W αN P (pos j)) (i : Fin (k + 1)) :
    PtFold s o (α i) i (xs j).val := by
  have hi : i.val ≤ k := by omega
  have hn : 1 ≤ n := by omega
  unfold PtFold
  simp only [foldingPrefix_eq s hs1 i.castSucc, Fin.coe_castSucc]
  rw [L.hx j]
  have hfl := hflat i.val hi
  have hR : ∀ g, Rd n (pos j) i.val g →
      committedFunction s o i.castSucc (Yp c γ i.val g) = W i.val g := fun g hg =>
    L.hCF j i.castSucc (by simp; omega) g (by simpa using hg)
  have h1 := level_fold L.hγ hn (by omega : i.val + 1 ≤ n) (pos j) W (committedFunction s o i.castSucc) hR
    (α i) (if i.val < k then W (i.val + 1) (pos j % hf n i) else P (Yp c γ (k + 1) (pos j % hf n i)))
    (by rw [L.hα i]; exact hfl)
  rw [h1, sq_pt L.hγ hn (by omega : i.val + 1 ≤ n) (pos j)]
  by_cases hik : i.val < k
  · rw [if_pos hik]
    have := L.hCF j i.succ (by simp; omega) (pos j % hf n i) ⟨?_, ?_⟩
    · exact this.symm
    · simp only [Fin.val_succ]
      calc pos j % hf n i < hf n i := Nat.mod_lt _ (Nat.two_pow_pos _)
        _ = 2 ^ (n - (i.val + 1)) := by unfold hf; rw [show n - (i.val + 1) = n - i.val - 1 by omega]
    · simp only [Fin.val_succ]
      unfold hf
      rw [show n - (i.val + 1) = n - i.val - 1 by omega]
      exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))
  · rw [if_neg hik]
    have hlast : i.succ = Fin.last (k + 1) := Fin.ext (by simp; omega)
    rw [hlast, committedFunction_last, L.hP, show i.val = k by omega]


/-- **L9 (query verifier).** The flat walks of all `l` queries (`FlatFri` index form) imply the audited query verifier accepts. -/
theorem verifyQueries_of_flat (hs : (∑ j, (s j).val) ≤ n) (hs1 : ∀ i, (s i).val = 1)
    {o : ∀ j, FinalOracleStatement s ω j} {α : FinalStatement F k} {l : ℕ}
    {xs : Fin l → (ω.subdomain 0).toFinset} {c γ : F} {pos : Fin l → ℕ} {W : ℕ → ℕ → F} {P : F → F}
    {αN : ℕ → F} (L : Link s o α xs c γ pos W P αN)
    (hflat : ∀ j, FlatFri c γ n k W αN P (pos j)) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (QueryRound.verifyQueries s hs l α xs).run).run ≠ none := by
  have hk : k + 1 ≤ n := by
    have : (∑ j, (s j).val) = k + 1 := by simp [hs1]
    omega
  exact verifyQueries_ne_none_of_pointwise s hs hs1 o α xs
    (fun j i => ptFold_of_flat s hs1 hk L j (hflat j) i)

/-! ### the audited acceptance predicate on the decoded transcript -/

variable (d : ℕ+) (l : ℕ)

/-- the commitment history `queryBad` reads (before the query challenge) -/
noncomputable abbrev qO (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    ∀ j, FinalOracleStatement s ω j :=
  queryHistory s l f (tr.restrict (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

noncomputable abbrev qA (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    FinalStatement F k :=
  queryFoldChallenges s l (tr.restrict (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

noncomputable abbrev qX (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    Fin l → (ω.subdomain 0).toFinset :=
  cast (queryChallenge_type (ω := ω) s l) (tr.read (queryChallenge s l).val (by simp))

/-- **L9.** The flat verifier's FRI checks (`FlatFri` per query, final degree `< d`) imply the audited `queryBad`
(final degree check ∧ the query verifier does not return `none`) on the transcript `tr`. -/
theorem queryBad_of_flat (hs : (∑ j, (s j).val) ≤ n) (hs1 : ∀ i, (s i).val = 1)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ)
    {c γ : F} {pos : Fin l → ℕ} {W : ℕ → ℕ → F} {P : F → F} {αN : ℕ → F}
    (L : Link s (qO s l f tr) (qA s l tr) (qX s l tr) c γ pos W P αN)
    (hdeg : (finalPolynomial s (qO s l f tr)).natDegree < d.val)
    (hflat : ∀ j, FlatFri c γ n k W αN P (pos j)) :
    queryBad s d l hs f tr :=
  ⟨hdeg, verifyQueries_of_flat s hs hs1 L hflat⟩

end Glue

section Accepts

open NockvmE2E.FriPort Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- **L9 in the form `cLocal` consumes**: `friAccepts` (the FRI part of the audited local check) on the decoded native path. -/
theorem friAccepts_of_flat (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (hs1 : ∀ i, (s i).val = 1)
    {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath)
    {c γ : F} {pos : Fin l → ℕ} {W : ℕ → ℕ → F} {P : F → F} {αN : ℕ → F}
    (L : Link s
      (qO s l (initialOracle s z.1)
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          (friTranscript s d l path)))
      (qA s l (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          (friTranscript s d l path)))
      (qX s l (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          (friTranscript s d l path))) c γ pos W P αN)
    (hdeg : (finalPolynomial s (qO s l (initialOracle s z.1)
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          (friTranscript s d l path)))).natDegree < d.val)
    (hflat : ∀ j, FlatFri c γ n k W αN P (pos j)) :
    friAccepts s d l hdom z path = true :=
  (friAccepts_iff s d l hdom z path).mpr
    (queryBad_of_flat s d l (round_bound hdom) hs1 _ _ L hdeg hflat)

end Accepts

/-! ## Part C: the verifier's K3 arithmetic and loop, read through a ring-hom record -/

section C
open NockvmE2E.Exec.V NockvmE2E.Exec.VF

theorem k3_beq {a b : K3} (h : (a == b) = true) : a = b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  change instBEqK3.beq _ _ = true at h
  simp [instBEqK3.beq] at h
  obtain ⟨h0, h1, h2⟩ := h
  simp [h0, h1, h2]

/-- The verifier's `K3`/`G` arithmetic, read in a field `F` (VLink supplies the instance with `F = KC`).
`C`/`Cg` are the canonical-limb predicates (`limb < p`): `VF.add`/`VF.sub` are modular only on canonical limbs, so `φ_add`/`φ_sub` carry
`C a → C b →`.  `C` is closed under every operation the verifier performs (`mul`/`smul`/`inv` produce canonical limbs from ANY inputs). -/
structure Hom (F : Type) [Field F] where
  φ : K3 → F
  ψ : G → F
  C : K3 → Prop
  Cg : G → Prop
  C_add : ∀ a b, C a → C b → C (K3.add a b)
  C_sub : ∀ a b, C a → C b → C (K3.sub a b)
  C_mul : ∀ a b, C (K3.mul a b)
  C_smul : ∀ s a, C (K3.smul s a)
  C_inv : ∀ a, C (K3.inv a)
  C_zero : C K3.zero
  C_ofG : ∀ g, Cg g → C (K3.ofG g)
  Cg_mul : ∀ a b, Cg (VF.mul a b)
  φ_add : ∀ a b, C a → C b → φ (K3.add a b) = φ a + φ b
  φ_sub : ∀ a b, C a → C b → φ (K3.sub a b) = φ a - φ b
  φ_mul : ∀ a b, φ (K3.mul a b) = φ a * φ b
  φ_smul : ∀ s a, φ (K3.smul s a) = ψ s * φ a
  φ_ofG : ∀ g, φ (K3.ofG g) = ψ g
  φ_zero : φ K3.zero = 0
  φ_one : φ K3.one = 1
  φ_inv : ∀ a, φ (K3.inv a) = (φ a)⁻¹
  ψ_mul : ∀ a b, ψ (VF.mul a b) = ψ a * ψ b
  ψ_pow : ∀ a e, ψ (VF.pow a e) = ψ a ^ e
  ψ_inv : ∀ a, ψ (VF.inv a) = (ψ a)⁻¹
  ψ_two : ψ 2 = 2

variable {F : Type} [Field F] (H : Hom F)

theorem foldK3_hom (a b : K3) (y : G) (al : K3) (ha : H.C a) (hb : H.C b) :
    H.φ (foldK3 a b y al) = fold2F (H.φ a) (H.φ b) (H.ψ y) (H.φ al) := by
  unfold foldK3 fold2F
  rw [H.φ_smul, H.φ_add _ _ (H.C_add _ _ ha hb) (H.C_mul _ _), H.φ_add _ _ ha hb, H.φ_mul, H.φ_smul,
    H.φ_sub _ _ ha hb, H.ψ_inv, H.ψ_inv, H.ψ_two]
  ring

theorem yAt_hom (XI : ExecInst) (w g : ℕ) :
    H.ψ (yAt XI w g) = Yp (H.ψ XI.dShift) (H.ψ XI.dGen) w g := by
  unfold yAt Yp
  rw [H.ψ_mul, H.ψ_pow, H.ψ_pow, H.ψ_pow]

theorem Cg_yAt (XI : ExecInst) (w g : ℕ) : H.Cg (yAt XI w g) := H.Cg_mul _ _

/-- Horner evaluation of `c 0 .. c (n-1)` at `z` -/
def hornerF (c : ℕ → F) (n : ℕ) (z : F) : F :=
  (List.range' 0 n).foldl (fun acc i => acc * z + c (n - 1 - i)) 0

/-- fold homomorphism with a canonicity invariant on the accumulator -/
theorem foldl_hom {α : Type} (l : List α) (f : K3 → α → K3) (g : F → α → F) (acc : K3) (ha : H.C acc)
    (hf : ∀ a x, x ∈ l → H.C a → H.C (f a x) ∧ H.φ (f a x) = g (H.φ a) x) :
    H.C (l.foldl f acc) ∧ H.φ (l.foldl f acc) = l.foldl g (H.φ acc) := by
  induction l generalizing acc with
  | nil => exact ⟨ha, rfl⟩
  | cons x l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := hf acc x (List.mem_cons_self) ha
    obtain ⟨h3, h4⟩ := ih _ h1 (fun a y hy => hf a y (List.mem_cons_of_mem _ hy))
    exact ⟨h3, by rw [h4, h2]⟩

/-- Structural twin of `K3.horner` (the proof-side description; the totalised `K3.horner` must coincide with it). -/
def hornerK (coef : Array K3) (z : K3) : K3 :=
  (List.range' 0 coef.size).foldl (fun acc i => K3.add (K3.mul acc z) coef[coef.size - 1 - i]!) K3.zero

theorem hornerK_hom (coef : Array K3) (z : K3) (hc : ∀ j, j < coef.size → H.C coef[j]!) :
    H.φ (hornerK coef z) = hornerF (fun j => H.φ coef[j]!) coef.size (H.φ z) := by
  unfold hornerK hornerF
  have := foldl_hom H (List.range' 0 coef.size)
    (fun (acc : K3) (i : ℕ) => K3.add (K3.mul acc z) coef[coef.size - 1 - i]!)
    (fun (acc : F) (i : ℕ) => acc * H.φ z + H.φ coef[coef.size - 1 - i]!) K3.zero H.C_zero
    (fun a x hx hca => by
      have hx' : x < coef.size := by simpa using (List.mem_range'_1.mp hx).2
      exact ⟨H.C_add _ _ (H.C_mul _ _) (hc _ (by omega)),
        by rw [H.φ_add _ _ (H.C_mul _ _) (hc _ (by omega)), H.φ_mul]⟩)
  rw [this.2, H.φ_zero]

/-- Structural twin of the verifier's per-query FRI loop (`verifyFlatE`, "(vii) FRI", the body of `for q in π.pos`):
`walkKGo r prev prevIdx w` = the remaining `r` iterations of `for w in [1:k+1]` followed by the final-polynomial check.
`fa w gw` / `fb w gw` = `friAt (3+w) (lb sels[3+w]! (2*gw))` / `(2*gw+1)`; `word0` = `deepWord XI pts ops baseAt`. -/
def walkKGo (XI : ExecInst) (fa fb : ℕ → ℕ → K3) (alphas pfinal : Array K3) (q : ℕ) :
    ℕ → K3 → ℕ → ℕ → Bool
  | 0, prev, pI, _ => prev == hornerK pfinal (K3.ofG (yAt XI (XI.k + 1) pI))
  | r + 1, prev, pI, w =>
      (prev == (if pI < 2 ^ (XI.nD - w - 1) then fa w (q % 2 ^ (XI.nD - w - 1)) else fb w (q % 2 ^ (XI.nD - w - 1)))) &&
      walkKGo XI fa fb alphas pfinal q r
        (foldK3 (fa w (q % 2 ^ (XI.nD - w - 1))) (fb w (q % 2 ^ (XI.nD - w - 1)))
          (yAt XI w (q % 2 ^ (XI.nD - w - 1))) alphas[w]!) (q % 2 ^ (XI.nD - w - 1)) (w + 1)

def walkK (XI : ExecInst) (word0 : ℕ → K3) (fa fb : ℕ → ℕ → K3) (alphas pfinal : Array K3) (q : ℕ) : Bool :=
  walkKGo XI fa fb alphas pfinal q XI.k
    (foldK3 (word0 (q % 2 ^ (XI.nD - 1))) (word0 (q % 2 ^ (XI.nD - 1) + 2 ^ (XI.nD - 1))) (yAt XI 0 (q % 2 ^ (XI.nD - 1)))
      alphas[0]!) (q % 2 ^ (XI.nD - 1)) 1

/-- the field-side word read by the flat model: word 0 = `word0`, word `w ≥ 1` at index `idx` = `fa`/`fb` by the half of the leaf pair. -/
def Wf (XI : ExecInst) (word0 : ℕ → K3) (fa fb : ℕ → ℕ → K3) (w idx : ℕ) : K3 :=
  if w = 0 then word0 idx else if idx < 2 ^ (XI.nD - w - 1) then fa w idx else fb w (idx - 2 ^ (XI.nD - w - 1))

theorem walkKGo_sound (XI : ExecInst) (word0 : ℕ → K3) (fa fb : ℕ → ℕ → K3) (alphas pfinal : Array K3) (q : ℕ)
    (hfa : ∀ w g, H.C (fa w g)) (hfb : ∀ w g, H.C (fb w g)) (hpf : ∀ j, j < pfinal.size → H.C pfinal[j]!) :
    ∀ r prev pI w, 1 ≤ w → walkKGo XI fa fb alphas pfinal q r prev pI w = true →
      walkGo (H.ψ XI.dShift) (H.ψ XI.dGen) XI.nD XI.k (fun w i => H.φ (Wf XI word0 fa fb w i))
        (fun i => H.φ alphas[i]!) (hornerF (fun j => H.φ pfinal[j]!) pfinal.size) q r (H.φ prev) pI w := by
  intro r
  induction r with
  | zero =>
    intro prev pI w hw h
    simp only [walkKGo] at h
    have := k3_beq h
    simp only [walkGo]
    rw [this, hornerK_hom H _ _ hpf, H.φ_ofG, yAt_hom]
  | succ r ih =>
    intro prev pI w hw h
    simp only [walkKGo, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hpos : 0 < 2 ^ (XI.nD - w - 1) := Nat.two_pow_pos _
    have hlt : q % 2 ^ (XI.nD - w - 1) < 2 ^ (XI.nD - w - 1) := Nat.mod_lt _ hpos
    have hWa : Wf XI word0 fa fb w (q % 2 ^ (XI.nD - w - 1)) = fa w (q % 2 ^ (XI.nD - w - 1)) := by
      unfold Wf; rw [if_neg (by omega), if_pos hlt]
    have hWb : Wf XI word0 fa fb w (q % 2 ^ (XI.nD - w - 1) + 2 ^ (XI.nD - w - 1)) = fb w (q % 2 ^ (XI.nD - w - 1)) := by
      unfold Wf; rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    have e1 := k3_beq h1
    simp only [walkGo, hf]
    rw [hWa, hWb]
    refine ⟨?_, ?_⟩
    · rw [e1]; split_ifs <;> rfl
    · have := ih _ _ (w + 1) (by omega) h2
      rw [foldK3_hom H _ _ _ _ (hfa _ _) (hfb _ _), yAt_hom] at this
      exact this

theorem walkK_sound (XI : ExecInst) (word0 : ℕ → K3) (fa fb : ℕ → ℕ → K3) (alphas pfinal : Array K3) (q : ℕ)
    (hw0 : ∀ i, H.C (word0 i)) (hfa : ∀ w g, H.C (fa w g)) (hfb : ∀ w g, H.C (fb w g))
    (hpf : ∀ j, j < pfinal.size → H.C pfinal[j]!)
    (h : walkK XI word0 fa fb alphas pfinal q = true) :
    Walk (H.ψ XI.dShift) (H.ψ XI.dGen) XI.nD XI.k (fun w i => H.φ (Wf XI word0 fa fb w i))
      (fun i => H.φ alphas[i]!) (hornerF (fun j => H.φ pfinal[j]!) pfinal.size) q := by
  have := walkKGo_sound H XI word0 fa fb alphas pfinal q hfa hfb hpf _ _ _ 1 le_rfl h
  unfold Walk
  rw [foldK3_hom H _ _ _ _ (hw0 _) (hw0 _), yAt_hom] at this
  simpa [Wf, hf, Nat.sub_zero] using this


/-! ### Part D1 (L8, verifier side): `deepWord` regrouped -/

/-- Structural twin of the verifier's `deepWord` (the `ops` accumulation grouped by opening point, then one inverse per point):
the totalised `deepWord` must coincide with it. -/
def deepWordS (XI : ExecInst) (pts : Array K3) (ops : List (ℕ × ℕ × K3 × K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ) : K3 :=
  let y := VF.mul XI.dShift (VF.pow XI.dGen idx)
  (List.range' 0 (XI.r + 2)).foldl (fun tot p =>
    K3.add tot (K3.mul
      (ops.foldl (fun a (o : ℕ × ℕ × K3 × K3) =>
        if o.2.1 = p then K3.add a (K3.mul o.2.2.1 (K3.sub (K3.ofG (baseAt o.1 idx)) o.2.2.2)) else a) K3.zero)
      (K3.inv (K3.sub (K3.ofG y) pts[p]!)))) K3.zero

/-- sum of the per-opening summands (field side) -/
def opSum (T : (ℕ × ℕ × K3 × K3) → F) (w : ℕ → F) (M : ℕ) (ops : List (ℕ × ℕ × K3 × K3)) : F :=
  (ops.map fun o => if o.2.1 < M then T o * w o.2.1 else 0).sum

theorem group_sum (T : (ℕ × ℕ × K3 × K3) → F) (w : ℕ → F) (M : ℕ) (ops : List (ℕ × ℕ × K3 × K3)) :
    ∑ p ∈ Finset.range M, (ops.map fun o => if o.2.1 = p then T o else 0).sum * w p = opSum T w M ops := by
  induction ops with
  | nil => simp [opSum]
  | cons o ops ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at *
    rw [ih]
    simp only [opSum, List.map_cons, List.sum_cons]
    congr 1
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range]

theorem foldl_range_sum (f : ℕ → F) : ∀ M, (List.range' 0 M).foldl (fun t p => t + f p) 0 = ∑ p ∈ Finset.range M, f p := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range'_concat, List.foldl_append, ih, Finset.sum_range_succ]
    simp

theorem foldl_ite_sum {α : Type} (c : α → Prop) [DecidablePred c] (t : α → F) (l : List α) (a : F) :
    l.foldl (fun a o => if c o then a + t o else a) a = a + (l.map fun o => if c o then t o else 0).sum := by
  induction l generalizing a with
  | nil => simp
  | cons o l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases h : c o
    · simp only [if_pos h]; rw [ih]; ring
    · simp only [if_neg h]; rw [ih]; ring

/-- the inner accumulation of `deepWordS` at point slot `p` -/
def inK (ops : List (ℕ × ℕ × K3 × K3)) (baseAt : ℕ → ℕ → G) (idx p : ℕ) : K3 :=
  ops.foldl (fun a (o : ℕ × ℕ × K3 × K3) =>
        if o.2.1 = p then K3.add a (K3.mul o.2.2.1 (K3.sub (K3.ofG (baseAt o.1 idx)) o.2.2.2)) else a) K3.zero

theorem deepWordS_eq (XI : ExecInst) (pts : Array K3) (ops : List (ℕ × ℕ × K3 × K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ) :
    deepWordS XI pts ops baseAt idx = (List.range' 0 (XI.r + 2)).foldl
      (fun (tot : K3) (p : ℕ) => K3.add tot (K3.mul (inK ops baseAt idx p)
      (K3.inv (K3.sub (K3.ofG (VF.mul XI.dShift (VF.pow XI.dGen idx))) pts[p]!)))) K3.zero := rfl

theorem deepWordS_hom (XI : ExecInst) (pts : Array K3) (ops : List (ℕ × ℕ × K3 × K3)) (baseAt : ℕ → ℕ → G) (idx : ℕ)
    (hops : ∀ o ∈ ops, H.C o.2.2.1 ∧ H.C o.2.2.2 ∧ H.Cg (baseAt o.1 idx))
    (hpts : ∀ p, p < XI.r + 2 → H.C pts[p]!) :
    H.C (deepWordS XI pts ops baseAt idx) ∧
    H.φ (deepWordS XI pts ops baseAt idx) =
      opSum (fun o => H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2))
        (fun p => (H.ψ XI.dShift * H.ψ XI.dGen ^ idx - H.φ pts[p]!)⁻¹) (XI.r + 2) ops := by
  have inner : ∀ p, H.C (inK ops baseAt idx p) ∧ H.φ (inK ops baseAt idx p) =
      (ops.map fun o => if o.2.1 = p then
        H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2) else 0).sum := by
    intro p
    have := foldl_hom H ops
      (fun (a : K3) (o : ℕ × ℕ × K3 × K3) =>
        if o.2.1 = p then K3.add a (K3.mul o.2.2.1 (K3.sub (K3.ofG (baseAt o.1 idx)) o.2.2.2)) else a)
      (fun (a : F) (o : ℕ × ℕ × K3 × K3) => if o.2.1 = p then
        a + H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2) else a) K3.zero H.C_zero
      (fun a o ho hca => by
        by_cases h : o.2.1 = p
        · rw [if_pos h]
          obtain ⟨c1, c2, c3⟩ := hops o ho
          exact ⟨H.C_add _ _ hca (H.C_mul _ _),
            by rw [H.φ_add _ _ hca (H.C_mul _ _), H.φ_mul, H.φ_sub _ _ (H.C_ofG _ c3) c2, H.φ_ofG, if_pos h]⟩
        · simp [h, hca])
    refine ⟨this.1, ?_⟩
    show H.φ (ops.foldl _ K3.zero) = _
    rw [this.2, H.φ_zero]
    have := foldl_ite_sum (fun o : ℕ × ℕ × K3 × K3 => o.2.1 = p)
      (fun o => H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2)) ops 0
    rw [this, zero_add]
  have outer := foldl_hom H (List.range' 0 (XI.r + 2))
    (fun (tot : K3) (p : ℕ) => K3.add tot (K3.mul (inK ops baseAt idx p)
      (K3.inv (K3.sub (K3.ofG (VF.mul XI.dShift (VF.pow XI.dGen idx))) pts[p]!))))
    (fun (tot : F) (p : ℕ) => tot + (ops.map fun o => if o.2.1 = p then
        H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2) else 0).sum *
      (H.ψ XI.dShift * H.ψ XI.dGen ^ idx - H.φ pts[p]!)⁻¹) K3.zero H.C_zero
    (fun a p hp hca => by
      have hp' : p < XI.r + 2 := by simpa using (List.mem_range'_1.mp hp).2
      refine ⟨H.C_add _ _ hca (H.C_mul _ _), ?_⟩
      rw [H.φ_add _ _ hca (H.C_mul _ _), H.φ_mul, H.φ_inv,
        H.φ_sub _ _ (H.C_ofG _ (H.Cg_mul _ _)) (hpts p hp'), H.φ_ofG, H.ψ_mul, H.ψ_pow, (inner p).2])
  rw [deepWordS_eq]
  refine ⟨outer.1, ?_⟩
  rw [outer.2, H.φ_zero,
    foldl_range_sum (fun p => (ops.map fun o => if o.2.1 = p then
        H.φ o.2.2.1 * (H.ψ (baseAt o.1 idx) - H.φ o.2.2.2) else 0).sum *
      (H.ψ XI.dShift * H.ψ XI.dGen ^ idx - H.φ pts[p]!)⁻¹)]
  exact group_sum _ _ _ _

end C


/-! ## Part D: L8, the batched input word -/

section D
open OracleComp OracleSpec ProtocolSpec Polynomial
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep
open NockvmE2E.Exec.V NockvmE2E.Exec.VF

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable (s : Fin (k + 1) → ℕ+)

/-- **L8 (audited side).** The batched input word (`combinedOracle` of the DEEP quotient words) at a point of the initial domain. -/
theorem combined_deep_eq (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) (cs : F)
    (idx : Fin (2 ^ n)) (v : (ω.subdomain (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1)).toFinset)
    (hv : initialDomainPoint (s := s) (0 : Fin 1) v = ω.equivToFinset idx) :
    combinedOracle s m (CoreDefinitions.univariatePowersGenerator F m) cs
      (deepStmt (ω := ω) P A R0 e tr fin χ).2 0 v =
    ((List.finRange (m + 1)).map fun (j : Fin (m + 1)) => cs ^ (j : ℕ) *
      ((liftW (tr (colOf P e j)) idx - valOf P R0 e fin j) / (ω idx - ptOf P A e χ j))).sum := by
  unfold combinedOracle
  simp only [deepStmt]
  erw [hv, Equiv.symm_apply_apply]
  rfl

theorem forall2_sum {α β γ : Type} [AddCommMonoid γ] (R : α → β → Prop) (f : α → γ) (g : β → γ)
    (h : ∀ a b, R a b → f a = g b) : ∀ (l : List α) (l' : List β), List.Forall₂ R l l' → (l.map f).sum = (l'.map g).sum := by
  intro l l' hl
  induction hl with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, List.sum_cons]; rw [h _ _ hab, ih]

/-- **L8.** The verifier's batched input word at domain index `idx` (`deepWordS`, K3 read through `Hom`) equals the audited batched
word `combinedOracle … (deepStmt tr fin χ)` at the corresponding point. Hypotheses (VLink): `ops` is the `e`-ordered opening list
(`Forall₂` with `finRange (m+1)`: coefficient `cs^j`, point `ptOf j` (`pts[p]`), claimed value `valOf j`, base value `liftW (tr col) idx`),
every point slot is `< r+2`, and `ω idx = dShift · dGen^idx`. -/
theorem input_word_eq (H : Hom F) (XI : ExecInst) (pts : Array K3) (ops : List (ℕ × ℕ × K3 × K3)) (baseAt : ℕ → ℕ → G)
    (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) (cs : F) (idx : Fin (2 ^ n))
    (v : (ω.subdomain (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1)).toFinset)
    (hv : initialDomainPoint (s := s) (0 : Fin 1) v = ω.equivToFinset idx)
    (hω : ω idx = H.ψ XI.dShift * H.ψ XI.dGen ^ (idx : ℕ))
    (hops : List.Forall₂ (fun (o : ℕ × ℕ × K3 × K3) (j : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ H.φ o.2.2.1 = cs ^ (j : ℕ) ∧ H.φ pts[o.2.1]! = ptOf P A e χ j ∧
      H.φ o.2.2.2 = valOf P R0 e fin j ∧ H.ψ (baseAt o.1 idx) = liftW (tr (colOf P e j)) idx)
      ops (List.finRange (m + 1)))
    (hops_can : ∀ o ∈ ops, H.C o.2.2.1 ∧ H.C o.2.2.2 ∧ H.Cg (baseAt o.1 idx))
    (hpts_can : ∀ p, p < XI.r + 2 → H.C pts[p]!) :
    H.φ (deepWordS XI pts ops baseAt idx) =
      combinedOracle s m (CoreDefinitions.univariatePowersGenerator F m) cs
        (deepStmt (ω := ω) P A R0 e tr fin χ).2 0 v := by
  rw [combined_deep_eq P A R0 e s tr fin χ cs idx v hv, (deepWordS_hom H XI pts ops baseAt idx hops_can hpts_can).2, opSum]
  refine forall2_sum _ _ _ ?_ _ _ hops
  rintro o j ⟨hp, hc, hpt, hval, hb⟩
  simp only [if_pos hp]
  rw [hc, hpt, hval, hb, ← hω, div_eq_mul_inv]
  ring

end D

/-! ## Non-vacuity: the flat model on a tiny FRI instance (`k = 1`, domain `2^3`, `ZMod 17`)
`γ = 2` has `γ^(2^(n-1)) = -1`; word 0 = evaluations of `f(x) = x` on `3·⟨2⟩`, word 1 = the constant `5`, `pfinal = 5`;
`FlatFri` holds for EVERY query position `< 8` (kernel `decide`, no `native_decide`). The `Link`/ArkLib side is not instantiated here. -/

section NonVac

instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

instance decFlat (c γ : ZMod 17) (n k : ℕ) (W : ℕ → ℕ → ZMod 17) (α : ℕ → ZMod 17) (P : ZMod 17 → ZMod 17) (pos : ℕ) :
    Decidable (FlatFri c γ n k W α P pos) := by unfold FlatFri; infer_instance

theorem nonvac_hγ : (2 : ZMod 17) ^ 2 ^ (3 - 1) = -1 := by decide

theorem nonvac_flat : ∀ pos : Fin 8, FlatFri (3 : ZMod 17) 2 3 1 (fun w g => if w = 0 then 3 * 2 ^ g else 5)
    (fun i => if i = 0 then 5 else 7) (fun _ => 5) pos := by
  decide +kernel

end NonVac

end NockvmE2E.Exec.SF
