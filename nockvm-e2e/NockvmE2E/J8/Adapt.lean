/-
two adapters
`RapAirJ → RapAirJ`, outside the audited files.

* `plusJ` (J+): public columns `P` as extra round-2 columns (`ι0 ⊕ P`, no fixed polynomial), `C+ = rename inl ∘ C`,
  `Acc+ χ M tr = Acc χ M (tr ∘ inl)`, summands pulled back along `tr ↦ tr ∘ inl`. `plusPR` is the `PubRead` of J+ whose
  `rd` reads the public columns; `rdC0` reads only the c0 (base) coordinate of each opened value.
* `minusJ` (J−): restriction to the present columns `p`; absent columns are extended by `0`
  (`C− = bind₁ (absent ↦ 0)`). Needs `hpre0`: an absent column with a fixed polynomial has fixed polynomial `0`.
-/
import NockvmE2E.J8.Deep
import NockvmE2E.J8.NonVac

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace NockvmE2E.J8

open NockvmE2E.Rap NockvmE2E.Succ

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]

/-! ## J+ : public columns -/

section Plus

variable (J : RapAirJ B K) (P : Type) [Fintype P] [DecidableEq P]

/-- The base trace of a J+ trace. -/
def plusMap : (J.ι0 ⊕ P → B[X]) → (J.ι0 → B[X]) := fun tr j => tr (Sum.inl j)

theorem plus_staged :
    ∀ Q : Coins J.Φ0 K → (J.ι0 ⊕ P → B[X]),
      TracesStaged J.Φ0 (Sum.elim J.colRound0 (fun _ : P => 2)) Q →
      TracesStaged J.Φ0 J.colRound0 (fun χ => plusMap J P (Q χ)) :=
  staged_colMap (Sum.elim J.colRound0 (fun _ : P => 2)) J.colRound0 Sum.inl (fun _ => rfl)
    (fun _ => (id : B[X] → B[X]))

/-- The J+ summand. -/
noncomputable def plusSummand
    (s : BadSummand J.Φ0 K (J.ι0 → B[X]) (TracesStaged J.Φ0 J.colRound0)) :
    BadSummand J.Φ0 K (J.ι0 ⊕ P → B[X]) (TracesStaged J.Φ0 (Sum.elim J.colRound0 (fun _ : P => 2))) :=
  pullback (plusMap J P) (plus_staged J P) s

/-- **J+**: `tp` is the table assigned to the public columns (they occur in no constraint, so any table);
`hcap` is the new `cap_m` (the width grows by `|P| * r`). -/
noncomputable def plusJ (tp : Fin J.T)
    (hcap : (Fintype.card J.ι0 + Fintype.card P) * J.r + 3 * (J.d - 1) ≤ 2 ^ 12) : RapAirJ B K where
  Φ0 := J.Φ0
  ι0 := J.ι0 ⊕ P
  fι := inferInstance
  dι := inferInstance
  colRound0 := Sum.elim J.colRound0 (fun _ => 2)
  hround := by rintro (j | _); exacts [J.hround j, le_rfl]
  hcoin := J.hcoin
  pre := Sum.elim J.pre (fun _ => none)
  Msg := J.Msg
  Mcode := J.Mcode
  fM := J.fM
  dM := J.dM
  dec := J.dec
  Acc χ M tr := J.Acc χ M (plusMap J P tr)
  Holds := J.Holds
  summands := J.summands.map (plusSummand J P)
  sound := by
    intro χ M tr h hs
    refine J.sound χ M (plusMap J P tr) h ?_
    intro s hs'
    exact hs (plusSummand J P s) (List.mem_map_of_mem hs')
  eps := by
    have := epsilonOf_map_pullback (plusMap J P) (plus_staged J P) J.summands
    show epsilonOf (J.summands.map (pullback (plusMap J P) (plus_staged J P))) ≤ _
    rw [this]; exact J.eps
  oneRound := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    have h0 := J.oneRound s0 hs0
    exact ⟨h0.ne, h0.same, h0.dep_le⟩
  H := J.H
  T := J.T
  Ht := J.Ht
  hHt := J.hHt
  ωt := J.ωt
  r := J.r
  off := J.off
  hoff := J.hoff
  tabC := Sum.elim J.tabC (fun _ => tp)
  ns := J.ns
  tabS := J.tabS
  d := J.d
  hd2 := J.hd2
  C χ M i := MvPolynomial.rename (Prod.map Sum.inl id) (J.C χ M i)
  hdeg χ M i := (MvPolynomial.totalDegree_rename_le _ _).trans (J.hdeg χ M i)
  hCreads M i χ χ' h := by
    simp only
    exact congrArg _ (J.hCreads M i χ χ' h)
  Pub := J.Pub
  StmtOK := J.StmtOK
  acc_of := by
    intro χ M tr hv hp hs hpre
    refine J.acc_of χ M (plusMap J P tr) (fun i x hx => ?_) hp hs (fun j c h => hpre (Sum.inl j) c h)
    have := hv i x hx
    rw [MvPolynomial.aeval_rename] at this
    exact this
  cap_ns := J.cap_ns
  cap_d := J.cap_d
  cap_m := by
    have h := hcap
    rw [← Fintype.card_sum] at h
    exact h
  cap_H := J.cap_H

/-- J+ has the same price. -/
theorem epsilonOf_plusJ (tp : Fin J.T)
    (hcap : (Fintype.card J.ι0 + Fintype.card P) * J.r + 3 * (J.d - 1) ≤ 2 ^ 12) :
    epsilonOf (plusJ J P tp hcap).summands = epsilonOf J.summands :=
  epsilonOf_map_pullback (plusMap J P) (plus_staged J P) J.summands

variable {J P}

/-- A reader of the c0 (base) coordinate only: `decB` decodes the base words `c0 (v i)`. -/
noncomputable def rdC0 (c0 : K → B) (decB : (P → B) → J.Msg) : (P → K) → J.Msg := fun v => decB (fun i => c0 (v i))

theorem rdC0_congr (c0 : K → B) (decB : (P → B) → J.Msg) {v v' : P → K}
    (h : ∀ i, c0 (v i) = c0 (v' i)) : rdC0 c0 decB v = rdC0 c0 decB v' :=
  congrArg decB (funext h)

end Plus

section PlusPR

variable {B K : Type} [Field B] [Fintype B] [DecidableEq B] [NonBinaryField K] [Fintype K] [DecidableEq K]
  [Algebra B K] {J : RapAirJ B K} {P : Type} [Fintype P] [DecidableEq P]

/-- The public-column `PubRead` of J+: `rdP` reads the opened values of the public columns. -/
noncomputable def plusPR {tp : Fin J.T} {hcap} (ppt : P → K) (gen : K) (rdP : (P → K) → J.Msg) :
    PubRead (plusJ J P tp hcap) where
  pub := Sum.elim (fun _ => false) (fun _ => true)
  ppt := Sum.elim (fun _ => 0) ppt
  rd v := rdP (fun i => v (Sum.inr i))
  gen := gen
  hrd v v' h := congrArg rdP (funext fun i => h (Sum.inr i) rfl)
  hCpub := by
    intro χ M i p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hp)
    rfl

end PlusPR

/-! ## J− : present columns only -/

section Minus

/-- A polynomial of total degree `≤ 1` in each substituted variable does not raise the degree. -/
theorem totalDegree_bind₁_le {σ τ : Type} (φ : σ → MvPolynomial τ B) (hφ : ∀ s, (φ s).totalDegree ≤ 1)
    (f : MvPolynomial σ B) : (MvPolynomial.bind₁ φ f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left (m i) (hφ i))) ?_
  simpa [Finsupp.sum] using MvPolynomial.le_totalDegree (Finsupp.mem_support_iff.mp hm |> fun _ => hm)

variable (J : RapAirJ B K) (p : J.ι0 → Prop) [DecidablePred p]

/-- The present columns. -/
abbrev PresentCols : Type := {j : J.ι0 // p j}

/-- Extend a present trace by `0` on the absent columns. -/
noncomputable def extZ (tr : PresentCols J p → B[X]) : J.ι0 → B[X] :=
  fun j => if h : p j then tr ⟨j, h⟩ else 0

theorem minus_staged :
    ∀ Q : Coins J.Φ0 K → (PresentCols J p → B[X]),
      TracesStaged J.Φ0 (fun j : PresentCols J p => J.colRound0 j.1) Q →
      TracesStaged J.Φ0 J.colRound0 (fun χ => extZ J p (Q χ)) := by
  intro Q hQ j χ χ' h
  show extZ J p (Q χ) j = extZ J p (Q χ') j
  by_cases hj : p j
  · simp only [extZ, hj, dite_true]
    exact hQ ⟨j, hj⟩ χ χ' h
  · simp [extZ, hj]

/-- The J− summand. -/
noncomputable def minusSummand
    (s : BadSummand J.Φ0 K (J.ι0 → B[X]) (TracesStaged J.Φ0 J.colRound0)) :
    BadSummand J.Φ0 K (PresentCols J p → B[X])
      (TracesStaged J.Φ0 (fun j : PresentCols J p => J.colRound0 j.1)) :=
  pullback (extZ J p) (minus_staged J p) s

/-- Absent variables go to `0`, present ones to themselves. -/
noncomputable def minusSub : J.ι0 × Fin J.r → MvPolynomial (PresentCols J p × Fin J.r) B :=
  fun q => if h : p q.1 then MvPolynomial.X (⟨q.1, h⟩, q.2) else 0

theorem minusSub_deg (q : J.ι0 × Fin J.r) : (minusSub J p q).totalDegree ≤ 1 := by
  unfold minusSub
  split_ifs
  · simp
  · simp

/-- The composed constraint of `C−` at a present trace is the composed constraint of `C` at its extension. -/
theorem compose_minus (f : MvPolynomial (J.ι0 × Fin J.r) B) (tr : PresentCols J p → B[X]) :
    MvPolynomial.aeval (fun q : PresentCols J p × Fin J.r =>
      (tr q.1).comp (Polynomial.C (J.off (J.tabC q.1.1) q.2) * Polynomial.X))
      (MvPolynomial.bind₁ (minusSub J p) f) =
    MvPolynomial.aeval (fun q : J.ι0 × Fin J.r =>
      (extZ J p tr q.1).comp (Polynomial.C (J.off (J.tabC q.1) q.2) * Polynomial.X)) f := by
  rw [MvPolynomial.aeval_bind₁]
  congr 2
  funext q
  by_cases hq : p q.1
  · simp [minusSub, extZ, hq]
  · simp [minusSub, extZ, hq]

/-- **J−**: restrict to the present columns `p`, absent columns `:= 0`. `hpre0`: an absent fixed column is `0`.
Not for J-8: `hpre0` is false there and the DAG side needs a table restriction; use `minusT` (J8/MinusT.lean). -/
noncomputable def minusJ (hpre0 : ∀ j, ¬ p j → ∀ c, J.pre j = some c → c = 0) : RapAirJ B K where
  Φ0 := J.Φ0
  ι0 := PresentCols J p
  fι := inferInstance
  dι := inferInstance
  colRound0 j := J.colRound0 j.1
  hround j := J.hround j.1
  hcoin := J.hcoin
  pre j := J.pre j.1
  Msg := J.Msg
  Mcode := J.Mcode
  fM := J.fM
  dM := J.dM
  dec := J.dec
  Acc χ M tr := J.Acc χ M (extZ J p tr)
  Holds := J.Holds
  summands := J.summands.map (minusSummand J p)
  sound := by
    intro χ M tr h hs
    refine J.sound χ M (extZ J p tr) h ?_
    intro s hs'
    exact hs (minusSummand J p s) (List.mem_map_of_mem hs')
  eps := by
    have := epsilonOf_map_pullback (extZ J p) (minus_staged J p) J.summands
    show epsilonOf (J.summands.map (pullback (extZ J p) (minus_staged J p))) ≤ _
    rw [this]; exact J.eps
  oneRound := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    have h0 := J.oneRound s0 hs0
    exact ⟨h0.ne, h0.same, h0.dep_le⟩
  H := J.H
  T := J.T
  Ht := J.Ht
  hHt := J.hHt
  ωt := J.ωt
  r := J.r
  off := J.off
  hoff := J.hoff
  tabC j := J.tabC j.1
  ns := J.ns
  tabS := J.tabS
  d := J.d
  hd2 := J.hd2
  C χ M i := MvPolynomial.bind₁ (minusSub J p) (J.C χ M i)
  hdeg χ M i := (totalDegree_bind₁_le _ (minusSub_deg J p) _).trans (J.hdeg χ M i)
  hCreads M i χ χ' h := by
    simp only
    exact congrArg _ (J.hCreads M i χ χ' h)
  Pub := J.Pub
  StmtOK := J.StmtOK
  acc_of := by
    intro χ M tr hv hp hs hpre
    refine J.acc_of χ M (extZ J p tr) (fun i x hx => ?_) hp hs ?_
    · have := hv i x hx
      rw [compose_minus] at this
      exact this
    · intro j c h
      by_cases hj : p j
      · simp only [extZ, hj, dite_true]
        exact hpre ⟨j, hj⟩ c h
      · simp only [extZ, hj, dite_false]
        exact (hpre0 j hj c h).symm
  cap_ns := J.cap_ns
  cap_d := J.cap_d
  cap_m := by
    refine le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _) J.cap_m
    exact Fintype.card_subtype_le _
  cap_H := J.cap_H

theorem epsilonOf_minusJ (hpre0 : ∀ j, ¬ p j → ∀ c, J.pre j = some c → c = 0) :
    epsilonOf (minusJ J p hpre0).summands = epsilonOf J.summands :=
  epsilonOf_map_pullback (extZ J p) (minus_staged J p) J.summands

end Minus

/-! ## Non-vacuity: the toy interface, J+ then J− (which removes the public column again) -/

namespace ToyAdapt

open NockvmE2E.J8.Toy

theorem hcapT : (Fintype.card toy.ι0 + Fintype.card Unit) * toy.r + 3 * (toy.d - 1) ≤ 2 ^ 12 := by
  show (1 + 1) * 1 + 3 * (0 - 1) ≤ 2 ^ 12
  norm_num

/-- J+ of the toy: one extra (public) round-2 column. -/
noncomputable def toyPlus : RapAirJ (ZMod 2) (ZMod 2) := plusJ toy Unit (0 : Fin 1) hcapT

/-- Only the base column is present. -/
def presT : toyPlus.ι0 → Prop := fun j => Sum.isLeft (show Unit ⊕ Unit from j) = true

instance : DecidablePred presT := fun j => inferInstanceAs (Decidable (Sum.isLeft (show Unit ⊕ Unit from j) = true))

theorem hpre0T : ∀ j, ¬ presT j → ∀ c, toyPlus.pre j = some c → c = 0 := by
  intro j _ c h
  rcases j with j | j <;> simp [toyPlus, plusJ, toy] at h

/-- J− of J+ of the toy: a one-column interface again, with an absent column. -/
noncomputable def toyMinus : RapAirJ (ZMod 2) (ZMod 2) := minusJ toyPlus presT hpre0T

/-- Both adapters preserve the price and the fields (instantiated). -/
theorem toyPlus_eps : epsilonOf toyPlus.summands = epsilonOf toy.summands := epsilonOf_plusJ _ _ _ _

theorem toyMinus_eps : epsilonOf toyMinus.summands = epsilonOf toyPlus.summands := epsilonOf_minusJ _ _ _

/-- The extension really sees the absent column as `0`. -/
theorem toyMinus_ext (tr : PresentCols toyPlus presT → (ZMod 2)[X]) :
    extZ toyPlus presT tr (Sum.inr ()) = 0 := by
  have h : ¬ presT (Sum.inr ()) := by show ¬ ((Sum.inr () : Unit ⊕ Unit).isLeft = true); decide
  simp [extZ, h]

theorem toyMinus_card : Fintype.card toyMinus.ι0 = 1 := by
  show Fintype.card (PresentCols toyPlus presT) = 1
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨Sum.inl (), rfl⟩, fun ⟨j, hj⟩ => Subtype.ext ?_⟩
  rcases j with j | j
  · rfl
  · exact absurd hj (by show ¬ ((Sum.inr j : Unit ⊕ Unit).isLeft = true); simp)

theorem toyPlus_card : Fintype.card toyPlus.ι0 = 2 := rfl

/-- `rd` reads the c0 coordinate only. -/
theorem rdC0_toy (v v' : Unit → ZMod 2) (h : ∀ i, v i = v' i) :
    rdC0 (P := Unit) (J := toy) id (fun _ => ()) v = rdC0 id (fun _ => ()) v' := rdC0_congr _ _ h

/- J+ with its `PubRead` over `ZMod 17` (the `PubRead` needs a non-binary coin field): `toyP` plus one extra
public column read through `rdC0`. -/
section PR17

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem hcapP : (Fintype.card toyP.ι0 + Fintype.card Unit) * toyP.r + 3 * (toyP.d - 1) ≤ 2 ^ 12 := by
  show (2 + 1) * 1 + 3 * (1 - 1) ≤ 2 ^ 12
  norm_num

noncomputable def toyPPlus : RapAirJ (ZMod 17) (ZMod 17) := plusJ toyP Unit (0 : Fin 1) hcapP

noncomputable def toyPPlusPR : PubRead (plusJ toyP Unit (0 : Fin 1) hcapP) :=
  plusPR (tp := (0 : Fin 1)) (hcap := hcapP) (fun _ => 5) 1
    (rdC0 (J := toyP) (P := Unit) id (fun _ => (0 : ZMod 17)))

end PR17

end ToyAdapt

end NockvmE2E.J8

#print axioms NockvmE2E.J8.plusJ
#print axioms NockvmE2E.J8.epsilonOf_plusJ
#print axioms NockvmE2E.J8.plusPR
#print axioms NockvmE2E.J8.minusJ
#print axioms NockvmE2E.J8.epsilonOf_minusJ
#print axioms NockvmE2E.J8.totalDegree_bind₁_le
#print axioms NockvmE2E.J8.compose_minus
#print axioms NockvmE2E.J8.ToyAdapt.toyMinus
#print axioms NockvmE2E.J8.ToyAdapt.toyMinus_eps
#print axioms NockvmE2E.J8.ToyAdapt.toyMinus_card
#print axioms NockvmE2E.J8.ToyAdapt.toyPPlusPR
