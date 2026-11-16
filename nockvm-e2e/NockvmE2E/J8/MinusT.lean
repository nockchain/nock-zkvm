import NockvmE2E.J8.Adapt

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace NockvmE2E.J8

open NockvmE2E.Rap NockvmE2E.Succ

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]

/-- **`hfree`**: `J` accepts as soon as the constraints of the tables in `q` vanish (on their `H_t`), `Pub`, `StmtOK`
hold and the fixed columns of the tables in `q` are bound. Nothing is asked of a table outside `q`. -/
def RapAirJ.AccOn (J : RapAirJ B K) (q : Fin J.T → Prop) : Prop :=
  ∀ (χ : Coins J.Φ0 K) (M : J.Msg) (tr : J.ι0 → B[X]),
    (∀ i, q (J.tabS i) → ∀ x ∈ J.Ht (J.tabS i), (J.compose χ M tr i).eval x = 0) →
    J.Pub χ M → J.StmtOK → (∀ j c, q (J.tabC j) → J.pre j = some c → tr j = c) → J.Acc χ M tr

/-- every interface has `AccOn ⊤` (it is `acc_of`) -/
theorem RapAirJ.accOn_top (J : RapAirJ B K) : J.AccOn (fun _ => True) :=
  fun χ M tr h hp hs hpre => J.acc_of' χ M tr (fun i => h i trivial) hp hs (fun j c => hpre j c trivial)

/-- `AccOn q` is monotone: fewer present tables = a stronger statement -/
theorem RapAirJ.AccOn.mono (J : RapAirJ B K) {q q' : Fin J.T → Prop} (hqq : ∀ t, q t → q' t) (h : J.AccOn q) :
    J.AccOn q' :=
  fun χ M tr hv hp hs hpre => h χ M tr (fun i hi => hv i (hqq _ hi)) hp hs (fun j c hj => hpre j c (hqq _ hj))

/-- The present tables of `J`, in the order `σ` (the flat table order), and the present constraints `ρ`. -/
structure TabRestr (J : RapAirJ B K) where
  T' : ℕ
  σ : Fin T' → Fin J.T
  p : J.ι0 → Prop
  dp : DecidablePred p
  hp : ∀ j, p j ↔ ∃ t, σ t = J.tabC j
  ns' : ℕ
  ρ : Fin ns' → Fin J.ns
  hρ : Function.Injective ρ
  tabS' : Fin ns' → Fin T'
  hρtab : ∀ i, σ (tabS' i) = J.tabS (ρ i)
  hρcov : ∀ i t, σ t = J.tabS i → ∃ i', ρ i' = i

attribute [instance] TabRestr.dp

/-- the present tables as a predicate on `Fin J.T` -/
def TabRestr.q {J : RapAirJ B K} (R : TabRestr J) : Fin J.T → Prop := fun t => ∃ t', R.σ t' = t

/-- the identity restriction (all tables present) -/
def TabRestr.id (J : RapAirJ B K) : TabRestr J where
  T' := J.T
  σ := fun t => t
  p := fun _ => True
  dp := fun _ => instDecidableTrue
  hp := fun j => ⟨fun _ => ⟨J.tabC j, rfl⟩, fun _ => trivial⟩
  ns' := J.ns
  ρ := fun i => i
  hρ := fun _ _ h => h
  tabS' := J.tabS
  hρtab := fun _ => rfl
  hρcov := fun i _ _ => ⟨i, rfl⟩

section MinusT
variable (J : RapAirJ B K) (R : TabRestr J)

/-- the table of a present column -/
noncomputable def TabRestr.tabC' (j : PresentCols J R.p) : Fin R.T' := Classical.choose ((R.hp j.1).1 j.2)

theorem TabRestr.σ_tabC' (j : PresentCols J R.p) : R.σ (R.tabC' J j) = J.tabC j.1 :=
  Classical.choose_spec ((R.hp j.1).1 j.2)

/-- **J− (table restriction)**: the present tables `σ`, their columns `R.p`, their constraints `ρ`. Absent columns
are extended by `0` (`extZ`), but nothing of them is used: `hfree` says `J` asks nothing of the absent tables. -/
noncomputable def minusT (hfree : J.AccOn R.q) : RapAirJ B K where
  Φ0 := J.Φ0
  ι0 := PresentCols J R.p
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
  Acc χ M tr := J.Acc χ M (extZ J R.p tr)
  Holds := J.Holds
  summands := J.summands.map (minusSummand J R.p)
  sound := by
    intro χ M tr h hs
    refine J.sound χ M (extZ J R.p tr) h ?_
    intro s hs'
    exact hs (minusSummand J R.p s) (List.mem_map_of_mem hs')
  eps := by
    have := epsilonOf_map_pullback (extZ J R.p) (minus_staged J R.p) J.summands
    show epsilonOf (J.summands.map (pullback (extZ J R.p) (minus_staged J R.p))) ≤ _
    rw [this]; exact J.eps
  oneRound := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    have h0 := J.oneRound s0 hs0
    exact ⟨h0.ne, h0.same, h0.dep_le⟩
  H := J.H
  T := R.T'
  Ht t := J.Ht (R.σ t)
  hHt t := J.hHt (R.σ t)
  ωt t := J.ωt (R.σ t)
  r := J.r
  off t := J.off (R.σ t)
  hoff t := J.hoff (R.σ t)
  tabC := R.tabC' J
  ns := R.ns'
  tabS := R.tabS'
  d := J.d
  hd2 := J.hd2.imp id (fun h t => h (R.σ t))
  C χ M i := MvPolynomial.bind₁ (minusSub J R.p) (J.C χ M (R.ρ i))
  hdeg χ M i := (totalDegree_bind₁_le _ (minusSub_deg J R.p) _).trans (J.hdeg χ M (R.ρ i))
  hCreads M i χ χ' h := by
    simp only
    exact congrArg _ (J.hCreads M (R.ρ i) χ χ' h)
  Pub := J.Pub
  StmtOK := J.StmtOK
  acc_of := by
    intro χ M tr hv hp hs hpre
    refine hfree χ M (extZ J R.p tr) (fun i hi x hx => ?_) hp hs (fun j c hj h => ?_)
    · obtain ⟨t, ht⟩ := hi
      obtain ⟨i', rfl⟩ := R.hρcov i t ht
      have hx' : x ∈ J.Ht (R.σ (R.tabS' i')) := by rw [R.hρtab]; exact hx
      have := hv i' x hx'
      have hoffE : (fun q : PresentCols J R.p × Fin J.r =>
          (tr q.1).comp (Polynomial.C (J.off (R.σ (R.tabC' J q.1)) q.2) * Polynomial.X)) =
          (fun q : PresentCols J R.p × Fin J.r =>
          (tr q.1).comp (Polynomial.C (J.off (J.tabC q.1.1) q.2) * Polynomial.X)) := by
        funext q; rw [R.σ_tabC']
      rw [hoffE, compose_minus] at this
      exact this
    · have hpj : R.p j := (R.hp j).2 hj
      simp only [extZ, hpj, dite_true]
      exact hpre ⟨j, hpj⟩ c h
  cap_ns := by
    have h := Fintype.card_le_of_injective R.ρ R.hρ
    simp only [Fintype.card_fin] at h
    exact h.trans J.cap_ns
  cap_d := J.cap_d
  cap_m := by
    refine le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _) J.cap_m
    exact Fintype.card_subtype_le _
  cap_H := J.cap_H

theorem epsilonOf_minusT (hfree : J.AccOn R.q) :
    epsilonOf (minusT J R hfree).summands = epsilonOf J.summands :=
  epsilonOf_map_pullback (extZ J R.p) (minus_staged J R.p) J.summands

/-- the composed constraint of `minusT` = the composed `ρ`-constraint of `J` at the extension (for `htie`) -/
theorem compose_minusT (hfree : J.AccOn R.q) (χ : Coins J.Φ0 K) (M : J.Msg) (tr : PresentCols J R.p → B[X])
    (i : Fin R.ns') :
    (minusT J R hfree).compose χ M tr i = J.compose χ M (extZ J R.p tr) (R.ρ i) := by
  have hoffE : (fun q : PresentCols J R.p × Fin J.r =>
      (tr q.1).comp (Polynomial.C (J.off (R.σ (R.tabC' J q.1)) q.2) * Polynomial.X)) =
      (fun q : PresentCols J R.p × Fin J.r =>
      (tr q.1).comp (Polynomial.C (J.off (J.tabC q.1.1) q.2) * Polynomial.X)) := by
    funext q; rw [R.σ_tabC']
  exact (congrArg (fun f => MvPolynomial.aeval f (MvPolynomial.bind₁ (minusSub J R.p) (J.C χ M (R.ρ i)))) hoffE).trans
    (compose_minus J R.p _ tr)

/-- `aeval` of a `minusT` constraint at any valuation (the form `htie` evaluates) -/
theorem aeval_minusT_C {A : Type} [CommRing A] [Algebra B A] (hfree : J.AccOn R.q) (χ : Coins J.Φ0 K) (M : J.Msg)
    (i : Fin R.ns') (val : PresentCols J R.p × Fin J.r → A) :
    MvPolynomial.aeval val ((minusT J R hfree).C χ M i) =
      MvPolynomial.aeval (fun q : J.ι0 × Fin J.r => if h : R.p q.1 then val (⟨q.1, h⟩, q.2) else 0)
        (J.C χ M (R.ρ i)) := by
  show MvPolynomial.aeval val (MvPolynomial.bind₁ (minusSub J R.p) (J.C χ M (R.ρ i))) = _
  rw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun f => MvPolynomial.aeval f (J.C χ M (R.ρ i))) (funext fun q => ?_)
  by_cases hq : R.p q.1 <;> simp [minusSub, hq]

instance minusT_neZero (hfree : J.AccOn R.q) [NeZero J.r] : NeZero (minusT J R hfree).r :=
  inferInstanceAs (NeZero J.r)

end MinusT

/-! ## Non-vacuity -/

/-- `minusT` at every interface: the identity restriction -/
noncomputable def minusT_id (J : RapAirJ B K) : RapAirJ B K := minusT J (TabRestr.id J)
  (RapAirJ.AccOn.mono J (fun t _ => ⟨t, rfl⟩) J.accOn_top)

theorem minusT_id_eps (J : RapAirJ B K) : epsilonOf (minusT_id J).summands = epsilonOf J.summands :=
  epsilonOf_minusT _ _ _

/-! ### The absent-table shape: an absent table with a NONZERO fixed column; `hpre0` is false, `minusT` applies -/
namespace ToyAbs
open NockvmE2E.J8.Toy

/-- `toy2` with table 1 made "absent-free": column 1 is preprocessed to the constant `1` (like a first-row mask);
`Acc` asks only table 0 (col 0 vanishes on `Ht2 0`). -/
noncomputable def toyA : RapAirJ (ZMod 17) (ZMod 17) where
  Φ0 := Φ2
  ι0 := Fin 2
  fι := inferInstance
  dι := inferInstance
  colRound0 := fun _ => 0
  hround := fun _ => by norm_num
  hcoin := fun _ => by show 0 < 2; norm_num
  pre := fun j => if j = 1 then some (Polynomial.C 1) else none
  Msg := Unit
  Mcode := Unit
  fM := inferInstance
  dM := inferInstance
  dec := id
  Acc := fun _ _ tr => ∀ x ∈ Ht2 0, (MvPolynomial.aeval (fun p : Fin 2 × Fin 1 =>
    (tr p.1).comp (Polynomial.C 1 * Polynomial.X)) (MvPolynomial.X ((0 : Fin 2), (0 : Fin 1)) ^ 2)).eval x = 0
  Holds := True
  summands := [sum2]
  sound := fun _ _ _ _ _ => trivial
  eps := by simp [epsilonOf, sum2]
  oneRound := by
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨⟨0, by simp [sum2]⟩, by simp [sum2], by simp [sum2]⟩
  H := {1, 4, 16}
  T := 2
  Ht := Ht2
  hHt := fun t => by fin_cases t <;> decide
  ωt := fun _ => 1
  r := 1
  off := fun _ _ => 1
  hoff := by simp
  tabC := id
  ns := 2
  tabS := id
  d := 2
  hd2 := Or.inl le_rfl
  C := fun _ _ i => MvPolynomial.X (i, 0) ^ 2
  hdeg := fun _ _ i => by
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    simp
  hCreads := fun _ _ _ _ _ => rfl
  Pub := fun _ _ => True
  StmtOK := True
  acc_of := by
    intro χ M tr h _ _ _ x hx
    exact h 0 x hx
  cap_ns := by norm_num
  cap_d := by norm_num
  cap_m := by simp
  cap_H := by decide

theorem toyA_hpre0_false : ¬ (∀ j, ¬ (j = (0 : Fin 2)) → ∀ c, toyA.pre (show Fin 2 from j) = some c → c = 0) := by
  intro h
  have := h 1 (by decide) (Polynomial.C 1) (by simp [toyA])
  simp at this

/-- only table 0 is present -/
noncomputable def RA : TabRestr toyA where
  T' := 1
  σ := fun _ => (0 : Fin 2)
  p := fun j => (show Fin 2 from j) = 0
  dp := inferInstance
  hp := fun j => by
    show (show Fin 2 from j) = 0 ↔ ∃ _ : Fin 1, (0 : Fin 2) = j
    exact ⟨fun h => ⟨0, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  ns' := 1
  ρ := fun _ => (0 : Fin 2)
  hρ := fun a b _ => Subsingleton.elim a b
  tabS' := fun _ => (0 : Fin 1)
  hρtab := fun _ => rfl
  hρcov := fun i t h => ⟨0, by
    have : (0 : Fin 2) = i := h
    exact this⟩

theorem toyA_free : toyA.AccOn RA.q := by
  intro χ M tr h _ _ _ x hx
  exact h (0 : Fin 2) ⟨(0 : Fin 1), rfl⟩ x hx

noncomputable def toyAMinus : RapAirJ (ZMod 17) (ZMod 17) := minusT toyA RA toyA_free

theorem toyAMinus_T : toyAMinus.T = 1 := rfl
theorem toyAMinus_ns : toyAMinus.ns = 1 := rfl

theorem toyAMinus_card_le : Fintype.card toyAMinus.ι0 ≤ 2 := by
  show Fintype.card (PresentCols toyA RA.p) ≤ 2
  exact (Fintype.card_subtype_le _).trans (by simp [toyA])

theorem hcapAM : (Fintype.card toyAMinus.ι0 + Fintype.card Unit) * toyAMinus.r + 3 * (toyAMinus.d - 1) ≤ 2 ^ 12 := by
  have h := toyAMinus_card_le
  have hr : toyAMinus.r = 1 := rfl
  have hd : toyAMinus.d = 2 := rfl
  rw [hr, hd]
  simp only [Fintype.card_unit]
  omega

/-- `plusJ ∘ minusT` composes without casts, and the price is preserved. -/
noncomputable def toyAMinusPlus : RapAirJ (ZMod 17) (ZMod 17) := plusJ toyAMinus Unit (0 : Fin 1) hcapAM

theorem toyAMinusPlus_eps : epsilonOf toyAMinusPlus.summands = epsilonOf toyA.summands :=
  (epsilonOf_plusJ _ _ _ _).trans (epsilonOf_minusT toyA RA toyA_free)

end ToyAbs

end NockvmE2E.J8
#print axioms NockvmE2E.J8.minusT_neZero
#print axioms NockvmE2E.J8.minusT_id
#print axioms NockvmE2E.J8.minusT_id_eps
#print axioms NockvmE2E.J8.ToyAbs.toyA_free
#print axioms NockvmE2E.J8.ToyAbs.toyAMinusPlus
#print axioms NockvmE2E.J8.ToyAbs.toyAMinusPlus_eps
#print axioms NockvmE2E.J8.ToyAbs.toyAMinus_T
#print axioms NockvmE2E.J8.minusT
#print axioms NockvmE2E.J8.compose_minusT
#print axioms NockvmE2E.J8.aeval_minusT_C
#print axioms NockvmE2E.J8.ToyAbs.toyAMinus
#print axioms NockvmE2E.J8.ToyAbs.toyA_hpre0_false
#print axioms NockvmE2E.J8.epsilonOf_minusT
#print axioms NockvmE2E.J8.ToyAbs.toyAMinus_ns
#print axioms NockvmE2E.J8.ToyAbs.hcapAM
