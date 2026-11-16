/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/AxisTeleJ9.lean

Read off the gates `AxisChipJ9.axQ` (§3 of `AxisChipJ9.lean`):
  * inverses `invL · den(limbKey) = 1`, `invP · den(pathKey) = 1`, `invT · den(tagKey) = 1`;
  * service accumulator `accS`: init `isFT·(accS − (invL − mu·invT))`, step
    `(1 − isLT)·(next.accS − accS − (next.invL − next.mu·next.invT))`, terminal `isLT·(accS − pubAXs)`;
  * path accumulator `accP`: the same with term `(1 − z1a)·invP` and terminal `pubAXp`.

  So the service terminal is (limb consumes, weight `1`, every row) − (`TAG_ax` provides, weight `mu`), and the
  path terminal is the path consumes at weight `1 − z1a`.  The lists `axTagProvs` / `axPathReqs` drop the rows
  of zero activity; those rows contribute `0` to the telescope.  For the path list the weight `1` of a
  kept row is `1 − z1a = 1`, which uses G1 (`z1a` boolean, a base gate).

  * `axis_service_sumQ` (A), `axis_path_sumQ` (B): the list-sum forms at the `𝕂′` handle coins
    `κ = ((χ₃₃, χ₃₅), (χ₃₄, χ₃₆))`;
  * `axLists_chals_free` (C): the three lists read only the base trace (the coin / public slots of the base
    environment do not enter).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AxisTeleJ9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
open Module
open scoped Polynomial

noncomputable section

/-! ## 0. Generic helpers -/

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **A `𝕂′` key denominator is `compress` of the zero-padded lifted key** (any width `m ≥ |key|`). -/
theorem denKeyQ_evL (eK : Env K) (eF : Env F) (m : ℕ) (l : List (CoeffExpr F)) (hl : l.length ≤ m) :
    (HQ.denKeyQ δF l).ev δF eK eF =
      compress (TeleHQ.coinsQ δF eK) (liftRec (K := K) (L := 𝕂′) (AxisChipJ9.keyVecL (K := K) m l eF)) := by
  rw [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev]
  simp only [compress, Walk.rlc, TeleHQ.coinsQ, liftRec, AxisChipJ9.keyVecL, zero_add]
  congr 1
  have key : ∀ c ∈ Finset.range m, c ∉ Finset.range l.length →
      (Quad.mk (algebraMap F K δF) (eK.chal 33) (eK.chal 35)) ^ c *
        liftQ δF ((l.getD c (.const 0)).eval eF) = 0 := by
    intro c _ hc
    rw [Finset.mem_range, not_lt] at hc
    rw [List.getD_eq_default _ _ hc]
    simp [CoeffExpr.eval]
  rw [Finset.sum_subset (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hl)) key]
  exact Finset.sum_range _

end Den

/-! ## 1. Row facts on the axis chip -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (axisChipJ9 δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The `𝕂′` value of role pair `r, r + 1` at row `i`. -/
abbrev axQv {w : ℕ} (Q' : Fin w → F[X]) (r : ℕ) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((axEK δF b nodes orbit chals pubs Q' i).trace r) ((axEK δF b nodes orbit chals pubs Q' i).trace (r + 1))

/-- The `𝕂′` denominator of key `l` at row `i`. -/
abbrev axDen {w : ℕ} (Q' : Fin w → F[X]) (l : List (CoeffExpr F)) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF l).ev δF (axEK δF b nodes orbit chals pubs Q' i) (axEF b nodes orbit chals pubs Q' i)

/-- The `𝕂′` handle coins. -/
abbrev κ : IOCoins 𝕂′ := ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩

theorem axDen_eq (l : List (CoeffExpr F)) (m : ℕ) (hl : l.length ≤ m) (i : Fin n) :
    axDen δF b nodes orbit chals pubs Q l i =
      compress (κ δF chals) (liftRec (K := K) (L := 𝕂′) (keyVecL (K := K) m l (axEF b nodes orbit chals pubs Q i))) := by
  rw [axDen, denKeyQ_evL δF _ _ m l hl]
  simp only [TeleHQ.coinsQ, axEK_chal, κ]

theorem axEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (axEK δF b nodes orbit chals pubs Q i).traceNext r = (axEK δF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  TeleH.gather_next_T b _ _ _ (axEF_next δF b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The three `𝕂′` inverses** of the axis chip. -/
theorem ax_inv (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    axQv δF b nodes orbit chals pubs Q invL i = (axDen δF b nodes orbit chals pubs Q limbKey i)⁻¹ ∧
      axQv δF b nodes orbit chals pubs Q invP i = (axDen δF b nodes orbit chals pubs Q AxisChipJ9.pathKey i)⁻¹ ∧
      axQv δF b nodes orbit chals pubs Q invT i = (axDen δF b nodes orbit chals pubs Q tagKey i)⁻¹ := by
  have hg := ax_qgates δF b hn nodes orbit chals pubs Q hsat i
  refine ⟨?_, ?_, ?_⟩
  · have g := hg _ (by simp [axQ] : QE.sub (QE.mul δF (QE.var invL) (HQ.denKeyQ δF limbKey)) QE.one ∈ axQ δF)
    rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
    exact eq_inv_of_mul_eq_one_left g
  · have g := hg _ (by simp [axQ] : QE.sub (QE.mul δF (QE.var invP) (HQ.denKeyQ δF AxisChipJ9.pathKey)) QE.one ∈ axQ δF)
    rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
    exact eq_inv_of_mul_eq_one_left g
  · have g := hg _ (by simp [axQ] : QE.sub (QE.mul δF (QE.var invT) (HQ.denKeyQ δF tagKey)) QE.one ∈ axQ δF)
    rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
    exact eq_inv_of_mul_eq_one_left g

/-- **The service telescope**: `Σ_i (invLᵢ − muᵢ · invTᵢ) = (pub₀, pub₁)`. -/
theorem ax_teleS (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, (axQv δF b nodes orbit chals pubs Q invL i -
        liftQ δF ((axEF b nodes orbit chals pubs Q i).trace mu) * axQv δF b nodes orbit chals pubs Q invT i) =
      Quad.mk _ (pubs pubAXs) (pubs (pubAXs + 1)) := by
  have hg := ax_qgates δF b hn nodes orbit chals pubs Q hsat
  refine TeleHQ.qTelescope δF hn (fun i => (axEF b nodes orbit chals pubs Q i).trace isFT)
    (fun i => (axEF b nodes orbit chals pubs Q i).trace isLT)
    (fun i => axQv δF b nodes orbit chals pubs Q accS i) _ _
    (fun i => (ax_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (ax_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [axQ] : QE.scale (cv isFT) (QE.sub (QE.var accS) (sTerm true)) ∈ axQ δF)
    simp only [sTerm, ite_true, ev_scale, ev_sub, ev_var] at g
    simpa only [axQv, cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [axQ] : QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next accS) (QE.var accS))
      (sTerm false)) ∈ axQ δF)
    simp only [sTerm, Bool.false_eq_true, ite_false, ev_scale, ev_sub, ev_next, ev_var] at g
    simp only [notE, cv, nv, CoeffExpr.eval, axEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      axEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [axQv, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [axQ] : QE.scale (cv isLT) (QE.sub (QE.var accS) (QE.pub pubAXs)) ∈ axQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, axEK_pub, axEK_pub] at g
    simpa only [axQv, cv, CoeffExpr.eval] using g

/-- **The path telescope**: `Σ_i (1 − z1aᵢ) · invPᵢ = (pub₂, pub₃)`. -/
theorem ax_teleP (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, liftQ δF (1 - (axEF b nodes orbit chals pubs Q i).trace z1a) * axQv δF b nodes orbit chals pubs Q invP i =
      Quad.mk _ (pubs pubAXp) (pubs (pubAXp + 1)) := by
  have hg := ax_qgates δF b hn nodes orbit chals pubs Q hsat
  refine TeleHQ.qTelescope δF hn (fun i => (axEF b nodes orbit chals pubs Q i).trace isFT)
    (fun i => (axEF b nodes orbit chals pubs Q i).trace isLT)
    (fun i => axQv δF b nodes orbit chals pubs Q accP i) _ _
    (fun i => (ax_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (ax_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [axQ] : QE.scale (cv isFT) (QE.sub (QE.var accP) (pTerm true)) ∈ axQ δF)
    simp only [pTerm, ite_true, ev_scale, ev_sub, ev_var] at g
    simpa only [axQv, cv, notE, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [axQ] : QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next accP) (QE.var accP))
      (pTerm false)) ∈ axQ δF)
    simp only [pTerm, Bool.false_eq_true, ite_false, ev_scale, ev_sub, ev_next, ev_var] at g
    simp only [notE, cv, nv, CoeffExpr.eval, axEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      axEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [axQv, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [axQ] : QE.scale (cv isLT) (QE.sub (QE.var accP) (QE.pub pubAXp)) ∈ axQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, axEK_pub, axEK_pub] at g
    simpa only [axQv, cv, CoeffExpr.eval] using g

/-! ## 2. The list-sum forms -/

theorem limb_sum (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ((axLimbReqs b nodes orbit chals pubs Q).map fun r => (compress (κ δF chals) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ∑ i, axQv δF b nodes orbit chals pubs Q invL i := by
  simp only [axLimbReqs, List.map_map, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ax_inv δF b hn nodes orbit chals pubs Q hsat i).1, axDen_eq δF b hn nodes orbit chals pubs Q limbKey 8
    (by simp [limbKey]) i]

theorem tag_sum [DecidableEq F] (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ((axTagProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (κ δF chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      ∑ i, liftQ δF ((axEF b nodes orbit chals pubs Q i).trace mu) * axQv δF b nodes orbit chals pubs Q invT i := by
  unfold axTagProvs
  rw [sum_map_flatMap, Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : (axEF b nodes orbit chals pubs Q i).trace mu = 0
  · rw [if_pos hm, hm]
    simp
  · rw [if_neg hm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [(ax_inv δF b hn nodes orbit chals pubs Q hsat i).2.2, axDen_eq δF b hn nodes orbit chals pubs Q tagKey 8
      (by simp [tagKey]) i]

theorem path_sum [DecidableEq F] (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ((axPathReqs b nodes orbit chals pubs Q).map fun r => (compress (κ δF chals) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ∑ i, liftQ δF (1 - (axEF b nodes orbit chals pubs Q i).trace z1a) * axQv δF b nodes orbit chals pubs Q invP i := by
  unfold axPathReqs
  rw [sum_map_flatMap, Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hz : 1 - (axEF b nodes orbit chals pubs Q i).trace z1a = 0
  · rw [if_pos hz, hz]
    simp
  · rw [if_neg hz]
    have H := ax_rowEqs δF b hn nodes orbit chals pubs Q hsat i
    have h1 : 1 - (axEF b nodes orbit chals pubs Q i).trace z1a = 1 := by
      rcases (G1 H).2.2.1 with h0 | h0
      · rw [h0, sub_zero]
      · exact absurd (by rw [h0, sub_self]) hz
    rw [h1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, liftQ, map_one, one_mul]
    rw [(ax_inv δF b hn nodes orbit chals pubs Q hsat i).2.1, axDen_eq δF b hn nodes orbit chals pubs Q AxisChipJ9.pathKey 5
      (by simp [AxisChipJ9.pathKey]) i]

/-- **(A) The service balance**: limb consumes (weight `1`) minus `TAG_ax` provides (weight `mu`) is the
terminal `(pub₀, pub₁)`. -/
theorem axis_service_sumQ [DecidableEq F] (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((axLimbReqs b nodes orbit chals pubs Q).map fun r =>
        (compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ : IOCoins 𝕂′)
          (liftRec (L := 𝕂′) r))⁻¹).sum -
      ((axTagProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ :
          IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs AxisChipJ9.pubAXs) (pubs (AxisChipJ9.pubAXs + 1)) := by
  have hl := limb_sum δF b hn nodes orbit chals pubs Q hsat
  have ht := tag_sum δF b hn nodes orbit chals pubs Q hsat
  simp only [κ] at hl ht
  rw [hl, ht, ← Finset.sum_sub_distrib]
  exact ax_teleS δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj

/-- **(B) The path balance**: the path consumes (rows with `1 − z1a ≠ 0`, weight `1`) sum to `(pub₂, pub₃)`. -/
theorem axis_path_sumQ [DecidableEq F] (hsat : (axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((axPathReqs b nodes orbit chals pubs Q).map fun r =>
        (compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ : IOCoins 𝕂′)
          (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubs AxisChipJ9.pubAXp) (pubs (AxisChipJ9.pubAXp + 1)) := by
  have hp := path_sum δF b hn nodes orbit chals pubs Q hsat
  simp only [κ] at hp
  rw [hp]
  exact ax_teleP δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj

end Rows

/-! ## 3. (C) The lists are coin-free -/

section Free
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

theorem keyVecL_limb_congr (m : ℕ) {e e' : Env F} (ht : e.trace = e'.trace) :
    keyVecL (K := K) m limbKey e = keyVecL (K := K) m limbKey e' := by
  funext c
  simp only [keyVecL]
  rcases c with ⟨_ | _ | _ | _ | c, hc⟩ <;> simp [limbKey, CoeffExpr.eval, cv, congrFun ht]

theorem keyVecL_path_congr (m : ℕ) {e e' : Env F} (ht : e.trace = e'.trace) :
    keyVecL (K := K) m AxisChipJ9.pathKey e = keyVecL (K := K) m AxisChipJ9.pathKey e' := by
  funext c
  simp only [keyVecL]
  rcases c with ⟨_ | _ | _ | _ | c, hc⟩ <;> simp [AxisChipJ9.pathKey, CoeffExpr.eval, cv, congrFun ht]

theorem keyVecL_tag_congr (m : ℕ) {e e' : Env F} (ht : e.trace = e'.trace) :
    keyVecL (K := K) m tagKey e = keyVecL (K := K) m tagKey e' := by
  funext c
  simp only [keyVecL]
  rcases c with ⟨_ | _ | _ | _ | _ | _ | _ | _ | c, hc⟩ <;> simp [tagKey, CoeffExpr.eval, cv, congrFun ht]

/-- **(C)** The three axis lists read only the base trace: at `chals pubs` they equal the lists at the zero
coins / publics. -/
theorem axLists_chals_free [DecidableEq F] (chals pubs : ℕ → K) {w : ℕ} (Q' : Fin w → F[X]) :
    axLimbReqs b nodes orbit chals pubs Q' = axLimbReqs b nodes orbit (fun _ => 0) (fun _ => 0) Q' ∧
      axPathReqs b nodes orbit chals pubs Q' = axPathReqs b nodes orbit (fun _ => 0) (fun _ => 0) Q' ∧
      axTagProvs b nodes orbit chals pubs Q' = axTagProvs b nodes orbit (fun _ => 0) (fun _ => 0) Q' := by
  have ht : ∀ i, (axEF b nodes orbit chals pubs Q' i).trace =
      (axEF b nodes orbit (fun _ => (0 : K)) (fun _ => (0 : K)) Q' i).trace := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold axLimbReqs
    exact List.map_congr_left fun i _ => keyVecL_limb_congr 8 (ht i)
  · unfold axPathReqs
    refine List.flatMap_congr fun i _ => ?_
    rw [congrFun (ht i) z1a, keyVecL_path_congr (K := K) 5 (ht i)]
  · unfold axTagProvs
    refine List.flatMap_congr fun i _ => ?_
    rw [congrFun (ht i) mu, keyVecL_tag_congr (K := K) 8 (ht i)]

end Free

end

section Axioms
#print axioms denKeyQ_evL
#print axioms ax_inv
#print axioms ax_teleS
#print axioms ax_teleP
#print axioms axis_service_sumQ
#print axioms axis_path_sumQ
#print axioms axLists_chals_free
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.AxisTeleJ9
