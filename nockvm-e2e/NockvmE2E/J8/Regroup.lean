/-
the regroup of J-8's coordinate constraints into the DAG's K-gates.
`P.regroup G b` sums the J-constraints of one K-gate with the coordinate basis `b`; `regroup_vanish` transports vanishing back;
`hlink_regroup` is `hlink_J` for the regrouped parameters.
-/
import NockvmE2E.J8.Deep
import NockvmE2E.Exec.Field
import NockvmE2E.J8.NonVac

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open Polynomial
open scoped NNReal

namespace NockvmE2E.J8
open NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.Succ Fri.Spec Domain

/-! ## E. the regroup (K-gates vs J-8's coordinate gates) -/

structure Regroup (ns nsK : ℕ) where
  grp : Fin ns → Fin nsK
  crd : Fin ns → Fin 3
  hinj : ∀ j j', grp j = grp j' → crd j = crd j' → j = j'

section RG
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}

noncomputable def _root_.NockvmE2E.Rap.DeepParams.regroup (P : DeepParams Φ K ι β colRound) {nsK : ℕ} (G : Regroup P.ns nsK) (b : Fin 3 → K) :
    DeepParams Φ K ι β colRound :=
  { P with
    ns := nsK
    Cp := fun χ tr i => ∑ j ∈ Finset.univ.filter (fun j => G.grp j = i), C (b (G.crd j)) * P.Cp χ tr j
    hC := fun χ tr i => by
      refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      exact natDegree_C_mul_le _ _ |>.trans (P.hC χ tr j)
    hCcoin := fun χ χ' h => by funext tr i; simp only [P.hCcoin χ χ' h] }

noncomputable def _root_.NockvmE2E.Deep.AirShape.regroup {P : DeepParams Φ K ι β colRound} {r : ℕ} (A : AirShape P r) {nsK : ℕ}
    (G : Regroup P.ns nsK) (b : Fin 3 → K) : AirShape (P.regroup G b) r where
  off := A.off
  pt := A.pt
  Cv χ y i v := ∑ j ∈ Finset.univ.filter (fun j => G.grp j = (show Fin nsK from i)), b (G.crd j) * A.Cv χ y j v
  hCv χ tr i y := by
    show eval y (∑ j ∈ Finset.univ.filter (fun j => G.grp j = (show Fin nsK from i)), C (b (G.crd j)) * P.Cp χ tr j) = _
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [eval_mul, eval_C, A.hCv]; rfl

/-- the types the residual links mention do not change: `RestJ`/`RestVJ`/`hRest_J` are reused verbatim -/
example (P : DeepParams Φ K ι β colRound) {nsK : ℕ} (G : Regroup P.ns nsK) (b : Fin 3 → K) :
    DeepTr (P.regroup G b) = DeepTr P := rfl
example (P : DeepParams Φ K ι β colRound) {nsK : ℕ} (G : Regroup P.ns nsK) (b : Fin 3 → K) {r : ℕ}
    (R0 : RapStatement Φ K ι β colRound) : DeepFin (P.regroup G b) (r := r) R0 = DeepFin P (r := r) R0 := rfl
example [Fintype ι] (P : DeepParams Φ K ι β colRound) {nsK : ℕ} (G : Regroup P.ns nsK) (b : Fin 3 → K) {r : ℕ}
    (A : AirShape P r) (R0 : RapStatement Φ K ι β colRound) (χ : Coins Φ K) (fin : DeepFin P (r := r) R0) :
    deepClaims (P.regroup G b) (A.regroup G b) R0 χ fin = deepClaims P A R0 χ fin := rfl

/-- **Vanishing transport**: the regrouped constraints vanish on `H` ⇒ every original one does (values on `H` in
the base field, `b` independent over it) -/
theorem regroup_vanish {B : Type} [Field B] [Algebra B K] (P : DeepParams Φ K ι β colRound) {nsK : ℕ}
    (G : Regroup P.ns nsK) (b : Fin 3 → K)
    (hb : ∀ c : Fin 3 → B, (∀ k, (∀ j, G.crd j ≠ k) → c k = 0) → ∑ k, algebraMap B K (c k) * b k = 0 → ∀ k, c k = 0)
    (χ : Coins Φ K) (tr : ι → β)
    (hbase : ∀ j, ∀ x ∈ P.H, ∃ c : B, eval x (P.Cp χ tr j) = algebraMap B K c)
    (h : ∀ i, ∀ x ∈ P.H, eval x ((P.regroup G b).Cp χ tr i) = 0) :
    ∀ j, ∀ x ∈ P.H, eval x (P.Cp χ tr j) = 0 := by
  classical
  intro j x hx
  choose c hc using fun j' => hbase j' x hx
  -- the coordinate vector of group `grp j`
  let cv : Fin 3 → B := fun k =>
    if h : ∃ j' : Fin P.ns, G.grp j' = G.grp j ∧ G.crd j' = k then c (Classical.choose h) else 0
  have hsum : ∑ k, algebraMap B K (cv k) * b k = 0 := by
    have h0 := h (G.grp j) x hx
    change eval x (∑ j' ∈ Finset.univ.filter (fun j' => G.grp j' = G.grp j), C (b (G.crd j')) * P.Cp χ tr j') = 0 at h0
    rw [eval_finsetSum] at h0
    set S := Finset.univ.filter (fun j' => G.grp j' = G.grp j) with hS
    have hcv : ∀ j' ∈ S, cv (G.crd j') = c j' := by
      intro j' hj'
      have hj'' : G.grp j' = G.grp j := (Finset.mem_filter.mp hj').2
      have hex : ∃ j'' : Fin P.ns, G.grp j'' = G.grp j ∧ G.crd j'' = G.crd j' := ⟨j', hj'', rfl⟩
      have he : Classical.choose hex = j' :=
        G.hinj _ _ ((Classical.choose_spec hex).1.trans hj''.symm) (Classical.choose_spec hex).2
      simp only [cv, dif_pos hex, he]
    have hinjS : Set.InjOn G.crd (S : Set (Fin P.ns)) := fun a ha a' ha' e =>
      G.hinj a a' (((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp ha').2).symm) e
    rw [← Finset.sum_subset (Finset.subset_univ (S.image G.crd)) (fun k _ hk => by
        have : cv k = 0 := by
          simp only [cv]
          rw [dif_neg]
          rintro ⟨j', h1, h2⟩
          exact hk (Finset.mem_image.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩)
        rw [this, map_zero, zero_mul]),
      Finset.sum_image (fun a ha a' ha' e => hinjS ha ha' e)]
    rw [← h0]
    refine Finset.sum_congr rfl (fun j' hj' => ?_)
    rw [hcv j' hj', eval_mul, eval_C, hc j', mul_comm]
  have hk := hb cv (fun k hk => by
    simp only [cv]
    rw [dif_neg]
    rintro ⟨j', _, h2⟩
    exact hk j' h2) hsum (G.crd j)
  have hex : ∃ j' : Fin P.ns, G.grp j' = G.grp j ∧ G.crd j' = G.crd j := ⟨j, rfl, rfl⟩
  have hj' : Classical.choose hex = j :=
    G.hinj _ _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
  simp only [cv, dif_pos hex, hj'] at hk
  rw [hc j, hk, map_zero]

end RG

section Link
variable {B K : Type} [Field B] [Fintype B] [DecidableEq B] [NonBinaryField K] [Fintype K] [DecidableEq K]
  [Algebra B K] {n : ℕ} (J : RapAirJ B K) (pr : PubRead J) (ω : SmoothCosetFftDomain n K) (δ : ℝ≥0) (N : ℕ)
  (hNH : N ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)

/-- the `deepParamsJ` constraint polynomials take base-field values on the trace domain -/
theorem hbase_deepParamsJ (χ : Coins (extFrame J.Φ0 2) K) (tr : DeepTr (deepParamsJ J pr ω δ N hNH hpd))
    (j : Fin (deepParamsJ J pr ω δ N hNH hpd).ns) :
    ∀ x ∈ (deepParamsJ J pr ω δ N hNH hpd).H,
      ∃ c : B, eval x ((deepParamsJ J pr ω δ N hNH hpd).Cp χ ((deepParamsJ J pr ω δ N hNH hpd).restr tr) j) =
        algebraMap B K c := by
  intro x hx
  obtain ⟨x0, _, rfl⟩ := (mem_HK J).1 hx
  refine ⟨eval x0 (J.compose (restr 2 χ) (preadJ J pr ω δ N ((deepParamsJ J pr ω δ N hNH hpd).restr tr))
    ((wmJ J ω δ N).base ((deepParamsJ J pr ω δ N hNH hpd).restr tr)) j *
      Zout J.H (J.Ht (J.tabS j))), ?_⟩
  exact eval_map_algebraMap _ _ |>.trans (by simp [Polynomial.aeval_def, eval₂_at_apply])

/-- **`hlink` for the regrouped parameters**: `hlink_J` composed with `regroup_vanish`. -/
theorem hlink_regroup {nsK : ℕ} (G : Regroup (deepParamsJ J pr ω δ N hNH hpd).ns nsK) (b : Fin 3 → K)
    (hb : ∀ c : Fin 3 → B, (∀ k, (∀ j, G.crd j ≠ k) → c k = 0) → ∑ k, algebraMap B K (c k) * b k = 0 → ∀ k, c k = 0) :
    ∀ m0 (tr : DeepTr ((deepParamsJ J pr ω δ N hNH hpd).regroup G b)) fin χ,
      RestJ J pr ω δ N hNH hpd m0 tr fin χ →
      (∀ i, ∀ x ∈ ((deepParamsJ J pr ω δ N hNH hpd).regroup G b).H,
        eval x (((deepParamsJ J pr ω δ N hNH hpd).regroup G b).Cp χ
          (((deepParamsJ J pr ω δ N hNH hpd).regroup G b).restr tr) i) = 0) →
      (R0J J pr ω δ N).Accepts m0 (((deepParamsJ J pr ω δ N hNH hpd).regroup G b).restr tr) fin χ := by
  intro m0 tr fin χ hr hv
  exact hlink_J J pr ω δ N hNH hpd m0 tr fin χ hr
    (regroup_vanish _ G b hb χ _ (hbase_deepParamsJ J pr ω δ N hNH hpd χ tr) hv)

end Link

/-- the basis `(1, xr, xr²)` is independent over the prime field -/
theorem gb_indep : ∀ c : Fin 3 → ZMod NockvmE2E.Exec.p,
    ∑ k, algebraMap (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC (c k) *
      (![1, NockvmE2E.Exec.xr, NockvmE2E.Exec.xr ^ 2] : Fin 3 → NockvmE2E.Exec.KC) k = 0 → ∀ k, c k = 0 := by
  intro c h k
  simp only [Fin.sum_univ_three] at h
  have := NockvmE2E.Exec.K3.coords_eq_zero (c 0) (c 1) (c 2) (by simpa using h)
  fin_cases k
  · exact this.1
  · exact this.2.1
  · exact this.2.2

/-- the full-independence form implies the restricted one `hlink_regroup` takes -/
theorem hb_weak {B K : Type} [Field B] [Field K] [Algebra B K] {ns nsK : ℕ} (G : Regroup ns nsK) (b : Fin 3 → K)
    (h : ∀ c : Fin 3 → B, ∑ k, algebraMap B K (c k) * b k = 0 → ∀ k, c k = 0) :
    ∀ c : Fin 3 → B, (∀ k, (∀ j, G.crd j ≠ k) → c k = 0) → ∑ k, algebraMap B K (c k) * b k = 0 → ∀ k, c k = 0 :=
  fun c _ => h c

/-! ## Witness: `toy2` (J8/NonVac.lean) with the identity regroup -/

section Witness
open NockvmE2E.J8.Toy

/-- identity regroup: `grp = id`, `crd = 0` -/
def toy2G : Regroup (deepParamsJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd).ns 2 where
  grp := fun j => j
  crd := fun _ => 0
  hinj := fun _ _ h _ => h

theorem toy2_hb : ∀ c : Fin 3 → ZMod 17, (∀ k, (∀ j, toy2G.crd j ≠ k) → c k = 0) →
    ∑ k, algebraMap (ZMod 17) (ZMod 17) (c k) * (fun _ : Fin 3 => (1 : ZMod 17)) k = 0 → ∀ k, c k = 0 := by
  intro c h0 h k
  have h1 : c 1 = 0 := h0 1 (fun _ => by simp [toy2G])
  have h2 : c 2 = 0 := h0 2 (fun _ => by simp [toy2G])
  simp only [Fin.sum_univ_three, h1, h2, Algebra.algebraMap_self, RingHom.id_apply, mul_one, add_zero] at h
  fin_cases k
  · exact h
  · exact h1
  · exact h2

set_option linter.defProp false in
/-- `hlink_regroup` instantiated at `toy2` -/
noncomputable def toy2_hlink_regroup := hlink_regroup toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd toy2G
  (fun _ => 1) toy2_hb

end Witness

end NockvmE2E.J8

#print axioms NockvmE2E.J8.regroup_vanish
#print axioms NockvmE2E.J8.hbase_deepParamsJ
#print axioms NockvmE2E.J8.hlink_regroup
#print axioms NockvmE2E.J8.gb_indep
#print axioms NockvmE2E.J8.toy2_hlink_regroup
