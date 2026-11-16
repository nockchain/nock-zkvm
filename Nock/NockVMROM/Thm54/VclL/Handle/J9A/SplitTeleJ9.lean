/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/SplitTeleJ9.lean

The split chip's `𝕂′` gates (`SplitChipJ9.spQ`) are, at the handle coins `γ = (chal 33, chal 35)`,
  `ρ = (chal 34, chal 36)` (`HQ.gamQ`, `HQ.rhoQ`):
  * `inv2 · den(key2) − 1`, `inv3 · den(key3) − 1` (`den l = ρ + Σ_k γ^k · l_k`, `key2 = (id,2,0,lo)`,
    `key3 = (id,3,0,hi)`);
  * `isFT · (acc − m·(inv2 + inv3))`, `(1 − isLT) · (acc′ − acc − m′·(inv2′ + inv3′))`,
    `isLT · (acc − pub_{pubSPs})`.

  * `den8_eq`: a `𝕂′` key denominator of a key of length `≤ 8` is `compress` of the lifted zero-padded
    width-8 key (`keyVecL 8`);
  * `split_inv` (two inverses per row), `split_tele` (`Σ m·(inv2 + inv3) = (pub₀, pub₁)`);
  * **`split_provs_sumQ`**: the providers' weighted `𝕂′` sum (zero-activity rows dropped, two records per
    row) is the terminal;
  * **`splitProvs_chals_free`**: the provider list reads only the base trace (equal at `chals pubs` and at
    `0 0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SplitTeleJ9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (spEF spEK splitProvs keyVecL key2 key3 spQ splitChipJ9
  splitTemplateJ9 splitTemplateJ9_baseCols pTerm sp_qgates sp_masks pubSPs)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The width-8 denominator -/

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem rlc_keyVecL8 (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length ≤ 8) (γ : 𝕂′) :
    ∑ c ∈ Finset.range l.length, γ ^ c * liftQ δF ((l.getD c (.const 0)).eval eF) =
      Walk.rlc γ (liftRec (K := K) (L := 𝕂′) (keyVecL 8 l eF)) := by
  have h8 : (∑ c : Fin 8, γ ^ (c : ℕ) * liftRec (K := K) (L := 𝕂′) (keyVecL 8 l eF) c) =
      ∑ k ∈ Finset.range 8, γ ^ k * liftQ δF ((l.getD k (.const 0)).eval eF) :=
    Fin.sum_univ_eq_sum_range (fun k => γ ^ k * liftQ δF ((l.getD k (.const 0)).eval eF)) 8
  rw [Walk.rlc, h8]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hl) fun k _ hk => ?_
  have hk' : l.length ≤ k := by simpa using hk
  rw [List.getD_eq_default _ _ hk']
  simp [CoeffExpr.eval]

/-- **A `𝕂′` key denominator (key length `≤ 8`) is `compress` of the lifted width-8 key at the `𝕂′` coins.** -/
theorem den8_eq (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length ≤ 8) :
    (HQ.denKeyQ δF l).ev δF eK eF =
      compress (TeleHQ.coinsQ δF eK) (liftRec (K := K) (L := 𝕂′) (keyVecL 8 l eF)) := by
  rw [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev]
  simp only [zero_add]
  rw [rlc_keyVecL8 δF eF l hl]
  rfl

end Den

/-! ## 2. The split chip telescope -/

section Tele
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (nA : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The `𝕂′` value of role pair `r, r + 1` at row `i`. -/
abbrev sQ {w : ℕ} (Q' : Fin w → F[X]) (r : ℕ) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((spEK δF nA b nodes orbit chals pubs Q' i).trace r)
    ((spEK δF nA b nodes orbit chals pubs Q' i).trace (r + 1))

abbrev sDen {w : ℕ} (Q' : Fin w → F[X]) (l : List (CoeffExpr F)) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF l).ev δF (spEK δF nA b nodes orbit chals pubs Q' i) (spEF b nodes orbit chals pubs Q' i)

/-- The row term `m · (inv2 + inv3)`. -/
abbrev sTerm {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  liftQ δF ((spEF b nodes orbit chals pubs Q' i).trace SplitChipJ9.mult) *
    (sQ δF nA b nodes orbit chals pubs Q' SplitChipJ9.inv2 i + sQ δF nA b nodes orbit chals pubs Q' SplitChipJ9.inv3 i)

theorem spEK_pub (i : Fin n) (idx : ℕ) : (spEK δF nA b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (splitTemplateJ9 δF nA) 72 (splitTemplateJ9_baseCols δF nA) _ pubs rfl idx

theorem spEK_chal (i : Fin n) (idx : ℕ) : (spEK δF nA b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (splitTemplateJ9 δF nA) 72 (splitTemplateJ9_baseCols δF nA) _ chals rfl idx

theorem spEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (spEF b nodes orbit chals pubs Q i).traceNext j = (spEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem spEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (spEK δF nA b nodes orbit chals pubs Q i).traceNext r =
      (spEK δF nA b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (spEF_next δF nA b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The two `𝕂′` provide inverses of a split row.** -/
theorem split_inv (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (sDen δF nA b nodes orbit chals pubs Q key2 i ≠ 0 ∧
      sQ δF nA b nodes orbit chals pubs Q SplitChipJ9.inv2 i = (sDen δF nA b nodes orbit chals pubs Q key2 i)⁻¹) ∧
    (sDen δF nA b nodes orbit chals pubs Q key3 i ≠ 0 ∧
      sQ δF nA b nodes orbit chals pubs Q SplitChipJ9.inv3 i = (sDen δF nA b nodes orbit chals pubs Q key3 i)⁻¹) := by
  have hg := sp_qgates δF nA b hn nodes orbit chals pubs Q hsat i
  refine ⟨TeleHQ.inv_of_gate δF ?_, TeleHQ.inv_of_gate δF ?_⟩
  · have g := hg _ (by simp [spQ] : QE.sub (QE.mul δF (QE.var SplitChipJ9.inv2) (HQ.denKeyQ δF key2))
      QE.one ∈ spQ δF)
    rwa [ev_sub, ev_mul, ev_var, ev_one] at g
  · have g := hg _ (by simp [spQ] : QE.sub (QE.mul δF (QE.var SplitChipJ9.inv3) (HQ.denKeyQ δF key3))
      QE.one ∈ spQ δF)
    rwa [ev_sub, ev_mul, ev_var, ev_one] at g

/-- **The split telescope**: `Σ_i m_i · (inv2_i + inv3_i) = (pub_{pubSPs}, pub_{pubSPs+1})`. -/
theorem split_tele (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (splitChipJ9 δF nA b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, sTerm δF nA b nodes orbit chals pubs Q i = Quad.mk _ (pubs pubSPs) (pubs (pubSPs + 1)) := by
  have hg := sp_qgates δF nA b hn nodes orbit chals pubs Q hsat
  refine TeleHQ.qTelescope δF hn (fun i => (spEF b nodes orbit chals pubs Q i).trace SplitChipJ9.isFT)
    (fun i => (spEF b nodes orbit chals pubs Q i).trace SplitChipJ9.isLT)
    (fun i => sQ δF nA b nodes orbit chals pubs Q SplitChipJ9.acc i) _ _
    (fun i => (sp_masks δF nA b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (sp_masks δF nA b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [spQ] : QE.scale (cv SplitChipJ9.isFT) (QE.sub (QE.var SplitChipJ9.acc)
      (pTerm true)) ∈ spQ δF)
    simp only [pTerm, ite_true, ev_scale, ev_sub, ev_add, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [spQ] : QE.scale (notE (cv SplitChipJ9.isLT)) (QE.sub (QE.sub
      (QE.next SplitChipJ9.acc) (QE.var SplitChipJ9.acc)) (pTerm false)) ∈ spQ δF)
    simp only [pTerm, Bool.false_eq_true, ite_false, ev_scale, ev_sub, ev_add, ev_var, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, spEK_next δF nA b hn nodes orbit chals pubs Q hadj i hi,
      spEF_next δF nA b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [sTerm, sQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [spQ] : QE.scale (cv SplitChipJ9.isLT) (QE.sub (QE.var SplitChipJ9.acc)
      (QE.pub pubSPs)) ∈ spQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, spEK_pub, spEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

/-- The split row denominators are `compress` at the `𝕂′` coins of the lifted width-8 keys. -/
theorem sDen_eq (l : List (CoeffExpr F)) (hl : l.length ≤ 8) (i : Fin n) :
    sDen δF nA b nodes orbit chals pubs Q l i =
      compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ : IOCoins 𝕂′)
        (liftRec (K := K) (L := 𝕂′) (keyVecL 8 l (spEF b nodes orbit chals pubs Q i))) := by
  rw [sDen, den8_eq δF _ _ _ hl]
  simp only [TeleHQ.coinsQ, spEK_chal]

theorem key2_len : (key2 : List (CoeffExpr F)).length ≤ 8 := by simp [key2]
theorem key3_len : (key3 : List (CoeffExpr F)).length ≤ 8 := by simp [key3]

/-- **The split providers' weighted `𝕂′` sum is the terminal `(pub_{pubSPs}, pub_{pubSPs+1})`** (the
zero-activity rows contribute `0`; two records per active row, each at weight `m`). -/
theorem split_provs_sumQ [DecidableEq F] (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (splitChipJ9 δF nA b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((splitProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩ :
          IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs SplitChipJ9.pubSPs) (pubs (SplitChipJ9.pubSPs + 1)) := by
  rw [← split_tele δF nA b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  rw [splitProvs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hI := split_inv δF nA b hn nodes orbit chals pubs Q hsat i
  by_cases h0 : (spEF b nodes orbit chals pubs Q i).trace SplitChipJ9.mult = 0
  · rw [if_pos h0]
    simp only [sTerm, h0, List.map_nil, List.sum_nil, liftQ, map_zero, zero_mul]
  · rw [if_neg h0]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    simp only [sTerm]
    rw [hI.1.2, hI.2.2, sDen_eq δF nA b hn nodes orbit chals pubs Q _ key2_len,
      sDen_eq δF nA b hn nodes orbit chals pubs Q _ key3_len, mul_add]

end Tele

/-! ## 3. The provider list is coin-free -/

section Free
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **`splitProvs_chals_free`**: the split provider list reads only the base trace; it is the same at
`chals pubs` and at the zero coins / publics. -/
theorem splitProvs_chals_free [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) :
    splitProvs b nodes orbit chals pubs Q' = splitProvs (K := K) b nodes orbit (fun _ => 0) (fun _ => 0) Q' := by
  unfold splitProvs
  refine List.flatMap_congr fun i _ => ?_
  have ht : ∀ j, (spEF b nodes orbit chals pubs Q' i).trace j =
      (spEF b nodes orbit (fun _ => (0 : K)) (fun _ => (0 : K)) Q' i).trace j := fun _ => rfl
  rw [ht SplitChipJ9.mult]
  split_ifs
  · rfl
  · simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    refine ⟨?_, ?_⟩
    · funext c
      fin_cases c <;>
        simp [keyVecL, key2, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht]
    · funext c
      fin_cases c <;>
        simp [keyVecL, key3, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht]

end Free

end

end Nock.NockVMROM.Thm54.VclL.Handle.SplitTeleJ9

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.SplitTeleJ9
#print axioms rlc_keyVecL8
#print axioms den8_eq
#print axioms split_inv
#print axioms split_tele
#print axioms sDen_eq
#print axioms split_provs_sumQ
#print axioms splitProvs_chals_free
end Axioms
