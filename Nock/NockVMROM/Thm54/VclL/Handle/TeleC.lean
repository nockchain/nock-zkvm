/-
  Nock/NockVMROM/Thm54/VclL/Handle/TeleC.lean

* §1 `computeChipVCLH_sat_iff` (the copy of `TowerD.computeChipVCLQ7T_sat_iff`) and the row facts:
    every base template gate vanishes as `evalQ` (`base_of_sat`), every `𝕂` template gate as `evalMQ` at
    the gathered environment (`k_of_sat`), through `eval_mapC_cast` / `eval_mapM_cast`.
  * §2 the one-hot selector: from the `11` booleanity gates, the sum gate and `11 < char 𝔽`, exactly
    one state `j₀` is on (`onehot`).
  * §3 the generic slot lemma `slot_core`: under booleanity, pairwise-exclusive activities, and nonzero
    denominators of the ACTIVE records, a slot gate `inv·(Σ a·d + f·dₐ·d_b) = Σ a + f·(dₐ + d_b)` gives
    `(Σ_{x∈P} aₓ)·inv = Σ_{x∈P active} dₓ⁻¹` and `f·inv = [f = 1](dₐ⁻¹ + d_b⁻¹)`.  The nonzero
    denominators are NOT assumed at the end: they come from outside the IO pole event (item 2).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PoleFree
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleC

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. `sat_iff` and the row facts -/

section Sat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

set_option maxHeartbeats 4000000 in
/-- **`sat_iff` for the VS compute chip** (copy of `computeChipVCLQ7T_sat_iff`). -/
theorem computeChipVCLH_sat_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P ↔
      (computeChipVCLH hn nodes b chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesH b,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLH hn nodes b chalV pubVal orbit).rap.compose P i).eval x =
        ((gatesH b).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

variable {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])

/-- **Base row facts**: every gate of the `ℚ` base template vanishes (as `evalQ`) at every row. -/
theorem base_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) (t : CoeffExpr ℚ) (ht : t ∈ baseGatesH (F := ℚ)) :
    evalQ t (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have h0 := ((computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mp hsat).2 x hx
    (mapC (fun q : ℚ => (q : F)) t) (List.mem_append_left _ (List.mem_map_of_mem ht))
  rwa [eval_mapC_cast] at h0

/-- **`𝕂` row facts**: every gate of the `ℚ` `𝕂` template vanishes (as `evalMQ`) at the gathered
environment of every row. -/
theorem k_of_sat (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) (t : MixedExpr ℚ) (ht : t ∈ kGatesH (F := ℚ)) :
    evalMQ t (Compute.TowerD.gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
      (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have hall := ((computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mp hsat).2 x hx
  have hm : mapM (fun q : ℚ => (q : F)) t ∈ (kGatesF : List (MixedExpr F)) := List.mem_map_of_mem ht
  have h0 : ∀ k, (mixedCompile b Compute.TowerD.col0Id (mapM (fun q : ℚ => (q : F)) t) k).eval
      (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := fun k =>
    hall _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hm, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
  have h1 := (mixedCompile_zero_iff b Compute.TowerD.col0Id
    (Compute.TowerD.isCoordEnv_gather b (Reify.envOfTrace P orbit.ω x chalV pubVal)) _).mpr h0
  rwa [eval_mapM_cast] at h1

end Sat

/-! ## 2. The one-hot selector -/

section OneHot
variable {F : Type} [Field F]

theorem evalQ_cc (i : ℕ) (env : Env F) : evalQ (cc i : CoeffExpr ℚ) env = env.trace i := rfl

theorem evalQ_selS (l : List ℕ) (env : Env F) : evalQ (selS l : CoeffExpr ℚ) env = (l.map env.trace).sum := by
  simp only [selS, evalQ_sumList, evalQ_cc]

theorem sum_ind (l : List ℕ) (hl : l.Nodup) (j0 : ℕ) :
    (l.map fun j => if j = j0 then (1 : F) else 0).sum = if j0 ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, ih hl.2]
    by_cases ha : a = j0
    · subst ha; simp [hl.1]
    · by_cases hm : j0 ∈ l
      · simp [ha, hm]
      · have : j0 ≠ a := fun h => ha h.symm
        simp [ha, hm, this]

/-- **One-hot**: booleans summing to `1` below the characteristic: exactly one is on. -/
theorem onehot (s : ℕ → F) (hb : ∀ j < 11, s j * (s j - 1) = 0)
    (hsum : ((List.range 11).map s).sum = 1) (hc : 11 < ringChar F) :
    ∃ j0 < 11, ∀ j < 11, s j = if j = j0 then 1 else 0 := by
  classical
  have hb' : ∀ j < 11, s j = 0 ∨ s j = 1 := fun j hj => by
    rcases mul_eq_zero.mp (hb j hj) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcount : ∀ l : List ℕ, (∀ j ∈ l, s j = 0 ∨ s j = 1) →
      (l.map s).sum = ((l.filter fun j => s j = 1).length : F) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih fun j hj => hl j (List.mem_cons_of_mem _ hj),
        List.filter_cons]
      rcases hl a List.mem_cons_self with h | h
      · simp [h]
      · simp [h]; ring
  set L := (List.range 11).filter fun j => s j = 1 with hL
  have hlen : (L.length : F) = 1 := by
    rw [← hcount _ (fun j hj => hb' j (List.mem_range.mp hj)), hsum]
  have hle : L.length ≤ 11 := (List.length_filter_le _ _).trans (by simp)
  have h1 : L.length = 1 := by
    have hz : ((L.length - 1 : ℕ) : F) = 0 := by
      have hpos : 1 ≤ L.length := by
        by_contra hc0
        have : L.length = 0 := by omega
        rw [this, Nat.cast_zero] at hlen; exact zero_ne_one hlen
      rw [Nat.cast_sub hpos, hlen, Nat.cast_one, sub_self]
    have hdvd := (ringChar.spec F _).mp hz
    have : L.length - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    have hpos : 1 ≤ L.length := by
      by_contra hc0
      have : L.length = 0 := by omega
      rw [this, Nat.cast_zero] at hlen; exact zero_ne_one hlen
    omega
  obtain ⟨j0, hj0⟩ := List.length_eq_one_iff.mp h1
  have hmem : j0 ∈ L := by rw [hj0]; exact List.mem_singleton_self _
  rw [hL, List.mem_filter, List.mem_range] at hmem
  refine ⟨j0, hmem.1, fun j hj => ?_⟩
  by_cases hjj : j = j0
  · subst hjj; simpa using hmem.2
  · rw [if_neg hjj]
    rcases hb' j hj with h | h
    · exact h
    · exfalso
      have : j ∈ L := by rw [hL, List.mem_filter, List.mem_range]; exact ⟨hj, by simpa using h⟩
      rw [hj0, List.mem_singleton] at this
      exact hjj this

end OneHot

/-! ## 3. The generic slot lemma -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- Booleans weight a sum by membership in the active sublist. -/
theorem sum_bool {ι : Type} (M : List ι) (a : ι → F) (g : ι → K) (hb : ∀ x ∈ M, a x = 0 ∨ a x = 1) :
    (M.map fun x => algebraMap F K (a x) * g x).sum = ((M.filter fun x => a x = 1).map g).sum := by
  induction M with
  | nil => simp
  | cons y M ih =>
    rw [List.map_cons, List.sum_cons, ih fun x hx => hb x (List.mem_cons_of_mem _ hx), List.filter_cons]
    rcases hb y List.mem_cons_self with h | h
    · simp [h]
    · simp [h]

theorem sum_bool_one {ι : Type} (M : List ι) (a : ι → F) (hb : ∀ x ∈ M, a x = 0 ∨ a x = 1) :
    algebraMap F K ((M.map a).sum) = (((M.filter fun x => a x = 1).map fun _ => (1 : K))).sum := by
  rw [← sum_bool M a (fun _ => (1 : K)) hb, map_list_sum, List.map_map]
  simp [Function.comp_def]

/-- At most one active entry. -/
theorem active_le_one {ι : Type} (L : List ι) (a : ι → F)
    (hpw : L.Pairwise fun x y => a x * a y = 0) :
    (L.filter fun x => a x = 1) = [] ∨ ∃ x0 ∈ L, a x0 = 1 ∧ (L.filter fun x => a x = 1) = [x0] := by
  have hsub : (L.filter fun x => a x = 1).Sublist L := List.filter_sublist
  have hpw' := hpw.sublist hsub
  have hall : ∀ x ∈ (L.filter fun x => a x = 1), a x = 1 := fun x hx => by
    simpa using (List.mem_filter.mp hx).2
  rcases hA : (L.filter fun x => a x = 1) with _ | ⟨x0, _ | ⟨y, r⟩⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨x0, ?_, ?_, rfl⟩
    · exact hsub.subset (by rw [hA]; exact List.mem_singleton_self _)
    · exact hall x0 (by rw [hA]; exact List.mem_singleton_self _)
  · exfalso
    rw [hA] at hpw' hall
    have h1 := List.rel_of_pairwise_cons hpw' (List.mem_cons_self)
    rw [hall x0 List.mem_cons_self, hall y (List.mem_cons_of_mem _ List.mem_cons_self), one_mul] at h1
    exact one_ne_zero h1

/-- **The generic slot lemma.** -/
theorem slot_core {ι : Type} (L : List ι) (a : ι → F) (d : ι → K) (P : ι → Bool) (inv : K) (f : F)
    (da db : K)
    (hb : ∀ x ∈ L, a x = 0 ∨ a x = 1) (hpw : L.Pairwise fun x y => a x * a y = 0)
    (hf : f = 0 ∨ f = 1) (hfa : ∀ x ∈ L, f * a x = 0)
    (hgate : inv * ((L.map fun x => algebraMap F K (a x) * d x).sum + algebraMap F K f * (da * db)) -
      (algebraMap F K ((L.map a).sum) + algebraMap F K f * (da + db)) = 0)
    (hdp : f = 1 → da ≠ 0 ∧ db ≠ 0) :
    algebraMap F K (((L.filter P).map a).sum) * inv =
        ((((L.filter P).filter fun x => a x = 1)).map fun x => (d x)⁻¹).sum ∧
      algebraMap F K f * inv = if f = 1 then da⁻¹ + db⁻¹ else 0 := by
  have hbP : ∀ x ∈ L.filter P, a x = 0 ∨ a x = 1 := fun x hx => hb x (List.mem_filter.mp hx).1
  rw [sum_bool_one _ a hbP]
  rw [sum_bool L a d hb, sum_bool_one L a hb] at hgate
  have hcomm : ((L.filter P).filter fun x => a x = 1) = ((L.filter fun x => a x = 1).filter P) := by
    rw [List.filter_filter, List.filter_filter]
    congr 1; funext x; exact Bool.and_comm _ _
  rw [hcomm]
  rcases hf with hf0 | hf1
  · subst hf0
    simp only [map_zero, zero_mul, add_zero] at hgate
    refine ⟨?_, by simp⟩
    rcases active_le_one L a hpw with hA | ⟨x0, hx0, ha0, hA⟩
    · rw [hA]; simp
    · rw [hA] at hgate ⊢
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hgate
      have hm : inv * d x0 = 1 := sub_eq_zero.mp hgate
      have hinv : inv = (d x0)⁻¹ := eq_inv_of_mul_eq_one_left hm
      by_cases hP : P x0 = true
      · simp [hP, hinv]
      · simp [hP]
  · subst hf1
    have ha0 : ∀ x ∈ L, a x = 0 := fun x hx => by simpa using hfa x hx
    have hA : (L.filter fun x => a x = 1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx; rw [ha0 x hx]; simp
    rw [hA] at hgate ⊢
    simp only [List.map_nil, List.sum_nil, zero_add, map_one, one_mul, List.filter_nil] at hgate ⊢
    obtain ⟨hda, hdb⟩ := hdp rfl
    refine ⟨by simp, ?_⟩
    rw [if_pos trivial]
    have hm : inv * (da * db) = da + db := sub_eq_zero.mp hgate
    field_simp
    linear_combination hm

end Slot

/-! ## 4. The three slots at a row -/

section Shape

/-- Structural facts of the three slots (kernel `decide`). -/
theorem slots_states : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents,
    x.states.Nodup ∧ (∀ j ∈ x.states, j < 11) ∧ x.rcd.length ≤ 5 := by decide

theorem slots_disjoint : ∀ S ∈ (slots : List (SlotSpec ℚ)),
    S.ents.Pairwise (fun x y => ∀ j ∈ x.states, j ∉ y.states) := by decide

theorem slots_pair : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ fl a b, S.pair = some (fl, a, b) →
    fl = prC ∧ a.length ≤ 5 ∧ b.length ≤ 5 ∧ ∀ x ∈ S.ents, 5 ∉ x.states := by
  intro S hS fl a b hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · simp [slot0] at hp
  · simp [slot1] at hp
  · simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨rfl, by decide, by decide, by decide⟩

theorem slots_extra (Pr : CoeffExpr ℚ → Prop) (h1 : Pr (.const 1)) (h2 : Pr (notC z1C)) (h3 : Pr (cc hSf1.k)) :
    ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents, Pr x.extra := by
  simp [slots, slot0, slot1, slot2, h1, h2, h3]

end Shape

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- The pair flag of a slot (`0` without a pair). -/
def pairF (S : SlotSpec ℚ) (eF : Env F) : F :=
  match S.pair with
  | some (fl, _, _) => eF.trace fl
  | none => 0

def pairDa (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) : K :=
  match S.pair with
  | some (_, a, _) => evalMQ (ChipH.den a) eK eF
  | none => 0

def pairDb (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) : K :=
  match S.pair with
  | some (_, _, b) => evalMQ (ChipH.den b) eK eF
  | none => 0

theorem slotGate_val (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) :
    evalMQ (slotGate S) eK eF =
      eK.trace S.inv * ((S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (ChipH.den x.rcd) eK eF).sum +
          algebraMap F K (pairF S eF) * (pairDa S eK eF * pairDb S eK eF)) -
        (algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
          algebraMap F K (pairF S eF) * (pairDa S eK eF + pairDb S eK eF)) := by
  rw [evalMQ_slotGate]
  cases hp : S.pair with
  | none => simp [pairF, pairDa, pairDb, hp]
  | some q => obtain ⟨fl, a, b⟩ := q; simp [pairF, pairDa, pairDb, hp, evalQ_cc]

theorem evalQ_actX (S : SlotSpec ℚ) (eF : Env F) :
    evalQ S.actX eF = ((S.ents.filter fun x => !x.path).map fun x => evalQ x.act eF).sum := by
  simp only [SlotSpec.actX, evalQ_sumList]

theorem evalQ_actP (S : SlotSpec ℚ) (eF : Env F) :
    evalQ S.actP eF = ((S.ents.filter fun x => x.path).map fun x => evalQ x.act eF).sum + pairF S eF := by
  unfold SlotSpec.actP
  cases hp : S.pair with
  | none => simp [evalQ, evalQ_sumList, pairF, hp]
  | some q => obtain ⟨fl, a, b⟩ := q; simp [evalQ, evalQ_sumList, pairF, hp]; rfl

/-- **A row's selector facts** (from the arithmetic gates): the one-hot state `j₀`, booleans `z1`,
`β`, `sf1_e.kind`, and the read-pair flag gate. -/
structure RowSel (eF : Env F) (j0 : ℕ) : Prop where
  lt : j0 < 11
  sel : ∀ j < 11, eF.trace j = if j = j0 then 1 else 0
  z1 : eF.trace z1C = 0 ∨ eF.trace z1C = 1
  beta : eF.trace betaC = 0 ∨ eF.trace betaC = 1
  k1 : eF.trace hSf1.k = 0 ∨ eF.trace hSf1.k = 1
  pr : eF.trace prC = eF.trace 5 * eF.trace betaC * (1 - eF.trace z1C)

variable {eF : Env F} {j0 : ℕ}

theorem bool_mul {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x * y = 0 ∨ x * y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

theorem act_val (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents) :
    evalQ x.act eF = (if j0 ∈ x.states then 1 else 0) * evalQ x.extra eF := by
  obtain ⟨hnd, hlt, -⟩ := slots_states S hS x hx
  simp only [Ent.act, evalQ, evalQ_selS]
  congr 1
  rw [List.map_congr_left (fun j hj => hs.sel j (hlt j hj))]
  exact sum_ind _ hnd j0

theorem extra_bool (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents) :
    evalQ x.extra eF = 0 ∨ evalQ x.extra eF = 1 := by
  refine slots_extra (fun g => evalQ g eF = 0 ∨ evalQ g eF = 1) ?_ ?_ ?_ S hS x hx
  · right; simp [evalQ]
  · simp only [notC, evalQ, Rat.cast_one, evalQ_cc]
    rcases hs.z1 with h | h <;> rw [h] <;> simp
  · exact hs.k1

theorem act_bool (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents) :
    evalQ x.act eF = 0 ∨ evalQ x.act eF = 1 := by
  rw [act_val hs S hS x hx]
  exact bool_mul (by split_ifs <;> simp) (extra_bool hs S hS x hx)

theorem act_pairwise (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) :
    S.ents.Pairwise fun x y => evalQ x.act eF * evalQ y.act eF = 0 := by
  have hd := slots_disjoint S hS
  rw [List.pairwise_iff_forall_sublist] at hd ⊢
  intro x y hxy
  have hx : x ∈ S.ents := hxy.subset (List.mem_cons_self)
  have hy : y ∈ S.ents := hxy.subset (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [act_val hs S hS x hx, act_val hs S hS y hy]
  by_cases h1 : j0 ∈ x.states
  · have h2 : j0 ∉ y.states := hd hxy j0 h1
    simp [h2]
  · simp [h1]

theorem pairF_bool (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) :
    pairF S eF = 0 ∨ pairF S eF = 1 := by
  unfold pairF
  cases hp : S.pair with
  | none => simp
  | some q =>
    obtain ⟨fl, a, b⟩ := q
    obtain ⟨rfl, -⟩ := slots_pair S hS fl a b hp
    simp only
    rw [hs.pr]
    have h5 : eF.trace 5 = 0 ∨ eF.trace 5 = 1 := by
      rw [hs.sel 5 (by omega)]; split_ifs <;> simp
    have hz : 1 - eF.trace z1C = 0 ∨ 1 - eF.trace z1C = 1 := by
      rcases hs.z1 with h | h <;> rw [h] <;> simp
    exact bool_mul (bool_mul h5 hs.beta) hz

theorem pairF_act (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents) :
    pairF S eF * evalQ x.act eF = 0 := by
  unfold pairF
  cases hp : S.pair with
  | none => simp
  | some q =>
    obtain ⟨fl, a, b⟩ := q
    obtain ⟨rfl, -, -, h5⟩ := slots_pair S hS fl a b hp
    simp only
    by_cases hj : j0 = 5
    · subst hj
      rw [act_val hs S hS x hx, if_neg (h5 x hx)]; simp
    · rw [hs.pr, hs.sel 5 (by omega), if_neg (fun h => hj h.symm)]; simp

end Row


/-! ## 5. Denominators, the per-row request lists and the per-row identities -/

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A compute record's key: its columns lifted to `𝕂`, padded by `0` to length `5`. -/
def entKeyN (r : List ℕ) (eF : Env F) (c : ℕ) : K :=
  if c < r.length then algebraMap F K (eF.trace (r.getD c 0)) else 0

def entKey (r : List ℕ) (eF : Env F) : Fin 5 → K := fun c => entKeyN r eF c

/-- The handle coins as read by the compute chip (`γ` at limb `0`, `ρ` at limb `3`). -/
def coinsOf (eK : Env K) : IOCoins K := ⟨eK.chal chalGammaL, eK.chal chalRhoL⟩

theorem evalMQ_rlcKey (eK : Env K) (eF : Env F) (γ : ℕ) : ∀ (r : List ℕ) (m : ℕ),
    evalMQ (rlcKey .traceCur γ m r : MixedExpr ℚ) eK eF =
      ∑ c ∈ Finset.range r.length, eK.chal γ ^ (m + c) * algebraMap F K (eF.trace (r.getD c 0))
  | [], m => by simp [rlcKey, evalMQ]
  | i :: r, m => by
    rw [rlcKey, evalMQ, evalMQ_rlcKey eK eF γ r (m + 1), List.length_cons, Finset.sum_range_succ']
    simp only [evalMQ, evalQ, List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

/-- **A compute denominator is `compress`** of the record's key at the handle coins. -/
theorem evalMQ_den (eK : Env K) (eF : Env F) (r : List ℕ) (hr : r.length ≤ 5) :
    evalMQ (ChipH.den r : MixedExpr ℚ) eK eF = compress (coinsOf eK) (entKey r eF) := by
  simp only [ChipH.den, evalMQ, evalMQ_rlcKey, compress, Walk.rlc, entKey, coinsOf, zero_add]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun c => eK.chal chalGammaL ^ c * entKeyN r eF c) 5]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hr)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    simp [entKeyN, hc]
  · intro c _ hc
    rw [Finset.mem_range] at hc
    simp [entKeyN, hc]

end Den

section RowId
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

def activeX (S : SlotSpec ℚ) (eF : Env F) : List (Ent ℚ) :=
  (S.ents.filter fun x => !x.path).filter fun x => evalQ x.act eF = 1

def activeP (S : SlotSpec ℚ) (eF : Env F) : List (Ent ℚ) :=
  (S.ents.filter fun x => x.path).filter fun x => evalQ x.act eF = 1

/-- The batched read pair's two records when the flag is on. -/
def pairReqs (S : SlotSpec ℚ) (eF : Env F) : List (Fin 5 → K) :=
  match S.pair with
  | some (fl, a, b) => if eF.trace fl = 1 then [entKey a eF, entKey b eF] else []
  | none => []

/-- **The compute row's consumed handle-export keys** (L1, L2, L3, L5: `cellRec`). -/
def rowXReqs (eF : Env F) : List (Fin 5 → K) :=
  (slots : List (SlotSpec ℚ)).flatMap fun S => (activeX S eF).map fun x => entKey x.rcd eF

/-- **The compute row's consumed handle walk records**. -/
def rowPReqs (eF : Env F) : List (Fin 5 → K) :=
  (slots : List (SlotSpec ℚ)).flatMap fun S => (activeP S eF).map (fun x => entKey x.rcd eF) ++ pairReqs S eF

theorem termVal_slots (b : Basis (Fin 3) F K) (sel : SlotSpec ℚ → CoeffExpr ℚ) (eF : Env F) :
    Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S => (⟨sel S, S.inv⟩ : Compute.LogUp.Slot ℚ)).map
        castSlot) eF =
      ((slots : List (SlotSpec ℚ)).map fun S =>
        algebraMap F K (evalQ (sel S) eF) * (Compute.TowerD.gatherEnv b eF).trace S.inv).sum := by
  simp only [Compute.LogUp.termVal, List.map_map, Function.comp_def, castSlot, eval_mapC_cast,
    Algebra.smul_def]
  rfl

variable {eF : Env F} {j0 : ℕ}

theorem pairReqs_sub (S : SlotSpec ℚ) (hS : S ∈ slots) (r : Fin 5 → K) (hr : r ∈ pairReqs S eF) :
    r ∈ rowPReqs eF :=
  List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ hr⟩

/-- The slot lemma at a row of the chip. -/
theorem slot_at (b : Basis (Fin 3) F K) (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots)
    (hg : evalMQ (slotGate S) (Compute.TowerD.gatherEnv b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs eF, compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r ≠ 0) (P : Ent ℚ → Bool) :
    algebraMap F K (((S.ents.filter P).map fun x => evalQ x.act eF).sum) *
        (Compute.TowerD.gatherEnv b eF).trace S.inv =
      ((((S.ents.filter P).filter fun x => evalQ x.act eF = 1)).map fun x =>
        (compress (coinsOf (Compute.TowerD.gatherEnv b eF)) (entKey x.rcd eF))⁻¹).sum ∧
    algebraMap F K (pairF S eF) * (Compute.TowerD.gatherEnv b eF).trace S.inv =
      ((pairReqs S eF).map fun r => (compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r)⁻¹).sum := by
  set eK := Compute.TowerD.gatherEnv b eF
  have hcore := slot_core S.ents (fun x => evalQ x.act eF) (fun x => evalMQ (ChipH.den x.rcd) eK eF) P
    (eK.trace S.inv) (pairF S eF) (pairDa S eK eF) (pairDb S eK eF)
    (fun x hx => act_bool hs S hS x hx) (act_pairwise hs S hS) (pairF_bool hs S hS)
    (fun x hx => pairF_act hs S hS x hx) (by rw [← slotGate_val]; exact hg) ?_
  · refine ⟨?_, ?_⟩
    · rw [hcore.1]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      have hxS : x ∈ S.ents := (List.mem_filter.mp (List.mem_filter.mp hx).1).1
      rw [evalMQ_den eK eF _ (slots_states S hS x hxS).2.2]
    · rw [hcore.2]
      unfold pairReqs pairF pairDa pairDb
      cases hp : S.pair with
      | none => simp
      | some q =>
        obtain ⟨fl, a, c⟩ := q
        obtain ⟨-, ha, hc, -⟩ := slots_pair S hS fl a c hp
        simp only
        split_ifs with h1
        · simp [evalMQ_den eK eF _ ha, evalMQ_den eK eF _ hc]
        · simp
  · intro h1
    unfold pairDa pairDb
    unfold pairF at h1
    cases hp : S.pair with
    | none => rw [hp] at h1; exact absurd h1 zero_ne_one
    | some q =>
      obtain ⟨fl, a, c⟩ := q
      rw [hp] at h1
      obtain ⟨-, ha, hc, -⟩ := slots_pair S hS fl a c hp
      simp only at h1 ⊢
      have hin : ∀ r ∈ pairReqs S eF, compress (coinsOf eK) r ≠ 0 := fun r hr =>
        hden r (pairReqs_sub S hS r hr)
      unfold pairReqs at hin
      rw [hp] at hin
      simp only [h1, if_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hin
      rw [evalMQ_den eK eF _ ha, evalMQ_den eK eF _ hc]
      exact hin

/-- **The export term of a row**: `termVal slotsX = Σ_{rowXReqs} compress⁻¹`. -/
theorem termX_row (b : Basis (Fin 3) F K) (hs : RowSel eF j0)
    (hg : ∀ S ∈ (slots : List (SlotSpec ℚ)), evalMQ (slotGate S) (Compute.TowerD.gatherEnv b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs eF, compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r ≠ 0) :
    Compute.LogUp.termVal b (slotsX (F := F)) eF =
      ((rowXReqs eF).map fun r => (compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r)⁻¹).sum := by
  rw [slotsX, termVal_slots, rowXReqs, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  rw [evalQ_actX, (slot_at b hs S hS (hg S hS) hden (fun x => !x.path)).1, List.map_map]
  rfl

/-- **The path term of a row**: `termVal slotsP = Σ_{rowPReqs} compress⁻¹`. -/
theorem termP_row (b : Basis (Fin 3) F K) (hs : RowSel eF j0)
    (hg : ∀ S ∈ (slots : List (SlotSpec ℚ)), evalMQ (slotGate S) (Compute.TowerD.gatherEnv b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs eF, compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r ≠ 0) :
    Compute.LogUp.termVal b (slotsP (F := F)) eF =
      ((rowPReqs eF).map fun r => (compress (coinsOf (Compute.TowerD.gatherEnv b eF)) r)⁻¹).sum := by
  rw [slotsP, termVal_slots, rowPReqs, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have h := slot_at b hs S hS (hg S hS) hden (fun x => x.path)
  rw [evalQ_actP, map_add, add_mul, h.1, h.2, List.map_append, List.sum_append, List.map_map]
  rfl

end RowId


/-! ## 6. The chip: row selectors, masks and the two compute telescopes -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])

/-- Row `i`'s base environment on the compute chip. -/
abbrev rEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F := Reify.envOfTrace Q' orbit.ω (nodes i) chalV pubVal

theorem arith_sub (t : CoeffExpr ℚ) (ht : t ∈ arithGates (F := ℚ)) : t ∈ baseGatesH (F := ℚ) :=
  List.mem_append_left _ (List.mem_append_left _ ht)

theorem gate_q {env : Env F} (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t env = 0) (t : CoeffExpr ℚ)
    (ht : t ∈ arithGates (F := ℚ)) : evalQ t env = 0 := hbase t (arith_sub t ht)

theorem bool_of {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- **The row selector facts from the arithmetic gates** (under `11 < char 𝔽`). -/
theorem rowSel_of_base {env : Env F} (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t env = 0)
    (hc : 11 < ringChar F) : ∃ j0, RowSel env j0 := by
  have hb : ∀ j < 11, env.trace j * (env.trace j - 1) = 0 := fun j hj => by
    have := gate_q hbase (.mul (cc j) (.sub (cc j) (.const 1)))
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))
    simpa [evalQ, evalQ_cc] using this
  have hsum : ((List.range 11).map env.trace).sum = 1 := by
    have := gate_q hbase (.sub (selS (List.range 11)) (.const 1)) (by simp [arithGates])
    rw [evalQ, evalQ_selS] at this
    simpa [evalQ, sub_eq_zero] using this
  obtain ⟨j0, hj0, hsel⟩ := onehot env.trace hb hsum hc
  have hz := gate_q hbase (.mul (cc z1C) (.sub (cc z1C) (.const 1))) (by simp [arithGates])
  have hβ := gate_q hbase (.mul (cc betaC) (.sub (cc betaC) (.const 1))) (by simp [arithGates])
  have hk := gate_q hbase (.mul (cc hSf1.k) (.sub (cc hSf1.k) (.const 1)))
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨hSf1, List.mem_map.mpr ⟨3, List.mem_range.mpr (by decide), rfl⟩, rfl⟩)))
  have hpr := gate_q hbase prGate (by simp [arithGates])
  simp only [evalQ, evalQ_cc, Rat.cast_one] at hz hβ hk
  simp only [prGate, prodL, notC, List.foldr, evalQ, evalQ_cc, Rat.cast_one, mul_one] at hpr
  exact ⟨j0, hj0, hsel, bool_of hz, bool_of hβ, bool_of hk, by rw [← sub_eq_zero, ← hpr]; ring⟩

theorem slotGate_mem (S : SlotSpec ℚ) (hS : S ∈ (slots : List (SlotSpec ℚ))) :
    slotGate S ∈ kGatesH (F := ℚ) :=
  List.mem_append_left _ (List.mem_map_of_mem hS)

/-- The endpoint masks of the compute chip (preprocessing columns `11 / 12`). -/
theorem masksC (hbind : (computeChipVCLH hn nodes b chalV pubVal orbit).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (rEF nodes chalV pubVal orbit P i).trace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rEF nodes chalV pubVal orbit P i).trace 12 = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w = 70 := rfl
  have h0 : P ⟨11, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : P ⟨12, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  rw [envOfTrace_trace P _ _ _ _ (show 11 < _ by rw [hw]; omega),
    envOfTrace_trace P _ _ _ _ (show 12 < _ by rw [hw]; omega), h0, h1,
    firstRowMask_eval nodes hinj i, lastRowMask_eval hn nodes hinj i]
  refine ⟨rfl, ?_⟩
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

/-- Rows extended to `ℕ` (junk past `n`). -/
def envsN {w : ℕ} (Q' : Fin w → F[X]) (k : ℕ) : Env F :=
  if hk : k < n then rEF nodes chalV pubVal orbit Q' ⟨k, hk⟩ else rEF nodes chalV pubVal orbit Q' ⟨0, hn⟩

theorem envsN_lt (k : ℕ) (hk : k < n) :
    envsN hn nodes chalV pubVal orbit P k = rEF nodes chalV pubVal orbit P ⟨k, hk⟩ := by
  simp [envsN, hk]

/-- **The generic compute telescope**: an accumulator over `slots'` at `accBase` / `pubBase`, whose
`ℚ` gate list is in the base template, sums its terms to the public limbs. -/
theorem compute_telescope (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (sl : List (Compute.LogUp.Slot ℚ)) (accBase pubBase : ℕ)
    (hsub : ∀ t ∈ Compute.LogUp.accGates 3 sl accBase pubBase, t ∈ baseGatesH (F := ℚ)) :
    ∑ i : Fin n, Compute.LogUp.termVal b (sl.map castSlot) (rEF nodes chalV pubVal orbit P i) =
      Compute.LogUp.limbVal b pubVal pubBase := by
  have hbind := ((computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mp hsat).1
  have hg : ∀ i < n, ∀ g ∈ Compute.LogUp.accGates 3 (sl.map castSlot) accBase pubBase,
      g.eval (envsN hn nodes chalV pubVal orbit P i) = 0 := by
    intro i hi g hg
    rw [← accGates_map] at hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    rw [envsN_lt hn nodes b chalV pubVal orbit P i hi, eval_mapC_cast]
    exact base_of_sat hn nodes b chalV pubVal orbit P hsat _ (mem_rowNodeSet nodes _) t (hsub t ht)
  have hsum := Compute.LogUp.acc_rows b (sl.map castSlot) accBase pubBase n hn
    (envsN hn nodes chalV pubVal orbit P) hg
    (fun i hi j => by
      rw [envsN_lt hn nodes b chalV pubVal orbit P i (by omega),
        envsN_lt hn nodes b chalV pubVal orbit P (i + 1) hi]
      exact traceNext_eq nodes orbit P _ _ hadj ⟨i, by omega⟩ hi j)
    (by rw [envsN_lt hn nodes b chalV pubVal orbit P 0 hn,
          (masksC hn nodes b chalV pubVal orbit P hbind hinj _).1]; rfl)
    (fun i hi => by
      rw [envsN_lt hn nodes b chalV pubVal orbit P i (by omega),
        (masksC hn nodes b chalV pubVal orbit P hbind hinj _).2]
      simp only; rw [if_neg (by omega)])
    (by rw [envsN_lt hn nodes b chalV pubVal orbit P (n - 1) (by omega),
          (masksC hn nodes b chalV pubVal orbit P hbind hinj _).2]; simp)
    (Compute.LogUp.limbVal b pubVal pubBase)
    (by rw [envsN_lt hn nodes b chalV pubVal orbit P (n - 1) (by omega)]; rfl)
  rw [← hsum, Finset.sum_range (fun i => Compute.LogUp.termVal b (sl.map castSlot)
    (envsN hn nodes chalV pubVal orbit P i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [envsN_lt hn nodes b chalV pubVal orbit P i i.isLt]

theorem accX_sub : ∀ t ∈ Compute.LogUp.accGates 3 ((slots : List (SlotSpec ℚ)).map fun S =>
    (⟨S.actX, S.inv⟩ : Compute.LogUp.Slot ℚ)) accX pubRhoX, t ∈ baseGatesH (F := ℚ) := fun _ ht =>
  List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ ht))

theorem accP_sub : ∀ t ∈ Compute.LogUp.accGates 3 ((slots : List (SlotSpec ℚ)).map fun S =>
    (⟨S.actP, S.inv⟩ : Compute.LogUp.Slot ℚ)) accP pubRhoP, t ∈ baseGatesH (F := ℚ) := fun _ ht =>
  List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ ht))

/-- The compute chip's handle coins (constant over rows). -/
def coinsC : IOCoins K := ⟨Compute.LogUp.limbVal b chalV chalGammaL, Compute.LogUp.limbVal b chalV chalRhoL⟩

/-- **The compute consumed handle-export keys** (every row). -/
def compXReqs {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 5 → K) :=
  (List.finRange n).flatMap fun i => rowXReqs (rEF nodes chalV pubVal orbit Q' i)

/-- **The compute consumed handle walk records** (every row). -/
def compPReqs {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 5 → K) :=
  (List.finRange n).flatMap fun i => rowPReqs (rEF nodes chalV pubVal orbit Q' i)

/-- **The compute export telescope**: `Σ_{compXReqs} compress⁻¹ = limbs 15..17` (`Re ρ₃` at VS). -/
theorem compX_sum (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : 11 < ringChar F)
    (hden : ∀ r ∈ compPReqs nodes chalV pubVal orbit P, compress (coinsC b chalV) r ≠ 0) :
    ((compXReqs nodes chalV pubVal orbit P).map fun r => (compress (coinsC b chalV) r)⁻¹).sum =
      Compute.LogUp.limbVal b pubVal pubRhoX := by
  rw [← compute_telescope hn nodes b chalV pubVal orbit P hsat hinj hadj _ accX pubRhoX accX_sub,
    compXReqs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbase := fun t ht => base_of_sat hn nodes b chalV pubVal orbit P hsat _ (mem_rowNodeSet nodes i) t ht
  obtain ⟨j0, hs⟩ := rowSel_of_base hbase hc
  have := termX_row b hs (fun S hS => k_of_sat hn nodes b chalV pubVal orbit P hsat _
    (mem_rowNodeSet nodes i) _ (slotGate_mem S hS))
    (fun r hr => hden r (List.mem_flatMap.mpr ⟨i, List.mem_finRange _, hr⟩))
  exact this.symm

/-- **The compute path telescope**: `Σ_{compPReqs} compress⁻¹ = limbs 18..20` (`Re ρ₄` at VS). -/
theorem compP_sum (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : 11 < ringChar F)
    (hden : ∀ r ∈ compPReqs nodes chalV pubVal orbit P, compress (coinsC b chalV) r ≠ 0) :
    ((compPReqs nodes chalV pubVal orbit P).map fun r => (compress (coinsC b chalV) r)⁻¹).sum =
      Compute.LogUp.limbVal b pubVal pubRhoP := by
  rw [← compute_telescope hn nodes b chalV pubVal orbit P hsat hinj hadj _ accP pubRhoP accP_sub,
    compPReqs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbase := fun t ht => base_of_sat hn nodes b chalV pubVal orbit P hsat _ (mem_rowNodeSet nodes i) t ht
  obtain ⟨j0, hs⟩ := rowSel_of_base hbase hc
  have := termP_row b hs (fun S hS => k_of_sat hn nodes b chalV pubVal orbit P hsat _
    (mem_rowNodeSet nodes i) _ (slotGate_mem S hS))
    (fun r hr => hden r (List.mem_flatMap.mpr ⟨i, List.mem_finRange _, hr⟩))
  exact this.symm

end Chip


/-! ## 7. The served lookups (export: three parties; path: compute against the walk twin) -/

section Serve
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

/-- **Poles are priced**: outside the weighted IO failure event every consumer's denominator is
nonzero (`IOPoleHitEvent` is a component). -/
theorem den_ne_of_out {m : ℕ} [Fintype K] [DecidableEq K] (reqs : List (Fin m → K))
    (provs : List ((Fin m → K) × K)) (γ ρ : K) (hout : (γ, ρ) ∉ IOFailureEventW reqs provs) :
    ∀ r ∈ reqs, compress ⟨γ, ρ⟩ r ≠ 0 := by
  intro r hr h0
  apply hout
  rw [mem_IOFailureEventW_iff]
  right; left
  simp only [IOPoleHitEvent, recordsW, Finset.mem_univ, true_and]
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  exact ⟨r, List.mem_append_left _ hr, h0⟩

variable [Fintype K] [DecidableEq K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])
  {hT nT : ℕ} (hnT : 0 < nT) (nodesT : Fin nT → F) (orbitT : StrictOrbitDomain F 3 hT)
  {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → F) (orbitW : StrictOrbitDomain F 3 hW)
  (chals pubsT pubsW : ℕ → K)
  (QT : Fin (cellChipH δF b hnT nodesT orbitT chals pubsT).rap.w → F[X])
  (QW : Fin (walkChipH δF kroots b hnW nodesW orbitW chals pubsW).rap.w → F[X])

/-- **The handle-export lookup is served** (three parties at `(γH, ρH)`): every compute export key
(`L1–L3, L5`) and every walk-consumed key is a cell-twin provided key, outside the export and path
IO failure events, given the consumer count `< p`. -/
theorem export_served {p : ℕ} [CharP K p]
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsatT : RAP.SatisfiesWithPreprocessing (cellChipH δF b hnT nodesT orbitT chals pubsT) QT)
    (hinjT : Function.Injective nodesT)
    (hadjT : ∀ (i : Fin nT) (hi : (i : ℕ) + 1 < nT), nodesT ⟨(i : ℕ) + 1, hi⟩ = nodesT i * orbitT.ω)
    (hsatW : RAP.SatisfiesWithPreprocessing (walkChipH δF kroots b hnW nodesW orbitW chals pubsW) QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hc : 11 < ringChar F)
    (hγ : coinsC b chalV = ⟨chals CellH.hGam, chals CellH.hRho⟩)
    (hpub : pubsT CellH.pubH = Compute.LogUp.limbVal b pubVal pubRhoX + pubsW WalkHC.pubX)
    (houtP : (chals CellH.hGam, chals CellH.hRho) ∉
      IOFailureEventW (compPReqs nodes chalV pubVal orbit P) (walkPProvs b nodesW orbitW chals pubsW QW))
    (hout : (chals CellH.hGam, chals CellH.hRho) ∉
      IOFailureEventW (compXReqs nodes chalV pubVal orbit P ++ walkXReqs b nodesW orbitW chals pubsW QW)
        (cellProvs b nodesT orbitT chals pubsT QT))
    (hcount : (compXReqs nodes chalV pubVal orbit P ++ walkXReqs b nodesW orbitW chals pubsW QW).length < p) :
    ∀ r ∈ compXReqs nodes chalV pubVal orbit P ++ walkXReqs b nodesW orbitW chals pubsW QW,
      r ∈ (cellProvs b nodesT orbitT chals pubsT QT).map Prod.fst := by
  have hd := den_ne_of_out _ _ _ _ hout
  have hdP := den_ne_of_out _ _ _ _ houtP
  refine keys_served _ _ _ _ _ (Compute.LogUp.limbVal b pubVal pubRhoX) (pubsW WalkHC.pubX)
    (fun r hr => hd r (List.mem_append_left _ hr))
    (walk_reqs_den δF kroots b hnW nodesW orbitW chals pubsW QW hsatW.1)
    (cell_provs_den δF b hnT nodesT orbitT chals pubsT QT hsatT.1) ?_
    (walk_reqs_sum δF kroots b hnW nodesW orbitW chals pubsW QW hsatW.1 hsatW.2 hinjW hadjW)
    (by rw [cell_provs_sum δF b hnT nodesT orbitT chals pubsT QT hsatT.1 hsatT.2 hinjT hadjT, hpub])
    hcount hout
  rw [← hγ]
  exact compX_sum hn nodes b chalV pubVal orbit P hsat hinj hadj hc (by rw [hγ]; exact hdP)

/-- **The handle walk lookup is served**: every compute walk record is a
walk-twin provided handle walk record, outside the path IO failure event. -/
theorem path_served {p : ℕ} [CharP K p]
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsatW : RAP.SatisfiesWithPreprocessing (walkChipH δF kroots b hnW nodesW orbitW chals pubsW) QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hc : 11 < ringChar F)
    (hγ : coinsC b chalV = ⟨chals CellH.hGam, chals CellH.hRho⟩)
    (hpub : pubsW WalkHC.pubP = Compute.LogUp.limbVal b pubVal pubRhoP)
    (houtP : (chals CellH.hGam, chals CellH.hRho) ∉
      IOFailureEventW (compPReqs nodes chalV pubVal orbit P) (walkPProvs b nodesW orbitW chals pubsW QW))
    (hcount : (compPReqs (K := K) nodes chalV pubVal orbit P).length < p) :
    ∀ r ∈ compPReqs nodes chalV pubVal orbit P,
      r ∈ (walkPProvs b nodesW orbitW chals pubsW QW).map Prod.fst := by
  have hdP := den_ne_of_out _ _ _ _ houtP
  refine served_of_balance _ _ _ _ hdP
    (walk_provs_den δF kroots b hnW nodesW orbitW chals pubsW QW hsatW.1) ?_ hcount houtP
  rw [walk_provs_sum δF kroots b hnW nodesW orbitW chals pubsW QW hsatW.1 hsatW.2 hinjW hadjW, hpub, ← hγ]
  exact compP_sum hn nodes b chalV pubVal orbit P hsat hinj hadj hc (by rw [hγ]; exact hdP)

end Serve


/-! ## 8. Request counts: `≤ 3` export and `≤ 2` path records per row (the `reqBoundVS` budgets) -/

section Count

/-- Export entries a state `j₀` can activate. -/
def exportCount (j0 : ℕ) : ℕ :=
  ((slots : List (SlotSpec ℚ)).map fun S => (S.ents.filter fun x => !x.path && decide (j0 ∈ x.states)).length).sum

/-- Path records a state `j₀` can activate (a read pair counts `2`). -/
def pathCount (j0 : ℕ) : ℕ :=
  ((slots : List (SlotSpec ℚ)).map fun S => (S.ents.filter fun x => x.path && decide (j0 ∈ x.states)).length +
    (if S.pair.isSome && decide (j0 = 5) then 2 else 0)).sum

theorem exportCount_le : ∀ j0 < 11, exportCount j0 ≤ 3 := by decide
theorem pathCount_le : ∀ j0 < 11, pathCount j0 ≤ 2 := by decide

theorem len_filter_mono {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left h

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] {eF : Env F} {j0 : ℕ}

theorem active_states (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents)
    (h1 : evalQ x.act eF = 1) : j0 ∈ x.states := by
  by_contra hj
  rw [act_val hs S hS x hx, if_neg hj, zero_mul] at h1
  exact zero_ne_one h1

theorem activeX_len (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) :
    (activeX S eF).length ≤ (S.ents.filter fun x => !x.path && decide (j0 ∈ x.states)).length := by
  unfold activeX
  rw [List.filter_filter]
  refine len_filter_mono fun x hx hp => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
  exact ⟨hp.2, active_states hs S hS x hx hp.1⟩

theorem activeP_len (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) :
    (activeP S eF).length ≤ (S.ents.filter fun x => x.path && decide (j0 ∈ x.states)).length := by
  unfold activeP
  rw [List.filter_filter]
  refine len_filter_mono fun x hx hp => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
  exact ⟨hp.2, active_states hs S hS x hx hp.1⟩

theorem pairReqs_len (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) :
    (pairReqs (K := K) S eF).length ≤ (if S.pair.isSome && decide (j0 = 5) then 2 else 0) := by
  unfold pairReqs
  cases hp : S.pair with
  | none => simp
  | some q =>
    obtain ⟨fl, a, c⟩ := q
    obtain ⟨rfl, -⟩ := slots_pair S hS fl a c hp
    simp only
    split_ifs with h1 h2 h2
    · simp
    · exfalso
      simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq] at h2
      rw [hs.pr, hs.sel 5 (by omega), if_neg (fun h => h2 h.symm), zero_mul, zero_mul] at h1
      exact zero_ne_one h1
    · simp
    · simp

/-- **At most `3` export records per row.** -/
theorem rowXReqs_len (hs : RowSel eF j0) : (rowXReqs (K := K) eF).length ≤ 3 := by
  unfold rowXReqs
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_sum fun S hS => ?_) (exportCount_le j0 hs.lt)
  rw [List.length_map]
  exact activeX_len hs S hS

/-- **At most `2` path records per row.** -/
theorem rowPReqs_len (hs : RowSel eF j0) : (rowPReqs (K := K) eF).length ≤ 2 := by
  unfold rowPReqs
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_sum fun S hS => ?_) (pathCount_le j0 hs.lt)
  rw [List.length_append, List.length_map]
  exact Nat.add_le_add (activeP_len hs S hS) (pairReqs_len hs S hS)

end Count

section CountChip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])

theorem compXReqs_len (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hc : 11 < ringChar F) : (compXReqs (K := K) nodes chalV pubVal orbit P).length ≤ 3 * n := by
  unfold compXReqs
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange n).map fun _ => 3).sum := List.sum_le_sum fun i _ => by
          obtain ⟨j0, hs⟩ := rowSel_of_base (fun t ht => base_of_sat hn nodes b chalV pubVal orbit P hsat _
            (mem_rowNodeSet nodes i) t ht) hc
          exact rowXReqs_len hs
    _ = 3 * n := by simp [mul_comm]

theorem compPReqs_len (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hc : 11 < ringChar F) : (compPReqs (K := K) nodes chalV pubVal orbit P).length ≤ 2 * n := by
  unfold compPReqs
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange n).map fun _ => 2).sum := List.sum_le_sum fun i _ => by
          obtain ⟨j0, hs⟩ := rowSel_of_base (fun t ht => base_of_sat hn nodes b chalV pubVal orbit P hsat _
            (mem_rowNodeSet nodes i) t ht) hc
          exact rowPReqs_len hs
    _ = 2 * n := by simp [mul_comm]

end CountChip


/-! ## 9. At VS: the coins and publics of `chipCVS`, and the served lookups from `AcceptsG` -/

section VS
open FrameVS SVFrameG T0Tower

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

/-- **The compute chip reads the handle coins `(γH, ρH) = (χ₁₁, χ₁₂)`.** -/
theorem coinsC_VS (b : Basis (Fin 3) F K) (χ : Coins frameVS K) :
    coinsC b (chalVH b χ) = (⟨χ cGamH, χ cRhoH⟩ : IOCoins K) := by
  unfold coinsC
  congr 1
  · refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [chalVH, coinH, chalGammaL]
  · refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [chalVH, coinH, chalRhoL]

/-- The compute export terminal is `Re ρ₃`. -/
theorem pubX_VS (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (pubVH δF b c m ρ χ) pubRhoX = Quad.re _ (ρ 3) := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubVH, pubRhoX]

/-- The compute path terminal is `Re ρ₄`. -/
theorem pubP_VS (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (pubVH δF b c m ρ χ) pubRhoP = Quad.re _ (ρ 4) := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubVH, pubRhoP]

theorem cellW (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (cellChipH δF b hn nodes orbit chals pubs).rap.w = ((shapeVS hT hP).table (tCS hT hP)).width := by
  rw [cellChipH_width]; rfl

theorem walkW (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (walkChipH δF kr b hn nodes orbit chals pubs).rap.w = ((shapeVS hT hP).table (tWS hT hP)).width := by
  rw [walkChipH_width]; rfl

variable {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- The VS compute consumed export keys. -/
abbrev cXVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    List (Fin 5 → K) :=
  compXReqs V.computeNodes (chalVH V.basis χ) (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ)
    V.orbitC (msg.Qc χ)

abbrev cPVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    List (Fin 5 → K) :=
  compPReqs V.computeNodes (chalVH V.basis χ) (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ)
    V.orbitC (msg.Qc χ)

/-- The VS walk-consumed export keys. -/
abbrev wXVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    List (Fin 5 → K) :=
  walkXReqs V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (chalsVS δF χ)
    (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWS hT hP))

abbrev wPVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    List ((Fin 5 → K) × K) :=
  walkPProvs V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (chalsVS δF χ)
    (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWS hT hP))

abbrev tXVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    List ((Fin 5 → K) × K) :=
  cellProvs V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (chalsVS δF χ)
    (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tCS hT hP))

/-- No hypothesis beyond `V.Checks` (the consumer
budgets `3N + W`, `2N`) and the chip guard `2^63 < char 𝔽`. -/
theorem vs_served (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (houtX : (χ cGamH, χ cRhoH) ∉ IOFailureEventW (cXVS δF hT hP kr hC V msg χ ++ wXVS δF hT hP kr hC V msg χ)
      (tXVS δF hT hP kr hC V msg χ))
    (houtP : (χ cGamH, χ cRhoH) ∉ IOFailureEventW (cPVS δF hT hP kr hC V msg χ) (wPVS δF hT hP kr hC V msg χ)) :
    (∀ r ∈ cXVS δF hT hP kr hC V msg χ ++ wXVS δF hT hP kr hC V msg χ,
        r ∈ (tXVS δF hT hP kr hC V msg χ).map Prod.fst) ∧
      ∀ r ∈ cPVS δF hT hP kr hC V msg χ, r ∈ (wPVS δF hT hP kr hC V msg χ).map Prod.fst := by
  obtain ⟨hg, hsat⟩ := compute_facts δF hT hP kr hC V msg χ h
  obtain ⟨-, hwT, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  obtain ⟨-, hwW, hsatW⟩ := walk_facts δF hT hP kr hC V msg χ h
  have hq : 2 ^ 63 < ringChar F := hg.2.2.1
  have hc : 11 < ringChar F := lt_trans (by norm_num) hq
  have hadj : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.computeNodes i * V.orbitC.ω := fun i hi => by
    rw [hg.1 i hi, mul_comm]
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar K := by
    rw [ringChar_quad_eq δF, Algebra.ringChar_eq F K]
  have hcons3 := hV.hcons 3
  have hcons4 := hV.hcons 4
  simp [reqBoundVS, internalBoundVS, hchar] at hcons3 hcons4
  have hcC := compXReqs_len (K := K) V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ) hsat hc
  have hcP := compPReqs_len (K := K) V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ) hsat hc
  have hγ : coinsC V.basis (chalVH V.basis χ) = ⟨chalsVS δF χ CellH.hGam, chalsVS δF χ CellH.hRho⟩ := by
    rw [coinsC_VS, chalsVS_hGam, chalsVS_hRho]
  rw [← chalsVS_hGam δF χ, ← chalsVS_hRho δF χ] at houtX houtP
  refine ⟨?_, ?_⟩
  · refine export_served (p := ringChar K) δF kr V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ)
      (V.hM _) (V.memNodes _) (V.orbitM _) (V.hM _) (V.memNodes _) (V.orbitM _) (chalsVS δF χ) _ _ _ _
      hsat hg.2.1 hadj hsatT (hV.memNodes_injective _) (hV.hadjM _) hsatW (hV.memNodes_injective _)
      (hV.hadjM _) hc hγ ?_ houtP houtX ?_
    · erw [pubX_VS]
      simp [pubsCH, pubsWH]
    · rw [List.length_append]
      simp only [walkXReqs, List.length_map, List.length_finRange]
      omega
  · refine path_served (p := ringChar K) δF kr V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ)
      (V.hM _) (V.memNodes _) (V.orbitM _) (chalsVS δF χ) _ _ hsat hg.2.1 hadj hsatW
      (hV.memNodes_injective _) (hV.hadjM _) hc hγ ?_ houtP (by omega)
    erw [pubP_VS]
    simp [pubsWH, WalkHC.pubX, WalkHC.pubP]

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleC
