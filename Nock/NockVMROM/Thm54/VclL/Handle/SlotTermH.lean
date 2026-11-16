/-
  Nock/NockVMROM/Thm54/VclL/Handle/SlotTermH.lean

  Additive.

  A compute slot carries ONE inverse column `inv = A / D` (`HonestLookups.slotGate_honest`), `D = Σ act·den
  (+ pr·den_a·den_b)`, `A = Σ act (+ pr·(den_a + den_b))`.  Because the states of the entries of a slot
  are pairwise disjoint (and the OP5 pair state is disjoint from them), at most one entry (or the pair)
  is active on a row, and then the slot's contribution to the accumulator is exactly the sum of `1/den`
  over the active records.
  * `slot_term_X`: `actX · inv = Σ_{active export entries} 1/den`;
  * `slot_term_P`: `actP · inv = Σ_{active path entries} 1/den + (pair active ? 1/den_a + 1/den_b : 0)`.
  Hypotheses: the activity values are 0/1 (`hact`, `hfl`), at most one active (`hex`), and the active
  denominators are non-zero (`hpole`, the priced pole event `PoleFree`).  Pure algebra over any
  `Field K` with `Algebra F K`; the per-state activity facts are the row casework of the next lemma.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

noncomputable section

section SlotTerm
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem sum_filter_act (eF : Env F) (l : List (Ent ℚ)) (P : Ent ℚ → Prop) [DecidablePred P]
    (R : Ent ℚ → Bool) (g : Ent ℚ → K)
    (hact : ∀ x ∈ l, evalQ x.act eF = if P x then 1 else 0) :
    ((l.filter R).map fun x => algebraMap F K (evalQ x.act eF) * g x).sum =
      ((l.filter fun x => R x && decide (P x)).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => hact x (List.mem_cons_of_mem _ hx))
    have ha := hact a (List.mem_cons_self ..)
    by_cases hP : P a <;> by_cases hR : R a = true <;>
      simp [List.filter_cons, hP, hR, ha, ih']

theorem sum_filter_act1 (eF : Env F) (l : List (Ent ℚ)) (P : Ent ℚ → Prop) [DecidablePred P]
    (R : Ent ℚ → Bool)
    (hact : ∀ x ∈ l, evalQ x.act eF = if P x then 1 else 0) :
    (((l.filter R).map fun x => evalQ x.act eF).sum : F) =
      (((l.filter fun x => R x && decide (P x)).length : ℕ) : F) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => hact x (List.mem_cons_of_mem _ hx))
    have ha := hact a (List.mem_cons_self ..)
    by_cases hP : P a <;> by_cases hR : R a = true <;>
      simp [List.filter_cons, hP, hR, ha, ih', add_comm]

theorem filter_and_eq (l : List (Ent ℚ)) (P : Ent ℚ → Prop) [DecidablePred P] (R : Ent ℚ → Bool) :
    (l.filter fun x => R x && decide (P x)) = (l.filter fun x => decide (P x)).filter R := by
  rw [List.filter_filter]

/-- The pair's contribution when it is active. -/
def pairTerm (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (q : Prop) [Decidable q] : K :=
  match S.pair with
  | some (_, a, b) => if q then (evalMQ (den a) eK eF)⁻¹ + (evalMQ (den b) eK eF)⁻¹ else 0
  | none => 0

/-- **The slot terms are sums of `1/den` over the active records** (see the header). -/
theorem slot_term (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (P : Ent ℚ → Prop) [DecidablePred P]
    (q : Prop) [Decidable q]
    (hact : ∀ x ∈ S.ents, evalQ x.act eF = if P x then 1 else 0)
    (hfl : ∀ fl a b, S.pair = some (fl, a, b) → evalQ (cc fl) eF = if q then 1 else 0)
    (hq : S.pair = none → ¬ q)
    (hex : (S.ents.filter fun x => decide (P x)).length + (if q then 1 else 0) ≤ 1)
    (hpole : ∀ x ∈ S.ents, P x → evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ fl a b, S.pair = some (fl, a, b) → q →
      evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0)
    (D A : K)
    (hD : D = (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
          (match S.pair with
           | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
           | none => 0))
    (hA : A = algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
        (match S.pair with
         | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
         | none => 0))
    (hinv : eK.trace S.inv = A * D⁻¹) :
    algebraMap F K (evalQ S.actX eF) * eK.trace S.inv =
        ((S.ents.filter fun x => !x.path && decide (P x)).map fun x => (evalMQ (den x.rcd) eK eF)⁻¹).sum ∧
    algebraMap F K (evalQ S.actP eF) * eK.trace S.inv =
        ((S.ents.filter fun x => x.path && decide (P x)).map fun x => (evalMQ (den x.rcd) eK eF)⁻¹).sum
          + pairTerm S eK eF q := by
  -- the sums over all entries
  have hDs : (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum =
      ((S.ents.filter fun x => decide (P x)).map fun x => evalMQ (den x.rcd) eK eF).sum := by
    have := sum_filter_act (F := F) (K := K) eF S.ents P (fun _ => true) (fun x => evalMQ (den x.rcd) eK eF) hact
    simpa using this
  have hAs : (S.ents.map fun x => evalQ x.act eF).sum =
      (((S.ents.filter fun x => decide (P x)).length : ℕ) : F) := by
    have := sum_filter_act1 (F := F) eF S.ents P (fun _ => true) hact
    simpa using this
  have hXv : evalQ S.actX eF =
      (((S.ents.filter fun x => !x.path && decide (P x)).length : ℕ) : F) := by
    unfold SlotSpec.actX
    rw [evalQ_sumList]
    have := sum_filter_act1 (F := F) eF S.ents P (fun x => !x.path) hact
    simpa [Ent.act, evalQ_sumList] using this
  have hPv : evalQ S.actP eF = (((S.ents.filter fun x => x.path && decide (P x)).length : ℕ) : F) +
      (match S.pair with | some (fl, _, _) => evalQ (cc fl) eF | none => 0) := by
    unfold SlotSpec.actP
    have h1 : evalQ (CoeffExpr.sumList (S.ents.filter fun x => x.path) Ent.act) eF =
        (((S.ents.filter fun x => x.path && decide (P x)).length : ℕ) : F) := by
      rw [evalQ_sumList]
      exact sum_filter_act1 (F := F) eF S.ents P (fun x => x.path) hact
    rcases hp : S.pair with _ | ⟨fl, a, b⟩
    · simp only [evalQ, h1]; simp
    · simp only [evalQ, h1]
  rw [hXv, hPv, hinv, hD, hA, hDs, hAs, filter_and_eq, filter_and_eq]
  generalize hLd : S.ents.filter (fun x => decide (P x)) = L at *
  by_cases hq' : q
  · have hL0 : L = [] := by
      have : L.length + 1 ≤ 1 := by simpa [hq'] using hex
      exact List.length_eq_zero_iff.mp (by omega)
    subst hL0
    rcases hp : S.pair with _ | ⟨fl, a, b⟩
    · exact absurd hq' (hq hp)
    · obtain ⟨hda, hdb⟩ := hpoleP fl a b hp hq'
      have hf := hfl fl a b hp
      simp only [hp, hf, if_pos hq', pairTerm, hq'] at *
      simp
      field_simp
      ring
  · have hL1 : L.length ≤ 1 := by simpa [hq'] using hex
    rcases hy : L with _ | ⟨y, ys⟩
    · have : S.pair = none → True := fun _ => trivial
      rcases hp : S.pair with _ | ⟨fl, a, b⟩
      · simp [pairTerm, hp]
      · have hf := hfl fl a b hp
        simp only [hp, hf, if_neg hq', pairTerm]
        simp
    · have hys : ys = [] := by
        have h2 : (y :: ys).length ≤ 1 := hy ▸ hL1
        simp only [List.length_cons] at h2
        exact List.length_eq_zero_iff.mp (by omega)
      subst hys
      have hyP : P y := by
        have : y ∈ S.ents.filter (fun x => decide (P x)) := by rw [hLd, hy]; simp
        simpa using (List.mem_filter.mp this).2
      have hyM : y ∈ S.ents := by
        have : y ∈ S.ents.filter (fun x => decide (P x)) := by rw [hLd, hy]; simp
        exact (List.mem_filter.mp this).1
      have hd := hpole y hyM hyP
      rcases hp : S.pair with _ | ⟨fl, a, b⟩
      · cases hyp : y.path <;> simp [pairTerm, hp, hyp, hd]
      · have hf := hfl fl a b hp
        cases hyp : y.path <;> simp [pairTerm, hp, hyp, hd, hf, hq']

end SlotTerm

end

end Nock.NockVMROM.Thm54.VclL.Handle
