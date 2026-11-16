import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Asymptotic

/-! Degeneracy witnesses for the soundness-bound, completeness and canonical-RAP clauses (S5 to S7) of the Nock VM-ROM capstone. Each shows that a clause is satisfied by a degenerate model, or that a model body ignores the VM, MEF or field parameters it is stated over. -/

namespace RTMore

open Nock Nock.Framework Nock.NockVMROM

instance rt_fact_prime_7' : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## N8 — S7 admits `bound := badProbability`, hence soundness error 1 -/

/-- For ANY trial space and ANY soundness-breaking probability, taking the bound to be that same
    function satisfies `HasConcreteSoundness`.  The class asks for no absolute bound at all. -/
def n8_bound_eq_badProb (ι : Type) [VMSystem ι] (T : Type) (p : T → ℚ) :
    HasConcreteSoundness ι ⟨T, p, p⟩ where
  sound := fun _ => le_rfl

/-- Concretely: the S7 clause is satisfied by a model whose soundness error is `1` on every
    trial — no security content.  Paper Theorem 5.4 asks for *negligible* soundness
    error. -/
def n8_soundness_error_one (ι : Type) [VMSystem ι] :
    HasConcreteSoundness ι ⟨Unit, fun _ => 1, fun _ => 1⟩ :=
  n8_bound_eq_badProb ι Unit (fun _ => 1)

/-- The same holds for the S5 two-RAP clause. -/
def n8_twoRAP_bound_eq_badProb (ι : Type) [VMSystem ι] (M : MEF) (F : Type) [CommRing F]
    (p q : Unit → ℚ) :
    HasTwoRAPVerification ι M F ⟨Unit, Unit, Unit, p, q, p, q, fun _ => True, 0⟩ where
  compute_sound := fun _ => le_rfl
  memory_sound := fun _ => le_rfl
  shared_io := ⟨(), trivial⟩

/-! ## N9 — S6 admits a vacuous `accepted` predicate -/

/-- `HasPerfectCompleteness` is satisfied by any model that accepts nothing. -/
def n9_vacuous_completeness (ι : Type) [VMSystem ι] (M : MEF) (F : Type) [CommRing F]
    (T : Type) : HasPerfectCompleteness ι M F ⟨T, fun _ => False, fun _ => False⟩ where
  complete := fun _ h => h.elim

/-! ## N10 — the stored S2 RAPs are not the paper's `RAP_NockComp-IO` / `RAP_NockMem-IO` -/

/-- The stored canonical RAPs describe a `2^1 = 2`-row trace with extension degree `1`, widths
    `94`/`35`, and an EMPTY evaluation domain — whereas Theorem 5.4's named RAPs
    `RAP_NockComp-IO`/`RAP_NockMem-IO` have `62·e+13`/`61·e+13` columns.  No `+IO` RAP is reified anywhere: `walkAIR`/`ioProgAIR`/`ioMemAIR` exist
    only as separate AIRs and are never composed into a RAP. -/
theorem n10_stored_RAPs_are_not_thm54_RAPs :
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rprog.e = 1 ∧
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rprog.h = 1 ∧
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rprog.w = 94 ∧
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rprog.H = ∅ ∧
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rmem.w = 36 ∧
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).Rmem.H = ∅ ∧
    Nock.NockVM.comp_io_columns 3 = 199 ∧ Nock.NockVM.mem_io_columns 3 = 196 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

/-! ## N11 — the four bundle *model parameters* are VM-, MEF- and field-agnostic -/

/-- `TwoRAPVerificationModel ι M F`'s body mentions none of `ι`, `M`, `F`. -/
def n11_twoRAP_transport {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂] {M₁ M₂ : MEF}
    {F₁ F₂ : Type} [CommRing F₁] [CommRing F₂]
    (m : TwoRAPVerificationModel ι₁ M₁ F₁) : TwoRAPVerificationModel ι₂ M₂ F₂ :=
  { ComputeTrial := m.ComputeTrial, MemoryTrial := m.MemoryTrial, IOWitness := m.IOWitness,
    computeBadProbability := m.computeBadProbability,
    memoryBadProbability := m.memoryBadProbability,
    computeBound := m.computeBound, memoryBound := m.memoryBound,
    rapIOAccepts := m.rapIOAccepts, ioBound := m.ioBound }

/-- …and `HasTwoRAPVerification` transports along it. -/
theorem n11_twoRAP_prop_transport {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂] {M₁ M₂ : MEF}
    {F₁ F₂ : Type} [CommRing F₁] [CommRing F₂] (m : TwoRAPVerificationModel ι₁ M₁ F₁)
    (h : HasTwoRAPVerification ι₁ M₁ F₁ m) :
    HasTwoRAPVerification ι₂ M₂ F₂ (n11_twoRAP_transport (ι₂ := ι₂) (M₂ := M₂) (F₂ := F₂) m) :=
  ⟨h.compute_sound, h.memory_sound, h.shared_io⟩

/-- `CompletenessModel ι M F`'s body mentions none of `ι`, `M`, `F`. -/
def n11_comp_transport {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂] {M₁ M₂ : MEF}
    {F₁ F₂ : Type} [CommRing F₁] [CommRing F₂]
    (m : CompletenessModel ι₁ M₁ F₁) : CompletenessModel ι₂ M₂ F₂ :=
  { Problem := m.Problem, accepted := m.accepted,
    hasSatisfyingAssignment := m.hasSatisfyingAssignment }

/-- `ConcreteSoundnessModel ι`'s body mentions no `ι`. -/
def n11_sound_transport {ι₁ ι₂ : Type} [VMSystem ι₁] [VMSystem ι₂]
    (m : ConcreteSoundnessModel ι₁) : ConcreteSoundnessModel ι₂ :=
  { Trial := m.Trial, badProbability := m.badProbability, bound := m.bound }

/-- Concretely: the shipped Nock S7 model, transported to the rejecting-VM tag, still verifies. -/
theorem n11_nock_sound_model_on_other_vm (ι : Type) [VMSystem ι] :
    HasConcreteSoundness ι
      (n11_sound_transport (ι₂ := ι) (nockConcreteSoundness (ZMod 7) (ZMod 7) 0 1 1)) :=
  ⟨(nock_hasConcreteSoundness (ZMod 7) (ZMod 7) 0 1 1).sound⟩

#print axioms n11_twoRAP_transport
#print axioms n11_twoRAP_prop_transport
#print axioms n11_comp_transport
#print axioms n11_sound_transport
#print axioms n11_nock_sound_model_on_other_vm
#print axioms n8_bound_eq_badProb
#print axioms n8_soundness_error_one
#print axioms n8_twoRAP_bound_eq_badProb
#print axioms n9_vacuous_completeness
#print axioms n10_stored_RAPs_are_not_thm54_RAPs

end RTMore
