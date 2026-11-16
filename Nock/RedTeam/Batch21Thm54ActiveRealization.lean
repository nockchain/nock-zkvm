/-
  Nock/RedTeam/Batch21Thm54ActiveRealization.lean

  Locked facts:

  1. **The cast-injectivity premise `hcast` is free at the characteristic** — no external hypothesis
     is needed once the atom range is the field characteristic (canonical field nouns).
  2. **Active realization upgrades to `FPRealized`** — the bare existential is witnessed by committed
     data, removing the vacuity risk.
  3. **Pair-local uniqueness holds hypothesis-free at the characteristic** — two active realizations
     of one fingerprint, NPR-separated, have equal witness nouns; and `PairFaithful.eq_of_enc_eq`
     needs no external cast premise.
-/

import Nock.NockVMROM.Thm54.StrictRawReconstruction

namespace Nock.RedTeam.Batch21

open Nock Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictRawReconstruction

variable {K : Type} [Field K]

/-- **`hcast` is free at the characteristic.** -/
theorem b21_hcast_free_at_char (p : ℕ) [CharP K p] :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio p) :=
  charCast_injOn p

/-- **Active realization upgrades to `FPRealized`.** -/
theorem b21_active_upgrades_fpRealized {z : K} {p : ℕ} {fp : ComputeTable.FP K}
    (a : ActiveRealization z p fp) : FPRealized z p fp :=
  a.fpRealized

/-- **Pair-local witness uniqueness at the characteristic, no external cast hypothesis.** -/
theorem b21_active_noun_unique {z : K} {p : ℕ} [CharP K p] {fp : ComputeTable.FP K}
    (a b : ActiveRealization z p fp)
    (hsep : GlobalCarryRecognizer.SepSeed z a.noun b.noun) :
    a.noun = b.noun :=
  a.noun_eq b hsep

/-- **`PairFaithful.eq_of_enc_eq` is hypothesis-free at the characteristic.** -/
theorem b21_pairFaithful_free_at_char {z : K} {p : ℕ} [CharP K p] {l r : Noun}
    (h : OpcodeSemantics.PairFaithful z p l r)
    (heq : GlobalCarryRecognizer.enc z l = GlobalCarryRecognizer.enc z r) :
    l = r :=
  pairFaithful_eq_at_char h heq

/-- **A concrete active realization exists**, so the notion is non-vacuous: any bounded noun realizes
its own encoding. -/
theorem b21_active_realization_nonvacuous {z : K} {p : ℕ} {n : Noun}
    (hn : FieldEmbedding.BoundedBy p n) :
    FPRealized z p (GlobalCarryRecognizer.enc z n) :=
  (ActiveRealization.mk n hn rfl).fpRealized

end Nock.RedTeam.Batch21

#print axioms Nock.RedTeam.Batch21.b21_hcast_free_at_char
#print axioms Nock.RedTeam.Batch21.b21_active_upgrades_fpRealized
#print axioms Nock.RedTeam.Batch21.b21_active_noun_unique
#print axioms Nock.RedTeam.Batch21.b21_pairFaithful_free_at_char
