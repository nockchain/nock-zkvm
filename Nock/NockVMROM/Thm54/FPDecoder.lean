import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.BoundGates

/-!
# Fingerprint decoder (Track B)

`FPRealized` is a *propositional* existence statement: it says a bounded noun preimage exists but
carries no function from field data back to a noun. Track B needs the converse direction — given an
accepted fingerprint that passes the leaf/decode bound gate (`BoundGates.LeafBoundGate`, i.e.
`FPRealized`), recover the noun it encodes — so it can rebuild a skeleton from committed arrays.

This module supplies that decoder as a total (noncomputable) function on the **gated domain**: every
fingerprint that passes the bound gate is decoded to a bounded noun with a verified round-trip
`enc z (decode …) = fp`. The decoder is exactly the witness extracted from the gate, which is why
the bound gate (Track B0) is a strict prerequisite: on an ungated fingerprint like `badFP` there is
no witness to extract.

Decode uniqueness is pair-local: a candidate preimage equals the chosen decode when their concrete
pair satisfies `SepSeed` and bounded Nat-cast injectivity.  The batch proof supplies `SepSeed`
outside the counted bad-seed event, while Nat-cast injectivity is a separate deterministic range
hypothesis; no global bounded-domain injectivity theorem is required (and the concrete regression
below shows that such a premise is false already at `z = 1`, `q = 1`).  Assembly of per-row decoded
nouns into a full `SemanticSkeleton` with `BindsAt` remains separate.
-/

namespace Nock.NockVMROM.Thm54

open Nock

noncomputable section

variable {K : Type} [Field K]

/-- Decode a gate-passing fingerprint to the bounded noun it encodes. Defined as the witness of the
leaf/decode bound gate `FPRealized z q fp`; total on the gated domain. -/
noncomputable def decodeFP {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) : Noun :=
  h.choose

/-- The decoded noun is `q`-bounded. -/
theorem decodeFP_bounded {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    FieldEmbedding.BoundedBy q (decodeFP h) :=
  h.choose_spec.1

/-- **Verified round-trip.** The decoded noun encodes back to the original fingerprint. -/
theorem decodeFP_roundtrip {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (decodeFP h) = fp :=
  h.choose_spec.2

/-- **The decoder is total exactly on the gated domain.** A fingerprint is decodable iff it passes
the leaf/decode bound gate; equivalently, the gate is precisely the decodability predicate. -/
theorem decodable_iff_boundGate {z : K} {q : ℕ} {fp : ComputeTable.FP K} :
    (∃ n : Noun, FieldEmbedding.BoundedBy q n ∧ GlobalCarryRecognizer.enc z n = fp) ↔
      BoundGates.LeafBoundGate z q fp :=
  Iff.rfl

/-- **The forgery is undecodable.** `badFP` fails the bound gate, so no round-trip witness exists —
the decoder is undefined there, which is the intended behavior. -/
theorem badFP_undecodable (q : ℕ) :
    ¬ ∃ n : Noun,
        FieldEmbedding.BoundedBy q n ∧
          GlobalCarryRecognizer.enc (1 : NounRealizationCounterRegression.K289) n =
            NounRealizationCounterRegression.badFP :=
  NounRealizationCounterRegression.badFP_not_realized q

/-- **Pair-local uniqueness of the decode.** A bounded candidate preimage equals the chosen decode
when this concrete pair is separated at `z` and Nat-casts are injective below `q`.  The batch proof
supplies `SepSeed` outside its counted bad-seed event; this is not a global injectivity premise. -/
theorem decodeFP_unique {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp)
    (n : Noun) (hn : FieldEmbedding.BoundedBy q n)
    (hne : GlobalCarryRecognizer.enc z n = fp)
    (hsep : GlobalCarryRecognizer.SepSeed z n (decodeFP h))
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    n = decodeFP h :=
  GlobalCarryRecognizer.noun_eq_of_enc_eq z n (decodeFP h)
    hsep hcast hn (decodeFP_bounded h) (hne.trans (decodeFP_roundtrip h).symm)

/-! ## Regression: the former global premise is false -/

namespace FPDecoderCounterRegression

abbrev K289 := NounRealizationCounterRegression.K289

/-- The right-associated three-zero noun `[0,[0,0]]`. -/
def leftCollisionNoun : Noun :=
  .cell (.atom 0) (.cell (.atom 0) (.atom 0))

/-- The left-associated three-zero noun `[[0,0],0]`. -/
def rightCollisionNoun : Noun :=
  .cell (.cell (.atom 0) (.atom 0)) (.atom 0)

/-- At `z = 1`, both three-leaf shapes have the same size coordinate, their Dyck coordinates
evaluate to the same internal-node count, and their zero leaves give the same leaf coordinate. -/
theorem collision_enc_eq :
    GlobalCarryRecognizer.enc (1 : K289) leftCollisionNoun =
      GlobalCarryRecognizer.enc (1 : K289) rightCollisionNoun := by
  rw [leftCollisionNoun, rightCollisionNoun]
  rw [GlobalCarryRecognizer.enc_cons (by norm_num : (1 : K289) ≠ 0)]
  rw [GlobalCarryRecognizer.enc_cons (by norm_num : (1 : K289) ≠ 0)]
  rw [GlobalCarryRecognizer.enc_cons (by norm_num : (1 : K289) ≠ 0)]
  rw [GlobalCarryRecognizer.enc_cons (by norm_num : (1 : K289) ≠ 0)]
  simp [GlobalCarryRecognizer.enc_atom, ComputeTable.FP.cons, ComputeTable.FP.atomFP]

/-- The collision nouns have genuinely different ordered binary-tree shapes. -/
theorem collision_nouns_ne : leftCollisionNoun ≠ rightCollisionNoun := by
  decide

/-- Both collision nouns are bounded by the explicit common atom bound `q = 1`. -/
theorem collision_nouns_bounded :
    FieldEmbedding.BoundedBy 1 leftCollisionNoun ∧
      FieldEmbedding.BoundedBy 1 rightCollisionNoun := by
  norm_num [leftCollisionNoun, rightCollisionNoun, FieldEmbedding.BoundedBy]

/-- The former global bounded-domain injectivity premise is false at the concrete parameters
`K289`, `z = 1`, and `q = 1`. -/
theorem old_global_injectivity_false :
    ¬ (∀ n₁ n₂ : Noun,
      FieldEmbedding.BoundedBy 1 n₁ →
      FieldEmbedding.BoundedBy 1 n₂ →
      GlobalCarryRecognizer.enc (1 : K289) n₁ =
        GlobalCarryRecognizer.enc (1 : K289) n₂ →
      n₁ = n₂) := by
  intro hinj
  exact collision_nouns_ne
    (hinj leftCollisionNoun rightCollisionNoun
      collision_nouns_bounded.1 collision_nouns_bounded.2 collision_enc_eq)

end FPDecoderCounterRegression

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.decodeFP_roundtrip
#print axioms Nock.NockVMROM.Thm54.decodeFP_bounded
#print axioms Nock.NockVMROM.Thm54.decodable_iff_boundGate
#print axioms Nock.NockVMROM.Thm54.badFP_undecodable
#print axioms Nock.NockVMROM.Thm54.decodeFP_unique
#print axioms Nock.NockVMROM.Thm54.FPDecoderCounterRegression.collision_enc_eq
#print axioms Nock.NockVMROM.Thm54.FPDecoderCounterRegression.collision_nouns_ne
#print axioms Nock.NockVMROM.Thm54.FPDecoderCounterRegression.collision_nouns_bounded
#print axioms Nock.NockVMROM.Thm54.FPDecoderCounterRegression.old_global_injectivity_false
