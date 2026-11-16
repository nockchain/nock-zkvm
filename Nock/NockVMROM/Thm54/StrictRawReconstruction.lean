/-
  Nock/NockVMROM/Thm54/StrictRawReconstruction.lean

  Packet 2 of the Theorem 5.4 north star: active fingerprint realization at the field
  characteristic, and the pair-local faithfulness it buys.

  * **`FPRealized` is a bare existential (vacuity risk).**  `FPRealized z q fp` only
    says *some* `q`-bounded noun encodes to `fp`; a prover need not exhibit it.  `ActiveRealization`
    is the *data-carrying* version: the prover commits the actual witness noun pre-`z`, its
    canonical-residue bound, and the encoding equation.  `ActiveRealization.fpRealized` upgrades it to
    `FPRealized`, so realization is witnessed, not assumed.

  * **The cast-injectivity premise `hcast : Set.InjOn (·:ℕ→K) (Iio q)` is threaded everywhere.**  At
    the field characteristic it is *free*: `charCast_injOn` derives it from `CharP K p`.  Hence, when
    the atom range is the characteristic (canonical field nouns, Packet 0), the pair-local
    faithfulness `noun_eq_of_enc_eq` / `PairFaithful.eq_of_enc_eq` needs **no external hypothesis**
    (`ActiveRealization.noun_eq`, `pairFaithful_eq_at_char`).

  This is the atomic building block of `BindsAt`: a single committed fingerprint is bound to a unique
  bounded noun at the characteristic.  Deriving the *whole-execution* `BindsAt` from acceptance (not
  as a universal proof-side premise) remains the documented raw-arbitrary-prover crux; this module
  makes its per-fingerprint step honest and hypothesis-free at the characteristic.
-/

import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.StrictReleaseContract
import Mathlib.Algebra.CharP.Basic

namespace Nock.NockVMROM.Thm54
namespace StrictRawReconstruction

open Nock Nock.Noun ComputeTable

variable {K : Type} [Field K]

/-! ## The cast-injectivity premise is free at the characteristic -/

/-- **`hcast` for free.**  The natural-number cast is injective on the canonical-residue window
`[0, p)` whenever `p` is the characteristic of `K`.  This is exactly the `hinj`/`hcast` hypothesis
consumed by `noun_eq_of_enc_eq`, `PairFaithful.eq_of_enc_eq`, and `accepted_outside_failureUnion`. -/
theorem charCast_injOn (p : ℕ) [CharP K p] :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio p) := by
  intro a ha b hb hab
  exact CharP.natCast_injOn_Iio K p ha hb hab

/-! ## Active realization: a committed witness noun -/

/-- **Active fingerprint realization.**  The data a prover commits pre-`z` to make a fingerprint
`fp` honest: the witness noun, its canonical-residue bound `< p`, and the encoding equation.  Unlike
`FPRealized`, this is data, not an existential. -/
structure ActiveRealization (z : K) (p : ℕ) (fp : FP K) where
  /-- The committed witness noun. -/
  noun : Noun
  /-- Every atom is a canonical residue `< p` (the field characteristic), i.e.
      `CanonicalFieldNoun p noun`. -/
  bounded : FieldEmbedding.BoundedBy p noun
  /-- The fingerprint is the NPR encoding of the committed noun at seed `z`. -/
  realizes : GlobalCarryRecognizer.enc z noun = fp

/-- **Active realization upgrades to `FPRealized`.**  The bare existential is witnessed by the
committed data. -/
theorem ActiveRealization.fpRealized {z : K} {p : ℕ} {fp : FP K}
    (a : ActiveRealization z p fp) : FPRealized z p fp :=
  ⟨a.noun, a.bounded, a.realizes⟩

/-- **Pair-local uniqueness at the characteristic, with no external cast hypothesis.**  Two active
realizations of the *same* fingerprint whose witnesses are NPR-separated have equal witness nouns. -/
theorem ActiveRealization.noun_eq {z : K} {p : ℕ} [CharP K p] {fp : FP K}
    (a b : ActiveRealization z p fp)
    (hsep : GlobalCarryRecognizer.SepSeed z a.noun b.noun) :
    a.noun = b.noun :=
  GlobalCarryRecognizer.noun_eq_of_enc_eq z a.noun b.noun hsep (charCast_injOn p)
    a.bounded b.bounded (a.realizes.trans b.realizes.symm)

/-! ## Pair-local faithfulness at the characteristic -/

/-- A pair-local faithfulness datum is available for any two canonical field nouns that are
NPR-separated at `z`. -/
theorem pairFaithful_of_canonical {z : K} {p : ℕ} {l r : Noun}
    (hl : CanonicalFieldNoun p l) (hr : CanonicalFieldNoun p r)
    (hsep : GlobalCarryRecognizer.SepSeed z l r) :
    OpcodeSemantics.PairFaithful z p l r :=
  ⟨hsep, hl, hr⟩

/-- **`PairFaithful.eq_of_enc_eq` is hypothesis-free at the characteristic.**  A fingerprint equality
of two pair-faithful canonical nouns forces noun equality with no external `hcast`. -/
theorem pairFaithful_eq_at_char {z : K} {p : ℕ} [CharP K p] {l r : Noun}
    (h : OpcodeSemantics.PairFaithful z p l r)
    (heq : GlobalCarryRecognizer.enc z l = GlobalCarryRecognizer.enc z r) :
    l = r :=
  h.eq_of_enc_eq (charCast_injOn p) heq

end StrictRawReconstruction
end Nock.NockVMROM.Thm54
