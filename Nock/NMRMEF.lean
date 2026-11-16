import Nock.Framework.Core
import Nock.NMR
import Mathlib.GroupTheory.OrderOfElement

/-!
# `nmrMEF` — the semantic NMR memory-encoding family + the bounded field-timestamp encoding

So the memory-encoding family used for `Def:MES` uses **semantic** timestamps `k ∈ ℕ` (`nmrMEF`,
with a genuine `LinearOrder`), and the field-timestamped `NMR^{α,β}` records are recovered by a
**bounded-injective encoding** `NMRRecordEncoding` (`k ↦ β^k`, injective while `k < orderOf β`).

Consequence: S1 (`UniqueMemoryExecutionSeparable`) is proved **exactly over `nmrMEF`**, and is
`1-1*` w.r.t. the paper's literal field-timestamped `NMR^{α,β}` — bridged faithfully here.
-/

namespace Nock

open Nock.Framework

/-- **Semantic NMR memory-encoding family (SC10).**  Address = axis `∈ 𝔽`; value domain = the pair
    of `𝕂³` NPR fingerprints `(root_fn, child_fn)`; timestamp set = `ℕ` (the *semantic* access
    exponent `k`, carrying a genuine `LinearOrder`, unlike the field element `β^k`). -/
@[reducible] def nmrMEF (F K : Type) [Field F] [Field K] : MEF where
  A := F
  VD := (K × K × K) × (K × K × K)
  T := ℕ
  Tord := inferInstance

@[simp] theorem nmrMEF_A (F K : Type) [Field F] [Field K] : (nmrMEF F K).A = F := rfl
@[simp] theorem nmrMEF_VD (F K : Type) [Field F] [Field K] :
    (nmrMEF F K).VD = ((K × K × K) × (K × K × K)) := rfl
@[simp] theorem nmrMEF_T (F K : Type) [Field F] [Field K] : (nmrMEF F K).T = ℕ := rfl

/-- **`NMRRecordEncoding` — the faithful bridge `nmrMEF.Rec → NMR.Rec` (SC18).**  Maps a semantic
    record `(axis, (root_fn, child_fn), k)` to the field-timestamped `NMR^{α,β}` record with
    `timestamp = β^k`, preserving axis and value verbatim, and **injective on the bounded window**
    `{k < B}` whenever `B ≤ orderOf β` (so distinct semantic times give distinct field timestamps).
    This is the exact sense in which S1-over-`nmrMEF` faithfully models S1-over-`NMR^{α,β}`. -/
structure NMRRecordEncoding (F K : Type) [Field F] [Field K] (β : K) where
  /-- The record encoding `k ↦ β^k`. -/
  encode : (nmrMEF F K).Rec → NMR.Rec F K
  /-- Axis preserved. -/
  encode_axis : ∀ r, (encode r).axis = r.1
  /-- Value (both fingerprints) preserved. -/
  encode_value : ∀ r, ((encode r).root_fn, (encode r).child_fn) = r.2.1
  /-- Semantic exponent time realized as the field power `β^k`. -/
  encode_time : ∀ r, (encode r).timestamp = β ^ r.2.2
  /-- Injective while the semantic time stays below `orderOf β` (SC18 faithfulness). -/
  injective_bounded : ∀ {B : ℕ}, B ≤ orderOf β → Set.InjOn encode {r | r.2.2 < B}

/-- **The canonical `NMRRecordEncoding`.**  `(axis, (root_fn, child_fn), k) ↦ ⟨root_fn, child_fn,
    axis, β^k⟩`, with the bounded-injectivity discharged from `pow_injOn_Iio_orderOf`. -/
def nmrEncoding (F K : Type) [Field F] [Field K] (β : K) : NMRRecordEncoding F K β where
  encode r := { root_fn := r.2.1.1, child_fn := r.2.1.2, axis := r.1, timestamp := β ^ r.2.2 }
  encode_axis _ := rfl
  encode_value _ := rfl
  encode_time _ := rfl
  injective_bounded := by
    intro B hB r hr r' hr' heq
    simp only [Set.mem_setOf_eq] at hr hr'
    simp only [NMR.Rec.mk.injEq] at heq
    obtain ⟨hroot, hchild, haxis, htime⟩ := heq
    have hk : r.2.2 = r'.2.2 :=
      pow_injOn_Iio_orderOf (Set.mem_Iio.mpr (lt_of_lt_of_le hr hB))
        (Set.mem_Iio.mpr (lt_of_lt_of_le hr' hB)) htime
    exact Prod.ext haxis (Prod.ext (Prod.ext hroot hchild) hk)

end Nock

#print axioms Nock.nmrEncoding
