import Nock.IO

/-
  Nock/RedTeam/Batch1280Thm54PinForcesIdentity.lean
-/

/-!
  `JU` §1 offers two reasons the memory-side `ln`/`ts` pin is unreachable:

  (a) "`ts(row j) = α^{j+1}` is *false* on the honest response trace", because `respRecs`
      flat-maps memory rows and only `read_root` rows serve a record;
  (b) "Forcing it on both sides would collapse the permutation to the identity and destroy
      the multiset argument".

  (a) is defeasible: a selector-gated counter column advancing only on `read_root` rows
  re-indexes the pin onto the served subsequence, so the indexing mismatch is not the
  obstruction.  (b) is the obstruction, and this file makes it a theorem rather than prose:
  a positional `ts` pin on BOTH sides of an `IO.LIO` pair forces the two record lists to be
  *equal as lists*, i.e. forces the permutation `σ` of `Def:L_IO` to be the
  identity.
-/

namespace Nock.RedTeam.Batch1280PinForcesIdentity

open List

/-- **The pin collapses the permutation.**  If a coordinate `f` reads the value `g i` at
index `i` on both lists, `g` is injective below the common length, and the two lists are a
permutation of one another, then they are equal as lists.

`f` is the record's timestamp slot, `g i = α^(i+1)` the positional pin, and injectivity of
`g` is exactly the distinctness of timestamp powers that `AxisSoundness.TimestampClosedAt`
and the orbit-order side condition supply. -/
theorem pin_forces_identity
    {R V : Type*} [DecidableEq R]
    (f : R → V) (g : ℕ → V)
    (req resp : List R)
    (hperm : req.Perm resp)
    (hreq : ∀ i (h : i < req.length), f req[i] = g i)
    (hresp : ∀ i (h : i < resp.length), f resp[i] = g i)
    (hg : ∀ i j, i < resp.length → j < resp.length → g i = g j → i = j) :
    req = resp := by
  have hlen : req.length = resp.length := hperm.length_eq
  apply List.ext_getElem hlen
  intro i h1 h2
  -- `req[i]` occurs in `resp`; say at index `j`
  have hmem : req[i] ∈ resp := hperm.mem_iff.mp (List.getElem_mem h1)
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
  have hgg : g i = g j := by
    rw [← hreq i h1, ← hje, hresp j hj]
  have hij : i = j := hg i j (hlen ▸ h1) hj hgg
  subst hij
  exact hje.symm

/-- The distinctness hypothesis is exactly an orbit-order condition: powers of `α` below the
order of `α` are pairwise distinct.  Stated for the positional pin `g i = α ^ (i + 1)`. -/
theorem pin_powers_injective
    {K : Type*} [Field K] (α : K) (n : ℕ)
    (hα : ∀ a b : ℕ, a < n → b < n → α ^ (a + 1) = α ^ (b + 1) → a = b) :
    ∀ i j, i < n → j < n → (fun k => α ^ (k + 1)) i = (fun k => α ^ (k + 1)) j → i = j :=
  hα

/-- Consequence for `IO.LIO`: under the two-sided positional pin, `IO.LIO` degenerates —
its `Perm` conjunct carries no information beyond list equality, so the response list is
forced to be the request list *in request order*.  That is a positional construction. -/
theorem lio_degenerates_under_two_sided_pin
    {R V : Type*} [DecidableEq R]
    (f : R → V) (g : ℕ → V) (Ksz : ℕ)
    (req resp : List R)
    (hlio : Nock.IO.LIO Ksz req resp)
    (hreq : ∀ i (h : i < req.length), f req[i] = g i)
    (hresp : ∀ i (h : i < resp.length), f resp[i] = g i)
    (hg : ∀ i j, i < resp.length → j < resp.length → g i = g j → i = j) :
    req = resp :=
  pin_forces_identity f g req resp hlio.2.2 hreq hresp hg

end Nock.RedTeam.Batch1280PinForcesIdentity

#print axioms Nock.RedTeam.Batch1280PinForcesIdentity.pin_forces_identity
#print axioms Nock.RedTeam.Batch1280PinForcesIdentity.lio_degenerates_under_two_sided_pin
