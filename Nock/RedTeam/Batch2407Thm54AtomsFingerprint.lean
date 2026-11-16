/-
  Nock/RedTeam/Batch2407Thm54AtomsFingerprint.lean

  Exact statements by `example`, and their axioms.

  * `L_injective`: atom ↦ leaf polynomial over `𝔽_p` is injective.
  * Step 1 (`card_roots'` once): `card_limb_collision_le`, `card_leafVal_collision_le`.
  * Step 2 (`card_roots'` a second time): `card_leafSum_collision_le`, the bivariate bound over
    `(z, y)`.
  * NC: `sameCoin_collision` / `sameCoin_collision_419` (the same-coin encoding collides at every
    `z`), with `sameCoin_collision_nouns_distinct`; positive control `limbCoin_separates`.
-/
import Nock.Atoms.Fingerprint

set_option autoImplicit false

namespace Nock.RedTeam.Batch2407

open Nock.Atoms Polynomial

example : Function.Injective L := L_injective
example (n : ℕ) : L n = if n < p then C (n : Fp) else limbPoly (limbs n) := rfl

example {K : Type} [Field K] [Algebra Fp K] [Fintype K] [DecidableEq K]
    {l l' : List ℕ} (hl : Canonical l) (hl' : Canonical l') (hne : l ≠ l') :
    (Finset.univ.filter (fun y : K => aeval y (limbPoly l) = aeval y (limbPoly l'))).card ≤
      max l.length l'.length - 1 :=
  card_limb_collision_le hl hl' hne

example {K : Type} [Field K] [Algebra Fp K] [Fintype K] [DecidableEq K] {n m : ℕ} (hne : n ≠ m) :
    (Finset.univ.filter (fun y : K => leafVal y n = leafVal y m)).card ≤ max (lenL n) (lenL m) - 1 :=
  card_leafVal_collision_le hne

example {K : Type} [Field K] [Algebra Fp K] [Fintype K] [DecidableEq K]
    {ns ms : List ℕ} (hlen : ns.length = ms.length) {j : ℕ} (hj : j < ns.length)
    (hdiff : ns[j] ≠ ms[j]'(hlen ▸ hj)) {N : ℕ}
    (hN : max (lenL ns[j]) (lenL (ms[j]'(hlen ▸ hj))) ≤ N) :
    (Finset.univ.filter (fun zy : K × K => leafSum zy.2 zy.1 ns = leafSum zy.2 zy.1 ms)).card ≤
      Fintype.card K * (ns.length - 1) + Fintype.card K * (N - 1) :=
  card_leafSum_collision_le hlen hj hdiff hN

example {K : Type} [Field K] (z : K) :
    Nock.ComputeTable.FP.cons z (sameCoinBig z [5, 2, 1]) (Nock.ComputeTable.FP.atomFP z 0) =
      Nock.ComputeTable.FP.cons z (sameCoinBig z [5, 1, 1]) (Nock.ComputeTable.FP.atomFP z 1) :=
  sameCoin_collision z

example : leafSum (K := Fp) 1 0 [val [5, 2, 1], 0] ≠ leafSum (K := Fp) 1 0 [val [5, 1, 1], 1] :=
  limbCoin_separates

end Nock.RedTeam.Batch2407

#print axioms Nock.Atoms.limbPoly_injOn
#print axioms Nock.Atoms.L_injective
#print axioms Nock.Atoms.card_agree_le
#print axioms Nock.Atoms.card_limb_collision_le
#print axioms Nock.Atoms.card_leafVal_collision_le
#print axioms Nock.Atoms.card_leafSum_collision_le
#print axioms Nock.Atoms.sameCoin_collision
#print axioms Nock.Atoms.sameCoin_collision_419
#print axioms Nock.Atoms.sameCoin_collision_nouns_distinct
#print axioms Nock.Atoms.limbCoin_separates
