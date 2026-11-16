/-
  Nock/RedTeam/Batch4802Thm54J9bFinal.lean

  **THE bound over `AcceptsJ9V`** (big atoms in the claim), every layout.
  * `LinkJ9G.probJ9B_final`: `Pr_χ[(∃ M, AcceptsJ9V … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`, at `LinkJ8A.probJ8V_final`'s
    binders with ONE binder restated: `hreg : |censusG Pb c| ≤ 2^31` becomes `hreg9 : |censusG Pb c| + 6 ≤ 2^31`
    (the census list gains the claim extension `claimX`, at most 6 nouns, so the census weight stays `P = 2^66`).
  * `LinkJ9G.probJ9B_final_clean`: the same without the two derived instance binders (`CleanJ8`'s wrapper).
  Both go through the UNCHANGED `RepriceJ8.probJ8X_lt_155_census32`: no new coin, no new summand, same figure.
  `hreg_of_hreg9`: the restated binder implies the J-8 one.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G

set_option autoImplicit false

namespace Nock.RedTeam.Batch4802

open Nock.NockVMROM.Thm54.VclL.Handle

/-- The restated census binder implies the J-8 one. -/
theorem hreg_of_hreg9 {p : ℕ} [Fact p.Prime] (Pb : AcceptsJ8.PubJ8 p) (c : Nock.NockVMROM.Thm54.P8PublicClaim)
    (h : (AcceptsJ8P.censusG Pb c).length + 6 ≤ 2 ^ 31) : (AcceptsJ8P.censusG Pb c).length ≤ 2 ^ 31 := by omega

#check @LinkJ9G.probJ9B_final_clean
#print axioms LinkJ9G.probJ9_present
#print axioms LinkJ9G.probJ9B_final
#print axioms LinkJ9G.probJ9B_final_clean

end Nock.RedTeam.Batch4802
