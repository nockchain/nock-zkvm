/-
  Nock/RedTeam/Batch4800Thm54J9bClaim.lean

  * `ClaimJ9.pubVJ9` (the claim label's third arm `atom n ≥ p ↦ (2, idx)`), `claimRecsJ9`, `censusGJ9`;
  * the compute assembly over any public vector agreeing with `pubVJ8` at publics `≥ 12`
    (`HokJ9G` / `HokJ9GA`, present / absent atom walk).
  Receipts: conservativity (no big claim atom ⇒ `pubVJ9 = pubVJ8`), the claim records stay `≤ 3`, and a kind-2 label
  at a big claim atom.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
import Nock.NockVMROM.Thm54.VclL.Handle.HokJ9G
import Nock.NockVMROM.Thm54.VclL.Handle.HokJ9GA
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z

set_option autoImplicit false

namespace Nock.RedTeam.Batch4800

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)

/-- A big claim atom gets the kind-2 handle at the prover's serial; a small one keeps `(0, v)`. -/
theorem claimKH_big (p v idx : ℕ) (h : p ≤ v) : claimKH p (.atom v) idx = (2, idx) := by
  simp [claimKH, h]

theorem claimKH_small (p v idx : ℕ) (h : v < p) : claimKH p (.atom v) idx = (0, v) := by
  simp [claimKH, Nat.not_le.mpr h]

/-- The demo claim `*[[(p+5) 0] [0 2]] = p+5` has exactly one big claim atom, the result. -/
theorem demo_bigs (p : ℕ) :
    claimBigs p ⟨.cell (.atom (p + 5)) (.atom 0), .cell (.atom 0) (.atom 2), .atom (p + 5)⟩ = [2] := by
  simp [claimBigs, isBigN, claimNoun, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop]

#print axioms labelJ9_eq_labelF
#print axioms pubVJ9_eq_pubVJ8
#print axioms claimRecsJ9_length
#print axioms AcceptsJ9V.AcceptsJ9V
#print axioms HokJ9G.acceptsJ9_holdsN_finalLG
#print axioms HokJ9GA.acceptsJ9_holdsN_finalLGA
#print axioms AcceptsJ9Z.acceptsJ9ZA_of_V

end Nock.RedTeam.Batch4800
