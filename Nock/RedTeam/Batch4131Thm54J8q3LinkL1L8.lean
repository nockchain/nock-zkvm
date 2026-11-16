/-
  Nock/RedTeam/Batch4131Thm54J8q3LinkL1L8.lean

  L8: `AcceptsJ8` reads the claim only through `labelF` (cell nouns: `(1, idx)`; atoms
  mod `p`), so `cFalse` is accepted wherever `cTrue` is and `hs` is the false field (`hs_false_cFalse`).  L1:
  `padM` (p copies of a request) preserves `AcceptsJ8` and breaks `hcountC`, so `probJ8_final`'s `hlink` forces
  no acceptance (`hlink_forces_no_accept`); `padX` shows `rdV` cannot hold at two messages accepted at one
  `(tr, χ)` (`not_rdV_both`): the prover messages are unstaged.  Discharged: L8 `hseed` (`hseedJ8`) and `hreal` at
  a cell formula (`hrealJ8`), from `AcceptsJ8` and `17 < p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3

namespace Nock.RedTeam.Batch4131

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3

#check @hs_false_cFalse
#check @hlink_forces_no_accept
#check @not_rdV_both
#print axioms holdsN_cTrue
#print axioms not_holdsN_cFalse
#print axioms pubVJ8_claim_congr
#print axioms acceptsJ8_claim_congr
#print axioms acceptsJ8_cFalse_of_cTrue
#print axioms acceptsJ8_atom_wrap
#print axioms linkJ8_cFalse_of_cTrue
#print axioms no_linkJ8_cFalse
#print axioms hs_false_cFalse
#print axioms acceptsJ8_padM
#print axioms not_linkJ8_padM
#print axioms hlink_forces_no_accept
#print axioms acceptsJ8_padX
#print axioms not_rdV_both
#print axioms xctxJ8
#print axioms row0_claim
#print axioms hseedJ8
#print axioms hrealJ8

end Nock.RedTeam.Batch4131
