/-
  Nock/RedTeam/Batch4161Thm54J8r1AcceptsP.lean

  The verifier predicate without free post-coin lists: `MsgJ8'` carries no list; `toMsgJ8` computes `reqsC`
  (claim + pin records, verifier), `xsC / vp` (read from the atom table's `mb` rows), `wreqs` (the atom walk's
  handle reads).  `acceptsJ8_of'`: `AcceptsJ8'` ⇒ `AcceptsJ8` at `toMsgJ8` (g5 telescope `mbXs_sum`, walk telescope).
  Derived `LinkJ8` fields: `hcountC`, `hcountA`, `hinjE`, `hseed`, `hreal` (cell formula), `hs / hf / he`.
  `hsoundJ8'`, `probJ8_final'` (conditional on the residue `LinkJ8'` only), `acceptsJ8'_cFalse_rejected`.
  FINDING `chalsAJ8_zAt`: the g5 key's size entry reads `γ′^13`, not `z`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

namespace Nock.RedTeam.Batch4161

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

#check @hsoundJ8'
#check @probJ8_final'
#print axioms mbXs_sum
#print axioms mbXs_den
#print axioms keyVec_mbKey
#print axioms mbXs_claimVec
#print axioms mbVp_small
#print axioms mbVp_row
#print axioms chalsAJ8_zAt
#print axioms toMsgJ8_reqsC
#print axioms acceptsJ8_of'
#print axioms hcountC_of'
#print axioms hcountA_of'
#print axioms rkC_ne
#print axioms row0_hd
#print axioms den_claim
#print axioms hsoundJ8'
#print axioms acceptsJ8'_cFalse_rejected
#print axioms probJ8_final'
#check @hsoundJ8X'
#check @probJ8X_final'
#print axioms hsoundJ8X'
#print axioms probJ8X_final'

end Nock.RedTeam.Batch4161
