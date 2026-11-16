/-
  Nock/RedTeam/Batch3331Thm54J8bHonestComputeBase.lean

  * `colX` / `hEnvX`: the honest columns `0.. 68` of a noun row (`RowNX`) under a handle map `H`
    (`HdlOK`: small atom `(0, v)`, big atom kind `2`, cell kind `1`) and the op-5 α-pair limb data
    `pd` (`PairOK`, a named row-level hypothesis on `isPair` rows).
  * `RowOKX p r`: the per-state row facts the gates need (`RowNX.SemN` plus small axis / id atoms,
    the op-5 first-difference shape and the real-child formulas being cells).
  * `arith_eq_hold`: every arithmetic gate (one-hot, kinds, all 17 state arms, the 23 kid-kind gates)
    and every equality gate (incl. the claim publics, `PubOK`) vanishes at the honest row; split per
    state as `restA_sX` / `restE_sX`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

namespace Nock.RedTeam.Batch3331

open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

#print axioms kind_hold
#print axioms oneHot_hold
#print axioms claim_hold
#print axioms restA_s5
#print axioms restE_s5
#print axioms restA_s10L
#print axioms restA_hold
#print axioms restE_hold
#print axioms arith_eq_hold

end Nock.RedTeam.Batch3331
