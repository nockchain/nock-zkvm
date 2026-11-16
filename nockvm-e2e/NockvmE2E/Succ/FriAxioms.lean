/-
axiom guard: every declaration below must depend on `[propext, Classical.choice, Quot.sound]` only.
-/
import NockvmE2E.Succ.FriDeep

#print axioms NockvmE2E.Succ.App.appExt_terminal
#print axioms NockvmE2E.Succ.App.appExt_preserving
#print axioms NockvmE2E.Succ.App.appExt_bounded
#print axioms NockvmE2E.Succ.App.sum_appErr
#print axioms NockvmE2E.Succ.App.sup_appErr_le
#print axioms NockvmE2E.Succ.FriC.sufExt_ks
#print axioms NockvmE2E.Succ.FriC.rap_fri_sound
#print axioms NockvmE2E.Succ.FriDeep.udDecode_lt_card
#print axioms NockvmE2E.Succ.FriDeep.udDecode_le_card
#print axioms NockvmE2E.Succ.FriDeep.udDecode_eq
#print axioms NockvmE2E.Succ.FriDeep.deep_hbind
#print axioms NockvmE2E.Succ.FriDeep.rap_fri_sound_deep
