/-
  Nock/RedTeam/Batch2143Thm54VSQDescent.lean

  New module `DescentVSQ`; additive.

  * `envOfTrace_congrW`, `compReqs_congrW`, `walkLists_congrW`, `cellProvs_congrW`: the round-0 record
    lists agree across DIFFERENT widths (and orbits) when the round-0 columns agree;
  * `listsQ_at`: at every coin, `reqX0 / provX0 / reqP0 / provP0 (toVSV V) (projQ tr)` are the VSQ
    chips' `cXQ ++ wXQ`, `tXQ`, `cPQ`, `wPQ`;
  * `cXQ_len`: compute consumer budgets `3N` / `2N` at the `𝕂′` twin;
  * `den_of_not_pole`, `out_evXQ`, `out_evPQ`, `cPQ_den`: outside the `𝕂′` handle summands, the lifted
    events fail and every lifted denominator is nonzero;
  * **`kX_identity` / `kP_identity`**: at an accepted VSQ coin outside `ioSummandHXQ / ioSummandHPQ`,
    `Σ_{reqX0} f = Σ_{provX0} w · f` and `Σ_{reqP0} f = Σ_{provP0} w · f` for EVERY `f`
    (`BalanceQ.logup_descends`);
  * positive control: the pole-hit component fires on a vanishing denominator (`ZMod 5`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ

namespace Nock.RedTeam.Batch2143

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle

#print axioms DescentVSQ.envOfTrace_congrW
#print axioms DescentVSQ.compReqs_congrW
#print axioms DescentVSQ.walkLists_congrW
#print axioms DescentVSQ.cellProvs_congrW
#print axioms DescentVSQ.listsQ_at
#print axioms DescentVSQ.cXQ_len
#print axioms DescentVSQ.den_of_not_pole
#print axioms DescentVSQ.out_evXQ
#print axioms DescentVSQ.out_evPQ
#print axioms DescentVSQ.cPQ_den
#print axioms DescentVSQ.kP_identity
#print axioms DescentVSQ.kX_identity

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Positive control: a record whose denominator vanishes (`4 + 1 = 0` in `ZMod 5`) puts the pole in
`IOPoleHitEvent`, so `den_of_not_pole`'s hypothesis is a real restriction. -/
theorem pole_hit_fires :
    (4 : ZMod 5) ∈ IOPoleHitEvent (recordsW [fun _ : Fin 1 => (1 : ZMod 5)] []) 0 := by
  decide

/-- ...and a pole that hits no record is outside it. -/
theorem pole_hit_misses :
    (0 : ZMod 5) ∉ IOPoleHitEvent (recordsW [fun _ : Fin 1 => (1 : ZMod 5)] []) 0 := by
  decide

#print axioms pole_hit_fires
#print axioms pole_hit_misses

end Nock.RedTeam.Batch2143
