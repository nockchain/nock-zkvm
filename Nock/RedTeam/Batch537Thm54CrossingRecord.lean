/-
  Nock/RedTeam/Batch537Thm54CrossingRecord.lean

  **Crossing record.**  Notes-only.  No status flip.
  No chip edit.

  Claim A: CONFIRMED at `Vmem`/`eqBlk`.  Full
  `memoryChipAt c` interpolant NOT constructed.  End-to-end
  `nockCompiles_zmod` false claim NOT constructed;
  the noun identity and the paper OP0 record shape are compiled.

  Claim B: both repairs reject the crossing; both break today's
  honest interior-read generator (F97 `aReadInnerPub`,
  `chainedInnerRootState`).  (A) is `:1429` taken literally
  (roots-only / stacked reads) and drops `:1413` interior batching;
  degree 5 as written, 4 if the `⊥` factor is dropped.
  (B) as `pt.counts = 0` at every `read_root` also rejects honest
  axis-2 leftovers (`pt.counts = 12` at F97).  Item F: `:1423-1424`
  0/1 coefficients are an assumption, not a `Vmem` gate.
-/
import Nock.RedTeam.Batch534Thm54CrossingVmem
import Nock.RedTeam.Batch535Thm54CrossingClaim
import Nock.RedTeam.Batch536Thm54CrossingRepairs

set_option autoImplicit false

namespace Nock.RedTeam.Batch537

open Nock.MemoryTable
open Nock.RedTeam.Batch534
open Nock.RedTeam.Batch535
open Nock.RedTeam.Batch536

def claimA_scope : String :=
  "CONFIRMED at Vmem/eqBlk (crossing_vmem). Full memoryChipAt interpolant NOT constructed. End-to-end nockCompiles NOT constructed."

def claimB_surviving_repair : String :=
  "Neither repair is completeness-safe against today's generator. (A) is the :1429 roots-only design; it rejects the crossing and honest interior reads. (B) rejects the crossing and honest F97 pt.counts = 12."

theorem claimA_confirmed_at_vmem :
    claimA_scope =
      "CONFIRMED at Vmem/eqBlk (crossing_vmem). Full memoryChipAt interpolant NOT constructed. End-to-end nockCompiles NOT constructed." :=
  rfl

theorem claimB_neither_completeness_safe :
    claimB_surviving_repair =
      "Neither repair is completeness-safe against today's generator. (A) is the :1429 roots-only design; it rejects the crossing and honest interior reads. (B) rejects the crossing and honest F97 pt.counts = 12." :=
  rfl

theorem live_crossing_vmem_named :
    let inp : Nock.MemoryTable.Inputs ℚ := { z := 2, γ := 0, β := 0 }
    Vmem inp (readR inp (5 : ℚ) 6 0 1) := by
  intro inp
  exact vmem_readR inp 5 6 0 1

theorem no_digest_move :
    (Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  chip_interpolant_not_constructed

end Nock.RedTeam.Batch537

#print axioms Nock.RedTeam.Batch537.claimA_confirmed_at_vmem
#print axioms Nock.RedTeam.Batch537.live_crossing_vmem_named
