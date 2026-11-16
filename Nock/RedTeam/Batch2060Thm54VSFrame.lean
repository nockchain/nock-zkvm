/-
  Nock/RedTeam/Batch2060Thm54VSFrame.lean

  **The VS instance's cores.**  New module
  `Thm54/VclL/Handle/FrameVS.lean`: `frameVS` (15 coins: `frameVCL`'s 11 + `γH ρH αW γW` after round
  0), the coin maps `chalsVS` (memory, leaves 33/34 = `γH/ρH`) and `chalVH` (compute limbs 0..11),
  the compute publics `pubVH` (claim handles 0..5, `αW`, the walk seed, `Re ρ₃ / Re ρ₄`), the claim
  message `ClaimMsgVS` and the verifier-computed claim validity records `claimRecs` / `claimValSum`,
  the tables `tableVS` (70) / `shapeVS` (232 / 151) with their round maps, the gated chips
  `chipCVS` / `chipMVS`, the cores `compCoreVS` / `memCoreVS` (summands as parameters, honest
  `Empty`), and the unpacking of `AcceptsG` (`compute_facts`, `cell_facts`, `walk_facts`).

  Discriminating control: acceptance forces `ρ₁ = 0` (the fingerprint export request is empty at VS)
  and the verifier's claim sum at `ρ₀`; the rejecting chip accepts nothing.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

set_option autoImplicit false

namespace Nock.RedTeam.Batch2060

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.T0Tower

example (hC : ℕ) : (tableVS hC).width = 70 := rfl
example : frameVS.n = 15 := rfl

section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- **Control**: an accepted VS transcript has an empty fingerprint export request and the
verifier-computed claim validity sum at accumulator 0. -/
theorem accepted_requests_forced (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM))
    (χ : Coins frameVS K) (h : AcceptsG V msg χ) :
    msg.requests χ 1 = 0 ∧ msg.requests χ 0 = claimValSum δF V.claim msg.msg0C χ :=
  let hg := (compute_facts δF hT hP kr hC V msg χ h).1
  ⟨hg.2.2.2.2.1, hg.2.2.2.1⟩

end

#print axioms frameVS_new_round0
#print axioms toVCL_sampled
#print axioms chalsVS_hGam
#print axioms chalsVS_hRho
#print axioms chalsVS_old
#print axioms colRoundCH_shift
#print axioms colRoundWH_shift
#print axioms rejectChipW_unsat
#print axioms chipCVS_width
#print axioms chipMVS_width
#print axioms claimRecs_length_le
#print axioms compute_facts
#print axioms cell_facts
#print axioms walk_facts
#print axioms accepted_requests_forced

end Nock.RedTeam.Batch2060
