/-
  The ALU layout fields of the lifted `PubJ9AL` are
  inert (`nL = 1`, `nodesL = 0`, the `orbitL`/`preL` of the J-9 AL toy `BL`).
-/
import Nock.RedTeam.Batch4883Thm54J9AComplToy
import Nock.RedTeam.Batch4921Thm54J9ALComplToy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4935

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4883 (BA sA fA rA)
open Nock.RedTeam.Batch4921 (BL)

/-- The lifted public layout: `BA.Pb` with an inert ALU layout and the ALU off. -/
noncomputable def PbN : RealIOJ9AL.PubJ9AL Nock.Field.p :=
  { toPubJ9A := BA.Pb
    hL := BL.Pb.hL
    nL := 1
    hnL := Nat.one_pos
    nodesL := fun _ => 0
    orbitL := BL.Pb.orbitL
    aluOn := false
    prims := []
    idxP := fun _ => 0
    rkP := fun _ => (1, 1)
    preL := BL.Pb.preL }

theorem regsA : BA.Pb.regs = [] := by
  have h := Nock.RedTeam.Batch4883.callsA
  show ((Nock.RedTeam.Batch4883.DD).calls.map Prod.fst).dedup = []
  rw [h]; rfl

open Classical in
/-- **`acceptsJ9AL_noAlu`: the J-9 AL acceptance predicate is satisfiable with the ALU off.**
At the J-9 A toy claim, over the empty verified registry, there are a coin, message, trace and row record at which
`AcceptsJ9AL` accepts, with the ALU off (`aluOn = false`) and no primitives (`prims = []`); the acceptance is
obtained from the J-9 A acceptance of the same run (`AcceptsJ9AL.of_A`). -/
theorem acceptsJ9AL_noAlu :
    ∃ χ M tr r g, AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 PbN Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ sA fA rA) χ M tr r g ∧ PbN.aluOn = false ∧ PbN.prims = [] := by
  obtain ⟨χ, hχ⟩ := Nock.RedTeam.Batch4883.complJ9A_toy_figure.2.2.2
  have hr := ComplJ9AClosed.rowsLe31A_runA deltaF powerBasis3 Nock.RedTeam.Batch4842.RtT
    Nock.RedTeam.Batch4883.genA rfl Nock.RedTeam.Batch4883.h31A
  have hn : BA.Pb.n ≤ 2 ^ 31 := hr.1.1
  have hC : BA.Pb.nC ≤ 2 ^ 31 := hr.1.2.1
  have hp : (2 : ℕ) ^ 31 + 2 ^ 31 + 2 ^ 31 + 10 < Nock.Field.p := by norm_num [Nock.Field.p]
  refine ⟨χ, { toMsgJ9A' := BA.M χ, pubsL := fun _ => 0 },
    { toTrJ9A := BA.tr χ, L := fun _ => 0 }, { toRowsJ9A := BA.rows, AL := 2 ^ 31 }, BA.g, ?_, rfl, rfl⟩
  refine AcceptsJ9AL.AcceptsJ9AL.of_A deltaF powerBasis3 (Pb := PbN) hχ (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl ⟨?_, ?_, ?_⟩ ?_
  · show 1 + BA.Pb.n < Nock.Field.p; omega
  · show 1 ≤ 2 ^ 31; norm_num
  · intro q hq; exact absurd hq (by simp [PbN])
  · show 3 + BA.Pb.regs.length + [].length + 1 + 2 * BA.Pb.nC < Nock.Field.p
    rw [regsA]; simp; omega

end Nock.RedTeam.Batch4935

#print axioms Nock.RedTeam.Batch4935.acceptsJ9AL_noAlu
