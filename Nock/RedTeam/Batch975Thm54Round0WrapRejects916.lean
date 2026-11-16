/-
  Nock/RedTeam/Batch975Thm54Round0WrapRejects916.lean

  A `read_root` row storing `T = 9 = formRT 3 4` (axis 4, shift 2) satisfies `eqBlk`, and
  the lifted wrap's specialization re-encodes the stored slot, `formRT 3 (nockAxisOf 9) = 27`,
  which breaks `eqBlk` (so `FmemTopo` fails for every child assignment).

  Here, on the Form R row of axis 4 (`T = 9`, `C' = formRC 3 4 = 81 ≡ 19`, `ts = 1 = α⁰`):
  * **the round-0 route reproduces the row** — `wrapMemoryLabelR0 0 4` (exponent `0`, recovered
    axis `4`) then `specialize α 3` IS the row, at every `α` (`r0_route_identity`), so `eqBlk`
    holds and `FmemTopo`'s `eqBlk` conjunct holds (`r0_route_eqBlk`);
  * **the lifted route breaks it** — its specialization stores `27` (`lifted_route_axis`) and
    `C' = formRC 3 9 ≡ 22`, and fails `eqBlk` whenever `0 < orderOf α` (then `ts = α⁰ = 1`;
    `lifted_route_not_eqBlk`), e.g. at `α = 1` (`lifted_route_not_fmemTopo_at_one`, every child
    assignment);
-/
import Nock.RedTeam.Batch973Thm54Round0WrapJoin
import Nock.RedTeam.Batch916Thm54Part2bEqBlkDoubleEncode

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch975

open Nock Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch916

noncomputable section

/-- The Form R `read_root` row of axis `4` at `λ = 3`: `T = 9`, `C' = 19`, `ts = 1`. -/
def row4 : MemoryTable.Pub Z31 where
  st := .read_root
  pt := ⟨n0, 0 - 3 ^ 4 * 9 * 1, 0 - 9 * 19 * 1⟩
  lc := ⟨n0, 0, 0⟩
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := ⟨n0, n0, 9, 1⟩
  ipre := 0
  icur := 0
  cprime? := some 19
  lambda? := some 3

theorem nockAxisOf_4 : nockAxisOf ((4 : ℕ) : Z31) = 4 :=
  nockAxisOf_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem nockAxisOf_9 : nockAxisOf ((9 : ℕ) : Z31) = 9 :=
  nockAxisOf_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem formRT_3_4 : formRT (3 : Z31) 4 = 9 := by
  unfold formRT; rw [show formRCertShift 4 = 2 from by decide]; decide

theorem formRT_3_9 : formRT (3 : Z31) 9 = 27 := by
  unfold formRT; rw [show formRCertShift 9 = 3 from by decide]; decide

theorem formRC_3_4 : formRC (3 : Z31) 4 = 19 := by
  simp only [MemoryTable.formRC, pw4]
  decide

theorem formRC_3_9 : formRC (3 : Z31) 9 = 22 := by
  simp only [MemoryTable.formRC, pw4]
  decide

theorem row4_eqBlk : eqBlk inp row4 := by
  simp only [eqBlk, row4, Pub.cprime, Pub.lambda, pw4]
  decide

/-- **The round-0 route reproduces the row**, at every `α`. -/
theorem r0_route_identity (α : Z31) :
    (wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3 =
      (MState.read_root, (inp, row4)) := by
  apply Batch973.specialize_wrapR0_eq_self
  · rfl
  · rfl
  · intro h; exact absurd h (by decide)
  · intro _
    refine ⟨by simp [row4], ?_, ?_⟩
    · show (9 : Z31) = formRT 3 (nockAxisOf ((4 : ℕ) : Z31))
      rw [nockAxisOf_4, formRT_3_4]
    · show some (19 : Z31) = some (formRC 3 (nockAxisOf ((4 : ℕ) : Z31)))
      rw [nockAxisOf_4, formRC_3_4]

theorem r0_route_eqBlk (α : Z31) :
    eqBlk inp ((wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3).2.2 := by
  rw [r0_route_identity]; exact row4_eqBlk

/-- `FmemTopo`'s `eqBlk` conjunct holds on the round-0 route. -/
theorem r0_route_fmemTopo_eqBlk_conjunct (α : Z31) :
    ((wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3).2.2.st =
        ((wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3).1 ∧
      eqBlk ((wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3).2.1
        ((wrapMemoryLabelR0 0 4 (MState.read_root, (inp, row4))).specialize α 3).2.2 := by
  rw [r0_route_identity]; exact ⟨rfl, row4_eqBlk⟩

/-- **The lifted route re-encodes the stored `9` to `27`**, at every `α`. -/
theorem lifted_route_axis (α : Z31) :
    ((StrategyOfTracesLift.wrapMemoryLabel α (MState.read_root, (inp, row4))).specialize α 3).2.2.mem.axis
      = 27 := by
  have hact : memoryMemRecKind MState.read_root = .active := rfl
  simp only [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
    MemoryRowTemplate.specializeA, StrategyOfTracesLift.wrapMemoryLabel, specializeMemRec, hact,
    if_true, decide_true, NockVM.formRRow, row4]
  have h9 := nockAxisOf_9
  simp only [Nat.cast_ofNat] at h9
  rw [h9, formRT_3_9]

theorem memExponent_one {α : Z31} (hα : 0 < orderOf α) :
    StrategyOfTracesLift.memExponent α 1 = 0 := by
  unfold StrategyOfTracesLift.memExponent
  have hex : ∃ n : ℕ, n < orderOf α ∧ α ^ n = 1 := ⟨0, hα, pow_zero α⟩
  rw [dif_pos hex]
  exact (Nat.find_eq_zero hex).mpr ⟨hα, pow_zero α⟩

/-- **The lifted route breaks `eqBlk`** whenever `0 < orderOf α`. -/
theorem lifted_route_not_eqBlk {α : Z31} (hα : 0 < orderOf α) :
    ¬ eqBlk inp
      ((StrategyOfTracesLift.wrapMemoryLabel α (MState.read_root, (inp, row4))).specialize α 3).2.2 := by
  have hact : memoryMemRecKind MState.read_root = .active := rfl
  have h9 := nockAxisOf_9
  simp only [Nat.cast_ofNat] at h9
  simp only [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
    MemoryRowTemplate.specializeA, StrategyOfTracesLift.wrapMemoryLabel, specializeMemRec, hact,
    if_true, decide_true, NockVM.formRRow, NockVM.formRCprime, row4]
  rw [show (StrategyOfTracesLift.memExponent α 1) = 0 from memExponent_one hα, h9, formRT_3_9,
    formRC_3_9]
  simp only [eqBlk, Pub.cprime, Pub.lambda, pw4, pow_zero]
  decide

theorem orderOf_one_pos : 0 < orderOf (1 : Z31) := by rw [orderOf_one]; decide

/-- At `α = 1`, `FmemTopo` fails on the lifted route for EVERY child assignment. -/
theorem lifted_route_not_fmemTopo_at_one (xout : Fin 2 → Option (MState × DTmem Z31)) :
    ¬ MemoryTopoBetaFree.FmemTopo
        ((StrategyOfTracesLift.wrapMemoryLabel 1 (MState.read_root, (inp, row4))).specialize 1 3)
        xout := by
  intro h
  exact lifted_route_not_eqBlk orderOf_one_pos h.2.1

theorem r0_route_axis_on_916 (e : ℕ) (α : Z31) :
    ((wrapMemoryLabelR0 e 4 (MState.read_root, (inp, honestRow))).specialize α 3).2.2.mem.axis = 9 ∧
      (9 : Z31) ≠ (reencode honestRow).mem.axis := by
  have hact : memoryMemRecKind MState.read_root = .active := rfl
  refine ⟨?_, ?_⟩
  · simp only [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
      MemoryRowTemplate.specializeA, wrapMemoryLabelR0, specializeMemRec, hact, if_true,
      decide_true, NockVM.formRRow]
    rw [nockAxisOf_4, formRT_3_4]
  · rw [axis_reencoded]; decide

end

end Nock.RedTeam.Batch975

#print axioms Nock.RedTeam.Batch975.r0_route_identity
#print axioms Nock.RedTeam.Batch975.r0_route_eqBlk
#print axioms Nock.RedTeam.Batch975.lifted_route_axis
#print axioms Nock.RedTeam.Batch975.lifted_route_not_eqBlk
#print axioms Nock.RedTeam.Batch975.lifted_route_not_fmemTopo_at_one
#print axioms Nock.RedTeam.Batch975.r0_route_axis_on_916
