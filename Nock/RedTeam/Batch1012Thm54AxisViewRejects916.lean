/-
  Nock/RedTeam/Batch1012Thm54AxisViewRejects916.lean

  Brief item 4.

  `BindsAtCoin` reads the row-level `SemanticStrategy.BindMemRow z s r C' λ`, whose record equations
  are `r.axis = formRT λ (nockAxisOf s.axis)` and `C' = formRC λ (nockAxisOf s.axis)` with `s.axis`
  the SKELETON's record axis.  On the Form R `read_root` row of axis `4` (`Batch975.row4`: `T = 9`,
  `C' = 19`, the row the round-0 route reproduces, `Batch975.r0_route_identity`):

  * **the skeleton `strategyOfTracesR0` carries fails**: `decodedSkeletonOf` decodes the typed
    forest, whose records have `axis = 0` (`typedMemoryLabel`), so its skeleton axis is
    `leafAtomOf 31 0 = 0` and `BindMemRow` demands `T = formRT 3 (nockAxisOf 0) = 1 ≠ 9`
    (`typed_skeleton_axis_rejected`);
  * **the a-bearing skeleton holds**: with the recovered axis `4` both record equations are the
    row's stored values (`new_route_axis_facts`: the `haxisA` instance of
    `Batch1010.memoryTreeBinds_of_topologyA` at this row).
-/
import Nock.RedTeam.Batch975Thm54Round0WrapRejects916
import Nock.NockVMROM.Thm54.StrategyOfTracesR0A

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1012

open Nock Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.RedTeam.Batch916
open Nock.RedTeam.Batch975

noncomputable section

theorem nockAxisOf_0 : nockAxisOf ((0 : ℕ) : Z31) = 0 :=
  nockAxisOf_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem formRT_3_0 : formRT (3 : Z31) 0 = 1 := by
  unfold formRT; rw [show formRCertShift 0 = 0 from by decide]; rfl

/-- `leafAtomOf 31 0 = 0`: the typed skeleton's record axis. -/
theorem leafAtomOf_31_0 : leafAtomOf 31 (0 : Z31) = 0 := by
  have h : ∃ k : ℕ, k < 31 ∧ (k : Z31) = 0 := ⟨0, by norm_num, by norm_num⟩
  have hlt := leafAtomOf_lt h
  have hc := leafAtomOf_cast h
  have : (leafAtomOf 31 (0 : Z31) : ZMod 31).val = (0 : ZMod 31).val := by rw [hc]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at this
  simpa using this

/-- **The typed skeleton's axis (`0`) is rejected** by `BindMemRow`'s axis equation on `row4`
(`T = 9 ≠ 1`): `strategyOfTracesR0`'s own skeleton cannot satisfy `BindsAtCoin` on this row,
whatever the nouns. -/
theorem typed_skeleton_axis_rejected (s : MemRecSkeleton) (hs : s.axis = leafAtomOf 31 (0 : Z31)) :
    ¬ BindMemRow (3 : Z31) s row4.mem row4.cprime row4.lambda := by
  intro h
  have hax := h.2.2.1
  rw [hs, leafAtomOf_31_0] at hax
  change (9 : Z31) = formRT (Pub.lambda row4) (nockAxisOf ((0 : ℕ) : Z31)) at hax
  rw [nockAxisOf_0, show Pub.lambda row4 = 3 from rfl, formRT_3_0] at hax
  exact absurd hax (by decide)

theorem leafAtomOf_31_9 : leafAtomOf 31 (9 : Z31) = 9 := by
  have h : ∃ k : ℕ, k < 31 ∧ (k : Z31) = 9 := ⟨9, by norm_num, by norm_num⟩
  have hlt := leafAtomOf_lt h
  have hc := leafAtomOf_cast h
  have : (leafAtomOf 31 (9 : Z31) : ZMod 31).val = (9 : ZMod 31).val := by rw [hc]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at this
  rw [this]; rfl

theorem old_route_axis_rejected (s : MemRecSkeleton) (hs : s.axis = leafAtomOf 31 (9 : Z31)) :
    ¬ BindMemRow (3 : Z31) s row4.mem row4.cprime row4.lambda := by
  intro h
  have hax := h.2.2.1
  rw [hs, leafAtomOf_31_9] at hax
  change (9 : Z31) = formRT (Pub.lambda row4) (nockAxisOf ((9 : ℕ) : Z31)) at hax
  rw [nockAxisOf_9, show Pub.lambda row4 = 3 from rfl, formRT_3_9] at hax
  exact absurd hax (by decide)

/-- **The a-bearing skeleton holds** on `row4`: with the recovered axis `4` the two record
equations of `BindMemRow` are the row's stored `(T, C') = (9, 19)` — the `haxisA` instance. -/
theorem new_route_axis_facts :
    row4.mem.axis = formRT row4.lambda (nockAxisOf ((4 : ℕ) : Z31)) ∧
      row4.cprime = formRC row4.lambda (nockAxisOf ((4 : ℕ) : Z31)) := by
  rw [nockAxisOf_4, show Pub.lambda row4 = 3 from rfl, formRT_3_4, formRC_3_4]
  exact ⟨rfl, rfl⟩

/-- `BindMemRow`'s record clauses at axis `4`, with the nouns' fingerprint equations assumed: the
only clauses the axis view changes are the two above. -/
theorem new_route_bindMemRow (s : MemRecSkeleton) (hs : s.axis = 4)
    (hroot : bindFP (3 : Z31) s.root row4.mem.root)
    (hchild : bindFP (3 : Z31) s.child row4.mem.child) :
    BindMemRow (3 : Z31) s row4.mem row4.cprime row4.lambda := by
  refine ⟨hroot, hchild, ?_, ?_⟩
  · rw [hs]; exact new_route_axis_facts.1
  · rw [hs]; exact new_route_axis_facts.2

theorem literal_916_cprime_rejected (s : MemRecSkeleton) (hs : s.axis = 4) :
    ¬ BindMemRow (3 : Z31) s honestRow.mem honestRow.cprime honestRow.lambda := by
  intro h
  have hc := h.2.2.2
  rw [hs] at hc
  change (1 : Z31) = formRC (Pub.lambda honestRow) (nockAxisOf ((4 : ℕ) : Z31)) at hc
  rw [nockAxisOf_4, show Pub.lambda honestRow = 3 from rfl, formRC_3_4] at hc
  exact absurd hc (by decide)

end

end Nock.RedTeam.Batch1012

#print axioms Nock.RedTeam.Batch1012.typed_skeleton_axis_rejected
#print axioms Nock.RedTeam.Batch1012.old_route_axis_rejected
#print axioms Nock.RedTeam.Batch1012.new_route_axis_facts
#print axioms Nock.RedTeam.Batch1012.new_route_bindMemRow
#print axioms Nock.RedTeam.Batch1012.literal_916_cprime_rejected
