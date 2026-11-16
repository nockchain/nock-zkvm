/-
  Nock/RedTeam/Batch916Thm54Part2bEqBlkDoubleEncode.lean

  Nothing consumes this.

  Consequence: the
  encoded `specializedExec` of the trace-built strategy (`specialized_memoryForest_eq_encode`) cannot feed
  `Batch524.memoryTreeBinds_of_topology'` on such rows; `BindsAtCoin` needs the a-recovering wrap (`wrapJoin`)
  or the `specializeA` view.
-/
import Nock.MemoryTable
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree

namespace Nock.RedTeam.Batch916

open Nock Nock.MemoryTable Nock.ComputeTable

abbrev Z31 := ZMod 31
instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

def n0 : ComputeTable.FP Z31 := ⟨0, 0, 0⟩
def inp : MemoryTable.Inputs Z31 := ⟨5, 0, 0⟩

theorem pw4 : pwScaleExp Z31 = 4 := by
  unfold pwScaleExp
  rw [ZMod.ringChar_zmod_n]
  decide

/-- The honest `read_root` row: `T = 9`, `C' = 1`, `ts = 1`, `λ = 3`. -/
def honestRow : MemoryTable.Pub Z31 where
  st := .read_root
  pt := ⟨n0, 0 - 3 ^ 4 * 9 * 1, 0 - 9 * 1 * 1⟩
  lc := ⟨n0, 0, 0⟩
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := ⟨n0, n0, 9, 1⟩
  ipre := 0
  icur := 0
  cprime? := some 1
  lambda? := some 3

/-- The re-encoded row: the stored axis is encoded once more (`hW`'s double encode). -/
noncomputable def reencode (p : MemoryTable.Pub Z31) : MemoryTable.Pub Z31 :=
  { p with mem := { p.mem with axis := formRT p.lambda (nockAxisOf p.mem.axis) } }

theorem axis_reencoded : (reencode honestRow).mem.axis = 27 := by
  have hs := nockAxisOf_spec (K := Z31) (a := 9) (by rw [ZMod.ringChar_zmod_n]; norm_num)
  have hlt : nockAxisOf ((9 : ℕ) : Z31) < 31 := by
    have := hs.1; rwa [ZMod.ringChar_zmod_n] at this
  have h9 : nockAxisOf ((9 : ℕ) : Z31) = 9 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hs.2
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num)] at this
  have hax : honestRow.mem.axis = ((9 : ℕ) : Z31) := by simp [honestRow]
  show formRT (Pub.lambda honestRow) (nockAxisOf honestRow.mem.axis) = 27
  rw [hax, h9, show Pub.lambda honestRow = 3 from rfl]
  unfold formRT
  rw [show formRCertShift 9 = 3 from by decide]
  decide

theorem honest_eqBlk : eqBlk inp honestRow := by
  simp only [eqBlk, honestRow, Pub.cprime, Pub.lambda, pw4]
  decide

/-- The re-encoded row, written out. -/
def reencodedRow : MemoryTable.Pub Z31 := { honestRow with mem := { honestRow.mem with axis := 27 } }

theorem reencode_eq : reencode honestRow = reencodedRow := by
  have h := axis_reencoded
  unfold reencodedRow
  rw [← h]
  rfl

theorem reencodedRow_not_eqBlk : ¬ eqBlk inp reencodedRow := by
  simp only [eqBlk, reencodedRow, honestRow, Pub.cprime, Pub.lambda, pw4]
  decide

theorem reencoded_not_eqBlk : ¬ eqBlk inp (reencode honestRow) := by
  rw [reencode_eq]; exact reencodedRow_not_eqBlk

/-- **`FmemTopo` fails on the re-encoded row for every child assignment** (its `eqBlk`
conjunct is false). -/
theorem reencoded_not_fmemTopo (xout : Fin 2 → Option (MState × DTmem Z31)) :
    ¬ Nock.NockVMROM.Thm54.MemoryTopoBetaFree.FmemTopo
        (MState.read_root, (inp, reencode honestRow)) xout := by
  intro h
  exact reencoded_not_eqBlk h.2.1

/-- And it holds (its `eqBlk` conjunct) on the honest row: the failure is the re-encode, not
the row. -/
theorem honest_eqBlk_conjunct :
    (MState.read_root, (inp, honestRow)).2.2.st = (MState.read_root, (inp, honestRow)).1 ∧
      eqBlk (MState.read_root, (inp, honestRow)).2.1 (MState.read_root, (inp, honestRow)).2.2 :=
  ⟨rfl, honest_eqBlk⟩

end Nock.RedTeam.Batch916

#print axioms Nock.RedTeam.Batch916.reencoded_not_fmemTopo
#print axioms Nock.RedTeam.Batch916.honest_eqBlk
