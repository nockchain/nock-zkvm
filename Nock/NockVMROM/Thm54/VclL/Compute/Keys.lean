import Nock.NockVMROM.Thm54.VclL.Compute.ChipVCL
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily
import Nock.NockVMROM.Thm54.RecordCarrier
import Nock.NockVMROM.Thm54.P8Core.VclL.Consumers

/-!
# V4c, the addendum's first deliverable: the `node_records` key probe at `computeChipVCL`

`CompSoundnessFamily.recKey` is typed on
`B0Cols F C` (`MemSoundnessFamily.lean`, r2 (3)), so a key slot is admissible on the compute side
exactly when it is a function of the round-0 columns.

1. **The compute B0 of `computeChipVCL`** (`colRoundVCL_zero_iff`): the base block `0..12` (state
   one-hot, fanout / count cells, masks), the new `vIdx₀, vIdx₁, idx/μ` columns `202..207`, and the
   serial `220`.  Nothing else; in particular every `𝕂`-role column `13..201` (fingerprints, record
   slots, decompositions) is round `≥ 1` (`roles_not_b0`).
2. **The export key is B0** (`export_key_clause`): the export record `(fp p, fp l, fp r, vIdx)` carries
   the consumed cell's serial in its slot `9`, the compute row commits it in the B0 column
   `vIdxCol j`, and `recKeyExport` (typed on `B0Cols`) reads that column: the clause
   `R.key r = recKey (b0 Q) …` holds by evaluation, for every trace.
3. A key reading
   only the root serial cannot be served: two honest reads of one root at axes `2` and `3`
   (`honest_two_axes_one_root`) force `served κ` to be both children
   (`root_serial_key_unservable`, against `MemSoundnessFamily.response_sound`'s slot clause).  The key
   must therefore carry the axis; on the compute side the axis of an OP0 / OP9 read is the formula
   atom `b` (`f_t.leaf` / `f_th.leaf`, option R "no new column"), which lives in a `𝕂`-role column,
   round `≥ 1`; and no `B0Cols`-typed `recKey` agrees with a key slot read from a non-B0 column
   (`nonB0_slot_not_b0_key`).
4. **The inline record `0`** (`inline_record_not_requested`): r2's `node_records` quantifies over
   every `j < recordCount st`, but VCL-L decomposes record `0` inline (no lookup,
   `Consumers.lookupsVCL`), e.g. `s1` has one record and zero lookups.

Paper: `:1728-1742` (`V_comp`), `:1751` (OP0's formula tail as the NMR address), `:1738` (OP9),
`:1456-1479` (rounds).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Framework Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.RecordCarrier
open Nock.NockVMROM.Thm54.VclL
open scoped Polynomial

noncomputable section

/-! ## 1. The compute table and its B0 columns -/

/-- The compute table of VCL-L: width `221`, round map `colRoundVCL`. -/
def tableVCL (h : ℕ) : TableSpec where
  width := vclWidth
  colRound := fun j => colRoundVCL j
  height := h

/-- The round-0 columns of `computeChipVCL`. -/
def IsB0VCL (c : ℕ) : Prop := c < 13 ∨ (202 ≤ c ∧ c < 208) ∨ c = 220

instance (c : ℕ) : Decidable (IsB0VCL c) := by unfold IsB0VCL; infer_instance

/-- **The compute B0, measured**: a column of `computeChipVCL` is round `0` iff it is a base cell
`0..12`, one of the six new B0 columns `202..207`, or the serial `220`. -/
theorem colRoundVCL_zero_iff : ∀ c : Fin 221, colRoundVCL c = 0 ↔ IsB0VCL c := by
  decide +kernel

/-- Every `𝕂`-role column (fingerprints, record slots, decompositions) is round `≥ 1`. -/
theorem roles_not_b0 (c : ℕ) (h1 : 13 ≤ c) (h2 : c < 202) : colRoundVCL c ≠ 0 := by
  have h13 : ¬ c < 13 := by omega
  simp only [colRoundVCL, if_pos h2, RepartitionedStaging.newComputeColRound, if_neg h13,
    RepartitionedStaging.newComputeRoleRound]
  split_ifs <;> omega

/-- The `vIdx` column `j` as a B0 column of the table. -/
def vIdxB0 (h : ℕ) (j : Fin 2) : {c : Fin (tableVCL h).width // (tableVCL h).colRound c = 0} :=
  ⟨⟨vIdxCol j, by have := j.isLt; simp only [tableVCL, vclWidth, vIdxCol]; omega⟩, colRoundVCL_vIdx j⟩

/-! ## 2. The export key reads B0 -/

/-- The key type of the addendum: a cell serial and a side. -/
abbrev KeyVCL := ℕ × Bool

section Export

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The export request record of a row at lookup `j` (`m_x = 10` over `K`): the nine fingerprint
coordinates `(p, l, r)` (round-1 role columns, given) and, in slot `9`, the consumed cell's serial,
read from the row's B0 column `vIdxCol j`. -/
def exportRecOfRow (fps : Fin 9 → K) (envF : Env F) (j : Fin 2) : Fin 10 → K :=
  fun k => if hk : (k : ℕ) < 9 then fps ⟨k, hk⟩ else algebraMap F K (envF.trace (vIdxCol j))

def keyOfExportRec (r : Fin 10 → K) : KeyVCL := (natLift (r 9), false)

/-- **`recKey` at an export lookup**: the B0 column `vIdxCol j` at the row's node, by type. -/
def recKeyExport {h : ℕ} (x : F) (b : B0Cols F (tableVCL h)) (j : Fin 2) : KeyVCL :=
  (natLift (algebraMap F K ((b (vIdxB0 h j)).eval x)), false)

/-- **The export key clause is B0** (one row, any trace, any node): the record's key is the B0
`recKey` of the row. -/
theorem export_key_clause {h : ℕ} (Q : Fin (tableVCL h).width → F[X]) (ω x : F) (chal pub : ℕ → F)
    (fps : Fin 9 → K) (j : Fin 2) :
    keyOfExportRec (exportRecOfRow fps (Reify.envOfTrace Q ω x chal pub) j) =
      recKeyExport (K := K) x (b0 (T := tableVCL h) Q) j := by
  have hj : vIdxCol j < (tableVCL h).width := by
    have := j.isLt; simp only [tableVCL, vclWidth, vIdxCol]; omega
  simp only [keyOfExportRec, exportRecOfRow, recKeyExport, b0, vIdxB0, Reify.envOfTrace,
    dif_pos hj]
  rfl

end Export

/-! ## 3. -/

/-- Any served oracle that answers two records of one key at two axes answers the same slot. -/
theorem served_slot_eq {Key : Type} (servedRoot served : Key → Noun) (κ : Key) (a₁ a₂ : ℕ)
    (h₁ : Noun.slot a₁ (servedRoot κ) = some (served κ))
    (h₂ : Noun.slot a₂ (servedRoot κ) = some (served κ)) :
    Noun.slot a₁ (servedRoot κ) = Noun.slot a₂ (servedRoot κ) :=
  h₁.trans h₂.symm

/-- The honest situation: one root cell `[0 1]` read at axis `2` (`[0 2]`) and at axis `3` (`[0 3]`)
— two distinct path records `(root, child, 2, rootIdx)`, `(root, child', 3, rootIdx)` with one root
serial. -/
theorem honest_two_axes_one_root :
    Noun.slot 2 (.cell (.atom 0) (.atom 1)) = some (.atom 0) ∧
      Noun.slot 3 (.cell (.atom 0) (.atom 1)) = some (.atom 1) := ⟨by simp [Noun.slot], by simp [Noun.slot]⟩

/-- **A root-serial path key is unservable**: no `(servedRoot, served)` answers both honest reads of
`honest_two_axes_one_root` at one key, i.e. `MemSoundnessFamily.response_sound`'s slot clause fails
for one of them. -/
theorem root_serial_key_unservable {Key : Type} (κ : Key) :
    ¬ ∃ servedRoot served : Key → Noun, servedRoot κ = .cell (.atom 0) (.atom 1) ∧
      Noun.slot 2 (servedRoot κ) = some (served κ) ∧ Noun.slot 3 (servedRoot κ) = some (served κ) := by
  rintro ⟨sR, sv, hR, h2, h3⟩
  have := served_slot_eq sR sv κ 2 3 h2 h3
  rw [hR] at this
  simp [Noun.slot] at this

/-- The general form, against an arbitrary record view: two records of one accumulator with one key
and the slot clause at two axes give equal slots of the served root. -/
theorem key_determines_slot {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
    {C : TableSpec} {S : MemShape} {hC nAcc : ℕ} {m : Fin nAcc → ℕ}
    (R : RecordView F K Kio Kfp Key C S hC m) (servedRoot served : Key → Noun) (a : Fin nAcc)
    (axis₁ axis₂ : ℕ) (r₁ r₂ : Fin (m a) → Kio) (hk : R.key a r₁ = R.key a r₂)
    (h₁ : Noun.slot axis₁ (servedRoot (R.key a r₁)) = some (served (R.key a r₁)))
    (h₂ : Noun.slot axis₂ (servedRoot (R.key a r₂)) = some (served (R.key a r₂))) :
    Noun.slot axis₁ (servedRoot (R.key a r₁)) = Noun.slot axis₂ (servedRoot (R.key a r₁)) := by
  rw [hk] at h₁ ⊢
  exact h₁.trans h₂.symm

/-- **A key slot read from a non-B0 column is not a B0 key**: for any `B0Cols`-typed `recKey` and any
column `c` of round `≠ 0`, the clause "the slot read at `c` equals `recKey (b0 Q)`" fails for some
trace (the two traces below differ only at `c`, so their B0 projections agree). -/
theorem nonB0_slot_not_b0_key {F : Type} [Field F] {h : ℕ} (hF : 3 < ringChar F)
    (c : Fin (tableVCL h).width) (hc : colRoundVCL c ≠ 0) (x : F)
    (recKey : B0Cols F (tableVCL h) → ℕ) :
    ¬ ∀ Q : Fin (tableVCL h).width → F[X], natLift ((Q c).eval x) = recKey (b0 (T := tableVCL h) Q) := by
  intro hall
  let Q₂ : Fin (tableVCL h).width → F[X] := fun j => if j = c then Polynomial.C 2 else 0
  let Q₃ : Fin (tableVCL h).width → F[X] := fun j => if j = c then Polynomial.C 3 else 0
  have hb : b0 (T := tableVCL h) Q₂ = b0 (T := tableVCL h) Q₃ := by
    funext j
    have hj : j.1 ≠ c := fun he => hc (by rw [← he]; exact j.2)
    simp [b0, Q₂, Q₃, hj]
  have e2 := hall Q₂
  have e3 := hall Q₃
  rw [hb, ← e3] at e2
  simp only [Q₂, Q₃, if_pos rfl, Polynomial.eval_C] at e2
  have n2 : natLift (2 : F) = 2 := by
    have := natLift_natCast (F := F) (n := 2) (by omega); simpa using this
  have n3 : natLift (3 : F) = 3 := by
    have := natLift_natCast (F := F) (n := 3) (by omega); simpa using this
  rw [n2, n3] at e2
  omega

theorem path_axis_key_needs_b1 {F : Type} [Field F] {h : ℕ} (hF : 3 < ringChar F)
    (c : ℕ) (h1 : 13 ≤ c) (h2 : c < 202) (x : F) (recKey : B0Cols F (tableVCL h) → ℕ) :
    ¬ ∀ Q : Fin (tableVCL h).width → F[X],
      natLift ((Q ⟨c, by simp only [tableVCL, vclWidth]; omega⟩).eval x) = recKey (b0 (T := tableVCL h) Q) :=
  nonB0_slot_not_b0_key hF _ (roles_not_b0 c h1 h2) x recKey

/-! ## 4. The inline record `0` -/

/-- r2's `node_records` asks, at an `s1` node, for a request record of record `0`; VCL-L looks up
none (the `[1 b]` opening is the inline cons, `Consumers.lookupsVCL`). -/
theorem inline_record_not_requested :
    Nock.Framework.recordCount .s1 = 1 ∧ lookupsVCL .s1 = 0 ∧
      ∀ s : Nock.ComputeTable.State, lookupsVCL s + inlineRecords s = Nock.Framework.recordCount s := by
  refine ⟨rfl, rfl, fun s => ?_⟩
  cases s <;> decide

end

end VclL.Compute
end Nock.NockVMROM.Thm54
