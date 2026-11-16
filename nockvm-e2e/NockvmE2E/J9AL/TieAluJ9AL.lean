/-
  ("TieAluJ9AL"): the Emit-level facts for the J-9 AL ALU chip, with no
dependence on `InstJ9AL`.
  * `decR_alu`   : the reversed-table decode of the emitted ALU DAG equals the template's gates (`decide +kernel`, one template);
  * `chk_alu`    : the leaf-class check `chkT aluTemplate 6 chalAL` (`decide +kernel`, one template);
  * `SlotY`, `chalE_aluDers_eq`, `slotOK_XL`, `slotY_X` : the loader slot map of `aluDers` is the audited challenge vector
    (the frame coins, the `γ′` powers of `jDers` and the limb-coin powers `y^t` of `yDers`);
  * `chalsAL_eq`, `fL_leaf` : the ALU challenge vector `chalsALJ8` against the slot map `fL`.
Not zero-knowledge (the prover is RS+FRI without masking).
-/
import NockvmE2E.Exec.E2EJ8F
import NockvmE2E.Emit.ChipsJ9AL
import NockvmE2E.Emit.TieR
import NockvmE2E.J8.TieJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option maxRecDepth 100000

namespace NockvmE2E.J9AL.TieAluJ9AL

open NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec NockvmE2E.Exec.J8Chips
open NockvmE2E.J8.TieJ8 (chkT χf KN)
open NockvmE2E.J8.InstJ8 (Φ0)
open NockvmE2E.Exec.E2EJ8F
open NockvmE2E.J8.TieJ8G (chalK)
open NockvmE2E.Exec.E2EJ8P2 (sl0X sl1X)
open Nock.TraceGenExe (deltaF)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower

/-! ## 1. the two template-level kernel checks (one template each; never a whole instance) -/

theorem decR_alu : decodeDagR emit_alu = some aluSpec.gates := by decide +kernel

/-- the ALU's leaf predicate on challenge slots: `chalsALJ8` reads the atom vector `j ≤ 38` and the powers `40 ≤ j < 106` -/
def chalAL : ℕ → Bool := fun i => decide (i ≤ 38 ∨ (40 ≤ i ∧ i < 106))

theorem chk_alu : chkT aluTemplate 6 chalAL = true := by decide +kernel

/-! ## 2. the challenge vector of the ALU -/

/-- the ALU's challenge vector over the coins `χ : ℕ → KC` (`chalsALJ8` of nock, restated as `atomVec` + powers of `y = (χ17, χ18)`) -/
noncomputable def alVec (χ : ℕ → KC) (j : ℕ) : KC :=
  if 40 ≤ j ∧ j < 106 then
    (if j % 2 = 0 then (NockvmE2E.Exec.DagSemV.qpow (χ 17) (χ 18) ((j - 40) / 2)).1
     else (NockvmE2E.Exec.DagSemV.qpow (χ 17) (χ 18) ((j - 40) / 2)).2)
  else NockvmE2E.Emit.atomVec χ j

/-- the verifier reads the powers `y^t`, `t ≤ 32`, at slots `41 + 2t` (Re) and `42 + 2t` (Im) -/
structure SlotY (E χ : ℕ → KC) : Prop where
  hy : ∀ t, t ≤ 32 → E (41 + 2 * t) = (NockvmE2E.Exec.DagSemV.qpow (χ 17) (χ 18) t).1 ∧
    E (42 + 2 * t) = (NockvmE2E.Exec.DagSemV.qpow (χ 17) (χ 18) t).2

theorem ypowC_eq_qpow (y1 y2 : KN) : ∀ t, AluSZChipJ9.ypowC deltaF y1 y2 t = NockvmE2E.Exec.DagSemV.qpow y1 y2 t
  | 0 => rfl
  | t + 1 => by
      have ih := ypowC_eq_qpow y1 y2 t
      have h7 : algebraMap (ZMod Nock.Field.p) KN deltaF = 7 := by
        have : deltaF = (7 : ZMod Nock.Field.p) := rfl
        rw [this]; exact map_ofNat _ 7
      simp only [AluSZChipJ9.ypowC, NockvmE2E.Exec.DagSemV.qpow, ih, h7]
      rfl

theorem chalsAL_eq (χ : NockvmE2E.Rap.Coins Φ0 KN) (j : ℕ) (hj : j ≤ 38 ∨ 40 ≤ j) (hj2 : j < 106) :
    AluSZChipJ9.chalsALJ8 deltaF χ j = alVec (χf χ) j := by
  unfold AluSZChipJ9.chalsALJ8 alVec
  by_cases h : 40 ≤ j ∧ j < 106
  · simp only [h, and_self, ite_true]
    have e1 : χ FrameJ8.cY1 = χf χ 17 := by simp [χf, FrameJ8.cY1]; rfl
    have e2 : χ FrameJ8.cY2 = χf χ 18 := by simp [χf, FrameJ8.cY2]; rfl
    rw [e1, e2, ypowC_eq_qpow]
    rfl
  · simp only [h, ite_false]
    exact NockvmE2E.J8.TieJ8.chalsA_eq χ j (by omega)

theorem fL_leaf {E χ : ℕ → KC} (hE : NockvmE2E.Emit.SlotOK E χ) (hY : SlotY E χ) (j : ℕ) (hj : j ≤ 38 ∨ 40 ≤ j) (hj2 : j < 106) :
    E (fL j) = alVec χ j := by
  unfold fL alVec
  by_cases h : 40 ≤ j ∧ j < 106
  · simp only [h, and_self, ite_true]
    have ht : (j - 40) / 2 ≤ 32 := by omega
    obtain ⟨hre, him⟩ := hY.hy ((j - 40) / 2) ht
    by_cases hp : j % 2 = 0
    · have : 41 + (j - 40) = 41 + 2 * ((j - 40) / 2) := by omega
      rw [this, hre]; simp [hp]
    · have : 41 + (j - 40) = 42 + 2 * ((j - 40) / 2) := by omega
      rw [this, him]; simp [hp]
  · simp only [h, ite_false]
    exact NockvmE2E.Emit.fA_leaf hE j (by omega)

/-! ## 3. the loader slot map of `aluDers` -/

theorem order_none_y : ∀ i : ℕ, i < 66 → (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 41 + i) = none := by decide +kernel
theorem jders_none_y : ∀ i : ℕ, i < 66 → jDers.find? (·.slot == 41 + i) = none := by decide +kernel
theorem ydersFind : ∀ t : ℕ, t ≤ 32 →
    (match aluDers.find? (·.slot == 41 + 2 * t) with
      | some d => d.re == 17 && d.im == 18 && d.power == t && d.isRe == true
      | none => false) = true ∧
    (match aluDers.find? (·.slot == 42 + 2 * t) with
      | some d => d.re == 17 && d.im == 18 && d.power == t && d.isRe == false
      | none => false) = true := by decide +kernel
theorem idx17 : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 17) = some (J8Shape.slotOfJ8[17]!) := by decide +kernel
theorem idx18 : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 18) = some (J8Shape.slotOfJ8[18]!) := by decide +kernel

/-- on every coin slot and on every `jDers` slot the two derived-slot tables agree (`aluDers = jDers ++ yDers`) -/
theorem chalE_aluDers_eq (v : ℕ → KC) (i : ℕ)
    (h : i < 19 ∨ (jDers.find? (·.slot == i)).isSome = true) :
    NockvmE2E.Exec.DagSemV.chalE aluDers jMeta v i = NockvmE2E.Exec.DagSemV.chalE jDers jMeta v i := by
  unfold NockvmE2E.Exec.DagSemV.chalE
  simp only []
  cases hfi : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == i) with
  | some q => rfl
  | none =>
    rcases h with h | h
    · exfalso
      rw [order_find i h] at hfi
      exact absurd hfi (by simp)
    · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
      have : aluDers.find? (·.slot == i) = some d := by
        unfold aluDers yDers
        rw [Array.find?_append, hd]; rfl
      simp only [this, hd]

theorem slotOK_XL (χ : NockvmE2E.Rap.Coins Φ0 KC) :
    NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE aluDers jMeta (chalK Φ0 sl0X sl1X χ)) (NockvmE2E.J8.TieJ8.χf χ) := by
  have h := slotOK_X χ
  refine ⟨fun i hi => ?_, fun m hm => ?_⟩
  · rw [chalE_aluDers_eq _ i (Or.inl hi)]; exact h.hcoin i hi
  · have hs : (jDers.find? (·.slot == 19 + m)).isSome = true := by
      have : ∀ m : ℕ, m < 22 → (jDers.find? (·.slot == 19 + m)).isSome = true := by decide +kernel
      exact this m hm
    rw [chalE_aluDers_eq _ _ (Or.inr hs)]; exact h.hder m hm

theorem slotY_X (χ : NockvmE2E.Rap.Coins Φ0 KC) :
    SlotY (NockvmE2E.Exec.DagSemV.chalE aluDers jMeta (chalK Φ0 sl0X sl1X χ)) (NockvmE2E.J8.TieJ8.χf χ) := by
  have h17 : chalK Φ0 sl0X sl1X χ J8Shape.slotOfJ8[17]! = χ ⟨17, by decide⟩ := chalK_coin χ 17 (by decide)
  have h18 : chalK Φ0 sl0X sl1X χ J8Shape.slotOfJ8[18]! = χ ⟨18, by decide⟩ := chalK_coin χ 18 (by decide)
  have e17 : NockvmE2E.J8.TieJ8.χf χ 17 = χ ⟨17, by decide⟩ := by simp [NockvmE2E.J8.TieJ8.χf]; rfl
  have e18 : NockvmE2E.J8.TieJ8.χf χ 18 = χ ⟨18, by decide⟩ := by simp [NockvmE2E.J8.TieJ8.χf]; rfl
  refine ⟨fun t ht => ⟨?_, ?_⟩⟩
  · have hf := (ydersFind t ht).1
    have hn := order_none_y (2 * t) (by omega)
    have hj := jders_none_y (2 * t) (by omega)
    unfold NockvmE2E.Exec.DagSemV.chalE
    simp only []
    rw [hn]
    cases hd : aluDers.find? (·.slot == 41 + 2 * t) with
    | none => rw [hd] at hf; simp at hf
    | some d =>
      rw [hd] at hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨⟨⟨hre, him⟩, hpw⟩, hisre⟩ := hf
      simp only [hre, him, idx17, idx18, hpw, Option.getD, h17, h18, e17, e18, hisre]
      simp
  · have hf := (ydersFind t ht).2
    have hn : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 42 + 2 * t) = none := by
      have := order_none_y (2 * t + 1) (by omega)
      rwa [show 41 + (2 * t + 1) = 42 + 2 * t by omega] at this
    unfold NockvmE2E.Exec.DagSemV.chalE
    simp only []
    rw [hn]
    cases hd : aluDers.find? (·.slot == 42 + 2 * t) with
    | none => rw [hd] at hf; simp at hf
    | some d =>
      rw [hd] at hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨⟨⟨hre, him⟩, hpw⟩, hisre⟩ := hf
      simp only [hre, him, idx17, idx18, hpw, Option.getD, h17, h18, e17, e18, hisre]
      simp

end NockvmE2E.J9AL.TieAluJ9AL

#print axioms NockvmE2E.J9AL.TieAluJ9AL.decR_alu
#print axioms NockvmE2E.J9AL.TieAluJ9AL.chk_alu
#print axioms NockvmE2E.J9AL.TieAluJ9AL.ypowC_eq_qpow
#print axioms NockvmE2E.J9AL.TieAluJ9AL.chalsAL_eq
#print axioms NockvmE2E.J9AL.TieAluJ9AL.fL_leaf
#print axioms NockvmE2E.J9AL.TieAluJ9AL.chalE_aluDers_eq
#print axioms NockvmE2E.J9AL.TieAluJ9AL.slotOK_XL
#print axioms NockvmE2E.J9AL.TieAluJ9AL.slotY_X
