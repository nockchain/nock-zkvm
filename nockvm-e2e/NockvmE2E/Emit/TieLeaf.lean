/-
  NockvmE2E/Emit/TieLeaf.lean   (the `qpow` ↔ `Quad` lemma)

  The slot maps `fM / fA / fJ / fX` of `Chips.lean` (chip-family challenge leaf `j` ↦ document slot) against the J-8 challenge
  vectors (`CheckJ8.lean:71-110`: `chalsMJ8E`, `chalsAJ8ZE`, `chalsJJ8E`, restated here over `KC` as `memVec / atomVec / jetVec`).

  The verifier reads document slot `s` as `chalE ders meta chalV s` (Exec/DagSemV.lean:50).  We abstract that function to
  `E : ℕ → KC` and assume only what the loader data delivers (to be discharged per instance):
    `hcoin`: slot `i < 19` is the frame coin `χ i`;
    `hder` : slot `19 + m` (`m < 22`) is `Re / Im` of `γ′^(m/2)`, with `γ′ = (χ 4, χ 6)` and `qpow` the `𝕂′` power
             (`m` even ↦ `Re`).
  No claim about slots outside the read sets; the atom walk agrees with `chalsMJ8` only on the read set (finding 6b).
-/
import NockvmE2E.Emit.Chips
import NockvmE2E.Exec.DagSemV
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower

set_option autoImplicit false

namespace NockvmE2E.Emit

open Nock.Emit NockvmE2E.Exec NockvmE2E.Exec.DagSem

/-! ### `qpow` is the `Quad` power (`Quad.mk_mul`) -/
theorem qpow_mk (re im : KC) :
    ∀ n, Nock.NockVMROM.Thm54.T0Tower.Quad.mk (7 : KC) re im ^ n =
      Nock.NockVMROM.Thm54.T0Tower.Quad.mk (7 : KC) (NockvmE2E.Exec.DagSemV.qpow re im n).1 (NockvmE2E.Exec.DagSemV.qpow re im n).2
  | 0 => by
      simp only [pow_zero, NockvmE2E.Exec.DagSemV.qpow]
      exact (Nock.NockVMROM.Thm54.T0Tower.Quad.mk_one' (7 : KC)).symm
  | n + 1 => by
      rw [pow_succ, qpow_mk re im n, Nock.NockVMROM.Thm54.T0Tower.Quad.mk_mul]
      simp only [NockvmE2E.Exec.DagSemV.qpow]

/-! ### slot maps against the challenge vectors -/

noncomputable def memVec (χ : ℕ → KC) (j : ℕ) : KC :=
  if j = 35 then χ 15 else if j = 36 then χ 16 else if j = 33 then χ 11 else if j = 34 then χ 12
  else if j < 11 then χ j
  else if (j - 11) % 2 = 0 then (NockvmE2E.Exec.DagSemV.qpow (χ 4) (χ 6) ((j - 11) / 2)).1
  else (NockvmE2E.Exec.DagSemV.qpow (χ 4) (χ 6) ((j - 12) / 2)).2

noncomputable def atomVec (χ : ℕ → KC) (j : ℕ) : KC :=
  if j = 37 then χ 2 else if j = 38 then χ 3 else if j = 2 then χ 17 else if j = 3 then χ 18 else memVec χ j

noncomputable def jetVec (χ : ℕ → KC) (j : ℕ) : KC :=
  if j < 8 then (if j % 4 = 0 then χ 11 else if j % 4 = 1 then χ 12 else if j % 4 = 2 then χ 15 else χ 16) else 0

/-- the slot function of the verifier reads the frame coins and the derived `γ′` powers -/
structure SlotOK (E χ : ℕ → KC) : Prop where
  hcoin : ∀ i, i < 19 → E i = χ i
  hder : ∀ m, m < 22 → E (19 + m) =
    if m % 2 = 0 then (NockvmE2E.Exec.DagSemV.qpow (χ 4) (χ 6) (m / 2)).1 else (NockvmE2E.Exec.DagSemV.qpow (χ 4) (χ 6) (m / 2)).2

theorem fM_leaf {E χ : ℕ → KC} (h : SlotOK E χ) (j : ℕ) (hj : j ≤ 36) : E (fM j) = memVec χ j := by
  unfold fM memVec
  by_cases h35 : j = 35
  · subst h35; simpa using h.hcoin 15 (by omega)
  by_cases h36 : j = 36
  · subst h36; simpa using h.hcoin 16 (by omega)
  by_cases h33 : j = 33
  · subst h33; simpa using h.hcoin 11 (by omega)
  by_cases h34 : j = 34
  · subst h34; simpa using h.hcoin 12 (by omega)
  by_cases h11 : j < 11
  · simpa [h35, h36, h33, h34, h11] using h.hcoin j (by omega)
  · have hle : j ≤ 32 := by omega
    have hfm : (if j < 11 then j else if j ≤ 32 then j + 8 else if j = 33 then 11 else if j = 34 then 12
        else if j = 35 then 15 else if j = 36 then 16 else j) = 19 + (j - 11) := by
      rw [if_neg h11, if_pos hle]; omega
    rw [hfm, h.hder (j - 11) (by omega)]
    simp only [h35, h36, h33, h34, h11, if_false]
    by_cases hp : (j - 11) % 2 = 0
    · simp [hp]
    · have : (j - 12) / 2 = (j - 11) / 2 := by omega
      simp [hp, this]

theorem fA_leaf {E χ : ℕ → KC} (h : SlotOK E χ) (j : ℕ) (hj : j ≤ 38) : E (fA j) = atomVec χ j := by
  unfold fA atomVec
  by_cases h37 : j = 37
  · subst h37; simpa using h.hcoin 2 (by omega)
  by_cases h38 : j = 38
  · subst h38; simpa using h.hcoin 3 (by omega)
  by_cases h2 : j = 2
  · subst h2; simpa using h.hcoin 17 (by omega)
  by_cases h3 : j = 3
  · subst h3; simpa using h.hcoin 18 (by omega)
  simp only [h37, h38, h2, h3, if_false]
  exact fM_leaf h j (by omega)

theorem fJ_leaf {E χ : ℕ → KC} (h : SlotOK E χ) (j : ℕ) (hj : j < 8) : E (fJ j) = jetVec χ j := by
  unfold fJ jetVec
  rw [if_pos hj]
  have : j % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hm : j % 4 <;> simp [hm] <;> exact h.hcoin _ (by omega)

/-- compute leaves `3q + r` are the coordinates of the coin `[11,12,13,14,15,16][q]` -/
theorem fX_leaf {E χ : ℕ → KC} (h : SlotOK E χ) (j : ℕ) (hj : j < 18) :
    E (fX j) = χ ([11, 12, 13, 14, 15, 16].getD (j / 3) 0) := by
  unfold fX
  have : j / 3 < 6 := by omega
  interval_cases hq : j / 3 <;> simp <;> exact h.hcoin _ (by omega)

/-- the slot maps never leave the frame (`< 41`: 19 coins + 22 derived slots) -/
theorem fM_lt (j : ℕ) (hj : j ≤ 36) : fM j < 41 := by unfold fM; split_ifs <;> omega
theorem fA_lt (j : ℕ) (hj : j ≤ 38) : fA j < 41 := by
  unfold fA; split_ifs <;> first | omega | exact fM_lt j (by omega)

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.qpow_mk
#print axioms NockvmE2E.Emit.fM_leaf
#print axioms NockvmE2E.Emit.fA_leaf
#print axioms NockvmE2E.Emit.fJ_leaf
#print axioms NockvmE2E.Emit.fX_leaf
