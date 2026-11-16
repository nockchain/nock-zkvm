/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/NounAx.lean

* `valId`: the value of the atom-table row `id` read through `extA` (not `D (2,·)` = `extB`) when
    `id < nA`, or the split row `id - nA`'s value `sv (id - nA)` (`splitVal`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8
import Nock.Reference
import Nock.Atoms.Limbs
import Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8

set_option autoImplicit false

open Nock Noun

namespace Nock.J9A.NounAx

open Nock
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA)

/-- the natural number of an atom (`none` on a cell). -/
def atomOf : Noun → Option ℕ
  | .atom n => some n
  | .cell _ _ => none

/-- **`valId`**: ids `< nA` are atom-table rows, read through `extA` (every denoted row, whatever its
value); ids `≥ nA` are split rows, `sv (id - nA)` (`splitVal`). -/
noncomputable def valId (nA : ℕ) (rA : ℕ → ARow) (sv : ℕ → Option ℕ) (id : ℕ) : Option ℕ :=
  if id < nA then (extA rA id).bind atomOf else sv (id - nA)

end Nock.J9A.NounAx

/-! ## Noun composition and segment lemmas -/

namespace Nock.J9A.NounComp

/-- one-bit step for `slot`. -/
theorem slot_double (k b : ℕ) (x : Noun) (hk : 1 ≤ k) (hb : b < 2) :
    slot (2 * k + b) x = (slot k x).bind (fun n => match n with
      | .cell l r => some (if b = 0 then l else r) | _ => none) := by
  obtain ⟨a, ha⟩ : ∃ a, 2 * k + b = a + 2 := ⟨2 * k + b - 2, by omega⟩
  have h1 : (a + 2) / 2 = k := by omega
  have h2 : (a + 2) % 2 = b := by omega
  rw [ha, slot, h1]
  rcases h : slot k x with _ | n
  · simp
  · cases n with
    | atom _ => simp
    | cell l r => simp [h2]

theorem slot_comp (a m r : ℕ) (x : Noun) (ha : 1 ≤ a) (hr : r < 2 ^ m) :
    slot (a * 2 ^ m + r) x = (slot a x).bind (slot (2 ^ m + r)) := by
  induction m generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    subst this
    simp [slot]
  | succ m ih =>
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hr' : r / 2 < 2 ^ m := by omega
    have e1 : a * 2 ^ (m + 1) + r = 2 * (a * 2 ^ m + r / 2) + r % 2 := by
      rw [hpow, Nat.mul_left_comm]; omega
    have e2 : 2 ^ (m + 1) + r = 2 * (2 ^ m + r / 2) + r % 2 := by
      rw [hpow]; omega
    have hb : r % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hk1 : 1 ≤ a * 2 ^ m + r / 2 := by nlinarith
    have hk2 : 1 ≤ 2 ^ m + r / 2 := by omega
    rw [e1, e2, slot_double _ _ _ hk1 hb, ih _ hr']
    rcases hs : slot a x with _ | s
    · simp
    · simp only [Option.bind_some]
      rw [slot_double _ _ _ hk2 hb]

/-- one-bit step for `edit`. -/
theorem edit_two_step (k b : ℕ) (new old : Noun) (hk : 1 ≤ k) (hb : b < 2) :
    edit (2 * k + b) new old =
      (slot (2 * k + (1 - b)) old).bind (fun sib =>
        edit k (if b = 0 then Noun.cell new sib else Noun.cell sib new) old) := by
  obtain ⟨a, ha⟩ : ∃ a, 2 * k + b = a + 2 := ⟨2 * k + b - 2, by omega⟩
  have h1 : (a + 2) / 2 = k := by omega
  rw [ha, edit]
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · have h2 : (a + 2) % 2 = 0 := by omega
    have h3 : a + 2 + 1 = 2 * k + (1 - 0) := by omega
    simp [h2, h1, h3]
    rcases slot (2 * k + 1) old with _ | s <;> rfl
  · have h2 : (a + 2) % 2 = 1 := by omega
    have h3 : a + 2 - 1 = 2 * k + (1 - 1) := by omega
    simp [h2, h1, h3]
    rcases slot (2 * k) old with _ | s <;> rfl

/-- if the slot is missing, so is the edit (no extra hypothesis needed). -/
theorem edit_none_of_slot_none (a : ℕ) (new old : Noun) (ha : 1 ≤ a)
    (h : slot a old = none) : edit a new old = none := by
  have ha2 : a ≠ 1 := by
    rintro rfl; simp [slot] at h
  obtain ⟨k, hk, b, hb, rfl⟩ : ∃ k, 1 ≤ k ∧ ∃ b, b < 2 ∧ a = 2 * k + b :=
    ⟨a / 2, by omega, a % 2, by omega, by omega⟩
  rw [edit_two_step k b new old hk hb]
  rw [slot_double k b old hk hb] at h
  have h' : ∀ b' : ℕ, b' < 2 → slot (2 * k + b') old = none := by
    intro b' hb'
    rw [slot_double k b' old hk hb']
    rcases hs : slot k old with _ | n
    · simp
    · cases n with
      | atom _ => simp
      | cell l r => rw [hs] at h; simp at h
  rw [h' (1 - b) (by omega)]; rfl

theorem edit_comp (a m r : ℕ) (new old : Noun) (ha : 1 ≤ a) (hr : r < 2 ^ m) :
    edit (a * 2 ^ m + r) new old =
      (slot a old).bind (fun s => (edit (2 ^ m + r) new s).bind (fun s' => edit a s' old)) := by
  induction m generalizing r new with
  | zero =>
    have : r = 0 := by simpa using hr
    subst this
    rcases hs : slot a old with _ | s
    · simpa [hs] using edit_none_of_slot_none a new old ha hs
    · simp [edit]
  | succ m ih =>
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hr' : r / 2 < 2 ^ m := by omega
    have e1 : a * 2 ^ (m + 1) + r = 2 * (a * 2 ^ m + r / 2) + r % 2 := by
      rw [hpow, Nat.mul_left_comm]; omega
    have e2 : 2 ^ (m + 1) + r = 2 * (2 ^ m + r / 2) + r % 2 := by
      rw [hpow]; omega
    have hb : r % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hk1 : 1 ≤ a * 2 ^ m + r / 2 := by nlinarith
    have hk2 : 1 ≤ 2 ^ m + r / 2 := by omega
    have hsib : 2 * (a * 2 ^ m + r / 2) + (1 - r % 2)
        = a * 2 ^ (m + 1) + (2 * (r / 2) + (1 - r % 2)) := by rw [hpow]; ring
    have hsib2 : 2 ^ (m + 1) + (2 * (r / 2) + (1 - r % 2))
        = 2 * (2 ^ m + r / 2) + (1 - r % 2) := by rw [hpow]; ring
    have hlt : 2 * (r / 2) + (1 - r % 2) < 2 ^ (m + 1) := by rw [hpow]; omega
    rw [e1, edit_two_step _ _ _ _ hk1 hb, hsib, slot_comp a (m + 1) _ old ha hlt]
    simp only [e2, edit_two_step _ _ _ _ hk2 hb, hsib2, ih _ _ hr']
    rcases hs : slot a old with _ | s
    · simp
    · simp only [Option.bind_some, Option.bind_assoc]

end Nock.J9A.NounComp

namespace Nock.J9A.NounSeg

open Nock.J9A.NounComp

/-- value of an LSB-first limb list in base `2^m`. -/
def limbVal (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | l :: ls => l + 2 ^ m * limbVal m ls

/-- slot by `top`, then each lower limb (MSB first) with leading-1 convention. -/
def slotSegs (m : ℕ) (top : ℕ) (lows : List ℕ) (x : Noun) : Option Noun :=
  lows.foldl (fun acc l => acc.bind (slot (2 ^ m + l))) (slot top x)

/-- edit, with the lower limbs given LSB-first (head = deepest segment). -/
def editSegsR (m : ℕ) (top : ℕ) : List ℕ → Noun → Noun → Option Noun
  | [], new, old => edit top new old
  | l :: lr, new, old =>
    (slotSegs m top lr.reverse old).bind (fun s =>
      (edit (2 ^ m + l) new s).bind (fun s' => editSegsR m top lr s' old))

/-- edit with lower limbs MSB-first. -/
def editSegs (m : ℕ) (top : ℕ) (lows : List ℕ) (new old : Noun) : Option Noun :=
  editSegsR m top lows.reverse new old

theorem slotSegs_snoc (m top : ℕ) (lows : List ℕ) (l : ℕ) (x : Noun) :
    slotSegs m top (lows ++ [l]) x = (slotSegs m top lows x).bind (slot (2 ^ m + l)) := by
  simp [slotSegs, List.foldl_append]

theorem limbVal_snoc_pos (m : ℕ) (lo : List ℕ) (top : ℕ) (ht : 1 ≤ top) :
    1 ≤ limbVal m (lo ++ [top]) := by
  induction lo with
  | nil => simp [limbVal]; omega
  | cons l lo ih =>
    simp only [List.cons_append, limbVal]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    nlinarith

theorem limbVal_cons_comm (m l : ℕ) (ls : List ℕ) :
    limbVal m (l :: ls) = limbVal m ls * 2 ^ m + l := by
  simp only [limbVal]; ring

theorem slot_limbs (m : ℕ) (lo : List ℕ) (hlo : ∀ l ∈ lo, l < 2 ^ m) (top : ℕ) (ht : 1 ≤ top)
    (x : Noun) :
    slot (limbVal m (lo ++ [top])) x = slotSegs m top lo.reverse x := by
  induction lo with
  | nil => simp [limbVal, slotSegs]
  | cons l lo ih =>
    have hl : l < 2 ^ m := hlo l (by simp)
    have ih' := ih (fun l' h => hlo l' (by simp [h]))
    rw [List.cons_append, limbVal_cons_comm,
      slot_comp _ _ _ _ (limbVal_snoc_pos m lo top ht) hl, ih', List.reverse_cons,
      slotSegs_snoc]

theorem edit_limbs (m : ℕ) (lo : List ℕ) (hlo : ∀ l ∈ lo, l < 2 ^ m) (top : ℕ) (ht : 1 ≤ top)
    (new old : Noun) :
    edit (limbVal m (lo ++ [top])) new old = editSegs m top lo.reverse new old := by
  induction lo generalizing new with
  | nil => simp [limbVal, editSegs, editSegsR]
  | cons l lo ih =>
    have hl : l < 2 ^ m := hlo l (by simp)
    have hlo' : ∀ l' ∈ lo, l' < 2 ^ m := fun l' h => hlo l' (by simp [h])
    rw [List.cons_append, limbVal_cons_comm,
      edit_comp _ _ _ _ _ (limbVal_snoc_pos m lo top ht) hl, slot_limbs m lo hlo' top ht]
    simp only [editSegs, List.reverse_reverse, editSegsR]
    congr 1
    funext s
    congr 1
    funext s'
    rw [ih hlo']
    simp [editSegs]

theorem slot_split2 (hi lo m : ℕ) (x : Noun) (hh : 1 ≤ hi) (hl : lo < 2 ^ m) :
    slot (hi * 2 ^ m + lo) x = (slot hi x).bind (slot (2 ^ m + lo)) :=
  slot_comp hi m lo x hh hl

theorem edit_split2 (hi lo m : ℕ) (new old : Noun) (hh : 1 ≤ hi) (hl : lo < 2 ^ m) :
    edit (hi * 2 ^ m + lo) new old =
      (slot hi old).bind (fun s => (edit (2 ^ m + lo) new s).bind (fun s' => edit hi s' old)) :=
  edit_comp hi m lo new old hh hl

/-- bridge to `Nock.Atoms.val` (base `B = 2^32`). -/
theorem limbVal_32 (l : List ℕ) : limbVal 32 l = Nock.Atoms.val l := by
  induction l with
  | nil => simp [limbVal]
  | cons a l ih => simp [limbVal, ih, Nock.Atoms.B]

end Nock.J9A.NounSeg

/-! ## `slot_combL_atom`: where the atoms of the canonical comb sit (S3) -/

namespace Nock.J9A.NounAx

open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combL)
open Nock.J9A.NounComp

theorem slot_cell_tail (h t : Noun) (e r : ℕ) (hr : r < 2 ^ e) :
    slot (3 * 2 ^ e + r) (Noun.cell h t) = slot (2 ^ e + r) t := by
  rw [slot_comp 3 e r _ (by norm_num) hr]
  have : slot 3 (Noun.cell h t) = some t := by simp [slot]
  simp [this]

theorem slot_cell_head (h t : Noun) (e r : ℕ) (hr : r < 2 ^ e) :
    slot (2 * 2 ^ e + r) (Noun.cell h t) = slot (2 ^ e + r) h := by
  rw [slot_comp 2 e r _ (by norm_num) hr]
  have : slot 2 (Noun.cell h t) = some h := by simp [slot]
  simp [this]

theorem slot_atom_none (n : ℕ) : ∀ a, 2 ≤ a → slot a (Noun.atom n) = none := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    rw [slot]
    rcases Nat.lt_or_ge ((b + 2) / 2) 2 with h | h
    · have h1 : (b + 2) / 2 = 1 := by omega
      rw [h1]; simp [slot]
    · rw [ih _ (by omega) h]

theorem slot_atom_ne (a x n : ℕ) (ha : 2 ≤ a) : slot a (Noun.atom n) ≠ some (Noun.atom x) := by
  rw [slot_atom_none n a ha]; simp

theorem getLast!_cons_cons (a b : ℕ) (l : List ℕ) : (a :: b :: l).getLast! = (b :: l).getLast! := by
  simp [List.getLast!_eq_getLast?_getD, List.getLast?_cons_cons]

/-- Every atom of the right comb sits at an even spine-left axis or at the odd spine end. -/
theorem slot_combL_atom {L : List ℕ} {a x : ℕ} (h : Noun.slot a (combL L) = some (.atom x)) :
    (∃ j, j + 2 ≤ L.length ∧ a = 2 ^ (j + 2) - 2 ∧ x = L[j]!) ∨
    (1 ≤ L.length ∧ a = 2 ^ L.length - 1 ∧ x = L.getLast!) ∨ (L = [] ∧ a = 1 ∧ x = 0) := by
  induction L generalizing a x with
  | nil =>
    right; right
    refine ⟨rfl, ?_⟩
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · simp [combL, slot] at h
      · simp [combL, slot] at h; exact ⟨rfl, h.symm⟩
    · exact absurd h (slot_atom_ne a x 0 ha)
  | cons c0 L ih =>
    rcases L with _ | ⟨c1, l⟩
    · right; left
      simp only [combL] at h
      rcases Nat.lt_or_ge a 2 with ha | ha
      · interval_cases a
        · simp [slot] at h
        · simp [slot] at h; simp [h]
      · exact absurd h (slot_atom_ne a x c0 ha)
    · have ih' := @ih
      simp only [combL] at h
      rcases Nat.lt_or_ge a 2 with ha | ha
      · interval_cases a
        · simp [slot] at h
        · simp [slot] at h
      · -- a ≥ 2: split off the leading two bits
        have hk1 : 1 ≤ Nat.log 2 a := Nat.log_pos (by norm_num) ha
        obtain ⟨e, he⟩ : ∃ e, Nat.log 2 a = e + 1 := ⟨Nat.log 2 a - 1, by omega⟩
        have hlo : 2 ^ (e + 1) ≤ a := by
          have := Nat.pow_log_le_self 2 (show a ≠ 0 by omega); rwa [he] at this
        have hhi : a < 2 ^ (e + 2) := by
          have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a; rw [he] at this; simpa using this
        have hp : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
        have hp2 : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
        have he1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
        by_cases hs : a < 3 * 2 ^ e
        · -- prefix 10: into the head atom, which is only the axis 2
          obtain ⟨s, hs'⟩ : ∃ s, a = 2 * 2 ^ e + s := ⟨a - 2 * 2 ^ e, by omega⟩
          rw [hs', slot_cell_head _ _ e s (by omega)] at h
          have h2 : 2 ^ e + s < 2 := by
            by_contra hc
            exact slot_atom_ne _ _ _ (by omega) h
          have he0 : e = 0 := by
            by_contra hne
            have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          subst he0
          have hs0 : s = 0 := by simp at h2; omega
          subst hs0
          have hx : x = c0 := by simpa [slot] using h.symm
          left
          exact ⟨0, by simp, by simpa using hs', by simp [hx]⟩
        · -- prefix 11: into the tail
          obtain ⟨r, hr'⟩ : ∃ r, a = 3 * 2 ^ e + r := ⟨a - 3 * 2 ^ e, by omega⟩
          have hr : r < 2 ^ e := by omega
          rw [hr', slot_cell_tail _ _ e r hr] at h
          have hlen : (c0 :: c1 :: l).length = l.length + 2 := by simp
          rcases ih h with ⟨j, hj, hax, hx⟩ | ⟨hl1, hax, hx⟩ | ⟨hnil, -, -⟩
          · -- the tail's even-axis atom: shift by one
            left
            have hlen' : (c1 :: l).length = l.length + 1 := by simp
            have h1 : 2 ^ e ≤ 2 ^ (j + 2) - 2 := by omega
            have hq : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
            have hq1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
            have hej : e = j + 1 := by
              have h3 : 2 ^ e < 2 ^ (j + 2) := by omega
              have h4 : 2 ^ (j + 1) ≤ 2 ^ e * 2 - 1 := by
                have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
                omega
              have e1 : e < j + 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
              have e2 : j + 1 ≤ e := by
                by_contra hc
                have : 2 ^ e ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
                have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
                omega
              omega
            subst hej
            refine ⟨j + 1, by omega, ?_, by simpa using hx⟩
            have : 2 ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
            have h5 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
            omega
          · -- the tail's odd end
            right; left
            have hlen' : (c1 :: l).length = l.length + 1 := by simp
            rw [hlen'] at hax
            refine ⟨by omega, ?_, by rw [getLast!_cons_cons]; exact hx⟩
            rw [hlen]
            have hq : 2 ^ (l.length + 1) ≤ 2 ^ (e + 1) := by
              have : 2 ^ (l.length + 1) - 1 < 2 ^ (e + 1) := by omega
              have h0 : 1 ≤ 2 ^ (l.length + 1) := Nat.one_le_two_pow
              omega
            have hq2 : 2 ^ e < 2 ^ (l.length + 1) := by
              have h0 : 1 ≤ 2 ^ (l.length + 1) := Nat.one_le_two_pow
              omega
            have e1 : e < l.length + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hq2
            have e2 : l.length + 1 ≤ e + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hq
            have hel : e = l.length := by omega
            rw [hel] at hr' hax
            have : 2 ^ (l.length + 2) = 2 * 2 ^ (l.length + 1) := by ring
            have h6 : 2 ^ (l.length + 1) = 2 * 2 ^ l.length := by ring
            omega
          · simp at hnil

end Nock.J9A.NounAx

/-! ## `valId` arithmetic, `top`, `segAx` -/

namespace Nock.J9A.NounAx

open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA_of_denotes)
open Nock.Atoms (val)

theorem valId_of_lt {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ} {id : ℕ} (h : id < nA) :
    valId nA rA sv id = (extA rA id).bind atomOf := by
  simp [valId, h]

theorem valId_of_ge {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ} {id : ℕ} (h : nA ≤ id) :
    valId nA rA sv id = sv (id - nA) := by
  simp [valId, not_lt.2 h]

/-- an atom-table row that denotes the limb list `l` has value `val l`. -/
theorem valId_of_denotes {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ} {id : ℕ} {l : List ℕ}
    (h : id < nA) (hd : Denotes rA id l) : valId nA rA sv id = some (val l) := by
  rw [valId_of_lt h, extA_of_denotes hd]; rfl

/-- a split id `nA + s` reads the split table at `s`. -/
theorem valId_split {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ} (s : ℕ) :
    valId nA rA sv (nA + s) = sv s := by
  rw [valId_of_ge (Nat.le_add_right _ _)]; simp

/-- a defined `valId` below `nA` is a denoted atom-table row. -/
theorem valId_lt_some {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ} {id n : ℕ} (h : id < nA)
    (hv : valId nA rA sv id = some n) : extA rA id = some (.atom n) := by
  rw [valId_of_lt h] at hv
  rcases he : extA rA id with _ | w
  · rw [he] at hv; simp at hv
  · rw [he] at hv
    cases w with
    | atom k => simpa [atomOf] using hv
    | cell _ _ => simp [atomOf] at hv

/-- `top n`: the index of the top limb (one less than the limb count). -/
def top (n : ℕ) : ℕ := Nat.log (2 ^ 32) n

theorem top_eq_length (n : ℕ) (hn : n ≠ 0) : (Nock.Atoms.limbs n).length = top n + 1 := by
  have hb : 1 < 2 ^ 32 := by norm_num
  have := Nat.length_digits (2 ^ 32) n hb hn
  simpa [Nock.Atoms.limbs, Nock.Atoms.B, top] using this

/-- `segAx n m`: the axis of the low `m + 1` limbs with a leading `1` (the top segment is `n` itself). -/
def segAx (n m : ℕ) : ℕ := if m = top n then n else 2 ^ (32 * (m + 1)) + n % 2 ^ (32 * (m + 1))

/-- the segment read at level `m`: the limb `m` (head: alone; else with a leading `B`). -/
def segRd (n m : ℕ) : ℕ := n / 2 ^ (32 * m) % 2 ^ 32 + (if m = top n then 0 else 2 ^ 32)

/-- the axis one level down: the low `m` limbs with a leading `1`. -/
def nxtAx (n m : ℕ) : ℕ := 2 ^ (32 * m) + n % 2 ^ (32 * m)

/-- `D (3, 64·id + m)`'s value: `none` above the top limb. -/
def segD (n m : ℕ) : Option ℕ := if m ≤ top n then some (segAx n m) else none

theorem segAx_top (n : ℕ) : segAx n (top n) = n := by simp [segAx]

theorem pow_top_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (32 * top n) ≤ n := by
  have := Nat.pow_log_le_self (2 ^ 32) hn
  rwa [← pow_mul] at this

theorem lt_pow_top (n : ℕ) : n < 2 ^ (32 * (top n + 1)) := by
  have := Nat.lt_pow_succ_log_self (b := 2 ^ 32) (by norm_num) n
  rwa [← pow_mul] at this

theorem segAx_decomp (n m : ℕ) (hm : m ≤ top n) :
    segAx n m = segRd n m * 2 ^ (32 * m) + n % 2 ^ (32 * m) := by
  have ha : 0 < 2 ^ (32 * m) := Nat.two_pow_pos _
  have hmul : 2 ^ (32 * (m + 1)) = 2 ^ (32 * m) * 2 ^ 32 := by rw [Nat.mul_succ, pow_add]
  by_cases h : m = top n
  · subst h
    have hlt := lt_pow_top n
    rw [hmul] at hlt
    have hd : n / 2 ^ (32 * top n) < 2 ^ 32 := Nat.div_lt_of_lt_mul hlt
    simp only [segAx, segRd, ite_true, add_zero, Nat.mod_eq_of_lt hd]
    have := Nat.div_add_mod n (2 ^ (32 * top n))
    linarith
  · simp only [segAx, segRd, h, ite_false]
    rw [hmul, Nat.mod_mul]
    ring

theorem segAx_next (n m : ℕ) (hm : m ≤ top n) (h1 : 1 ≤ m) : segAx n (m - 1) = nxtAx n m := by
  have h2 : m - 1 ≠ top n := by omega
  have h3 : m - 1 + 1 = m := by omega
  simp [segAx, nxtAx, h2, h3]

theorem nxtAx_zero (n : ℕ) : nxtAx n 0 = 1 := by simp [nxtAx, Nat.mod_one]

theorem segRd_pos {n : ℕ} (hn : n ≠ 0) (m : ℕ) (hm : m ≤ top n) : 1 ≤ segRd n m := by
  by_cases h : m = top n
  · subst h
    have hlt := lt_pow_top n
    have hmul : 2 ^ (32 * (top n + 1)) = 2 ^ (32 * top n) * 2 ^ 32 := by rw [Nat.mul_succ, pow_add]
    rw [hmul] at hlt
    have hd : n / 2 ^ (32 * top n) < 2 ^ 32 := Nat.div_lt_of_lt_mul hlt
    have hp : 0 < n / 2 ^ (32 * top n) := Nat.div_pos (pow_top_le hn) (Nat.two_pow_pos _)
    simp only [segRd, ite_true, add_zero, Nat.mod_eq_of_lt hd]
    omega
  · simp only [segRd, h, ite_false]
    omega

theorem segRd_lt (n m : ℕ) : segRd n m < 2 ^ 33 := by
  have h1 : n / 2 ^ (32 * m) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have h2 : (2 : ℕ) ^ 33 = 2 ^ 32 + 2 ^ 32 := by norm_num
  unfold segRd
  split <;> omega

theorem nxtAx_lt_pow (n m : ℕ) : n % 2 ^ (32 * m) < 2 ^ (32 * m) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

end Nock.J9A.NounAx

/-! ## `wrap62`: the distance-62 axis is not a comb atom axis at Goldilocks -/

namespace Nock.J9A.NounAx

open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combL)

/-- the odd/even obstruction: `2^32 - 3` is neither `2^(j+2) - 2` nor `2^len - 1`. -/
theorem not_comb_axis_2_32_sub_3 {L : List ℕ} {x : ℕ}
    (h : Noun.slot (2 ^ 32 - 3) (combL L) = some (.atom x)) : False := by
  have hq : (2 : ℕ) ^ 32 = 4 * 2 ^ 30 := by norm_num
  rcases slot_combL_atom h with ⟨j, -, hj, -⟩ | ⟨hl, hj, -⟩ | ⟨-, hj, -⟩
  · have : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ 30 := Nat.one_le_two_pow
    omega
  · rcases Nat.lt_or_ge L.length 2 with h2 | h2
    · have : L.length = 1 := by omega
      rw [this] at hj; norm_num at hj
    · obtain ⟨u, hu⟩ : ∃ u, L.length = u + 2 := ⟨L.length - 2, by omega⟩
      rw [hu] at hj
      have : 2 ^ (u + 2) = 4 * 2 ^ u := by ring
      have h1 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      omega
  · norm_num at hj

/-- **`wrap62`**: a field element `a < p` with `a = 2^64 - 2` in `ZMod p` (the wrapped distance-62 axis) is no
comb atom axis. -/
theorem wrap62 {a : ℕ} (ha : a < Nock.Atoms.p)
    (hc : ((a : ℕ) : ZMod Nock.Atoms.p) = 2 ^ 64 - 2) (L : List ℕ) (x : ℕ) :
    Noun.slot a (combL L) ≠ some (.atom x) := by
  intro h
  have hp : Nock.Atoms.p = 2 ^ 64 - 2 ^ 32 + 1 := by norm_num [Nock.Atoms.p, Nock.Field.p]
  have e : (2 : ZMod Nock.Atoms.p) ^ 64 - 2 = ((2 ^ 64 - 2 : ℕ) : ZMod Nock.Atoms.p) := by
    rw [Nat.cast_sub (by norm_num)]; push_cast; ring
  rw [e, ZMod.natCast_eq_natCast_iff'] at hc
  have h1 : a % Nock.Atoms.p = a := Nat.mod_eq_of_lt ha
  have h2 : (2 ^ 64 - 2) % Nock.Atoms.p = 2 ^ 32 - 3 := by
    rw [hp]; norm_num
  rw [h1, h2] at hc
  subst hc
  exact not_comb_axis_2_32_sub_3 h

end Nock.J9A.NounAx

#print axioms Nock.J9A.NounComp.slot_comp
#print axioms Nock.J9A.NounComp.edit_comp
#print axioms Nock.J9A.NounSeg.slot_limbs
#print axioms Nock.J9A.NounSeg.edit_limbs
#print axioms Nock.J9A.NounSeg.slot_split2
#print axioms Nock.J9A.NounSeg.edit_split2
#print axioms Nock.J9A.NounSeg.limbVal_32

#print axioms Nock.J9A.NounAx.slot_combL_atom
#print axioms Nock.J9A.NounAx.valId
#print axioms Nock.J9A.NounAx.valId_of_denotes
#print axioms Nock.J9A.NounAx.valId_lt_some
#print axioms Nock.J9A.NounAx.segAx_decomp
#print axioms Nock.J9A.NounAx.segAx_next
#print axioms Nock.J9A.NounAx.segRd_pos
#print axioms Nock.J9A.NounAx.segRd_lt
#print axioms Nock.J9A.NounAx.wrap62
