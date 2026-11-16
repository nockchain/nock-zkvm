/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AtomWalkAL.lean

  **`AluSZOps`'s `Ctx.walk` at a padded reader.**

  `AluSZOps`'s `Ctx.walk : ∀ v l, Denotes r v l → atomPoly t v = limbPolyQ l` is FALSE at the J-9 A reader `valReader` past
  the table (`valReader` pads row `k ≥ nA` as `wR = 0, aL = 0, aR = 1`, so `Denotes r k [0, 1]`, while `AluSZEvent`'s walk
  returns `none` out of range and `atomPoly t k = 0`).  So the assembly runs `AluSZOps` at the reader `rStar rA nA`: `rA` below `nA`,
  a self-loop (`wR = 1`, `idR = k`) at `k ≥ nA`, where nothing is denoted.
  * `rStar_lt`: `Denotes (rStar rA nA) k l → k < nA`; `rStar_len`: the denoted list has `≤ nA + 1` limbs (the rows
    of a derivation are distinct, by `denotes_unique`).
  * **`walk_rStar`** (`Ctx.walk`): given that the round-0 table `t` reads `rA` below `nA` (`RowRead`) and
    `nA ≤ |t|`, `Denotes (rStar rA nA) v l → atomPoly t v = limbPolyQ l`.
  * `denotes_rStar_iff` (below `nA`, child serials in range) and **`extB_rStar`** (`extB` is the same at both
    readers when padded rows denote `< q`): the `rA`-side facts (`fp_read_sound`, the J-9 A denotation) transfer.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent
import Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAL

open Polynomial
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent (atomLimbs atomPoly limbPolyQ)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (denotes_unique)
open Nock.NockVMROM.Thm54.VclL

noncomputable section

/-- **The padded reader**: `rA` below `nA`; a self-loop (`wR = 1`, `idR = k`) at `k ≥ nA`. -/
def rStar (rA : ℕ → ARow) (nA : ℕ) : ℕ → ARow := fun k => if k < nA then rA k else { rA k with wR := 1, idR := k }

variable {rA : ℕ → ARow} {nA : ℕ}

theorem rStar_of_lt {k : ℕ} (hk : k < nA) : rStar rA nA k = rA k := by simp [rStar, hk]

/-- **A denoted serial of the padded reader is a table row.** -/
theorem rStar_lt {k : ℕ} {l : List ℕ} (h : Denotes (rStar rA nA) k l) : k < nA := by
  induction h with
  | @top i hw =>
    by_contra hi
    simp [rStar, hi] at hw
  | @step i l hw hd ih =>
    by_contra hi
    have : (rStar rA nA i).idR = i := by simp [rStar, hi]
    rw [this] at ih
    exact hi ih

/-- **A derivation visits distinct table rows**: the denoted list has `≤ nA + 1` limbs. -/
theorem rStar_len {k : ℕ} {l : List ℕ} (h : Denotes (rStar rA nA) k l) : l.length ≤ nA + 1 := by
  have key : ∀ {k : ℕ} {l : List ℕ}, Denotes (rStar rA nA) k l → ∃ S : Finset ℕ, S ⊆ Finset.range nA ∧
      S.card + 1 = l.length ∧ ∀ u ∈ S, ∃ l', Denotes (rStar rA nA) u l' ∧ l'.length ≤ l.length := by
    intro k l h
    induction h with
    | @top i hw =>
      refine ⟨{i}, ?_, by simp, ?_⟩
      · intro u hu
        rw [Finset.mem_singleton] at hu
        subst hu
        exact Finset.mem_range.mpr (rStar_lt (Denotes.top hw))
      · intro u hu
        rw [Finset.mem_singleton] at hu
        subst hu
        exact ⟨_, Denotes.top hw, le_refl _⟩
    | @step i l hw hd ih =>
      obtain ⟨S, hS, hc, hu⟩ := ih
      have hdi : Denotes (rStar rA nA) i ((rStar rA nA i).aL :: l) := Denotes.step hw hd
      have hni : i ∉ S := by
        intro hi
        obtain ⟨l'', h'', hl''⟩ := hu i hi
        have := denotes_unique hdi h''
        rw [← this] at hl''
        simp at hl''
      refine ⟨insert i S, ?_, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact Finset.mem_range.mpr (rStar_lt hdi)
        · exact hS hu
      · rw [Finset.card_insert_of_notMem hni, List.length_cons]; omega
      · intro u hu'
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨_, hdi, le_refl _⟩
        · obtain ⟨l'', h'', hl''⟩ := hu u hu'
          exact ⟨l'', h'', by simp only [List.length_cons]; omega⟩
  obtain ⟨S, hS, hc, -⟩ := key h
  have := Finset.card_le_card hS
  rw [Finset.card_range] at this
  omega

/-- **The round-0 table reads `rA` below `nA`** (the four walk fields of `CellRowB0`). -/
def RowRead {q : ℕ} (t : List (CellRowB0 q)) (rA : ℕ → ARow) (nA : ℕ) : Prop :=
  ∀ k < nA, ∃ c, t[k]? = some c ∧ c.wR = decide ((rA k).wR = 1) ∧ c.idR = (rA k).idR ∧
    c.aL.val = (rA k).aL ∧ c.aR.val = (rA k).aR

theorem denotes_len2 {r : ℕ → ARow} {k : ℕ} {l : List ℕ} (h : Denotes r k l) : 2 ≤ l.length := by
  induction h with
  | top _ => simp
  | step _ _ ih => simp only [List.length_cons]; omega

theorem atomLimbs_of_denotes {q : ℕ} {t : List (CellRowB0 q)} (ht : RowRead t rA nA) {k : ℕ} {l : List ℕ}
    (h : Denotes (rStar rA nA) k l) : ∀ f, l.length ≤ f + 1 → atomLimbs t f k = some l := by
  induction h with
  | @top i hw =>
    intro f hf
    have hi := rStar_lt (Denotes.top hw)
    obtain ⟨c, hc, hcw, -, hcL, hcR⟩ := ht i hi
    rw [rStar_of_lt hi] at hw ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [atomLimbs, hc, hcw, hw, hcL, hcR]
    rfl
  | @step i l hw hd ih =>
    intro f hf
    have hi := rStar_lt (Denotes.step hw hd)
    obtain ⟨c, hc, hcw, hcI, hcL, -⟩ := ht i hi
    have hw' := hw
    rw [rStar_of_lt hi] at hw'
    have h2 := denotes_len2 hd
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have e := ih f' (by simp at hf; omega)
    rw [rStar_of_lt hi] at e ⊢
    simp only [atomLimbs, hc, hcw, hw', hcI, hcL, e]
    rfl

/-- **`AluSZOps`'s `Ctx.walk` at the padded reader.** -/
theorem walk_rStar {q : ℕ} {t : List (CellRowB0 q)} (ht : RowRead t rA nA) (hn : nA ≤ t.length) :
    ∀ v l, Denotes (rStar rA nA) v l → atomPoly t v = limbPolyQ l := by
  intro v l h
  have e := atomLimbs_of_denotes ht h t.length (by have := rStar_len h; omega)
  unfold atomPoly
  rw [e]

/-- **Below `nA`, with in-range child serials, the two readers denote the same lists.** -/
theorem denotes_rStar_of {k : ℕ} {l : List ℕ} (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (h : Denotes rA k l) (hk : k < nA) : Denotes (rStar rA nA) k l := by
  induction h with
  | @top i hw =>
    have hs := Denotes.top (r := rStar rA nA) (i := i) (by rw [rStar_of_lt hk]; exact hw)
    rwa [rStar_of_lt hk] at hs
  | @step i l hw hd ih =>
    have e := ih (hin i hk hw)
    have hs : Denotes (rStar rA nA) i ((rStar rA nA i).aL :: l) :=
      Denotes.step (by rw [rStar_of_lt hk]; exact hw) (by rw [rStar_of_lt hk]; exact e)
    rwa [rStar_of_lt hk] at hs

theorem denotes_of_rStar {k : ℕ} {l : List ℕ} (h : Denotes (rStar rA nA) k l) : Denotes rA k l := by
  induction h with
  | @top i hw =>
    have hi := rStar_lt (Denotes.top hw)
    rw [rStar_of_lt hi] at hw ⊢
    exact Denotes.top hw
  | @step i l hw hd ih =>
    have hi := rStar_lt (Denotes.step hw hd)
    rw [rStar_of_lt hi] at hw ih ⊢
    exact Denotes.step hw ih

/-- **`extB` is the same at both readers** when child serials are in range and every padded row's denotation is
below `q` (`valReader`'s padding denotes `[0, 1]`, value `B`). -/
theorem extB_rStar {q : ℕ} (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (hpad : ∀ k, nA ≤ k → ∀ l, Denotes rA k l → Nock.Atoms.val l < q) (k : ℕ) :
    extB q (rStar rA nA) k = extB q rA k := by
  by_cases hk : k < nA
  · unfold extB
    have hiff : (∃ l, Denotes (rStar rA nA) k l ∧ q ≤ Nock.Atoms.val l) ↔ (∃ l, Denotes rA k l ∧ q ≤ Nock.Atoms.val l) :=
      ⟨fun ⟨l, h1, h2⟩ => ⟨l, denotes_of_rStar h1, h2⟩, fun ⟨l, h1, h2⟩ => ⟨l, denotes_rStar_of hin h1 hk, h2⟩⟩
    by_cases h : ∃ l, Denotes rA k l ∧ q ≤ Nock.Atoms.val l
    · have h' := hiff.mpr h
      rw [dif_pos h', dif_pos h]
      congr 2
      exact congrArg Nock.Atoms.val (denotes_unique (denotes_of_rStar (Classical.choose_spec h').1)
        (Classical.choose_spec h).1)
    · rw [dif_neg (fun h' => h (hiff.mp h')), dif_neg h]
  · unfold extB
    rw [dif_neg (fun ⟨l, h1, _⟩ => hk (rStar_lt h1)), dif_neg (fun ⟨l, h1, h2⟩ => by
      have := hpad k (by omega) l h1; omega)]

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAL
#print axioms walk_rStar
#print axioms rStar_len
#print axioms extB_rStar
#print axioms denotes_rStar_of
end Axioms
