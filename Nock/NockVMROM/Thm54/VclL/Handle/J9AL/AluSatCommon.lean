/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatCommon.lean

  **The common part**: the op-independent honest gate satisfaction
  of the J-9 AL ALU chip `AluSZChipJ9` on the honest block `blockB`/`blockQ` of `AluHonestRows`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatCommon

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 0. Facts about the slots of a call -/

theorem packQ1_ne_nil : ∀ (l : List ℕ), l ≠ [] → packQ1 l ≠ []
  | [], h => absurd rfl h
  | q :: qs, _ => by rw [packQ1]; simp

theorem limbs_ne_nil {v : ℕ} (h : v ≠ 0) : Nock.Atoms.limbs v ≠ [] := by
  unfold Nock.Atoms.limbs; exact Nat.digits_ne_nil_iff_ne_zero.mpr h

theorem limbs_lt {v w : ℕ} (h : w ∈ Nock.Atoms.limbs v) : w < Bn :=
  (Nock.Atoms.limbs_canonical v).1 w h

theorem wordsOf_ne_nil (v : ℕ) : wordsOf v ≠ [] := by
  unfold wordsOf; split_ifs with h
  · simp
  · exact limbs_ne_nil h

theorem wordsOf_lt (v : ℕ) : ∀ w ∈ wordsOf v, w < Bn := by
  unfold wordsOf; split_ifs with h
  · intro w hw; simp at hw; subst hw; norm_num [Bn]
  · intro w hw; exact limbs_lt hw

/-- The handle hypothesis of a call: small values have kind `0` and serial the value, big values kind `2`. -/
def HK (p v k t : ℕ) : Prop := (v < p → k = 0 ∧ t = v) ∧ (p ≤ v → k = 2)

theorem handleSlot_cases (p : ℕ) (o : PrimOp) (lb r v k t : ℕ) :
    (v < p ∧ ∃ c1 c2, handleSlot p o lb r v k t = ⟨some r, 1, splitOf v, splitOf v, 0, v, c1, c2⟩) ∨
    (p ≤ v ∧ isFactor o r = true ∧ ∃ c1 c2,
      handleSlot p o lb r v k t = ⟨some r, 2, Nock.Atoms.limbs v, Nock.Atoms.limbs v, k, t, c1, c2⟩) ∨
    (p ≤ v ∧ isFactor o r = false ∧ ∃ c1 c2,
      handleSlot p o lb r v k t = ⟨some r, 0, [0], Nock.Atoms.limbs v, k, t, c1, c2⟩) := by
  by_cases h1 : v < p
  · left
    exact ⟨h1, (coefOf o lb (some r)).1, (coefOf o lb (some r)).2, by simp [handleSlot, h1]⟩
  · right
    have h1' : p ≤ v := not_lt.mp h1
    by_cases h2 : isFactor o r = true
    · left
      exact ⟨h1', h2, (coefOf o lb (some r)).1, (coefOf o lb (some r)).2, by simp [handleSlot, h1, h2]⟩
    · right
      have h2' : isFactor o r = false := by simpa using h2
      exact ⟨h1', h2', (coefOf o lb (some r)).1, (coefOf o lb (some r)).2, by simp [handleSlot, h1, h2']⟩

theorem splitOf_lt {p v : ℕ} (hpG : p = Nock.Atoms.p) (hv : v < p) : ∀ w ∈ splitOf v, w < Bn := by
  intro w hw
  simp only [splitOf, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl
  · exact Nat.mod_lt _ (by norm_num [Bn])
  · have : p = 1 + Nock.Atoms.B * (Nock.Atoms.B - 1) := hpG ▸ Nock.Atoms.p_eq_limbs
    show v / Bn < Bn
    rw [Nat.div_lt_iff_lt_mul (by norm_num [Bn])]
    have hB : Nock.Atoms.B = Bn := rfl
    rw [hB] at this
    have : Bn * (Bn - 1) < Bn * Bn := Nat.mul_lt_mul_of_pos_left (by norm_num [Bn]) (by norm_num [Bn])
    omega

/-- **The slot facts** the gate groups need (op-independent, plus the handle bindings and the mode/role
compatibilities of the chip's op). -/
structure SG (p : ℕ) (cl : CallL) (s : SlotL) : Prop where
  ne : 0 < s.words.length
  wf : (∃ r, r < 7 ∧ s.role = some r ∧ s.mode < 4) ∨ (s.role = none ∧ (s.mode = 4 ∨ s.mode = 5))
  m0 : s.mode = 0 → s.words = [0]
  m1 : s.mode = 1 → ∃ v, v < p ∧ s.words = splitOf v ∧ s.sv = v ∧ s.sk = 0
  wb : s.mode < 4 → ∀ w ∈ s.words, w < Bn
  vw : (s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3) → s.vw = s.words
  sk2 : (s.mode = 0 ∨ s.mode = 2) → s.sk = 2
  bA : s.role = some 0 → s.sk = cl.kA ∧ s.sv = cl.vA
  bB : s.role = some 1 → s.sk = cl.kB ∧ s.sv = cl.vB
  bE : (s.role = some 2 ∨ (s.role = some 4 ∧ cl.op = .div) ∨ (s.role = some 5 ∧ cl.op = .mod)) →
    s.sk = cl.kE ∧ s.sv = cl.vE
  c1 : (s.role = some 0 ∨ s.role = some 1 ∨ s.role = some 2) → s.mode ≠ 3
  c2 : (s.role = some 3 ∨ s.role = some 6) → s.mode = 3
  c3 : s.role = some 4 → cl.op = .div → s.mode ≠ 3
  c4 : s.role = some 4 → cl.op = .mod → s.mode = 3
  c5 : s.role = some 5 → cl.op = .mod → s.mode ≠ 3
  c6 : s.role = some 5 → cl.op = .div → s.mode = 3
  c7 : s.mode = 0 → (cl.op = .mul → s.role ≠ some 0 ∧ s.role ≠ some 1) ∧
    ((cl.op = .div ∨ cl.op = .mod) → s.role ≠ some 4 ∧ s.role ≠ some 1)

theorem SG.of_handle {p : ℕ} {cl : CallL} {s : SlotL} {r k t : ℕ} (hr : r < 7) (hrole : s.role = some r)
    (hmode : s.mode < 3) (hsk : s.sk = k) (hsv : s.sv = t) (hfac : s.mode = 0 → isFactor cl.op r = false)
    (hA : r = 0 → k = cl.kA ∧ t = cl.vA) (hB : r = 1 → k = cl.kB ∧ t = cl.vB)
    (hE : (r = 2 ∨ (r = 4 ∧ cl.op = .div) ∨ (r = 5 ∧ cl.op = .mod)) → k = cl.kE ∧ t = cl.vE)
    (h36 : r ≠ 3 ∧ r ≠ 6) (h4 : r = 4 → cl.op ≠ .mod) (h5 : r = 5 → cl.op ≠ .div)
    (ne : 0 < s.words.length) (m0 : s.mode = 0 → s.words = [0])
    (m1 : s.mode = 1 → ∃ v, v < p ∧ s.words = splitOf v ∧ s.sv = v ∧ s.sk = 0)
    (wb : ∀ w ∈ s.words, w < Bn) (vw : (s.mode = 1 ∨ s.mode = 2) → s.vw = s.words)
    (sk2 : (s.mode = 0 ∨ s.mode = 2) → s.sk = 2) : SG p cl s := by
  have hm3 : s.mode ≠ 3 := by omega
  refine ⟨ne, Or.inl ⟨r, hr, hrole, by omega⟩, m0, m1, fun _ => wb, ?_, sk2, ?_, ?_, ?_, fun _ => hm3, ?_,
    fun _ _ => hm3, ?_, fun _ _ => hm3, ?_, ?_⟩
  · intro h; rcases h with h | h | h
    · exact vw (Or.inl h)
    · exact vw (Or.inr h)
    · omega
  · intro h; rw [hrole] at h; simp only [Option.some.injEq] at h; subst h
    obtain ⟨a, b⟩ := hA rfl; exact ⟨hsk ▸ a, hsv ▸ b⟩
  · intro h; rw [hrole] at h; simp only [Option.some.injEq] at h; subst h
    obtain ⟨a, b⟩ := hB rfl; exact ⟨hsk ▸ a, hsv ▸ b⟩
  · intro h
    have h' : r = 2 ∨ (r = 4 ∧ cl.op = .div) ∨ (r = 5 ∧ cl.op = .mod) := by
      rw [hrole] at h
      simpa only [Option.some.injEq] using h
    obtain ⟨a, b⟩ := hE h'; exact ⟨hsk ▸ a, hsv ▸ b⟩
  · intro h; rw [hrole] at h; simp only [Option.some.injEq] at h
    rcases h with h | h
    · exact absurd h h36.1
    · exact absurd h h36.2
  · intro h h'; rw [hrole] at h; simp only [Option.some.injEq] at h; exact absurd h' (h4 h)
  · intro h h'; rw [hrole] at h; simp only [Option.some.injEq] at h; exact absurd h' (h5 h)
  · intro h0
    have hf := hfac h0
    rw [hrole]
    constructor
    · intro hm
      rw [hm] at hf
      simp only [isFactor, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      simp only [ne_eq, Option.some.injEq]
      exact hf
    · intro hm
      rcases hm with hm | hm <;> (rw [hm] at hf; simp only [isFactor, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
                                  simp only [ne_eq, Option.some.injEq]; exact hf)

theorem handle_SG {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (r v k t : ℕ) (hr : r < 7) (hk : HK p v k t)
    (hA : r = 0 → k = cl.kA ∧ t = cl.vA) (hB : r = 1 → k = cl.kB ∧ t = cl.vB)
    (hE : (r = 2 ∨ (r = 4 ∧ cl.op = .div) ∨ (r = 5 ∧ cl.op = .mod)) → k = cl.kE ∧ t = cl.vE)
    (h36 : r ≠ 3 ∧ r ≠ 6) (h4 : r = 4 → cl.op ≠ .mod) (h5 : r = 5 → cl.op ≠ .div) :
    SG p cl (handleSlot p cl.op cl.lbv r v k t) := by
  have hp0 : 0 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  rcases handleSlot_cases p cl.op cl.lbv r v k t with ⟨hv, c1, c2, e⟩ | ⟨hv, hf, c1, c2, e⟩ | ⟨hv, hf, c1, c2, e⟩
  · rw [e]
    obtain ⟨hk0, hkt⟩ := hk.1 hv
    refine SG.of_handle hr rfl (by norm_num) hk0.symm hkt.symm (by simp) hA hB hE h36 h4 h5 (by simp [splitOf])
      (by simp) (fun _ => ⟨v, hv, rfl, rfl, rfl⟩) (splitOf_lt hpG hv) (fun _ => rfl) (by simp)
  · rw [e]
    have hk2 := hk.2 hv
    refine SG.of_handle hr rfl (by norm_num) rfl rfl (by simp) hA hB hE h36 h4 h5 ?_ (by simp) (by simp)
      (fun w hw => limbs_lt hw) (fun _ => rfl) (fun _ => hk2)
    exact List.length_pos_of_ne_nil (limbs_ne_nil (by omega))
  · rw [e]
    have hk2 := hk.2 hv
    refine SG.of_handle hr rfl (by norm_num) rfl rfl (fun _ => hf) hA hB hE h36 h4 h5 (by simp) (fun _ => rfl)
      (by simp) (by intro w hw; simp at hw; subst hw; norm_num [Bn]) (by simp) (fun _ => hk2)

theorem wit_SG {p : ℕ} (cl : CallL) (r w : ℕ) (hr : r < 7) (h012 : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2)
    (h4 : r = 4 → cl.op ≠ .div) (h5 : r = 5 → cl.op ≠ .mod) :
    SG p cl (witSlot cl.op cl.lbv r w) := by
  have e : ∃ c1 c2, witSlot cl.op cl.lbv r w = ⟨some r, 3, wordsOf w, wordsOf w, 0, 0, c1, c2⟩ :=
    ⟨_, _, rfl⟩
  obtain ⟨c1, c2, e⟩ := e
  rw [e]
  refine ⟨List.length_pos_of_ne_nil (wordsOf_ne_nil w), Or.inl ⟨r, hr, rfl, by norm_num⟩, by simp, by simp,
    fun _ => wordsOf_lt w, fun _ => rfl, by simp, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, fun _ _ => rfl, ?_,
    fun _ _ => rfl, by simp⟩
  · intro h; simp only [Option.some.injEq] at h; exact absurd h h012.1
  · intro h; simp only [Option.some.injEq] at h; exact absurd h h012.2.1
  · intro h; simp only [Option.some.injEq] at h
    rcases h with h | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact absurd h h012.2.2
    · exact absurd h' (h4 h)
    · exact absurd h' (h5 h)
  · intro h; simp only [Option.some.injEq] at h; rcases h with h | h | h
    · exact absurd h h012.1
    · exact absurd h h012.2.1
    · exact absurd h h012.2.2
  · intro h h'; simp only [Option.some.injEq] at h; exact absurd h' (h4 h)
  · intro h h'; simp only [Option.some.injEq] at h; exact absurd h' (h5 h)

theorem q_key {p : ℕ} (cl : CallL) (w : List ℕ) (m : ℕ) (hm : m = 4 ∨ m = 5) (c1 c2 : ℤ) (hne : 0 < w.length) :
    SG p cl ⟨none, m, w, [], 0, 0, c1, c2⟩ := by
  refine ⟨hne, Or.inr ⟨rfl, hm⟩, fun h => by simp at h; omega, fun h => by simp at h; omega,
    fun h => by simp at h; omega, fun h => by simp at h; omega, fun h => by simp at h; omega,
    fun h => by simp at h, fun h => by simp at h, fun h => ?_, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h; omega⟩
  simp at h

theorem q_SG {p : ℕ} (cl : CallL) (packed : Bool) (qs : List ℤ) : SG p cl (qSlot cl.op packed qs) := by
  cases packed
  · simp only [qSlot, Bool.false_eq_true, if_false]
    refine q_key cl _ 5 (Or.inr rfl) _ _ ?_
    split_ifs with h
    · simp
    · exact List.length_pos_of_ne_nil h
  · simp only [qSlot, if_true]
    refine q_key cl _ 4 (Or.inl rfl) _ _ ?_
    split_ifs with h
    · simp
    · exact List.length_pos_of_ne_nil (packQ1_ne_nil _ h)

theorem slots_SG {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    ∀ s ∈ slotsOf p cl, SG p cl s := by
  intro s hs
  have hkA : HK p cl.a cl.kA cl.vA := ⟨hcl.kAok.1, hcl.kAok.2⟩
  have hkB : HK p cl.b cl.kB cl.vB := ⟨hcl.kBok.1, hcl.kBok.2⟩
  unfold slotsOf at hs
  dsimp only at hs
  split at hs
  · -- add
    have hkE : HK p cl.c cl.kE cl.vE := ⟨(hcl.kEok (by simp_all)).1, (hcl.kEok (by simp_all)).2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 2 _ _ _ (by norm_num) hkE (fun h => by simp at h) (fun h => by simp at h)
        (fun _ => ⟨rfl, rfl⟩) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
  · -- sub
    have hkE : HK p cl.c cl.kE cl.vE := ⟨(hcl.kEok (by simp_all)).1, (hcl.kEok (by simp_all)).2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 2 _ _ _ (by norm_num) hkE (fun h => by simp at h) (fun h => by simp at h)
        (fun _ => ⟨rfl, rfl⟩) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
  · -- lt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact wit_SG cl 3 _ (by norm_num) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
  · -- mul
    have hkE : HK p cl.c cl.kE cl.vE := ⟨(hcl.kEok (by simp_all)).1, (hcl.kEok (by simp_all)).2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 2 _ _ _ (by norm_num) hkE (fun h => by simp at h) (fun h => by simp at h)
        (fun _ => ⟨rfl, rfl⟩) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
  · -- div
    have hkE : HK p cl.c cl.kE cl.vE := ⟨(hcl.kEok (by simp_all)).1, (hcl.kEok (by simp_all)).2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 4 _ _ _ (by norm_num) hkE (fun h => by simp at h) (fun h => by simp at h)
        (fun _ => ⟨rfl, rfl⟩) (by simp) (fun _ => by simp_all) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact wit_SG cl 5 _ (by norm_num) (by simp) (fun h => by simp at h) (fun _ => by simp_all)
    · exact wit_SG cl 6 _ (by norm_num) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
    · exact q_SG cl _ _
  · -- mod
    have hkE : HK p cl.c cl.kE cl.vE := ⟨(hcl.kEok (by simp_all)).1, (hcl.kEok (by simp_all)).2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact handle_SG hpG cl 0 _ _ _ (by norm_num) hkA (fun _ => ⟨rfl, rfl⟩) (fun h => by simp at h)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact wit_SG cl 4 _ (by norm_num) (by simp) (fun _ => by simp_all) (fun h => by simp at h)
    · exact handle_SG hpG cl 1 _ _ _ (by norm_num) hkB (fun h => by simp at h) (fun _ => ⟨rfl, rfl⟩)
        (fun h => by simp at h) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact handle_SG hpG cl 5 _ _ _ (by norm_num) hkE (fun h => by simp at h) (fun h => by simp at h)
        (fun _ => ⟨rfl, rfl⟩) (by simp) (fun h => by simp at h) (fun _ => by simp_all)
    · exact wit_SG cl 6 _ (by norm_num) (by simp) (fun h => by simp at h) (fun h => by simp at h)
    · exact q_SG cl _ _
    · exact q_SG cl _ _
  · exact absurd (by simp_all) hcl.notDec

theorem handleSlot_role (p : ℕ) (o : PrimOp) (lb r v k t : ℕ) : (handleSlot p o lb r v k t).role = some r := by
  unfold handleSlot; split_ifs <;> rfl

theorem slots_head {p : ℕ} {cl : CallL} (hcl : CallOK p cl) :
    ∃ s0 tl, slotsOf p cl = s0 :: tl ∧ s0.role = some 0 := by
  unfold slotsOf
  dsimp only
  split
  all_goals first
    | exact ⟨_, _, rfl, handleSlot_role _ _ _ _ _ _ _⟩
    | exact absurd (by simp_all) hcl.notDec

/-! ## 1. The row index of a block -/

/-- The `(slot, row)` index of the lane rows of a list of slots, in order. -/
def idxOf (ss : List SlotL) : List (SlotL × ℕ) :=
  ss.flatMap fun s => (List.range s.words.length).map fun i => (s, i)

theorem idxOf_nil : idxOf [] = [] := rfl

theorem idxOf_cons (s : SlotL) (ss : List SlotL) :
    idxOf (s :: ss) = (List.range s.words.length).map (fun i => (s, i)) ++ idxOf ss := by
  simp [idxOf]

/-- The block rows through the row index. -/
def rowsOf {F : Type} [Field F] (p : ℕ) (cl : CallL) : List (BRow F) :=
  hdrRow cl :: (idxOf (slotsOf p cl)).map (fun x => slotRow p cl x.1 x.2)

theorem blockB_eq {F : Type} [Field F] (p : ℕ) (cl : CallL) : (blockB (F := F) p cl) = rowsOf p cl := by
  unfold rowsOf
  unfold blockB
  congr 1
  rw [idxOf, List.map_flatMap]
  refine List.flatMap_congr (fun a _ => ?_)
  simp [slotRows, List.map_map, Function.comp_def]

/-- Adjacency in `idxOf`. -/
theorem idx_prop : ∀ (ss : List SlotL), (∀ s ∈ ss, 0 < s.words.length) → ∀ (k : ℕ) (a : SlotL × ℕ),
    (idxOf ss)[k]? = some a →
      (a.1 ∈ ss ∧ a.2 < a.1.words.length) ∧ (k = 0 → a.2 = 0) ∧
      ((idxOf ss)[k + 1]? = none → a.2 + 1 = a.1.words.length) ∧
      (∀ b, (idxOf ss)[k + 1]? = some b →
        (b = (a.1, a.2 + 1) ∧ a.2 + 1 < a.1.words.length) ∨ (a.2 + 1 = a.1.words.length ∧ b.2 = 0 ∧ b.1 ∈ ss))
  | [], _, k, a, h => by simp [idxOf] at h
  | s :: ss, hne, k, a, h => by
    have ih := idx_prop ss (fun x hx => hne x (List.mem_cons_of_mem _ hx))
    have hn : 0 < s.words.length := hne s List.mem_cons_self
    rw [idxOf_cons] at h ⊢
    set n := s.words.length with hnn
    by_cases hk : k < n
    · have hl : ((List.range n).map (fun i => (s, i)))[k]? = some (s, k) := by simp [hk]
      rw [List.getElem?_append_left (by simpa using hk), hl] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨⟨List.mem_cons_self, hk⟩, fun _ => ‹k = 0›, ?_, ?_⟩
      · intro h2
        by_contra hne2
        dsimp only at hne2
        have : k + 1 < n := by omega
        rw [List.getElem?_append_left (by simpa using this)] at h2
        simp [this] at h2
      · intro b hb
        by_cases hk1 : k + 1 < n
        · rw [List.getElem?_append_left (by simpa using hk1)] at hb
          simp [hk1] at hb
          left; exact ⟨hb.symm, hk1⟩
        · have hk1' : k + 1 = n := by omega
          right
          refine ⟨hk1', ?_⟩
          rw [List.getElem?_append_right (by simp; omega)] at hb
          simp only [List.length_map, List.length_range] at hb
          rw [show k + 1 - n = 0 by omega] at hb
          cases hss : idxOf ss with
          | nil => rw [hss] at hb; simp at hb
          | cons c cs =>
            rw [hss] at hb
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
            subst hb
            have h0 : (idxOf ss)[0]? = some c := by rw [hss]; rfl
            exact ⟨(ih 0 c h0).2.1 rfl, List.mem_cons_of_mem _ (ih 0 c h0).1.1⟩
    · have hk' : n ≤ k := by omega
      rw [List.getElem?_append_right (by simpa using hk')] at h
      simp only [List.length_map, List.length_range] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih (k - n) a h
      refine ⟨⟨List.mem_cons_of_mem _ h1.1, h1.2⟩, fun h0 => by omega, ?_, ?_⟩
      · intro hnone
        rw [List.getElem?_append_right (by simp; omega)] at hnone
        simp only [List.length_map, List.length_range] at hnone
        rw [show k + 1 - n = k - n + 1 by omega] at hnone
        exact h3 hnone
      · intro b hb
        rw [List.getElem?_append_right (by simp; omega)] at hb
        simp only [List.length_map, List.length_range] at hb
        rw [show k + 1 - n = k - n + 1 by omega] at hb
        rcases h4 b hb with h5 | ⟨h5, h6, h7⟩
        · exact Or.inl h5
        · exact Or.inr ⟨h5, h6, List.mem_cons_of_mem _ h7⟩

/-! ## 2. Successor pairs of a block -/

section Pair
variable {F : Type} [Field F]

/-- **The (row, successor) pairs of a block**: hdr to the first slot's first row, inside a slot, across slots, and
the last row of the block against any non-lane non-first row. -/
inductive PairK (p : ℕ) (cl : CallL) : BRow F → BRow F → Prop
  | hdr (s0 : SlotL) (hs0 : s0 ∈ slotsOf p cl) (hr : s0.role = some 0) :
      PairK p cl (hdrRow cl) (slotRow p cl s0 0)
  | mid (s : SlotL) (hs : s ∈ slotsOf p cl) (i : ℕ) (hi : i + 1 < s.words.length) :
      PairK p cl (slotRow p cl s i) (slotRow p cl s (i + 1))
  | cross (s : SlotL) (hs : s ∈ slotsOf p cl) (i : ℕ) (hi : i + 1 = s.words.length) (s' : SlotL)
      (hs' : s' ∈ slotsOf p cl) : PairK p cl (slotRow p cl s i) (slotRow p cl s' 0)
  | last (s : SlotL) (hs : s ∈ slotsOf p cl) (i : ℕ) (hi : i + 1 = s.words.length) (nxt : BRow F)
      (h : nxt.sL = 0 ∧ nxt.fst = 0) : PairK p cl (slotRow p cl s i) nxt

theorem pair_of_next {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) (j : ℕ)
    (hj : j < (blockB (F := F) p cl).length) (nxt : BRow F) (hn : NextOK (blockB p cl) j nxt) :
    PairK p cl ((blockB p cl).getD j BRow.zero) nxt := by
  have hne : ∀ s ∈ slotsOf p cl, 0 < s.words.length := fun s hs => (slots_SG hpG hcl s hs).ne
  obtain ⟨s0, tl, hss, hr0⟩ := slots_head hcl
  have hs0 : s0 ∈ slotsOf p cl := by rw [hss]; exact List.mem_cons_self
  have hn0 : 0 < s0.words.length := hne s0 hs0
  have h0 : (idxOf (slotsOf p cl))[0]? = some (s0, 0) := by
    rw [hss, idxOf_cons]
    rw [List.getElem?_append_left (by simpa using hn0)]
    simp [hn0]
  have hlen0 : 0 < (idxOf (slotsOf p cl)).length := (List.getElem?_eq_some_iff.mp h0).1
  rw [blockB_eq (F := F)] at hj hn ⊢
  cases j with
  | zero =>
    have hl1 : 0 + 1 < (rowsOf (F := F) p cl).length := by
      simp [rowsOf]; omega
    have h1 := hn.1 hl1
    have e : nxt = slotRow p cl s0 0 := by
      simpa [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_map, h0] using h1
    subst e
    exact PairK.hdr (F := F) s0 hs0 hr0
  | succ k =>
    have hk : k < (idxOf (slotsOf p cl)).length := by simp [rowsOf] at hj; omega
    obtain ⟨a, ha⟩ : ∃ a, (idxOf (slotsOf p cl))[k]? = some a := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨⟨hmem, hlt⟩, -, hnone, hsome⟩ := idx_prop (slotsOf p cl) hne k a ha
    have hcur : (rowsOf (F := F) p cl).getD (k + 1) BRow.zero
        = slotRow p cl a.1 a.2 := by
      simp [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_map, ha]
    rw [hcur]
    cases hb : (idxOf (slotsOf p cl))[k + 1]? with
    | none =>
      have hlast := hnone hb
      have hlen : (rowsOf (F := F) p cl).length ≤ k + 1 + 1 := by
        simp [rowsOf]
        by_contra hcon
        have : k + 1 < (idxOf (slotsOf p cl)).length := by omega
        rw [List.getElem?_eq_getElem this] at hb
        simp at hb
      exact PairK.last a.1 hmem a.2 hlast nxt (hn.2 hlen)
    | some b =>
      have hlen : k + 1 + 1 < (rowsOf (F := F) p cl).length := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [rowsOf]; omega
      have h1 := hn.1 hlen
      have e : nxt = slotRow p cl b.1 b.2 := by
        simpa [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_map, hb] using h1
      rw [e]
      rcases hsome b hb with ⟨hbe, hlt'⟩ | ⟨hlast, hb0, hbm⟩
      · rw [hbe]; exact PairK.mid a.1 hmem a.2 hlt'
      · have : slotRow (F := F) p cl b.1 b.2 = slotRow p cl b.1 0 := by rw [hb0]
        rw [this]
        exact PairK.cross a.1 hmem a.2 hlast b.1 hbm

end Pair

/-! ## 3. Gate groups -/

section Gates
variable {F : Type} [Field F]

open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 in
/-- The rows of a block. -/
def RowOK (p : ℕ) (cl : CallL) (cur : BRow F) : Prop :=
  cur = hdrRow cl ∨ ∃ s ∈ slotsOf p cl, ∃ i < s.words.length, cur = slotRow p cl s i

theorem PairK.rowOK {p : ℕ} {cl : CallL} {cur nxt : BRow F} (h : PairK p cl cur nxt) : RowOK p cl cur := by
  cases h with
  | hdr s0 hs0 hr => exact Or.inl rfl
  | mid s hs i hi => exact Or.inr ⟨s, hs, i, by omega, rfl⟩
  | cross s hs i hi s' hs' => exact Or.inr ⟨s, hs, i, by omega, rfl⟩
  | last s hs i hi nxt h => exact Or.inr ⟨s, hs, i, by omega, rfl⟩

theorem groupSat_of_pairs {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    (gs : List (AxisChipJ9.AG F))
    (h : ∀ cur nxt : BRow F, PairK p cl cur nxt → ∀ a ∈ gs, (AxisChipJ9.AG.gate a).eval (envB cur.col nxt.col) = 0) :
    GroupSat (F := F) p cl gs := by
  intro j hj nxt hn a ha
  exact h _ _ (pair_of_next hpG hcl j hj nxt hn) a ha

theorem groupSat_of_rows {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    (gs : List (AxisChipJ9.AG F))
    (h : ∀ cur : BRow F, RowOK p cl cur → ∀ nxt : BRow F, ∀ a ∈ gs,
      (AxisChipJ9.AG.gate a).eval (envB cur.col nxt.col) = 0) :
    GroupSat (F := F) p cl gs :=
  groupSat_of_pairs hpG hcl gs fun cur nxt hp a ha => h cur hp.rowOK nxt a ha

@[simp] theorem ind_true (c : Prop) [Decidable c] (h : c) : (ind c : F) = 1 := by simp [ind, h]
@[simp] theorem ind_false (c : Prop) [Decidable c] (h : ¬ c) : (ind c : F) = 0 := by simp [ind, h]

/-! ### Row field lemmas (all `rfl`) -/

section RowFields

@[simp] theorem hdrRow_op (cl : CallL) (j : ℕ) : (hdrRow cl : BRow F).op j = ind (j = opIx cl.op) := rfl
@[simp] theorem hdrRow_role (cl : CallL) (j : ℕ) : (hdrRow cl : BRow F).role j = 0 := rfl
@[simp] theorem hdrRow_mode (cl : CallL) (j : ℕ) : (hdrRow cl : BRow F).mode j = 0 := rfl
@[simp] theorem hdrRow_bit (cl : CallL) (j : ℕ) : (hdrRow cl : BRow F).bit j = 0 := rfl
@[simp] theorem hdrRow_cb (cl : CallL) (j : ℕ) : (hdrRow cl : BRow F).cb j = 0 := rfl
@[simp] theorem hdrRow_isFT (cl : CallL) : (hdrRow cl : BRow F).isFT = 0 := rfl
@[simp] theorem hdrRow_isLT (cl : CallL) : (hdrRow cl : BRow F).isLT = 0 := rfl
@[simp] theorem hdrRow_sP (cl : CallL) : (hdrRow cl : BRow F).sP = 0 := rfl
@[simp] theorem hdrRow_pId (cl : CallL) : (hdrRow cl : BRow F).pId = 0 := rfl
@[simp] theorem hdrRow_pOp (cl : CallL) : (hdrRow cl : BRow F).pOp = 0 := rfl
@[simp] theorem hdrRow_sH (cl : CallL) : (hdrRow cl : BRow F).sH = 1 := rfl
@[simp] theorem hdrRow_sL (cl : CallL) : (hdrRow cl : BRow F).sL = 0 := rfl
@[simp] theorem hdrRow_fst (cl : CallL) : (hdrRow cl : BRow F).fst = 0 := rfl
@[simp] theorem hdrRow_eos (cl : CallL) : (hdrRow cl : BRow F).eos = 0 := rfl
@[simp] theorem hdrRow_f1 (cl : CallL) : (hdrRow cl : BRow F).f1 = 0 := rfl
@[simp] theorem hdrRow_f2 (cl : CallL) : (hdrRow cl : BRow F).f2 = 0 := rfl
@[simp] theorem hdrRow_sf (cl : CallL) : (hdrRow cl : BRow F).sf = 0 := rfl
@[simp] theorem hdrRow_aV (cl : CallL) : (hdrRow cl : BRow F).aV = 0 := rfl
@[simp] theorem hdrRow_cf1 (cl : CallL) : (hdrRow cl : BRow F).cf1 = 0 := rfl
@[simp] theorem hdrRow_cf2 (cl : CallL) : (hdrRow cl : BRow F).cf2 = 0 := rfl
@[simp] theorem hdrRow_V (cl : CallL) : (hdrRow cl : BRow F).V = 0 := rfl
@[simp] theorem hdrRow_invP (cl : CallL) : (hdrRow cl : BRow F).invP = 0 := rfl
@[simp] theorem hdrRow_sk (cl : CallL) : (hdrRow cl : BRow F).sk = 0 := rfl
@[simp] theorem hdrRow_sv (cl : CallL) : (hdrRow cl : BRow F).sv = 0 := rfl
@[simp] theorem hdrRow_kA (cl : CallL) : (hdrRow cl : BRow F).kA = (cl.kA : F) := rfl
@[simp] theorem hdrRow_vA (cl : CallL) : (hdrRow cl : BRow F).vA = (cl.vA : F) := rfl
@[simp] theorem hdrRow_kB (cl : CallL) : (hdrRow cl : BRow F).kB = (cl.kB : F) := rfl
@[simp] theorem hdrRow_vB (cl : CallL) : (hdrRow cl : BRow F).vB = (cl.vB : F) := rfl
@[simp] theorem hdrRow_kE (cl : CallL) : (hdrRow cl : BRow F).kE = (cl.kE : F) := rfl
@[simp] theorem hdrRow_vE (cl : CallL) : (hdrRow cl : BRow F).vE = (cl.vE : F) := rfl
@[simp] theorem hdrRow_lb (cl : CallL) : (hdrRow cl : BRow F).lb = (cl.lbv : F) := rfl
@[simp] theorem hdrRow_idc (cl : CallL) : (hdrRow cl : BRow F).idc = (cl.id : F) := rfl
@[simp] theorem hdrRow_kc (cl : CallL) : (hdrRow cl : BRow F).kc = 1 := rfl
@[simp] theorem hdrRow_vc (cl : CallL) : (hdrRow cl : BRow F).vc = (cl.vc : F) := rfl
@[simp] theorem hdrRow_opc (cl : CallL) : (hdrRow cl : BRow F).opc = ((opIx cl.op + 1 : ℕ) : F) := rfl
@[simp] theorem hdrRow_kS (cl : CallL) : (hdrRow cl : BRow F).kS = 1 := rfl
@[simp] theorem hdrRow_vS (cl : CallL) : (hdrRow cl : BRow F).vS = (cl.vS : F) := rfl
@[simp] theorem hdrRow_mJ (cl : CallL) : (hdrRow cl : BRow F).mJ = 1 := rfl
@[simp] theorem hdrRow_mP (cl : CallL) : (hdrRow cl : BRow F).mP = 0 := rfl
@[simp] theorem hdrRow_cn (cl : CallL) : (hdrRow cl : BRow F).cn = 0 := rfl
@[simp] theorem hdrRow_cA (cl : CallL) : (hdrRow cl : BRow F).cA = 0 := rfl
@[simp] theorem hdrRow_cB (cl : CallL) : (hdrRow cl : BRow F).cB = 0 := rfl
@[simp] theorem slotRow_op (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) : (slotRow p cl s i : BRow F).op j = ind (j = opIx cl.op) := rfl
@[simp] theorem slotRow_role (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) : (slotRow p cl s i : BRow F).role j = ind (s.role = some j) := rfl
@[simp] theorem slotRow_mode (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) : (slotRow p cl s i : BRow F).mode j = ind (j = s.mode) := rfl
@[simp] theorem slotRow_bit (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) : (slotRow p cl s i : BRow F).bit j = ((bitOf (s.words.getD i 0) j : ℕ) : F) := rfl
@[simp] theorem slotRow_cb (p : ℕ) (cl : CallL) (s : SlotL) (i j : ℕ) : (slotRow p cl s i : BRow F).cb j = if s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3 then ((bitOf (i + 1) j : ℕ) : F) else 0 := by
  simp [slotRow]
@[simp] theorem slotRow_isFT (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).isFT = 0 := rfl
@[simp] theorem slotRow_isLT (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).isLT = 0 := rfl
@[simp] theorem slotRow_sP (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sP = 0 := rfl
@[simp] theorem slotRow_pId (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).pId = 0 := rfl
@[simp] theorem slotRow_pOp (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).pOp = 0 := rfl
@[simp] theorem slotRow_sH (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sH = 0 := rfl
@[simp] theorem slotRow_sL (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sL = 1 := rfl
@[simp] theorem slotRow_fst (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).fst = ind (i = 0) := by simp [slotRow]
@[simp] theorem slotRow_eos (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).eos = ind (i + 1 = s.words.length) := by simp [slotRow]
@[simp] theorem slotRow_f1 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).f1 = ind (i = 0 ∧ isF1 cl.op s = true) := by simp [slotRow]
@[simp] theorem slotRow_f2 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).f2 = ind (i = 0 ∧ isF2 cl.op s = true) := by simp [slotRow]
@[simp] theorem slotRow_sf (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sf = ind (i = 0 ∧ s.mode = 1) := by simp [slotRow]
@[simp] theorem slotRow_aV (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).aV = ind (i = 0 ∧ (s.mode = 0 ∨ s.mode = 2)) := by simp [slotRow]
@[simp] theorem slotRow_cf1 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).cf1 = if i = 0 then (s.cf1 : F) else 0 := by simp [slotRow]
@[simp] theorem slotRow_cf2 (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).cf2 = if i = 0 then (s.cf2 : F) else 0 := by simp [slotRow]
@[simp] theorem slotRow_V (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).V = if i = 0 ∧ s.mode = 1 then ((s.words.getD 0 0 + Bn * s.words.getD 1 0 : ℕ) : F) else 0 := by simp [slotRow]
@[simp] theorem slotRow_invP (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).invP = if i = 0 ∧ s.mode = 1 ∧ s.words.getD 0 0 ≠ 0 then ((s.words.getD 1 0 : F) - ((Bn - 1 : ℕ) : F))⁻¹ else 0 := by simp [slotRow]
@[simp] theorem slotRow_sk (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sk = (s.sk : F) := rfl
@[simp] theorem slotRow_sv (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).sv = (s.sv : F) := rfl
@[simp] theorem slotRow_kA (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).kA = (cl.kA : F) := rfl
@[simp] theorem slotRow_vA (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).vA = (cl.vA : F) := rfl
@[simp] theorem slotRow_kB (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).kB = (cl.kB : F) := rfl
@[simp] theorem slotRow_vB (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).vB = (cl.vB : F) := rfl
@[simp] theorem slotRow_kE (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).kE = (cl.kE : F) := rfl
@[simp] theorem slotRow_vE (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).vE = (cl.vE : F) := rfl
@[simp] theorem slotRow_lb (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).lb = (cl.lbv : F) := rfl
@[simp] theorem slotRow_idc (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).idc = 0 := rfl
@[simp] theorem slotRow_kc (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).kc = 0 := rfl
@[simp] theorem slotRow_vc (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).vc = 0 := rfl
@[simp] theorem slotRow_opc (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).opc = 0 := rfl
@[simp] theorem slotRow_kS (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).kS = 0 := rfl
@[simp] theorem slotRow_vS (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).vS = 0 := rfl
@[simp] theorem slotRow_mJ (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).mJ = 0 := rfl
@[simp] theorem slotRow_mP (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).mP = 0 := rfl
@[simp] theorem slotRow_cn (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).cn = if s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3 then ((i + 1 : ℕ) : F) else 0 := by simp [slotRow]
@[simp] theorem slotRow_cA (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).cA = if s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3 then ((bitOf (i + 1) 0 * bitOf (i + 1) 1 * bitOf (i + 1) 2 : ℕ) : F) else 0 := by simp [slotRow]
@[simp] theorem slotRow_cB (p : ℕ) (cl : CallL) (s : SlotL) (i : ℕ) : (slotRow p cl s i : BRow F).cB = if s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3 then ((bitOf (i + 1) 3 * bitOf (i + 1) 4 * bitOf (i + 1) 5 : ℕ) : F) else 0 := by simp [slotRow]

end RowFields

/-! ### Arithmetic of the `ind` sums -/

theorem ind_bool (c : Prop) [Decidable c] : (ind c : F) * (ind c - 1) = 0 := by
  by_cases h : c <;> simp [h]

theorem roleSum (ro : Option ℕ) (m : ℕ)
    (wf : (∃ r, r < 7 ∧ ro = some r ∧ m < 4) ∨ (ro = none ∧ (m = 4 ∨ m = 5))) :
    (ind (ro = some 0) + (ind (ro = some 1) + (ind (ro = some 2) + (ind (ro = some 3) + (ind (ro = some 4) +
      (ind (ro = some 5) + ind (ro = some 6))))))) = (if m < 4 then (1 : F) else 0) := by
  rcases wf with ⟨r, hr, rfl, hm⟩ | ⟨rfl, hm⟩
  · rw [if_pos hm]; interval_cases r <;> simp [ind]
  · rw [if_neg (by omega)]; simp [ind]

theorem modeSum4 (m : ℕ) :
    (ind (0 = m) + (ind (1 = m) + (ind (2 = m) + ind (3 = m))) : F) = (if m < 4 then (1 : F) else 0) := by
  by_cases h : m < 4
  · rw [if_pos h]; interval_cases m <;> simp [ind]
  · rw [if_neg h]
    have h0 : ¬ (0 = m) := by omega
    have h1 : ¬ (1 = m) := by omega
    have h2 : ¬ (2 = m) := by omega
    have h3 : ¬ (3 = m) := by omega
    simp [ind, h0, h1, h2, h3]

/-- The unfolding of a chip gate's evaluation into row fields. -/
macro "gsimp" : tactic => `(tactic| simp only [Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.AG.gate,
  Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.CopyG.gate, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.Op.expr,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.gKS, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.opCode,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.hzV, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.gHdrNotLast,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.ar, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.prod3,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.sumC, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.opCols,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.roleCols, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.modeCols,
  boolE, notE, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, nv, envB, List.map_cons, List.map_nil,
  List.map_append, List.sum_cons, List.sum_nil, List.sum_append, add_zero, BRow.col_isFT, BRow.col_isLT, BRow.col_sP, BRow.col_pId, BRow.col_pOp, BRow.col_sH, BRow.col_sL, BRow.col_oAdd, BRow.col_oSub, BRow.col_oLt, BRow.col_oMul, BRow.col_oDiv, BRow.col_oMod, BRow.col_ra, BRow.col_rb, BRow.col_rc, BRow.col_rd, BRow.col_rx, BRow.col_ry, BRow.col_rs, BRow.col_mR, BRow.col_mS, BRow.col_mV, BRow.col_mW, BRow.col_mQ1, BRow.col_mQM, BRow.col_fst, BRow.col_eos, BRow.col_f1, BRow.col_f2, BRow.col_sf, BRow.col_aV, BRow.col_cf1, BRow.col_cf2, BRow.col_invP, BRow.col_sk, BRow.col_sv, BRow.col_kA, BRow.col_vA, BRow.col_kB, BRow.col_vB, BRow.col_kE, BRow.col_vE, BRow.col_lb, BRow.col_idc, BRow.col_kc, BRow.col_vc, BRow.col_opc, BRow.col_kS, BRow.col_vS, BRow.col_mJ, BRow.col_mP, BRow.col_cn, BRow.col_cA, BRow.col_cB, BRow.col_Vc])

macro "gexpand" : tactic => `(tactic| simp only [Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.opCols,
  Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.roleCols, Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.modeCols,
  List.map_cons, List.map_nil, List.map_append, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
  false_imp_iff, implies_true, and_true])

theorem modeSum45 (m : ℕ) (wf : m < 4 ∨ m = 4 ∨ m = 5) :
    (ind (4 = m) + ind (5 = m) : F) = (if m < 4 then (0 : F) else 1) := by
  rcases wf with h | rfl | rfl
  · rw [if_pos h]
    have h4 : ¬ (4 = m) := by omega
    have h5 : ¬ (5 = m) := by omega
    simp [ind, h4, h5]
  · simp [ind]
  · simp [ind]

theorem opSum (o : PrimOp) (h : o ≠ .dec) :
    (ind (0 = opIx o) + (ind (1 = opIx o) + (ind (2 = opIx o) + (ind (3 = opIx o) +
      (ind (4 = opIx o) + ind (5 = opIx o))))) : F) = 1 := by
  cases o <;> simp [opIx, ind] at h ⊢

section Test
open AluSZChipJ9

theorem gKind_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gKind := by
  refine groupSat_of_rows hpG hcl _ ?_
  intro cur hcur nxt
  simp only [gKind]
  gexpand
  gsimp
  rcases hcur with rfl | ⟨s, hs, i, hi, rfl⟩
  · have h := opSum (F := ZMod p) cl.op hcl.notDec
    simp only [hdrRow_sH, hdrRow_sL, hdrRow_sP, hdrRow_isLT, hdrRow_op, hdrRow_role, hdrRow_mode, ind_bool, h]
    simp
  · have sg := slots_SG hpG hcl s hs
    have h1 := roleSum (F := ZMod p) s.role s.mode sg.wf
    have h2 := modeSum4 (F := ZMod p) s.mode
    have h3 := modeSum45 (F := ZMod p) s.mode (by rcases sg.wf with ⟨r, hr, hrole, hmode⟩ | ⟨hrole, hmode⟩ <;> omega)
    simp only [slotRow_sH, slotRow_sL, slotRow_sP, slotRow_isLT, slotRow_op, slotRow_role, slotRow_mode, ind_bool,
      h1, h2, h3]
    split_ifs <;> simp

theorem flag1 (m i : ℕ) : (ind (i = 0 ∧ m = 1) - ind (i = 0) * ind (1 = m) : F) = 0 := by
  by_cases h0 : i = 0 <;> by_cases h1 : m = 1 <;> simp [ind, h0, h1, eq_comm (a := 1) (b := m)]

theorem flag2 (m i : ℕ) : (ind (i = 0 ∧ (m = 0 ∨ m = 2)) - ind (i = 0) * (ind (0 = m) + ind (2 = m)) : F) = 0 := by
  by_cases h0 : i = 0 <;> by_cases h1 : m = 0 <;> by_cases h2 : m = 2 <;>
    simp [ind, h0, h1, h2, eq_comm (a := 0) (b := m), eq_comm (a := 2) (b := m)]

theorem flag3 (o : PrimOp) (s : SlotL) (i : ℕ) :
    (ind (i = 0 ∧ isF1 o s = true) - ind (i = 0) *
      (ind (3 = opIx o) * ind (s.role = some 0) + (ind (4 = opIx o) + ind (5 = opIx o)) * ind (s.role = some 4)) : F)
      = 0 := by
  cases o <;> by_cases h0 : i = 0 <;> by_cases h1 : s.role = some 0 <;> by_cases h2 : s.role = some 4 <;>
    simp [ind, isF1, opIx, h0, h1, h2]

theorem flag4 (o : PrimOp) (s : SlotL) (i : ℕ) :
    (ind (i = 0 ∧ isF2 o s = true) - ind (i = 0) * ind (s.role = some 1) *
      (ind (3 = opIx o) + (ind (4 = opIx o) + ind (5 = opIx o))) : F) = 0 := by
  cases o <;> by_cases h0 : i = 0 <;> by_cases h1 : s.role = some 1 <;> simp [ind, isF2, opIx, h0, h1]

theorem gFlag_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gFlag := by
  refine groupSat_of_rows hpG hcl _ ?_
  intro cur hcur nxt
  simp only [gFlag]
  gexpand
  gsimp
  rcases hcur with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp
  · simp only [slotRow_sf, slotRow_aV, slotRow_f1, slotRow_f2, slotRow_fst, slotRow_op, slotRow_role,
      slotRow_mode]
    exact ⟨flag1 _ _, flag2 _ _, flag3 _ _ _, by simpa [mul_assoc] using flag4 (F := ZMod p) cl.op s i⟩

theorem lb_bool {p : ℕ} {cl : CallL} (hcl : CallOK p cl) : (cl.lbv = 0 ∨ cl.lbv = 1) := by
  have h := hcl.sem
  unfold CallL.lbv
  split_ifs with ho
  · rw [ho] at h
    simp only [Nock.Jet.Prim.primSem, Option.some.injEq] at h
    split_ifs at h <;> omega
  · left; rfl

theorem gHdr_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gHdr := by
  refine groupSat_of_rows hpG hcl _ ?_
  intro cur hcur nxt
  simp only [gHdr]
  gexpand
  gsimp
  have hlb := lb_bool hcl
  have hlbb : (cl.lbv : ZMod p) * ((cl.lbv : ZMod p) - 1) = 0 := by
    rcases hlb with h | h <;> simp [h]
  rcases hcur with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp only [hdrRow_sH, hdrRow_sP, hdrRow_op, hdrRow_kE, hdrRow_vE, hdrRow_lb, hdrRow_kS, hdrRow_opc, hdrRow_idc]
    have hop := hcl.notDec
    refine ⟨?_, ?_, hlbb, by simp, ?_, by simp, by simp⟩
    · by_cases ho : cl.op = .lt
      · have := (hcl.kElt ho).1; simp [opIx, ho, ind, this]
      · generalize cl.op = o at *; cases o <;> simp [opIx, ind] at ho ⊢
    · by_cases ho : cl.op = .lt
      · have := (hcl.kElt ho).2; simp [opIx, ho, ind, this, CallL.lbv]
      · generalize cl.op = o at *; cases o <;> simp [opIx, ind] at ho ⊢
    · generalize cl.op = o at *; cases o <;> simp [opIx, ind] at hop ⊢
  · simp only [slotRow_sH, slotRow_sP, slotRow_lb]
    exact ⟨by simp, by simp, hlbb, by simp, by simp, by simp, by simp⟩

theorem ix0 (o : PrimOp) : (0 = opIx o) ↔ o = .add := by cases o <;> simp [opIx]
theorem ix1 (o : PrimOp) : (1 = opIx o) ↔ o = .sub := by cases o <;> simp [opIx]
theorem ix2 (o : PrimOp) : (2 = opIx o) ↔ o = .lt := by cases o <;> simp [opIx]
theorem ix3 (o : PrimOp) : (3 = opIx o) ↔ o = .mul := by cases o <;> simp [opIx]
theorem ix4 (o : PrimOp) : (4 = opIx o) ↔ o = .div := by cases o <;> simp [opIx]
theorem ix5 (o : PrimOp) : (5 = opIx o) ↔ o = .mod := by cases o <;> simp [opIx]

theorem bind2 (c1 c2 : Prop) [Decidable c1] [Decidable c2] (a b : ℕ) (h : c1 → c2 → a = b) :
    (ind c1 * ind c2 * ((a : F) - (b : F))) = 0 := by
  by_cases h1 : c1
  · by_cases h2 : c2
    · have := h h1 h2; subst this; simp [ind, h1, h2]
    · simp [ind, h2]
  · simp [ind, h1]

theorem bind3 (c1 c2 c3 : Prop) [Decidable c1] [Decidable c2] [Decidable c3] (a b : ℕ)
    (h : c1 → c2 → c3 → a = b) : (ind c1 * ind c2 * ind c3 * ((a : F) - (b : F))) = 0 := by
  by_cases h1 : c1
  · by_cases h2 : c2
    · by_cases h3 : c3
      · have := h h1 h2 h3; subst this; simp [ind, h1, h2, h3]
      · simp [ind, h3]
    · simp [ind, h2]
  · simp [ind, h1]

theorem gBind_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gBind := by
  refine groupSat_of_rows hpG hcl _ ?_
  intro cur hcur nxt
  simp only [gBind, AluSZChipJ9.bind]
  gexpand
  gsimp
  rcases hcur with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp
  · have sg := slots_SG hpG hcl s hs
    simp only [slotRow_sf, slotRow_fst, slotRow_role, slotRow_mode, slotRow_op, slotRow_sk, slotRow_sv,
      slotRow_kA, slotRow_vA, slotRow_kB, slotRow_vB, slotRow_kE, slotRow_vE, ix4, ix5, and_assoc]
    have hA := sg.bA
    have hB := sg.bB
    have hE := sg.bE
    refine ⟨bind2 _ _ _ _ fun _ h => (hA h).1, bind2 _ _ _ _ fun _ h => (hA h).2,
      bind2 _ _ _ _ fun _ h => (hB h).1, bind2 _ _ _ _ fun _ h => (hB h).2,
      bind2 _ _ _ _ fun _ h => (hE (Or.inl h)).1, bind2 _ _ _ _ fun _ h => (hE (Or.inl h)).2,
      bind3 _ _ _ _ _ fun _ h h' => (hE (Or.inr (Or.inl ⟨h, h'⟩))).1,
      bind3 _ _ _ _ _ fun _ h h' => (hE (Or.inr (Or.inl ⟨h, h'⟩))).2,
      bind3 _ _ _ _ _ fun _ h h' => (hE (Or.inr (Or.inr ⟨h, h'⟩))).1,
      bind3 _ _ _ _ _ fun _ h h' => (hE (Or.inr (Or.inr ⟨h, h'⟩))).2, ?_, ?_⟩
    · have h2 := sg.sk2
      by_cases hm0 : s.mode = 0
      · have := h2 (Or.inl hm0); simp [ind, hm0, this]
      · by_cases hm2 : s.mode = 2
        · have := h2 (Or.inr hm2); simp [ind, hm2, this]
        · have e0 : ¬ (0 = s.mode) := fun h => hm0 h.symm
          have e2 : ¬ (2 = s.mode) := fun h => hm2 h.symm
          simp [ind, e0, e2]
    · by_cases hm1 : s.mode = 1
      · obtain ⟨v, -, -, -, hsk⟩ := sg.m1 hm1
        simp [ind, hm1, hsk]
      · simp [ind, hm1]


/-! ### Bit sums -/

/-- The 32 lane-bit booleanities of `gBits` (the split of : `gBits = gBitsB ++ gBitsQM`). -/
def gBitsB : List (AxisChipJ9.AG F) := (List.range 32).map (fun t => AluSZChipJ9.ar (boolE (cv (AluSZChipJ9.bt0 + t))))

/-- The `mQM·b_t = 0` part, `t ≥ 25`. -/
def gBitsQM : List (AxisChipJ9.AG F) :=
  (List.range 7).map (fun t => AluSZChipJ9.ar (.mul (cv AluSZChipJ9.mQM) (cv (AluSZChipJ9.bt0 + 25 + t))))

theorem gBits_split : (AluSZChipJ9.gBits : List (AxisChipJ9.AG F)) = gBitsB ++ gBitsQM := rfl

theorem bitsum_nat (k w : ℕ) : ∀ n : ℕ, ∑ i ∈ Finset.range n, 2 ^ i * (w / 2 ^ (k + i) % 2) = (w / 2 ^ k) % 2 ^ n
  | 0 => by rw [pow_zero, Nat.mod_one]; simp
  | n + 1 => by
    rw [Finset.sum_range_succ, bitsum_nat k w n, Nat.mod_pow_succ]
    congr 2
    rw [pow_add, Nat.div_div_eq_div_mul]

theorem bitsum_F {Fq : Type} [Field Fq] (k w n : ℕ) :
    ∑ i ∈ Finset.range n, (2 : Fq) ^ i * ((bitOf w (k + i) : ℕ) : Fq) = (((w / 2 ^ k) % 2 ^ n : ℕ) : Fq) := by
  have := bitsum_nat k w n
  rw [← this]
  push_cast [bitOf]
  rfl

theorem bitsum_lt (w n : ℕ) (hw : w < 2 ^ n) : (w / 2 ^ 0) % 2 ^ n = w := by
  simp [Nat.mod_eq_of_lt hw]

/-- The lane value of a row: the bit sum of a word below `2^32`. -/
theorem laneBits_F {Fq : Type} [Field Fq] (w : ℕ) (hw : w < 2 ^ 32) :
    ∑ i ∈ Finset.range 32, (2 : Fq) ^ i * ((bitOf w i : ℕ) : Fq) = (w : Fq) := by
  have := bitsum_F (Fq := Fq) 0 w 32
  simp only [zero_add, pow_zero, Nat.div_one] at this
  rw [this, Nat.mod_eq_of_lt hw]

theorem laneHi_F {Fq : Type} [Field Fq] (w : ℕ) (hw : w < 2 ^ 32) :
    ∑ i ∈ Finset.range 16, (2 : Fq) ^ i * ((bitOf w (16 + i) : ℕ) : Fq) = ((w / 2 ^ 16 : ℕ) : Fq) := by
  rw [bitsum_F (Fq := Fq) 16 w 16, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  calc w < 2 ^ 32 := hw
    _ = 2 ^ 16 * 2 ^ 16 := by norm_num

theorem bitOf_bool {Fq : Type} [Field Fq] (w t : ℕ) : ((bitOf w t : ℕ) : Fq) * (((bitOf w t : ℕ) : Fq) - 1) = 0 := by
  have : bitOf w t = 0 ∨ bitOf w t = 1 := by unfold bitOf; omega
  rcases this with h | h <;> simp [h]

theorem slot_word_lt {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) {s : SlotL}
    (hs : s ∈ slotsOf p cl) (hm : s.mode < 4) (i : ℕ) : s.words.getD i 0 < 2 ^ 32 := by
  have sg := slots_SG hpG hcl s hs
  by_cases hi : i < s.words.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact sg.wb hm _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

theorem gBitsB_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl (gBitsB (F := ZMod p)) := by
  refine groupSat_of_rows hpG hcl _ ?_
  intro cur hcur nxt a ha
  simp only [gBitsB, List.mem_map, List.mem_range] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  simp only [AluSZChipJ9.ar, AxisChipJ9.AG.gate, CoeffExpr.eval, envB, boolE, cv, BRow.col_bit _ t ht]
  show cur.bit t * (cur.bit t - 1) = 0
  rcases hcur with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp
  · exact bitOf_bool _ _

theorem gConst_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gConst := by
  refine groupSat_of_pairs hpG hcl _ ?_
  intro cur nxt hp
  simp only [gConst]
  gexpand
  gsimp
  cases hp with
  | hdr s0 hs0 hr => simp
  | mid s hs i hi => simp
  | cross s hs i hi s' hs' => simp
  | last s hs i hi nxt h => simp [h.1]

theorem gSlot_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gSlot := by
  refine groupSat_of_pairs hpG hcl _ ?_
  intro cur nxt hp
  simp only [gSlot, gHdrNotLast]
  gexpand
  gsimp
  cases hp with
  | hdr s0 hs0 hr =>
    simp [hr, ind]
  | mid s hs i hi =>
    have h1 : ¬ (i + 1 = s.words.length) := by omega
    simp [ind, h1]
    intro h; simp [h]
  | cross s hs i hi s' hs' =>
    simp [ind, hi]
    intro h; simp [h]
  | last s hs i hi nxt h =>
    simp [ind, hi, h.1, h.2]
    intro h; simp [h]

theorem prod3_zero (c1 c2 c3 : Prop) [Decidable c1] [Decidable c2] [Decidable c3] (h : c1 → c2 → ¬ c3) :
    (ind c1 * ind c2 * ind c3 : F) = 0 := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;> simp [ind, h1, h2, h3] at h ⊢

theorem prod3_zero' (c1 c2 c3 : Prop) [Decidable c1] [Decidable c2] [Decidable c3] (h : c1 → c2 → c3) :
    (ind c1 * ind c2 * (1 - ind c3) : F) = 0 := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;> simp [ind, h1, h2, h3] at h ⊢

theorem fstMode1_next {p : ℕ} [Fact p.Prime] {cl : CallL} (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl) {cur nxt : BRow (ZMod p)}
    (hp : PairK p cl cur nxt) : cur.fst * cur.mode 1 * (1 - nxt.eos) = 0 := by
  cases hp with
  | hdr s0 hs0 hr => simp
  | mid s hs i hi =>
    have sg := slots_SG hpG hcl s hs
    simp only [slotRow_fst, slotRow_mode, slotRow_eos]
    by_cases h0 : i = 0
    · by_cases hm : 1 = s.mode
      · obtain ⟨v, -, hw, -⟩ := sg.m1 hm.symm
        have : s.words.length = 2 := by rw [hw]; rfl
        have hm' := hm.symm
        simp [ind, h0, hm', this]
      · simp [ind, hm]
    · simp [ind, h0]
  | cross s hs i hi s' hs' =>
    have sg := slots_SG hpG hcl s hs
    simp only [slotRow_fst, slotRow_mode]
    by_cases h0 : i = 0
    · by_cases hm : 1 = s.mode
      · obtain ⟨v, -, hw, -⟩ := sg.m1 hm.symm
        have : s.words.length = 2 := by rw [hw]; rfl
        omega
      · simp [ind, hm]
    · simp [ind, h0]
  | last s hs i hi nxt h =>
    have sg := slots_SG hpG hcl s hs
    simp only [slotRow_fst, slotRow_mode]
    by_cases h0 : i = 0
    · by_cases hm : 1 = s.mode
      · obtain ⟨v, -, hw, -⟩ := sg.m1 hm.symm
        have : s.words.length = 2 := by rw [hw]; rfl
        omega
      · simp [ind, hm]
    · simp [ind, h0]

theorem gCompat_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gCompat := by
  refine groupSat_of_pairs hpG hcl _ ?_
  intro cur nxt hp
  have h10 := fstMode1_next hpG hcl hp
  simp only [gCompat]
  gexpand
  gsimp
  have hrow := hp.rowOK
  rcases hrow with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp
  · simp only [slotRow_op, slotRow_role, slotRow_mode, slotRow_eos, slotRow_fst, ix3, ix4, ix5]
    simp only [slotRow_fst, slotRow_mode] at h10
    have sg := slots_SG hpG hcl s hs
    refine ⟨?_, ?_, prod3_zero _ _ _ fun h1 h2 h3 => sg.c3 h1 h2 h3.symm,
      prod3_zero' _ _ _ fun h1 h2 => (sg.c4 h1 h2).symm,
      prod3_zero _ _ _ fun h1 h2 h3 => sg.c5 h1 h2 h3.symm,
      prod3_zero' _ _ _ fun h1 h2 => (sg.c6 h1 h2).symm, ?_, ?_, ?_, h10⟩
    · by_cases hm : 3 = s.mode
      · have h := sg.c1
        have n0 : s.role ≠ some 0 := fun h' => h (Or.inl h') hm.symm
        have n1 : s.role ≠ some 1 := fun h' => h (Or.inr (Or.inl h')) hm.symm
        have n2 : s.role ≠ some 2 := fun h' => h (Or.inr (Or.inr h')) hm.symm
        simp [ind, hm, n0, n1, n2]
      · simp [ind, hm]
    · by_cases hm : 3 = s.mode
      · simp [ind, hm]
      · have h := sg.c2
        have n3 : s.role ≠ some 3 := fun h' => hm (h (Or.inl h')).symm
        have n6 : s.role ≠ some 6 := fun h' => hm (h (Or.inr h')).symm
        simp [ind, hm, n3, n6]
    · by_cases hm : 0 = s.mode
      · obtain ⟨ha, hb⟩ := sg.c7 hm.symm
        have hm' := hm.symm
        by_cases hmul : cl.op = .mul
        · have := ha hmul
          simp [ind, hm', hmul, this.1, this.2]
        · by_cases hd : cl.op = .div ∨ cl.op = .mod
          · have := hb hd
            rcases hd with hd | hd <;> simp [ind, hm', hmul, hd, this.1, this.2]
          · rw [not_or] at hd
            simp [ind, hm', hmul, hd.1, hd.2]
      · simp [ind, hm]
    · by_cases hm : 0 = s.mode
      · have := sg.m0 hm.symm
        have hn : s.words.length = 1 := by rw [this]; rfl
        have : i + 1 = s.words.length := by omega
        simp [ind, this]
      · simp [ind, hm]
    · by_cases h0 : i = 0
      · by_cases hm : 1 = s.mode
        · obtain ⟨v, -, hw, -⟩ := sg.m1 hm.symm
          have : s.words.length = 2 := by rw [hw]; rfl
          have : ¬ (i + 1 = s.words.length) := by omega
          simp [ind, this]
        · simp [ind, hm]
      · simp [ind, h0]

theorem lane_eval_cur {Fq : Type} [Field Fq] (r : BRow Fq) (nx : ℕ → Fq) (c pu : ℕ → Fq) (w : ℕ)
    (hr : ∀ t < 32, r.bit t = ((bitOf w t : ℕ) : Fq)) (hw : w < 2 ^ 32) :
    (bitSum AluSZChipJ9.bt0 32 : CoeffExpr Fq).eval ⟨r.col, nx, c, pu⟩ = (w : Fq) := by
  rw [eval_bitSum]
  show ∑ i ∈ Finset.range 32, (2 : Fq) ^ i * r.col (AluSZChipJ9.bt0 + i) = _
  rw [Finset.sum_congr rfl (fun i hi => by rw [BRow.col_bit r i (Finset.mem_range.mp hi), hr i (Finset.mem_range.mp hi)])]
  exact laneBits_F w hw

theorem lane_nxt {Fq : Type} [Field Fq] (r : BRow Fq) (w : ℕ)
    (hr : ∀ t < 32, r.bit t = ((bitOf w t : ℕ) : Fq)) (hw : w < 2 ^ 32) :
    (List.map (fun i => (2 : Fq) ^ i * r.col (AluSZChipJ9.bt0 + i)) (List.range 32)).sum = (w : Fq) := by
  rw [list_range_sum]
  rw [Finset.sum_congr rfl (fun i hi => by rw [BRow.col_bit r i (Finset.mem_range.mp hi), hr i (Finset.mem_range.mp hi)])]
  exact laneBits_F w hw

theorem notSplitTail {p : ℕ} (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) {s : SlotL}
    (hs : s ∈ slotsOf p cl) {i : ℕ} (hi : i + 1 = s.words.length) : ¬ (i = 0 ∧ s.mode = 1) := by
  rintro ⟨h0, hm⟩
  have sg := slots_SG hpG hcl s hs
  obtain ⟨v, -, hw, -⟩ := sg.m1 hm
  have : s.words.length = 2 := by rw [hw]; rfl
  omega

theorem splitMain {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) {s : SlotL}
    (hs : s ∈ slotsOf p cl) (hm : s.mode = 1) :
    ∃ v : ℕ, v < p ∧ s.sv = v ∧ s.words.getD 0 0 = v % Bn ∧ s.words.getD 1 0 = v / Bn := by
  have sg := slots_SG hpG hcl s hs
  obtain ⟨v, hv, hw, hsv, -⟩ := sg.m1 hm
  exact ⟨v, hv, hsv, by simp [hw, splitOf], by simp [hw, splitOf]⟩

theorem hi_lt {p v : ℕ} (hpG : p = Nock.Atoms.p) (hv : v < p) (hlo : v % Bn ≠ 0) : v / Bn + 1 < Bn := by
  have hp : p = 1 + Bn * (Bn - 1) := by
    have h0 : p = 1 + Nock.Atoms.B * (Nock.Atoms.B - 1) := hpG ▸ Nock.Atoms.p_eq_limbs
    have hB : Nock.Atoms.B = Bn := rfl
    rw [hB] at h0
    exact h0
  have hBpos : 2 ≤ Bn := by norm_num [Bn]
  generalize Bn = B at *
  by_contra hc
  have h1 : B - 1 ≤ v / B := by omega
  have h2 : B * (B - 1) ≤ v := by
    calc B * (B - 1) ≤ B * (v / B) := Nat.mul_le_mul_left _ h1
      _ ≤ v := Nat.mul_div_le v B
  have h3 : v = B * (B - 1) := by omega
  apply hlo
  rw [h3]
  exact Nat.mul_mod_right _ _

theorem gSplit_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gSplit := by
  refine groupSat_of_pairs hpG hcl _ ?_
  intro cur nxt hp
  simp only [gSplit, gSplitV, gLtP, lE, lN]
  gexpand
  gsimp
  cases hp with
  | hdr s0 hs0 hr => simp
  | mid s hs i hi =>
    simp only [slotRow_sf, slotRow_V, slotRow_invP, slotRow_sv]
    by_cases h : i = 0 ∧ s.mode = 1
    · obtain ⟨hi0, hm⟩ := h
      subst hi0
      obtain ⟨v, hv, hsv, hlo, hhi⟩ := splitMain hpG hcl hs hm
      have hb := splitOf_lt hpG hv
      have hlt0 : v % Bn < 2 ^ 32 := hb _ (by simp [splitOf])
      have hlt1 : v / Bn < 2 ^ 32 := hb _ (by simp [splitOf])
      have e0 := lane_eval_cur (slotRow (F := ZMod p) p cl s 0) (slotRow p cl s 1).col (fun _ => 0) (fun _ => 0) (v % Bn)
        (fun t _ => by show ((bitOf (s.words.getD 0 0) t : ℕ) : ZMod p) = _; rw [hlo]) hlt0
      have e1 := lane_nxt (slotRow (F := ZMod p) p cl s 1) (v / Bn)
        (fun t _ => by show ((bitOf (s.words.getD 1 0) t : ℕ) : ZMod p) = _; rw [hhi]) hlt1
      rw [e0, e1]
      simp only [hlo, hhi, hsv, hm, ind, and_self, if_true, true_and, ne_eq]
      have hBf : (Bf : ZMod p) = ((Bn : ℕ) : ZMod p) := by norm_num [Bf, Bn]
      refine ⟨?_, ?_, ?_⟩
      · rw [one_mul, Nat.cast_add, Nat.cast_mul, hBf]; ring
      · by_cases hz : v % Bn = 0
        · simp [hz]
        · rw [if_pos hz, one_mul]
          have hh := hi_lt hpG hv hz
          have hne : ((v / Bn : ℕ) : ZMod p) - ((Bn - 1 : ℕ) : ZMod p) ≠ 0 := by
            rw [sub_ne_zero]
            intro hc
            rw [ZMod.natCast_eq_natCast_iff'] at hc
            have hpp : Bn < p := hcl.hp
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
            omega
          have h3 : (Bf : ZMod p) - 1 = ((Bn - 1 : ℕ) : ZMod p) := by
            have : 1 ≤ Bn := Nat.one_le_two_pow
            rw [hBf, Nat.cast_sub this]; simp
          rw [h3, mul_inv_cancel₀ hne, sub_self, mul_zero]
      · rw [one_mul, Nat.mod_add_div]; simp
    · simp [ind, h]
  | cross s hs i hi s' hs' =>
    have := notSplitTail hpG hcl hs hi
    simp [ind, this]
  | last s hs i hi nxt h =>
    have := notSplitTail hpG hcl hs hi
    simp [ind, this]

theorem bitOf_prod : ∀ n < 63, bitOf n 0 * bitOf n 1 * bitOf n 2 * (bitOf n 3 * bitOf n 4 * bitOf n 5) = 0 := by
  unfold bitOf; decide

theorem modeSum_hv {Fq : Type} [Field Fq] (m : ℕ) :
    (ind (1 = m) + (ind (2 = m) + ind (3 = m)) : Fq) = if (m = 1 ∨ m = 2 ∨ m = 3) then 1 else 0 := by
  by_cases h : m = 1 ∨ m = 2 ∨ m = 3
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp [ind]
  · rw [if_neg h]
    have h1 : ¬ (1 = m) := fun e => h (Or.inl e.symm)
    have h2 : ¬ (2 = m) := fun e => h (Or.inr (Or.inl e.symm))
    have h3 : ¬ (3 = m) := fun e => h (Or.inr (Or.inr e.symm))
    simp [ind, h1, h2, h3]

theorem cap_row {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    {cur : BRow (ZMod p)} (hrow : RowOK p cl cur) :
    cur.cn = ∑ i ∈ Finset.range 6, (2 : ZMod p) ^ i * cur.cb i ∧ (∀ i < 6, cur.cb i * (cur.cb i - 1) = 0) ∧
    cur.cA = cur.cb 0 * cur.cb 1 * cur.cb 2 ∧ cur.cB = cur.cb 3 * cur.cb 4 * cur.cb 5 ∧ cur.cA * cur.cB = 0 ∧
    cur.fst * (cur.mode 1 + (cur.mode 2 + cur.mode 3)) * (cur.cn - 1) = 0 := by
  rcases hrow with rfl | ⟨s, hs, i, hi, rfl⟩
  · simp [Finset.sum_const_zero]
  · simp only [slotRow_cn, slotRow_cb, slotRow_cA, slotRow_cB, slotRow_fst, slotRow_mode]
    rw [modeSum_hv]
    by_cases hv : s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3
    · have hl := hcl.limbs62 s hs hv
      simp only [if_pos hv]
      refine ⟨?_, fun j _ => bitOf_bool _ _, by push_cast; rfl, by push_cast; rfl, ?_, ?_⟩
      · have := bitsum_F (Fq := ZMod p) 0 (i + 1) 6
        simp only [zero_add, pow_zero, Nat.div_one] at this
        rw [this, Nat.mod_eq_of_lt (by omega)]
      · have := bitOf_prod (i + 1) (by omega)
        rw [← Nat.cast_mul, this]; simp
      · by_cases h0 : i = 0
        · subst h0; simp [ind]
        · simp [ind, h0]
    · simp only [if_neg hv]
      simp [Finset.sum_const_zero]

theorem cap_next {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    {cur nxt : BRow (ZMod p)} (hp : PairK p cl cur nxt) :
    (cur.mode 1 + (cur.mode 2 + cur.mode 3)) * (1 - cur.eos) * (nxt.cn - cur.cn - 1) = 0 := by
  cases hp with
  | hdr s0 hs0 hr => simp
  | mid s hs i hi =>
    simp only [slotRow_cn, slotRow_mode, slotRow_eos]
    rw [modeSum_hv]
    by_cases hv : s.mode = 1 ∨ s.mode = 2 ∨ s.mode = 3
    · have h1 : ¬ (i + 1 = s.words.length) := by omega
      simp only [if_pos hv, ind, if_neg h1]
      push_cast; ring
    · simp [if_neg hv]
  | cross s hs i hi s' hs' =>
    simp [slotRow_eos, ind, hi]
  | last s hs i hi nxt h =>
    simp [slotRow_eos, ind, hi]

theorem gCap_sat {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl gCap := by
  refine groupSat_of_pairs hpG hcl _ ?_
  intro cur nxt hp a ha
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := cap_row hpG hcl hp.rowOK
  have f7 := cap_next hpG hcl hp
  simp only [gCap, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | ⟨i, hi, rfl⟩) | rfl | rfl | rfl | rfl | rfl
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, cnE, eval_bitSum, cv, BRow.col_cn]
    rw [Finset.sum_congr rfl (fun i hi => by rw [BRow.col_cb _ i (Finset.mem_range.mp hi)] : ∀ i ∈ Finset.range 6,
      (2 : ZMod p) ^ i * cur.col (AluSZChipJ9.cb0 + i) = (2 : ZMod p) ^ i * cur.cb i)]
    show cur.cn - _ = 0
    rw [← f1]; ring
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, boolE, cv, BRow.col_cb _ i hi]
    exact f2 i hi
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, prod3, cv]
    have e1 := BRow.col_cb cur 0 (by norm_num)
    have e2 := BRow.col_cb cur 1 (by norm_num)
    have e3 := BRow.col_cb cur 2 (by norm_num)
    simp only [add_zero] at e1
    simp only [BRow.col_cA, e1, e2, e3]
    rw [f3]; ring
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, prod3, cv]
    have e1 := BRow.col_cb cur 3 (by norm_num)
    have e2 := BRow.col_cb cur 4 (by norm_num)
    have e3 := BRow.col_cb cur 5 (by norm_num)
    simp only [BRow.col_cB, e1, e2, e3]
    rw [f4]; ring
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, cv, BRow.col_cA, BRow.col_cB]
    exact f5
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, prod3, hzV, sumC, CoeffExpr.eval_sumList, cv,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, BRow.col_fst, BRow.col_mS, BRow.col_mV,
      BRow.col_mW, BRow.col_cn]
    exact f6
  · simp only [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, prod3, hzV, sumC, CoeffExpr.eval_sumList, cv,
      nv, notE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, BRow.col_eos, BRow.col_mS,
      BRow.col_mV, BRow.col_mW, BRow.col_cn]
    exact f7

end Test
end Gates

/-! ## QPART -/
section QStruct
variable {Q : Type} [CommRing Q]

theorem laneHL_idx (y : Q) (cl : CallL) (p : ℕ) :
    laneHL y cl p = (idxOf (slotsOf p cl)).map
      (fun a => (slotH y a.1 a.2, slotHO y a.1 a.2, if a.2 = 0 then slotL y a.1 else 0)) := by
  unfold laneHL idxOf
  rw [List.map_flatMap]
  refine List.flatMap_congr (fun s _ => ?_)
  simp [List.map_map, Function.comp_def]

theorem laneD_idx (y : Q) (cl : CallL) (p : ℕ) :
    laneD p y cl = (idxOf (slotsOf p cl)).map
      (fun a => if a.2 = 0 then AluHonestRows.slotD p y cl a.1 else (0, 0)) := by
  unfold laneD idxOf
  rw [List.map_flatMap]
  refine List.flatMap_congr (fun s _ => ?_)
  simp [List.map_map, Function.comp_def]

theorem runSums_length' (acc : Q × Q) (ds : List (Q × Q)) : (runSums acc ds).length = ds.length := by
  induction ds generalizing acc with
  | nil => simp [runSums]
  | cons d ds ih => simp [runSums, ih]

theorem runSums_zero (acc : Q × Q) (d : Q × Q) (ds : List (Q × Q)) :
    (runSums acc (d :: ds)).getD 0 (0, 0) = (acc.1 + d.1, acc.2 + d.2) := rfl

theorem runSums_succ : ∀ (ds : List (Q × Q)) (acc : Q × Q) (k : ℕ), k + 1 < ds.length →
    (runSums acc ds).getD (k + 1) (0, 0) =
      (((runSums acc ds).getD k (0, 0)).1 + (ds.getD (k + 1) (0, 0)).1,
       ((runSums acc ds).getD k (0, 0)).2 + (ds.getD (k + 1) (0, 0)).2)
  | [], _, _, h => by simp at h
  | [d], _, k, h => by simp at h
  | d :: e :: ds, acc, 0, _ => by
    simp [runSums]
  | d :: e :: ds, acc, k + 1, h => by
    have ih := runSums_succ (e :: ds) (acc.1 + d.1, acc.2 + d.2) k (by simpa using h)
    simp only [runSums, List.getD_cons_succ] at ih ⊢
    exact ih

/-- The block's `𝕂′` lane row `k + 1`: the alignment with the row index. -/
theorem blockQ_lane (p : ℕ) (y : Q) (cl : CallL) (k : ℕ) (a : SlotL × ℕ)
    (ha : (idxOf (slotsOf p cl))[k]? = some a) :
    (blockQ p y cl).getD (k + 1) QRow.zero =
      ⟨slotH y a.1 a.2, slotHO y a.1 a.2, (if a.2 = 0 then slotL y a.1 else 0),
        ((laneD p y cl).getD k (0, 0)).1, ((laneD p y cl).getD k (0, 0)).2,
        ((runSums (hdrD (Q := Q) cl) (laneD p y cl)).getD k (0, 0)).1,
        ((runSums (hdrD (Q := Q) cl) (laneD p y cl)).getD k (0, 0)).2,
        (latchOf p y cl).1, (latchOf p y cl).2⟩ := by
  have hk : k < (idxOf (slotsOf p cl)).length := (List.getElem?_eq_some_iff.mp ha).1
  have hHL : (laneHL y cl p).length = (idxOf (slotsOf p cl)).length := by rw [laneHL_idx]; simp
  have hD : (laneD p y cl).length = (idxOf (slotsOf p cl)).length := by rw [laneD_idx]; simp
  have hSS : (runSums (hdrD (Q := Q) cl) (laneD p y cl)).length = (idxOf (slotsOf p cl)).length := by
    rw [runSums_length', hD]
  have hlt : k < (List.map (fun x => (⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2,
      (latchOf p y cl).1, (latchOf p y cl).2⟩ : QRow Q))
      ((laneHL y cl p).zip ((laneD p y cl).zip (runSums (hdrD (Q := Q) cl) (laneD p y cl))))).length := by
    simp [List.length_zip, hHL, hD, hSS]; omega
  simp only [blockQ]
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_zip, List.getElem_zip]
  have e1 : (laneHL y cl p)[k]'(by omega) = (slotH y a.1 a.2, slotHO y a.1 a.2, if a.2 = 0 then slotL y a.1 else 0) := by
    have : (laneHL y cl p)[k]? = some (slotH y a.1 a.2, slotHO y a.1 a.2, if a.2 = 0 then slotL y a.1 else 0) := by
      rw [laneHL_idx, List.getElem?_map, ha]; rfl
    exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans this)
  have e2 : (laneD p y cl)[k]'(by omega) = (laneD p y cl).getD k (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
  have e3 : (runSums (hdrD (Q := Q) cl) (laneD p y cl))[k]'(by omega) =
      (runSums (hdrD (Q := Q) cl) (laneD p y cl)).getD k (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
  dsimp only
  rw [e1, e2, e3]


/-- The `𝕂′` lane row of lane index `k` with index entry `a`. -/
def laneQ (p : ℕ) (y : Q) (cl : CallL) (k : ℕ) (a : SlotL × ℕ) : QRow Q :=
  ⟨slotH y a.1 a.2, slotHO y a.1 a.2, (if a.2 = 0 then slotL y a.1 else 0),
        ((laneD p y cl).getD k (0, 0)).1, ((laneD p y cl).getD k (0, 0)).2,
        ((runSums (hdrD (Q := Q) cl) (laneD p y cl)).getD k (0, 0)).1,
        ((runSums (hdrD (Q := Q) cl) (laneD p y cl)).getD k (0, 0)).2,
        (latchOf p y cl).1, (latchOf p y cl).2⟩

/-- The hdr `𝕂′` row. -/
def hdrQ (p : ℕ) (y : Q) (cl : CallL) : QRow Q :=
  ⟨0, 0, 0, (hdrD (Q := Q) cl).1, (hdrD (Q := Q) cl).2, (hdrD (Q := Q) cl).1, (hdrD (Q := Q) cl).2,
    (latchOf p y cl).1, (latchOf p y cl).2⟩

theorem blockQ_lane' (p : ℕ) (y : Q) (cl : CallL) (k : ℕ) (a : SlotL × ℕ)
    (ha : (idxOf (slotsOf p cl))[k]? = some a) : (blockQ p y cl).getD (k + 1) QRow.zero = laneQ p y cl k a :=
  blockQ_lane p y cl k a ha

theorem blockQ_zero (p : ℕ) (y : Q) (cl : CallL) : (blockQ p y cl).getD 0 QRow.zero = hdrQ p y cl := rfl

theorem blockB_len {F : Type} [Field F] (p : ℕ) (cl : CallL) :
    (blockB (F := F) p cl).length = (idxOf (slotsOf p cl)).length + 1 := by
  rw [blockB_eq]; simp [rowsOf]

theorem blockB_zero {F : Type} [Field F] (p : ℕ) (cl : CallL) : (blockB (F := F) p cl).getD 0 BRow.zero = hdrRow cl := by
  rw [blockB_eq]; rfl

theorem blockB_lane {F : Type} [Field F] (p : ℕ) (cl : CallL) (k : ℕ) (a : SlotL × ℕ)
    (ha : (idxOf (slotsOf p cl))[k]? = some a) : (blockB (F := F) p cl).getD (k + 1) BRow.zero = slotRow p cl a.1 a.2 := by
  rw [blockB_eq]
  simp [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_map, ha]

/-- **The context of a block row**: the row index `j` is the hdr, or a lane row `k` of the index, with its successor
as the next lane row (same slot or the next slot's first row) or the block's end. -/
theorem qctx {p : ℕ} [Fact p.Prime] (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) (y : Q) (j : ℕ)
    (hj : j < (blockB (F := ZMod p) p cl).length) (nxt : BRow (ZMod p))
    (hn : NextOK (blockB p cl) j nxt) (nq : QRow Q)
    (hq : j + 1 < (blockB (F := ZMod p) p cl).length → nq = (blockQ p y cl).getD (j + 1) QRow.zero) :
    (j = 0 ∧ (blockB (F := ZMod p) p cl).getD j BRow.zero = hdrRow cl ∧
      (blockQ p y cl).getD j QRow.zero = hdrQ p y cl ∧
      ∃ b, (idxOf (slotsOf p cl))[0]? = some b ∧ b.2 = 0 ∧ b.1.role = some 0 ∧ b.1 ∈ slotsOf p cl ∧
        nxt = slotRow p cl b.1 b.2 ∧ nq = laneQ p y cl 0 b) ∨
    (∃ k a, j = k + 1 ∧ (idxOf (slotsOf p cl))[k]? = some a ∧ a.1 ∈ slotsOf p cl ∧ a.2 < a.1.words.length ∧
      (blockB (F := ZMod p) p cl).getD j BRow.zero = slotRow p cl a.1 a.2 ∧
      (blockQ p y cl).getD j QRow.zero = laneQ p y cl k a ∧
      ((∃ b, (idxOf (slotsOf p cl))[k + 1]? = some b ∧ nxt = slotRow p cl b.1 b.2 ∧ nq = laneQ p y cl (k + 1) b ∧
        ((b = (a.1, a.2 + 1) ∧ a.2 + 1 < a.1.words.length) ∨
         (a.2 + 1 = a.1.words.length ∧ b.2 = 0 ∧ b.1 ∈ slotsOf p cl))) ∨
       ((idxOf (slotsOf p cl))[k + 1]? = none ∧ a.2 + 1 = a.1.words.length ∧ nxt.sL = 0 ∧ nxt.fst = 0))) := by
  have hne : ∀ s ∈ slotsOf p cl, 0 < s.words.length := fun s hs => (slots_SG hpG hcl s hs).ne
  have hlen := blockB_len (F := ZMod p) p cl
  cases j with
  | zero =>
    left
    obtain ⟨s0, tl, hss, hr0⟩ := slots_head hcl
    have hs0 : s0 ∈ slotsOf p cl := by rw [hss]; exact List.mem_cons_self
    have hn0 : 0 < s0.words.length := hne s0 hs0
    have h0 : (idxOf (slotsOf p cl))[0]? = some (s0, 0) := by
      rw [hss, idxOf_cons]
      rw [List.getElem?_append_left (by simpa using hn0)]
      simp [hn0]
    have hlen0 : 0 < (idxOf (slotsOf p cl)).length := (List.getElem?_eq_some_iff.mp h0).1
    have hl1 : 0 + 1 < (blockB (F := ZMod p) p cl).length := by omega
    refine ⟨rfl, blockB_zero p cl, rfl, (s0, 0), h0, rfl, hr0, hs0, ?_, ?_⟩
    · rw [hn.1 hl1]; exact blockB_lane p cl 0 _ h0
    · rw [hq hl1]; exact blockQ_lane' p y cl 0 _ h0
  | succ k =>
    right
    have hk : k < (idxOf (slotsOf p cl)).length := by omega
    obtain ⟨a, ha⟩ : ∃ a, (idxOf (slotsOf p cl))[k]? = some a := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨⟨hmem, hlt⟩, -, hnone, hsome⟩ := idx_prop (slotsOf p cl) hne k a ha
    refine ⟨k, a, rfl, ha, hmem, hlt, blockB_lane p cl k a ha, blockQ_lane' p y cl k a ha, ?_⟩
    cases hb : (idxOf (slotsOf p cl))[k + 1]? with
    | none =>
      right
      have hl : (blockB (F := ZMod p) p cl).length ≤ k + 1 + 1 := by
        by_contra hcon
        have : k + 1 < (idxOf (slotsOf p cl)).length := by omega
        rw [List.getElem?_eq_getElem this] at hb
        simp at hb
      exact ⟨rfl, hnone hb, (hn.2 hl).1, (hn.2 hl).2⟩
    | some b =>
      left
      have hl : k + 1 + 1 < (blockB (F := ZMod p) p cl).length := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        omega
      refine ⟨b, rfl, ?_, ?_, hsome b hb⟩
      · rw [hn.1 hl]; exact blockB_lane p cl (k + 1) b hb
      · rw [hq hl]; exact blockQ_lane' p y cl (k + 1) b hb

end QStruct

section QEq
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 in
/-- placeholder to open -/
theorem qeq_dummy : True := trivial

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem kvec_pair (q : QRow (Quad (algebraMap (ZMod p) K δ))) (r : ℕ) (hr : r % 2 = 0) :
    Quad.mk (algebraMap (ZMod p) K δ) (kvec δ q r) (kvec δ q (r + 1)) = q.role r := by
  have h1 : r - r % 2 = r := by omega
  have h2 : (r + 1) - (r + 1) % 2 = r := by omega
  have h3 : (r + 1) % 2 ≠ 0 := by omega
  simp only [kvec, h1, h2, hr, h3, if_true, if_false]
  exact Quad.mk_re_im (algebraMap (ZMod p) K δ) (q.role r)

theorem rdv (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) (r : ℕ)
    (hr : r % 2 = 0) :
    (QE.var r : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.role r := by
  rw [ev_var]; exact kvec_pair δ qc r hr

theorem rdn (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) (r : ℕ)
    (hr : r % 2 = 0) :
    (QE.next r : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.role r := by
  rw [ev_next]; exact kvec_pair δ qn r hr

end QEq

section QEq2
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem rdvH (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.H : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.H :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.H])

theorem rdnH (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.H : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.H :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.H])

theorem rdvHO (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.HO : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.HO :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.HO])

theorem rdnHO (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.HO : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.HO :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.HO])

theorem rdvL (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.L : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.L :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.L])

theorem rdnL (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.L : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.L :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.L])

theorem rdvD1 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.D1 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.D1 :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.D1])

theorem rdnD1 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.D1 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.D1 :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.D1])

theorem rdvD2 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.D2 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.D2 :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.D2])

theorem rdnD2 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.D2 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.D2 :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.D2])

theorem rdvS1 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.S1 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.S1 :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.S1])

theorem rdnS1 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.S1 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.S1 :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.S1])

theorem rdvS2 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.S2 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.S2 :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.S2])

theorem rdnS2 (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.S2 : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.S2 :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.S2])

theorem rdvRL (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.RL : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.RL :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.RL])

theorem rdnRL (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.RL : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.RL :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.RL])

theorem rdvRO (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.var AluSZChipJ9.RO : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qc.RO :=
  (rdv δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.RO])

theorem rdnRO (qc qn : QRow (Quad (algebraMap (ZMod p) K δ))) (chal cc : ℕ → K) (eF : Env (ZMod p)) :
    (QE.next AluSZChipJ9.RO : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = qn.RO :=
  (rdn δ qc qn chal cc eF _ (by decide)).trans (by simp [QRow.role, AluSZChipJ9.RO])

theorem ev_yQ (y : Quad (algebraMap (ZMod p) K δ)) (chal : ℕ → K) {cc : ℕ → K} {qc qn : QRow (Quad (algebraMap (ZMod p) K δ))}
    {eF : Env (ZMod p)} (hy : Quad.mk _ (chal 2) (chal 3) = y) :
    (AluSZChipJ9.yQ : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ eF = y := by
  unfold AluSZChipJ9.yQ; rw [ev_chal]; exact hy

theorem liftQ_item (σ : ZMod p) (X : Quad (algebraMap (ZMod p) K δ)) (h : σ = 0 ∨ X = 0) :
    liftQ δ σ * X = 0 := by
  rcases h with h | h <;> simp [h, liftQ]

end QEq2

section QHorn
variable {Q : Type} [CommRing Q]

theorem horner_cons (y : Q) (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    hornerFrom y ws i = ((ws.getD i 0 : ℕ) : Q) + y * hornerFrom y ws (i + 1) := by
  unfold hornerFrom horner
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]
  simp only [zl, List.map_cons, evR]
  rw [show ((Int.ofNat ws[i] : ℤ) : Q) = ((ws[i] : ℕ) : Q) from Int.cast_natCast _]

end QHorn

section QHorn2
variable {Q : Type} [CommRing Q]

theorem slotH_horner (y : Q) (s : SlotL) (i : ℕ) (h4 : s.mode ≠ 4) (h0 : s.mode ≠ 0) :
    slotH y s i = hornerFrom y s.words i := by
  unfold slotH; simp [h4, h0]

theorem slotHO_horner (y : Q) (s : SlotL) (i : ℕ) (h4 : s.mode ≠ 4) (h0 : s.mode ≠ 0) :
    slotHO y s i = hornerFrom y (hiL s.words) i := by
  unfold slotHO; simp [h4, h0]

theorem hiL_getD (ws : List ℕ) (i : ℕ) : (hiL ws).getD i 0 = ws.getD i 0 / 2 ^ 16 := by
  simp only [hiL, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> simp

theorem hiL_length (ws : List ℕ) : (hiL ws).length = ws.length := by simp [hiL]

end QHorn2

section QBase
variable {F : Type} [Field F]

theorem hz_eval (cur nxt : BRow F) :
    (AluSZChipJ9.hz : CoeffExpr F).eval (envB cur.col nxt.col) = cur.mode 1 + (cur.mode 2 + (cur.mode 3 + cur.mode 5)) := by
  simp [AluSZChipJ9.hz, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, envB]

theorem hzV_eval (cur nxt : BRow F) :
    (AluSZChipJ9.hzV : CoeffExpr F).eval (envB cur.col nxt.col) = cur.mode 1 + (cur.mode 2 + cur.mode 3) := by
  simp [AluSZChipJ9.hzV, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, envB]

theorem modeSum_hz (m : ℕ) :
    (ind (1 = m) + (ind (2 = m) + (ind (3 = m) + ind (5 = m))) : F) = if (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 5) then 1 else 0 := by
  by_cases h : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 5
  · rw [if_pos h]; rcases h with rfl | rfl | rfl | rfl <;> simp [ind]
  · rw [if_neg h]
    have h1 : ¬ (1 = m) := fun e => h (Or.inl e.symm)
    have h2 : ¬ (2 = m) := fun e => h (Or.inr (Or.inl e.symm))
    have h3 : ¬ (3 = m) := fun e => h (Or.inr (Or.inr (Or.inl e.symm)))
    have h5 : ¬ (5 = m) := fun e => h (Or.inr (Or.inr (Or.inr e.symm)))
    simp [ind, h1, h2, h3, h5]

end QBase

section QHorn3
variable {Q : Type} [CommRing Q]

theorem hornerFrom_len (y : Q) (ws : List ℕ) : hornerFrom y ws ws.length = 0 := by
  simp [hornerFrom, horner, evR, zl]

end QHorn3

section QEq3
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem lE_slot (cl : CallL) (s : SlotL) (i : ℕ) (nxt : BRow (ZMod p)) (hw : s.words.getD i 0 < 2 ^ 32) :
    (AluSZChipJ9.lE : CoeffExpr (ZMod p)).eval (envB (slotRow p cl s i).col nxt.col) = ((s.words.getD i 0 : ℕ) : ZMod p) :=
  lane_eval_cur (slotRow p cl s i) nxt.col (fun _ => 0) (fun _ => 0) _ (fun t _ => rfl) hw

theorem oE_slot (cl : CallL) (s : SlotL) (i : ℕ) (nxt : BRow (ZMod p)) (hw : s.words.getD i 0 < 2 ^ 32) :
    (AluSZChipJ9.oE : CoeffExpr (ZMod p)).eval (envB (slotRow p cl s i).col nxt.col) =
      ((s.words.getD i 0 / 2 ^ 16 : ℕ) : ZMod p) := by
  unfold AluSZChipJ9.oE
  rw [eval_bitSum]
  show ∑ j ∈ Finset.range 16, (2 : ZMod p) ^ j * (slotRow p cl s i).col (AluSZChipJ9.bt0 + 16 + j) = _
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [add_assoc, BRow.col_bit _ (16 + j) (by have := Finset.mem_range.mp hj; omega)]
    exact rfl : ∀ j ∈ Finset.range 16, (2 : ZMod p) ^ j * (slotRow p cl s i).col (AluSZChipJ9.bt0 + 16 + j) =
      (2 : ZMod p) ^ j * ((bitOf (s.words.getD i 0) (16 + j) : ℕ) : ZMod p))]
  exact laneHi_F _ hw

theorem word_lt {cl : CallL} (hpG : p = Nock.Atoms.p) (hcl : CallOK p cl)
    (hQ : ∀ s ∈ slotsOf p cl, s.mode = 5 → ∀ w ∈ s.words, w < 2 ^ 32) {s : SlotL} (hs : s ∈ slotsOf p cl)
    (hm : s.mode ≠ 4) (i : ℕ) : s.words.getD i 0 < 2 ^ 32 := by
  have sg := slots_SG hpG hcl s hs
  by_cases hi : i < s.words.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases h5 : s.mode = 5
    · exact hQ s hs h5 _ (List.getElem_mem hi)
    · have : s.mode < 4 := by rcases sg.wf with ⟨r, hr, hrole, hmode⟩ | ⟨hrole, hmode⟩ <;> omega
      exact sg.wb this _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; norm_num

end QEq3

section QEq4
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- The lane-row reading shared by the equation proofs: the next `𝕂′` row of a non-last row of a slot. -/
theorem lane_nq {cl : CallL} {y : Quad (algebraMap (ZMod p) K δ)} {k : ℕ} {a : SlotL × ℕ} {nxt : BRow (ZMod p)}
    {nq : QRow (Quad (algebraMap (ZMod p) K δ))}
    (hnext : (∃ b, (idxOf (slotsOf p cl))[k + 1]? = some b ∧ nxt = slotRow p cl b.1 b.2 ∧ nq = laneQ p y cl (k + 1) b ∧
        ((b = (a.1, a.2 + 1) ∧ a.2 + 1 < a.1.words.length) ∨
         (a.2 + 1 = a.1.words.length ∧ b.2 = 0 ∧ b.1 ∈ slotsOf p cl))) ∨
       ((idxOf (slotsOf p cl))[k + 1]? = none ∧ a.2 + 1 = a.1.words.length ∧ nxt.sL = 0 ∧ nxt.fst = 0))
    (hne : a.2 + 1 ≠ a.1.words.length) : nq = laneQ p y cl (k + 1) (a.1, a.2 + 1) := by
  rcases hnext with ⟨b, -, -, hnq, (⟨hb, -⟩ | ⟨h, -⟩)⟩ | ⟨-, h, -⟩
  · rw [hnq, hb]
  · exact absurd h hne
  · exact absurd h hne

theorem qSat_hor (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    (hQ : ∀ s ∈ slotsOf p cl, s.mode = 5 → ∀ w ∈ s.words, w < 2 ^ 32) :
    QSat (K := K) δ p cl ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).take 4) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  simp only [AluSZChipJ9.identQ, List.take, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases qctx hpG hcl y j hj nxt hn nq hq with ⟨-, hcur, hqc, b, hb0, hb2, hbr, hbs, rfl, rfl⟩ |
    ⟨k, a, hjk, ha, hmem, hlt, hcur, hqc, hnext⟩
  · rw [hcur, hqc]
    rcases he with rfl | rfl | rfl | rfl <;>
    · simp only [AluSZChipJ9.qz, ev_scale]
      apply liftQ_item
      left
      simp [CoeffExpr.eval, hz_eval, envB, AluSZChipJ9.hz, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, cv]
  · rw [hcur, hqc]
    have sg := slots_SG hpG hcl a.1 hmem
    have hzev : (AluSZChipJ9.hz : CoeffExpr (ZMod p)).eval (envB (slotRow p cl a.1 a.2).col nxt.col) =
        if (a.1.mode = 1 ∨ a.1.mode = 2 ∨ a.1.mode = 3 ∨ a.1.mode = 5) then 1 else 0 := by
      rw [hz_eval]; simp only [slotRow_mode]; exact modeSum_hz _
    have hev : (envB (slotRow p cl a.1 a.2).col nxt.col).trace AluSZChipJ9.eos =
        ind (a.2 + 1 = a.1.words.length) := by
      show (slotRow p cl a.1 a.2).col AluSZChipJ9.eos = _
      rw [BRow.col_eos, slotRow_eos]
    have hσ0 : (AluSZChipJ9.hz.mul (notE (cv AluSZChipJ9.eos)) : CoeffExpr (ZMod p)).eval
        (envB (slotRow p cl a.1 a.2).col nxt.col) =
        (if (a.1.mode = 1 ∨ a.1.mode = 2 ∨ a.1.mode = 3 ∨ a.1.mode = 5) then 1 else 0) * (1 - ind (a.2 + 1 = a.1.words.length)) := by
      simp only [CoeffExpr.eval, notE, hzev, hev]
    have hσ1 : (AluSZChipJ9.hz.mul (cv AluSZChipJ9.eos) : CoeffExpr (ZMod p)).eval
        (envB (slotRow p cl a.1 a.2).col nxt.col) =
        (if (a.1.mode = 1 ∨ a.1.mode = 2 ∨ a.1.mode = 3 ∨ a.1.mode = 5) then 1 else 0) * ind (a.2 + 1 = a.1.words.length) := by
      simp only [CoeffExpr.eval, hzev, hev]
    by_cases hzm : a.1.mode = 1 ∨ a.1.mode = 2 ∨ a.1.mode = 3 ∨ a.1.mode = 5
    · have hm4 : a.1.mode ≠ 4 := by omega
      have hm0 : a.1.mode ≠ 0 := by omega
      have hww := word_lt hpG hcl hQ hmem hm4 a.2
      have hHc : slotH y a.1 a.2 = hornerFrom y a.1.words a.2 := slotH_horner _ _ _ hm4 hm0
      have hOc : slotHO y a.1 a.2 = hornerFrom y (hiL a.1.words) a.2 := slotHO_horner _ _ _ hm4 hm0
      by_cases heos : a.2 + 1 = a.1.words.length
      · rcases he with rfl | rfl | rfl | rfl
        · simp only [AluSZChipJ9.qz, ev_scale, hσ0, if_pos hzm, ind_true _ heos]
          apply liftQ_item; left; simp
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_base, rdvH, hσ1, if_pos hzm, ind_true _ heos, lE_slot cl _ _ _ hww]
          apply liftQ_item; right
          dsimp only [laneQ]
          rw [hHc, horner_cons y _ _ hlt, heos, hornerFrom_len]
          simp [liftQ]
        · simp only [AluSZChipJ9.qz, ev_scale, hσ0, if_pos hzm, ind_true _ heos]
          apply liftQ_item; left; simp
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_base, rdvHO, hσ1, if_pos hzm, ind_true _ heos, oE_slot cl _ _ _ hww]
          apply liftQ_item; right
          dsimp only [laneQ]
          rw [hOc, horner_cons y _ _ (by rw [hiL_length]; exact hlt), hiL_getD, show a.2 + 1 = (hiL a.1.words).length by
            rw [hiL_length]; exact heos, hornerFrom_len]
          simp [liftQ]
      · have hnq := lane_nq δ hnext heos
        rcases he with rfl | rfl | rfl | rfl
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, rdvH, rdnH, ev_yQ δ y chal hy, hσ0, if_pos hzm,
            ind_false _ heos, lE_slot cl _ _ _ hww]
          apply liftQ_item; right
          rw [hnq]
          dsimp only [laneQ]
          rw [hHc, slotH_horner _ _ _ hm4 hm0, horner_cons y _ _ hlt]
          simp [liftQ]
        · simp only [AluSZChipJ9.qz, ev_scale, hσ1, if_pos hzm, ind_false _ heos]
          apply liftQ_item; left; simp
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, rdvHO, rdnHO, ev_yQ δ y chal hy, hσ0, if_pos hzm,
            ind_false _ heos, oE_slot cl _ _ _ hww]
          apply liftQ_item; right
          rw [hnq]
          dsimp only [laneQ]
          rw [hOc, slotHO_horner _ _ _ hm4 hm0, horner_cons y _ _ (by rw [hiL_length]; exact hlt), hiL_getD]
          simp [liftQ]
        · simp only [AluSZChipJ9.qz, ev_scale, hσ1, if_pos hzm, ind_false _ heos]
          apply liftQ_item; left; simp
    · rcases he with rfl | rfl | rfl | rfl <;>
      · simp only [AluSZChipJ9.qz, ev_scale, hσ0, hσ1, if_neg hzm]
        apply liftQ_item; left; simp
end QEq4

section QLatch

theorem isF1_op {o : PrimOp} {s : SlotL} (h : isF1 o s = true) : o = .mul ∨ o = .div ∨ o = .mod := by
  revert h; unfold isF1; cases o <;> simp

theorem isF1_unique {p : ℕ} (cl : CallL) :
    ∀ s ∈ slotsOf p cl, ∀ s' ∈ slotsOf p cl, isF1 cl.op s = true → isF1 cl.op s' = true → s = s' := by
  intro s hs s' hs' h h'
  rcases isF1_op h with hop | hop | hop
  · unfold slotsOf at hs hs'
    dsimp only at hs hs'
    simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at hs hs' h h'
    rcases hs with rfl | rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl | rfl <;>
      simp [isF1, handleSlot_role, qSlot] at h h' ⊢
  · unfold slotsOf at hs hs'
    dsimp only at hs hs'
    simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at hs hs' h h'
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [isF1, handleSlot_role, witSlot, qSlot] at h h' ⊢
  · unfold slotsOf at hs hs'
    dsimp only at hs hs'
    simp only [hop, List.mem_cons, List.not_mem_nil, or_false] at hs hs' h h'
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [isF1, handleSlot_role, witSlot, qSlot] at h h' ⊢

theorem latch_eq {Q : Type} [CommRing Q] (p : ℕ) (y : Q) (cl : CallL) {s : SlotL} (hs : s ∈ slotsOf p cl)
    (h : isF1 cl.op s = true) : latchOf p y cl = (slotL y s, slotHO y s 0) := by
  unfold latchOf
  cases hf : (slotsOf p cl).find? (fun s => isF1 cl.op s) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd h (hf s hs)
  | some s0 =>
    have h0 := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    have := isF1_unique cl s0 hm s hs h0 h
    subst this
    rfl

end QLatch

section QRest
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem liftQ_nat (n : ℕ) : liftQ δ ((n : ℕ) : ZMod p) = (n : Quad (algebraMap (ZMod p) K δ)) := by
  simp [liftQ]

theorem laneD_len (p : ℕ) {Q : Type} [CommRing Q] (y : Q) (cl : CallL) : (laneD p y cl).length = (idxOf (slotsOf p cl)).length := by
  rw [laneD_idx]; simp

theorem laneD_getD {Q : Type} [CommRing Q] (p : ℕ) (y : Q) (cl : CallL) (k : ℕ) (a : SlotL × ℕ)
    (ha : (idxOf (slotsOf p cl))[k]? = some a) :
    (laneD p y cl).getD k (0, 0) = if a.2 = 0 then AluHonestRows.slotD p y cl a.1 else (0, 0) := by
  rw [laneD_idx, List.getD_eq_getElem?_getD, List.getElem?_map, ha]
  rfl

theorem runSums_zero' {Q : Type} [CommRing Q] (acc : Q × Q) (ds : List (Q × Q)) (h : 0 < ds.length) :
    (runSums acc ds).getD 0 (0, 0) = (acc.1 + (ds.getD 0 (0, 0)).1, acc.2 + (ds.getD 0 (0, 0)).2) := by
  cases ds with
  | nil => simp at h
  | cons d ds => rfl

theorem qSat_rest (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    QSat (K := K) δ p cl (((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 8).take 15) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  simp only [AluSZChipJ9.identQ, List.drop, List.take, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases qctx hpG hcl y j hj nxt hn nq hq with ⟨-, hcur, hqc, b, hb0, hb2, hbr, hbs, rfl, rfl⟩ |
    ⟨k, a, hjk, ha, hmem, hlt, hcur, hqc, hnext⟩
  · rw [hcur, hqc]
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, AluSZChipJ9.yMB, ev_yQ δ y chal hy, rdvH,
        rdvHO, rdvL, rdvD1, rdvD2, rdvS1, rdvS2, rdvRL, rdvRO, rdnH, rdnHO, rdnL, rdnD1, rdnD2, rdnS1, rdnS2, rdnRL, rdnRO]
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 8
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 9
    · exact liftQ_item δ _ _ (Or.inr (by simp [laneQ, hdrQ]))                -- 10
    · exact liftQ_item δ _ _ (Or.inr (by simp [laneQ, hdrQ]))                -- 11
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 12
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, notE, envB]))   -- 13
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 14
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, notE, envB]))   -- 15
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, notE, envB]))   -- 16
    · refine liftQ_item δ _ _ (Or.inr ?_)   -- 17
      simp [hdrQ, hdrD, CoeffExpr.eval, cv, notE, envB, liftQ, ix2, ind]
      by_cases ho : cl.op = PrimOp.lt <;> simp [ho]
    · refine liftQ_item δ _ _ (Or.inr ?_)   -- 18
      simp [hdrQ, hdrD, CoeffExpr.eval, cv, envB, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, liftQ, ix4, ix5, ind]
      by_cases h1 : cl.op = PrimOp.div <;> by_cases h2 : cl.op = PrimOp.mod <;> simp [h1, h2]
    · exact liftQ_item δ _ _ (Or.inr (by simp [hdrQ]))   -- 19
    · exact liftQ_item δ _ _ (Or.inr (by simp [hdrQ]))   -- 20
    · have hlen : 0 < (laneD p y cl).length := by rw [laneD_len]; exact (List.getElem?_eq_some_iff.mp hb0).1
      refine liftQ_item δ _ _ (Or.inr ?_)   -- 21
      simp only [laneQ, hdrQ]
      rw [runSums_zero' _ _ hlen]
      ring
    · have hlen : 0 < (laneD p y cl).length := by rw [laneD_len]; exact (List.getElem?_eq_some_iff.mp hb0).1
      refine liftQ_item δ _ _ (Or.inr ?_)   -- 22
      simp only [laneQ, hdrQ]
      rw [runSums_zero' _ _ hlen]
      ring
  · rw [hcur, hqc]
    have sg := slots_SG hpG hcl a.1 hmem
    have hnext' := hnext
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, AluSZChipJ9.yMB, ev_yQ δ y chal hy, rdvH,
        rdvHO, rdvL, rdvD1, rdvD2, rdvS1, rdvS2, rdvRL, rdvRO, rdnH, rdnHO, rdnL, rdnD1, rdnD2, rdnS1, rdnS2, rdnRL, rdnRO]
    · -- 8
      by_cases h : a.2 = 0 ∧ isF1 cl.op a.1 = true
      · refine liftQ_item δ _ _ (Or.inr ?_)
        simp only [laneQ, if_pos h.1, latch_eq p y cl hmem h.2]
        simp
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h]
    · -- 9
      by_cases h : a.2 = 0 ∧ isF1 cl.op a.1 = true
      · refine liftQ_item δ _ _ (Or.inr ?_)
        simp only [laneQ, h.1, latch_eq p y cl hmem h.2]
        simp
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h]
    · -- 10
      rcases hnext' with ⟨b, -, -, hnq, -⟩ | ⟨-, -, hsL, -⟩
      · refine liftQ_item δ _ _ (Or.inr ?_)
        rw [hnq]; simp [laneQ]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, nv, envB, hsL]
    · -- 11
      rcases hnext' with ⟨b, -, -, hnq, -⟩ | ⟨-, -, hsL, -⟩
      · refine liftQ_item δ _ _ (Or.inr ?_)
        rw [hnq]; simp [laneQ]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, nv, envB, hsL]
    · -- 12
      by_cases h : a.2 = 0 ∧ isF2 cl.op a.1 = true
      · refine liftQ_item δ _ _ (Or.inr ?_)
        have hBf : liftQ δ (AluSZChipJ9.Bf : ZMod p) = ((Bn : ℕ) : Quad (algebraMap (ZMod p) K δ)) := by
          have h0 : (AluSZChipJ9.Bf : ZMod p) = ((Bn : ℕ) : ZMod p) := by norm_num [AluSZChipJ9.Bf, Bn]
          rw [h0, liftQ_nat]
        simp only [laneQ, laneD_getD p y cl k a ha, if_pos h.1, CoeffExpr.eval]
        simp only [AluHonestRows.slotD, if_pos h.2, hBf, h.1]
        simp
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h]
    · -- 13
      by_cases h0 : a.2 = 0
      · by_cases h2 : isF2 cl.op a.1 = true
        · refine liftQ_item δ _ _ (Or.inl ?_)
          simp [CoeffExpr.eval, cv, notE, envB, ind, h0, h2]
        · refine liftQ_item δ _ _ (Or.inr ?_)
          simp only [laneQ, laneD_getD p y cl k a ha, if_pos h0, AluHonestRows.slotD, if_neg h2]
          simp [CoeffExpr.eval, cv, envB, h0, liftQ]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, notE, envB, ind, h0]
    · -- 14
      by_cases h0 : a.2 = 0
      · refine liftQ_item δ _ _ (Or.inr ?_)
        simp only [laneQ, laneD_getD p y cl k a ha, if_pos h0, AluHonestRows.slotD]
        split_ifs <;> simp [CoeffExpr.eval, cv, envB, h0, liftQ]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h0]
    · -- 15
      by_cases h0 : a.2 = 0
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, notE, envB, ind, h0]
      · refine liftQ_item δ _ _ (Or.inr ?_)
        simp only [laneQ, laneD_getD p y cl k a ha, if_neg h0]
        try rfl
    · -- 16
      by_cases h0 : a.2 = 0
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, notE, envB, ind, h0]
      · refine liftQ_item δ _ _ (Or.inr ?_)
        simp only [laneQ, laneD_getD p y cl k a ha, if_neg h0]
        try rfl
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 17
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 18
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 19
    · exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))   -- 20
    · -- 21
      rcases hnext' with ⟨b, hb, -, hnq, -⟩ | ⟨-, -, hsL, -⟩
      · have hlen : k + 1 < (laneD p y cl).length := by rw [laneD_len]; exact (List.getElem?_eq_some_iff.mp hb).1
        have hs := congrArg Prod.fst (runSums_succ (laneD p y cl) (hdrD (Q := Quad (algebraMap (ZMod p) K δ)) cl) k hlen)
        refine liftQ_item δ _ _ (Or.inr ?_)
        rw [hnq]
        simp only [laneQ]
        rw [hs]; ring
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, nv, envB, hsL]
    · -- 22
      rcases hnext' with ⟨b, hb, -, hnq, -⟩ | ⟨-, -, hsL, -⟩
      · have hlen : k + 1 < (laneD p y cl).length := by rw [laneD_len]; exact (List.getElem?_eq_some_iff.mp hb).1
        have hs := congrArg Prod.snd (runSums_succ (laneD p y cl) (hdrD (Q := Quad (algebraMap (ZMod p) K δ)) cl) k hlen)
        refine liftQ_item δ _ _ (Or.inr ?_)
        rw [hnq]
        simp only [laneQ]
        rw [hs]; ring
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, nv, envB, hsL]
end QRest

section QL
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem liftQ_Bf : liftQ δ (AluSZChipJ9.Bf : ZMod p) = ((Bn : ℕ) : Quad (algebraMap (ZMod p) K δ)) := by
  have h0 : (AluSZChipJ9.Bf : ZMod p) = ((Bn : ℕ) : ZMod p) := by norm_num [AluSZChipJ9.Bf, Bn]
  rw [h0, liftQ_nat]

theorem qSat_L (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    QSat (K := K) δ p cl (((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 6).take 2) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  simp only [AluSZChipJ9.identQ, List.drop, List.take, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases qctx hpG hcl y j hj nxt hn nq hq with ⟨-, hcur, hqc, b, hb0, hb2, hbr, hbs, rfl, rfl⟩ |
    ⟨k, a, hjk, ha, hmem, hlt, hcur, hqc, hnext⟩
  · rw [hcur, hqc]
    rcases he with rfl | rfl
    all_goals simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, AluSZChipJ9.yMB, ev_yQ δ y chal hy,
      rdvH, rdvL]
    all_goals exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, envB]))
  · rw [hcur, hqc]
    have sg := slots_SG hpG hcl a.1 hmem
    rcases he with rfl | rfl
    all_goals simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, ev_base, AluSZChipJ9.yMB, ev_yQ δ y chal hy,
      rdvH, rdvL]
    · -- 6
      by_cases h0 : a.2 = 0
      · by_cases hm : a.1.mode = 1 ∨ a.1.mode = 2 ∨ a.1.mode = 3
        · refine liftQ_item δ _ _ (Or.inr ?_)
          have hm4 : a.1.mode ≠ 4 := by omega
          have hm5 : a.1.mode ≠ 5 := by omega
          have hm0 : a.1.mode ≠ 0 := by omega
          simp only [laneQ, if_pos h0]
          rw [slotH_horner y _ _ hm4 hm0, h0, slotL, if_neg (by omega), sg.vw hm]
          simp [hornerFrom, horner]
        · refine liftQ_item δ _ _ (Or.inl ?_)
          have := hzV_eval (F := ZMod p) (slotRow p cl a.1 a.2) nxt
          simp only [CoeffExpr.eval, cv, envB, BRow.col_fst]
          show (slotRow p cl a.1 a.2).fst * (AluSZChipJ9.hzV : CoeffExpr (ZMod p)).eval (envB (slotRow p cl a.1 a.2).col nxt.col) = 0
          rw [this]; simp only [slotRow_mode, modeSum_hv, if_neg hm, mul_zero]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h0]
    · -- 7
      by_cases h0 : a.2 = 0
      · by_cases hm : a.1.mode = 4 ∨ a.1.mode = 5
        · refine liftQ_item δ _ _ (Or.inr ?_)
          simp only [laneQ, if_pos h0, CoeffExpr.eval, liftQ_Bf, h0]
          rw [slotL, if_pos hm]
          try simp only [if_true]
          ring
        · refine liftQ_item δ _ _ (Or.inl ?_)
          have hwf : a.1.mode < 4 ∨ a.1.mode = 4 ∨ a.1.mode = 5 := by
            rcases sg.wf with ⟨r, hr, hrole, hmode⟩ | ⟨hrole, hmode⟩ <;> omega
          have h45 := modeSum45 (F := ZMod p) a.1.mode hwf
          simp only [CoeffExpr.eval, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, cv, envB, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero, BRow.col_fst, BRow.col_mQ1, BRow.col_mQM, slotRow_mode, slotRow_fst]
          have hlt4 : a.1.mode < 4 := by omega
          have n4 : ¬ (4 = a.1.mode) := by omega
          have n5 : ¬ (5 = a.1.mode) := by omega
          simp [ind, h0, n4, n5]
      · refine liftQ_item δ _ _ (Or.inl ?_)
        simp [CoeffExpr.eval, cv, envB, ind, h0]
end QL

section QPack
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

theorem ev_sumQ (eK : Env K) (eF : Env (ZMod p)) (l : List (QE (ZMod p))) :
    (AluSZChipJ9.sumQ l).ev δ eK eF = (l.map fun x => x.ev δ eK eF).sum := by
  induction l with
  | nil => simp [AluSZChipJ9.sumQ, ev_zero]
  | cons a t ih =>
    simp only [AluSZChipJ9.sumQ, List.foldr_cons, ev_add] at ih ⊢
    rw [ih]; simp

theorem packE_ev (y : Quad (algebraMap (ZMod p) K δ)) (chal cc : ℕ → K) (qc qn : QRow (Quad (algebraMap (ZMod p) K δ)))
    (hp : ∀ t ≤ 32, Quad.mk (algebraMap (ZMod p) K δ) (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t)
    (cur nxt : BRow (ZMod p)) (w : ℕ) (hr : ∀ t < 32, cur.bit t = ((bitOf w t : ℕ) : ZMod p)) :
    (AluSZChipJ9.packE : QE (ZMod p)).ev δ ⟨kvec δ qc, kvec δ qn, chal, cc⟩ (envB cur.col nxt.col) = packV y w := by
  unfold AluSZChipJ9.packE packV
  rw [ev_sumQ, List.map_map]
  congr 1
  refine List.map_congr_left (fun t ht => ?_)
  have ht' : t < 32 := List.mem_range.mp ht
  simp only [Function.comp, ev_scale, AluSZChipJ9.ypow, ev_chal]
  rw [hp t (by omega)]
  show liftQ δ ((cv (AluSZChipJ9.bt0 + t)).eval (envB cur.col nxt.col)) * y ^ t = _
  simp only [CoeffExpr.eval, cv, envB]
  show liftQ δ (cur.col (AluSZChipJ9.bt0 + t)) * y ^ t = _
  rw [BRow.col_bit cur t ht', hr t ht', liftQ_nat]

theorem hornerQ1_step {Q : Type} [CommRing Q] (y : Q) (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    hornerQ1 y (ws.drop i) = packV y (ws.getD i 0) + y ^ 32 * hornerQ1 y (ws.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]
  rfl

theorem qSat_Q1 (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    QSat (K := K) δ p cl (((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 4).take 2) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  simp only [AluSZChipJ9.identQ, List.drop, List.take, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases qctx hpG hcl y j hj nxt hn nq hq with ⟨-, hcur, hqc, b, hb0, hb2, hbr, hbs, rfl, rfl⟩ |
    ⟨k, a, hjk, ha, hmem, hlt, hcur, hqc, hnext⟩
  · rw [hcur, hqc]
    rcases he with rfl | rfl
    all_goals simp only [AluSZChipJ9.qz, ev_scale]
    all_goals exact liftQ_item δ _ _ (Or.inl (by simp [CoeffExpr.eval, cv, notE, envB]))
  · rw [hcur, hqc]
    have sg := slots_SG hpG hcl a.1 hmem
    have hev : (envB (slotRow p cl a.1 a.2).col nxt.col).trace AluSZChipJ9.eos =
        ind (a.2 + 1 = a.1.words.length) := by
      show (slotRow p cl a.1 a.2).col AluSZChipJ9.eos = _
      rw [BRow.col_eos, slotRow_eos]
    have hmo : (envB (slotRow p cl a.1 a.2).col nxt.col).trace AluSZChipJ9.mQ1 = ind (4 = a.1.mode) := by
      show (slotRow p cl a.1 a.2).col AluSZChipJ9.mQ1 = _
      rw [BRow.col_mQ1, slotRow_mode]
    have hpk := packE_ev δ y chal (fun _ => 0) (laneQ p y cl k a) nq hp (slotRow p cl a.1 a.2) nxt (a.1.words.getD a.2 0)
      (fun t _ => rfl)
    by_cases hm : a.1.mode = 4
    · have hm0 : a.1.mode ≠ 0 := by omega
      have hHc : slotH y a.1 a.2 = hornerQ1 y (a.1.words.drop a.2) := by unfold slotH; simp [hm]
      by_cases heos : a.2 + 1 = a.1.words.length
      · rcases he with rfl | rfl
        · simp only [AluSZChipJ9.qz, ev_scale, CoeffExpr.eval, notE, hev, hmo, ind_true _ heos]
          exact liftQ_item δ _ _ (Or.inl (by simp))
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, CoeffExpr.eval, hev, hmo, ind_true _ heos, rdvH, hpk]
          refine liftQ_item δ _ _ (Or.inr ?_)
          dsimp only [laneQ]
          rw [hHc, hornerQ1_step y _ _ hlt, show a.2 + 1 = a.1.words.length from heos, List.drop_length]
          simp [hornerQ1]
      · have hnq := lane_nq δ hnext heos
        rcases he with rfl | rfl
        · simp only [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_mul, rdvH, rdnH, hpk, AluSZChipJ9.ypow, ev_chal,
            CoeffExpr.eval, notE, hev, hmo, ind_false _ heos]
          refine liftQ_item δ _ _ (Or.inr ?_)
          rw [hp 32 (by norm_num), hnq]
          dsimp only [laneQ]
          rw [hHc, slotH, if_pos hm, hornerQ1_step y _ _ hlt]
          ring
        · simp only [AluSZChipJ9.qz, ev_scale, CoeffExpr.eval, hev, hmo, ind_false _ heos]
          exact liftQ_item δ _ _ (Or.inl (by simp))
    · have n4 : ¬ (4 = a.1.mode) := fun h => hm h.symm
      rcases he with rfl | rfl
      all_goals simp only [AluSZChipJ9.qz, ev_scale, CoeffExpr.eval, notE, hev, hmo, ind_false _ n4]
      all_goals exact liftQ_item δ _ _ (Or.inl (by simp))
end QPack

section QCommon
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- **`QSat` of the op-independent `𝕂′` recurrence equations** of `identQ` (equations `0 … 22`: Horner `H`/`HO`,
packed `H`, `L`, latch `RL`/`RO`, `D1`/`D2`, `S1`/`S2` running sums; NOT the terminal `S1 = S2 = 0`, equations
`23`, `24`).  The one hypothesis beyond `CallOK`: `hQ`, the 32-bit bound on the words of every `mQM` slot (a `mul` /
`div` / `mod` fact; vacuous for `add` / `sub` / `lt`, which have no `mQM` slot). -/
theorem qSat_common (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl)
    (hQ : ∀ s ∈ slotsOf p cl, s.mode = 5 → ∀ w ∈ s.words, w < 2 ^ 32) :
    QSat (K := K) δ p cl ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).take 23) := by
  have e : ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).take 23) =
      ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).take 4 ++
        ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 4).take 2) ++
      (((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 6).take 2 ++
        ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 8).take 15) := rfl
  rw [e, qSat_append, qSat_append, qSat_append]
  exact ⟨⟨qSat_hor δ hpG hcl hQ, qSat_Q1 δ hpG hcl⟩, qSat_L δ hpG hcl, qSat_rest δ hpG hcl⟩

end QCommon

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatCommon
