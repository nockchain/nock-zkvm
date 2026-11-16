/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatA.lean

  **Honest gate satisfaction of the ALU for `add`, `sub`,
  `lt`.** The chip and the interface (`AluHonestRows`, `CarrySZ`) are untouched.

  For `op ∈ {add, sub, lt}` and `CallOK p cl`:
  * `groupSat_gSeq_A`   : `GroupSat gSeq`;
  * `groupSat_gCoef_A`  : `GroupSat gCoef`;
  * `groupSat_gBitsQM_A`: the 25-bit part of `gBits` (`gBits = gBitsB ++ gBitsQM`, `gBits_split`);
  * `qSat_term_A`       : `QSat` of the two terminal equations `(1 − next.sL)·S1 = 0`, `(1 − next.sL)·S2 = 0`
                          (`termQ`, a sub-list of `identQ`, `termQ_sub`), via `carry_id` + position-aware bounds.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatA

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. A position-aware carry bound (head coefficient may be one larger) -/

/-- **`carr_bound_head`**: the carries from `0` lie in `[0, M]` when the HEAD coefficient satisfies the relaxed
`d₀ < B·(M+1)` (the incoming carry is `0`, not `M`; the lt yes-case `+[1−lb]` at `k = 0`) and the tail satisfies the
uniform `carr_bound` hypothesis. -/
theorem carr_bound_head {B M : ℤ} (hB : 0 < B) (hM : 0 ≤ M) (d0 : ℤ) (ds : List ℤ)
    (h : evB B (d0 :: ds) = 0) (h0 : -B < d0 ∧ d0 < B * (M + 1))
    (hd : ∀ d ∈ ds, -B < d ∧ d + M < B * (M + 1)) : ∀ q ∈ carr B 0 (d0 :: ds), 0 ≤ q ∧ q ≤ M := by
  have h' : (0 : ℤ) + evB B (d0 :: ds) = 0 := by simpa using h
  obtain ⟨hcd, hrest⟩ := carr_step hB.ne' h'
  have hq0 : 0 ≤ (0 + d0) / B := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : B * ((0 + d0) / B) ≤ B * (-1) := mul_le_mul_of_nonneg_left (by omega) hB.le
    linarith [h0.1]
  have hqM : (0 + d0) / B ≤ M := by
    by_contra hbig
    replace hbig := not_le.mp hbig
    have : B * (M + 1) ≤ B * ((0 + d0) / B) := mul_le_mul_of_nonneg_left (by omega) hB.le
    linarith [h0.2]
  intro q hq
  simp only [carr, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact ⟨hq0, hqM⟩
  · exact carr_bound hB ds _ hrest hq0 hqM hd q hq

/-- `addL X [e] = (X.headD 0 + e) :: X.tail`: the single-coefficient list lands on the head. -/
theorem addL_single (X : List ℤ) (e : ℤ) : addL X [e] = (X.headD 0 + e) :: X.tail := by
  cases X with
  | nil => simp [addL]
  | cons x xs => cases xs <;> simp [addL]

/-! ## 2. Limbs -/

/-- `Bn` is the atoms' `B`. -/
theorem Bn_eq : Bn = Nock.Atoms.B := rfl

theorem evB_zl' (B : ℕ) (l : List ℕ) : evB (B : ℤ) (zl l) = ((Nat.ofDigits B l : ℕ) : ℤ) := by
  induction l with
  | nil => simp [zl, evB]
  | cons a l ih =>
    simp only [zl, List.map_cons, evB, Nat.ofDigits_cons] at ih ⊢
    rw [Int.ofNat_eq_natCast, ih]
    push_cast
    rfl

theorem evB_zl (l : List ℕ) : evB (Bn : ℤ) (zl l) = (Nock.Atoms.val l : ℤ) := evB_zl' Bn l

theorem limbs_lt (v : ℕ) : ∀ a ∈ Nock.Atoms.limbs v, a < Bn := fun a ha =>
  Nat.digits_lt_base Nock.Atoms.one_lt_B ha

theorem splitOf_lt {p : ℕ} (hpG : p = Nock.Atoms.p) {v : ℕ} (hv : v < p) : ∀ a ∈ splitOf v, a < Bn := by
  intro a ha
  have hp : p ≤ Bn * Bn := by
    rw [hpG, Nock.Atoms.p_eq_limbs]
    have := Nock.Atoms.one_lt_B
    have h2 : Nock.Atoms.B * (Nock.Atoms.B - 1) + 1 ≤ Nock.Atoms.B * Nock.Atoms.B := by
      have : Nock.Atoms.B * (Nock.Atoms.B - 1) < Nock.Atoms.B * Nock.Atoms.B :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    rw [Bn_eq]; omega
  simp only [splitOf, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact Nat.mod_lt _ (by norm_num [Bn])
  · exact (Nat.div_lt_iff_lt_mul (by norm_num [Bn])).2 (by omega)

theorem val_splitOf (v : ℕ) : Nock.Atoms.val (splitOf v) = v := by
  simp only [splitOf, Nock.Atoms.val_cons, Nock.Atoms.val_nil, mul_zero, add_zero]
  rw [← Bn_eq]; exact Nat.mod_add_div v Bn

theorem wordsOf_lt (v : ℕ) : ∀ a ∈ wordsOf v, a < Bn := by
  intro a ha
  unfold wordsOf at ha
  split_ifs at ha with h
  · simp at ha; subst ha; norm_num [Bn]
  · exact limbs_lt v a ha

theorem val_wordsOf (v : ℕ) : Nock.Atoms.val (wordsOf v) = v := by
  unfold wordsOf
  split_ifs with h
  · simp [h]
  · exact Nock.Atoms.val_limbs v

theorem wordsOf_ne_nil (v : ℕ) : wordsOf v ≠ [] := by
  unfold wordsOf
  split_ifs with h
  · simp
  · exact fun h' => h (Nat.digits_eq_nil_iff_eq_zero.mp h')

/-! ## 3. The packed Q block: `hornerQ1 y (packQ1 ws) = evR y ws` for `0/1` carries -/

/-- Little-endian value of a list of bits (base `2`). -/
def val2 : List ℕ → ℕ
  | [] => 0
  | a :: xs => a + 2 * val2 xs

theorem zipIdx_sum (l : List ℕ) :
    ∀ k : ℕ, ((l.zipIdx k).map fun x => x.1 * 2 ^ x.2).sum = 2 ^ k * val2 l := by
  induction l with
  | nil => intro k; simp [val2]
  | cons a l ih => intro k; simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1), val2, pow_succ]; ring

theorem bitOf_val2 : ∀ (x : List ℕ), (∀ a ∈ x, a ≤ 1) → ∀ t, bitOf (val2 x) t = x.getD t 0
  | [], _, t => by simp [val2, bitOf]
  | a :: xs, h, 0 => by
    have ha := h a (by simp)
    simp only [bitOf, val2, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | a :: xs, h, t + 1 => by
    have ha := h a (by simp)
    have ih := bitOf_val2 xs (fun b hb => h b (by simp [hb])) t
    simp only [bitOf, val2, List.getD_cons_succ] at ih ⊢
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have : (a + 2 * val2 xs) / 2 = val2 xs := by omega
    rw [this, ih]

section Ring
variable {Q : Type} [CommRing Q]

theorem rsum_eq (y : Q) : ∀ (x : List ℕ) (m : ℕ), x.length ≤ m →
    ((List.range m).map fun t => ((x.getD t 0 : ℕ) : Q) * y ^ t).sum = evR y (zl x)
  | [], m, _ => by simp [evR, zl]
  | a :: x, 0, h => by simp at h
  | a :: x, m + 1, h => by
    have ih := rsum_eq y x m (by simpa using h)
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have hf : ((fun t => ((((a :: x).getD t 0 : ℕ) : Q)) * y ^ t) ∘ Nat.succ) =
        fun t => y * (((x.getD t 0 : ℕ) : Q) * y ^ t) := by
      funext t; simp only [Function.comp, List.getD_cons_succ, Nat.succ_eq_add_one]; ring
    rw [hf, List.sum_map_mul_left, ih]
    simp [evR, zl]

theorem evR_zl_append (y : Q) : ∀ (a b : List ℕ),
    evR y (zl (a ++ b)) = evR y (zl a) + y ^ a.length * evR y (zl b)
  | [], b => by simp [zl, evR]
  | x :: a, b => by
    have ih := evR_zl_append y a b
    simp only [zl, List.cons_append, List.map_cons, evR, List.length_cons, pow_succ] at ih ⊢
    rw [ih]; ring

theorem evR_take_drop (y : Q) (ws : List ℕ) :
    evR y (zl ws) = evR y (zl (ws.take 32)) + y ^ 32 * evR y (zl (ws.drop 32)) := by
  by_cases h : 32 ≤ ws.length
  · conv_lhs => rw [← List.take_append_drop 32 ws]
    rw [evR_zl_append, List.length_take, min_eq_left h]
  · have : ws.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
    rw [this, List.take_of_length_le (by omega)]
    simp [zl, evR]

theorem packV_val2 (y : Q) (x : List ℕ) (h1 : ∀ a ∈ x, a ≤ 1) (hl : x.length ≤ 32) :
    packV y (val2 x) = evR y (zl x) := by
  unfold packV
  have : ∀ t ∈ List.range 32, ((bitOf (val2 x) t : ℕ) : Q) * y ^ t = ((x.getD t 0 : ℕ) : Q) * y ^ t := by
    intro t _; rw [bitOf_val2 x h1 t]
  rw [List.map_congr_left this]
  exact rsum_eq y x 32 hl

theorem hornerQ1_packQ1 (y : Q) : ∀ (n : ℕ) (ws : List ℕ), ws.length ≤ n → (∀ a ∈ ws, a ≤ 1) →
    hornerQ1 y (packQ1 ws) = evR y (zl ws)
  | 0, ws, hl, _ => by
    have : ws = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [packQ1, hornerQ1, evR, zl]
  | n + 1, ws, hl, h1 => by
    cases ws with
    | nil => simp [packQ1, hornerQ1, evR, zl]
    | cons q qs =>
      rw [packQ1.eq_def]
      dsimp only
      rw [hornerQ1]
      have hz := zipIdx_sum ((q :: qs).take 32) 0
      simp only [pow_zero, one_mul] at hz
      rw [hz]
      have hlt : ((q :: qs).take 32).length ≤ 32 := by simp
      have hle : ∀ a ∈ (q :: qs).take 32, a ≤ 1 := fun a ha => h1 a (List.mem_of_mem_take ha)
      rw [packV_val2 y _ hle hlt]
      have ih := hornerQ1_packQ1 y n ((q :: qs).drop 32) (by simp at hl ⊢; omega)
        (fun a ha => h1 a (List.mem_of_mem_drop ha))
      rw [ih, evR_take_drop y (q :: qs)]

end Ring

/-! ## 4. Slot facts of `add` / `sub` / `lt` calls -/

/-- The facts the gate groups read of a slot: a role slot `r ≤ 3` of mode `≤ 3` whose coefficients are `coefOf`, or
the packed Q block (mode `4`, no role) with `coefQ1`. -/
def SlotOK (o : PrimOp) (lb : ℕ) (s : SlotL) : Prop :=
  (∃ r, r ≤ 3 ∧ s.role = some r ∧ s.mode ≤ 3 ∧ s.cf1 = (coefOf o lb (some r)).1 ∧
      s.cf2 = (coefOf o lb (some r)).2) ∨
    (s.role = none ∧ s.mode = 4 ∧ s.cf1 = (coefQ1 o).1 ∧ s.cf2 = (coefQ1 o).2)

theorem handleSlot_ok (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) (hr : r ≤ 3) :
    SlotOK o lb (handleSlot p o lb r v k s) := by
  left
  refine ⟨r, hr, ?_⟩
  unfold handleSlot
  split_ifs <;> simp

theorem handleSlot_pos (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) (hf : isFactor o r = false) :
    0 < (handleSlot p o lb r v k s).words.length := by
  unfold handleSlot
  split_ifs with h1 h2
  · simp [splitOf]
  · simp [hf] at h2
  · simp

theorem handleSlot_vw (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    (handleSlot p o lb r v k s).vw = if v < p then splitOf v else Nock.Atoms.limbs v := by
  unfold handleSlot
  split_ifs <;> simp_all

theorem witSlot_ok (o : PrimOp) (lb r w : ℕ) (hr : r ≤ 3) : SlotOK o lb (witSlot o lb r w) := by
  left
  exact ⟨r, hr, by simp [witSlot]⟩

theorem witSlot_pos (o : PrimOp) (lb r w : ℕ) : 0 < (witSlot o lb r w).words.length := by
  simp only [witSlot]
  exact List.length_pos_iff.mpr (wordsOf_ne_nil w)

theorem packQ1_ne_nil (ws : List ℕ) (h : ws ≠ []) : packQ1 ws ≠ [] := by
  cases ws with
  | nil => exact absurd rfl h
  | cons q qs => rw [packQ1.eq_def]; simp

theorem qSlot_ok (o : PrimOp) (lb : ℕ) (qs : List ℤ) : SlotOK o lb (qSlot o true qs) := by
  right
  simp [qSlot]

theorem qSlot_pos (o : PrimOp) (qs : List ℤ) : 0 < (qSlot o true qs).words.length := by
  simp only [qSlot, if_true]
  split_ifs with h
  · simp
  · exact List.length_pos_iff.mpr (packQ1_ne_nil _ (by simpa using h))

/-! ### The three shapes -/

def slA (p : ℕ) (cl : CallL) : SlotL := handleSlot p cl.op cl.lbv 0 cl.a cl.kA cl.vA
def slB (p : ℕ) (cl : CallL) : SlotL := handleSlot p cl.op cl.lbv 1 cl.b cl.kB cl.vB
def slC (p : ℕ) (cl : CallL) : SlotL := handleSlot p cl.op cl.lbv 2 cl.c cl.kE cl.vE
def slD (cl : CallL) : SlotL := witSlot cl.op cl.lbv 3 (ltWit cl.a cl.b)

/-- The coefficient lists of the three identities. -/
def dsAdd (p : ℕ) (cl : CallL) : List ℤ :=
  addL (addL (zl (slA p cl).vw) (zl (slB p cl).vw)) (negL (zl (slC p cl).vw))
def dsSub (p : ℕ) (cl : CallL) : List ℤ :=
  addL (addL (zl (slB p cl).vw) (zl (slC p cl).vw)) (negL (zl (slA p cl).vw))
def dsLt (p : ℕ) (cl : CallL) : List ℤ :=
  addL (addL (addL ((zl (slA p cl).vw).map ((1 - 2 * (cl.lbv : ℤ)) * ·))
    ((zl (slB p cl).vw).map (-(1 - 2 * (cl.lbv : ℤ)) * ·))) (zl (slD cl).vw)) [1 - (cl.lbv : ℤ)]

theorem slotsOf_add (p : ℕ) (cl : CallL) (h : cl.op = .add) :
    slotsOf p cl = [slA p cl, slB p cl, slC p cl, qSlot .add true (carr Bn 0 (dsAdd p cl))] := by
  simp only [slA, slB, slC, dsAdd, slotsOf, h]

theorem slotsOf_sub (p : ℕ) (cl : CallL) (h : cl.op = .sub) :
    slotsOf p cl = [slA p cl, slB p cl, slC p cl, qSlot .sub true (carr Bn 0 (dsSub p cl))] := by
  simp only [slA, slB, slC, dsSub, slotsOf, h]

theorem slotsOf_lt (p : ℕ) (cl : CallL) (h : cl.op = .lt) :
    slotsOf p cl = [slA p cl, slB p cl, slD cl, qSlot .lt true (carr Bn 0 (dsLt p cl))] := by
  simp only [slA, slB, slD, dsLt, slotsOf, h]

theorem handleSlot_role (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    (handleSlot p o lb r v k s).role = some r := by
  unfold handleSlot; split_ifs <;> rfl

theorem handleSlot_mode_le (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    (handleSlot p o lb r v k s).mode ≤ 3 := by
  unfold handleSlot; split_ifs <;> simp

/-- **The shape of an add/sub/lt slot list**: three role slots (`ra`, `rb`, `rc` or `rd`) then the packed Q
block. -/
structure Shape (o : PrimOp) (lb : ℕ) (s1 s2 s3 s4 : SlotL) : Prop where
  r1 : s1.role = some 0
  r2 : s2.role = some 1
  r3 : (o = .lt → s3.role = some 3) ∧ (o ≠ .lt → s3.role = some 2)
  r4 : s4.role = none
  m1 : s1.mode ≤ 3
  m2 : s2.mode ≤ 3
  m3 : s3.mode ≤ 3
  m4 : s4.mode = 4
  ok1 : SlotOK o lb s1
  ok2 : SlotOK o lb s2
  ok3 : SlotOK o lb s3
  ok4 : SlotOK o lb s4
  n1 : 0 < s1.words.length
  n2 : 0 < s2.words.length
  n3 : 0 < s3.words.length
  n4 : 0 < s4.words.length

theorem shape_A (p : ℕ) (cl : CallL) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    ∃ s1 s2 s3 s4, slotsOf p cl = [s1, s2, s3, s4] ∧ Shape cl.op cl.lbv s1 s2 s3 s4 := by
  have hf : ∀ r, isFactor cl.op r = false := by
    intro r; rcases hop with h | h | h <;> simp [isFactor, h]
  rcases hop with h | h | h
  · refine ⟨_, _, _, _, slotsOf_add p cl h, ?_⟩
    exact ⟨handleSlot_role .., handleSlot_role .., ⟨fun h' => (by rw [h] at h'; cases h'), fun _ => handleSlot_role ..⟩, rfl,
      handleSlot_mode_le .., handleSlot_mode_le .., handleSlot_mode_le .., rfl,
      handleSlot_ok _ _ _ _ _ _ _ (by omega), handleSlot_ok _ _ _ _ _ _ _ (by omega),
      handleSlot_ok _ _ _ _ _ _ _ (by omega), by rw [h]; exact qSlot_ok _ _ _,
      handleSlot_pos _ _ _ _ _ _ _ (hf _), handleSlot_pos _ _ _ _ _ _ _ (hf _),
      handleSlot_pos _ _ _ _ _ _ _ (hf _), qSlot_pos _ _⟩
  · refine ⟨_, _, _, _, slotsOf_sub p cl h, ?_⟩
    exact ⟨handleSlot_role .., handleSlot_role .., ⟨fun h' => (by rw [h] at h'; cases h'), fun _ => handleSlot_role ..⟩, rfl,
      handleSlot_mode_le .., handleSlot_mode_le .., handleSlot_mode_le .., rfl,
      handleSlot_ok _ _ _ _ _ _ _ (by omega), handleSlot_ok _ _ _ _ _ _ _ (by omega),
      handleSlot_ok _ _ _ _ _ _ _ (by omega), by rw [h]; exact qSlot_ok _ _ _,
      handleSlot_pos _ _ _ _ _ _ _ (hf _), handleSlot_pos _ _ _ _ _ _ _ (hf _),
      handleSlot_pos _ _ _ _ _ _ _ (hf _), qSlot_pos _ _⟩
  · refine ⟨_, _, _, _, slotsOf_lt p cl h, ?_⟩
    exact ⟨handleSlot_role .., handleSlot_role .., ⟨fun _ => rfl, fun h' => absurd h h'⟩, rfl,
      handleSlot_mode_le .., handleSlot_mode_le .., by simp [slD, witSlot], rfl,
      handleSlot_ok _ _ _ _ _ _ _ (by omega), handleSlot_ok _ _ _ _ _ _ _ (by omega),
      witSlot_ok _ _ _ _ (by omega), by rw [h]; exact qSlot_ok _ _ _,
      handleSlot_pos _ _ _ _ _ _ _ (hf _), handleSlot_pos _ _ _ _ _ _ _ (hf _),
      witSlot_pos _ _ _ _, qSlot_pos _ _⟩

/-! ## 5. Row positions of a block -/

section Rows
variable {X : Type}

/-- The slot rows of a slot list under a row constructor `f`. -/
def rowsOf (f : SlotL → ℕ → X) (ss : List SlotL) : List X :=
  ss.flatMap fun s => (List.range s.words.length).map (f s)

theorem rowsOf_cons (f : SlotL → ℕ → X) (s : SlotL) (rest : List SlotL) :
    rowsOf f (s :: rest) = (List.range s.words.length).map (f s) ++ rowsOf f rest := by
  simp [rowsOf]

/-- **Every row is some slot's row `i`; if it is a slot's last row, the following row is the next slot's first row,
or the list ends.** -/
theorem rowsAt (f : SlotL → ℕ → X) (d : X) : ∀ (ss : List SlotL), (∀ s ∈ ss, 0 < s.words.length) →
    ∀ j, j < (rowsOf f ss).length → ∃ k i s, ss[k]? = some s ∧ i < s.words.length ∧
      (rowsOf f ss).getD j d = f s i ∧
      (i + 1 = s.words.length →
        (∀ s', ss[k + 1]? = some s' → j + 1 < (rowsOf f ss).length ∧ (rowsOf f ss).getD (j + 1) d = f s' 0) ∧
        (ss[k + 1]? = none → (rowsOf f ss).length ≤ j + 1))
  | [], _, j, hj => by simp [rowsOf] at hj
  | s :: rest, hpos, j, hj => by
    have hn : 0 < s.words.length := hpos s (by simp)
    have hrest : ∀ s' ∈ rest, 0 < s'.words.length := fun s' h => hpos s' (by simp [h])
    rw [rowsOf_cons] at hj ⊢
    have hlenA : ((List.range s.words.length).map (f s)).length = s.words.length := by simp
    by_cases hjn : j < s.words.length
    · refine ⟨0, j, s, by simp, hjn, ?_, ?_⟩
      · rw [List.getD_append _ _ _ _ (by rw [hlenA]; exact hjn), List.getD_eq_getElem _ _ (by rw [hlenA]; exact hjn)]
        simp
      · intro hj1
        refine ⟨?_, ?_⟩
        · intro s' hs'
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hs'
          cases rest with
          | nil => simp at hs'
          | cons s2 rest2 =>
            have hs2 : s2 = s' := by simpa using hs'
            subst hs2
            have hn2 : 0 < s2.words.length := hrest s2 (by simp)
            have hR' : 0 < (rowsOf f (s2 :: rest2)).length := by rw [rowsOf_cons]; simp; omega
            refine ⟨by rw [List.length_append, hlenA]; omega, ?_⟩
            rw [List.getD_append_right _ _ _ _ (by rw [hlenA]; omega), hlenA, show j + 1 - s.words.length = 0 by omega,
              rowsOf_cons, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
            simp
        · intro hnone
          simp only [List.getElem?_cons_succ] at hnone
          have : rest = [] := by
            cases rest with
            | nil => rfl
            | cons _ _ => simp at hnone
          subst this
          simp [rowsOf, hlenA]; omega
    · have hj' : j - s.words.length < (rowsOf f rest).length := by
        rw [List.length_append, hlenA] at hj; omega
      obtain ⟨k, i, s0, hk, hi, hrow, hnext⟩ := rowsAt f d rest hrest (j - s.words.length) hj'
      refine ⟨k + 1, i, s0, by simpa using hk, hi, ?_, ?_⟩
      · rw [List.getD_append_right _ _ _ _ (by rw [hlenA]; omega), hlenA]; exact hrow
      · intro hi1
        obtain ⟨h1, h2⟩ := hnext hi1
        refine ⟨?_, ?_⟩
        · intro s' hs'
          obtain ⟨h1a, h1b⟩ := h1 s' (by simpa using hs')
          refine ⟨by rw [List.length_append, hlenA]; omega, ?_⟩
          rw [List.getD_append_right _ _ _ _ (by rw [hlenA]; omega), hlenA,
            show j + 1 - s.words.length = j - s.words.length + 1 by omega]
          exact h1b
        · intro hnone
          have := h2 (by simpa using hnone)
          rw [List.length_append, hlenA]; omega

end Rows

/-! ## 6. `gSeq` -/

section Gates
variable {F : Type} [Field F]

/-- **`gSeq`, abstractly**: a row `cur` of role `r0` / mode `m0` that ends its slot (`eos = 1`) in an op-`o` block
(`o ≤ 2`: add sub lt), followed by `nxt` as stated, satisfies every `gSeq` gate. -/
theorem gSeq_abs (cur nxt : BRow F) (o : ℕ) (ho : o ≤ 2)
    (hop : ∀ k, cur.op k = ind (k = o)) (heos : cur.eos = 1)
    (r0 : Option ℕ) (m0 : ℕ)
    (hr : ∀ j, cur.role j = ind (r0 = some j)) (hm : ∀ j, cur.mode j = ind (j = m0))
    (hr3 : ∀ r, r0 = some r → r ≤ 3) (hm5 : m0 ≠ 5)
    (hnone : r0 = none → m0 = 4 ∧ nxt.sL = 0) (hsome : r0 ≠ none → m0 ≠ 4)
    (h1 : r0 = some 0 → nxt.role 1 = 1)
    (h2 : r0 = some 1 → (o ≤ 1 → nxt.role 2 = 1) ∧ (o = 2 → nxt.role 3 = 1))
    (h3 : r0 = some 2 → o ≤ 1 ∧ nxt.mode 4 = 1) (h4 : r0 = some 3 → o = 2 ∧ nxt.mode 4 = 1) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)), a.gate.eval (envB cur.col nxt.col) = 0 := by
  have e_ra : cur.col AluSZChipJ9.ra = ind (r0 = some 0) := hr 0
  have e_rb : cur.col AluSZChipJ9.rb = ind (r0 = some 1) := hr 1
  have e_rc : cur.col AluSZChipJ9.rc = ind (r0 = some 2) := hr 2
  have e_rd : cur.col AluSZChipJ9.rd = ind (r0 = some 3) := hr 3
  have e_rx : cur.col AluSZChipJ9.rx = ind (r0 = some 4) := hr 4
  have e_ry : cur.col AluSZChipJ9.ry = ind (r0 = some 5) := hr 5
  have e_rs : cur.col AluSZChipJ9.rs = ind (r0 = some 6) := hr 6
  have e_q1 : cur.col AluSZChipJ9.mQ1 = ind (4 = m0) := hm 4
  have e_qm : cur.col AluSZChipJ9.mQM = ind (5 = m0) := hm 5
  have e_oa : cur.col AluSZChipJ9.oAdd = ind (0 = o) := hop 0
  have e_os : cur.col AluSZChipJ9.oSub = ind (1 = o) := hop 1
  have e_ol : cur.col AluSZChipJ9.oLt = ind (2 = o) := hop 2
  have e_om : cur.col AluSZChipJ9.oMul = ind (3 = o) := hop 3
  have e_od : cur.col AluSZChipJ9.oDiv = ind (4 = o) := hop 4
  have e_omo : cur.col AluSZChipJ9.oMod = ind (5 = o) := hop 5
  have e_eos : cur.col AluSZChipJ9.eos = 1 := heos
  have n_rb : nxt.col AluSZChipJ9.rb = nxt.role 1 := rfl
  have n_rc : nxt.col AluSZChipJ9.rc = nxt.role 2 := rfl
  have n_rd : nxt.col AluSZChipJ9.rd = nxt.role 3 := rfl
  have n_rx : nxt.col AluSZChipJ9.rx = nxt.role 4 := rfl
  have n_rs : nxt.col AluSZChipJ9.rs = nxt.role 6 := rfl
  have n_q1 : nxt.col AluSZChipJ9.mQ1 = nxt.mode 4 := rfl
  have n_qm : nxt.col AluSZChipJ9.mQM = nxt.mode 5 := rfl
  have n_sL : nxt.col AluSZChipJ9.sL = nxt.sL := rfl
  have hnm : ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)), True := fun _ _ => trivial
  intro a ha
  have hm5' : ind (5 = m0) = (0 : F) := by simp [ind, Ne.symm hm5]
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases r0 with _ | n
  · obtain ⟨hm4, hs⟩ := hnone rfl
    subst hm4
    interval_cases o <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, AluSZChipJ9.sumC,
      CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs, e_q1, e_qm,
      e_oa, e_os, e_ol, e_om, e_od, e_omo, e_eos, n_rb, n_rc, n_rd, n_rx, n_rs, n_q1, n_qm, n_sL, hs, ind]
  · have hm4 : m0 ≠ 4 := hsome (by simp)
    have hq1 : ind (4 = m0) = (0 : F) := by simp [ind, Ne.symm hm4]
    rcases n with _ | _ | _ | _ | n
    · have h1' := h1 rfl
      interval_cases o <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, AluSZChipJ9.sumC,
      CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs, e_q1, e_qm,
      e_oa, e_os, e_ol, e_om, e_od, e_omo, e_eos, n_rb, n_rc, n_rd, n_rx, n_rs, n_q1, n_qm, n_sL, ind, h1', Ne.symm hm4, Ne.symm hm5]
    · obtain ⟨h2a, h2b⟩ := h2 rfl
      interval_cases o <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, AluSZChipJ9.sumC,
      CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs, e_q1, e_qm,
      e_oa, e_os, e_ol, e_om, e_od, e_omo, e_eos, n_rb, n_rc, n_rd, n_rx, n_rs, n_q1, n_qm, n_sL, ind, h2a, h2b, Ne.symm hm4, Ne.symm hm5]
    · obtain ⟨h3a, h3b⟩ := h3 rfl
      interval_cases o <;> try (exfalso; omega)
      all_goals
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, AluSZChipJ9.sumC,
      CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs, e_q1, e_qm,
      e_oa, e_os, e_ol, e_om, e_od, e_omo, e_eos, n_rb, n_rc, n_rd, n_rx, n_rs, n_q1, n_qm, n_sL, ind, h3b, Ne.symm hm4, Ne.symm hm5]
    · obtain ⟨h4a, h4b⟩ := h4 rfl
      subst h4a
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, AluSZChipJ9.sumC,
      CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs, e_q1, e_qm,
      e_oa, e_os, e_ol, e_om, e_od, e_omo, e_eos, n_rb, n_rc, n_rd, n_rx, n_rs, n_q1, n_qm, n_sL, ind, h4b, Ne.symm hm4, Ne.symm hm5]
    · have := hr3 (n + 4) rfl
      omega

/-- A row that does not end its slot satisfies every `gSeq` gate (they all carry the factor `eos`). -/
theorem gSeq_eos0 (cur nxt : BRow F) (h : cur.eos = 0) :
    ∀ a ∈ (AluSZChipJ9.gSeq : List (AxisChipJ9.AG F)), a.gate.eval (envB cur.col nxt.col) = 0 := by
  have e_eos : cur.col AluSZChipJ9.eos = 0 := h
  intro a ha
  simp only [AluSZChipJ9.gSeq, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [AluSZChipJ9.succ, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, CoeffExpr.eval, envB, e_eos]

theorem blockB_eq (p : ℕ) (cl : CallL) :
    blockB (F := F) p cl = hdrRow cl :: rowsOf (slotRow p cl) (slotsOf p cl) := rfl

theorem opIx_le (cl : CallL) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) : opIx cl.op ≤ 2 := by
  rcases hop with h | h | h <;> simp [opIx, h]

theorem opIx_eq2 (cl : CallL) : opIx cl.op = 2 ↔ cl.op = .lt := by
  cases h : cl.op <;> simp [opIx]

/-- **`GroupSat gSeq`** for `add` / `sub` / `lt`. -/
theorem groupSat_gSeq_A (p : ℕ) (cl : CallL) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    GroupSat (F := F) p cl AluSZChipJ9.gSeq := by
  obtain ⟨s1, s2, s3, s4, hss, sh⟩ := shape_A p cl hop
  have hsl : ∀ s ∈ slotsOf p cl, 0 < s.words.length := by
    rw [hss]; intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [sh.n1, sh.n2, sh.n3, sh.n4]
  have hoo := opIx_le cl hop
  have hlt2 := opIx_eq2 cl
  intro j hj nxt hnx a ha
  cases j with
  | zero => exact gSeq_eos0 _ _ (by rfl) a ha
  | succ j' =>
    have hlen : j' < (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length := by
      rw [blockB_eq] at hj; simpa using hj
    obtain ⟨k, i, s, hk, hi, hrow, hnext⟩ := rowsAt (slotRow (F := F) p cl) BRow.zero (slotsOf p cl) hsl j' hlen
    have hcur : (blockB (F := F) p cl).getD (j' + 1) BRow.zero = slotRow p cl s i := by
      rw [blockB_eq]; exact hrow
    rw [hcur]
    by_cases hlast : i + 1 = s.words.length
    · obtain ⟨hn1, hn2⟩ := hnext hlast
      have hk' := hk
      rw [hss] at hk'
      obtain ⟨hk4, -⟩ := List.getElem?_eq_some_iff.mp hk'
      simp only [List.length_cons, List.length_nil] at hk4
      have heos : (slotRow (F := F) p cl s i).eos = 1 := by
        show ind (i + 1 = s.words.length) = (1 : F); simp [ind, hlast]
      have hnxt : ∀ s', ([s1, s2, s3, s4] : List SlotL)[k + 1]? = some s' → nxt = slotRow p cl s' 0 := by
        intro s' hs'
        obtain ⟨hl, heq⟩ := hn1 s' (by rw [hss]; exact hs')
        have := hnx.1 (by rw [blockB_eq]; simpa using hl)
        rw [this, blockB_eq]; exact heq
      have hend : ([s1, s2, s3, s4] : List SlotL)[k + 1]? = none → nxt.sL = 0 := by
        intro hn
        have := hn2 (by rw [hss]; exact hn)
        exact (hnx.2 (by rw [blockB_eq]; simpa using this)).1
      have m1 := sh.m1
      have m2 := sh.m2
      have m3 := sh.m3
      have m4 := sh.m4
      have r3a := sh.r3.1
      have r3b := sh.r3.2
      interval_cases k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
        subst hk'
        have hn := hnxt s2 (by simp)
        refine gSeq_abs _ nxt (opIx cl.op) hoo (fun _ => rfl) heos s1.role s1.mode (fun _ => rfl) (fun _ => rfl)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a ha
        · intro r hr; rw [sh.r1] at hr; cases hr; omega
        · omega
        · intro h; rw [sh.r1] at h; cases h
        · intro _; omega
        · intro _; rw [hn]; show ind (s2.role = some 1) = 1; simp [ind, sh.r2]
        · intro h; rw [sh.r1] at h; cases h
        · intro h; rw [sh.r1] at h; cases h
        · intro h; rw [sh.r1] at h; cases h
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        subst hk'
        have hn := hnxt s3 (by simp)
        refine gSeq_abs _ nxt (opIx cl.op) hoo (fun _ => rfl) heos s2.role s2.mode (fun _ => rfl) (fun _ => rfl)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a ha
        · intro r hr; rw [sh.r2] at hr; cases hr; omega
        · omega
        · intro h; rw [sh.r2] at h; cases h
        · intro _; omega
        · intro h; rw [sh.r2] at h; cases h
        · intro _
          refine ⟨fun h1 => ?_, fun h2 => ?_⟩
          · rw [hn]; show ind (s3.role = some 2) = 1
            have : ¬ cl.op = .lt := fun hl => by have := (opIx_eq2 cl).2 hl; omega
            simp [ind, r3b this]
          · rw [hn]; show ind (s3.role = some 3) = 1
            simp [ind, r3a ((opIx_eq2 cl).1 h2)]
        · intro h; rw [sh.r2] at h; cases h
        · intro h; rw [sh.r2] at h; cases h
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        subst hk'
        have hn := hnxt s4 (by simp)
        have hmode4 : nxt.mode 4 = 1 := by
          rw [hn]; show ind (4 = s4.mode) = 1; simp [ind, m4]
        by_cases hl : cl.op = .lt
        · refine gSeq_abs _ nxt (opIx cl.op) hoo (fun _ => rfl) heos s3.role s3.mode (fun _ => rfl) (fun _ => rfl)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a ha
          · intro r hr; rw [r3a hl] at hr; cases hr; omega
          · omega
          · intro h; rw [r3a hl] at h; cases h
          · intro _; omega
          · intro h; rw [r3a hl] at h; cases h
          · intro h; rw [r3a hl] at h; cases h
          · intro h; rw [r3a hl] at h; cases h
          · intro _; exact ⟨(opIx_eq2 cl).2 hl, hmode4⟩
        · refine gSeq_abs _ nxt (opIx cl.op) hoo (fun _ => rfl) heos s3.role s3.mode (fun _ => rfl) (fun _ => rfl)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a ha
          · intro r hr; rw [r3b hl] at hr; cases hr; omega
          · omega
          · intro h; rw [r3b hl] at h; cases h
          · intro _; omega
          · intro h; rw [r3b hl] at h; cases h
          · intro h; rw [r3b hl] at h; cases h
          · intro _
            refine ⟨?_, hmode4⟩
            have := (opIx_eq2 cl).not.2 hl
            omega
          · intro h; rw [r3b hl] at h; cases h
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk'
        subst hk'
        refine gSeq_abs _ nxt (opIx cl.op) hoo (fun _ => rfl) heos s4.role s4.mode (fun _ => rfl) (fun _ => rfl)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a ha
        · intro r hr; rw [sh.r4] at hr; cases hr
        · omega
        · intro _; exact ⟨m4, hend (by simp)⟩
        · intro h; exact absurd sh.r4 h
        · intro h; rw [sh.r4] at h; cases h
        · intro h; rw [sh.r4] at h; cases h
        · intro h; rw [sh.r4] at h; cases h
        · intro h; rw [sh.r4] at h; cases h
    · exact gSeq_eos0 _ _ (by show ind (i + 1 = s.words.length) = (0 : F); simp [ind, hlast]) a ha

/-! ## 7. `gCoef` -/

/-- A row that is not a slot's first row (`fst = 0`) satisfies every `gCoef` gate. -/
theorem gCoef_fst0 (cur nxt : BRow F) (h : cur.fst = 0) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)), a.gate.eval (envB cur.col nxt.col) = 0 := by
  have e_fst : cur.col AluSZChipJ9.fst = 0 := h
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [AluSZChipJ9.coef, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3, CoeffExpr.eval, envB, e_fst]

/-- **`gCoef`, abstractly**: a slot's first row whose coefficient columns are the slot's `coefOf` / `coefQ1`. -/
theorem gCoef_abs (cur nxt : BRow F) (o : PrimOp) (ho : o = .add ∨ o = .sub ∨ o = .lt) (L : ℕ)
    (hop : ∀ k, cur.op k = ind (k = opIx o)) (hlb : cur.lb = (L : F)) (hfst : cur.fst = 1)
    (r0 : Option ℕ) (m0 : ℕ)
    (hr : ∀ j, cur.role j = ind (r0 = some j)) (hm : ∀ j, cur.mode j = ind (j = m0))
    (c1 c2 : ℤ) (hc1 : cur.cf1 = (c1 : F)) (hc2 : cur.cf2 = (c2 : F))
    (hok : (∃ r, r ≤ 3 ∧ r0 = some r ∧ m0 ≤ 3 ∧ c1 = (coefOf o L (some r)).1 ∧ c2 = (coefOf o L (some r)).2) ∨
      (r0 = none ∧ m0 = 4 ∧ c1 = (coefQ1 o).1 ∧ c2 = (coefQ1 o).2)) :
    ∀ a ∈ (AluSZChipJ9.gCoef : List (AxisChipJ9.AG F)), a.gate.eval (envB cur.col nxt.col) = 0 := by
  have e_ra : cur.col AluSZChipJ9.ra = ind (r0 = some 0) := hr 0
  have e_rb : cur.col AluSZChipJ9.rb = ind (r0 = some 1) := hr 1
  have e_rc : cur.col AluSZChipJ9.rc = ind (r0 = some 2) := hr 2
  have e_rd : cur.col AluSZChipJ9.rd = ind (r0 = some 3) := hr 3
  have e_rx : cur.col AluSZChipJ9.rx = ind (r0 = some 4) := hr 4
  have e_ry : cur.col AluSZChipJ9.ry = ind (r0 = some 5) := hr 5
  have e_rs : cur.col AluSZChipJ9.rs = ind (r0 = some 6) := hr 6
  have e_q1 : cur.col AluSZChipJ9.mQ1 = ind (4 = m0) := hm 4
  have e_qm : cur.col AluSZChipJ9.mQM = ind (5 = m0) := hm 5
  have e_oa : cur.col AluSZChipJ9.oAdd = ind (0 = opIx o) := hop 0
  have e_os : cur.col AluSZChipJ9.oSub = ind (1 = opIx o) := hop 1
  have e_ol : cur.col AluSZChipJ9.oLt = ind (2 = opIx o) := hop 2
  have e_om : cur.col AluSZChipJ9.oMul = ind (3 = opIx o) := hop 3
  have e_od : cur.col AluSZChipJ9.oDiv = ind (4 = opIx o) := hop 4
  have e_omo : cur.col AluSZChipJ9.oMod = ind (5 = opIx o) := hop 5
  have e_fst : cur.col AluSZChipJ9.fst = 1 := hfst
  have e_lb : cur.col AluSZChipJ9.lb = (L : F) := hlb
  have e_c1 : cur.col AluSZChipJ9.cf1 = (c1 : F) := hc1
  have e_c2 : cur.col AluSZChipJ9.cf2 = (c2 : F) := hc2
  intro a ha
  simp only [AluSZChipJ9.gCoef, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases hok with ⟨r, hr3, rfl, hm3, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · have h4 : (4 : ℕ) ≠ m0 := by omega
    have h5 : (5 : ℕ) ≠ m0 := by omega
    interval_cases r <;> rcases ho with rfl | rfl | rfl <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AluSZChipJ9.coef, AluSZChipJ9.sgnLt, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3,
      AluSZChipJ9.sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs,
      e_q1, e_qm, e_oa, e_os, e_ol, e_om, e_od, e_omo, e_fst, e_lb, e_c1, e_c2, h4, h5, coefOf, opIx, ind]
  · rcases ho with rfl | rfl | rfl <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AluSZChipJ9.coef, AluSZChipJ9.sgnLt, AxisChipJ9.AG.gate, AluSZChipJ9.ar, AluSZChipJ9.prod3,
      AluSZChipJ9.sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, envB, e_ra, e_rb, e_rc, e_rd, e_rx, e_ry, e_rs,
      e_q1, e_qm, e_oa, e_os, e_ol, e_om, e_od, e_omo, e_fst, e_lb, e_c1, e_c2, coefQ1, opIx, ind]

/-- **`GroupSat gCoef`** for `add` / `sub` / `lt`. -/
theorem groupSat_gCoef_A (p : ℕ) (cl : CallL) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    GroupSat (F := F) p cl AluSZChipJ9.gCoef := by
  obtain ⟨s1, s2, s3, s4, hss, sh⟩ := shape_A p cl hop
  have hsl : ∀ s ∈ slotsOf p cl, 0 < s.words.length := by
    rw [hss]; intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [sh.n1, sh.n2, sh.n3, sh.n4]
  have hsok : ∀ s ∈ slotsOf p cl, SlotOK cl.op cl.lbv s := by
    rw [hss]; intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [sh.ok1, sh.ok2, sh.ok3, sh.ok4]
  intro j hj nxt hnx a ha
  cases j with
  | zero => exact gCoef_fst0 _ _ (by rfl) a ha
  | succ j' =>
    have hlen : j' < (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length := by
      rw [blockB_eq] at hj; simpa using hj
    obtain ⟨k, i, s, hk, hi, hrow, -⟩ := rowsAt (slotRow (F := F) p cl) BRow.zero (slotsOf p cl) hsl j' hlen
    have hcur : (blockB (F := F) p cl).getD (j' + 1) BRow.zero = slotRow p cl s i := by
      rw [blockB_eq]; exact hrow
    rw [hcur]
    by_cases hi0 : i = 0
    · subst hi0
      have hsm : s ∈ slotsOf p cl := List.mem_of_getElem? hk
      refine gCoef_abs _ nxt cl.op hop cl.lbv (fun _ => rfl) rfl (by show ind (0 = 0) = (1 : F); simp [ind])
        s.role s.mode (fun _ => rfl) (fun _ => rfl) s.cf1 s.cf2 (by simp [slotRow]) (by simp [slotRow]) ?_ a ha
      rcases hsok s hsm with ⟨r, hr3, hr, hm, hc1, hc2⟩ | ⟨hr, hm, hc1, hc2⟩
      · exact Or.inl ⟨r, hr3, hr, hm, hc1, hc2⟩
      · exact Or.inr ⟨hr, hm, hc1, hc2⟩
    · exact gCoef_fst0 _ _ (by show ind (i = 0) = (0 : F); simp [ind, hi0]) a ha

/-! ## 8. The 25-bit part of `gBits` -/

/-- The 32 lane-bit booleanities of `gBits`. -/
def gBitsB : List (AxisChipJ9.AG F) := (List.range 32).map (fun t => AluSZChipJ9.ar (boolE (cv (AluSZChipJ9.bt0 + t))))

/-- The `mQM·b_t = 0` part, `t ≥ 25`. -/
def gBitsQM : List (AxisChipJ9.AG F) :=
  (List.range 7).map (fun t => AluSZChipJ9.ar (.mul (cv AluSZChipJ9.mQM) (cv (AluSZChipJ9.bt0 + 25 + t))))

theorem gBits_split : (AluSZChipJ9.gBits : List (AxisChipJ9.AG F)) = gBitsB ++ gBitsQM := rfl

/-- **The mQM part of `gBits`** for `add` / `sub` / `lt` (no row has mode `mQM`). -/
theorem groupSat_gBitsQM_A (p : ℕ) (cl : CallL) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    GroupSat (F := F) p cl gBitsQM := by
  obtain ⟨s1, s2, s3, s4, hss, sh⟩ := shape_A p cl hop
  have hsl : ∀ s ∈ slotsOf p cl, 0 < s.words.length := by
    rw [hss]; intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [sh.n1, sh.n2, sh.n3, sh.n4]
  have hm5 : ∀ s ∈ slotsOf p cl, s.mode ≠ 5 := by
    rw [hss]; intro s hs
    have := sh.m1; have := sh.m2; have := sh.m3; have := sh.m4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> omega
  intro j hj nxt hnx a ha
  have hq : ∀ cur : BRow F, cur.mode 5 = 0 → a.gate.eval (envB cur.col nxt.col) = 0 := by
    intro cur h
    have e : cur.col AluSZChipJ9.mQM = 0 := h
    simp only [gBitsQM, List.mem_map, List.mem_range] at ha
    obtain ⟨t, -, rfl⟩ := ha
    simp [AxisChipJ9.AG.gate, AluSZChipJ9.ar, CoeffExpr.eval, envB, e]
  cases j with
  | zero => exact hq _ (by rfl)
  | succ j' =>
    have hlen : j' < (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length := by
      rw [blockB_eq] at hj; simpa using hj
    obtain ⟨k, i, s, hk, hi, hrow, -⟩ := rowsAt (slotRow (F := F) p cl) BRow.zero (slotsOf p cl) hsl j' hlen
    have hcur : (blockB (F := F) p cl).getD (j' + 1) BRow.zero = slotRow p cl s i := by
      rw [blockB_eq]; exact hrow
    rw [hcur]
    apply hq
    have := hm5 s (List.mem_of_getElem? hk)
    show ind (5 = s.mode) = (0 : F)
    simp [ind, Ne.symm this]

end Gates

/-! ## 9. The last `𝕂′` row of a block -/

section QRows
variable {Q : Type} [CommRing Q]

theorem rowsOf_length {X : Type} (f : SlotL → ℕ → X) (ss : List SlotL) :
    (rowsOf f ss).length = (ss.map (·.words.length)).sum := by
  induction ss with
  | nil => simp [rowsOf]
  | cons s rest ih => rw [rowsOf_cons, List.length_append, ih]; simp

theorem runSums_length (acc : Q × Q) (ds : List (Q × Q)) : (runSums acc ds).length = ds.length := by
  induction ds generalizing acc with
  | nil => simp [runSums]
  | cons d ds ih => simp [runSums, ih]

theorem runSums_getD : ∀ (ds : List (Q × Q)) (acc : Q × Q) (k : ℕ), k < ds.length →
    (runSums acc ds).getD k (0, 0) =
      (acc.1 + ((ds.take (k + 1)).map Prod.fst).sum, acc.2 + ((ds.take (k + 1)).map Prod.snd).sum)
  | [], _, _, h => by simp at h
  | d :: ds, acc, 0, _ => by
    simp [runSums]
  | d :: ds, acc, k + 1, h => by
    have ih := runSums_getD ds (acc.1 + d.1, acc.2 + d.2) k (by simpa using h)
    simp only [runSums, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ext <;> simp <;> ring

/-- The honest lane rows are `rowsOf` of the per-slot `(D1, D2)`. -/
theorem laneD_eq (p : ℕ) (y : Q) (cl : CallL) :
    laneD p y cl = rowsOf (fun s i => if i = 0 then AluHonestRows.slotD p y cl s else (0, 0)) (slotsOf p cl) := rfl

theorem laneHL_eq (p : ℕ) (y : Q) (cl : CallL) :
    laneHL y cl p = rowsOf (fun s i => (slotH y s i, slotHO y s i, if i = 0 then slotL y s else 0)) (slotsOf p cl) :=
  rfl

theorem sum_rowsOf_first (x : SlotL → Q × Q) : ∀ (ss : List SlotL), (∀ s ∈ ss, 0 < s.words.length) →
    ((rowsOf (fun s i => if i = 0 then x s else (0, 0)) ss).map Prod.fst).sum = (ss.map fun s => (x s).1).sum ∧
    ((rowsOf (fun s i => if i = 0 then x s else (0, 0)) ss).map Prod.snd).sum = (ss.map fun s => (x s).2).sum
  | [], _ => by simp [rowsOf]
  | s :: rest, h => by
    have hn : 0 < s.words.length := h s (by simp)
    have ih := sum_rowsOf_first x rest (fun s' hs' => h s' (by simp [hs']))
    rw [rowsOf_cons]
    obtain ⟨m, hm⟩ : ∃ m, s.words.length = m + 1 := ⟨s.words.length - 1, by omega⟩
    rw [hm, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def, ih.1, ih.2]

theorem blockQ_getD_last (p : ℕ) (y : Q) (cl : CallL) (hs : ∀ s ∈ slotsOf p cl, 0 < s.words.length)
    (hN : 0 < ((slotsOf p cl).map (·.words.length)).sum) :
    ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S1 =
        (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum ∧
    ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S2 =
        (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum := by
  set N := ((slotsOf p cl).map (·.words.length)).sum with hNdef
  have hHL : (laneHL y cl p).length = N := by rw [laneHL_eq, rowsOf_length]
  have hD : (laneD p y cl).length = N := by rw [laneD_eq, rowsOf_length]
  have hSS : (runSums (hdrD (Q := Q) cl) (laneD p y cl)).length = N := by rw [runSums_length, hD]
  obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hsums := sum_rowsOf_first (fun s => AluHonestRows.slotD p y cl s) (slotsOf p cl) hs
  have hkey := runSums_getD (laneD p y cl) (hdrD (Q := Q) cl) N' (by omega)
  have htake : (laneD p y cl).take (N' + 1) = laneD p y cl := List.take_of_length_le (by omega)
  rw [htake] at hkey
  rw [laneD_eq] at hkey
  rw [hsums.1, hsums.2] at hkey
  simp only [blockQ]
  rw [hN', List.getD_cons_succ]
  have hlt : N' < (List.map (fun x => (⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2,
      (latchOf p y cl).1, (latchOf p y cl).2⟩ : QRow Q))
      ((laneHL y cl p).zip ((laneD p y cl).zip (runSums (hdrD (Q := Q) cl) (laneD p y cl))))).length := by
    simp [List.length_zip, hHL, hD, hSS]; omega
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_zip, List.getElem_zip]
  have hgd : (runSums (hdrD (Q := Q) cl) (laneD p y cl))[N']'(by omega) =
      ((hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum,
        (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum) := by
    rw [← List.getD_eq_getElem _ (0, 0) _]; exact hkey
  refine ⟨?_, ?_⟩ <;> dsimp only <;> rw [hgd]

theorem qSlot_H (y : Q) (o : PrimOp) (cs : List ℤ) (hb : ∀ q ∈ cs, 0 ≤ q ∧ q ≤ 1) :
    hornerQ1 y (qSlot o true cs).words = evR y cs := by
  have hws : zl (cs.map Int.toNat) = cs := by
    unfold zl
    rw [List.map_map]
    conv_rhs => rw [← List.map_id cs]
    apply List.map_congr_left
    intro q hq
    simp [Int.toNat_of_nonneg (hb q hq).1]
  have hb' : ∀ a ∈ cs.map Int.toNat, a ≤ 1 := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    have := hb q hq
    omega
  simp only [qSlot, if_true]
  split_ifs with h
  · have : cs = [] := List.map_eq_nil_iff.mp h
    subst this
    simp [hornerQ1, packV, bitOf, evR]
  · rw [hornerQ1_packQ1 y _ (cs.map Int.toNat) le_rfl hb', hws]

theorem slotD_nf (p : ℕ) (y : Q) (cl : CallL) (s : SlotL) (h : isF2 cl.op s = false) :
    AluHonestRows.slotD p y cl s = ((s.cf1 : Q) * slotL y s, (s.cf2 : Q) * slotL y s) := by
  unfold AluHonestRows.slotD
  simp [h]

theorem isF2_false (o : PrimOp) (s : SlotL) (h : o = .add ∨ o = .sub ∨ o = .lt) : isF2 o s = false := by
  rcases h with rfl | rfl | rfl <;> simp [isF2]

theorem slotL_of_mode_le (y : Q) (s : SlotL) (h : s.mode ≤ 3) : slotL y s = evR y (zl s.vw) := by
  unfold slotL
  rw [if_neg (by omega)]
  rfl

theorem slotL_q (y : Q) (o : PrimOp) (cs : List ℤ) :
    slotL y (qSlot o true cs) = (y - (Bn : Q)) * hornerQ1 y (qSlot o true cs).words := by
  unfold slotL slotH
  have : (qSlot o true cs).mode = 4 := by simp [qSlot]
  simp [this]

theorem evR_map_mul (y : Q) (c : ℤ) : ∀ l : List ℤ, evR y (l.map (c * ·)) = (c : Q) * evR y l
  | [] => by simp [evR]
  | a :: l => by simp only [List.map_cons, evR, evR_map_mul y c l]; push_cast; ring

theorem evB_map_mul (B c : ℤ) : ∀ l : List ℤ, evB B (l.map (c * ·)) = c * evB B l
  | [] => by simp [evB]
  | a :: l => by simp only [List.map_cons, evB, evB_map_mul B c l]; ring

theorem evR_single (y : Q) (e : ℤ) : evR y [e] = (e : Q) := by simp [evR]
theorem evB_single (B e : ℤ) : evB B [e] = e := by simp [evB]

theorem handleSlot_cf1 (p : ℕ) (o : PrimOp) (lb r v k s : ℕ) :
    (handleSlot p o lb r v k s).cf1 = (coefOf o lb (some r)).1 := by
  unfold handleSlot; split_ifs <;> rfl

theorem handleSlot_facts {p : ℕ} (hpG : p = Nock.Atoms.p) (o : PrimOp) (lb r v k s : ℕ) :
    (∀ a ∈ (handleSlot p o lb r v k s).vw, a < Bn) ∧ Nock.Atoms.val (handleSlot p o lb r v k s).vw = v := by
  rw [handleSlot_vw]
  split_ifs with h
  · exact ⟨splitOf_lt hpG h, val_splitOf v⟩
  · exact ⟨limbs_lt v, Nock.Atoms.val_limbs v⟩

end QRows

/-! ## 10. Integer bounds of the carries -/

theorem mem_zl_bounds {l : List ℕ} (hl : ∀ a ∈ l, a < Bn) : ∀ x ∈ zl l, 0 ≤ x ∧ x ≤ (Bn : ℤ) - 1 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have := hl a ha
  simp only [Int.ofNat_eq_natCast]
  omega

theorem bound_pm (X Y Z : List ℕ) (hX : ∀ a ∈ X, a < Bn) (hY : ∀ a ∈ Y, a < Bn) (hZ : ∀ a ∈ Z, a < Bn) :
    ∀ d ∈ addL (addL (zl X) (zl Y)) (negL (zl Z)), -(Bn : ℤ) < d ∧ d + 1 < (Bn : ℤ) * (1 + 1) := by
  have bX := mem_zl_bounds hX
  have bY := mem_zl_bounds hY
  have bZ := mem_zl_bounds hZ
  apply mem_addL_bound
  intro x hx z hz
  have hx' : 0 ≤ x ∧ x ≤ 2 * (Bn : ℤ) - 2 := by
    rcases hx with rfl | hx
    · have : (0 : ℤ) < Bn := by norm_num [Bn]
      omega
    · have := mem_addL_bound (fun d => 0 ≤ d ∧ d ≤ 2 * (Bn : ℤ) - 2) (zl X) (zl Y) (by
        intro x' hx' z' hz'
        have a1 : 0 ≤ x' ∧ x' ≤ (Bn : ℤ) - 1 := by
          rcases hx' with rfl | h
          · have : (0 : ℤ) < Bn := by norm_num [Bn]
            omega
          · exact bX x' h
        have a2 : 0 ≤ z' ∧ z' ≤ (Bn : ℤ) - 1 := by
          rcases hz' with rfl | h
          · have : (0 : ℤ) < Bn := by norm_num [Bn]
            omega
          · exact bY z' h
        omega) x hx
      exact this
  have hz' : -((Bn : ℤ) - 1) ≤ z ∧ z ≤ 0 := by
    rcases hz with rfl | hz
    · have : (0 : ℤ) < Bn := by norm_num [Bn]
      omega
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have := bZ w hw
      omega
  omega

theorem bound_lt_X (sgn : ℤ) (hs : sgn = 1 ∨ sgn = -1) (A B D : List ℕ) (hA : ∀ a ∈ A, a < Bn)
    (hB : ∀ a ∈ B, a < Bn) (hD : ∀ a ∈ D, a < Bn) :
    ∀ x ∈ addL (addL ((zl A).map (sgn * ·)) ((zl B).map (-sgn * ·))) (zl D),
      -((Bn : ℤ) - 1) ≤ x ∧ x ≤ 2 * (Bn : ℤ) - 2 := by
  have bA := mem_zl_bounds hA
  have bB := mem_zl_bounds hB
  have bD := mem_zl_bounds hD
  have hBp : (0 : ℤ) < Bn := by norm_num [Bn]
  apply mem_addL_bound
  intro x hx z hz
  have hx' : -((Bn : ℤ) - 1) ≤ x ∧ x ≤ (Bn : ℤ) - 1 := by
    rcases hx with rfl | hx
    · omega
    · exact mem_addL_bound (fun d => -((Bn : ℤ) - 1) ≤ d ∧ d ≤ (Bn : ℤ) - 1) _ _ (by
        intro x' hx' z' hz'
        have a1 : ∀ w ∈ (zl A).map (sgn * ·), -((Bn : ℤ) - 1) ≤ w ∧ w ≤ (Bn : ℤ) - 1 := by
          intro w hw
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          have := bA u hu
          rcases hs with rfl | rfl <;> omega
        have a2 : ∀ w ∈ (zl B).map (-sgn * ·), -((Bn : ℤ) - 1) ≤ w ∧ w ≤ (Bn : ℤ) - 1 := by
          intro w hw
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          have := bB u hu
          rcases hs with rfl | rfl <;> omega
        have a3 : ∀ w ∈ (zl A).map (sgn * ·), ∀ w' ∈ (zl B).map (-sgn * ·), -((Bn : ℤ) - 1) ≤ w + w' ∧ w + w' ≤ (Bn : ℤ) - 1 := by
          intro w hw w' hw'
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
          obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hw'
          have := bA u hu
          have := bB u' hu'
          rcases hs with rfl | rfl <;> omega
        rcases hx' with rfl | h1
        · rcases hz' with rfl | h2
          · omega
          · have := a2 z' h2; omega
        · rcases hz' with rfl | h2
          · have := a1 x' h1; omega
          · exact a3 x' h1 z' h2) x hx
  have hz' : 0 ≤ z ∧ z ≤ (Bn : ℤ) - 1 := by
    rcases hz with rfl | hz
    · omega
    · exact bD z hz
  omega

/-- **The lt carries are bits** (position-aware: the `+[1 − lb]` lands on the head). -/
theorem carries_lt_bits (X : List ℤ) (e : ℤ) (he : 0 ≤ e ∧ e ≤ 1)
    (hX : ∀ x ∈ X, -((Bn : ℤ) - 1) ≤ x ∧ x ≤ 2 * (Bn : ℤ) - 2)
    (hid : evB (Bn : ℤ) (addL X [e]) = 0) : ∀ q ∈ carr (Bn : ℤ) 0 (addL X [e]), 0 ≤ q ∧ q ≤ 1 := by
  have hBp : (0 : ℤ) < Bn := by norm_num [Bn]
  rw [addL_single] at hid ⊢
  have h0 : X.headD 0 = 0 ∨ X.headD 0 ∈ X := by
    cases X with
    | nil => left; rfl
    | cons x xs => right; simp
  have hx0 : -((Bn : ℤ) - 1) ≤ X.headD 0 ∧ X.headD 0 ≤ 2 * (Bn : ℤ) - 2 := by
    rcases h0 with h | h
    · rw [h]; omega
    · exact hX _ h
  refine carr_bound_head hBp (by norm_num) (X.headD 0 + e) X.tail hid ⟨by omega, by omega⟩ ?_
  intro d hd
  have := hX d (List.mem_of_mem_tail hd)
  omega

/-! ## 11. The integer identities and the terminal sums -/

theorem slA_facts {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) :
    (∀ a ∈ (slA p cl).vw, a < Bn) ∧ Nock.Atoms.val (slA p cl).vw = cl.a := handleSlot_facts hpG _ _ _ _ _ _
theorem slB_facts {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) :
    (∀ a ∈ (slB p cl).vw, a < Bn) ∧ Nock.Atoms.val (slB p cl).vw = cl.b := handleSlot_facts hpG _ _ _ _ _ _
theorem slC_facts {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) :
    (∀ a ∈ (slC p cl).vw, a < Bn) ∧ Nock.Atoms.val (slC p cl).vw = cl.c := handleSlot_facts hpG _ _ _ _ _ _
theorem slD_facts (cl : CallL) :
    (∀ a ∈ (slD cl).vw, a < Bn) ∧ Nock.Atoms.val (slD cl).vw = ltWit cl.a cl.b :=
  ⟨wordsOf_lt _, val_wordsOf _⟩

theorem ds_add_id {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .add) :
    evB (Bn : ℤ) (dsAdd p cl) = 0 := by
  have hs := hcl.sem
  rw [h] at hs
  simp only [Nock.Jet.Prim.primSem, Option.some.injEq] at hs
  unfold dsAdd
  rw [evB_addL, evB_addL, evB_negL, evB_zl, evB_zl, evB_zl, (slA_facts hpG cl).2, (slB_facts hpG cl).2,
    (slC_facts hpG cl).2]
  omega

theorem ds_sub_id {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .sub) :
    evB (Bn : ℤ) (dsSub p cl) = 0 := by
  have hs := hcl.sem
  rw [h] at hs
  simp only [Nock.Jet.Prim.primSem] at hs
  split_ifs at hs with hb
  · simp only [Option.some.injEq] at hs
    unfold dsSub
    rw [evB_addL, evB_addL, evB_negL, evB_zl, evB_zl, evB_zl, (slA_facts hpG cl).2, (slB_facts hpG cl).2,
      (slC_facts hpG cl).2]
    omega

theorem lbv_lt (cl : CallL) (h : cl.op = .lt) : cl.lbv = cl.c := by simp [CallL.lbv, h]

theorem lt_sem (cl : CallL) (hcl_sem : Nock.Jet.Prim.primSem cl.op cl.a cl.b = some cl.c) (h : cl.op = .lt) :
    (cl.a < cl.b ∧ cl.c = 0) ∨ (cl.b ≤ cl.a ∧ cl.c = 1) := by
  rw [h] at hcl_sem
  simp only [Nock.Jet.Prim.primSem, Option.some.injEq] at hcl_sem
  by_cases hab : cl.a < cl.b
  · left; simp [hab] at hcl_sem; exact ⟨hab, hcl_sem.symm⟩
  · right; simp [hab] at hcl_sem; exact ⟨by omega, hcl_sem.symm⟩

theorem ds_lt_id {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .lt) :
    evB (Bn : ℤ) (dsLt p cl) = 0 := by
  have hl := lt_sem cl hcl.sem h
  have hlb := lbv_lt cl h
  unfold dsLt
  rw [evB_addL, evB_addL, evB_addL, evB_map_mul, evB_map_mul, evB_single, evB_zl, evB_zl, evB_zl,
    (slA_facts hpG cl).2, (slB_facts hpG cl).2, (slD_facts cl).2]
  rcases hl with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rw [hlb, hc]
    have : ltWit cl.a cl.b = cl.b - cl.a - 1 := by simp [ltWit, hab]
    rw [this]
    push_cast
    omega
  · rw [hlb, hc]
    have : ltWit cl.a cl.b = cl.a - cl.b := by simp [ltWit, not_lt.mpr hab]
    rw [this]
    push_cast
    omega

theorem carries_add {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .add) :
    ∀ q ∈ carr (Bn : ℤ) 0 (dsAdd p cl), 0 ≤ q ∧ q ≤ 1 :=
  carr_bound0 (by norm_num [Bn]) (by norm_num) _ (ds_add_id hpG cl hcl h)
    (bound_pm _ _ _ (slA_facts hpG cl).1 (slB_facts hpG cl).1 (slC_facts hpG cl).1)

theorem carries_sub {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .sub) :
    ∀ q ∈ carr (Bn : ℤ) 0 (dsSub p cl), 0 ≤ q ∧ q ≤ 1 :=
  carr_bound0 (by norm_num [Bn]) (by norm_num) _ (ds_sub_id hpG cl hcl h)
    (bound_pm _ _ _ (slB_facts hpG cl).1 (slC_facts hpG cl).1 (slA_facts hpG cl).1)

theorem carries_lt {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .lt) :
    ∀ q ∈ carr (Bn : ℤ) 0 (dsLt p cl), 0 ≤ q ∧ q ≤ 1 := by
  have hl := lt_sem cl hcl.sem h
  have hlb := lbv_lt cl h
  have hid := ds_lt_id hpG cl hcl h
  unfold dsLt at hid ⊢
  have hsg : (1 - 2 * (cl.lbv : ℤ)) = 1 ∨ (1 - 2 * (cl.lbv : ℤ)) = -1 := by
    rcases hl with ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [hlb, hc] <;> simp
  refine carries_lt_bits _ _ ?_ ?_ hid
  · rcases hl with ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [hlb, hc] <;> simp
  · exact bound_lt_X _ hsg _ _ _ (slA_facts hpG cl).1 (slB_facts hpG cl).1 (slD_facts cl).1

theorem slA_mode (p : ℕ) (cl : CallL) : (slA p cl).mode ≤ 3 := handleSlot_mode_le ..
theorem slB_mode (p : ℕ) (cl : CallL) : (slB p cl).mode ≤ 3 := handleSlot_mode_le ..
theorem slC_mode (p : ℕ) (cl : CallL) : (slC p cl).mode ≤ 3 := handleSlot_mode_le ..
theorem slD_mode (cl : CallL) : (slD cl).mode ≤ 3 := by simp [slD, witSlot]

theorem slotOK_cf2 {o : PrimOp} {lb : ℕ} {s : SlotL} (ho : o = .add ∨ o = .sub ∨ o = .lt) (h : SlotOK o lb s) :
    s.cf2 = 0 := by
  rcases h with ⟨r, hr, -, -, -, hc⟩ | ⟨-, -, -, hc⟩
  · rw [hc]; interval_cases r <;> rcases ho with rfl | rfl | rfl <;> simp [coefOf]
  · rw [hc]; rcases ho with rfl | rfl | rfl <;> simp [coefQ1]

section Terminal
variable {Q : Type} [CommRing Q]

theorem hdrD_ne_lt (cl : CallL) (h : cl.op = .add ∨ cl.op = .sub) :
    (hdrD (Q := Q) cl).1 = 0 ∧ (hdrD (Q := Q) cl).2 = 0 := by
  rcases h with h | h <;> simp [hdrD, h]

/-- **`S2` terminal**: no `cf2` anywhere. -/
theorem S2_terminal (p : ℕ) (cl : CallL) (y : Q) (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum = 0 := by
  obtain ⟨s1, s2, s3, s4, hss, sh⟩ := shape_A p cl hop
  have hF := fun s => isF2_false cl.op s hop
  rw [hss]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [slotD_nf p y cl s1 (hF _), slotD_nf p y cl s2 (hF _), slotD_nf p y cl s3 (hF _), slotD_nf p y cl s4 (hF _),
    slotOK_cf2 hop sh.ok1, slotOK_cf2 hop sh.ok2, slotOK_cf2 hop sh.ok3, slotOK_cf2 hop sh.ok4]
  have : (hdrD (Q := Q) cl).2 = 0 := by rcases hop with h | h | h <;> simp [hdrD, h]
  simp [this]

theorem Bcast (B : ℤ) : ((B : ℤ) : Q) = (B : Q) := rfl

theorem S1_add {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .add) (y : Q) :
    (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum = 0 := by
  have hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt := Or.inl h
  have hF := fun s => isF2_false cl.op s hop
  have hid := ds_add_id hpG cl hcl h
  have hcid := carry_id (R := Q) (B := (Bn : ℤ)) (by norm_num [Bn]) y (dsAdd p cl) hid
  have hH := qSlot_H y .add (carr (Bn : ℤ) 0 (dsAdd p cl)) (carries_add hpG cl hcl h)
  rw [slotsOf_add p cl h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _)]
  rw [slotL_of_mode_le y _ (slA_mode p cl), slotL_of_mode_le y _ (slB_mode p cl),
    slotL_of_mode_le y _ (slC_mode p cl), slotL_q, hH]
  have e1 : (slA p cl).cf1 = 1 := by simp [slA, handleSlot_cf1, h, coefOf]
  have e2 : (slB p cl).cf1 = 1 := by simp [slB, handleSlot_cf1, h, coefOf]
  have e3 : (slC p cl).cf1 = -1 := by simp [slC, handleSlot_cf1, h, coefOf]
  have e4 : (qSlot .add true (carr (Bn : ℤ) 0 (dsAdd p cl))).cf1 = 1 := by simp [qSlot, coefQ1]
  have hd0 := (hdrD_ne_lt (Q := Q) cl (Or.inl h)).1
  have hev : evR y (dsAdd p cl) = evR y (zl (slA p cl).vw) + evR y (zl (slB p cl).vw) - evR y (zl (slC p cl).vw) := by
    unfold dsAdd; rw [evR_addL, evR_addL, evR_negL]; ring
  rw [e1, e2, e3, e4, hd0]
  rw [hev] at hcid
  have hB : ((Bn : ℤ) : Q) = (Bn : Q) := Int.cast_natCast Bn
  rw [hB] at hcid
  push_cast
  linear_combination hcid

theorem S1_sub {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .sub) (y : Q) :
    (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum = 0 := by
  have hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt := Or.inr (Or.inl h)
  have hF := fun s => isF2_false cl.op s hop
  have hid := ds_sub_id hpG cl hcl h
  have hcid := carry_id (R := Q) (B := (Bn : ℤ)) (by norm_num [Bn]) y (dsSub p cl) hid
  have hH := qSlot_H y .sub (carr (Bn : ℤ) 0 (dsSub p cl)) (carries_sub hpG cl hcl h)
  rw [slotsOf_sub p cl h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _)]
  rw [slotL_of_mode_le y _ (slA_mode p cl), slotL_of_mode_le y _ (slB_mode p cl),
    slotL_of_mode_le y _ (slC_mode p cl), slotL_q, hH]
  have e1 : (slA p cl).cf1 = -1 := by simp [slA, handleSlot_cf1, h, coefOf]
  have e2 : (slB p cl).cf1 = 1 := by simp [slB, handleSlot_cf1, h, coefOf]
  have e3 : (slC p cl).cf1 = 1 := by simp [slC, handleSlot_cf1, h, coefOf]
  have e4 : (qSlot .sub true (carr (Bn : ℤ) 0 (dsSub p cl))).cf1 = 1 := by simp [qSlot, coefQ1]
  have hd0 := (hdrD_ne_lt (Q := Q) cl (Or.inr h)).1
  have hev : evR y (dsSub p cl) = evR y (zl (slB p cl).vw) + evR y (zl (slC p cl).vw) - evR y (zl (slA p cl).vw) := by
    unfold dsSub; rw [evR_addL, evR_addL, evR_negL]; ring
  rw [e1, e2, e3, e4, hd0]
  rw [hev] at hcid
  have hB : ((Bn : ℤ) : Q) = (Bn : Q) := Int.cast_natCast Bn
  rw [hB] at hcid
  push_cast
  linear_combination hcid

theorem S1_lt {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) (h : cl.op = .lt) (y : Q) :
    (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum = 0 := by
  have hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt := Or.inr (Or.inr h)
  have hF := fun s => isF2_false cl.op s hop
  have hid := ds_lt_id hpG cl hcl h
  have hcid := carry_id (R := Q) (B := (Bn : ℤ)) (by norm_num [Bn]) y (dsLt p cl) hid
  have hH := qSlot_H y .lt (carr (Bn : ℤ) 0 (dsLt p cl)) (carries_lt hpG cl hcl h)
  rw [slotsOf_lt p cl h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _), slotD_nf p y cl _ (hF _)]
  rw [slotL_of_mode_le y _ (slA_mode p cl), slotL_of_mode_le y _ (slB_mode p cl),
    slotL_of_mode_le y _ (slD_mode cl), slotL_q, hH]
  have e1 : (slA p cl).cf1 = 1 - 2 * (cl.lbv : ℤ) := by simp [slA, handleSlot_cf1, h, coefOf]
  have e2 : (slB p cl).cf1 = -(1 - 2 * (cl.lbv : ℤ)) := by simp [slB, handleSlot_cf1, h, coefOf]
  have e3 : (slD cl).cf1 = 1 := by simp [slD, witSlot, h, coefOf]
  have e4 : (qSlot .lt true (carr (Bn : ℤ) 0 (dsLt p cl))).cf1 = 1 := by simp [qSlot, coefQ1]
  have hd0 : (hdrD (Q := Q) cl).1 = 1 - (cl.lbv : Q) := by simp [hdrD, h]
  have hev : evR y (dsLt p cl) = ((1 - 2 * (cl.lbv : ℤ) : ℤ) : Q) * evR y (zl (slA p cl).vw) +
      ((-(1 - 2 * (cl.lbv : ℤ)) : ℤ) : Q) * evR y (zl (slB p cl).vw) + evR y (zl (slD cl).vw) +
      ((1 - (cl.lbv : ℤ) : ℤ) : Q) := by
    unfold dsLt; rw [evR_addL, evR_addL, evR_addL, evR_map_mul, evR_map_mul, evR_single]
  rw [e1, e2, e3, e4, hd0]
  rw [hev] at hcid
  have hB : ((Bn : ℤ) : Q) = (Bn : Q) := Int.cast_natCast Bn
  rw [hB] at hcid
  push_cast at hcid ⊢
  linear_combination hcid

/-- **The terminal sums vanish** for `add` / `sub` / `lt`: the hdr contribution plus the slots' contributions. -/
theorem S_terminal {p : ℕ} (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl)
    (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) (y : Q) :
    (hdrD (Q := Q) cl).1 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).1).sum = 0 ∧
    (hdrD (Q := Q) cl).2 + ((slotsOf p cl).map fun s => (AluHonestRows.slotD p y cl s).2).sum = 0 := by
  refine ⟨?_, S2_terminal p cl y hop⟩
  rcases hop with h | h | h
  · exact S1_add hpG cl hcl h y
  · exact S1_sub hpG cl hcl h y
  · exact S1_lt hpG cl hcl h y

end Terminal

section TermQ

variable {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

theorem kvec_pair (q : QRow (Quad (algebraMap F K δ))) (r : ℕ) (hr : r % 2 = 0) :
    Quad.mk (algebraMap F K δ) (kvec δ q r) (kvec δ q (r + 1)) = q.role r := by
  have h1 : r - r % 2 = r := by omega
  have h2 : (r + 1) - (r + 1) % 2 = r := by omega
  have h3 : (r + 1) % 2 ≠ 0 := by omega
  simp only [kvec, h1, h2, hr, h3, if_true, if_false]
  exact Quad.mk_re_im (algebraMap F K δ) (q.role r)

/-- The two terminal `𝕂'` equations of `identQ`: `(1 - sL')*S1 = 0`, `(1 - sL')*S2 = 0`. -/
def termQ {F : Type} [Field F] (δF : F) : List (QE F) :=
  [ QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S1),
    QE.scale (notE (nv AluSZChipJ9.sL)) (QE.var AluSZChipJ9.S2) ]

/-- They are the last two equations of `identQ`. -/
theorem termQ_eq_drop : (AluSZChipJ9.identQ δ : List (QE F)).drop 23 = termQ δ := rfl

/-- `termQ` is a sub-list of `identQ`. -/
theorem termQ_sub : ∀ e ∈ (termQ δ : List (QE F)), e ∈ (AluSZChipJ9.identQ δ : List (QE F)) := fun e he => by
  rw [← termQ_eq_drop δ] at he
  exact List.mem_of_mem_drop he

/-- Every row of the slot rows has `sL = 1`. -/
theorem rowsOf_sL (p : ℕ) (cl : CallL) (r : BRow F) (hr : r ∈ rowsOf (slotRow (F := F) p cl) (slotsOf p cl)) :
    r.sL = 1 := by
  simp only [rowsOf, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨s, _, i, _, rfl⟩ := hr
  rfl

/-- **`QSat` of the terminal equations** for `add` / `sub` / `lt`. -/
theorem qSat_term_A (p : ℕ) (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl)
    (hop : cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) :
    QSat (K := K) δ p cl (termQ δ : List (QE F)) := by
  intro y chal hy hp j hj nxt hn nq hq e he
  obtain ⟨s1, s2, s3, s4, hss, sh⟩ := shape_A p cl hop
  have hsl : ∀ s ∈ slotsOf p cl, 0 < s.words.length := by
    rw [hss]; intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [sh.n1, sh.n2, sh.n3, sh.n4]
  have hN : 0 < ((slotsOf p cl).map (·.words.length)).sum := by
    rw [hss]; have := sh.n1; simp; omega
  have hlen : (blockB (F := F) p cl).length = ((slotsOf p cl).map (·.words.length)).sum + 1 := by
    rw [blockB_eq]; simp [rowsOf_length]
  simp only [termQ, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  by_cases hl : j + 1 < (blockB (F := F) p cl).length
  · have hsL : nxt.sL = 1 := by
      rw [hn.1 hl, blockB_eq, List.getD_cons_succ]
      have hlt : j < (rowsOf (slotRow (F := F) p cl) (slotsOf p cl)).length := by
        rw [blockB_eq] at hl; simpa using hl
      rw [List.getD_eq_getElem _ _ hlt]
      exact rowsOf_sL p cl _ (List.getElem_mem hlt)
    rcases he with rfl | rfl <;>
    · rw [ev_scale]; simp [CoeffExpr.eval, envB, hsL]
  · have hjN : j = ((slotsOf p cl).map (·.words.length)).sum := by omega
    obtain ⟨b1, b2⟩ := blockQ_getD_last p y cl hsl hN
    have t := S_terminal (Q := Quad (algebraMap F K δ)) hpG cl hcl hop y
    subst hjN
    rcases he with rfl | rfl
    · have hk := kvec_pair δ ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero)
        AluSZChipJ9.S1 (by decide)
      have hrole : ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).role AluSZChipJ9.S1 =
          ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S1 := by
        simp [QRow.role, AluSZChipJ9.S1]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b1, t.1, mul_zero]
    · have hk := kvec_pair δ ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero)
        AluSZChipJ9.S2 (by decide)
      have hrole : ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).role AluSZChipJ9.S2 =
          ((blockQ p y cl).getD ((slotsOf p cl).map (·.words.length)).sum QRow.zero).S2 := by
        simp [QRow.role, AluSZChipJ9.S2]
      rw [ev_scale, ev_var]
      dsimp only
      rw [hk, hrole, b2, t.2, mul_zero]

end TermQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatA
