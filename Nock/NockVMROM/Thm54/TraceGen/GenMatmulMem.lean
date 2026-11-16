/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulMem.lean

  Memory-side local validity for generated forests.

  `genAnnotatedNounWalk` / axis-2/3 record trees / `genMemForestFromTree_of_rowOK`
  already live in `GenTierAMem`.  This file adds the missing well-formed
  induction on `genAnnotatedDescent`: a record tree is locally valid when
  the builder's axis-path target equals the request child.

  Formula-open records (`@2` / `@3`) are well-formed by construction, so
  `OP_1` / quote / cons / `OP_4` / `OP_5` / `OP_6` / `OP_7` constructor
  forests inhabit `MemoryNodesOK` via the existing axis-2/3 lemmas.

  Deep `OP_0` / `OP_9` arm-fetch records are discharged when
  `lsbTarget` matches the slot child.  The annotated builder walks
  paper `axisPath` (MSB-first), matching `Noun.slot` via
  `lsbTarget_of_slot`.

  Every tree of `genMemForestFromTree (encC z) z α (bfsAssign mmTree)`
  inhabits `MemoryNodesOK` (`mmMemForest_OK`): request well-formedness
  is fuel induction on `genComputeSkeleton`, stamps from `bfsAssign`
  do not change root/child/axis, and `genRowMemForest_wf_OK` covers
  singleton, independent, and chained rows.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

set_option maxHeartbeats 400000

/-! ## LSB target of the annotated builder -/

/-- Noun reached by the annotated descent: paper `axisPath` (MSB-first),
    `formulaTail` on `axisTopBit`, `formulaHead` otherwise, halt at `ax < 2`. -/
def lsbTarget (n : Noun) (ax : ℕ) : Noun :=
  if ax < 2 then n
  else if axisTopBit ax then lsbTarget (formulaTail n) (axisRest ax)
  else lsbTarget (formulaHead n) (axisRest ax)
termination_by ax
decreasing_by
  all_goals
    apply axisRest_lt
    omega

theorem lsbTarget_of_lt2 (n : Noun) {ax : ℕ} (h : ax < 2) :
    lsbTarget n ax = n := by
  unfold lsbTarget
  simp [h]

theorem lsbTarget_of_head (n : Noun) {ax : ℕ} (h2 : 2 ≤ ax)
    (hh : axisTopBit ax = false) :
    lsbTarget n ax = lsbTarget (formulaHead n) (axisRest ax) := by
  conv => lhs; unfold lsbTarget
  have hlt : ¬ ax < 2 := by omega
  simp [hlt, hh]

theorem lsbTarget_of_tail (n : Noun) {ax : ℕ} (h2 : 2 ≤ ax)
    (ht : axisTopBit ax = true) :
    lsbTarget n ax = lsbTarget (formulaTail n) (axisRest ax) := by
  conv => lhs; unfold lsbTarget
  have hlt : ¬ ax < 2 := by omega
  simp [hlt, ht]

theorem lsbTarget_axis3 (hd tl : Noun) : lsbTarget (.cell hd tl) 3 = tl := by
  rw [lsbTarget_of_tail (.cell hd tl) (ax := 3) (by omega) axisTopBit_three]
  simp [formulaTail, axisRest_three]
  exact lsbTarget_of_lt2 (ax := 1) tl (by omega)

theorem lsbTarget_axis2 (hd tl : Noun) : lsbTarget (.cell hd tl) 2 = hd := by
  rw [lsbTarget_of_head (.cell hd tl) (ax := 2) (by omega) axisTopBit_two]
  simp [formulaHead, axisRest_two]
  exact lsbTarget_of_lt2 (ax := 1) hd (by omega)

theorem lsbTarget_axis4 (a b c : Noun) :
    lsbTarget (.cell (.cell a b) c) 4 = a := by
  rw [lsbTarget_of_head (.cell (.cell a b) c) (ax := 4) (by omega) axisTopBit_four]
  simp [formulaHead, axisRest_four]
  exact lsbTarget_axis2 a b

theorem lsbTarget_axis8 (a b c d : Noun) :
    lsbTarget (.cell (.cell (.cell a b) c) d) 8 = a := by
  rw [lsbTarget_of_head (.cell (.cell (.cell a b) c) d) (ax := 8)
    (by omega) axisTopBit_eight]
  simp [formulaHead, axisRest_eight]
  exact lsbTarget_axis4 a b c

theorem lsbTarget_of_slot1 (n r : Noun) (h : Noun.slot 1 n = some r) :
    lsbTarget n 1 = r := by
  simp [Noun.slot] at h
  subst r
  exact lsbTarget_of_lt2 (ax := 1) n (by omega)

theorem lsbTarget_of_slot2 (n r : Noun) (h : Noun.slot 2 n = some r) :
    lsbTarget n 2 = r := by
  cases n with
  | atom a => simp [Noun.slot] at h
  | cell hd tl =>
    simp [Noun.slot] at h
    subst r
    exact lsbTarget_axis2 hd tl

theorem lsbTarget_of_slot3 (n r : Noun) (h : Noun.slot 3 n = some r) :
    lsbTarget n 3 = r := by
  cases n with
  | atom a => simp [Noun.slot] at h
  | cell hd tl =>
    simp [Noun.slot] at h
    subst r
    exact lsbTarget_axis3 hd tl

theorem lsbTarget_of_slot4 (n r : Noun) (h : Noun.slot 4 n = some r) :
    lsbTarget n 4 = r := by
  cases n with
  | atom a => simp [Noun.slot] at h
  | cell hd tl =>
    cases hd with
    | atom a => simp [Noun.slot] at h
    | cell a b =>
      simp [Noun.slot] at h
      subst r
      exact lsbTarget_axis4 a b tl

theorem lsbTarget_of_slot8 (n r : Noun) (h : Noun.slot 8 n = some r) :
    lsbTarget n 8 = r := by
  cases n with
  | atom a => simp [Noun.slot] at h
  | cell hd tl =>
    cases hd with
    | atom a => simp [Noun.slot] at h
    | cell a b =>
      cases a with
      | atom x => simp [Noun.slot] at h
      | cell x y =>
        simp [Noun.slot] at h
        subst r
        exact lsbTarget_axis8 x y b tl

/-! ## `Noun.slot` vs paper `axisPath` -/

theorem log2_div2 {a : ℕ} (h : 2 ≤ a) : a.log2 = (a / 2).log2 + 1 := by
  rw [Nat.log2_def]
  split
  · rfl
  · omega

theorem two_mul_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  rw [Nat.mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk]

theorem axisTopBit_iff {a : ℕ} :
    axisTopBit a = true ↔ 3 * 2 ^ (a.log2 - 1) ≤ a := by
  unfold axisTopBit
  split_ifs <;> simp_all

theorem axisRest_eq {a : ℕ} :
    axisRest a =
      if axisTopBit a then a - 2 ^ a.log2 else a - 2 ^ (a.log2 - 1) := by
  by_cases h : axisTopBit a = true
  · rw [if_pos h]
    unfold axisRest
    have hc : 3 * 2 ^ (a.log2 - 1) ≤ a := axisTopBit_iff.mp h
    simp [hc]
  · rw [if_neg h]
    unfold axisRest
    have hc : ¬ 3 * 2 ^ (a.log2 - 1) ≤ a := (not_congr axisTopBit_iff).mp h
    simp [hc]

theorem axisTopBit_div2 {a : ℕ} (h : 4 ≤ a) :
    axisTopBit a = axisTopBit (a / 2) := by
  have h2 : 2 ≤ a := by omega
  have hhalf : 2 ≤ a / 2 := by omega
  have hlog : a.log2 = (a / 2).log2 + 1 := log2_div2 h2
  have hk : 1 ≤ (a / 2).log2 := log2_ge_one hhalf
  have hx : a.log2 - 1 = (a / 2).log2 := by omega
  have hpow := two_mul_pow_pred hk
  have hiff :
      3 * 2 ^ ((a / 2).log2 - 1) ≤ a / 2 ↔
        3 * 2 ^ (a.log2 - 1) ≤ a := by
    rw [hx]
    have hmul :
        (3 * 2 ^ ((a / 2).log2 - 1)) * 2 = 3 * 2 ^ (a / 2).log2 := by
      rw [Nat.mul_assoc, Nat.mul_comm (2 ^ ((a / 2).log2 - 1)) 2, ← hpow]
    constructor
    · intro hh
      have := (Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 2)).mp hh
      rwa [hmul] at this
    · intro hh
      exact (Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 2)).mpr
        (by rwa [hmul])
  apply Bool.eq_iff_iff.mpr
  rw [axisTopBit_iff, axisTopBit_iff, hiff]

theorem axisRest_div2 {a : ℕ} (h : 4 ≤ a) :
    axisRest a = 2 * axisRest (a / 2) + a % 2 := by
  have h2 : 2 ≤ a := by omega
  have hhalf : 2 ≤ a / 2 := by omega
  have hlog : a.log2 = (a / 2).log2 + 1 := log2_div2 h2
  have hk : 1 ≤ (a / 2).log2 := log2_ge_one hhalf
  have hpowk : 2 ^ a.log2 = 2 * 2 ^ (a / 2).log2 := by
    rw [hlog, Nat.pow_succ, Nat.mul_comm]
  have hpowk1 : 2 ^ (a.log2 - 1) = 2 ^ (a / 2).log2 := by
    have : a.log2 - 1 = (a / 2).log2 := by omega
    rw [this]
  have hmod : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hbit := axisTopBit_div2 h
  rw [axisRest_eq, axisRest_eq, ← hbit]
  by_cases ht : axisTopBit a = true
  · simp [ht]
    have hle : 2 ^ (a / 2).log2 ≤ a / 2 :=
      two_pow_log2_le (a / 2) (by omega)
    calc
      a - 2 ^ a.log2
          = 2 * (a / 2) + a % 2 - 2 * 2 ^ (a / 2).log2 := by
            nth_rw 1 [hmod]; rw [hpowk]
      _ = 2 * (a / 2 - 2 ^ (a / 2).log2) + a % 2 := by
            rw [Nat.mul_sub_left_distrib]; omega
  · simp [ht]
    have hle : 2 ^ ((a / 2).log2 - 1) ≤ a / 2 := by
      have : 2 ^ (a / 2).log2 ≤ a / 2 :=
        two_pow_log2_le (a / 2) (by omega)
      have : 2 ^ ((a / 2).log2 - 1) ≤ 2 ^ (a / 2).log2 :=
        Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      omega
    have hpred := two_mul_pow_pred hk
    calc
      a - 2 ^ (a.log2 - 1)
          = 2 * (a / 2) + a % 2 - 2 ^ (a / 2).log2 := by
            nth_rw 1 [hmod]; rw [hpowk1]
      _ = 2 * (a / 2 - 2 ^ ((a / 2).log2 - 1)) + a % 2 := by
            rw [hpred, Nat.mul_sub_left_distrib]; omega

theorem axisRest_pos {a : ℕ} (h : 2 ≤ a) : 1 ≤ axisRest a := by
  have hk : 1 ≤ a.log2 := log2_ge_one h
  have hpow : 2 ^ a.log2 ≤ a := two_pow_log2_le a (by omega)
  have hhalf : 2 ^ (a.log2 - 1) ≤ 2 ^ a.log2 :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hsplit := two_mul_pow_pred hk
  rw [axisRest_eq]
  split_ifs with ht
  · have : 3 * 2 ^ (a.log2 - 1) = 2 ^ a.log2 + 2 ^ (a.log2 - 1) := by
      rw [hsplit]; omega
    have := (axisTopBit_iff.mp ht)
    omega
  · omega

theorem slot_ge_two (a : ℕ) (n : Noun) (h : 2 ≤ a) :
    Noun.slot a n =
      match Noun.slot (a / 2) n with
      | some (.cell l r) => some (if a % 2 == 0 then l else r)
      | _ => none := by
  have ha : a = (a - 2) + 2 := by omega
  have hdiv : ((a - 2) + 2) / 2 = a / 2 := by omega
  have hmod : ((a - 2) + 2) % 2 = a % 2 := by omega
  conv => lhs; rw [ha]
  simp [Noun.slot, hdiv, hmod]
  rfl

theorem slot_of_double {k : ℕ} (m : Noun) {b : ℕ}
    (hk : 1 ≤ k) (hb : b < 2) :
    Noun.slot (2 * k + b) m =
      match Noun.slot k m with
      | some (.cell l r) => some (if b == 0 then l else r)
      | _ => none := by
  have hge : 2 ≤ 2 * k + b := by omega
  rw [slot_ge_two (2 * k + b) m hge]
  have hdiv : (2 * k + b) / 2 = k := by omega
  have hmod : (2 * k + b) % 2 = b := by omega
  simp [hdiv, hmod]

theorem slot_atom_of_ge_two {a n : ℕ} (h : 2 ≤ a) :
    Noun.slot a (.atom n) = none := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    have hslot := slot_ge_two a (.atom n) h
    rw [hslot]
    by_cases h2 : a / 2 = 1
    · rw [h2]
      simp [Noun.slot]
    · have hge : 2 ≤ a / 2 := by
        have : 1 ≤ a / 2 := by omega
        omega
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      rw [ih (a / 2) hlt hge]

theorem slot_eq_msb {a : ℕ} (l r : Noun) (h : 2 ≤ a) :
    Noun.slot a (.cell l r) =
      if axisTopBit a then Noun.slot (axisRest a) r
      else Noun.slot (axisRest a) l := by
  induction a using Nat.strongRecOn generalizing l r with
  | _ a ih =>
    by_cases h4 : a < 4
    · have h23 : a = 2 ∨ a = 3 := by omega
      rcases h23 with rfl | rfl
      · simp [Noun.slot, axisTopBit_two, axisRest_two]
      · simp [Noun.slot, axisTopBit_three, axisRest_three]
    · have ha4 : 4 ≤ a := by omega
      have hbit := axisTopBit_div2 ha4
      have hrest := axisRest_div2 ha4
      have h2' : 2 ≤ a / 2 := by omega
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      have ih' := ih (a / 2) hlt l r h2'
      rw [slot_ge_two a (.cell l r) h, ih', hbit]
      have hk : 1 ≤ axisRest (a / 2) := axisRest_pos h2'
      have hb : a % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases ht : axisTopBit (a / 2) = true
      · simp only [ht, ↓reduceIte]
        rw [hrest, slot_of_double r hk hb]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte]
        rw [hrest, slot_of_double l hk hb]

theorem lsbTarget_of_slot (ax : ℕ) (n r : Noun)
    (h : Noun.slot ax n = some r) :
    lsbTarget n ax = r := by
  induction ax using Nat.strongRecOn generalizing n r with
  | _ ax ih =>
    by_cases h1 : ax < 2
    · interval_cases ax
      · simp [Noun.slot] at h
      · simp [Noun.slot] at h
        subst r
        exact lsbTarget_of_lt2 n (by omega)
    · have h2 : 2 ≤ ax := by omega
      cases n with
      | atom a =>
        rw [slot_atom_of_ge_two h2] at h
        simp at h
      | cell hd tl =>
        rw [slot_eq_msb hd tl h2] at h
        by_cases ht : axisTopBit ax = true
        · rw [lsbTarget_of_tail (.cell hd tl) h2 ht, formulaTail]
          exact ih (axisRest ax) (axisRest_lt h2) tl r (by simpa [ht] using h)
        · have hh : axisTopBit ax = false := Bool.eq_false_iff.mpr ht
          rw [lsbTarget_of_head (.cell hd tl) h2 hh, formulaHead]
          exact ih (axisRest ax) (axisRest_lt h2) hd r (by simpa [hh] using h)

/-! ## Descent cell noun -/

theorem genAnnotatedDescent_pt_noun (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ current remaining,
      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        current remaining).2.noun =
        if remaining < 2 then E child else E current := by
  intro current remaining
  induction remaining using Nat.strongRecOn generalizing current with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · simp [genAnnotatedVerify, annotatedVerifyPub]
    · split <;> simp [annotatedDecPub]

theorem genAnnotatedDescentCont_length (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ current remaining,
      (genAnnotatedDescentCont E z lmb cont contCell contState current remaining).1.length =
        if remaining < 2 then cont.length else 1 := by
  intro current remaining
  induction remaining using Nat.strongRecOn generalizing current with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · simp
    · split <;> simp

theorem genAnnotatedDescentCont_pt_noun (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ current remaining,
      (genAnnotatedDescentCont E z lmb cont contCell contState current remaining).2.noun =
        if remaining < 2 then contCell.noun else E current := by
  intro current remaining
  induction remaining using Nat.strongRecOn generalizing current with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · simp
    · split <;> simp [annotatedDecPub]

theorem bindFP_of_lsb_descent (z α : K) (root child : Noun) (recAxis e : ℕ)
    (current : Noun) (remaining : ℕ)
    (hwf : lsbTarget current remaining = child) :
    bindFP z current
      (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
        current remaining).2.noun := by
  have hpt := genAnnotatedDescent_pt_noun (lmb := lmb) (encC z) z root child recAxis
    (α ^ e) e current remaining
  by_cases hlt : remaining < 2
  · have hc : current = child := by
      rwa [lsbTarget_of_lt2 _ hlt] at hwf
    rw [hpt, if_pos hlt, hc]
    exact bindFP_encC z child
  · rw [hpt, if_neg hlt]
    exact bindFP_encC z current

theorem bindFP_of_lsb_descentCont (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (current : Noun) (remaining : ℕ)
    (hbind : bindFP z (lsbTarget current remaining) contCell.noun) :
    bindFP z current
      (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
        current remaining).2.noun := by
  have hpt := genAnnotatedDescentCont_pt_noun (lmb := lmb) (encC z) z cont contCell
    contState current remaining
  by_cases hlt : remaining < 2
  · have : lsbTarget current remaining = current := lsbTarget_of_lt2 _ hlt
    rw [hpt, if_pos hlt]
    rwa [this] at hbind
  · rw [hpt, if_neg hlt]
    exact bindFP_encC z current

theorem genAnnotatedDescentCont_length_one
    (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (h1 : cont.length = 1) (current : Noun) (remaining : ℕ) :
    (genAnnotatedDescentCont E z lmb cont contCell contState
      current remaining).1.length = 1 := by
  rw [genAnnotatedDescentCont_length]
  split_ifs <;> simp [h1]

/-! ## Descent local validity -/

theorem genAnnotatedDescent_OK (z α : K) (root child : Noun) (recAxis e : ℕ) :
    ∀ current remaining,
      lsbTarget current remaining = child →
      ∀ u ∈ (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
          current remaining).1,
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro current remaining hwf u hu
  induction remaining using Nat.strongRecOn generalizing current u with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · simp [genAnnotatedVerify] at hdesc
      subst u
      exact genAnnotatedVerify_OK z α root child recAxis e
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      split at hdesc
      · rename_i ht
        simp at hdesc
        subst u
        have hwf' : lsbTarget (formulaTail current) (axisRest n) = child := by
          rwa [lsbTarget_of_tail current h2 ht] at hwf
        simp only [mapNTree]
        have hlen :
            (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
              (formulaTail current) (axisRest n)).1.length = 1 :=
          genAnnotatedDescent_length _ _ _ _ _ _ _ _ _
        refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
        · have :
              ([(genAnnotatedNounWalk (encC z) z lmb (formulaHead current)).1] ++
                (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
                  (formulaTail current) (axisRest n)).1).length = 2 := by
            simp [hlen]
          simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node,
            List.length_map]
        · refine gMemRow9_dec_bind z current (formulaHead current) (formulaTail current) 0
            _ _ _ _ 0 0 ?_ ?_
          · simpa [genAnnotatedNounWalk_pt_noun] using
              bindFP_encC z (formulaHead current)
          · exact bindFP_of_lsb_descent z α root child recAxis e
              (formulaTail current) (axisRest n) hwf'
        · exact gMemRow9_dec_specializes z α current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0
        intro d hdmem
        simp [List.mem_map] at hdmem
        rcases hdmem with rfl | ⟨w, hw, rfl⟩
        · exact genAnnotatedNounWalk_OK z α (formulaHead current)
        · exact ih (axisRest n) (axisRest_lt h2) (formulaTail current) hwf' w hw
      · rename_i hh
        have hh' : axisTopBit n = false := Bool.eq_false_iff.mpr hh
        simp at hdesc
        subst u
        have hwf' : lsbTarget (formulaHead current) (axisRest n) = child := by
          rwa [lsbTarget_of_head current h2 hh'] at hwf
        simp only [mapNTree]
        have hlen :
            (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
              (formulaHead current) (axisRest n)).1.length = 1 :=
          genAnnotatedDescent_length _ _ _ _ _ _ _ _ _
        refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
        · have :
              ((genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
                  (formulaHead current) (axisRest n)).1 ++
                [(genAnnotatedNounWalk (encC z) z lmb (formulaTail current)).1]).length = 2 := by
            simp [hlen]
          simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node,
            List.length_map]
        · refine gMemRow9_dec_bind z current (formulaHead current) (formulaTail current) 0
            _ _ _ _ 0 0 ?_ ?_
          · exact bindFP_of_lsb_descent z α root child recAxis e
              (formulaHead current) (axisRest n) hwf'
          · simpa [genAnnotatedNounWalk_pt_noun] using
              bindFP_encC z (formulaTail current)
        · exact gMemRow9_dec_specializes z α current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0
        intro d hdmem
        simp [List.mem_map, List.mem_append] at hdmem
        rcases hdmem with ⟨w, hw, rfl⟩ | rfl
        · exact ih (axisRest n) (axisRest_lt h2) (formulaHead current) hwf' w hw
        · exact genAnnotatedNounWalk_OK z α (formulaTail current)

theorem genAnnotatedDescentCont_OK (z α : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (h1 : cont.length = 1)
    (hcs : ∀ u ∈ cont, MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ current remaining,
      bindFP z (lsbTarget current remaining) contCell.noun →
      ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
          current remaining).1,
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro current remaining hbind u hu
  induction remaining using Nat.strongRecOn generalizing current u with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · exact hcs u hdesc
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      split at hdesc
      · rename_i ht
        simp at hdesc
        subst u
        have hbind' :
            bindFP z (lsbTarget (formulaTail current) (axisRest n))
              contCell.noun := by
          rwa [← lsbTarget_of_tail current h2 ht]
        simp only [mapNTree]
        have hlen :
            (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
              (formulaTail current) (axisRest n)).1.length = 1 :=
          genAnnotatedDescentCont_length_one _ _ _ _ _ h1 _ _
        refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
        · have :
              ([(genAnnotatedNounWalk (encC z) z lmb (formulaHead current)).1] ++
                (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
                  (formulaTail current) (axisRest n)).1).length = 2 := by
            simp [hlen]
          simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node,
            List.length_map]
        · refine gMemRow9_dec_bind z current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0 ?_ ?_
          · simpa [genAnnotatedNounWalk_pt_noun] using
              bindFP_encC z (formulaHead current)
          · exact bindFP_of_lsb_descentCont z cont contCell contState
              (formulaTail current) (axisRest n) hbind'
        · exact gMemRow9_dec_specializes z α current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0
        intro d hdmem
        simp [List.mem_map] at hdmem
        rcases hdmem with rfl | ⟨w, hw, rfl⟩
        · exact genAnnotatedNounWalk_OK z α (formulaHead current)
        · exact ih (axisRest n) (axisRest_lt h2) (formulaTail current) hbind' w hw
      · rename_i hh
        have hh' : axisTopBit n = false := Bool.eq_false_iff.mpr hh
        simp at hdesc
        subst u
        have hbind' :
            bindFP z (lsbTarget (formulaHead current) (axisRest n))
              contCell.noun := by
          rwa [← lsbTarget_of_head current h2 hh']
        simp only [mapNTree]
        have hlen :
            (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
              (formulaHead current) (axisRest n)).1.length = 1 :=
          genAnnotatedDescentCont_length_one _ _ _ _ _ h1 _ _
        refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
        · have :
              ((genAnnotatedDescentCont (encC z) z lmb cont contCell contState
                  (formulaHead current) (axisRest n)).1 ++
                [(genAnnotatedNounWalk (encC z) z lmb (formulaTail current)).1]).length
                = 2 := by
            simp [hlen]
          simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node,
            List.length_map]
        · refine gMemRow9_dec_bind z current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0 ?_ ?_
          · exact bindFP_of_lsb_descentCont z cont contCell contState
              (formulaHead current) (axisRest n) hbind'
          · simpa [genAnnotatedNounWalk_pt_noun] using
              bindFP_encC z (formulaTail current)
        · exact gMemRow9_dec_specializes z α current (formulaHead current)
            (formulaTail current) 0 _ _ _ _ 0 0
        intro d hdmem
        simp [List.mem_map, List.mem_append] at hdmem
        rcases hdmem with ⟨w, hw, rfl⟩ | rfl
        · exact ih (axisRest n) (axisRest_lt h2) (formulaHead current) hbind' w hw
        · exact genAnnotatedNounWalk_OK z α (formulaTail current)

theorem genAnnotatedRecordTree_wf_OK (z α : K) (root child : Noun) (axis e : ℕ)
    (hwf : lsbTarget root axis = child) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb root child axis e)) := by
  unfold genAnnotatedRecordTree
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have hlen :=
      genAnnotatedDescent_length (lmb := lmb) (encC z) z root child axis (α ^ e) e root axis
    simp [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node, hlen]
  · refine gMemRow9_read_bind z root child axis e _ (α ^ e) 0 0 ?_
    exact bindFP_of_lsb_descent z α root child axis e root axis hwf
  · exact gMemRow9_read_specializes z α root child axis e _ 0 0
  intro c hc
  simp [List.mem_map] at hc
  rcases hc with ⟨w, hw, rfl⟩
  exact genAnnotatedDescent_OK z α root child axis e root axis hwf w hw

theorem genRowMemForest_singleton_wf_OK (z α : K) (r : MemRecordReq)
    (hwf : lsbTarget r.root r.axis = r.child) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [r],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_wf_OK z α r.root r.child r.axis r.recordExp hwf

theorem genRowMemForest_independent_wf_OK (z α : K) :
    ∀ rs : List MemRecordReq,
      (∀ r ∈ rs, lsbTarget r.root r.axis = r.child) →
      ∀ u ∈ rs.map (fun r =>
          genAnnotatedRecordTree (encC z) z α lmb r.root r.child r.axis r.recordExp),
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u)
  | [], _, u, hu => by simp at hu
  | r :: rs, hwf, u, hu => by
      rw [List.map_cons] at hu
      simp only [List.mem_cons] at hu
      rcases hu with hu | hu
      · subst u
        exact genAnnotatedRecordTree_wf_OK z α r.root r.child r.axis r.recordExp
          (hwf r (by simp))
      · exact genRowMemForest_independent_wf_OK z α rs
          (fun r' hr' => hwf r' (List.mem_cons.mpr (Or.inr hr'))) u hu

theorem genAnnotatedChainedInner_pair_length (E : Noun → ComputeTable.FP K)
    (z α : K) (prev r : MemRecordReq) :
    (genAnnotatedChainedInner E z α lmb prev [r]).1.length = 1 := by
  unfold genAnnotatedChainedInner
  simp [genAnnotatedChainedInner_nil]

theorem genAnnotatedChainedInner_pair_pt_noun
    (E : Noun → ComputeTable.FP K) (z α : K) (prev r : MemRecordReq) :
    (genAnnotatedChainedInner E z α lmb prev [r]).2.noun = E r.root := by
  unfold genAnnotatedChainedInner
  simp [genAnnotatedChainedInner_nil, annotatedReadPub]

theorem genAnnotatedChainedInner_one_OK (z α : K) (prev r : MemRecordReq)
    (hchain : prev.child = r.root)
    (hwf : lsbTarget r.root r.axis = r.child) :
    ∀ u ∈ (genAnnotatedChainedInner (encC z) z α lmb prev [r]).1,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp at hu
  subst u
  have hlenC :
      (genAnnotatedDescentCont (encC z) z lmb
        [(genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
            (α ^ r.recordExp) r.recordExp).1]
        (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
            (α ^ r.recordExp) r.recordExp).2
        .verify_child r.root r.axis).1.length = 1 :=
    genAnnotatedDescentCont_length_one _ _ _ _ _ (by simp) _ _
  have hbindR :
      bindFP z (lsbTarget r.root r.axis)
        (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
          (α ^ r.recordExp) r.recordExp).2.noun := by
    simpa [hwf, genAnnotatedVerify_pt_noun] using bindFP_encC z r.child
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node]
  · refine gMemRow9_read_bind z r.root r.child r.axis r.recordExp _ (α ^ r.recordExp) 0 0 ?_
    simpa [annotatedVerifyPub, hchain] using bindFP_encC z r.root
  · exact gMemRow9_read_specializes z α r.root r.child r.axis r.recordExp _ 0 0
  intro c hc
  simp at hc
  subst c
  rw [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simpa [gMemRow9, memVerifySkelAx, fanoutMem, GenMemoryRow.node, hlenC]
  · refine gMemRow9_verify_bind z prev.root prev.child prev.axis prev.recordExp
      _ (α ^ prev.recordExp) 0 0 ?_
    rw [hchain]
    exact bindFP_of_lsb_descentCont z
      [(genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
          (α ^ r.recordExp) r.recordExp).1]
      (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
          (α ^ r.recordExp) r.recordExp).2
      .verify_child r.root r.axis hbindR
  · exact gMemRow9_verify_specializes z α prev.root prev.child prev.axis
      prev.recordExp _ 0 0
  intro d hdmem
  simp [List.mem_map] at hdmem
  rcases hdmem with ⟨w, hw, rfl⟩
  exact genAnnotatedDescentCont_OK z α
    [(genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
        (α ^ r.recordExp) r.recordExp).1]
    (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
        (α ^ r.recordExp) r.recordExp).2
    .verify_child (by simp)
    (by
      intro v hv
      simp at hv
      subst v
      exact genAnnotatedVerify_OK z α r.root r.child r.axis r.recordExp)
    r.root r.axis hbindR w hw

theorem genAnnotatedChainedTree_two_OK (z α : K) (r1 r2 : MemRecordReq)
    (hchain : r1.child = r2.root)
    (hwf1 : lsbTarget r1.root r1.axis = r1.child)
    (hwf2 : lsbTarget r2.root r2.axis = r2.child)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree (encC z) z α lmb [r1, r2] = some t) :
    MemoryNodesOK z α (mapNTree GenMemoryRow.node t) := by
  have hopen :
      genAnnotatedChainedTree (encC z) z α lmb [r1, r2] =
        some
          (.node
            (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
              (annotatedReadPub (encC z) r1.root r1.child r1.axis (α ^ r1.recordExp)
                (genAnnotatedDescentCont (encC z) z lmb
                    (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
                    (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
                    (chainedInnerRootState [r2]) r1.root r1.axis).2
                0 0 lmb))
            (genAnnotatedDescentCont (encC z) z lmb
              (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
              (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
              (chainedInnerRootState [r2]) r1.root r1.axis).1) :=
    rfl
  rw [hopen] at ht
  injection ht with ht
  subst t
  have h1 := genAnnotatedChainedInner_pair_length (lmb := lmb) (encC z) z α r1 r2
  have hbind :
      bindFP z (lsbTarget r1.root r1.axis)
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2.noun := by
    rw [genAnnotatedChainedInner_pair_pt_noun, hwf1, hchain]
    exact bindFP_encC z r2.root
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have hlen :=
      genAnnotatedDescentCont_length_one (lmb := lmb) (encC z) z
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
        (chainedInnerRootState [r2]) h1 r1.root r1.axis
    simpa [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node, hlen]
  · refine gMemRow9_read_bind z r1.root r1.child r1.axis r1.recordExp
      _ (α ^ r1.recordExp) 0 0 ?_
    exact bindFP_of_lsb_descentCont z
      (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
      (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
      (chainedInnerRootState [r2]) r1.root r1.axis hbind
  · exact gMemRow9_read_specializes z α r1.root r1.child r1.axis r1.recordExp _ 0 0
  intro c hc
  simp [List.mem_map] at hc
  rcases hc with ⟨w, hw, rfl⟩
  exact genAnnotatedDescentCont_OK z α
    (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
    (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
    (chainedInnerRootState [r2]) h1
    (genAnnotatedChainedInner_one_OK z α r1 r2 hchain hwf2)
    r1.root r1.axis hbind w hw

theorem genRowMemForest_two_wf_OK (z α : K) (r1 r2 : MemRecordReq)
    (hwf1 : lsbTarget r1.root r1.axis = r1.child)
    (hwf2 : lsbTarget r2.root r2.axis = r2.child) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [r1, r2],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  rw [genRowMemForest_two_eq] at hu
  by_cases hc : r1.child = r2.root
  · rw [if_pos hc] at hu
    cases hch : genAnnotatedChainedTree (encC z) z α lmb [r1, r2] with
    | none =>
      have hsome :
          genAnnotatedChainedTree (encC z) z α lmb [r1, r2] =
            some
              (.node
                (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
                  (annotatedReadPub (encC z) r1.root r1.child r1.axis
                    (α ^ r1.recordExp)
                    (genAnnotatedDescentCont (encC z) z lmb
                        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
                        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
                        (chainedInnerRootState [r2]) r1.root r1.axis).2
                    0 0 lmb))
                (genAnnotatedDescentCont (encC z) z lmb
                  (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
                  (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
                  (chainedInnerRootState [r2]) r1.root r1.axis).1) :=
        rfl
      simp [hsome] at hch
    | some t =>
      simp [hch] at hu
      subst u
      exact genAnnotatedChainedTree_two_OK z α r1 r2 hc hwf1 hwf2 t hch
  · rw [if_neg hc] at hu
    simp at hu
    rcases hu with hu | hu
    · subst u
      exact genAnnotatedRecordTree_wf_OK z α r1.root r1.child r1.axis r1.recordExp hwf1
    · subst u
      exact genAnnotatedRecordTree_wf_OK z α r2.root r2.child r2.axis r2.recordExp hwf2

theorem genRowMemForest_wf_OK (z α : K) :
    ∀ rs : List MemRecordReq,
      (∀ r ∈ rs, lsbTarget r.root r.axis = r.child) →
      ∀ u ∈ genRowMemForest (encC z) z α lmb rs,
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u)
  | [], _, u, hu => by simp [genRowMemForest] at hu
  | [r], hwf, u, hu =>
      genRowMemForest_singleton_wf_OK z α r (hwf r (by simp)) u hu
  | [r1, r2], hwf, u, hu =>
      genRowMemForest_two_wf_OK z α r1 r2
        (hwf r1 (by simp)) (hwf r2 (by simp)) u hu
  | [r1, r2, r3], hwf, u, hu => by
      rw [genRowMemForest_three_eq] at hu
      simp [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact genRowMemForest_two_wf_OK z α r1 r2
          (hwf r1 (by simp)) (hwf r2 (by simp)) u hu
      · exact genAnnotatedRecordTree_wf_OK z α r3.root r3.child r3.axis r3.recordExp
          (hwf r3 (by simp))
  | r1 :: r2 :: r3 :: r4 :: rest, hwf, u, hu => by
      unfold genRowMemForest at hu
      exact genRowMemForest_independent_wf_OK z α (r1 :: r2 :: r3 :: r4 :: rest) hwf u hu

/-! ## Constructor forests -/

theorem gen_op1_mem_OK (z α : K) (n : ℕ) (subject : Noun) (k : ℕ)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op1 k) = .ok (t, r)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op1 (K := K) n subject k
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
    genMemForestFromList_nil, List.append_nil] at hu
  exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.atom k) 0 u hu

theorem gen_quote_mem_OK (z α : K) (n : ℕ) (subject result : Noun)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (quote result) = .ok (t, r)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_quote (K := K) n subject result
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
    genMemForestFromList_nil, List.append_nil] at hu
  have hq : quote result = .cell (.atom 1) result := rfl
  rw [hq] at hu
  exact genRowMemForest_singleton_axis3_OK z α (.atom 1) result 0 u hu

theorem gen_cons_mem_OK (z α : K) (n : ℕ)
    {subject leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {r : Noun}
    (hl : genComputeSkeleton (K := K) n subject (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n subject tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.cell leftHead leftTail) tail) = .ok (t, r))
    (hL : ∀ u ∈ genMemForestFromTree (encC z) z α lmb lTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hR : ∀ u ∈ genMemForestFromTree (encC z) z α lmb rTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_cons (K := K) n hl hr
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
    genMemForestFromList_two] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_singleton_axis3_OK z α (.cell leftHead leftTail) tail 0
      u hu
  · exact hL u hu
  · exact hR u hu

theorem gen_op4_mem_OK (z α : K) (n : ℕ)
    {subject tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) subject (op4 tail) = .ok (t, r))
    (hC : ∀ u ∈ genMemForestFromTree (encC z) z α lmb callTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op4 (K := K) n hc hinc
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_one,
    genMemForestFromList_cons, genMemForestFromList_nil, List.append_nil] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu
  · have hop : op4 tail = .cell (.atom 4) tail := rfl
    rw [hop] at hu
    exact genRowMemForest_singleton_axis3_OK z α (.atom 4) tail 0 u hu
  · exact hC u hu

theorem gen_op5_mem_OK (z α : K) (n : ℕ)
    {subject b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op5 b c) = .ok (t, r))
    (hB : ∀ u ∈ genMemForestFromTree (encC z) z α lmb bTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hC : ∀ u ∈ genMemForestFromTree (encC z) z α lmb cTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op5 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
    genMemForestFromList_two] at hu
  have hop : op5 b c = .cell (.atom 5) (.cell b c) := rfl
  rw [hop] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_chain32_OK z α (.atom 5) b c 0 0 u hu
  · exact hB u hu
  · exact hC u hu

theorem gen_op7_mem_OK (z α : K) (n : ℕ)
    {subject b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op7 b c) = .ok (t, r))
    (hB : ∀ u ∈ genMemForestFromTree (encC z) z α lmb bTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hC : ∀ u ∈ genMemForestFromTree (encC z) z α lmb cTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op7 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
    genMemForestFromList_two] at hu
  have hop : op7 b c = .cell (.atom 7) (.cell b c) := rfl
  rw [hop] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_chain32_OK z α (.atom 7) b c 0 0 u hu
  · exact hB u hu
  · exact hC u hu

theorem gen_op6_zero_mem_OK (z α : K) (n : ℕ)
    {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r))
    (hB : ∀ u ∈ genMemForestFromTree (encC z) z α lmb condTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hC : ∀ u ∈ genMemForestFromTree (encC z) z α lmb takenTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op6_zero (K := K) (d := d) n hb hc
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
    genMemForestFromList_two] at hu
  have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
  rw [hop] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_three_chain32_OK z α (.atom 6) b (.cell c d) c d 0 0 0
      u hu
  · exact hB u hu
  · exact hC u hu

theorem gen_op6_one_mem_OK (z α : K) (n : ℕ)
    {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n subject d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r))
    (hB : ∀ u ∈ genMemForestFromTree (encC z) z α lmb condTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hD : ∀ u ∈ genMemForestFromTree (encC z) z α lmb takenTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op6_one (K := K) (c := c) n hb hd
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
    genMemForestFromList_two] at hu
  have hop : op6 b c d = .cell (.atom 6) (.cell b (.cell c d)) := rfl
  rw [hop] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_three_chain32_OK z α (.atom 6) b (.cell c d) c d 0 0 0
      u hu
  · exact hB u hu
  · exact hD u hu

theorem genRowMemForest_op0_OK (z α : K) (ax : ℕ) (subject result : Noun)
    (e1 e2 : ℕ) (hne : .atom ax ≠ subject)
    (hwf : lsbTarget subject ax = result) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
        [⟨op0 ax, .atom ax, 3, e1⟩, ⟨subject, result, ax, e2⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genRowMemForest op0 at hu
  simp [hne] at hu
  rcases hu with hu | hu
  · subst u
    exact genAnnotatedRecordTree_axis3_OK z α (.atom 0) (.atom ax) e1
  · subst u
    exact genAnnotatedRecordTree_wf_OK z α subject result ax e2 hwf

theorem genRowMemForest_three_chain32_wf_OK (z α : K)
    (hd1 hd2 tl2 root3 child3 : Noun) (ax3 e1 e2 e3 : ℕ)
    (hwf : lsbTarget root3 ax3 = child3) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨root3, child3, ax3, e3⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genRowMemForest at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | hmem
    · rw [hmem]
      exact genAnnotatedChainedTree_axis3_axis2_OK z α hd1 hd2 tl2 e1 e2 t h
    · rw [hmem]
      exact genAnnotatedRecordTree_wf_OK z α root3 child3 ax3 e3 hwf

theorem gen_op0_mem_OK (z α : K) (n : ℕ) {subject : Noun} {axis : ℕ}
    {result : Noun}
    (hs : Noun.slot axis subject = some result)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op0 axis) = .ok (t, r))
    (hne : .atom axis ≠ subject)
    (hwf : lsbTarget subject axis = result) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op0 (K := K) n hs
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
    genMemForestFromList_nil, List.append_nil] at hu
  exact genRowMemForest_op0_OK z α axis subject result 0 0 hne hwf u hu

theorem gen_op9_mem_OK (z α : K) (n : ℕ)
    {subject c core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject c = .ok (coreTree, core))
    (hslot : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) n core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = .ok (t, r))
    (hC : ∀ u ∈ genMemForestFromTree (encC z) z α lmb coreTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hI : ∀ u ∈ genMemForestFromTree (encC z) z α lmb invokeTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hwf : lsbTarget core axis = arm) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have h' := gen_op9 (K := K) n hc hslot harm
  rw [(gen_ok_unique h h').1]
  intro u hu
  rw [genMemForestFromTree_node, extractNodeReqs_skel_three,
    genMemForestFromList_two] at hu
  simp [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · exact genRowMemForest_three_chain32_wf_OK z α (.atom 9) (.atom axis) c
      core arm axis 0 0 0 hwf u hu
  · exact hC u hu
  · exact hI u hu

theorem gen_invokeAxis_mem_OK (z α : K) (n : ℕ)
    {subject core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) subject (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) subject (invokeAxis axis) =
      .ok (t, r))
    (hCore : ∀ u ∈ genMemForestFromTree (encC z) z α lmb coreTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hI : ∀ u ∈ genMemForestFromTree (encC z) z α lmb invokeTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hwf : lsbTarget core axis = arm) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have hop9 :
      genComputeSkeleton (K := K) (n + 3) subject
        (.cell (.atom 9) (.cell (.atom axis) (op0 1))) = .ok (t, r) := by
    simpa [invokeAxis, op0] using h
  exact gen_op9_mem_OK z α (n + 2) hcore hslotA harm hop9 hCore hI hwf

theorem gen_slam_mem_OK (z α : K) (n : ℕ) {axis : ℕ}
    {subject bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) (n + 3) subject (.cell bHead bTail) =
      .ok (battTree, battery))
    (hs : genComputeSkeleton (K := K) (n + 3) subject sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (.cell battery sample) arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) subject
        (slam (.cell bHead bTail) sampleF axis) = .ok (t, r))
    (hB : ∀ u ∈ genMemForestFromTree (encC z) z α lmb battTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hS : ∀ u ∈ genMemForestFromTree (encC z) z α lmb sampTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hI : ∀ u ∈ genMemForestFromTree (encC z) z α lmb invokeTree,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hwf : lsbTarget (.cell battery sample) axis = arm) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  have hpair :=
    gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore :=
    gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  simp only [slam] at h
  refine gen_op7_mem_OK z α (n + 4) hpair hax h ?_ ?_
  · exact gen_cons_mem_OK z α (n + 3) hb hs hpair hB hS
  · refine gen_invokeAxis_mem_OK z α (n + 1) hcore hslot harm hax ?_ hI hwf
    exact gen_op0_mem_OK z α (n + 2) (slot_1 (.cell battery sample)) hcore
      (atom_ne_cell_battery_sample 1 battery sample)
      (lsbTarget_of_slot1 _ _ (slot_1 (.cell battery sample)))

/-! ## Assigned forest inhabitation -/

/-- Request well-formedness: paper `axisPath` matches the child, and
    `Noun.slot` succeeds on every axis `≥ 2` so decompose nodes are cells. -/
def RequestWF (req : ServiceReq K) : Prop :=
  lsbTarget req.root req.axis = req.child ∧
    Noun.slot req.axis req.root = some req.child

theorem reqWF_axis3 (hd tl : Noun) {req : ServiceReq K}
    (hr : req.root = .cell hd tl) (hc : req.child = tl) (ha : req.axis = 3) :
    RequestWF req := by
  rw [RequestWF, hr, hc, ha]
  exact ⟨lsbTarget_axis3 hd tl, (by simp [Noun.slot])⟩

theorem reqWF_axis2 (hd tl : Noun) {req : ServiceReq K}
    (hr : req.root = .cell hd tl) (hc : req.child = hd) (ha : req.axis = 2) :
    RequestWF req := by
  rw [RequestWF, hr, hc, ha]
  exact ⟨lsbTarget_axis2 hd tl, (by simp [Noun.slot])⟩

theorem reqWF_of_slot (ax : ℕ) (n r : Noun) {req : ServiceReq K}
    (hr : req.root = n) (hc : req.child = r) (ha : req.axis = ax)
    (h : Noun.slot ax n = some r) :
    RequestWF req := by
  rw [RequestWF, hr, hc, ha]
  exact ⟨lsbTarget_of_slot ax n r h, h⟩

def treeRequestsWF (t : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree t n → ∀ req ∈ n.label.requests, RequestWF req

theorem treeRequestsWF_node (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (hg : ∀ req ∈ g.requests, RequestWF req)
    (hcs : ∀ c ∈ cs, treeRequestsWF c) :
    treeRequestsWF (.node g cs) := by
  intro n hn
  cases hn with
  | here => exact hg
  | sub hs hst => exact hcs _ hs n hst

theorem extractNodeReqsAux_mem (stamp : ComputeTimestampRow) (i : ℕ)
    (rs : List (ServiceReq K)) (r : MemRecordReq)
    (hr : r ∈ extractNodeReqsAux stamp i rs) :
    ∃ req ∈ rs, r.root = req.root ∧ r.child = req.child ∧ r.axis = req.axis := by
  induction rs generalizing i with
  | nil => simp [extractNodeReqsAux] at hr
  | cons req rs ih =>
    simp [extractNodeReqsAux] at hr
    rcases hr with hr | hr
    · subst r
      exact ⟨req, by simp, rfl, rfl, rfl⟩
    · obtain ⟨req', hmem, h1, h2, h3⟩ := ih (i + 1) hr
      exact ⟨req', List.mem_cons.mpr (Or.inr hmem), h1, h2, h3⟩

set_option maxHeartbeats 800000 in
theorem genComputeSkeleton_tree_requests_wf :
    ∀ {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {r : Noun},
      genComputeSkeleton (K := K) fuel subject formula = .ok (t, r) →
      treeRequestsWF t := by
  intro fuel
  induction fuel with
  | zero =>
    intro subject formula t r h
    simp [genComputeSkeleton] at h
  | succ n ih =>
    intro subject formula t r h
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error e => simp [genComputeSkeleton, hL] at h
        | ok pr =>
          obtain ⟨lTree, lRes⟩ := pr
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hL, hR] at h
          | ok pr =>
            obtain ⟨rTree, rRes⟩ := pr
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine treeRequestsWF_node _ _ ?_ ?_
            · intro req hreq
              simp [skelNode] at hreq
              subst req
              exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
            · intro c hc
              simp at hc
              rcases hc with rfl | rfl
              · exact ih hL
              · exact ih hR
      | atom op =>
        match op with
        | 0 =>
          cases tl with
          | atom ax =>
            cases hs : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hs] at h
            | some result =>
              simp [genComputeSkeleton, hs] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestsWF_node _ _ ?_ (by intro c hc; simp at hc)
              intro req hreq
              simp [skelNode] at hreq
              rcases hreq with hreq | hreq
              · subst req
                exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
              · subst req
                exact ⟨lsbTarget_of_slot ax subject result hs, hs⟩
          | cell _ _ => simp [genComputeSkeleton] at h
        | 1 =>
          simp [genComputeSkeleton] at h
          obtain ⟨ht, _⟩ := h
          subst t
          refine treeRequestsWF_node _ _ ?_ (by intro c hc; simp at hc)
          intro req hreq
          simp [skelNode] at hreq
          subst req
          exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
        | 2 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                cases hM : genComputeSkeleton (K := K) n sf1 sf2 with
                | error e => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pr =>
                  obtain ⟨mTree, result⟩ := pr
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨ht, _⟩ := h
                  subst t
                  refine treeRequestsWF_node _ _ ?_ ?_
                  · intro req hreq
                    simp [skelNode] at hreq
                    rcases hreq with hreq | hreq
                    · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                    · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                  · intro ch hc
                    simp at hc
                    rcases hc with rfl | rfl | rfl
                    · exact ih hB
                    · exact ih hC
                    · exact ih hM
        | 3 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            simp [genComputeSkeleton, hC] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine treeRequestsWF_node _ _ ?_ ?_
            · intro req hreq
              simp [skelNode] at hreq
              subst req
              exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
            · intro ch hc
              simp at hc
              subst ch
              exact ih hC
        | 4 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            cases hinc : Noun.lus callResult with
            | none => simp [genComputeSkeleton, hC, hinc] at h
            | some result =>
              simp [genComputeSkeleton, hC, hinc] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestsWF_node _ _ ?_ ?_
              · intro req hreq
                simp [skelNode] at hreq
                subst req
                exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
              · intro ch hc
                simp at hc
                subst ch
                exact ih hC
        | 5 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsWF_node _ _ ?_ ?_
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                  · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 6 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b cd =>
            cases cd with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pr =>
                obtain ⟨condTree, cond⟩ := pr
                cases cond with
                | cell _ _ => simp [genComputeSkeleton, hB] at h
                | atom cv =>
                  match cv with
                  | 0 =>
                    cases hC : genComputeSkeleton (K := K) n subject c with
                    | error e => simp [genComputeSkeleton, hB, hC] at h
                    | ok pr =>
                      obtain ⟨takenTree, result⟩ := pr
                      simp [genComputeSkeleton, hB, hC] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestsWF_node _ _ ?_ ?_
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq | hreq
                        · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                        · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                        · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact ih hB
                        · exact ih hC
                  | 1 =>
                    cases hD : genComputeSkeleton (K := K) n subject d with
                    | error e => simp [genComputeSkeleton, hB, hD] at h
                    | ok pr =>
                      obtain ⟨takenTree, result⟩ := pr
                      simp [genComputeSkeleton, hB, hD] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestsWF_node _ _ ?_ ?_
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq | hreq
                        · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                        · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                        · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact ih hB
                        · exact ih hD
                  | _ + 2 => simp [genComputeSkeleton, hB] at h
        | 7 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n sb c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsWF_node _ _ ?_ ?_
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                  · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 8 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n (.cell sb subject) c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsWF_node _ _ ?_ ?_
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                  · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 9 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hC] at h
              | ok pr =>
                obtain ⟨coreTree, core⟩ := pr
                cases hslot : Noun.slot ax core with
                | none => simp [genComputeSkeleton, hC, hslot] at h
                | some arm =>
                  cases hI : genComputeSkeleton (K := K) n core arm with
                  | error e => simp [genComputeSkeleton, hC, hslot, hI] at h
                  | ok pr =>
                    obtain ⟨invokeTree, result⟩ := pr
                    simp [genComputeSkeleton, hC, hslot, hI] at h
                    obtain ⟨ht, _⟩ := h
                    subst t
                    refine treeRequestsWF_node _ _ ?_ ?_
                    · intro req hreq
                      simp [skelNode] at hreq
                      rcases hreq with hreq | hreq | hreq
                      · subst req; exact ⟨lsbTarget_axis3 _ _, (by simp [Noun.slot])⟩
                      · subst req; exact ⟨lsbTarget_axis2 _ _, (by simp [Noun.slot])⟩
                      · subst req
                        exact ⟨lsbTarget_of_slot ax core arm hslot, hslot⟩
                    · intro ch hc
                      simp at hc
                      rcases hc with rfl | rfl
                      · exact ih hC
                      · exact ih hI
        | 10 => simp [genComputeSkeleton] at h
        | 11 => simp [genComputeSkeleton] at h
        | _ + 12 => simp [genComputeSkeleton] at h

theorem bfsAssign_extract_requests_wf (t : NTree (GenComputeRow K))
    (ht : treeRequestsWF t) (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign t) n) :
    ∀ r ∈ extractNodeReqs n.label,
      lsbTarget r.root r.axis = r.child := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels t
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := t) hi
  intro r hr
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests t i hi'] at hr
  obtain ⟨req, hreq, hr1, hr2, hr3⟩ := extractNodeReqsAux_mem _ 0 _ r hr
  have hlen : i - 1 < (bfsForest [t]).length := by
    rwa [← bfsRows_length]
  have hnode : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem _
  have hin : InTree t (bfsForest [t])[i - 1] := by
    have := (mem_bfsForest [t] _).mp hnode
    rcases this with ⟨c, hc, hIn⟩
    simp only [List.mem_singleton] at hc
    subst c
    exact hIn
  have hreq' : req ∈ (bfsForest [t])[i - 1].label.requests := by
    have : (bfsRows t)[i - 1] = (bfsForest [t])[i - 1].label := by
      simp [bfsRows]
    simpa [this] using hreq
  have hwf := ht _ hin req hreq'
  rw [hr1, hr2, hr3]
  exact hwf.1

/-- **Every extracted request of an accepted program is genuinely served.** -/
theorem bfsAssign_extract_requests_slot (t : NTree (GenComputeRow K))
    (ht : treeRequestsWF t) (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign t) n) :
    ∀ r ∈ extractNodeReqs n.label,
      Noun.slot r.axis r.root = some r.child := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels t
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := t) hi
  intro r hr
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests t i hi'] at hr
  obtain ⟨req, hreq, hr1, hr2, hr3⟩ := extractNodeReqsAux_mem _ 0 _ r hr
  have hlen : i - 1 < (bfsForest [t]).length := by
    rwa [← bfsRows_length]
  have hnode : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem _
  have hin : InTree t (bfsForest [t])[i - 1] := by
    have := (mem_bfsForest [t] _).mp hnode
    rcases this with ⟨c, hc, hIn⟩
    simp only [List.mem_singleton] at hc
    subst c
    exact hIn
  have hreq' : req ∈ (bfsForest [t])[i - 1].label.requests := by
    have : (bfsRows t)[i - 1] = (bfsForest [t])[i - 1].label := by
      simp [bfsRows]
    simpa [this] using hreq
  have hwf := ht _ hin req hreq'
  rw [hr1, hr2, hr3]
  exact hwf.2

theorem mmTree_requests_wf : treeRequestsWF (mmTree (K := K)) :=
  genComputeSkeleton_tree_requests_wf (mmTree_gen (K := K))

theorem treeRequestsWF_airReorder {t : NTree (GenComputeRow K)}
    (h : treeRequestsWF t) : treeRequestsWF (airReorder t) := by
  intro u hu req hreq
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  exact h u0 hu0 req (by simpa [hl] using hreq)

theorem mmAssigned_rowOK (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genRowMemForest_wf_OK z α _ (bfsAssign_extract_requests_wf (mmTreeAir (K := K))
    (by unfold mmTreeAir; exact treeRequestsWF_airReorder mmTree_requests_wf) n hn)

theorem mmMemForest_OK (z α : K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTreeAir (K := K))),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _ (mmAssigned_rowOK z α)

theorem mmMemForest_unassigned_OK (z α : K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (mmTree (K := K)),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _ (fun n hn u hu =>
    genRowMemForest_wf_OK z α _ (fun r hr => by
      obtain ⟨req, hreq, hr1, hr2, hr3⟩ :=
        extractNodeReqsAux_mem n.label.stamp 0 n.label.requests r hr
      have hwf := mmTree_requests_wf n hn req hreq
      rw [hr1, hr2, hr3]
      exact hwf.1) u hu)

/-- Committed memory node forest of the assigned matmul tree.  Its row
    projection is `MatmulConfig65537.memoryForest`. -/
noncomputable def mmMemoryNodes (z α : K) : List (NTree (MemoryNode K)) :=
  (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))).map
    (mapNTree GenMemoryRow.node)

theorem mmMemoryNodes_OK (z α : K) :
    ∀ t ∈ mmMemoryNodes z α, MemoryNodesOK z α t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact mmMemForest_OK z α u hu

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedDescent_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_wf_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op1_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_quote_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_cons_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op4_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op5_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op7_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op6_zero_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.lsbTarget_of_slot2
#print axioms Nock.NockVMROM.Thm54.TraceGen.lsbTarget_of_slot4
#print axioms Nock.NockVMROM.Thm54.TraceGen.lsbTarget_of_slot8
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op0_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op9_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_invokeAxis_mem_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.lsbTarget_of_slot
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_wf_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_tree_requests_wf
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_extract_requests_slot
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmMemForest_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmMemForest_unassigned_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmMemoryNodes_OK
