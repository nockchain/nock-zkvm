/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/CountAL.lean

  **Length bounds on the ALU's coin-free lists.**
  At `p = Nock.Atoms.p`, with the ALU chip satisfied (`ALChipOK`):
  * `aluSL_pins_le`: `|aluSL| + 2·|prims| ≤ 2·nL` (a `hdr` row (`sH = 1`) is never a `preg` row (`sP = 1`): the gate
    `bool(sP + sH + sL)`; `PregOK` makes `sP = 1` exactly on the first `|prims|` rows);
  * `aluPL_le`: `|aluPL| ≤ 2·nL`;
  * `aluFpL_le`: `|aluFpL| ≤ nL` (one validity read per row at most; no chip fact needed).
  The absent case (`aluOn = false`, `prims = []`) makes the lists empty.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.HbalJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluShareAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.BindAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CountAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead (ag_zero mem_kind)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (aluEF aluEK alu_rowGates)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (PregOK ALChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

section Count
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {chals pubs : ℕ → K}

local notation "CH" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL
local notation "QL" => qAL δ b Pb tr chals pubs
local notation "E0" => alE0 (K := K) δ b Pb tr

theorem natcast_inj {m n : ℕ} (hm : m < Nock.Atoms.p) (hn : n < Nock.Atoms.p) (h : (m : Fp) = (n : Fp)) :
    m = n := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h
  exact h

/-- **The row facts**: `sH` is boolean; `sP = 1` exactly on the first `|prims|` rows; a `hdr` row is not one of them. -/
theorem row_facts (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (i : Fin Pb.nL) :
    ((E0 i).trace sH = 0 ∨ (E0 i).trace sH = 1) ∧
      (E0 i).trace sP = (if (i : ℕ) < Pb.prims.length then 1 else 0) ∧
      ((E0 i).trace sH ≠ 0 → ¬ (i : ℕ) < Pb.prims.length) := by
  have hH : (E0 i).trace sH = 0 ∨ (E0 i).trace sH = 1 := AluSumAL.sH_bool δ b Pb tr chals pubs hsat i
  have c0 := BindAL.pre_col δ b hbind 0 i
  simp only [Fin.val_zero, add_zero] at c0
  have hP : (E0 i).trace sP = (if (i : ℕ) < Pb.prims.length then 1 else 0) := by
    show (E0 i).trace 2 = _
    rw [c0]; exact (hpre.2 i).1
  refine ⟨hH, hP, fun hne hlt => ?_⟩
  have hs1 : (E0 i).trace sP = 1 := by rw [hP, if_pos hlt]
  have hh1 : (E0 i).trace sH = 1 := hH.resolve_left hne
  have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
    (mem_kind (a := ar (boolE (sumC [sP, sH, sL]))) (by simp [gKind]))
  have gL := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
    (mem_kind (a := ar (boolE (cv sL))) (by simp [gKind]))
  simp only [AG.gate, ar, boolE, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g gL
  have g2 : ((E0 i).trace sP + ((E0 i).trace sH + (E0 i).trace sL)) *
      ((E0 i).trace sP + ((E0 i).trace sH + (E0 i).trace sL) - 1) = 0 := g
  have gL2 : (E0 i).trace sL * ((E0 i).trace sL - 1) = 0 := gL
  have hsum := Chips.CertBound.bool_cases g2
  have hLb := Chips.CertBound.bool_cases gL2
  rw [hs1, hh1] at hsum
  rcases hLb with h0 | h1
  · rw [h0] at hsum
    rcases hsum with h | h
    · have := natcast_inj (m := 2) (n := 0) (by norm_num [Nock.Atoms.p, Nock.Field.p])
        (by norm_num [Nock.Atoms.p, Nock.Field.p]) (by push_cast; linear_combination h)
      omega
    · have := natcast_inj (m := 2) (n := 1) (by norm_num [Nock.Atoms.p, Nock.Field.p])
        (by norm_num [Nock.Atoms.p, Nock.Field.p]) (by push_cast; linear_combination h)
      omega
  · rw [h1] at hsum
    rcases hsum with h | h
    · have := natcast_inj (m := 3) (n := 0) (by norm_num [Nock.Atoms.p, Nock.Field.p])
        (by norm_num [Nock.Atoms.p, Nock.Field.p]) (by push_cast; linear_combination h)
      omega
    · have := natcast_inj (m := 3) (n := 1) (by norm_num [Nock.Atoms.p, Nock.Field.p])
        (by norm_num [Nock.Atoms.p, Nock.Field.p]) (by push_cast; linear_combination h)
      omega

/-- The `preg` rows counted: `Σ_i [i < |prims|] · 2 = 2·|prims|`. -/
theorem sum_preg (nL len : ℕ) (h : len ≤ nL) :
    ∑ i : Fin nL, (if (i : ℕ) < len then 2 else 0) = 2 * len := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < len then 2 else 0) nL,
    ← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_congr rfl (g := fun _ => 2) (fun i hi => if_pos (Finset.mem_range.mp hi)),
    Finset.sum_congr rfl (g := fun _ => 0) (fun i hi => if_neg (by have := (Finset.mem_Ico.mp hi).1; omega))]
  simp [mul_comm]

theorem aluSL_pins_le (hALk : AcceptsJ9AL.ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL chals pubs
      (RealIOJ9AL.qAL δ b Pb tr chals pubs)) :
    (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL := by
  rcases hALk with ⟨hon, hsat, hbind, hinj, hadj, hlt, hpre⟩ | ⟨hoff, hprims, -⟩
  · have hle : Pb.prims.length ≤ Pb.nL := hpre.1
    rw [RR49AL.aluSL, if_pos hon, aluRegReqsOf, List.length_flatMap, Chips.ChipRAP.sum_finRange]
    rw [← sum_preg Pb.nL Pb.prims.length hle, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ _i : Fin Pb.nL, 2 := Finset.sum_le_sum fun i _ => ?_
      _ = 2 * Pb.nL := by simp [mul_comm]
    obtain ⟨hH, hP, hC⟩ := row_facts δ b hsat hbind hpre i
    by_cases h0 : (E0 i).trace sH = 0
    · rw [if_pos h0]; split_ifs <;> simp
    · rw [if_neg h0, if_neg (hC h0)]; simp
  · simp [RR49AL.aluSL, hoff, hprims]

theorem aluPL_le (hALk : AcceptsJ9AL.ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL chals pubs
      (RealIOJ9AL.qAL δ b Pb tr chals pubs)) :
    (RR49AL.aluPL δ b Pb tr).length ≤ 2 * Pb.nL := by
  rcases hALk with ⟨hon, hsat, hbind, hinj, hadj, hlt, hpre⟩ | ⟨hoff, hprims, -⟩
  · rw [RR49AL.aluPL, if_pos hon, List.length_append, aluRegProvsOf, aluJetProvsOf, List.length_flatMap,
      List.length_flatMap, ← List.sum_map_add, Chips.ChipRAP.sum_finRange]
    calc _ ≤ ∑ _i : Fin Pb.nL, 2 := Finset.sum_le_sum fun i _ => ?_
      _ = 2 * Pb.nL := by simp [mul_comm]
    obtain ⟨hH, hP, hC⟩ := row_facts δ b hsat hbind hpre i
    by_cases hl : (i : ℕ) < Pb.prims.length
    · have hH0 : (E0 i).trace sH = 0 := by_contra fun h => hC h hl
      rw [if_pos (show (E0 i).trace sH * (E0 i).trace mJ = 0 by rw [hH0, zero_mul])]; split_ifs <;> simp
    · have hP0 : (E0 i).trace sP = 0 := by rw [hP, if_neg hl]
      rw [if_pos (show (E0 i).trace sP * (E0 i).trace mP = 0 by rw [hP0, zero_mul])]; split_ifs <;> simp
  · simp [RR49AL.aluPL, hoff]

end Count

section Fpl
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp}

theorem aluFpL_le (χ : Coins frameJ8 K) : (RR49AL.aluFpL δ b Pb tr χ).length ≤ Pb.nL := by
  unfold RR49AL.aluFpL
  split_ifs
  · unfold aluFpReqsOf
    rw [List.length_flatMap]
    calc _ ≤ ((List.finRange Pb.nL).map fun _ => 1).sum :=
          List.sum_le_sum fun i _ => by split_ifs <;> simp
      _ = Pb.nL := by simp
  · simp

end Fpl

end

end Nock.NockVMROM.Thm54.VclL.Handle.CountAL
