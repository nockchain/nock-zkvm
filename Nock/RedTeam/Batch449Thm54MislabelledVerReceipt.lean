/-
  Nock/RedTeam/Batch449Thm54MislabelledVerReceipt.lean

  **D10 mislabelled-row receipt.**

  Two-row toy: `verify_child` with `ver = true` and `read_root` with
  `ver = false`.  Old by-state list ≠ new ver list.
-/
import Nock.MemoryTable
import Nock.NockVM
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch449

open Nock
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVM

abbrev K17 := ZMod 17

instance b449_prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

def recA : MemRec K17 where
  root := FP.atomFP 1 1
  child := FP.atomFP 1 2
  axis := 3
  ts := 4

def recB : MemRec K17 where
  root := FP.atomFP 1 5
  child := FP.atomFP 1 6
  axis := 7
  ts := 8

def verifyPubMislabelled : MemoryTable.Pub K17 where
  st := .verify_child
  pt := Cell.zero
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := recA
  ipre := 0
  icur := 0
  ver := true

def readPubMislabelled : MemoryTable.Pub K17 where
  st := .read_root
  pt := Cell.zero
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := recB
  ipre := 0
  icur := 0
  ver := false

def verList : List (MemRec K17) :=
  responseRecords verifyPubMislabelled ++ responseRecords readPubMislabelled

def byStateList : List (MemRec K17) :=
  (match verifyPubMislabelled.st with
    | .read_root => [verifyPubMislabelled.mem]
    | _ => []) ++
  (match readPubMislabelled.st with
    | .read_root => [readPubMislabelled.mem]
    | _ => [])

theorem verList_eq : verList = [recA] := by
  simp [verList, responseRecords, verifyPubMislabelled, readPubMislabelled]

theorem byStateList_eq : byStateList = [recB] := by
  simp [byStateList, verifyPubMislabelled, readPubMislabelled]

theorem mislabelled_lists_disagree : verList ≠ byStateList := by
  rw [verList_eq, byStateList_eq]
  intro h
  have heq : recA = recB := List.head_eq_of_cons_eq h
  have hts := congrArg (fun r : MemRec K17 => r.ts) heq
  simp [recA, recB] at hts
  exact absurd hts (by decide : (4 : K17) ≠ 8)

def verEnc : List (Fin 9 → K17) := verList.map encRec
def byStateEnc : List (Fin 9 → K17) := byStateList.map encRec

theorem ver_enc_ne_by_state_enc : verEnc ≠ byStateEnc := by
  rw [verEnc, byStateEnc, verList_eq, byStateList_eq]
  intro h
  have heq : encRec (K := K17) recA = encRec recB := List.head_eq_of_cons_eq h
  have hts := congrArg (fun f : Fin 9 → K17 => f 7) heq
  simp [encRec, recA, recB] at hts
  exact absurd hts (by decide : (4 : K17) ≠ 8)

/-- D10 Prop receipt: mislabelled pubs make ver-list ≠ by-state list (raw and encoded). -/
theorem d10_mislabelled_receipt :
    verList ≠ byStateList ∧ verEnc ≠ byStateEnc :=
  ⟨mislabelled_lists_disagree, ver_enc_ne_by_state_enc⟩

end Nock.RedTeam.Batch449

#print axioms Nock.RedTeam.Batch449.mislabelled_lists_disagree
#print axioms Nock.RedTeam.Batch449.d10_mislabelled_receipt
