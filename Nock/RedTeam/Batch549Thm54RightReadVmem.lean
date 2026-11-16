/-
  Nock/RedTeam/Batch549Thm54RightReadVmem.lean

  Forest `S = cons(L, w)`, `L = cons(u, v)`, `v ≠ w`.  Compute requests `(fp w, fp v, 1, ts)`
  (claims `/[1 w] = v`, i.e. `w = v`).  Prover serves it with `read_root` at `w` (S's RIGHT
  child, `ver = true`) and `verify_child` at `v` (the head's tail, `ver = false`).

  Accounting: at `L`, `ind = 0 + ts = ts`, `2·counts = 0 + ts − ts = 0`;
  at `S`, `ind = ts − ts = 0`, `2·counts = 0 + (−ts) − (−ts) = 0`.  Every row satisfies `Vmem`.
  The read's `−ts` never reaches `counts` above it (`Batch546.read_right_invisible` at `λ = 2`),
  and this is the family the author's formula `a = addr(V) − 2^m·(addr(R) − 1)` gives at
  `addr(R) = 3`, `addr(V) = 5`, `m = 1`: `a = 5 − 2·2 = 1`.

  No `memoryChipAt c`
  interpolant.

  An
  unset `lambda?` used to read the table constant `1`; it now reads the package
  `λ = formRDefault = 2`.  The rows, the accounting and the claim are unchanged (still `λ = 1`).
-/
import Nock.MemoryTable
import Nock.Reference
import Nock.RedTeam.Batch546Thm54LambdaModel

set_option autoImplicit false

namespace Nock.RedTeam.Batch549

open Nock
open Nock.ComputeTable (FP MemRec)
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Polynomial

variable {K : Type*} [Field K]

/-! ## Rows -/

noncomputable def nU (inp : Inputs K) (u : K) : FP K := FP.atomFP inp.z u
noncomputable def nV (inp : Inputs K) (v : K) : FP K := FP.atomFP inp.z v
noncomputable def nW (inp : Inputs K) (w : K) : FP K := FP.atomFP inp.z w
noncomputable def nL (inp : Inputs K) (u v : K) : FP K :=
  FP.cons inp.z (nU inp u) (nV inp v)
noncomputable def nS (inp : Inputs K) (u v w : K) : FP K :=
  FP.cons inp.z (nL inp u v) (nW inp w)

/-- The forged record `(root = w, child = v, axis = 1, ts)`. -/
noncomputable def forgedRec (inp : Inputs K) (v w ts : K) : MemRec K :=
  ⟨nW inp w, nV inp v, 1, ts⟩

noncomputable def haltU (inp : Inputs K) (u : K) : Pub K where
  st := .halt
  pt := ⟨nU inp u, 0, 0⟩
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

noncomputable def haltV (inp : Inputs K) (v : K) : Pub K where
  st := .halt
  pt := ⟨nV inp v, 0, 0⟩
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

noncomputable def haltW (inp : Inputs K) (w : K) : Pub K where
  st := .halt
  pt := ⟨nW inp w, 0, 0⟩
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

/-- `verify_child` at `v` (the head's tail): `ind = ts`, `counts = 1·ts`. -/
noncomputable def verV (inp : Inputs K) (v w ts : K) : Pub K where
  st := .verify_child
  pt := ⟨nV inp v, ts, ts⟩
  lc := ⟨nV inp v, 0, 0⟩
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := forgedRec inp v w ts
  ipre := (pole inp (forgedRec inp v w ts) 1)⁻¹
  icur := 0
  ver := false
  lambda? := some 1

/-- `decompose` at `L = cons(u, v)`: form R `ind = ts`, `counts = 2·ts`. -/
noncomputable def decL (inp : Inputs K) (u v ts : K) : Pub K where
  st := .decompose
  pt := ⟨nL inp u v, ts, (2 : K) * ts⟩
  lc := ⟨nU inp u, 0, 0⟩
  rc := ⟨nV inp v, ts, ts⟩
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

/-- `read_root` at `w` (S's RIGHT child): `ind = counts = −ts`. -/
noncomputable def readW (inp : Inputs K) (v w ts : K) : Pub K where
  st := .read_root
  pt := ⟨nW inp w, -ts, -ts⟩
  lc := ⟨nW inp w, 0, 0⟩
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := forgedRec inp v w ts
  ipre := 0
  icur := (pole inp (forgedRec inp v w ts) 1)⁻¹
  ver := true
  lambda? := some 1

/-- `decompose` at `S = cons(L, w)`: `ind = ts + (−ts) = 0`, `2·counts = 0 + (−ts) − (−ts) = 0`. -/
noncomputable def decS (inp : Inputs K) (u v w ts : K) : Pub K where
  st := .decompose
  pt := ⟨nS inp u v w, 0, 0⟩
  lc := ⟨nL inp u v, ts, (2 : K) * ts⟩
  rc := ⟨nW inp w, -ts, -ts⟩
  lcSt := .decompose
  rcSt := .read_root
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

/-! ## `eqBlk` / `Vmem` -/

private theorem eqBlk_haltU (inp : Inputs K) (u : K) : eqBlk inp (haltU inp u) := by
  simp [eqBlk, haltU, nU]

private theorem eqBlk_haltV (inp : Inputs K) (v : K) : eqBlk inp (haltV inp v) := by
  simp [eqBlk, haltV, nV]

private theorem eqBlk_haltW (inp : Inputs K) (w : K) : eqBlk inp (haltW inp w) := by
  simp [eqBlk, haltW, nW]

private theorem eqBlk_verV (inp : Inputs K) (v w ts : K) : eqBlk inp (verV inp v w ts) := by
  simp [eqBlk, verV, forgedRec, Pub.lambda, MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_decL (inp : Inputs K) (u v ts : K) : eqBlk inp (decL inp u v ts) := by
  simp [eqBlk, decL, nL, Pub.lambda]; ring

private theorem eqBlk_readW (inp : Inputs K) (v w ts : K) : eqBlk inp (readW inp v w ts) := by
  simp [eqBlk, readW, forgedRec, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_decS (inp : Inputs K) (u v w ts : K) : eqBlk inp (decS inp u v w ts) := by
  simp [eqBlk, decS, nS, Pub.lambda]; ring

private theorem interV_halt (inp : Inputs K) (p : Pub K)
    (hst : p.st = .halt) (heq : p.icur = p.ipre) : interV inp p := by
  simp [interV, hst, heq]

private theorem interV_dec (inp : Inputs K) (p : Pub K)
    (hst : p.st = .decompose) (heq : p.icur = p.ipre) : interV inp p := by
  simp [interV, hst, heq]

private theorem interV_read (inp : Inputs K) (p : Pub K)
    (hst : p.st = .read_root) (hipre : p.ipre = 0)
    (hicur : p.icur = (pole inp p.mem p.cprime)⁻¹) : interV inp p := by
  simp [interV, hst, hipre, hicur]

private theorem interV_verify (inp : Inputs K) (p : Pub K)
    (hst : p.st = .verify_child) (hicur : p.icur = 0)
    (hipre : p.ipre = (pole inp p.mem p.cprime)⁻¹) : interV inp p := by
  simp [interV, hst, hipre, hicur]

private theorem vmem_of (inp : Inputs K) (p : Pub K)
    (heq : eqBlk inp p) (hin : interV inp p) : Vmem inp p :=
  ⟨verBool_holds p, heq, hin⟩

theorem vmem_haltU (inp : Inputs K) (u : K) : Vmem inp (haltU inp u) :=
  vmem_of inp _ (eqBlk_haltU inp u) (interV_halt inp _ rfl rfl)

theorem vmem_haltV (inp : Inputs K) (v : K) : Vmem inp (haltV inp v) :=
  vmem_of inp _ (eqBlk_haltV inp v) (interV_halt inp _ rfl rfl)

theorem vmem_haltW (inp : Inputs K) (w : K) : Vmem inp (haltW inp w) :=
  vmem_of inp _ (eqBlk_haltW inp w) (interV_halt inp _ rfl rfl)

theorem vmem_verV (inp : Inputs K) (v w ts : K) : Vmem inp (verV inp v w ts) :=
  vmem_of inp _ (eqBlk_verV inp v w ts)
    (interV_verify inp _ rfl rfl (by simp [verV, Pub.cprime]))

theorem vmem_decL (inp : Inputs K) (u v ts : K) : Vmem inp (decL inp u v ts) :=
  vmem_of inp _ (eqBlk_decL inp u v ts) (interV_dec inp _ rfl rfl)

theorem vmem_readW (inp : Inputs K) (v w ts : K) : Vmem inp (readW inp v w ts) :=
  vmem_of inp _ (eqBlk_readW inp v w ts)
    (interV_read inp _ rfl rfl (by simp [readW, Pub.cprime]))

theorem vmem_decS (inp : Inputs K) (u v w ts : K) : Vmem inp (decS inp u v w ts) :=
  vmem_of inp _ (eqBlk_decS inp u v w ts) (interV_dec inp _ rfl rfl)

/-- All seven rows satisfy the paper's `V_mem`; the root's accumulators are `0`. -/
theorem right_read_crossing_vmem (inp : Inputs K) (u v w ts : K) :
    Vmem inp (haltU inp u) ∧ Vmem inp (haltV inp v) ∧ Vmem inp (haltW inp w)
    ∧ Vmem inp (verV inp v w ts) ∧ Vmem inp (decL inp u v ts)
    ∧ Vmem inp (readW inp v w ts) ∧ Vmem inp (decS inp u v w ts)
    ∧ (decS inp u v w ts).pt.indicator = 0 ∧ (decS inp u v w ts).pt.counts = 0 :=
  ⟨vmem_haltU inp u, vmem_haltV inp v, vmem_haltW inp w, vmem_verV inp v w ts,
    vmem_decL inp u v ts, vmem_readW inp v w ts, vmem_decS inp u v w ts, rfl, rfl⟩

/-- The interior `decompose` at `L` carries a NONZERO indicator (`ts`) with form-R counts `2·ts`. -/
theorem interior_indicator_pending (inp : Inputs K) (u v ts : K) :
    (decL inp u v ts).pt.indicator = ts ∧ (decL inp u v ts).pt.counts = (2 : K) * ts := ⟨rfl, rfl⟩

/-- The record is served once, at the read (`ver = true`); the verify serves nothing. -/
theorem served_once (inp : Inputs K) (v w ts : K) :
    responseRecords (readW inp v w ts) = [forgedRec inp v w ts]
    ∧ responseRecords (verV inp v w ts) = [] := by
  simp [readW, verV, responseRecords]

/-- Concrete ℚ instance: `u = 5`, `v = 6`, `w = 0`, `ts = 1`, `z = 2`. -/
theorem right_read_crossing_rat :
    let inp : Inputs ℚ := { z := 2, γ := 0, β := 0 }
    Vmem inp (readW inp 6 0 1) ∧ Vmem inp (verV inp 6 0 1) ∧ Vmem inp (decL inp 5 6 1)
    ∧ Vmem inp (decS inp 5 6 0 1)
    ∧ (decS inp 5 6 0 1).pt.indicator = 0 ∧ (decS inp 5 6 0 1).pt.counts = 0 := by
  intro inp
  exact ⟨vmem_readW inp 6 0 1, vmem_verV inp 6 0 1, vmem_decL inp 5 6 1, vmem_decS inp 5 6 0 1,
    rfl, rfl⟩


theorem lookup_false (u v w : ℕ) (h : v ≠ w) :
    let S := Noun.cell (Noun.cell (Noun.atom u) (Noun.atom v)) (Noun.atom w)
    Noun.slot 3 S = some (Noun.atom w)
    ∧ Noun.slot 5 S = some (Noun.atom v)
    ∧ Noun.slot 1 (Noun.atom w) = some (Noun.atom w)
    ∧ (some (Noun.atom w) : Option Noun) ≠ some (Noun.atom v) :=
  Batch546.tfull_lookup_false u v w h

theorem shape_is_t1_at_two (e : ℕ) :
    indP_bin (Batch546.t1 e (1 : ℚ)) = 0 ∧ countsP_bin (Batch546.t1 e (1 : ℚ)) = 0 := by
  have h := Batch546.t1_boundaries (K := ℚ) 2 e
  rw [Batch546.axisL_one 2 64 (by norm_num), Batch546.countsL_two] at h
  exact h

end Nock.RedTeam.Batch549

#print axioms Nock.RedTeam.Batch549.right_read_crossing_vmem
#print axioms Nock.RedTeam.Batch549.right_read_crossing_rat
#print axioms Nock.RedTeam.Batch549.lookup_false
#print axioms Nock.RedTeam.Batch549.shape_is_t1_at_two
