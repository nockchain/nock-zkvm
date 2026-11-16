/-
  Nock/RedTeam/Batch534Thm54CrossingVmem.lean

  **The `u ≠ w` read/verify crossing at `Vmem`/`eqBlk`.**

  Forest `S = cons(R, w)`, `R = cons(u, v)`, `u ≠ w`.  Compute requests
  `(fp R, fp w, 2, ts)` (claims `/[2 R] = w`).  Prover places `read_root`
  at R (interior, left child of S) and `verify_child` at w (right child
  of S), `ver = true` at the read only.

  Accounting at S under form R (`λ = C' = 1`, `pwScaleExp = 63`, axis `2`):
  R-branch `(−2·ts, −2·ts)`, T-branch `(ts, ts)`; decompose gives
  `ind = −ts` and `counts = 0`.  Every row satisfies `Vmem`.
  Intermediate adds the record at the read and removes it at the verify.
  The lookup is FALSE: `Noun.slot 2 (cell u v) = u ≠ w`.

  Same tree shape as `` `AxisBridge.lean::readVerifyNested_wall` ``
  (`S = cons(cons(a₀,a₀), a₀)` there has `u = w = a₀`, so the *record*
  is a genuine lookup; here `u ≠ w` makes it a forgery).  Nested is
  FALSE on that shape.

  A full
  `memoryChipAt c` interpolant is not constructed.

  An
  unset `lambda?` used to read the table constant `1`; it now reads the package
  `λ = formRDefault = 2`.  The rows, the accounting and the claim are unchanged (still `λ = 1`).
-/
import Nock.MemoryTable
import Nock.Reference
import Nock.AxisBridge
import Nock.AxisBatching
import Nock.NockVMROM.Thm54.StrengtheningScope
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false

namespace Nock.RedTeam.Batch534

open Nock
open Nock.ComputeTable (FP MemRec)
open Nock.MemoryTable
open Nock.Thm54.StrengtheningScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.AxisBatching
open Nock.AxisBatching.MTree

variable {K : Type*} [Field K]

/-! ## Crossing rows (individual defs so `eqBlk` reduces) -/

noncomputable def nU (inp : Inputs K) (u : K) : FP K := FP.atomFP inp.z u
noncomputable def nV (inp : Inputs K) (v : K) : FP K := FP.atomFP inp.z v
noncomputable def nW (inp : Inputs K) (w : K) : FP K := FP.atomFP inp.z w
noncomputable def nR (inp : Inputs K) (u v : K) : FP K :=
  FP.cons inp.z (nU inp u) (nV inp v)
noncomputable def nS (inp : Inputs K) (u v w : K) : FP K :=
  FP.cons inp.z (nR inp u v) (nW inp w)
noncomputable def forgedRec (inp : Inputs K) (u v w ts : K) : MemRec K :=
  ⟨nR inp u v, nW inp w, 2, ts⟩

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

noncomputable def decR (inp : Inputs K) (u v : K) : Pub K where
  st := .decompose
  pt := ⟨nR inp u v, 0, 0⟩
  lc := ⟨nU inp u, 0, 0⟩
  rc := ⟨nV inp v, 0, 0⟩
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

/-- Form R `read_root` at axis `2`: `Δpw = Δcounts = −2·ts`. -/
noncomputable def readR (inp : Inputs K) (u v w ts : K) : Pub K where
  st := .read_root
  pt := ⟨nR inp u v, -(2 * ts), -(2 * ts)⟩
  lc := ⟨nR inp u v, 0, 0⟩
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := forgedRec inp u v w ts
  ipre := 0
  icur := (pole inp (forgedRec inp u v w ts) 1)⁻¹
  ver := true
  lambda? := some 1

/-- Form R `verify_child`: both accumulators add `λ^{63}·ts = ts`. -/
noncomputable def verW (inp : Inputs K) (u v w ts : K) : Pub K where
  st := .verify_child
  pt := ⟨nW inp w, ts, ts⟩
  lc := ⟨nW inp w, 0, 0⟩
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := forgedRec inp u v w ts
  ipre := (pole inp (forgedRec inp u v w ts) 1)⁻¹
  icur := 0
  ver := false
  lambda? := some 1

/-- Form R decompose of the crossing: `ind = −ts`, `counts = 0`. -/
noncomputable def decS (inp : Inputs K) (u v w ts : K) : Pub K where
  st := .decompose
  pt := ⟨nS inp u v w, -ts, 0⟩
  lc := ⟨nR inp u v, -(2 * ts), -(2 * ts)⟩
  rc := ⟨nW inp w, ts, ts⟩
  lcSt := .read_root
  rcSt := .verify_child
  mem := MemRec.zero
  ipre := 0
  icur := 0
  lambda? := some 1

/-! ## `eqBlk` / `Vmem` -/

private theorem eqBlk_haltU (inp : Inputs K) (u : K) :
    eqBlk inp (haltU inp u) := by
  simp [eqBlk, haltU, nU]

private theorem eqBlk_haltV (inp : Inputs K) (v : K) :
    eqBlk inp (haltV inp v) := by
  simp [eqBlk, haltV, nV]

private theorem eqBlk_haltW (inp : Inputs K) (w : K) :
    eqBlk inp (haltW inp w) := by
  simp [eqBlk, haltW, nW]

private theorem eqBlk_decR (inp : Inputs K) (u v : K) :
    eqBlk inp (decR inp u v) := by
  simp [eqBlk, decR, nR]

private theorem eqBlk_readR (inp : Inputs K) (u v w ts : K) :
    eqBlk inp (readR inp u v w ts) := by
  simp [eqBlk, readR, forgedRec, Pub.lambda, Pub.cprime,
    MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_verW (inp : Inputs K) (u v w ts : K) :
    eqBlk inp (verW inp u v w ts) := by
  simp [eqBlk, verW, forgedRec, Pub.lambda, MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_decS (inp : Inputs K) (u v w ts : K) :
    eqBlk inp (decS inp u v w ts) := by
  simp [eqBlk, decS, nS, Pub.lambda, one_pow]
  exact ⟨by ring, by ring⟩

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
  vmem_of inp _ (eqBlk_haltU inp u) (interV_halt inp (haltU inp u) rfl rfl)

theorem vmem_haltV (inp : Inputs K) (v : K) : Vmem inp (haltV inp v) :=
  vmem_of inp _ (eqBlk_haltV inp v) (interV_halt inp (haltV inp v) rfl rfl)

theorem vmem_haltW (inp : Inputs K) (w : K) : Vmem inp (haltW inp w) :=
  vmem_of inp _ (eqBlk_haltW inp w) (interV_halt inp (haltW inp w) rfl rfl)

theorem vmem_decR (inp : Inputs K) (u v : K) : Vmem inp (decR inp u v) :=
  vmem_of inp _ (eqBlk_decR inp u v) (interV_dec inp (decR inp u v) rfl rfl)

theorem vmem_readR (inp : Inputs K) (u v w ts : K) :
    Vmem inp (readR inp u v w ts) :=
  vmem_of inp _ (eqBlk_readR inp u v w ts)
    (interV_read inp (readR inp u v w ts) rfl rfl rfl)

theorem vmem_verW (inp : Inputs K) (u v w ts : K) :
    Vmem inp (verW inp u v w ts) :=
  vmem_of inp _ (eqBlk_verW inp u v w ts)
    (interV_verify inp (verW inp u v w ts) rfl rfl rfl)

theorem vmem_decS (inp : Inputs K) (u v w ts : K) :
    Vmem inp (decS inp u v w ts) :=
  vmem_of inp _ (eqBlk_decS inp u v w ts)
    (interV_dec inp (decS inp u v w ts) rfl rfl)

theorem crossing_root_zeros (inp : Inputs K) (u v w ts : K) :
    (decS inp u v w ts).pt.indicator = -ts ∧
      (decS inp u v w ts).pt.counts = 0 :=
  ⟨rfl, rfl⟩

theorem crossing_read_leftover (inp : Inputs K) (u v w ts : K) :
    (readR inp u v w ts).pt.indicator = -(2 * ts) ∧
      (readR inp u v w ts).pt.counts = -(2 * ts) := by
  simp [readR]

theorem crossing_served_record (inp : Inputs K) (u v w ts : K) :
    (readR inp u v w ts).ver = true ∧
      (verW inp u v w ts).ver = false ∧
      (readR inp u v w ts).mem = forgedRec inp u v w ts ∧
      (verW inp u v w ts).mem = forgedRec inp u v w ts ∧
      responseRecords (readR inp u v w ts) = [forgedRec inp u v w ts] ∧
      responseRecords (verW inp u v w ts) = [] := by
  simp [readR, verW, responseRecords, forgedRec]

/-- Concrete ℚ instance: `u = 5`, `v = 6`, `w = 0`, `ts = 1`. -/
theorem crossing_vmem_rat :
    let inp : Inputs ℚ := { z := 2, γ := 0, β := 0 }
    Vmem inp (readR inp 5 6 0 1) ∧ Vmem inp (verW inp 5 6 0 1) ∧
      Vmem inp       (decS inp 5 6 0 1) ∧
      (decS inp 5 6 0 1).pt.indicator = -1 ∧
      (decS inp 5 6 0 1).pt.counts = 0 := by
  intro inp
  exact ⟨vmem_readR inp 5 6 0 1, vmem_verW inp 5 6 0 1, vmem_decS inp 5 6 0 1,
    rfl, rfl⟩

/-! ## The lookup is false -/

theorem slot2_is_head (u v : ℕ) :
    Noun.slot 2 (Noun.cell (Noun.atom u) (Noun.atom v)) = some (Noun.atom u) := by
  simp [Noun.slot]

theorem slot3_is_tail (u v w : ℕ) :
    Noun.slot 3 (Noun.cell (Noun.cell (Noun.atom u) (Noun.atom v)) (Noun.atom w)) =
      some (Noun.atom w) := by
  simp [Noun.slot]

theorem crossing_lookup_false (u v w : ℕ) (h : u ≠ w) :
    Noun.slot 2 (Noun.cell (Noun.atom u) (Noun.atom v)) = some (Noun.atom u) ∧
      (some (Noun.atom u) : Option Noun) ≠ some (Noun.atom w) := by
  refine ⟨slot2_is_head u v, ?_⟩
  intro heq
  exact h (by simp at heq; exact heq)

theorem forged_double_head_eq_tail (u v w : ℕ) (h : u ≠ w) :
    let R := Noun.cell (Noun.atom u) (Noun.atom v)
    let S := Noun.cell R (Noun.atom w)
    Noun.slot 2 S = some R ∧
      Noun.slot 3 S = some (Noun.atom w) ∧
      Noun.slot 2 R = some (Noun.atom u) ∧
      Noun.slot 2 R ≠ Noun.slot 3 S := by
  intro R S
  refine ⟨by simp [Noun.slot, R, S], by simp [Noun.slot, R, S],
    slot2_is_head u v, ?_⟩
  intro heq
  have : some (Noun.atom u) = some (Noun.atom w) := by
    simpa [R, S, Noun.slot] using heq
  exact h (by simp at this; exact this)

/-! ## Same shape as the wall -/

theorem crossing_shape_is_the_wall (e : ℕ) :
    let t : MTree ℚ :=
      .decompose (.read e (.decompose .halt .halt)) (.verify e (2 : ℚ) .halt)
    indP_bin t = 0 ∧ countsP_bin t = 0 ∧ ¬ AxisBridge.ReadVerifyNested t :=
  let h := AxisBridge.readVerifyNested_wall (K := ℚ) e
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem nested_load_bearing_same_shape (e : ℕ) :
    let t : MTree ℚ :=
      .decompose (.read e .halt) (.verify e (2 : ℚ) .halt)
    indP_bin t = 0 ∧ countsP_bin t = 0 ∧ ¬ Nested e t :=
  let h := AxisBridge.nested_load_bearing (K := ℚ) e
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

/-! ## Item F -/

theorem eqBlk_admits_negative_indicator
    (inp : Inputs K) (u v w ts : K) :
    eqBlk inp (readR inp u v w ts) ∧
      (readR inp u v w ts).pt.indicator = -(2 * ts) := by
  refine ⟨eqBlk_readR inp u v w ts, ?_⟩
  simp [readR]

theorem paperKGates_still_49 :
    (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  paperKGates_length

theorem rootMask_still_two_endpoint_gates :
    rootMaskCountsGate (F := ℚ) ∈ paperEndpointGates (F := ℚ) ∧
      rootMaskIndicatorGate (F := ℚ) ∈ paperEndpointGates (F := ℚ) := by
  simp [paperEndpointGates]

theorem chip_interpolant_not_constructed :
    (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  paperKGates_length

theorem crossing_vmem (inp : Inputs K) (u v w ts : K) :
    Vmem inp (readR inp u v w ts) ∧ Vmem inp (verW inp u v w ts) ∧
      Vmem inp (decS inp u v w ts) :=
  ⟨vmem_readR inp u v w ts, vmem_verW inp u v w ts, vmem_decS inp u v w ts⟩

end Nock.RedTeam.Batch534

#print axioms Nock.RedTeam.Batch534.crossing_vmem
#print axioms Nock.RedTeam.Batch534.crossing_lookup_false
#print axioms Nock.RedTeam.Batch534.crossing_shape_is_the_wall
#print axioms Nock.RedTeam.Batch534.eqBlk_admits_negative_indicator
