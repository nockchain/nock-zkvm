/-
  Nock/RedTeam/Batch519Thm54CancellationAttack.lean

  At the deployed memory chip `ver` (role 39) is read only by `verBool`
  (`ver·(ver−1)=0`), the LogUp `contribution`/`safeInverse`, and nothing
  else; `timestampGate` (`paperClassGate 22`) pins `timestamp = 0` only at
  `decompose`/`halt`.  A `read_root`/`verify_child`
  pair with `ver = 0` is a legal forest descent whose record is NOT served
  (absent from `responseRecords`, hence unbound by LIO) and whose
  `timestamp` is a FREE trace value.

  Both `axis_counts` and
  `axis_indicator` returned to zero.

  **Form R:** the same chained forest still satisfies every row-local
  `eqBlk`/`Vmem`, but the two residuals cannot vanish together when
  `a' ≠ b'` (`λ = C' = 1` subtracts the same `axis·ts` from both
  accumulators).

  Compiled at the row/`eqBlk` level.  A full `memoryChipAt c` interpolant
  of the extra rows is not constructed (it would change `memRows`).

  An
  unset `lambda?` used to read the table constant `1`; it now reads the package
  `λ = formRDefault = 2`.  The rows, the accounting and the claim are unchanged (still `λ = 1`).
-/
import Nock.MemoryTable
import Nock.NockVMROM.Thm54.StrengtheningScope
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false

namespace Nock.RedTeam.Batch519

open Nock
open Nock.ComputeTable (FP MemRec)
open Nock.MemoryTable
open Nock.Thm54.StrengtheningScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

variable {K : Type*} [Field K]

/-! ## The free timestamp of an unserved pair -/

theorem timestampGate_is_class_22 :
    timestampGate (K := ℚ) (F := ℚ) = paperClassGate (K := ℚ) (F := ℚ) 22 :=
  rfl

/-! ## Cancellation timestamp -/

/-- `ts_u` that cancels a wrong-axis residual `(a' − 3)·ts_r` against a
    second pair at claimed axis `b' ≠ 3` on the same right-child descent. -/
noncomputable def cancelTs (a' b' ts_r : K) : K :=
  -(a' - 3) / (b' - 3) * ts_r

theorem cancelTs_clears_residual (a' b' ts_r : K) (hb : b' ≠ 3) :
    (a' - 3) * ts_r + (b' - 3) * cancelTs a' b' ts_r = 0 := by
  have hden : (b' - 3) ≠ 0 := sub_ne_zero.2 hb
  simp only [cancelTs]
  field_simp [hden]
  ring

/-! ## F97-shaped descent with a second pair on the same right child -/

structure CancelRows (K : Type*) where
  rRootS : Pub K
  rRootU : Pub K
  rDec   : Pub K
  rVCS   : Pub K
  rVCU   : Pub K
  rHL    : Pub K
  rHR    : Pub K

/-- Seven-row F97-shaped walk: served then unserved `read_root` over the
    same cons, one `decompose`, two chained `verify_child`s at the right
    atom, two `halt`s.  Cells satisfy form-R `eqBlk` and the parent/child
    chain; the 2-adic `/2` residual is gone. -/
noncomputable def cancelAttack (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) : CancelRows K :=
  let tu := cancelTs a' b' ts_r
  let consN := FP.cons inp.z nL nR
  let recS : MemRec K := ⟨consN, nR, a', ts_r⟩
  let recU : MemRec K := ⟨consN, nR, b', tu⟩
  { rHR :=
      { st := .halt, pt := ⟨nR, 0, 0⟩, lc := Cell.zero, rc := Cell.zero
        lcSt := .halt, rcSt := .halt, mem := MemRec.zero, ipre := 0, icur := 0, lambda? := some 1 }
    rHL :=
      { st := .halt, pt := ⟨nL, 0, 0⟩, lc := Cell.zero, rc := Cell.zero
        lcSt := .halt, rcSt := .halt, mem := MemRec.zero, ipre := 0, icur := 0, lambda? := some 1 }
    rVCU :=
      { st := .verify_child
        pt := ⟨nR, tu, tu⟩
        lc := ⟨nR, 0, 0⟩
        rc := Cell.zero
        lcSt := .verify_child, rcSt := .halt
        mem := recU
        ipre := (pole inp recU 1)⁻¹, icur := 0, lambda? := some 1 }
    rVCS :=
      { st := .verify_child
        pt := ⟨nR, tu + ts_r, tu + ts_r⟩
        lc := ⟨nR, tu, tu⟩
        rc := Cell.zero
        lcSt := .verify_child, rcSt := .halt
        mem := recS
        ipre := (pole inp recS 1)⁻¹, icur := 0, lambda? := some 1 }
    rDec :=
      { st := .decompose
        pt := ⟨consN, tu + ts_r, (2 : K) * (tu + ts_r)⟩
        lc := ⟨nL, 0, 0⟩
        rc := ⟨nR, tu + ts_r, tu + ts_r⟩
        lcSt := .halt, rcSt := .verify_child
        mem := MemRec.zero, ipre := 0, icur := 0, lambda? := some 1 }
    rRootU :=
      { st := .read_root
        pt := ⟨consN, (tu + ts_r) - b' * tu, (2 : K) * (tu + ts_r) - b' * tu⟩
        lc := ⟨consN, tu + ts_r, (2 : K) * (tu + ts_r)⟩
        rc := Cell.zero
        lcSt := .read_root, rcSt := .halt
        mem := recU
        ipre := 0, icur := (pole inp recU 1)⁻¹
        ver := false, lambda? := some 1 }
    rRootS :=
      { st := .read_root
        pt := ⟨consN,
          ((tu + ts_r) - b' * tu) - a' * ts_r,
          ((2 : K) * (tu + ts_r) - b' * tu) - a' * ts_r⟩
        lc := ⟨consN, (tu + ts_r) - b' * tu, (2 : K) * (tu + ts_r) - b' * tu⟩
        rc := Cell.zero
        lcSt := .read_root, rcSt := .halt
        mem := recS
        ipre := 0, icur := (pole inp recS 1)⁻¹
        ver := true, lambda? := some 1 } }

private theorem eqBlk_served_root (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) :
    eqBlk inp (cancelAttack inp a' b' ts_r nL nR).rRootS := by
  simp [eqBlk, cancelAttack, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_unserved_root (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) :
    eqBlk inp (cancelAttack inp a' b' ts_r nL nR).rRootU := by
  simp [eqBlk, cancelAttack, Pub.lambda, Pub.cprime, MemoryTable.pwScaleExp, one_pow]

private theorem eqBlk_decompose (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) :
    eqBlk inp (cancelAttack inp a' b' ts_r nL nR).rDec := by
  simp [eqBlk, cancelAttack, Pub.lambda]
  try ring

private theorem eqBlk_served_verify (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) :
    eqBlk inp (cancelAttack inp a' b' ts_r nL nR).rVCS := by
  simp [eqBlk, cancelAttack, Pub.lambda, MemoryTable.pwScaleExp, one_pow]
  try ring

private theorem eqBlk_unserved_verify (inp : Inputs K) (a' b' ts_r : K)
    (nL nR : FP K) :
    eqBlk inp (cancelAttack inp a' b' ts_r nL nR).rVCU := by
  simp [eqBlk, cancelAttack, Pub.lambda, MemoryTable.pwScaleExp, one_pow]

private theorem interV_read (inp : Inputs K) (p : Pub K)
    (hst : p.st = .read_root) (hipre : p.ipre = 0)
    (hicur : p.icur = (pole inp p.mem p.cprime)⁻¹) :
    interV inp p := by
  simp [interV, hst, hipre, hicur]

private theorem interV_verify (inp : Inputs K) (p : Pub K)
    (hst : p.st = .verify_child) (hicur : p.icur = 0)
    (hipre : p.ipre = (pole inp p.mem p.cprime)⁻¹) :
    interV inp p := by
  simp [interV, hst, hipre, hicur]

private theorem vmem_of (inp : Inputs K) (p : Pub K)
    (heq : eqBlk inp p) (hin : interV inp p) : Vmem inp p :=
  ⟨verBool_holds p, heq, hin⟩

/-- Form R walk-root residual (2-adic `counts = 0` does not survive). -/
theorem cancelAttack_root_residual
    (inp : Inputs K) (a' b' ts_r : K) (nL nR : FP K) :
    let tu := cancelTs a' b' ts_r
    let r := cancelAttack inp a' b' ts_r nL nR
    r.rRootS.pt.indicator = (tu + ts_r) - b' * tu - a' * ts_r ∧
      r.rRootS.pt.counts = (2 : K) * (tu + ts_r) - b' * tu - a' * ts_r := by
  intro tu r
  constructor
  · simp [r, cancelAttack, tu]
  · simp [r, cancelAttack, tu]

/-- Dummy T=1
    remaining leaves walk-root counts `tu + ts_r`. -/
theorem cancelAttack_root_counts_zero
    (inp : Inputs K) (a' b' ts_r : K) (nL nR : FP K) :
    let tu := cancelTs a' b' ts_r
    (cancelAttack inp a' b' ts_r nL nR).rRootS.pt.counts =
      (2 : K) * (tu + ts_r) - b' * tu - a' * ts_r :=
  (cancelAttack_root_residual inp a' b' ts_r nL nR).2

theorem cancelAttack_tsu
    (inp : Inputs K) (a' b' ts_r : K) (nL nR : FP K) :
    (cancelAttack inp a' b' ts_r nL nR).rRootU.mem.ts = cancelTs a' b' ts_r :=
  rfl

/-- **The cancellation attack** at `Vmem`/`eqBlk` on the F97-shaped descent.

    Served pair at wrong axis `a'` with timestamp `ts_r`; unrequested
    `ver = 0` pair on the same right-child descent at axis `b' ≠ 3` with
    `ts_u = cancelTs`.  Every row-local `Vmem` holds and the unserved
    record is absent from `responseRecords`.  Form R does not return both
    walk-root accumulators to zero. -/
theorem unserved_pair_cancels_wrong_axis
    (inp : Inputs K)
    (a' b' ts_r : K)
    (nL nR : FP K) (hL : AtomShape inp.z nL) (hR : AtomShape inp.z nR) :
    let r := cancelAttack inp a' b' ts_r nL nR
    r.rRootS.st = .read_root ∧ r.rRootS.ver = true ∧ Vmem inp r.rRootS ∧
      r.rRootU.st = .read_root ∧ r.rRootU.ver = false ∧ Vmem inp r.rRootU ∧
      r.rDec.st = .decompose ∧ Vmem inp r.rDec ∧
      r.rVCS.st = .verify_child ∧ Vmem inp r.rVCS ∧
      r.rVCU.st = .verify_child ∧ r.rVCU.ver = false ∧ Vmem inp r.rVCU ∧
      r.rHL.st = .halt ∧ Vmem inp r.rHL ∧
      r.rHR.st = .halt ∧ Vmem inp r.rHR ∧
      r.rRootS.lc = r.rRootU.pt ∧ r.rRootU.lc = r.rDec.pt ∧
        r.rDec.lc = r.rHL.pt ∧ r.rDec.rc = r.rVCS.pt ∧
        r.rVCS.lc = r.rVCU.pt ∧ r.rVCU.lc = r.rHR.pt ∧
      r.rRootS.mem.axis = a' ∧ r.rRootS.mem.ts = ts_r ∧
      r.rRootU.mem.axis = b' ∧ r.rRootU.mem.ts = cancelTs a' b' ts_r ∧
      responseRecords r.rRootU = [] ∧
      responseRecords r.rVCU = [] ∧
      responseRecords r.rRootS = [r.rRootS.mem] := by
  intro r
  have hinS : interV inp r.rRootS :=
    interV_read inp r.rRootS rfl rfl rfl
  have hinU : interV inp r.rRootU :=
    interV_read inp r.rRootU rfl rfl rfl
  have hinVS : interV inp r.rVCS :=
    interV_verify inp r.rVCS rfl rfl rfl
  have hinVU : interV inp r.rVCU :=
    interV_verify inp r.rVCU rfl rfl rfl
  refine ⟨rfl, rfl, vmem_of inp _ (eqBlk_served_root inp a' b' ts_r nL nR) hinS,
    rfl, rfl, vmem_of inp _ (eqBlk_unserved_root inp a' b' ts_r nL nR) hinU,
    rfl, vmem_of inp _ (eqBlk_decompose inp a' b' ts_r nL nR) rfl,
    rfl, vmem_of inp _ (eqBlk_served_verify inp a' b' ts_r nL nR) hinVS,
    rfl, rfl, vmem_of inp _ (eqBlk_unserved_verify inp a' b' ts_r nL nR) hinVU,
    rfl, vmem_of inp _ ⟨hL.1, hL.2, rfl, rfl, rfl, rfl, rfl⟩ rfl,
    rfl, vmem_of inp _ ⟨hR.1, hR.2, rfl, rfl, rfl, rfl, rfl⟩ rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unserved_read_root_fails_ver_gate
    (inp : Inputs K) (a' b' ts_r : K) (nL nR : FP K) :
    let r := cancelAttack inp a' b' ts_r nL nR
    r.rRootU.st = .read_root ∧ r.rRootU.ver = false ∧
      (if r.rRootU.st = .read_root then (1 : K) else 0) *
        (1 - if r.rRootU.ver then (1 : K) else 0) = 1 := by
  intro r
  constructor
  · rfl
  constructor
  · rfl
  · have hst : r.rRootU.st = .read_root := rfl
    have hver : r.rRootU.ver = false := rfl
    simp [hst, hver]

/-- Concrete ℚ instance: served axis `5`, unserved axis `7`, `ts_r = 1`,
    `ts_u = −1/2`. -/
theorem unserved_pair_cancels_wrong_axis_rat :
    let inp : Inputs ℚ := { z := 2, γ := 0, β := 0 }
    let r := cancelAttack inp (5 : ℚ) 7 1 (FP.atomFP 2 0) (FP.atomFP 2 1)
    r.rRootS.ver = true ∧ r.rRootU.ver = false ∧
      Vmem inp r.rRootS ∧ Vmem inp r.rRootU ∧
      r.rRootS.mem.axis = (5 : ℚ) ∧ r.rRootU.mem.axis = (7 : ℚ) ∧
      r.rRootU.mem.ts = (-1 / 2 : ℚ) ∧
      responseRecords r.rRootU = [] := by
  intro inp r
  have hL : AtomShape (2 : ℚ) (FP.atomFP (2 : ℚ) 0) := atomFP_atomShape _ _
  have hR : AtomShape (2 : ℚ) (FP.atomFP (2 : ℚ) 1) := atomFP_atomShape _ _
  have h := unserved_pair_cancels_wrong_axis (K := ℚ) inp 5 7 1
    (FP.atomFP 2 0) (FP.atomFP 2 1) hL hR
  refine ⟨rfl, rfl, h.2.2.1, h.2.2.2.2.2.1, rfl, rfl, ?tsu, rfl⟩
  · rw [cancelAttack_tsu]; simp [cancelTs]; norm_num

/-! ## Chip census: the missing pin is not committed -/

theorem paperBaseGates_length_still_five :
    (paperBaseGates (F := ℚ)).length = 5 :=
  paperBaseGates_length

theorem verBool_is_in_ioCore :
    Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.verBool (F := ℚ) ∈
      ioCoreGates (F := ℚ) := by
  simp [ioCoreGates]

/-- A full `memoryChipAt c` interpolant of these extra rows is not
    constructed: it would change `memRows`. -/
theorem chip_interpolant_not_constructed :
    (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  paperKGates_length

end Nock.RedTeam.Batch519

#print axioms Nock.RedTeam.Batch519.unserved_pair_cancels_wrong_axis
#print axioms Nock.RedTeam.Batch519.unserved_read_root_fails_ver_gate
#print axioms Nock.RedTeam.Batch519.cancelTs_clears_residual
