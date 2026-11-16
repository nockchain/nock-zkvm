/-
  Nock/NockVMROM/Thm54/P8Core/Batch1140Thm54CertAxesAtTraces.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1140Thm54CertAxesAtTraces`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1140Thm54CertAxesAtTraces.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1111Thm54C2CombinedAtTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1140

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.RedTeam.Batch575 (Padding)
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.DeployedComputeRows (pkgHchar)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

section Generic

open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.RedTeam.Batch575
open scoped Classical
variable {F : Type} [Field F]

/-- `pow_csum_cert64` (private in `OptimizedComputeCanonicalSatisfaction`), verbatim:
`2^{certShift a} · csum = a` when the certificate columns are `a`'s bits. -/
theorem pow_csum_cert64' (env : Env F) (a : ℕ) (ha0 : 0 < a) (ha : a < 2 ^ 64)
    (h2 : (2 : F) ≠ 0)
    (hC : ∀ j, j < 63 →
      env.trace (col0 + j) = if certCBit a j then (1 : F) else 0) :
    (2 : F) ^ certShift a * (csum (F := F)).eval env = (a : F) := by
  set m := certShift a with hm
  have hm63 : m ≤ 63 := certShift_le_63_of_lt_64 a ha
  have htwo (k : ℕ) (hk : k ≤ m) :
      (2 : F) ^ m * twoInv ^ k = (2 : F) ^ (m - k) := by
    have hkpow : (2 : F) ^ k ≠ 0 := pow_ne_zero k h2
    have hn : (2 : F) ^ m = (2 : F) ^ (m - k) * (2 : F) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc (2 : F) ^ m * twoInv ^ k
        = (2 : F) ^ m * ((2 : F) ^ k)⁻¹ := by rw [twoInv, inv_pow]
      _ = ((2 : F) ^ (m - k) * (2 : F) ^ k) * ((2 : F) ^ k)⁻¹ := by rw [hn]
      _ = (2 : F) ^ (m - k) * ((2 : F) ^ k * ((2 : F) ^ k)⁻¹) := by ring
      _ = (2 : F) ^ (m - k) := by rw [mul_inv_cancel₀ hkpow, mul_one]
  have hacc : ∀ n, n ≤ 63 →
      (2 : F) ^ m * (csumAcc (F := F) n).eval env =
        (2 : F) ^ m +
          ∑ i ∈ Finset.range (min n m),
            (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
    intro n hn
    induction n with
    | zero => simp [csumAcc, CoeffExpr.eval]
    | succ n ih =>
        have ihn := ih (Nat.le_of_succ_le hn)
        simp only [csumAcc, CoeffExpr.eval, colC, bcur]
        have hc := hC n (by omega)
        by_cases hnm : n < m
        · have hbit : certCBit a n = a.testBit (m - 1 - n) := by
            have hlt : n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hlt, hm]
          rw [hc, hbit]
          have hadd := htwo (n + 1) (by omega)
          have hexp : m - (n + 1) = m - 1 - n := by omega
          calc (2 : F) ^ m *
                ((csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) * twoInv ^ (n + 1))
              = (2 : F) ^ m * (csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) *
                    ((2 : F) ^ m * twoInv ^ (n + 1)) := by ring
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min n m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) +
                  (if a.testBit (m - 1 - n) then (2 : F) ^ (m - 1 - n) else 0) := by
                    rw [ihn, hadd, hexp]
                    by_cases hb : a.testBit (m - 1 - n) <;> simp [hb]
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min (n + 1) m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
                  have hmin : min n m = n := min_eq_left (Nat.le_of_lt hnm)
                  have hmin' : min (n + 1) m = n + 1 := min_eq_left hnm
                  rw [hmin, hmin', Finset.sum_range_succ]
                  ring
        · have hge : m ≤ n := by omega
          have hc0 : certCBit a n = false := by
            have hge' : ¬ n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hge']
          rw [hc, hc0]
          have hmin : min n m = m := min_eq_right hge
          have hmin' : min (n + 1) m = m := min_eq_right (Nat.le_trans hge (Nat.le_succ n))
          simp [ihn, hmin, hmin']
  have h63 := hacc 63 (by omega)
  have hmin : min 63 m = m := min_eq_right hm63
  rw [hmin] at h63
  have hreidx :
      ∑ i ∈ Finset.range m, (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) =
        ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) := by
    refine Finset.sum_nbij' (fun i => m - 1 - i) (fun j => m - 1 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      rfl
  have hcast :
      (2 : F) ^ m + ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) = (a : F) := by
    have hnat := nat_eq_certBits a ha0
    rw [← hm] at hnat
    conv_rhs => rw [hnat]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hb : a.testBit i <;> simp [hb, Nat.cast_pow]
  simpa [csum, hreidx, hcast] using h63

/-- One power factor: `1 + m_k (2^{2^k} − 1) = 2^{[bit k]·2^k}`. -/
theorem factor2_eval_of_bit (env : Env F) (m k : ℕ)
    (hk : env.trace (col0 + 63 + k) = bit01 (m.testBit k)) :
    (factor2 (F := F) k).eval env = (2 : F) ^ (if m.testBit k then 2 ^ k else 0) := by
  simp only [factor2, colM, bcur, CoeffExpr.eval, hk]
  cases m.testBit k <;> simp [bit01]

/-- **The power pins give `t = 2^m`** on a row whose shift columns are `m`'s bits, `m < 64`. -/
theorem t_eq_pow (env : Env F) (m : ℕ) (hm : m < 64)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 (m.testBit k))
    (hh : (hPin (F := F)).eval env = 0) (ht : (tPin (F := F)).eval env = 0) :
    env.trace (col0 + 70) = (2 : F) ^ m := by
  have f := fun k (hk : k < 6) => factor2_eval_of_bit env m k (hM k hk)
  simp only [hPin, tPin, CoeffExpr.eval, colHbase, colTbase, bcur, sub_eq_zero] at hh ht
  rw [ht, hh, f 0 (by decide), f 1 (by decide), f 2 (by decide), f 3 (by decide),
    f 4 (by decide), f 5 (by decide), ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have := sum_testBit_pow 6 m (by norm_num; omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at this
  simp only [pow_zero, pow_one] at this ⊢
  omega

/-- **The axis value of a padded accepted `s0` row**: the leaf column `136` is the certificate axis
`certAxis (rowShift) (rowBits)` (the axis equation, the power pins, the booleans, the C2 pin and
the padding). -/
theorem tcsum_eq_certAxis (env : Env F)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0)
    (hpad : Padding (OptimizedComputeRangeCertificate.formRN F) (DecodedLambdaEvent.rowShift env)
      (DecodedLambdaEvent.rowBits env)) :
    env.trace (col0 + 70) * (csum (F := F)).eval env =
      ((certAxis (DecodedLambdaEvent.rowShift env) (DecodedLambdaEvent.rowBits env) : ℕ) : F) := by
  have hp4 : 3 < ringChar F := hwidth.2.2
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F (ringChar F)] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set m := DecodedLambdaEvent.rowShift env with hm
  set cb := DecodedLambdaEvent.rowBits env with hcb
  have hmem : ∀ g, g ∈ booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      formRNamed → g ∈ formRCertificateGates (F := F) := fun g hg => by
    simpa [formRCertificateGates] using hg
  have hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0 := by
    intro k hk
    refine hacc _ (hmem _ ?_)
    simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
  have hm63 : m ≤ 63 := DecodedLambdaEvent.rowShift_le env
  obtain ⟨_, hR⟩ := Nock.RedTeam.Batch782.shift_cols_of_boolean env hb
  have hpos := certAxis_pos m cb
  have hlt := certAxis_lt m cb
  have hsz : certShift (certAxis m cb) = m := by
    rw [Batch972.certShift_eq_formRCertShift, formRCertShift_certAxis]
  have hA64 : certAxis m cb < 2 ^ 64 :=
    lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit (certAxis m cb) j) := by
    intro j hj
    rw [Batch972.certCBit_eq_formRCertBit, formRCertBit_certAxis]
    have hg := hacc
      (if OptimizedComputeRangeCertificate.formRN F - 1 < j + 1 then colC j else bbool (colC j))
      (hmem _ (by
        simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))))))
    have hcbj : cb (j + 1) = decide (env.trace (202 + j) = 1) := by
      rw [hcb]
      unfold DecodedLambdaEvent.rowBits
      simp only [Nat.add_sub_cancel]
      congr 1
      apply propext
      constructor
      · intro h; exact h.2.2
      · intro h; exact ⟨by omega, by omega, h⟩
    split_ifs at hg with hbig
    · have hz : env.trace (col0 + j) = 0 := by simpa [colC, bcur, CoeffExpr.eval] using hg
      have hjm : ¬ j < m := by
        have hsh : m ≤ OptimizedComputeRangeCertificate.formRN F - 1 := by
          rw [hm, Batch972.rowShift_eq_782]
          have hpP : (pPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
          have htP : (topPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRPins]))
          have hrG : (rangeGate (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [formRNamed]))
          exact Batch806.shift_le_formRN_pred env hb hpP htP hrG
        omega
      simp [hz, hjm]
    · have h01 : env.trace (col0 + j) = 0 ∨ env.trace (col0 + j) = 1 := by
        have h' : env.trace (col0 + j) * (env.trace (col0 + j) - 1) = 0 := by
          simpa [bbool, colC, bcur, CoeffExpr.eval] using hg
        rcases mul_eq_zero.mp h' with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      have hcol : col0 + j = 202 + j := rfl
      by_cases hjm : j < m
      · rw [hcbj, ← hcol]
        rcases h01 with h | h <;> simp [h, hjm]
      · have hc : cb (j + 1) = false := hpad (j + 1) (by omega) (by omega)
        rw [hcbj, ← hcol] at hc
        rcases h01 with h | h
        · simp [h, hjm]
        · simp [h] at hc
  have hcs := pow_csum_cert64' env (certAxis m cb) hpos hA64 h2 (fun j hj => by
    rw [hC j hj]; rfl)
  rw [hsz] at hcs
  have hhP : (hPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [powerPins]))
  have htPin : (tPin (F := F)).eval env = 0 := hacc _ (hmem _ (by simp [powerPins]))
  have hT := t_eq_pow env m (by omega) (fun k hk => by
    have := hR k hk; rw [← Batch972.rowShift_eq_782] at this; exact this) hhP htPin
  rw [hT, hcs]

theorem axis_gate_of (env : Env F)
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0) :
    (axisEquation (F := F)).eval env = 0 :=
  hacc _ (by simp [formRCertificateGates, formRNamed])

/-- **OP0: the leaf column `136` is the certificate axis.** -/
theorem leaf136_eq_certAxis (env : Env F)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0)
    (hpad : Padding (OptimizedComputeRangeCertificate.formRN F) (DecodedLambdaEvent.rowShift env)
      (DecodedLambdaEvent.rowBits env))
    (h0 : env.trace 0 = 1) (h9 : env.trace 9 = 0) :
    env.trace 136 =
      ((certAxis (DecodedLambdaEvent.rowShift env) (DecodedLambdaEvent.rowBits env) : ℕ) : F) := by
  have hax := axis_gate_of env hacc
  rw [axis_s0_mul_term env h9, h0, one_mul, sub_eq_zero, tcsum_eq_certAxis env hwidth hacc hpad] at hax
  exact hax

/-- **OP9: the leaf column `145` is the certificate axis.** -/
theorem leaf145_eq_certAxis (env : Env F)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hacc : ∀ g ∈ formRCertificateGates (F := F), g.eval env = 0)
    (hpad : Padding (OptimizedComputeRangeCertificate.formRN F) (DecodedLambdaEvent.rowShift env)
      (DecodedLambdaEvent.rowBits env))
    (h0 : env.trace 0 = 0) (h9 : env.trace 9 = 1) :
    env.trace 145 =
      ((certAxis (DecodedLambdaEvent.rowShift env) (DecodedLambdaEvent.rowBits env) : ℕ) : F) := by
  have hax := axis_gate_of env hacc
  rw [axis_s9_mul_term env h0, h9, one_mul, sub_eq_zero, tcsum_eq_certAxis env hwidth hacc hpad] at hax
  exact hax

end Generic

section Request

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- **The request-to-read-row bridge.**  Every active compute request `(a, j)` has a
`read_root` memory row whose record exponent is `expOfAt a j`: the LogUp response row (`ver = 1`)
is `read_root` itself, or a `verify_child` row whose `intermediate` partner is; a padding row
(`decompose` / `halt`) stores the zero record (`eqBlk`), whose timestamp `0` cannot answer the
request's `α^e` (`α ≠ 0`). -/
theorem read_row_of_request (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    ∃ k : Fin P.optimized.family.problem.cfg.memRows,
      memRowStateOf (memEnvF P c Qm k) = .read_root ∧
        Batch973.expR P c Qm k = expOfAt P c Qc a j := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hsatC := hacc.compute_satisfies
  obtain ⟨i, hver, hrec, hidx⟩ := request_named_by_row_at P c Qc Qm hacc hgood hio hchar'
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    a j hact
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) hact
  have hexpOf : ∀ k : Fin P.optimized.family.problem.cfg.memRows,
      (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol →
      Batch973.expR P c Qm k = expOfAt P c Qc a j := by
    intro k hk
    show RecordCarrier.natLift _ = _
    rw [hk, hidx]; exact RecordCarrier.natLift_natCast hlt
  -- the request's timestamp is `α^e ≠ 0`; a padding row's is `0`
  have hts : (memEnvK P c Qm i).trace 26 ≠ 0 := by
    have h7 := congrFun hrec 7
    rw [rowRecord_ts_at_at P c Qc hsatC hchar' (nprSeed_ne_of_good_at P c Qc Qm hgood) a j hact,
      hostile_ln0_eq_one_at P c Qc hsatC, one_mul] at h7
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at h7
    intro h0
    apply pow_ne_zero (expOfAt P c Qc a j) hα0
    rw [← h7]; simpa using h0
  have hpadz : memoryMemRecKind (memRowStateOf (memEnvF P c Qm i)) = .padding →
      (memEnvK P c Qm i).trace 26 = 0 := by
    intro hk
    have htop := Batch974.decoded_topology P c Qc Qm hacc hgood hax hbasis hwidth
    have hF := Batch509.fmem_of_topology P c (honestQc P c Qc) (honestQm P c Qm) _ htop
      (i.val + 1) (by omega) i.isLt
    rw [ExecOfTraces.lblM_succ] at hF
    have hst : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).2.2.st =
        (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 := hF.1
    have hstate : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 =
        memRowStateOf (memEnvF P c Qm i) := Batch844.memoryStateOf_eq_memRowStateOf _
    have hm := Batch509.eqBlk_padding_mem_zero hF.2.1 (by rw [hst, hstate]; exact hk)
    have := congrArg MemRec.ts hm
    exact this
  rcases hs : memRowStateOf (memEnvF P c Qm i) with _ | _ | _ | _
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · exact ⟨i, hs, hexpOf i rfl⟩
  · have h3 := UniqueExponentsBridge.verify_sel_at P c Qm hacc.memory_satisfies i hs
    obtain ⟨k, hsel', hrec'⟩ := UniqueExponentsBridge.verify_partner_at P c Qc Qm hacc hgood hrb i h3
    have hst' := Batch973.read_state_of_sel2 P c Qc Qm hacc hgood hrb k hsel'
    have h9 := congrFun hrec' 9
    simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h9
    have hr : (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol := by
      apply (algebraMap F K).injective
      simpa [reqIdxCol] using h9.symm
    exact ⟨k, hst', hexpOf k hr⟩

end Request

section Rows

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- The decoded source reads the selector columns verbatim. -/
theorem decodeSource_trace_sel (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (k : ℕ) (hk : k < 11) :
    (StrategyOfTracesLift.decodeSource env).trace k = algebraMap F K (env.baseTrace ⟨k, by omega⟩) := by
  have h13 : k < 13 := by omega
  simp [StrategyOfTracesLift.decodeSource, Env.ofSubst,
    OptimizedComputeSubstitution.computeSubst, OptimizedComputeSubstitution.computeTraceSubst, hk,
    Expr.eval, OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv, h13]

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- **The decoded state is the one-hot selector's state.** -/
theorem rowSelector_of_state (r : Fin P.optimized.family.problem.cfg.compRows) (st : State)
    (hst : StrategyOfTracesLift.computeStateOf
      (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r)) = st) :
    rowSelector (rowEnvAt P c Qc r) = Nock.ComputeTable.opSel st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_at P c Qc hsat (pkgHchar P) r
  have hk : ∀ t : State, (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r)).trace
      (Nock.Reified.opCol t) = Nock.ComputeTable.opSel s t := by
    intro t
    rw [decodeSource_trace_sel _ _ (by cases t <;> decide)]
    exact congrFun hs t
  have h1 := hk .s1; have h2 := hk .s2; have h3 := hk .s3; have h4 := hk .s4
  have h5 := hk .s5; have h6 := hk .s6; have h7 := hk .s7; have h8 := hk .s8
  have h9 := hk .s9; have h10 := hk .cons
  simp only [Nock.Reified.opCol] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have : StrategyOfTracesLift.computeStateOf
      (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r)) = s := by
    unfold StrategyOfTracesLift.computeStateOf
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    cases s <;> simp [Nock.ComputeTable.opSel]
  rw [← hst, this, hs]

/-- The base selector column `k` of a row whose selector is `opSel st`. -/
theorem base_sel_of (r : Fin P.optimized.family.problem.cfg.compRows) (st t : State)
    (h : rowSelector (rowEnvAt P c Qc r) = Nock.ComputeTable.opSel st) :
    (Batch908.envsFam P c Qc r).trace (Nock.Reified.opCol t) = if t = st then 1 else 0 := by
  have := congrFun h t
  simp only [rowSelector, Nock.ComputeTable.opSel] at this
  apply (algebraMap F K).injective
  rw [show (Batch908.envsFam P c Qc r).trace (Nock.Reified.opCol t) =
    (rowEnvAt P c Qc r).baseTrace ⟨Nock.Reified.opCol t, by cases t <;> decide⟩ from rfl, this]
  split_ifs <;> simp

end Rows

section RowsAcc

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- The padded certificate of an active request, at the package env `envsCR`. -/
theorem request_padding (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    Padding (FormRAxisEvent.formRN K) (slotCert (Batch824.envsCR P c Qc) a j).1
      (slotCert (Batch824.envsCR P c Qc) a j).2 := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨k, hst, hexp⟩ := read_row_of_request P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact
  have hpad := Batch973.read_row_padding P c Qc Qm hacc hgood hio hrb hb1 hwidth k hst
  rw [hexp] at hpad
  obtain ⟨hds, hdb⟩ := Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar' a j hact
  rw [hds, hdb] at hpad
  exact hpad

/-- **The recovered axis of an active request is the row's certificate axis, and is below `p`**:
`certAxisOfEnvs envsCR (expOfAt a j) = certAxis (slotCert a j)` and `< ringChar K`. -/
theorem request_axis (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) =
        certAxis (slotCert (Batch824.envsCR P c Qc) a j).1 (slotCert (Batch824.envsCR P c Qc) a j).2 ∧
      certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) < ringChar K := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨hds, hdb⟩ := Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar' a j hact
  have heq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) =
      certAxis (slotCert (Batch824.envsCR P c Qc) a j).1 (slotCert (Batch824.envsCR P c Qc) a j).2 := by
    unfold certAxisOfEnvs; rw [hds, hdb]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Batch973.cert_lt P c Qc Qm hacc hgood hio hrb hb1 hwidth a j
    (request_padding P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact)

/-- **The row's own certificate, at a selector-`s` row (`s = 0` or `9`)**: `slotCert` at the
row's slot is `(rowShift, rowBits)` of the family base env, and it is padded. -/
theorem row_cert_padded (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 2)
    (hsel : (Batch908.envsFam P c Qc a).trace (if (j : ℕ) = 1 then 0 else 9) = 1)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    slotCert (Batch824.envsCR P c Qc) a j =
        (rowShift (Batch908.envsFam P c Qc a), rowBits (Batch908.envsFam P c Qc a)) ∧
      Padding (OptimizedComputeRangeCertificate.formRN F) (rowShift (Batch908.envsFam P c Qc a))
        (rowBits (Batch908.envsFam P c Qc a)) := by
  have hE := Batch908.envsCR_embeds P c Qc
  have hs : rowShift (Batch824.envsCR P c Qc a) = rowShift (Batch908.envsFam P c Qc a) :=
    Batch908.rowShift_embed (algebraMap F K) (algebraMap F K).injective _ _
      (fun k hk => hE a (265 + k) (by unfold Batch908.ReadCols; omega))
  have hbits : rowBits (Batch824.envsCR P c Qc a) = rowBits (Batch908.envsFam P c Qc a) :=
    Batch973.rowBits_embed (algebraMap F K) (algebraMap F K).injective _ _
      (fun j h1 h2 => hE a j (by unfold Batch908.ReadCols; omega))
  have hselK : ∀ col, (col = 0 ∨ col = 9) → (Batch908.envsFam P c Qc a).trace col = 1 →
      (Batch824.envsCR P c Qc a).trace col = 1 := by
    intro col hcol h
    rw [hE a col (by unfold Batch908.ReadCols; omega), h, map_one]
  have hslot : slotCert (Batch824.envsCR P c Qc) a j =
      (rowShift (Batch908.envsFam P c Qc a), rowBits (Batch908.envsFam P c Qc a)) := by
    obtain ⟨jv, hjv⟩ := j
    simp only at hj hsel
    rcases hj with rfl | rfl
    · simp only [if_true] at hsel
      simp only [slotCert, hselK 0 (Or.inl rfl) hsel, if_true, hs, hbits]
    · simp only [show (2 : ℕ) ≠ 1 by decide, if_false] at hsel
      simp only [slotCert, hselK 9 (Or.inr rfl) hsel, if_true, hs, hbits]
  refine ⟨hslot, ?_⟩
  have hp := request_padding P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact
  rw [hslot] at hp
  rw [Batch908.formRN_agree (F := F) (K := K)]
  exact hp

end RowsAcc

section Tree

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

/-- The 0-indexed row of a 1-indexed label (`lblC`'s off-range convention). -/
def rowIdx (i : ℕ) : Fin P.optimized.family.problem.cfg.compRows :=
  if h : i - 1 < P.optimized.family.problem.cfg.compRows then ⟨i - 1, h⟩
  else ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

theorem lblCS_eq (i : ℕ) :
    lblCS P.optimized (honestQc P c Qc) c i =
      (StrategyOfTracesLift.lblCAt P.optimized (honestQc P c Qc) c (rowIdx P i),
        c2SAt P.optimized (honestQc P c Qc) c (rowIdx P i)) := by
  unfold lblCS StrategyOfTracesLift.lblC rowIdx
  split_ifs <;> rfl

/-- The decoded label of row `r` reads the family row env at `Qc`. -/
theorem lblCAt_eq (r : Fin P.optimized.family.problem.cfg.compRows) :
    StrategyOfTracesLift.lblCAt P.optimized (honestQc P c Qc) c r =
      (StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r)),
        (StrategyOfTracesLift.decodeInputs (rowEnvAt P c Qc r),
          StrategyOfTracesLift.decodePub (rowEnvAt P c Qc r)
            (StrategyOfTracesLift.computeStateOf
              (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r))),
          StrategyOfTracesLift.decodeDec (rowEnvAt P c Qc r))) := by
  have h : FamilyEnvCore.rowEnvAt P.optimized c
      (FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc)) r = rowEnvAt P c Qc r := by
    show FamilyComputeRows.rowEnvAt P c (familyQc P c (honestQc P c Qc)) r = _
    rw [Batch824.familyQc_honestQc]
  unfold StrategyOfTracesLift.lblCAt
  simp only []
  rw [h]

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- `f_t.leaf` / `f_th.leaf` are the `𝕂` roles `41` / `44`, three base columns each. -/
theorem decodeDec_ft_leaf (E : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    (StrategyOfTracesLift.decodeDec E).f_t.leaf = E.extTrace ⟨41, by decide⟩ ∧
      (StrategyOfTracesLift.decodeDec E).f_th.leaf = E.extTrace ⟨44, by decide⟩ := by
  constructor <;>
  simp [StrategyOfTracesLift.decodeDec, StrategyOfTracesLift.decodeSource, decOf, fpOf,
    Env.ofSubst, OptimizedComputeSubstitution.computeSubst,
    OptimizedComputeSubstitution.computeTraceSubst, OptimizedComputeSubstitution.decFP,
    OptimizedComputeSubstitution.ext0, Expr.eval,
    OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv]

end Tree

section CertAxes

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

/-- **The certificate axes, in the form the C2 induction consumes** (`Batch1110`'s `ax0` / `ax9`
read through the atom binding of the formula tail): at every OP0 (OP9) row of the S-carrying
tree, the round-0 certificate axis `axF (S + 2)` (`axF (S + 3)`) is below the characteristic, and
it is the atom whose cast is the row's `f_t.leaf` (`f_th.leaf`) whenever that leaf IS a cast atom.
The unconditional `𝕂`-cast of `Batch1111.CertAxesOK` additionally needs the leaf's two upper
coordinates to vanish, which no named source gives (the axis gate reads coordinate `0` only). -/
def CertAxesOK0 : Prop :=
  ∀ u : NTree ((State × DTcomp K) × ℕ), InTree (treeS P c Qc) u →
    (u.label.1.1 = .s0 →
      (∀ n : ℕ, n < ringChar K → u.label.1.2.2.2.f_t.leaf = (n : K) →
        axF P c Qc (u.label.2 + 2) = n) ∧ axF P c Qc (u.label.2 + 2) < ringChar K) ∧
    (u.label.1.1 = .s9 →
      (∀ n : ℕ, n < ringChar K → u.label.1.2.2.2.f_th.leaf = (n : K) →
        axF P c Qc (u.label.2 + 3) = n) ∧ axF P c Qc (u.label.2 + 3) < ringChar K)

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- Coordinate `0` of a cast atom under `FormRBasis`. -/
theorem coord_natCast (b : Module.Basis (Fin 3) F K) (hb : FormRBasis b) (n : ℕ) :
    coord b ((n : K)) 0 = (n : F) := by
  have : ((n : K)) = (n : F) • (1 : K) := by simp [Algebra.smul_def]
  rw [this, coord_smul, hb.1, smul_eq_mul, mul_one]

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

theorem activeMask_of_sel (r : Fin P.optimized.family.problem.cfg.compRows) (st : State)
    (h : rowSelector (rowEnvAt P c Qc r) = Nock.ComputeTable.opSel st) :
    (st = .s0 → activeMask (rowEnvAt P c Qc r) 1 = 1) ∧
      (st = .s9 → activeMask (rowEnvAt P c Qc r) 2 = 1) := by
  have hv : ∀ t : State, algebraMap F K ((rowEnvAt P c Qc r).baseTrace
      ⟨Nock.Reified.opCol t, by cases t <;> decide⟩) = Nock.ComputeTable.opSel st t :=
    fun t => congrFun h t
  have v0 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 0) = _ := hv .s0
  have v2 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 2) = _ := hv .s2
  have v5 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 5) = _ := hv .s5
  have v6 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 6) = _ := hv .s6
  have v7 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 7) = _ := hv .s7
  have v8 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 8) = _ := hv .s8
  have v9 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 9) = _ := hv .s9
  constructor
  · rintro rfl
    simp [activeMask, OptimizedComputeSubstitution.sampledActive, Nock.Reified.Expr.eval,
      OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv,
      v0, v2, v5, v6, v7, v8, v9, Nock.ComputeTable.opSel]
  · rintro rfl
    simp [activeMask, OptimizedComputeSubstitution.sampledActive, Nock.Reified.Expr.eval,
      OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv,
      v6, v9, Nock.ComputeTable.opSel]

end CertAxes

section CertAxesAcc

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)
variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- `axF` reads the package env `envsCR` (`Batch974.row_identity`'s congruence). -/
theorem axF_eq : axF P c Qc = certAxisOfEnvs (Batch824.envsCR P c Qc) := by
  refine Batch970.certAxisOfEnvs_congr fun i col _ => ?_
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  have htr : (computeEnvsR0 P.optimized (honestQc P c Qc) c i).trace =
      (Batch824.envsCR P c Qc i).trace := by
    unfold computeEnvsR0
    rw [hfam]
    exact (Batch823.envsC_trace P c Qc i).symm
  rw [htr]

/-- The carrier `S` of row `r` is the prefix `S(r)` (`expCol_eq_prefixExp_at`, no wraparound). -/
theorem c2SAt_eq (r : Fin P.optimized.family.problem.cfg.compRows) :
    c2SAt P.optimized (honestQc P c Qc) c r = prefixExpAt P c Qc r := by
  have hsatC := hacc.compute_satisfies
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hrb := P.rowsBound
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (OptimizedHostileTimestamps.activeMask_zero (rowEnvAt P c Qc r))
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have hlt' : prefixExpAt P c Qc r < ringChar K := by
    rw [← hFK]; simp only [expOfAt] at hlt; omega
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  unfold c2SAt computeEnvsR0
  rw [hfam]
  show RecordCarrier.natLift (algebraMap F K (rowEnvAt P c Qc r).expCol) = _
  rw [expCol_eq_prefixExp_at P c Qc hsatC hchar' r r.isLt, map_natCast]
  exact RecordCarrier.natLift_natCast hlt'

theorem certAxesOK0_of_traces
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    CertAxesOK0 P c Qc := by
  have hsatC := hacc.compute_satisfies
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  intro u hu
  obtain ⟨i, hi⟩ := Batch1111.label_of_inTree_S P c Qc Qm h hu
  set r := rowIdx P i with hr
  have hlab : u.label = (StrategyOfTracesLift.lblCAt P.optimized (honestQc P c Qc) c r,
      c2SAt P.optimized (honestQc P c Qc) c r) := by rw [hi, lblCS_eq]
  rw [hlab, lblCAt_eq P c Qc r, c2SAt_eq P c Qc Qm hacc hgood hax hbasis hwidth hα0 r,
    axF_eq P c Qc Qm hacc hgood hax hbasis hwidth hα0]
  simp only
  obtain ⟨hft, hfth⟩ := decodeDec_ft_leaf (rowEnvAt P c Qc r)
  rw [hft, hfth]
  -- the cast atom's coordinate 0
  have hcoordExt : ∀ (role : Fin 63), coord P.optimized.basis
      ((rowEnvAt P c Qc r).extTrace role) 0 =
        (Batch908.envsFam P c Qc r).trace (13 + 3 * (role : ℕ)) := by
    intro role
    have := Nock.NockVMROM.Thm54.MonolithicRAP.coord_sum_smul P.optimized.basis
      (fun k => (Batch908.envsFam P c Qc r).trace
        (OptimizedComputeCorrectedFinal.correctedFinalExtCoordIndex role k)) 0
    exact this.trans (by simp [OptimizedComputeCorrectedFinal.correctedFinalExtCoordIndex])
  have hinj : ∀ x y : ℕ, x < ringChar K → y < ringChar K → (x : F) = (y : F) → x = y := by
    intro x y hx hy hxy
    exact CharP.natCast_injOn_Iio F (ringChar F) (Set.mem_Iio.2 (hFK ▸ hx))
      (Set.mem_Iio.2 (hFK ▸ hy)) hxy
  refine ⟨fun hst => ?_, fun hst => ?_⟩
  · have hsel := rowSelector_of_state P c Qc hsatC r .s0 hst
    have hb0 : (Batch908.envsFam P c Qc r).trace 0 = 1 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s0 .s0 hsel
    have hb9 : (Batch908.envsFam P c Qc r).trace 9 = 0 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s0 .s9 hsel
    have hact := (activeMask_of_sel P c Qc hsatC r .s0 hsel).1 rfl
    obtain ⟨hslot, hpad⟩ := row_cert_padded P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 1
      (Or.inl rfl) (by simpa using hb0) hact
    obtain ⟨heq, hlt⟩ := request_axis P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 1 hact
    have hE : prefixExpAt P c Qc r + 2 = expOfAt P c Qc r 1 := by simp [expOfAt]
    rw [hE]
    refine ⟨fun n hn hleaf => ?_, hlt⟩
    have h136 := leaf136_eq_certAxis (Batch908.envsFam P c Qc r) hwidth
      (fun g hg => (row_obligations_at P c Qc hsatC r).formR99 g hg) hpad hb0 hb9
    have hc := hcoordExt ⟨41, by decide⟩
    rw [hleaf, coord_natCast _ hbasis] at hc
    simp only [show 13 + 3 * 41 = 136 from rfl] at hc
    have hAeq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc r 1) =
        certAxis (rowShift (Batch908.envsFam P c Qc r)) (rowBits (Batch908.envsFam P c Qc r)) := by
      rw [heq, hslot]
    rw [h136, ← hAeq] at hc
    exact (hinj _ _ hn hlt hc).symm
  · have hsel := rowSelector_of_state P c Qc hsatC r .s9 hst
    have hb0 : (Batch908.envsFam P c Qc r).trace 0 = 0 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s9 .s0 hsel
    have hb9 : (Batch908.envsFam P c Qc r).trace 9 = 1 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s9 .s9 hsel
    have hact := (activeMask_of_sel P c Qc hsatC r .s9 hsel).2 rfl
    obtain ⟨hslot, hpad⟩ := row_cert_padded P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 2
      (Or.inr rfl) (by simpa using hb9) hact
    obtain ⟨heq, hlt⟩ := request_axis P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 2 hact
    have hE : prefixExpAt P c Qc r + 3 = expOfAt P c Qc r 2 := by simp [expOfAt]
    rw [hE]
    refine ⟨fun n hn hleaf => ?_, hlt⟩
    have h145 := leaf145_eq_certAxis (Batch908.envsFam P c Qc r) hwidth
      (fun g hg => (row_obligations_at P c Qc hsatC r).formR99 g hg) hpad hb0 hb9
    have hc := hcoordExt ⟨44, by decide⟩
    rw [hleaf, coord_natCast _ hbasis] at hc
    simp only [show 13 + 3 * 44 = 145 from rfl] at hc
    have hAeq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc r 2) =
        certAxis (rowShift (Batch908.envsFam P c Qc r)) (rowBits (Batch908.envsFam P c Qc r)) := by
      rw [heq, hslot]
    rw [h145, ← hAeq] at hc
    exact (hinj _ _ hn hlt hc).symm

end CertAxesAcc

end

end Nock.RedTeam.Batch1140
