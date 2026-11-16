import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.CanonicalRAP

/-!
# Hostile-direction soundness of the `K`-valued IO chip

`Nock/NockVMROM/Thm54/FiniteFieldIOSoundness.lean` proves `finiteIO_sound`: a
`PostChallengeIOWitness` satisfying `FiniteIO.FiniteIOAccepts`, at coins outside two counted
events, implies the record-level IO language `IO.LIO`.  Every existing *consumer* of that theorem
obtains its `FiniteIOAccepts` from `finiteIO_complete_of_LIO`, which is fed `IO.LIO` in the first
place (`BuildableChips.sampledWitness_accepts`), so the argument runs on a fact already derived.

This module supplies the missing direction.  Nothing here mentions an execution, a carrier, or a
completeness theorem: the input is an **arbitrary** committed trace

    P : Fin (finiteIOProgAIR m).numTraceCols → K[X]

together with the statement that it satisfies the four kind-segmented ordinary RAPs of the
`K`-valued chip (`SegmentedRAPParams.rap`, i.e. `Reify.airToRAP (kindSeg …)`), and the witness is
*read off `P`* (`projWitness`).  `FiniteIOAccepts` is then proved, not assumed, and
`finiteIO_sound` closes.

## The agreement hypothesis, and why it cannot be dropped

`FiniteIOAccepts.requestInvPin` is an equation between a witness column and
`compress coins (records.requests.get i)` — it ties the columns to the *records*, and a trace `P`
whose record columns hold something else says nothing about `records`.  `ChipAgreement` carries
exactly that identification and nothing more:

* `record_eq` — the `m` record columns of `P`, read at row `i`, are `records`' `i`-th record;
* `gamma_eq` / `pole_eq` — the chip's two challenge slots carry the sampled coins;
* `terminal_eq` — public slot `0` carries the shared terminal.

This is the analogue of the slot agreement in `Nock/NockVMROM/Thm54/ComputeEnvAgreement.lean`
(`reEnv_trace_agree`, `rows_vanish_transfer`), and it is deliberately
prominent: identifying `P`'s columns with `records` silently would smuggle the conclusion back in.

## The row geometry

The chip's rows are the orbit prefix `rowPt ω x₀ i = ω^i · x₀`, which is what makes
`envOfTrace`'s next-row read `P_j(ω·x)` the following row (`rowEnv_traceNext`).  `ChipRows`
records that the boundary row `0`, the `n` record rows, and the terminal row `n` lie in the domain
their constraint kind is deployed on.  Both are hypotheses about the *deployment*, not about any
program.

## Non-vacuity

`hypotheses_inhabited` (§8) exhibits a deployment, a committed trace and a terminal satisfying
*every* hypothesis of `projWitness_accepts` simultaneously, at any `g ≠ 1` and any single record
with a nonzero compressed denominator.  So the implication is not vacuous.  It is *not* a
completeness theorem: it does not claim every accepting witness is realizable as some `P` (that
would be AIR-level completeness of the chip, proved separately in `IOChipCompleteness.lean` by
`satisfies_of_io_lio`, with `lio_roundtrip` checking the two are converse at the same deployment).
-/

namespace Nock.NockVMROM.Thm54.IOChip

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open scoped BigOperators Polynomial

variable {K : Type*} [Field K] {m : ℕ}

/-! ## 1. Row geometry -/

/-- The `i`-th row point of the orbit prefix based at `x₀`: the paper's `ω^i·x₀`
    (the paper's `Y_{i,j} ↦ P_i(ω^j·X)` read along a row walk). -/
def rowPt (ω x₀ : K) (i : ℕ) : K := ω ^ i * x₀

theorem rowPt_succ (ω x₀ : K) (i : ℕ) : rowPt ω x₀ (i + 1) = ω * rowPt ω x₀ i := by
  simp only [rowPt, pow_succ]
  ring

/-- The row environment the chip's constraints are evaluated in at row `i`: `Reify.envOfTrace`
    of the committed trace at the `i`-th row point, with the chip's own coin and public
    valuations. -/
noncomputable def rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) : Env K :=
  envOfTrace P q.ω (rowPt q.ω x₀ i) q.chalVal q.pubVal

@[simp] theorem rowEnv_chal {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i j : ℕ) : (rowEnv q x₀ P i).chal j = q.chalVal j := rfl

@[simp] theorem rowEnv_pub {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i j : ℕ) : (rowEnv q x₀ P i).pub j = q.pubVal j := rfl

/-- **The next-row read is the next row.**  `envOfTrace`'s `traceNext` reads `P_j(ω·x)`, and the
    row points are an orbit prefix, so it is exactly row `i+1`'s current-row read. -/
theorem rowEnv_traceNext {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i j : ℕ) : (rowEnv q x₀ P i).traceNext j = (rowEnv q x₀ P (i + 1)).trace j := by
  simp only [rowEnv, envOfTrace, rowPt_succ]

/-- Reading column `j < w` of the committed trace at row `i`. -/
theorem rowEnv_trace_eq {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i j : ℕ) (h : j < w) :
    (rowEnv q x₀ P i).trace j = (P ⟨j, h⟩).eval (rowPt q.ω x₀ i) := by
  simp only [rowEnv, envOfTrace, dif_pos h]

/-! ## 2. Gate evaluation in the row environment -/

theorem ioAccInit_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) : ioAccInit.eval (rowEnv q x₀ P i) = (rowEnv q x₀ P i).trace 0 := rfl

theorem ioTerm_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) :
    ioTerm.eval (rowEnv q x₀ P i) = q.pubVal 0 - (rowEnv q x₀ P i).trace 0 := rfl

theorem ioProgAccStep_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K)
    (P : Fin w → K[X]) (i : ℕ) :
    ioProgAccStep.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P (i + 1)).trace 0 - (rowEnv q x₀ P i).trace 0
          - (rowEnv q x₀ P i).trace 1 := by
  simp only [ioProgAccStep, Expr.eval, Trans.tn, tc]
  rw [show (rowEnv q x₀ P i).traceNext 0 = (rowEnv q x₀ P (i + 1)).trace 0 from
    rowEnv_traceNext q x₀ P i 0]

theorem ioMemAccStep_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K)
    (P : Fin w → K[X]) (i : ℕ) :
    ioMemAccStep.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P (i + 1)).trace 0 - (rowEnv q x₀ P i).trace 0
          - (rowEnv q x₀ P i).trace 2 * (rowEnv q x₀ P i).trace 1 := by
  simp only [ioMemAccStep, Expr.eval, Trans.tn, tc]
  rw [show (rowEnv q x₀ P i).traceNext 0 = (rowEnv q x₀ P (i + 1)).trace 0 from
    rowEnv_traceNext q x₀ P i 0]

theorem ioMultBool_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) :
    ioMultBool.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P i).trace 2 * ((rowEnv q x₀ P i).trace 2 - 1) := by
  simp only [ioMultBool, Expr.eval, tc, Int.cast_one]

theorem ioMultInvPin_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) :
    ioMultInvPin.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P i).trace 2 * (rowEnv q x₀ P i).trace 3 - 1 := by
  simp only [ioMultInvPin, Expr.eval, tc, Int.cast_one]

/-- The reified record-RLC gate, evaluated in an arbitrary environment, is `Walk.rlc` of whatever
    the record columns hold. -/
theorem rlcExpr_eval_of_record (env : Env K) (rec : Fin m → K)
    (hrec : ∀ c : Fin m, env.trace (4 + (c : ℕ)) = rec c) (γ : K) (hγ : env.chal 0 = γ) :
    (rlcExpr m 4).eval env = Walk.rlc γ rec := by
  rw [rlcExpr_eval, Finset.sum_range]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hrec c, hγ]

theorem ioInvPin_eval_rowEnv {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X])
    (i : ℕ) (coins : IOCoins K) (rec : Fin m → K)
    (hrec : ∀ c : Fin m, (rowEnv q x₀ P i).trace (4 + (c : ℕ)) = rec c)
    (hγ : q.chalVal 0 = coins.gamma) (hp : q.chalVal 1 = coins.pole) :
    (ioInvPin m 4).eval (rowEnv q x₀ P i)
      = compress coins rec * (rowEnv q x₀ P i).trace 1 - 1 := by
  simp only [ioInvPin, Expr.eval, chl, tc, Int.cast_one]
  rw [rlcExpr_eval_of_record (rowEnv q x₀ P i) rec hrec coins.gamma (by rw [rowEnv_chal, hγ])]
  show ((rowEnv q x₀ P i).chal 1 + _) * _ - _ = _
  rw [rowEnv_chal, hp]
  rfl

/-! ## 3. The two carried hypotheses -/

/-- **The committed-column agreement** (the analogue of `ComputeEnvAgreement`'s slot agreement).
    Identifies the hostile trace's record columns with the committed record list, its two
    challenge slots with the sampled coins, and its public slot `0` with the shared terminal.
    Nothing else about `P` is assumed. -/
structure ChipAgreement (recs : List (Fin m → K)) (coins : IOCoins K) (terminal : K)
    (q : SegmentedRAPParams K) (x₀ : K) {w : ℕ} (P : Fin w → K[X]) : Prop where
  /-- Challenge slot `0` is the record-RLC coin. -/
  gamma_eq : q.chalVal 0 = coins.gamma
  /-- Challenge slot `1` is the LogUp pole coin. -/
  pole_eq : q.chalVal 1 = coins.pole
  /-- Public slot `0` is the shared terminal both chips must reach. -/
  terminal_eq : q.pubVal 0 = terminal
  /-- The `m` record columns at row `i` hold the `i`-th committed record. -/
  record_eq : ∀ (i : Fin recs.length) (c : Fin m),
      (rowEnv q x₀ P (i : ℕ)).trace (4 + (c : ℕ)) = recs.get i c

/-- **The row-domain deployment condition.**  The boundary row, the `n` record rows and the
    terminal row lie in the evaluation domain their constraint kind is deployed on. -/
structure ChipRows (n : ℕ) (q : SegmentedRAPParams K) (x₀ : K) : Prop where
  /-- Row `0` carries the `.boundary` gate. -/
  boundary_mem : rowPt q.ω x₀ 0 ∈ q.domain .boundary
  /-- Rows `0 … n-1` carry the `.transition` gates. -/
  transition_mem : ∀ i, i < n → rowPt q.ω x₀ i ∈ q.domain .transition
  /-- Row `n` carries the `.terminal` gate. -/
  terminal_mem : rowPt q.ω x₀ n ∈ q.domain .terminal

/-! ## 4. Satisfaction of the segmented RAPs gives per-kind gate vanishing -/

/-- `SegmentedRAPParams.rap` is `airToRAP (kindSeg …)`, so `segmented_is_kinded` turns the family
    of ordinary RAP-satisfaction facts into per-kind pointwise gate vanishing.  No use is made of
    the constraint list of any particular chip here. -/
theorem gates_vanish_of_satisfies (q : SegmentedRAPParams K) (air : Reified.AIR)
    (P : Fin air.numTraceCols → K[X])
    (hsat : ∀ k : Reified.ConstraintKind, (q.rap air k).Satisfies P) :
    ∀ c ∈ air.constraints, ∀ x ∈ q.domain c.kind,
      c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
  (segmented_is_kinded air q.chalVal q.pubVal q.eDeg q.hExp q.ω q.βcoset
    q.βcoset_ne_zero q.hExp_pos q.domain P).mp hsat

/-! ## 5. The witness read off the committed columns -/

/-- **The projected witness.**  Nothing is chosen; nothing comes from an execution. -/
noncomputable def projWitness (records : PreChallengeRecords K m) (coins : IOCoins K)
    (terminal : K) (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
    (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
    (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X]) :
    PostChallengeIOWitness records coins where
  requestInv := fun i => (rowEnv qp x₀p Pp (i : ℕ)).trace 1
  responseInv := fun j => (rowEnv qm x₀m Pm (j : ℕ)).trace 1
  multiplicity := fun j => (rowEnv qm x₀m Pm (j : ℕ)).trace 2
  multInv := fun j => (rowEnv qm x₀m Pm (j : ℕ)).trace 3
  requestAcc := fun i => (rowEnv qp x₀p Pp (i : ℕ)).trace 0
  responseAcc := fun j => (rowEnv qm x₀m Pm (j : ℕ)).trace 0
  terminal := terminal

/-! ## 6. Acceptance, proved from satisfaction -/

section Accepts

variable (records : PreChallengeRecords K m) (coins : IOCoins K) (terminal : K)
  (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
  (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
  (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X])

/-- **`FiniteIOAccepts` from RAP satisfaction of the two `K`-valued IO chips.**  Each of the ten
    conjuncts is obtained by evaluating the corresponding reified gate in the row environment of
    the committed trace; the record columns enter only through `ChipAgreement.record_eq`. -/
theorem projWitness_accepts
    (hsatP : ∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsP : ChipRows records.requests.length qp x₀p)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagP : ChipAgreement records.requests coins terminal qp x₀p Pp)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm) :
    FiniteIOAccepts records coins
      (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) := by
  have hP := gates_vanish_of_satisfies qp (finiteIOProgAIR m) Pp hsatP
  have hM := gates_vanish_of_satisfies qm (finiteIOMemAIR m) Pm hsatM
  -- membership of each gate in its chip's constraint list
  have hmPinit : (⟨.boundary, ioAccInit⟩ : Constraint) ∈ (finiteIOProgAIR m).constraints := by
    simp [finiteIOProgAIR]
  have hmPpin : (⟨.transition, ioInvPin m 4⟩ : Constraint) ∈ (finiteIOProgAIR m).constraints := by
    simp [finiteIOProgAIR]
  have hmPstep : (⟨.transition, ioProgAccStep⟩ : Constraint) ∈
      (finiteIOProgAIR m).constraints := by simp [finiteIOProgAIR]
  have hmPterm : (⟨.terminal, ioTerm⟩ : Constraint) ∈ (finiteIOProgAIR m).constraints := by
    simp [finiteIOProgAIR]
  have hmMinit : (⟨.boundary, ioAccInit⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMpin : (⟨.transition, ioInvPin m 4⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMbool : (⟨.transition, ioMultBool⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMminv : (⟨.transition, ioMultInvPin⟩ : Constraint) ∈
      (finiteIOMemAIR m).constraints := by simp [finiteIOMemAIR]
  have hmMstep : (⟨.transition, ioMemAccStep⟩ : Constraint) ∈
      (finiteIOMemAIR m).constraints := by simp [finiteIOMemAIR]
  have hmMterm : (⟨.terminal, ioTerm⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  refine
    { requestInvPin := ?_, responseInvPin := ?_, multBool := ?_, multInvPin := ?_,
      requestInit := ?_, requestStep := ?_, responseInit := ?_, responseStep := ?_,
      requestTerm := ?_, responseTerm := ?_ }
  · -- request inverse pin
    intro i
    have h := hP _ hmPpin (rowPt qp.ω x₀p (i : ℕ)) (hrowsP.transition_mem i i.isLt)
    rw [show (envOfTrace Pp qp.ω (rowPt qp.ω x₀p (i : ℕ)) qp.chalVal qp.pubVal)
        = rowEnv qp x₀p Pp (i : ℕ) from rfl,
      ioInvPin_eval_rowEnv qp x₀p Pp (i : ℕ) coins (records.requests.get i)
        (hagP.record_eq i) hagP.gamma_eq hagP.pole_eq, sub_eq_zero] at h
    exact h
  · -- response inverse pin
    intro j
    have h := hM _ hmMpin (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl,
      ioInvPin_eval_rowEnv qm x₀m Pm (j : ℕ) coins (records.responses.get j)
        (hagM.record_eq j) hagM.gamma_eq hagM.pole_eq, sub_eq_zero] at h
    exact h
  · -- multiplicity booleanity
    intro j
    have h := hM _ hmMbool (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMultBool_eval_rowEnv] at h
    exact h
  · -- multiplicity inverse pin
    intro j
    have h := hM _ hmMminv (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMultInvPin_eval_rowEnv, sub_eq_zero] at h
    exact h
  · -- request accumulator init
    have h := hP _ hmPinit (rowPt qp.ω x₀p 0) hrowsP.boundary_mem
    rw [show (envOfTrace Pp qp.ω (rowPt qp.ω x₀p 0) qp.chalVal qp.pubVal)
        = rowEnv qp x₀p Pp 0 from rfl, ioAccInit_eval_rowEnv] at h
    exact h
  · -- request accumulator step
    intro i
    have h := hP _ hmPstep (rowPt qp.ω x₀p (i : ℕ)) (hrowsP.transition_mem i i.isLt)
    rw [show (envOfTrace Pp qp.ω (rowPt qp.ω x₀p (i : ℕ)) qp.chalVal qp.pubVal)
        = rowEnv qp x₀p Pp (i : ℕ) from rfl, ioProgAccStep_eval_rowEnv,
      sub_sub, sub_eq_zero] at h
    simp only [projWitness, Fin.val_succ, Fin.val_castSucc]
    exact h
  · -- response accumulator init
    have h := hM _ hmMinit (rowPt qm.ω x₀m 0) hrowsM.boundary_mem
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m 0) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm 0 from rfl, ioAccInit_eval_rowEnv] at h
    exact h
  · -- response accumulator step
    intro j
    have h := hM _ hmMstep (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMemAccStep_eval_rowEnv,
      sub_sub, sub_eq_zero] at h
    simp only [projWitness, Fin.val_succ, Fin.val_castSucc]
    exact h
  · -- request terminal
    have h := hP _ hmPterm (rowPt qp.ω x₀p records.requests.length) hrowsP.terminal_mem
    rw [show (envOfTrace Pp qp.ω (rowPt qp.ω x₀p records.requests.length) qp.chalVal qp.pubVal)
        = rowEnv qp x₀p Pp records.requests.length from rfl, ioTerm_eval_rowEnv,
      hagP.terminal_eq, sub_eq_zero] at h
    simp only [projWitness, Fin.val_last]
    exact h.symm
  · -- response terminal
    have h := hM _ hmMterm (rowPt qm.ω x₀m records.responses.length) hrowsM.terminal_mem
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m records.responses.length) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm records.responses.length from rfl, ioTerm_eval_rowEnv,
      hagM.terminal_eq, sub_eq_zero] at h
    simp only [projWitness, Fin.val_last]
    exact h.symm

/-- **Bridge to the existing tight biconditional.**  `Trans`-style `reified_finiteIO_sound`
    (`FiniteFieldIOAIR.lean:406`) equates `FiniteIOAccepts` with the vanishing of the ten gates at
    the *canonical* row environments `progEnvAt`/`memEnvAt`.  Composing it with
    `projWitness_accepts` shows those canonical gate facts are now available from **hostile** RAP
    satisfaction, with no execution anywhere in the derivation. -/
theorem projWitness_reified_gates
    (hsatP : ∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsP : ChipRows records.requests.length qp x₀p)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagP : ChipAgreement records.requests coins terminal qp x₀p Pp)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm) :
    ((ioAccInit.eval
          (progEnvAt records coins (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) 0) = 0
        ∧ (∀ i, i < records.requests.length →
            (ioInvPin m 4).eval (progEnvAt records coins
              (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) i) = 0)
        ∧ (∀ i, i < records.requests.length →
            ioProgAccStep.eval (Trans.twoRow
              (progEnvAt records coins
                (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) i)
              (progEnvAt records coins
                (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) (i + 1))) = 0)
        ∧ ioTerm.eval (progEnvAt records coins
            (projWitness records coins terminal qp qm x₀p x₀m Pp Pm)
            records.requests.length) = 0)
      ∧ (ioAccInit.eval
          (memEnvAt records coins (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) 0) = 0
        ∧ (∀ j, j < records.responses.length →
            (ioInvPin m 4).eval (memEnvAt records coins
              (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMultBool.eval (memEnvAt records coins
              (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMultInvPin.eval (memEnvAt records coins
              (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMemAccStep.eval (Trans.twoRow
              (memEnvAt records coins
                (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) j)
              (memEnvAt records coins
                (projWitness records coins terminal qp qm x₀p x₀m Pp Pm) (j + 1))) = 0)
        ∧ ioTerm.eval (memEnvAt records coins
            (projWitness records coins terminal qp qm x₀p x₀m Pp Pm)
            records.responses.length) = 0)) :=
  (reified_finiteIO_sound records coins
    (projWitness records coins terminal qp qm x₀p x₀m Pp Pm)).mpr
      (projWitness_accepts records coins terminal qp qm x₀p x₀m Pp Pm
        hsatP hsatM hrowsP hrowsM hagP hagM)

end Accepts

/-! ## 7. The headline: hostile columns imply `IO.LIO` -/

section Sound

variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- **`io_lio_of_satisfies` — the hostile direction.**  An arbitrary pair of committed traces that
    satisfies the kind-segmented ordinary RAPs of the two `K`-valued IO chips, at verifier-sampled
    coins outside the two counted events, implies the record-level IO language `IO.LIO`.

    The witness is `projWitness`, read off the traces; `FiniteIOAccepts` is proved by
    `projWitness_accepts`; `finiteIO_sound` closes.  No execution, carrier, or completeness
    theorem occurs anywhere in the derivation, so the `req.Perm resp` conjunct of `IO.LIO` is
    genuinely bought from the LogUp argument rather than from itself.

    The six non-event hypotheses (`hKp`, `hKreq`, `hKresp`, `hreqnd`, `hrespnd`) are
    `finiteIO_sound`'s own and are conjuncts of `RawMessage.VerifierGates`, so a consumer gets
    them from acceptance. -/
theorem io_lio_of_satisfies {Ksz : ℕ}
    (records : PreChallengeRecords K m) (coins : IOCoins K) (terminal : K)
    (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
    (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
    (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X])
    (hsatP : ∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsP : ChipRows records.requests.length qp x₀p)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagP : ChipAgreement records.requests coins terminal qp x₀p Pp)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  finiteIO_sound
    (projWitness_accepts records coins terminal qp qm x₀p x₀m Pp Pm
      hsatP hsatM hrowsP hrowsM hagP hagM)
    hKp hKreq hKresp hreqnd hrespnd hγ hpole

theorem perm_of_satisfies {Ksz : ℕ}
    (records : PreChallengeRecords K m) (coins : IOCoins K) (terminal : K)
    (qp qm : SegmentedRAPParams K) (x₀p x₀m : K)
    (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
    (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X])
    (hsatP : ∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsP : ChipRows records.requests.length qp x₀p)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagP : ChipAgreement records.requests coins terminal qp x₀p Pp)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    records.requests.Perm records.responses :=
  (io_lio_of_satisfies (Ksz := Ksz) records coins terminal qp qm x₀p x₀m Pp Pm
    hsatP hsatM hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hγ hpole).2.2

end Sound

/-! ## 8. The hypothesis bundle is inhabited

`io_lio_of_satisfies` is an implication, so it is worth knowing that its hypotheses can all hold
at once — otherwise the theorem would be vacuous.  They can, and the witness is elementary: a
two-row deployment (`twoRowParams`) with the boundary and transition gates on the row point `1`,
the terminal gate on `g`, and a committed trace (`twoRowTrace`) whose accumulator column is the
degree-`1` polynomial `v·(X−1)/(g−1)`.  No interpolation and no execution is involved. -/

section NonVacuity

/-- A two-row deployment: boundary and transition gates on the row point `1`, the terminal gate
    on the row point `g`, and an empty `.row` segment. -/
noncomputable def twoRowParams (g gam pol v : K) : SegmentedRAPParams K where
  chalVal := fun j => if j = 0 then gam else if j = 1 then pol else 0
  pubVal := fun _ => v
  eDeg := 1
  hExp := 1
  ω := g
  βcoset := 1
  domain := fun k => match k with
    | .boundary => {1}
    | .transition => {1}
    | .terminal => {g}
    | .row => ∅
  βcoset_ne_zero := one_ne_zero
  hExp_pos := le_refl 1

/-- A one-record committed trace: accumulator `v·(X−1)/(g−1)`, reciprocal column the constant `v`,
    the two multiplicity columns the constant `1`, and the record columns the constants of
    `rec`. -/
noncomputable def twoRowTrace (g v : K) (rec : Fin m → K) : Fin (m + 4) → K[X] :=
  fun j =>
    if j.val = 0 then Polynomial.C (v / (g - 1)) * (Polynomial.X - Polynomial.C 1)
    else if j.val = 1 then Polynomial.C v
    else if j.val = 2 then Polynomial.C 1
    else if j.val = 3 then Polynomial.C 1
    else if h : j.val - 4 < m then Polynomial.C (rec ⟨j.val - 4, h⟩)
    else 0

section Columns

variable (g gam pol v : K) (rec : Fin m → K)

theorem twoRow_pt0 : rowPt (twoRowParams g gam pol v).ω 1 0 = 1 := by
  rw [rowPt]; ring

theorem twoRow_pt1 : rowPt (twoRowParams g gam pol v).ω 1 1 = g := by
  show (twoRowParams g gam pol v).ω ^ 1 * 1 = g
  show g ^ 1 * 1 = g
  ring

theorem twoRow_acc0 :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 0).trace 0 = 0 := by
  rw [rowEnv_trace_eq _ _ _ _ _ (by omega : 0 < m + 4), twoRow_pt0]
  simp [twoRowTrace]

theorem twoRow_acc1 (hg : g - 1 ≠ 0) :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 1).trace 0 = v := by
  rw [rowEnv_trace_eq _ _ _ _ _ (by omega : 0 < m + 4), twoRow_pt1]
  show Polynomial.eval g (Polynomial.C (v / (g - 1)) * (Polynomial.X - Polynomial.C 1)) = v
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  field_simp

theorem twoRow_inv0 :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 0).trace 1 = v := by
  rw [rowEnv_trace_eq _ _ _ _ _ (by omega : 1 < m + 4), twoRow_pt0]
  simp [twoRowTrace]

theorem twoRow_mul0 :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 0).trace 2 = 1 := by
  rw [rowEnv_trace_eq _ _ _ _ _ (by omega : 2 < m + 4), twoRow_pt0]
  simp [twoRowTrace]

theorem twoRow_mulInv0 :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 0).trace 3 = 1 := by
  rw [rowEnv_trace_eq _ _ _ _ _ (by omega : 3 < m + 4), twoRow_pt0]
  simp [twoRowTrace]

theorem twoRow_rec0 (c : Fin m) :
    (rowEnv (twoRowParams g gam pol v) 1 (twoRowTrace g v rec) 0).trace (4 + (c : ℕ))
      = rec c := by
  have hlt : 4 + (c : ℕ) < m + 4 := by have := c.isLt; omega
  have h0 : ¬ (4 + (c : ℕ)) = 0 := by omega
  have h1 : ¬ (4 + (c : ℕ)) = 1 := by omega
  have h2 : ¬ (4 + (c : ℕ)) = 2 := by omega
  have h3 : ¬ (4 + (c : ℕ)) = 3 := by omega
  have h4 : 4 + (c : ℕ) - 4 < m := by have := c.isLt; omega
  rw [rowEnv_trace_eq _ _ _ _ _ hlt, twoRow_pt0]
  simp only [twoRowTrace, if_neg h0, if_neg h1, if_neg h2, if_neg h3, dif_pos h4,
    Polynomial.eval_C]
  exact congrArg rec (Fin.ext (show (4 : ℕ) + (c : ℕ) - 4 = (c : ℕ) from by omega))

end Columns

/-- **`hypotheses_inhabited` — `io_lio_of_satisfies` is not vacuous.**  For any `g ≠ 1`, any
    coins, and any record whose compressed denominator is nonzero there is a deployment, a
    committed trace and a terminal for which both chips' kind-segmented ordinary RAPs are
    satisfied, the row-domain conditions hold, and the column agreement holds — at the
    one-request / one-response record pair. -/
theorem hypotheses_inhabited (g gam pol : K) (hg : g ≠ 1) (rec : Fin m → K)
    (hne : pol + Walk.rlc gam rec ≠ 0) :
    ∃ (q : SegmentedRAPParams K) (P : Fin (m + 4) → K[X]) (terminal : K),
      (∀ k : Reified.ConstraintKind, (q.rap (finiteIOProgAIR m) k).Satisfies P)
        ∧ (∀ k : Reified.ConstraintKind, (q.rap (finiteIOMemAIR m) k).Satisfies P)
        ∧ ChipRows 1 q 1
        ∧ ChipAgreement [rec] ⟨gam, pol⟩ terminal q 1 P := by
  classical
  have hg1 : g - 1 ≠ 0 := sub_ne_zero_of_ne hg
  set v : K := (pol + Walk.rlc gam rec)⁻¹ with hvdef
  set q : SegmentedRAPParams K := twoRowParams g gam pol v with hqdef
  set P : Fin (m + 4) → K[X] := twoRowTrace g v rec with hPdef
  have hgam : q.chalVal 0 = gam := rfl
  have hpol : q.chalVal 1 = pol := rfl
  have hpub : q.pubVal 0 = v := rfl
  have hpt0 : rowPt q.ω 1 0 = 1 := twoRow_pt0 g gam pol v
  have hpt1 : rowPt q.ω 1 1 = g := twoRow_pt1 g gam pol v
  have hacc0 : (rowEnv q 1 P 0).trace 0 = 0 := twoRow_acc0 g gam pol v rec
  have hacc1 : (rowEnv q 1 P 1).trace 0 = v := twoRow_acc1 g gam pol v rec hg1
  have hinv0 : (rowEnv q 1 P 0).trace 1 = v := twoRow_inv0 g gam pol v rec
  have hmul0 : (rowEnv q 1 P 0).trace 2 = 1 := twoRow_mul0 g gam pol v rec
  have hmi0 : (rowEnv q 1 P 0).trace 3 = 1 := twoRow_mulInv0 g gam pol v rec
  have hrec0 : ∀ c : Fin m, (rowEnv q 1 P 0).trace (4 + (c : ℕ)) = rec c :=
    twoRow_rec0 g gam pol v rec
  -- the individual gate facts
  have gInit : ioAccInit.eval (rowEnv q 1 P 0) = 0 := hacc0
  have gTerm : ioTerm.eval (rowEnv q 1 P 1) = 0 := by
    rw [ioTerm_eval_rowEnv, hpub, hacc1, sub_self]
  have gPin : (ioInvPin m 4).eval (rowEnv q 1 P 0) = 0 := by
    rw [ioInvPin_eval_rowEnv q 1 P 0 ⟨gam, pol⟩ rec hrec0 hgam hpol, hinv0]
    show (pol + Walk.rlc gam rec) * v - 1 = 0
    rw [hvdef, mul_inv_cancel₀ hne, sub_self]
  have gStep : ioProgAccStep.eval (rowEnv q 1 P 0) = 0 := by
    rw [ioProgAccStep_eval_rowEnv, hacc0, hacc1, hinv0, sub_zero, sub_self]
  have gMStep : ioMemAccStep.eval (rowEnv q 1 P 0) = 0 := by
    rw [ioMemAccStep_eval_rowEnv, hacc0, hacc1, hinv0, hmul0, sub_zero, one_mul, sub_self]
  have gBool : ioMultBool.eval (rowEnv q 1 P 0) = 0 := by
    rw [ioMultBool_eval_rowEnv, hmul0, sub_self, mul_zero]
  have gMInv : ioMultInvPin.eval (rowEnv q 1 P 0) = 0 := by
    rw [ioMultInvPin_eval_rowEnv, hmul0, hmi0, mul_one, sub_self]
  -- reading the three singleton domains
  have hdb : ∀ x ∈ q.domain (.boundary : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q 1 P 0 := by
    intro x hx
    have hx1 : x = 1 := Finset.mem_singleton.mp hx
    rw [hx1, rowEnv, hpt0]
  have hdt : ∀ x ∈ q.domain (.transition : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q 1 P 0 := by
    intro x hx
    have hx1 : x = 1 := Finset.mem_singleton.mp hx
    rw [hx1, rowEnv, hpt0]
  have hdm : ∀ x ∈ q.domain (.terminal : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q 1 P 1 := by
    intro x hx
    have hxg : x = g := Finset.mem_singleton.mp hx
    rw [hxg, rowEnv, hpt1]
  refine ⟨q, P, v, ?_, ?_, ?_, ?_⟩
  · refine (segmented_is_kinded (finiteIOProgAIR m) q.chalVal q.pubVal q.eDeg q.hExp q.ω
      q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain P).mpr ?_
    intro c hc x hx
    simp only [finiteIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · show ioAccInit.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdb x hx]; exact gInit
    · show (ioInvPin m 4).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gPin
    · show ioProgAccStep.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gStep
    · show ioTerm.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdm x hx]; exact gTerm
  · refine (segmented_is_kinded (finiteIOMemAIR m) q.chalVal q.pubVal q.eDeg q.hExp q.ω
      q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain P).mpr ?_
    intro c hc x hx
    simp only [finiteIOMemAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · show ioAccInit.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdb x hx]; exact gInit
    · show (ioInvPin m 4).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gPin
    · show ioMultBool.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gBool
    · show ioMultInvPin.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gMInv
    · show ioMemAccStep.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdt x hx]; exact gMStep
    · show ioTerm.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdm x hx]; exact gTerm
  · exact
      { boundary_mem := by rw [hpt0]; exact Finset.mem_singleton_self 1
        transition_mem := by
          intro i hi
          have hi0 : i = 0 := by omega
          rw [hi0, hpt0]; exact Finset.mem_singleton_self 1
        terminal_mem := by rw [hpt1]; exact Finset.mem_singleton_self g }
  · exact
      { gamma_eq := hgam, pole_eq := hpol, terminal_eq := hpub
        record_eq := by
          intro i c
          obtain ⟨iv, hiv⟩ := i
          simp only [List.length_cons, List.length_nil] at hiv
          interval_cases iv
          exact hrec0 c }

end NonVacuity


end Nock.NockVMROM.Thm54.IOChip

#print axioms Nock.NockVMROM.Thm54.IOChip.rowEnv_traceNext
#print axioms Nock.NockVMROM.Thm54.IOChip.gates_vanish_of_satisfies
#print axioms Nock.NockVMROM.Thm54.IOChip.projWitness_accepts
#print axioms Nock.NockVMROM.Thm54.IOChip.projWitness_reified_gates
#print axioms Nock.NockVMROM.Thm54.IOChip.io_lio_of_satisfies
#print axioms Nock.NockVMROM.Thm54.IOChip.perm_of_satisfies
#print axioms Nock.NockVMROM.Thm54.IOChip.hypotheses_inhabited
