/-
  Nock/NockVMROM/Thm54/StrategyOfTracesEv.lean

  Additive: nothing is
  re-pointed; `strategyOfTracesR0AC2` stays the strategy `p8` is stated at.

  **Why.**  `strategyOfTracesR0AC2 O tag Qc Qm c h` names the sampled tuple `c` (in the decoded
  labels' challenge records, the config's challenges, the memory rows' `λ`) and a tiling proof
  `h : TracesWalkHyps O Qc Qm c`.  A pinned failure-event slot `{c | c.1 ∈ Union (T_c) c.λ}` is a
  DIAGONAL set, which no fibred card lemma bounds.  This module builds the
  strategy the EVENT is priced at:

  * `coinFree : OptimizedProductionChallengeTuple K F` — the all-zero tuple;
  * `skeletonEv O Qc Qm` — the C2 skeleton at `coinFree`, `h`-free (its memory forest is the
    inverse-BFS forest term itself, which `execOfTraces` only wraps);
  * `execTemplateEv O Qc Qm z` — the round-0 execution template at `coinFree` when the tiling
    hypotheses hold (`if`-guard, no `h` argument), else the package's own honest execution wrapped
    as a template (so the template type is inhabited at every trace);
  * `strategyOfTracesEv O tag Qc Qm : ProductionStrategy F K` — the generic chain `verifierGen`
    at the `h`-free timestamp strategy, skeleton `skeletonEv`.

  **The c-invariance lemmas.**  For
  EVERY `c` and EVERY `h`:
  * `computeTree_agree`: the skeleton compute tree of `strategyOfTracesR0AC2 … c h` IS
    `skeletonEv`'s (so the census pairs, the size-window nouns, the request targets and the public
    claim agree — `combinedSkeletonPairs_agree`, `skeletonSizeWindowNouns_agree`,
    `requestTargets_agree`, `publicClaim_agree`);
  * `memoryRows_length_agree`: the memory row counts agree;
  * `template_memoryForest_agree`: the committed template's memory forest at `c` is the event
    template's relabelled by `ψT c lam` (which touches only the placeholder's challenge record and
    `lambda?`, neither read by the axis tree nor by the topology payloads);
  * `template_computeTree_spec_agree`: the SPECIALIZED compute tree at `c` is the event's
    relabelled by `setInp` (the compute inputs record only; the specialization overwrites the
    three record timestamps, the only other `c`-dependent decoded fields — `computeTraceSubst`
    columns `74`, `82`, `90` read challenge `0`).
  The event-level consequences (axis share, topology event, the union) are in `P8EventEv.lean`.

  **Read set.**  The `c`-dependence of every decoded object is through `chal` / `pub` of the row
  environments; their `trace` fields are the committed polynomials' values and never mention `c`
  (`computeEnvsR0_trace`, `memoryEnvsR0_trace`, by `rfl` after `familyQc_envTrace`).  Every
  decoder field the P8 slot reads is a `traceOnly` expression (`FamilyChipTwins.traceOnly`,
  decided per column: `computeTraceSubst_traceOnly`).

  -- the paper (the claim), :1728-1742 (`V_comp`), :1413 (timestamps), :2266 (inverse BFS)
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.NockVMROM.Thm54.TraceOnlyExpr
import Nock.NockVMROM.Thm54.ReconTreeSize

namespace Nock.NockVMROM.Thm54.StrategyOfTracesEv

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FamilyChipTwins
open Nock.NockVMROM.Thm54.ReconTreeSize

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 800000

noncomputable section

/-! ## §A  Generic: the decoders read trace columns only -/

section Decoders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K]

/-- Every decoded compute column the P8 slot reads is a trace-only expression: all of `0..93`
except the three record timestamps (`74`, `82`, `90`, which read challenge `0`) and `93`
(challenge `5`).  Decided column by column. -/
theorem computeTraceSubst_traceOnly :
    ∀ k, k < 93 → k ≠ 74 → k ≠ 82 → k ≠ 90 →
      traceOnly (computeTraceSubst .traceCur k) = true := by decide

/-- `decodeSource`'s trace at a trace-only column agrees on environments with equal source traces. -/
theorem decodeSource_trace_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) (k : ℕ)
    (hk : traceOnly (computeTraceSubst .traceCur k) = true) :
    (decodeSource env).trace k = (decodeSource env').trace k :=
  eval_congr_of_traceOnly _ h hk

theorem computeStateOf_congr {E E' : Env K} (h : ∀ k, k < 11 → E.trace k = E'.trace k) :
    computeStateOf E = computeStateOf E' := by
  unfold computeStateOf
  rw [h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega), h 10 (by omega)]

theorem computeStateOf_decodeSource_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) :
    computeStateOf (decodeSource env) = computeStateOf (decodeSource env') :=
  computeStateOf_congr fun k hk =>
    decodeSource_trace_congr h k (computeTraceSubst_traceOnly k (by omega) (by omega) (by omega)
      (by omega))

theorem fpOf_decodeSource_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) (b : ℕ)
    (hb : b + 2 < 93) (h1 : b ≠ 74) (h2 : b ≠ 82) (h3 : b ≠ 90)
    (h4 : b + 1 ≠ 74) (h5 : b + 1 ≠ 82) (h6 : b + 1 ≠ 90)
    (h7 : b + 2 ≠ 74) (h8 : b + 2 ≠ 82) (h9 : b + 2 ≠ 90) :
    fpOf (decodeSource env) b = fpOf (decodeSource env') b := by
  unfold fpOf
  rw [decodeSource_trace_congr h b (computeTraceSubst_traceOnly b (by omega) h1 h2 h3),
    decodeSource_trace_congr h (b + 1) (computeTraceSubst_traceOnly (b + 1) (by omega) h4 h5 h6),
    decodeSource_trace_congr h (b + 2) (computeTraceSubst_traceOnly (b + 2) (by omega) h7 h8 h9)]

theorem decOf_decodeSource_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) :
    decOf (decodeSource env) = decOf (decodeSource env') := by
  unfold decOf
  rw [fpOf_decodeSource_congr h 47 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fpOf_decodeSource_congr h 50 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fpOf_decodeSource_congr h 53 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fpOf_decodeSource_congr h 56 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fpOf_decodeSource_congr h 59 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    fpOf_decodeSource_congr h 62 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The record root / child / axis (not the timestamp) of a decoded record agree. -/
theorem mrOf_decodeSource_core_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) (b : ℕ) (hb : b = 67 ∨ b = 75 ∨ b = 83) :
    (mrOf (decodeSource env) b).root = (mrOf (decodeSource env') b).root ∧
      (mrOf (decodeSource env) b).child = (mrOf (decodeSource env') b).child ∧
      (mrOf (decodeSource env) b).axis = (mrOf (decodeSource env') b).axis := by
  unfold mrOf
  rcases hb with rfl | rfl | rfl <;>
  · refine ⟨?_, ?_, ?_⟩
    · exact fpOf_decodeSource_congr h _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact fpOf_decodeSource_congr h _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact decodeSource_trace_congr h _ (computeTraceSubst_traceOnly _ (by omega) (by omega)
        (by omega) (by omega))

/-- Replace the compute inputs record of a row label. -/
def setInp (inp : ComputeTable.Inputs K) (l : State × DTcomp K) : State × DTcomp K :=
  (l.1, (inp, l.2.2))

@[simp] theorem setInp_fst (inp : ComputeTable.Inputs K) (l : State × DTcomp K) :
    (setInp inp l).1 = l.1 := rfl

@[simp] theorem setInp_pub (inp : ComputeTable.Inputs K) (l : State × DTcomp K) :
    (setInp inp l).2.2.1 = l.2.2.1 := rfl

@[simp] theorem setInp_dec (inp : ComputeTable.Inputs K) (l : State × DTcomp K) :
    (setInp inp l).2.2.2 = l.2.2.2 := rfl

/-- **The specialized compute row ignores the decoded record timestamps and the placeholder
inputs**: two decoded rows with equal source traces specialize to rows differing at most in the
inputs record (`computeLineOrigin … 0 = ln_prev`; `specializeMemRecScaled` overwrites `ts`). -/
theorem specialize_wrap_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.toSourceEnv.trace = env'.toSourceEnv.trace) (st : State) (α : K)
    (inp inp' : ComputeTable.Inputs K) :
    (wrapComputeLabel (st, (inp, decodePub env st, decodeDec env))).specialize α =
      setInp { inp with α := α }
        ((wrapComputeLabel (st, (inp', decodePub env' st, decodeDec env'))).specialize α) := by
  have hs := fpOf_decodeSource_congr h 11 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hf := fpOf_decodeSource_congr h 14 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have he := fpOf_decodeSource_congr h 17 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h20 := fpOf_decodeSource_congr h 20 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h23 := fpOf_decodeSource_congr h 23 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h26 := fpOf_decodeSource_congr h 26 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h29 := fpOf_decodeSource_congr h 29 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h32 := fpOf_decodeSource_congr h 32 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h35 := fpOf_decodeSource_congr h 35 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h38 := fpOf_decodeSource_congr h 38 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h41 := fpOf_decodeSource_congr h 41 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h44 := fpOf_decodeSource_congr h 44 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hln := decodeSource_trace_congr h 65 (computeTraceSubst_traceOnly 65 (by omega) (by omega)
    (by omega) (by omega))
  have hmr1 := mrOf_decodeSource_core_congr h 67 (by omega)
  have hmr2 := mrOf_decodeSource_core_congr h 75 (by omega)
  have hmr3 := mrOf_decodeSource_core_congr h 83 (by omega)
  have hdec := decOf_decodeSource_congr h
  -- the specialized record from a decoded record: root / child / axis of the decoded one, `ts`
  -- rewritten; equal decoded cores give equal specialized records
  have hrec : ∀ (b : ℕ) (hb : b = 67 ∨ b = 75 ∨ b = 83) (lnPrev : K) (active : Bool) (e : ℕ),
      specializeMemRecScaled α lnPrev active e (mrOf (decodeSource env) b) =
        specializeMemRecScaled α lnPrev active e (mrOf (decodeSource env') b) := by
    intro b hb lnPrev active e
    obtain ⟨hr, hc, ha⟩ := mrOf_decodeSource_core_congr h b hb
    unfold specializeMemRecScaled
    split_ifs
    · cases hm : mrOf (decodeSource env) b
      cases hm' : mrOf (decodeSource env') b
      rw [hm, hm'] at hr hc ha
      simp only at hr hc ha
      subst hr hc ha
      rfl
    · rfl
  unfold decodePub decodeDec
  simp only [ComputeRowTemplate.specialize, wrapComputeLabel, setInp, computeLineOrigin,
    pubOfState]
  rw [hdec, hs, hf, he, h20, h23, h26, h29, h32, h35, h38, h41, h44, hln,
    hrec 67 (by omega), hrec 75 (by omega), hrec 83 (by omega)]
  rfl

end Decoders

/-! ## §B  Over `O`: the coin-free tuple and the trace fields -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **The coin-free tuple**: every coordinate `0`.  The event-side strategy is the C2 strategy at
this tuple; nothing the P8 slot reads depends on it (§D). -/
def coinFree : OptimizedProductionChallengeTuple K F :=
  (((0, 0), (0, 0)), ((0, 0), (⟨0, 0, 0⟩, ⟨0, 0⟩)))

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- `P.computeChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

section Traces

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])

/-- The round-0 compute envs' traces do not read the tuple. -/
theorem computeEnvsR0_trace (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    (computeEnvsR0 O Qc c i).trace = (computeEnvsR0 O Qc c' i).trace := by
  unfold computeEnvsR0 FamilyEnvCore.rowEnvAt
  apply FamilyEnvCore.gather_toSourceEnv_trace_congr
  rw [FamilyEnvCore.familyQc_envTrace, FamilyEnvCore.familyQc_envTrace]
  rfl

/-- The memory base envs' traces do not read the tuple. -/
theorem memoryEnvsR0_trace (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.memRows) :
    (memoryEnvsR0 O Qm c i).trace = (memoryEnvsR0 O Qm c' i).trace := rfl

/-- The memory `𝕂` envs' traces do not read the tuple. -/
theorem memorySourceEnvAt_trace (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.memRows) :
    (FamilyEnvCore.memorySourceEnvAt O c Qm i).trace =
      (FamilyEnvCore.memorySourceEnvAt O c' Qm i).trace := rfl

/-- The memory `𝕂` envs' challenge `8` (the row's `λ`) does not read the row. -/
theorem memorySourceEnvAt_chal8 (c : OptimizedProductionChallengeTuple K F)
    (i j : Fin O.family.problem.cfg.memRows) :
    (FamilyEnvCore.memorySourceEnvAt O c Qm i).chal 8 =
      (FamilyEnvCore.memorySourceEnvAt O c Qm j).chal 8 := rfl

/-- The decoded compute state does not read the tuple. -/
theorem lblC_state (c c' : OptimizedProductionChallengeTuple K F) (i : ℕ) :
    (lblC O Qc c i).1 = (lblC O Qc c' i).1 := by
  unfold lblC
  split_ifs <;>
  · unfold lblCAt
    exact computeStateOf_decodeSource_congr (computeEnvsR0_trace O Qc c c' _)

/-- The round-0 record carrier `S` does not read the tuple. -/
theorem c2SAt_eq (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    c2SAt O Qc c i = c2SAt O Qc c' i := by
  unfold c2SAt
  rw [computeEnvsR0_trace O Qc c c' i]

theorem foC_eq (c c' : OptimizedProductionChallengeTuple K F) : foC O Qc c = foC O Qc c' := by
  funext i
  unfold foC
  rw [lblC_state O Qc c c' i]

/-- The compute inputs record decoded at `c` (row-independent: the five challenge slots). -/
def inpAt (c : OptimizedProductionChallengeTuple K F) : ComputeTable.Inputs K :=
  inpOf (decodeSource (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc)
    ⟨0, O.family.problem.cfg.compRows_pos⟩))

theorem inpOf_rowEnvAt (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    inpOf (decodeSource (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i)) =
      inpAt O Qc c := by
  unfold inpAt
  simp only [inpOf, decodeSource, Env.ofSubst, computeSubst, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, FamilyEnvCore.rowEnvAt,
    OptimizedComputeSemanticRealization.gatherCorrectedFinalTypedEnv, Framework.Reify.envOfTrace]

theorem lblCAt_inputs (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    (lblCAt O Qc c i).2.1 = inpAt O Qc c :=
  inpOf_rowEnvAt O Qc c i

theorem lblC_inputs (c : OptimizedProductionChallengeTuple K F) (i : ℕ) :
    (lblC O Qc c i).2.1 = inpAt O Qc c := by
  unfold lblC
  split_ifs <;> exact lblCAt_inputs O Qc c _

/-- The specialized compute row at `c`, row by row. -/
theorem specRowAt_eq (c c' : OptimizedProductionChallengeTuple K F) (α : K)
    (i : Fin O.family.problem.cfg.compRows) :
    (wrapComputeLabel (lblCAt O Qc c i)).specialize α =
      setInp { inpAt O Qc c with α := α }
        ((wrapComputeLabel (lblCAt O Qc c' i)).specialize α) := by
  have hst := computeStateOf_decodeSource_congr (computeEnvsR0_trace O Qc c c' i)
  have hinp := inpOf_rowEnvAt O Qc c i
  unfold lblCAt decodeInputs
  simp only []
  rw [hst, hinp]
  exact specialize_wrap_congr (computeEnvsR0_trace O Qc c c' i) _ α _ _

/-- **The specialized compute row at `c` is the one at `c'` with the inputs reset.** -/
theorem specRow_eq (c c' : OptimizedProductionChallengeTuple K F) (α : K) (j : ℕ) :
    (wrapComputeLabel (lblC O Qc c j)).specialize α =
      setInp { inpAt O Qc c with α := α }
        ((wrapComputeLabel (lblC O Qc c' j)).specialize α) := by
  unfold lblC
  split_ifs <;> exact specRowAt_eq O Qc c c' α _

/-- The decoded memory challenge record at `c`. -/
def memRec (c : OptimizedProductionChallengeTuple K F) : MemoryTable.Inputs K :=
  { z := nprSeed c.1, β := -(c.2.2.2.interPole), γ := c.2.1.1 }

/-- The memory rows' decoded `λ` at `c` (`chal 8` of the `𝕂` env; row-independent). -/
def lamAt (c : OptimizedProductionChallengeTuple K F) : K :=
  (FamilyEnvCore.memorySourceEnvAt O c Qm ⟨0, O.family.problem.cfg.memRows_pos⟩).chal 8

/-- Reset the challenge record and `lambda?` of a decoded memory label. -/
def ψM (c : OptimizedProductionChallengeTuple K F) (lam : K) :
    MState × DTmem K → MState × DTmem K :=
  fun l => (l.1, (memRec c, { l.2.2 with lambda? := some lam }))

@[simp] theorem ψM_fst (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (l : MState × DTmem K) : (ψM c lam l).1 = l.1 := rfl

@[simp] theorem ψM_pt (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (l : MState × DTmem K) : (ψM c lam l).2.2.pt = l.2.2.pt := rfl

@[simp] theorem ψM_lc (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (l : MState × DTmem K) : (ψM c lam l).2.2.lc = l.2.2.lc := rfl

@[simp] theorem ψM_rc (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (l : MState × DTmem K) : (ψM c lam l).2.2.rc = l.2.2.rc := rfl

@[simp] theorem ψM_mem (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (l : MState × DTmem K) : (ψM c lam l).2.2.mem = l.2.2.mem := rfl

/-- **The decoded memory label at `c` is the one at `c'` with the record and `λ` reset.** -/
theorem lblM_transport (c c' : OptimizedProductionChallengeTuple K F) (i : ℕ) :
    lblM O Qm c i = ψM c (lamAt O Qm c) (lblM O Qm c' i) := by
  unfold lblM
  split_ifs <;> rfl

theorem foM_eq (c c' : OptimizedProductionChallengeTuple K F) : foM O Qm c = foM O Qm c' := by
  funext i
  unfold foM
  rw [lblM_transport O Qm c c' i]
  rfl

/-- The tiling hypotheses do not read the tuple. -/
theorem tracesWalkHyps_iff (c c' : OptimizedProductionChallengeTuple K F) :
    TracesWalkHyps O Qc Qm c ↔ TracesWalkHyps O Qc Qm c' := by
  constructor
  · intro h
    exact ⟨by rw [← foC_eq O Qc c c']; exact h.sfCompute,
      by rw [← foC_eq O Qc c c']; exact h.validCompute,
      by rw [← foM_eq O Qm c c']; exact h.sfMemory,
      by rw [← foM_eq O Qm c c']; exact h.validMemory⟩
  · intro h
    exact ⟨by rw [foC_eq O Qc c c']; exact h.sfCompute,
      by rw [foC_eq O Qc c c']; exact h.validCompute,
      by rw [foM_eq O Qm c c']; exact h.sfMemory,
      by rw [foM_eq O Qm c c']; exact h.validMemory⟩

end Traces

/-! ## §C  Round-0 wrap data (exponent, certificate axis, served nouns) do not read the tuple -/

section Wrap

theorem memRowExpOfEnvs_congr {M : ℕ} {envsF envsF' : Fin M → Env F}
    (h : ∀ i, (envsF i).trace = (envsF' i).trace) (hM : 0 < M) (i : ℕ) :
    memRowExpOfEnvs envsF hM i = memRowExpOfEnvs envsF' hM i := by
  unfold memRowExpOfEnvs
  split_ifs <;> rw [h]

theorem computeArity_congr {E E' : Env K} (h : E.trace = E'.trace) :
    computeArity E = computeArity E' := by
  unfold computeArity; rw [h]

theorem computePrefix_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (i : Fin N) :
    computePrefix envsC i = computePrefix envsC' i := by
  unfold computePrefix
  exact Finset.sum_congr rfl fun j _ => computeArity_congr (h j)

theorem locateExp_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (e : ℕ) :
    locateExp envsC e = locateExp envsC' e := by
  have hp : (fun i : Fin N => decide (computePrefix envsC i < e ∧
      e ≤ computePrefix envsC i + computeArity (envsC i))) =
      fun i : Fin N => decide (computePrefix envsC' i < e ∧
      e ≤ computePrefix envsC' i + computeArity (envsC' i)) := by
    funext i
    rw [computePrefix_congr h i, computeArity_congr (h i)]
  unfold locateExp
  rw [hp]
  congr 1
  funext i
  rw [computePrefix_congr h i]

theorem slotCert_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (i : Fin N) (j : ℕ) :
    slotCert envsC i j = slotCert envsC' i j := by
  unfold slotCert rowShift rowBits
  rw [h i]

theorem decodedShift_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (e : ℕ) :
    decodedShift envsC e = decodedShift envsC' e := by
  unfold decodedShift
  rw [locateExp_congr h e]
  split
  · rw [slotCert_congr h]
  · rfl

theorem decodedBits_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (e : ℕ) :
    decodedBits envsC e = decodedBits envsC' e := by
  funext k
  unfold decodedBits
  rw [locateExp_congr h e]
  split
  · rw [slotCert_congr h]
  · rfl

theorem certAxisOfEnvs_congr {N : ℕ} {envsC envsC' : Fin N → Env K}
    (h : ∀ i, (envsC i).trace = (envsC' i).trace) (e : ℕ) :
    certAxisOfEnvs envsC e = certAxisOfEnvs envsC' e := by
  unfold certAxisOfEnvs
  rw [decodedShift_congr h e, decodedBits_congr h e]

end Wrap

section OverO

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])

theorem c2AxOf_eq (c c' : OptimizedProductionChallengeTuple K F) :
    c2AxOf O Qc c = c2AxOf O Qc c' := by
  funext e
  exact certAxisOfEnvs_congr (fun i => computeEnvsR0_trace O Qc c c' i) e

theorem c2ServedOf_eq (c c' : OptimizedProductionChallengeTuple K F) :
    c2ServedOf O Qm c = c2ServedOf O Qm c' := by
  unfold c2ServedOf
  exact PreZComputeCore.Served.servedNounOfEnvs_congr K _ _
    (fun i col _ => by rw [memoryEnvsR0_trace O Qm c c' i]) _

/-- Reset the placeholder's challenge record and `λ` of a memory row template. -/
def ψT (c : OptimizedProductionChallengeTuple K F) (lam : K) :
    MemoryRowTemplate (K := K) → MemoryRowTemplate (K := K) :=
  fun T => { T with placeholder := ψM c lam T.placeholder }

@[simp] theorem ψT_timestamp (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (T : MemoryRowTemplate (K := K)) : (ψT c lam T).timestamp = T.timestamp := rfl

@[simp] theorem ψT_axis (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (T : MemoryRowTemplate (K := K)) :
    (ψT c lam T).placeholder.2.2.mem.axis = T.placeholder.2.2.mem.axis := rfl

/-- **The round-0 template row at `c` is the one at `c'` with the record and `λ` reset.** -/
theorem lblMR0_transport (c c' : OptimizedProductionChallengeTuple K F) (i : ℕ) :
    lblMR0 O Qc Qm c i = ψT c (lamAt O Qm c) (lblMR0 O Qc Qm c' i) := by
  unfold lblMR0 wrapR0OfEnvs
  rw [memRowExpOfEnvs_congr (fun j => memoryEnvsR0_trace O Qm c c' j),
    certAxisOfEnvs_congr (fun j => computeEnvsR0_trace O Qc c c' j),
    lblM_transport O Qm c c' i]
  rfl

/-- The a-bearing specialization commutes with the reset. -/
theorem specializeA_ψT (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (T : MemoryRowTemplate (K := K)) (α : K) :
    (ψT c lam T).specializeA α = ψM c lam (T.specializeA α) := rfl

/-- Reset only the challenge record of a memory label (the row encode has written `λ`). -/
def setMemRec (c : OptimizedProductionChallengeTuple K F) :
    MState × DTmem K → MState × DTmem K :=
  fun l => (l.1, (memRec c, l.2.2))

/-- The full specialization (row encode included) commutes with the reset, up to the record. -/
theorem specialize_ψT (c : OptimizedProductionChallengeTuple K F) (lam : K)
    (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (ψT c lam T).specialize α lmb = setMemRec c (T.specialize α lmb) := by
  unfold MemoryRowTemplate.specialize MemoryRowTemplate.encodeRow setMemRec
  rw [specializeA_ψT]
  simp only [ψM]
  rfl

end OverO

/-! ## §D  The `h`-free skeleton, template and strategy at the coin-free tuple -/

section Strategy

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])

/-- **The event skeleton**: the C2 compute tree at `coinFree`, and the a-bearing memory forest
decoded from the inverse-BFS forest at `coinFree` — the term `execOfTraces … h` wraps, so no
tiling proof is needed. -/
def skeletonEv : SemanticSkeleton where
  computeTree := c2ComputeTree O Qc Qm coinFree
  memoryForest :=
    decodedMemoryForestAx (ringChar K)
      (reconForest O.family.problem.cfg.kMem (foM O Qm coinFree) (lblM O Qm coinFree)
        O.family.problem.cfg.memRows)
      (axOfRowsR0 O Qc Qm coinFree)

/-- At the coin-free tuple the event skeleton IS the C2 skeleton (any tiling proof). -/
theorem skeletonEv_eq (h : TracesWalkHyps O Qc Qm coinFree) :
    skeletonEv O Qc Qm = decodedSkeletonC2 O Qc Qm coinFree h := rfl

/-- The package's own honest execution, wrapped as a round-0 template at the traces' config
(the inhabitant of the template type when the traces do not tile). -/
def honestTemplateEv (z : K) : ExactExecutionTemplate (cfgTemplateOfTraces O Qc Qm coinFree z) where
  computeTree := mapNTree wrapComputeLabel O.family.problem.exec.computeTree
  memoryForest := O.family.problem.exec.memoryForest.map (mapNTree (wrapMemoryLabelR0 0 0))
  memoryForest_nonempty := by
    simpa using O.family.problem.exec.memoryForest_nonempty
  memory_root_count := by
    show (O.family.problem.exec.memoryForest.map _).length = O.family.problem.cfg.kMem
    rw [List.length_map]
    exact O.family.problem.exec.memory_root_count
  compute_bfs_length := by
    show (bfsForest [mapNTree wrapComputeLabel O.family.problem.exec.computeTree]).length =
      (computeLabelList O Qc coinFree).length
    rw [computeLabelList_length,
      show [mapNTree wrapComputeLabel O.family.problem.exec.computeTree] =
        [O.family.problem.exec.computeTree].map (mapNTree wrapComputeLabel) from rfl,
      bfsForest_mapNTree, List.length_map]
    exact O.family.problem.exec.compute_bfs_length
  memory_bfs_length := by
    show (bfsForest (O.family.problem.exec.memoryForest.map
      (mapNTree (wrapMemoryLabelR0 0 0)))).length = (memoryLabelList O Qm coinFree).length
    rw [memoryLabelList_length, bfsForest_mapNTree, List.length_map]
    exact O.family.problem.exec.memory_bfs_length

open scoped Classical in
/-- **The event template**: the round-0 template at `coinFree` when the traces tile, else the
honest wrap.  No `TracesWalkHyps` argument. -/
def execTemplateEv (z : K) : ExactExecutionTemplate (cfgTemplateOfTraces O Qc Qm coinFree z) :=
  if h : TracesWalkHyps O Qc Qm coinFree then execTemplateOfTracesR0 O Qc Qm coinFree h z
  else honestTemplateEv O Qc Qm z

theorem execTemplateEv_eq (h : TracesWalkHyps O Qc Qm coinFree) (z : K) :
    execTemplateEv O Qc Qm z = execTemplateOfTracesR0 O Qc Qm coinFree h z := by
  unfold execTemplateEv
  rw [dif_pos h]

/-- The event timestamp strategy: the event skeleton's public claim, the traces' config template
and the event template, at every seed. -/
def timestampEv : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    (skeletonEv O Qc Qm).publicClaim
    (fun seed => cfgTemplateOfTraces O Qc Qm coinFree seed.1)
    (fun seed => execTemplateEv O Qc Qm seed.1)
    (fun _ => rfl)

/-- **The event-side built strategy**: coin-free, `h`-free.  The generic chain `verifierGen` at
`timestampEv` and the coin-free tuple; skeleton `skeletonEv`; `publicClaim_eq` by `rfl`. -/
def strategyOfTracesEv (tag : NodeEncoding.StateTagChar K) : ProductionStrategy F K where
  verifier := verifierGen O (timestampEv O Qc Qm) tag Qc Qm coinFree
  skeleton := skeletonEv O Qc Qm
  publicClaim_eq := rfl

theorem strategyOfTracesEv_skeleton (tag : NodeEncoding.StateTagChar K) :
    (strategyOfTracesEv O Qc Qm tag).skeleton = skeletonEv O Qc Qm := rfl

/-- The event strategy's committed template at seed `z` is the event template. -/
theorem committedTemplate_Ev (tag : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) :
    committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz = execTemplateEv O Qc Qm z :=
  rfl

/-- The C2 strategy's committed template at seed `z` is the round-0 template at `c`. -/
theorem committedTemplate_C2 (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) (z : K)
    (hz : z ≠ 0) :
    committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz =
      execTemplateOfTracesR0 O Qc Qm c h z :=
  rfl

end Strategy

/-! ## §E  Agreement with `strategyOfTracesR0AC2 … c h`, for every `c` and `h` -/

section Agreement

variable {β : Type}

/-- The C2 join factors through the `(state, S)` projection of the labels. -/
theorem c2JoinFuel_factor (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (t : NTree β) (subj formula : Noun),
      c2JoinFuel st Sof sv ax n t subj formula =
        c2JoinFuel Prod.fst Prod.snd sv ax n (mapNTree (fun l => (st l, Sof l)) t) subj formula := by
  intro n
  induction n with
  | zero =>
      intro t subj formula
      cases t with
      | node row ch => simp [c2JoinFuel, mapNTree]
  | succ n ih =>
      intro t subj formula
      cases t with
      | node row ch =>
          simp only [c2JoinFuel, c2JoinKids, mapNTree]
          generalize hs : st row = s
          cases s <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ch'⟩⟩⟩⟩ <;>
            (simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, ih]
             try rfl)

/-- The C2 join never has more nodes than the label tree. -/
theorem c2JoinFuel_size_le (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (t : NTree β) (subj formula : Noun),
      (c2JoinFuel st Sof sv ax n t subj formula).size ≤ t.size := by
  intro n
  induction n with
  | zero =>
      intro t subj formula
      cases t with
      | node row ch =>
          simp only [c2JoinFuel, NTree.size, List.map_nil, List.sum_nil]
          omega
  | succ n ih =>
      intro t subj formula
      cases t with
      | node row ch =>
          have H : ∀ (c : NTree β) (s f : Noun),
              (c2JoinFuel st Sof sv ax n c s f).size ≤ c.size := ih
          have hsum : ∀ (kids : List (NTree ComputeRowSkeleton)) (ch : List (NTree β)),
              List.Forall₂ (fun k c => k.size ≤ c.size) kids ch →
              (kids.map NTree.size).sum ≤ (ch.map NTree.size).sum := by
            intro kids ch hf
            induction hf with
            | nil => simp
            | cons h _ ih' => simp only [List.map_cons, List.sum_cons]; omega
          simp only [c2JoinFuel, c2JoinKids]
          generalize hs : st row = s
          cases s <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ch'⟩⟩⟩⟩ <;>
            (simp only [NTree.size]
             apply Nat.add_le_add_left
             apply hsum
             simp [List.forall₂_cons, List.forall₂_map_left_iff, List.forall₂_same, H])

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])

/-- The `(state, S)` projection of the S-carrying exec tree does not read the tuple. -/
theorem c2TreeOfTraces_proj (c c' : OptimizedProductionChallengeTuple K F) :
    mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTraces O Qc c) =
      mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTraces O Qc c') := by
  unfold c2TreeOfTraces reconTree
  rw [mapNTree_buildT', mapNTree_buildT', foC_eq O Qc c c']
  congr 1
  funext j
  unfold lblCS
  split_ifs
  · rw [lblC_state O Qc c c' j, c2SAt_eq O Qc c c']
  · rw [lblC_state O Qc c c' j, c2SAt_eq O Qc c c']

/-- **The C2 compute tree does not read the tuple.** -/
theorem c2ComputeTree_eq (c c' : OptimizedProductionChallengeTuple K F) :
    c2ComputeTree O Qc Qm c = c2ComputeTree O Qc Qm c' := by
  unfold c2ComputeTree c2Join
  rw [c2JoinFuel_factor, c2JoinFuel_factor (t := c2TreeOfTraces O Qc c')]
  have hproj := c2TreeOfTraces_proj O Qc c c'
  have hsize : (c2TreeOfTraces O Qc c).size = (c2TreeOfTraces O Qc c').size := by
    have := congrArg NTree.size hproj
    rwa [size_mapNTree, size_mapNTree] at this
  rw [hsize, hproj, c2ServedOf_eq O Qm c c', c2AxOf_eq O Qc c c']

/-- **Agreement 1 — the compute skeleton**: for every `c` and `h`, the C2 strategy's compute tree
is the event skeleton's. -/
theorem computeTree_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton.computeTree =
      (strategyOfTracesEv O Qc Qm tag).skeleton.computeTree :=
  c2ComputeTree_eq O Qc Qm c coinFree

theorem publicClaim_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton.publicClaim =
      (strategyOfTracesEv O Qc Qm tag).skeleton.publicClaim := by
  unfold SemanticSkeleton.publicClaim
  rw [computeTree_agree O Qc Qm tag c h]

theorem computeSkeletonRows_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    computeSkeletonRows (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton =
      computeSkeletonRows (strategyOfTracesEv O Qc Qm tag).skeleton := by
  unfold computeSkeletonRows
  rw [computeTree_agree O Qc Qm tag c h]

/-- The census pair list (the P8 pairs and the edge pairs) agrees. -/
theorem combinedSkeletonPairs_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    EdgeComparisonCensus.combinedSkeletonPairs K (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton =
      EdgeComparisonCensus.combinedSkeletonPairs K (strategyOfTracesEv O Qc Qm tag).skeleton := by
  unfold EdgeComparisonCensus.combinedSkeletonPairs BoundSemanticTrace.skeletonPairs
    P8Census.skeletonComparisonCensus
  rw [computeTree_agree O Qc Qm tag c h, publicClaim_agree O Qc Qm tag c h,
    computeSkeletonRows_agree O Qc Qm tag c h]

/-- The size-window noun list agrees. -/
theorem skeletonSizeWindowNouns_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    SizeWindowCounting.skeletonSizeWindowNouns (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton =
      SizeWindowCounting.skeletonSizeWindowNouns (strategyOfTracesEv O Qc Qm tag).skeleton := by
  unfold SizeWindowCounting.skeletonSizeWindowNouns
  rw [computeSkeletonRows_agree O Qc Qm tag c h]

/-- The request targets (the 33rd's pair event at the built targets) agree. -/
theorem requestTargets_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    PreSeedCensus.requestTargets (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton =
      PreSeedCensus.requestTargets (strategyOfTracesEv O Qc Qm tag).skeleton := by
  funext st k
  unfold PreSeedCensus.requestTargets PreSeedCensus.requestList
  rw [computeSkeletonRows_agree O Qc Qm tag c h]

/-- The decoded memory tree keeps the forest's shape. -/
theorem size_decodeMemoryTreeAx (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (ax : MState × DTmem K → ℕ) :
    ∀ t, (decodeMemoryTreeAx q forest ax t).size = t.size := by
  intro t
  let P := fun t : NTree (MState × DTmem K) => (decodeMemoryTreeAx q forest ax t).size = t.size
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl ch ih
    simp only [P, decodeMemoryTreeAx, NTree.size, List.map_map]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

/-- **Agreement 2 — the memory row count**: for every `c` and `h`. -/
theorem memoryRows_length_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) :
    (memorySkeletonRows (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton).length =
      (memorySkeletonRows (strategyOfTracesEv O Qc Qm tag).skeleton).length := by
  show ((bfsForest (decodedMemoryForestAx (ringChar K)
      (reconForest O.family.problem.cfg.kMem (foM O Qm c) (lblM O Qm c)
        O.family.problem.cfg.memRows) (axOfRowsR0 O Qc Qm c))).map NTree.label).length =
    ((bfsForest (decodedMemoryForestAx (ringChar K)
      (reconForest O.family.problem.cfg.kMem (foM O Qm coinFree) (lblM O Qm coinFree)
        O.family.problem.cfg.memRows) (axOfRowsR0 O Qc Qm coinFree))).map NTree.label).length
  rw [List.length_map, List.length_map, bfsForest_length, bfsForest_length]
  unfold totalSize decodedMemoryForestAx
  rw [List.map_map, List.map_map]
  have hforest : reconForest O.family.problem.cfg.kMem (foM O Qm c) (lblM O Qm c)
      O.family.problem.cfg.memRows =
      (reconForest O.family.problem.cfg.kMem (foM O Qm coinFree) (lblM O Qm coinFree)
        O.family.problem.cfg.memRows).map (mapNTree (ψM c (lamAt O Qm c))) := by
    rw [mapNTree_reconForest, foM_eq O Qm c coinFree]
    congr 1
    funext i
    exact lblM_transport O Qm c coinFree i
  rw [hforest, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_def, size_decodeMemoryTreeAx, size_mapNTree]

/-- **Agreement 3 — the committed template's memory forest**: at `c` it is the event template's
relabelled by `ψT c (lamAt O Qm c)`, which touches neither the timestamp metadata nor the stored
axis (what the axis tree reads) nor the `pt`/`lc`/`rc` cells (what the topology payloads read). -/
theorem template_memoryForest_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) (z : K)
    (hz : z ≠ 0) :
    (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz).memoryForest =
      (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).memoryForest.map
        (mapNTree (ψT c (lamAt O Qm c))) := by
  have h0 : TracesWalkHyps O Qc Qm coinFree := (tracesWalkHyps_iff O Qc Qm c coinFree).1 h
  have hE : (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).memoryForest =
      (execTemplateOfTracesR0 O Qc Qm coinFree h0 z).memoryForest := by
    show (execTemplateEv O Qc Qm z).memoryForest = _
    rw [execTemplateEv_eq O Qc Qm h0 z]
  rw [hE]
  show reconForest O.family.problem.cfg.kMem (foM O Qm c) (lblMR0 O Qc Qm c)
      O.family.problem.cfg.memRows =
    (reconForest O.family.problem.cfg.kMem (foM O Qm coinFree) (lblMR0 O Qc Qm coinFree)
      O.family.problem.cfg.memRows).map (mapNTree (ψT c (lamAt O Qm c)))
  rw [mapNTree_reconForest, foM_eq O Qm c coinFree]
  congr 1
  funext i
  exact lblMR0_transport O Qc Qm c coinFree i

/-- **Agreement 4 — the specialized compute tree**: at `c` it is the event's relabelled by
`setInp` (the inputs record only). -/
theorem template_computeTree_spec_agree (tag : NodeEncoding.StateTagChar K)
    (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c) (z : K)
    (hz : z ≠ 0) (α : K) :
    mapNTree (fun r => r.specialize α)
        (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz).computeTree =
      mapNTree (setInp { inpAt O Qc c with α := α })
        (mapNTree (fun r => r.specialize α)
          (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).computeTree) := by
  have h0 : TracesWalkHyps O Qc Qm coinFree := (tracesWalkHyps_iff O Qc Qm c coinFree).1 h
  have hE : (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).computeTree =
      (execTemplateOfTracesR0 O Qc Qm coinFree h0 z).computeTree := by
    show (execTemplateEv O Qc Qm z).computeTree = _
    rw [execTemplateEv_eq O Qc Qm h0 z]
  rw [hE]
  show mapNTree (fun r => r.specialize α) (mapNTree wrapComputeLabel
      (reconTree (foC O Qc c) (lblC O Qc c) O.family.problem.cfg.compRows)) =
    mapNTree (setInp { inpAt O Qc c with α := α }) (mapNTree (fun r => r.specialize α)
      (mapNTree wrapComputeLabel
        (reconTree (foC O Qc coinFree) (lblC O Qc coinFree) O.family.problem.cfg.compRows)))
  rw [ReconTreeSize.mapNTree_comp, ReconTreeSize.mapNTree_comp,
    ReconTreeSize.mapNTree_comp, mapNTree_reconTree, mapNTree_reconTree,
    foC_eq O Qc c coinFree]
  congr 1
  funext j
  exact specRow_eq O Qc c coinFree α j

/-- The row counts of the event strategy's committed templates are the traces' (every seed). -/
theorem committedTemplate_Ev_compRows (tag : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) :
    ((strategyOfTracesEv O Qc Qm tag).verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.compRows =
      O.family.problem.cfg.compRows :=
  computeLabelList_length O Qc coinFree

theorem committedTemplate_Ev_memRows (tag : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) :
    ((strategyOfTracesEv O Qc Qm tag).verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.memRows =
      O.family.problem.cfg.memRows :=
  memoryLabelList_length O Qm coinFree

theorem committedTemplate_Ev_kMem (tag : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) :
    ((strategyOfTracesEv O Qc Qm tag).verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem =
      O.family.problem.cfg.kMem :=
  rfl

/-- The event skeleton's compute row count is at most the traces' compute row count, at every
trace (`ReconTreeSize.reconTree_size_le` + `c2JoinFuel_size_le`). -/
theorem skeletonEv_computeRows_le :
    (computeSkeletonRows (skeletonEv O Qc Qm)).length ≤ O.family.problem.cfg.compRows := by
  show ((bfsForest [c2ComputeTree O Qc Qm coinFree]).map NTree.label).length ≤ _
  rw [List.length_map, ← size_eq_bfs_length]
  unfold c2ComputeTree c2Join
  refine (c2JoinFuel_size_le _ _ _ _ _ _ _ _).trans ?_
  unfold c2TreeOfTraces
  exact reconTree_size_le _ _ _ O.family.problem.cfg.compRows_pos

end Agreement

end

end Nock.NockVMROM.Thm54.StrategyOfTracesEv
