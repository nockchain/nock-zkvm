/-
  Nock/RedTeam/Batch268Thm54MemoryTerminalBoundToRequests.lean

  **The memory chip's shared terminal is bound to the post-challenge public `requests`.**

  The paper's terminal is a RAP **output** — `requests = acc_prog(h₁)`
, `out_mem = acc_mem(h₂)` (`:586`) — and the IO consistency check equates
  the two sides (`:597-599`).

  `M.rap.s = 112` and the residual are
  untouched; role `45` is now unread.

* `terminal_bound_to_requests` — for **any** trace `P.memoryChip` accepts, at **every** row the
    gathered terminal role `40` equals the gathered public `requests`;
  * `moved_terminal_rejected` — a trace whose role-`40` columns are bumped by a constant `c ≠ 0`
    (at every row, so every other gate is untouched) is rejected;
  * `canonical_trace_accepted` — the honest trace still passes (the new pin is discharged by the
    package's `memoryPublicTargets`), so the binding costs no completeness.

  Together with `LL` the memory accumulator now telescopes hostilely from `0` to the public
  `requests`.  Not claimed: anything about the compute chip; anything about the compute/memory equality of `requests` beyond both
  chips reading the package's publics.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.BuildableChips

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch268

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Module
open scoped Polynomial

noncomputable section

open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The three binding gates, read at the gathered `𝕂` level -/

theorem memCol0_eq (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).col0 3 = memoryCol0 := rfl

/-- The three base gates `sampledTerminalCoord k` are the coordinates of the `𝕂`-level source
`role 40 − public 2`. -/
theorem sampledTerminalCoord_is_binding (b : Basis (Fin 3) F K) (k : Fin 3) :
    sampledTerminalCoord (F := F) k =
      coordinateCompile b memoryCol0 (.Sub (extVar .traceCur 40) (extVar .publicVal 2)) k := by
  simp [sampledTerminalCoord, extCoord, coordinateCompile, memoryCol0, extVar]

/-- If the three binding gates vanish on a base-field row environment, the gathered terminal
equals the gathered public. -/
theorem terminal_eq_requests_of_gates (b : Basis (Fin 3) F K) (envF : Env F)
    (h : ∀ k : Fin 3, (sampledTerminalCoord (F := F) k).eval envF = 0) :
    (gatherEnv b memoryCol0 envF).trace 40 = (gatherEnv b memoryCol0 envF).pub 2 := by
  have hz : (Expr.Sub (extVar .traceCur 40) (extVar .publicVal 2)).eval
      (gatherEnv b memoryCol0 envF) = 0 := by
    rw [coordinateCompile_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 envF)]
    intro k
    rw [← sampledTerminalCoord_is_binding b k]
    exact h k
  simpa [Expr.eval, extVar, sub_eq_zero] using hz

/-- The binding gates are members of the committed base transition bucket. -/
theorem sampledTerminalCoord_mem (b : Basis (Fin 3) F K) (k : Fin 3) :
    sampledTerminalCoord (F := F) k ∈ foldedBaseTransitionGates b := by
  fin_cases k <;> simp [foldedBaseTransitionGates, semanticBaseTail]

/-! ## B. At the consumed chip -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The source chip the consumed memory chip pads. -/
abbrev sourceOf : FixedPreprocessingRAP F :=
  namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

/-- The residual-column padding of the consumed chip. -/
abbrev extraOf : Fin (sourceOf P).rap.k → ℕ :=
  RAPPadding.firstRoundExtra (sourceOf P).rap (sourceOf P).rounds_pos
    (RAPPadding.memoryResidualColumns 3)

/-- The row environment of the projected trace at row `i`. -/
abbrev rowEnv (Q : Fin (sourceOf P).rap.w → F[X]) (i : Fin P.optimized.family.problem.cfg.memRows) :
    Env F :=
  envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
    P.optimized.memoryChallenge P.optimized.memoryPublic

/-- **For any accepted trace, at every row, the shared terminal role `40` equals the public
`requests`** — read off the source chip's language. -/
theorem terminal_bound_to_requests
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (gatherEnv P.optimized.basis memoryCol0
        (rowEnv P (RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm) i)).trace 40 =
      (gatherEnv P.optimized.basis memoryCol0
        (rowEnv P (RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm) i)).pub 2 := by
  have hsrc := (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem Qm).mp hsat
  set Q := RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm with hQ
  have hlang := expandChipTail_satisfies_iff_language (memorySourceTemplate P.optimized.basis)
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    (rowNodeSet P.optimized.memoryNodes) 2
  rw [memCol0_eq] at hlang
  have hraw : (expandChipTail (memorySourceTemplate P.optimized.basis) P.optimized.basis
      P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes) 2).Satisfies Q := hsrc.1
  erw [hlang] at hraw
  have hx : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  have hmix := (hraw _ hx).2.2.2
  have hterm : terminalRole (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
    simp [mixedTransitionGates, paperKGates, paperKGatesCore, ioCoreGates]
  have h := hmix _ hterm
  simp only [terminalRole, MixedExpr.eval, sub_eq_zero] at h
  change (gatherEnv P.optimized.basis memoryCol0
      (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
        P.optimized.memoryChallenge P.optimized.memoryPublic)).trace 40 =
    (gatherEnv P.optimized.basis memoryCol0
      (envOfTrace Q P.optimized.orbit.ω (P.optimized.memoryNodes i)
        P.optimized.memoryChallenge P.optimized.memoryPublic)).pub 2
  exact h

/-- The public `requests` gathered at a row is the package's `memoryPublic` block `12..14`. -/
theorem gathered_requests (Q : Fin (sourceOf P).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (gatherEnv P.optimized.basis memoryCol0 (rowEnv P Q i)).pub 2 =
      ∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k := by
  simp only [gatherEnv, memoryCol0, rowEnv, envOfTrace]

/-! ## C. Moving the terminal is rejected -/

/-- The three terminal columns: role `40`, columns `126..128`. -/
def IsTermCol (i : ℕ) : Prop := 126 ≤ i ∧ i < 129

instance (i : ℕ) : Decidable (IsTermCol i) := by unfold IsTermCol; infer_instance

/-- The coordinate a terminal column carries. -/
def termCoord (i : ℕ) : Fin 3 := ⟨(i - 126) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem termCoord_eq (k : Fin 3) : termCoord (126 + (k : ℕ)) = k := by
  apply Fin.ext; simp only [termCoord]; omega

/-- `Q` with the constant `c k` added to column `126 + k` (role `40`, coordinate `k`). -/
def bumpTerminal (c : Fin 3 → F) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun col => if IsTermCol (col : ℕ) then Q col + Polynomial.C (c (termCoord (col : ℕ))) else Q col

theorem bumpTerminal_eval (c : Fin 3 → F) {w : ℕ} (Q : Fin w → F[X]) (col : Fin w)
    (hc : IsTermCol (col : ℕ)) (x : F) :
    (bumpTerminal c Q col).eval x = (Q col).eval x + c (termCoord (col : ℕ)) := by
  simp [bumpTerminal, hc]

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- A nonzero `c` gathers to a nonzero `𝕂` value. -/
theorem gather_ne_zero (b : Basis (Fin 3) F K) (c : Fin 3 → F) (hc : c ≠ 0) :
    (∑ k, c k • b k) ≠ 0 := by
  intro h0
  apply hc
  funext k
  have := congrArg (fun x => coord b x k) h0
  simpa [coord_sum_smul, coord_zero] using this

/-- **A trace with the terminal moved by a nonzero constant is rejected.**  Since the accepted
trace's terminal equals `requests` at every row (`terminal_bound_to_requests`), the bumped one
would have to equal it too, while its gathered terminal is the original plus `Σ c_k b_k ≠ 0`. -/
theorem moved_terminal_rejected
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (c : Fin 3 → F) (hc : c ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip (bumpTerminal c Qm) := by
  intro hsat'
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have hrows := P.optimized.family.problem.cfg.memRows_pos
  set i₀ : Fin P.optimized.family.problem.cfg.memRows := ⟨0, hrows⟩ with hi₀
  have h1 := terminal_bound_to_requests P Qm hsat i₀
  have h2 := terminal_bound_to_requests P (bumpTerminal c Qm) hsat' i₀
  -- projecting commutes with the bump
  have hproj : RAPPadding.projectTrace (sourceOf P).rap (extraOf P)
      (bumpTerminal (w := P.memoryChip.rap.w) c Qm) =
      bumpTerminal c (RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm) := by
    funext col
    simp [RAPPadding.projectTrace, bumpTerminal, RAPPadding.columnInclusion] <;> rfl
  rw [hproj] at h2
  set Q := RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm with hQ
  -- the publics agree, the terminals differ by the gathered `c`
  rw [gathered_requests] at h1 h2
  have hshift : (gatherEnv P.optimized.basis memoryCol0 (rowEnv P (bumpTerminal c Q) i₀)).trace 40 =
      (gatherEnv P.optimized.basis memoryCol0 (rowEnv P Q i₀)).trace 40 +
        ∑ k, c k • P.optimized.basis k := by
    simp only [gatherEnv, memoryCol0]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : 6 + 3 * 40 + (k : ℕ) < (sourceOf P).rap.w := by rw [hw]; omega
    simp only [rowEnv, envOfTrace, dif_pos hlt]
    rw [bumpTerminal_eval c Q ⟨6 + 3 * 40 + (k : ℕ), hlt⟩
      (by show IsTermCol (6 + 3 * 40 + (k : ℕ)); unfold IsTermCol; omega)]
    rw [show termCoord (6 + 3 * 40 + (k : ℕ)) = k by
      apply Fin.ext; simp only [termCoord]; omega, add_smul]
  rw [hshift, h1] at h2
  exact gather_ne_zero P.optimized.basis c hc (by linear_combination h2)

/-- The honest trace is still accepted: the new pin is discharged by the package. -/
theorem canonical_trace_accepted [Fintype F] [DecidableEq F]
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) :=
  canonicalMemoryTrace_satisfies P hmore hC

end Deployed

end

end Nock.RedTeam.Batch268

#print axioms Nock.RedTeam.Batch268.terminal_eq_requests_of_gates
#print axioms Nock.RedTeam.Batch268.terminal_bound_to_requests
#print axioms Nock.RedTeam.Batch268.moved_terminal_rejected
#print axioms Nock.RedTeam.Batch268.canonical_trace_accepted
