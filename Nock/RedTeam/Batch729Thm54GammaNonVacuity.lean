/-
  Nock/RedTeam/Batch729Thm54GammaNonVacuity.lean

  Lane; notes only, no
  `passed` flip.

  This
  file hand-builds accepted memory rows at `γ ≠ 0`, `reqIdx ≠ 0` — exactly where the withdrawn
  `hexp0 : ∀ i, rowExpTerm = 0` is false (`Batch679.rowExpTerm_eq_zero_iff`).

  * **Rows.**  A three-row memory trace `read_root → verify_child → halt` (row 1 first and the
    forest root, `ver = 1`; row 2 its child; row 3 the `halt` leaf `(z, 0, atom)`, last).  The
    `read_root`/`verify_child` pair shares one record `(root N, child N, axis 1, ts t, C' Λ,
    reqIdx r)`, so the ten-slot `intermediate` pole cancels.
    Each row is a base environment in the deployed coordinate layout `6 + 3·role`
    (`memoryCol0`), every `𝕂` value in coordinate `0` (basis with `b 0 = 1`); the `𝕂` env is the
    production gather (`memorySourceEnvAt_eq_gather`).  The last row's successor `nx` is arbitrary.
  * **(a) gates.**  `RowLanguage b envF` is exactly `FamilyMemoryRows.row_parts_at`'s per-row
    conclusion (6 base + 50 mixed gates; equality and extension buckets empty), and every family-
    accepted row satisfies it (`rowLanguage_of_family`).  NOT claimed: `RAP.Satisfies` of a full
    polynomial trace at a package (no package is built; the receipt is per-row, at all three rows).
  * **(b) topology.**  The decoded labels (`lblEnv`/`decodePubEnv`, definitionally
    `ExecOfTraces.lblMAt`/`decodeMemPub`: `lblMAt_eq_env`, `decodeMemPub_eq_env`) satisfy the
    production `MemoryTopoBetaFree.FmemTopo` with the REAL child links (row 1's `lc` = row 2's
    `pt`; row 2's `lc` = row 3's `pt`).  `Batch490.hFcommit_memory` / `deployed_lblM_eqBlk` do not
    route: they take a package `P` and family-chip acceptance of a whole trace.
  * **(c) contrast.**  At both record rows `rowExpTermEnv = γ⁹·reqIdx ≠ 0` (definitionally
    `FamilyMemoryRows.rowExpTerm` at family envs, `rowExpTerm_eq_env`), and the paper's uniform-β
    `interV` (pole `RLC₉ − β`) is FALSE (`not_interV_row1/2`): the withdrawn statements were
    unsatisfiable on record rows whenever `γ ≠ 0`, while `FmemTopo` holds.
  * **Concrete** (`gamma_nonvacuity_K7`): `𝔽 = ZMod 7`, `𝕂 = GaloisField 7 3`, the compiler basis;
    `γ = 2`, `reqIdx = 1`, `γ⁹·reqIdx = 1`, pole `6` (uniform-β pole `5`), IO denominator `6`,
    `α_walk = 2`, `z = 3`, `atom = 5`, `ts = 2`, `λ = 2`, `Λ = λ^{pwScaleExp} = 4`.
-/
import Nock.RedTeam.Batch728Thm54MPrimeTopoReceipts
import Nock.RedTeam.Batch679Thm54ThirtyFirstReview
import Mathlib.FieldTheory.Finite.GaloisField
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch729

open Nock Nock.Reified Nock.MemoryTable Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree

noncomputable section

section Layout
variable {F : Type} [Field F]

/-- Coordinate-`0` layout `6 + 3·idx` (`memoryCol0`): role `idx` carries `v idx` in coordinate `0`
and `0` in coordinates `1, 2`. -/
def coordCol (v : ℕ → F) : ℕ → F := fun n =>
  if 6 ≤ n ∧ (n - 6) % 3 = 0 then v ((n - 6) / 3) else 0

/-- A hand-built memory row: the physical base columns (`0..5` selectors / masks, `153` rootMask,
`154` dequeueMask, `180` atom, `181` reqIdx) and coordinate `0` of every `𝕂` role. -/
structure Row (F : Type) where
  base : ℕ → F
  role : ℕ → F

def Row.col (R : Row F) : ℕ → F := fun n =>
  if n < 6 ∨ n = 153 ∨ n = 154 ∨ 180 ≤ n then R.base n else coordCol R.role n

/-- The base-field environment of row `cur` with successor `next`, challenges `chal` and
publics `pub` (all `𝕂` values in coordinate `0`). -/
def rowEnv (cur next : Row F) (chal pub : ℕ → F) : Env F :=
  ⟨cur.col, next.col, coordCol chal, coordCol pub⟩

end Layout

section Gather
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1)
include hb

theorem gather_coord (v : ℕ → F) (q : ℕ) :
    (∑ k : Fin 3, coordCol v (6 + 3 * q + (k : ℕ)) • b k) = algebraMap F K (v q) := by
  simp only [Fin.sum_univ_three, coordCol, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h0 : (6 ≤ 6 + 3 * q + 0 ∧ (6 + 3 * q + 0 - 6) % 3 = 0) := by omega
  have h1 : ¬ (6 ≤ 6 + 3 * q + 1 ∧ (6 + 3 * q + 1 - 6) % 3 = 0) := by omega
  have h2 : ¬ (6 ≤ 6 + 3 * q + 2 ∧ (6 + 3 * q + 2 - 6) % 3 = 0) := by omega
  have hq : (6 + 3 * q + 0 - 6) / 3 = q := by omega
  rw [if_pos h0, if_neg h1, if_neg h2, hq, hb]
  simp [Algebra.smul_def]

theorem gather_row (R : Row F) (r : ℕ) (hr : r ≠ 49) (hr2 : r < 58) :
    (∑ k : Fin 3, R.col (6 + 3 * r + (k : ℕ)) • b k) = algebraMap F K (R.role r) := by
  have : ∀ k : Fin 3, R.col (6 + 3 * r + (k : ℕ)) = coordCol R.role (6 + 3 * r + (k : ℕ)) := by
    intro k
    have hk := k.isLt
    unfold Row.col
    rw [if_neg (by omega)]
  simp_rw [this]
  exact gather_coord b hb R.role r

@[simp] theorem gtrace (cur next : Row F) (chal pub : ℕ → F) (r : ℕ) (hr : r ≠ 49) (hr2 : r < 58) :
    (gatherEnv b memoryCol0 (rowEnv cur next chal pub)).trace r = algebraMap F K (cur.role r) :=
  gather_row b hb cur r hr hr2

@[simp] theorem gnext (cur next : Row F) (chal pub : ℕ → F) (r : ℕ) (hr : r ≠ 49) (hr2 : r < 58) :
    (gatherEnv b memoryCol0 (rowEnv cur next chal pub)).traceNext r =
      algebraMap F K (next.role r) :=
  gather_row b hb next r hr hr2

@[simp] theorem gchal (cur next : Row F) (chal pub : ℕ → F) (q : ℕ) :
    (gatherEnv b memoryCol0 (rowEnv cur next chal pub)).chal q = algebraMap F K (chal q) :=
  gather_coord b hb chal q

@[simp] theorem gpub (cur next : Row F) (chal pub : ℕ → F) (q : ℕ) :
    (gatherEnv b memoryCol0 (rowEnv cur next chal pub)).pub q = algebraMap F K (pub q) :=
  gather_coord b hb pub q

end Gather

section Base
variable {F : Type} [Field F]

@[simp] theorem rowEnv_trace (cur next : Row F) (chal pub : ℕ → F) (n : ℕ) :
    (rowEnv cur next chal pub).trace n = cur.col n := rfl

@[simp] theorem rowEnv_traceNext (cur next : Row F) (chal pub : ℕ → F) (n : ℕ) :
    (rowEnv cur next chal pub).traceNext n = next.col n := rfl

/-- Finite table: `pick l n` is the value listed for `n`, else `0`. -/
def pick : List (ℕ × F) → ℕ → F
  | [], _ => 0
  | (k, v) :: rest, n => if n = k then v else pick rest n

end Base

section Rows
variable {F : Type} [Field F]

structure Params (F : Type) where
  z : F
  a : F
  t : F
  r : F
  α : F
  γ : F
  io : F
  ip : F
  wγ : F
  l : F
  Λ : F

variable (p : Params F)

/-- The nine-slot record RLC of the shared record `(root N, child N, axis 1, ts t, C' Λ)`,
`N = (z, 0, a)`. -/
def recF : F :=
  p.z + p.γ * 0 + p.γ ^ 2 * p.a + p.γ ^ 3 * p.z + p.γ ^ 4 * 0 + p.γ ^ 5 * p.a + p.γ ^ 6 * 1 +
    p.γ ^ 7 * p.t + p.γ ^ 8 * p.Λ

/-- The ten-slot `intermediate` pole `interPole + RLC₉ + γ⁹·reqIdx` at the record rows. -/
def poleF : F := p.ip + recF p + p.γ ^ 9 * p.r

/-- The IO response denominator `ioPole + RLC₉ + γ⁹·reqIdx` at the record rows. -/
def denF : F := p.io + recF p + p.γ ^ 9 * p.r

/-- Walk label RLC of the `verify_child` row and of the `halt` row. -/
def L2 : F := 3 + p.wγ * p.z + p.wγ ^ 2 * 0 + p.wγ ^ 3 * p.a + p.wγ ^ 4 * (p.Λ * p.t) +
  p.wγ ^ 5 * (p.Λ * p.t)
def L3 : F := 1 + p.wγ * p.z + p.wγ ^ 2 * 0 + p.wγ ^ 3 * p.a + p.wγ ^ 4 * 0 + p.wγ ^ 5 * 0

/-- Row 1: `read_root`, first row, forest root (`rootMask = 1`), `ver = 1`, `reqIdx = r`. -/
def row1 : Row F where
  base := pick [(2, 1), (4, 1), (153, 1), (154, 1), (181, p.r)]
  role := pick [(0, p.z), (2, p.a), (5, p.z), (7, p.a), (8, p.Λ * p.t), (9, p.Λ * p.t),
    (17, 1), (19, p.z), (21, p.a), (22, p.z), (24, p.a), (25, 1), (26, p.t),
    (28, (poleF p)⁻¹), (29, (poleF p)⁻¹), (31, p.α), (32, p.α ^ 2), (33, p.α ^ 2 * L2 p),
    (37, denF p), (38, (denF p)⁻¹), (39, 1), (40, (denF p)⁻¹), (42, (denF p)⁻¹), (45, 3),
    (47, 1), (50, denF p), (53, 1), (55, (p.α ^ 2 - p.α)⁻¹), (56, 1), (57, p.Λ)]

/-- Row 2: `verify_child`, the child of row 1, same record, `reqIdx = r`. -/
def row2 : Row F where
  base := pick [(3, 1), (154, 1), (181, p.r)]
  role := pick [(0, p.z), (2, p.a), (3, p.Λ * p.t), (4, p.Λ * p.t), (5, p.z), (7, p.a),
    (18, 1), (19, p.z), (21, p.a), (22, p.z), (24, p.a), (25, 1), (26, p.t),
    (27, (poleF p)⁻¹), (29, (poleF p)⁻¹), (31, p.α ^ 2), (32, p.α ^ 3), (33, p.α ^ 3 * L3 p),
    (37, denF p), (38, 1), (40, (denF p)⁻¹), (43, (denF p)⁻¹), (45, 1), (50, 1), (54, 1),
    (55, (p.α ^ 3 - p.α ^ 2)⁻¹), (56, 1), (57, p.Λ)]

/-- Row 3: `halt` leaf `(z, 0, a)`, last row, `atom = a`. -/
def row3 : Row F where
  base := pick [(1, 1), (5, 1), (180, p.a)]
  role := pick [(0, p.z), (2, p.a), (31, p.α ^ 3), (32, p.α ^ 3), (37, p.io), (38, 1),
    (40, (denF p)⁻¹), (43, (denF p)⁻¹), (48, 1), (50, 1), (52, 1)]

/-- Memory `𝕂` challenge slots (coordinate `0`): `0 = z`, `3 = α_walk`, `4 = γ`, `5 = ioPole`,
`6 = interPole`, `7 = walk γ`, `8 = λ`. -/
def chalV : ℕ → F := pick [(0, p.z), (3, p.α), (4, p.γ), (5, p.io), (6, p.ip), (7, p.wγ), (8, p.l)]

/-- Memory publics: `0 = initial_count = α^{kMem}` (`kMem = 1`), `2 = requests`. -/
def pubV : ℕ → F := pick [(0, p.α), (2, (denF p)⁻¹)]

def env1 : Env F := rowEnv (row1 p) (row2 p) (chalV p) (pubV p)
def env2 : Env F := rowEnv (row2 p) (row3 p) (chalV p) (pubV p)
def env3 (nx : Row F) : Env F := rowEnv (row3 p) nx (chalV p) (pubV p)

end Rows

set_option hygiene false in
/-- The gate-evaluation unfolding set (gathered `𝕂` env through `gtrace`/`gnext`/`gchal`/`gpub`). -/
macro "mem_eval" : tactic => `(tactic| simp [pick, Row.col, coordCol, gtrace b hb, gnext b hb,
    gchal b hb, gpub b hb, OptimizedMemoryGateBasis.rootMaskCol,
    MemoryWalkLabel.rootMaskCol, OptimizedMemoryGateBasis.dequeueMaskCol, MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, CoeffExpr.eval, Expr.subst, memorySubst,
    walkSubst, walkBoundarySubst, paperClassGate, selScale, MemoryFactorizationScope.memQuantity,
    MemoryFactorizationScope.paddedBlock, MemoryFactorizationScope.blockReadRoot,
    MemoryFactorizationScope.blockVerifyChild, MemoryFactorizationScope.blockHalt,
    MemoryFactorizationScope.blockDecompose, MemoryFactorizationScope.lamScaleE,
    MemoryFactorizationScope.lamE, MemoryFactorizationScope.recC',
    mPt, mLc, mRc, mMem, mrCol, fpCol, tc, chl, Trans.tn, extVar, consDyckQuantity, paperConsDyck,
    timestampGate, paperAggregator, poleSourceMixed, poleSource, recordRLCExpr, reqIdxRLCTerm,
    reqIdxCol, bcur, intermediateChain, chainMixed, walkTerminal, OptimizedMemoryGateBasis.verBool, safeNormalisation,
    safeInverse, contribution, denominatorPin, denominatorPinMixed, recordRLC, accStep, accInit,
    accTerminal, terminalRole, intermediateInit, intermediateTerminal, rootMaskCountsGate,
    rootMaskPwGate, rootMask, haltAtomMixed, haltSel, atomCol,
    MemoryWalkLabel.walkCount1InGate, MemoryWalkLabel.walkAccInitInGate,
    MemoryWalkLabel.walkCountStepInGate, MemoryWalkLabel.walkAccStepInGate,
    MemoryWalkLabel.walkQueueNonEmpty, MemoryWalkLabel.walkQueueTiling,
    MemoryWalkLabel.firstMaskBase, MemoryWalkLabel.lastMaskBase, MemoryWalkLabel.notLastBase,
    MemoryWalkLabel.lnCur, MemoryWalkLabel.lnNext, MemoryWalkLabel.countCur,
    MemoryWalkLabel.countNext, MemoryWalkLabel.accCur, MemoryWalkLabel.accNext,
    MemoryWalkLabel.walkInvCur, MemoryWalkLabel.initialCountPub,
    MemoryWalkLabel.dequeueMaskCur, MemoryWalkLabel.selectorCM, MemoryWalkLabel.selSum,
    MemoryWalkLabel.cmAt, MemoryWalkLabel.childSumCC, MemoryWalkLabel.childSumAt,
    MemoryWalkLabel.childInnerSum, MemoryWalkLabel.childRLCAt, MemoryWalkLabel.childCoordAt,
    MemoryWalkLabel.childTagHost, MemoryWalkLabel.childTagHostRole, MemoryWalkLabel.cellBase,
    MemoryWalkLabel.labelRLC, MemoryWalkLabel.labelRLCAt, MemoryWalkLabel.labelCoordAt,
    MemoryWalkLabel.stateTagExpr, MemoryWalkLabel.rlcExpr, MemoryWalkLabel.walkGammaChallenge,
    MemoryWalkLabel.walkGammaChallengeIndex, MemoryWalkLabel.walkAlphaChallenge,
    MemoryWalkLabel.walkAlphaChallengeIndex, MemoryWalkLabel.curReader,
    MemoryWalkLabel.nextReader, MemoryWalkLabel.lnRole, MemoryWalkLabel.countRole,
    MemoryWalkLabel.accRole, MemoryWalkLabel.walkInvRole, MemoryWalkLabel.dequeueMaskCol,
    Trans.walkLn1, Trans.walkLnStep, allMStates, mopCol, fanoutMem,
    NodeEncoding.memoryStateTag, List.ofFn_succ, Fin.sum_univ_three])

set_option hygiene false in
/-- Close the field identities left by `mem_eval` (denominators by `field_simp`, then `ring`). -/
macro "mem_close" : tactic => `(tactic| (
  try simp only [hΛK]
  try simp only [inv_mul_cancel₀ hA2, sub_self]
  try simp only [inv_mul_cancel₀ hA3, sub_self]
  try field_simp
  try simp only [poleF, denF, recF, L2, L3, map_add, map_mul, map_pow, map_sub, map_one,
    map_zero, map_ofNat, mul_zero, zero_mul, add_zero, mul_one]
  try ring_nf))

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1) (p : Params F)

include hb in
theorem coord_one_zero : CoordinateBasis.coord b (1 : K) 0 = 1 := by
  rw [← hb]; simp [CoordinateBasis.coord]

include hb in
theorem base_row1 : ∀ g ∈ baseTransitionGates b, g.eval (env1 p) = 0 := by
  intro g hg
  simp only [baseTransitionGates, paperBaseGates, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | rfl <;>
    simp [env1, readRootVerGate, bbool, bsum4, bcur, extCoord, CoeffExpr.eval, row1, Row.col,
      coordCol, pick, coord_one_zero b hb]

include hb in
theorem mixed_row1_raw
    (hPK : algebraMap F K (poleF p) ≠ 0) (hDK : algebraMap F K (denF p) ≠ 0)
    (hA2 : algebraMap F K p.α ^ 2 - algebraMap F K p.α ≠ 0)
    (hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
      g.eval (gatherEnv b memoryCol0 (env1 p)) (env1 p) = 0 := by
  simp only [mixedTransitionGates, paperKGates, paperKGatesCore, rapMemGates, tabVMemGates,
    tabVMemClassIndices, baseTypedClassGates, baseTypedClassIndices, bottomPins,
    bottomPinIndices, walkGates, walkInitGates, walkStepGates, ioCoreGates, paperEndpointGates,
    MemoryWalkLabel.queueWitnessGates, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_assoc, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals simp only [env1, row1, row2, chalV, pubV]
  all_goals mem_eval
  all_goals mem_close

include hb in
theorem mixed_row2_raw
    (hPK : algebraMap F K (poleF p) ≠ 0)
    (hA3 : algebraMap F K p.α ^ 3 - algebraMap F K p.α ^ 2 ≠ 0)
    (hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
      g.eval (gatherEnv b memoryCol0 (env2 p)) (env2 p) = 0 := by
  simp only [mixedTransitionGates, paperKGates, paperKGatesCore, rapMemGates, tabVMemGates,
    tabVMemClassIndices, baseTypedClassGates, baseTypedClassIndices, bottomPins,
    bottomPinIndices, walkGates, walkInitGates, walkStepGates, ioCoreGates, paperEndpointGates,
    MemoryWalkLabel.queueWitnessGates, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_assoc, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals simp only [env2, row2, row3, chalV, pubV]
  all_goals mem_eval
  all_goals mem_close

include hb in
theorem mixed_row3_raw (nx : Row F) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
      g.eval (gatherEnv b memoryCol0 (env3 p nx)) (env3 p nx) = 0 := by
  simp only [mixedTransitionGates, paperKGates, paperKGatesCore, rapMemGates, tabVMemGates,
    tabVMemClassIndices, baseTypedClassGates, baseTypedClassIndices, bottomPins,
    bottomPinIndices, walkGates, walkInitGates, walkStepGates, ioCoreGates, paperEndpointGates,
    MemoryWalkLabel.queueWitnessGates, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_assoc, List.forall_mem_cons, List.forall_mem_nil, and_true]
  and_intros
  all_goals simp only [env3, row3, chalV, pubV]
  all_goals mem_eval

theorem base_row2 : ∀ g ∈ baseTransitionGates b, g.eval (env2 p) = 0 := by
  intro g hg
  simp only [baseTransitionGates, paperBaseGates, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | rfl <;>
    simp [env2, readRootVerGate, bbool, bsum4, bcur, extCoord, CoeffExpr.eval, row2, Row.col,
      coordCol, pick]

theorem base_row3 (nx : Row F) : ∀ g ∈ baseTransitionGates b, g.eval (env3 p nx) = 0 := by
  intro g hg
  simp only [baseTransitionGates, paperBaseGates, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl) | rfl <;>
    simp [env3, readRootVerGate, bbool, bsum4, bcur, extCoord, CoeffExpr.eval, row3, Row.col,
      coordCol, pick]

end Gates

/-! ## Labels: the production decode, re-stated on an environment pair -/

section Decode
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq K]

/-- `ExecOfTraces.decodeMemPub`'s body on an explicit `(envF, envK)` pair. -/
def decodePubEnv (envF : Env F) (envK : Env K) : MemoryTable.Pub K :=
  let st := StrategyOfTraces.memoryStateOf envF
  { st := st
    pt := ⟨StrategyOfTraces.memoryPtNoun envK, envK.trace 3, envK.trace 4⟩
    lc := ⟨⟨envK.trace 5, envK.trace 6, envK.trace 7⟩, envK.trace 8, envK.trace 9⟩
    rc := ⟨⟨envK.trace 10, envK.trace 11, envK.trace 12⟩, envK.trace 13, envK.trace 14⟩
    lcSt :=
      match st with
      | .read_root | .verify_child => st
      | _ => .halt
    rcSt := .halt
    mem := ⟨StrategyOfTraces.memoryMemRoot envK, StrategyOfTraces.memoryMemChild envK,
      envK.trace 25, envK.trace 26⟩
    ipre := envK.trace 27
    icur := envK.trace 28
    ver := decide (envK.trace 39 = 1)
    cprime? := some (envK.trace 57)
    lambda? := some (envK.chal 8) }

/-- `ExecOfTraces.lblMAt`'s body: inputs `(z, β = −interPole, γ)` and the decoded public. -/
def lblEnv (z β γ : K) (envF : Env F) (envK : Env K) : MState × DTmem K :=
  (StrategyOfTraces.memoryStateOf envF, ({ z := z, β := β, γ := γ }, decodePubEnv envF envK))

/-- The environment-level contrast quantity: `FamilyMemoryRows.rowExpTerm`'s body. -/
def rowExpTermEnv (envF : Env F) (γ : K) : K :=
  algebraMap F K (envF.trace OptimizedMemoryGateBasis.reqIdxCol) * γ ^ 9

variable [Fintype F] [Fintype K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
  (Qm : Fin P.memoryChip.rap.w → Polynomial F)
  (i : Fin P.optimized.family.problem.cfg.memRows)

/-- **Production link (decode).**  The deployed decode is `decodePubEnv` at the family envs. -/
theorem decodeMemPub_eq_env :
    ExecOfTraces.decodeMemPub P Qm c i =
      decodePubEnv (FamilyComputeRows.memoryBaseEnvAt P c Qm i)
        (FamilyComputeRows.memorySourceEnvAt P c Qm i) := rfl

/-- **Production link (label).**  `lblMAt` is `lblEnv` at `(nprSeed, −interPole, γ)`. -/
theorem lblMAt_eq_env :
    ExecOfTraces.lblMAt P Qm c i =
      lblEnv (nprSeed c.1) (-(c.2.2.2.interPole)) c.2.1.1
        (FamilyComputeRows.memoryBaseEnvAt P c Qm i)
        (FamilyComputeRows.memorySourceEnvAt P c Qm i) := rfl

/-- **Production link (family env).**  The family `𝕂` env is the gather at `memoryCol0`. -/
theorem memorySourceEnvAt_eq_gather :
    FamilyComputeRows.memorySourceEnvAt P c Qm i =
      gatherEnv P.optimized.basis memoryCol0 (FamilyComputeRows.memoryBaseEnvAt P c Qm i) := rfl

/-- **Production link (contrast).**  The withdrawn `hexp0`'s quantity is `rowExpTermEnv` at the
family envs, read at the env's own `γ` slot. -/
theorem rowExpTerm_eq_env :
    FamilyMemoryRows.rowExpTerm P c Qm i =
      rowExpTermEnv (FamilyComputeRows.memoryBaseEnvAt P c Qm i)
        ((FamilyComputeRows.memorySourceEnvAt P c Qm i).chal 4) := by
  rw [HostilePoleAlignment.memorySourceEnvAt_chal4]; rfl

end Decode

/-! ## (b) `FmemTopo` on the decoded labels, with the real child links -/

set_option hygiene false in
/-- `FmemTopo` at a hand-built label: state, `eqBlk`, fanout, child link. -/
macro "topo_tac" : tactic => `(tactic| (
  refine ⟨rfl, ?_, ?_, ?_⟩
  · mem_eval
    all_goals simp [decodePubEnv, StrategyOfTraces.memoryStateOf, StrategyOfTraces.memoryPtNoun,
      StrategyOfTraces.memoryMemRoot, StrategyOfTraces.memoryMemChild, eqBlk, Pub.lambda,
      Pub.cprime, Cell.zero, ComputeTable.MemRec.zero, pick, Row.col, coordCol, gtrace b hb,
      gchal b hb, hΛK]
    all_goals rfl
  · simp only [Fin.forall_fin_two]
    simp [StrategyOfTraces.memoryStateOf, fanoutMem, pick, Row.col, coordCol]
  · simp only [childLinkMem, Fin.forall_fin_two]
    simp [one, StrategyOfTraces.memoryStateOf, fanoutMem, childLinkMem, memCell, decodePubEnv,
      StrategyOfTraces.memoryPtNoun, pick, Row.col, coordCol, gtrace b hb, gchal b hb]))

section Topo
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K]
  (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1) (p : Params F)

/-- The decoded label of a hand-built row, exactly as `lblMAt` decodes a family row
(`lblMAt_eq_env`): `z` = slot 0, `β = −interPole`, `γ` = slot 4. -/
def lab (envF : Env F) : MState × DTmem K :=
  lblEnv (algebraMap F K p.z) (-(algebraMap F K p.ip)) (algebraMap F K p.γ) envF
    (gatherEnv b memoryCol0 envF)

/-- Child vector: one child `c` in slot `0` (fanout `1`), or none. -/
def one (c : MState × DTmem K) : Fin 2 → Option (MState × DTmem K) :=
  fun j => if (j : ℕ) = 0 then some c else none

include hb in
theorem topo_row1 (hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ) :
    FmemTopo (lab b p (env1 p)) (one (lab b p (env2 p))) := by
  simp only [FmemTopo, lab, lblEnv, one, env1, env2, row1, row2, chalV, pubV]
  topo_tac

include hb in
theorem topo_row2 (hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ) :
    FmemTopo (lab b p (env2 p)) (one (lab b p (env3 p (row3 p)))) := by
  simp only [FmemTopo, lab, lblEnv, one, env2, env3, row2, row3, chalV, pubV]
  topo_tac

set_option linter.unusedVariables false in
include hb in
theorem topo_row3 (nx : Row F) (hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ) :
    FmemTopo (lab b p (env3 p nx)) (fun _ => none) := by
  simp only [FmemTopo, lab, lblEnv, env3, row3, chalV, pubV]
  topo_tac

end Topo

/-! ## (c) Contrast: the withdrawn `hexp0` is false here, and so is the uniform-β `interV` -/

section Contrast
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K]
  (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1) (p : Params F)

include hb in
theorem rowExpTerm_row1 :
    rowExpTermEnv (env1 p) ((gatherEnv b memoryCol0 (env1 p)).chal 4) =
      algebraMap F K (p.r * p.γ ^ 9) := by
  simp [rowExpTermEnv, env1, row1, row2, chalV, pubV, reqIdxCol, pick, Row.col, coordCol,
    gchal b hb]

include hb in
theorem rowExpTerm_row2 :
    rowExpTermEnv (env2 p) ((gatherEnv b memoryCol0 (env2 p)).chal 4) =
      algebraMap F K (p.r * p.γ ^ 9) := by
  simp [rowExpTermEnv, env2, row2, row3, chalV, pubV, reqIdxCol, pick, Row.col, coordCol,
    gchal b hb]

theorem poleSourceMixed_eval_env (envK : Env K) (envF : Env F) :
    (MemoryPaperFactorization.poleSourceMixed (F := F)).eval envK envF =
      MemoryPaperFactorization.poleSource.eval envK + rowExpTermEnv envF (envK.chal 4) := by
  simp only [MemoryPaperFactorization.poleSourceMixed, MixedExpr.eval, MixedExpr.ofExpr_eval,
    reqIdxRLCTerm, bcur, CoeffExpr.eval, rowExpTermEnv]

include hb in
/-- At the accepted `read_root` row the paper's uniform-β `interV` (pole `RLC₉ − β`,
`β = −interPole`) FAILS whenever `γ⁹·reqIdx ≠ 0`: the chip's ten-slot pole differs from it by
exactly that term.  (This is what "unsatisfiable on record rows whenever γ ≠ 0" means.) -/
theorem not_interV_row1 (hne : p.r * p.γ ^ 9 ≠ 0) :
    ¬ interV (lab b p (env1 p)).2.1 (lab b p (env1 p)).2.2 := by
  intro h
  simp [interV, lab, lblEnv, decodePubEnv, StrategyOfTraces.memoryStateOf, pole, recRLC,
    Pub.cprime, StrategyOfTraces.memoryMemRoot, StrategyOfTraces.memoryMemChild, env1, row1, row2,
    chalV, pubV, pick, Row.col, coordCol, gtrace b hb, gchal b hb] at h
  have h' := h
  apply hne
  apply (algebraMap F K).injective
  simp only [poleF, recF, map_add, map_mul, map_pow, map_one, map_zero, mul_zero, add_zero,
    mul_one, map_neg] at h' ⊢
  linear_combination h'

include hb in
/-- Same at the `verify_child` row (`ipre − icur = pole⁻¹`). -/
theorem not_interV_row2 (hne : p.r * p.γ ^ 9 ≠ 0) :
    ¬ interV (lab b p (env2 p)).2.1 (lab b p (env2 p)).2.2 := by
  intro h
  simp [interV, lab, lblEnv, decodePubEnv, StrategyOfTraces.memoryStateOf, pole, recRLC,
    Pub.cprime, StrategyOfTraces.memoryMemRoot, StrategyOfTraces.memoryMemChild, env2, row2, row3,
    chalV, pubV, pick, Row.col, coordCol, gtrace b hb, gchal b hb] at h
  have h' := h
  apply hne
  apply (algebraMap F K).injective
  simp only [poleF, recF, map_add, map_mul, map_pow, map_one, map_zero, mul_zero, add_zero,
    mul_one, map_neg] at h' ⊢
  linear_combination h'

end Contrast

/-! ## (a) The per-row language of the deployed memory chip, and the assembled receipt -/

section Assembled
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The deployed memory chip's per-row obligations at a base environment: exactly the four
conjuncts of `FamilyMemoryRows.row_parts_at` (base, equality, extension, mixed), with the `𝕂` env
the gather at the template's layout. -/
def RowLanguage (b : Module.Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ baseTransitionGates b, g.eval envF = 0) ∧
    (∀ g ∈ equalityChecks b, g.eval envF = 0) ∧
    (∀ g ∈ (memorySourceTemplate b).extTransition ++ (memorySourceTemplate b).extDeg1 ++
        (memorySourceTemplate b).extDeg3,
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0) ∧
    (∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
      g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0)

/-- **Production link (acceptance).**  Every row of a trace the family chip accepts satisfies
`RowLanguage` at its family base env (`row_parts_at`, unchanged). -/
theorem rowLanguage_of_family [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] {hOrb : ℕ}
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → Polynomial F)
    (hsat : Nock.Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    RowLanguage P.optimized.basis
      (FamilyComputeRows.memoryBaseEnvAt P c (FamilyMemoryRows.honestQm P c Qm) i) :=
  FamilyMemoryRows.row_parts_at P c Qm hsat i

/-- The equality and extension buckets are empty, so `RowLanguage` is base ∧ mixed. -/
theorem rowLanguage_of_base_mixed (b : Module.Basis (Fin 3) F K) (envF : Env F)
    (hbase : ∀ g ∈ baseTransitionGates b, g.eval envF = 0)
    (hmixed : ∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
      g.eval (gatherEnv b memoryCol0 envF) envF = 0) :
    RowLanguage b envF := by
  obtain ⟨-, -, -, hx, h1, h3, -⟩ := memorySourceTemplate_shape b
  refine ⟨hbase, by simp [equalityChecks], ?_, hmixed⟩
  rw [List.eq_nil_of_length_eq_zero hx, List.eq_nil_of_length_eq_zero h1,
    List.eq_nil_of_length_eq_zero h3]
  simp

variable [DecidableEq F] [DecidableEq K] (b : Module.Basis (Fin 3) F K) (hb : b 0 = 1)
  (p : Params F)

include hb in
/-- **Γ ≠ 0 non-vacuity receipt for `FmemTopo` (generic form).**  A hand-built
three-row memory trace `read_root → verify_child → halt` (read row first and a forest root,
halt row last; the last row's successor `nx` arbitrary): every row satisfies the deployed memory
chip's full per-row language (6 base + 50 mixed gates; equality/extension buckets empty);
the decoded labels satisfy the production `FmemTopo` with the REAL child links (row 1's `lc` is
row 2's `pt`, row 2's `lc` is row 3's `pt`); and at both record rows the withdrawn `hexp0`
quantity `rowExpTerm = γ⁹·reqIdx` is nonzero and the paper's uniform-β `interV` fails. -/
theorem gamma_nonvacuity
    (hα0 : p.α ≠ 0) (hα1 : p.α ≠ 1) (hP : poleF p ≠ 0) (hD : denF p ≠ 0)
    (hΛ : p.Λ = p.l ^ pwScaleExp K) (hγ : p.γ ≠ 0) (hr : p.r ≠ 0) (nx : Row F) :
    (RowLanguage b (env1 p) ∧ RowLanguage b (env2 p) ∧ RowLanguage b (env3 p nx)) ∧
    (FmemTopo (lab b p (env1 p)) (one (lab b p (env2 p))) ∧
      FmemTopo (lab b p (env2 p)) (one (lab b p (env3 p (row3 p)))) ∧
      FmemTopo (lab b p (env3 p nx)) (fun _ => none)) ∧
    (rowExpTermEnv (env1 p) ((gatherEnv b memoryCol0 (env1 p)).chal 4) ≠ 0 ∧
      rowExpTermEnv (env2 p) ((gatherEnv b memoryCol0 (env2 p)).chal 4) ≠ 0) ∧
    (¬ interV (lab b p (env1 p)).2.1 (lab b p (env1 p)).2.2 ∧
      ¬ interV (lab b p (env2 p)).2.1 (lab b p (env2 p)).2.2) := by
  have hinj := (algebraMap F K).injective
  have hPK : algebraMap F K (poleF p) ≠ 0 := (map_ne_zero _).2 hP
  have hDK : algebraMap F K (denF p) ≠ 0 := (map_ne_zero _).2 hD
  have hα10 : p.α - 1 ≠ 0 := sub_ne_zero.2 hα1
  have hA2 : algebraMap F K p.α ^ 2 - algebraMap F K p.α ≠ 0 := by
    rw [← map_pow, ← map_sub, map_ne_zero]
    have : p.α ^ 2 - p.α = p.α * (p.α - 1) := by ring
    rw [this]; exact mul_ne_zero hα0 hα10
  have hA3 : algebraMap F K p.α ^ 3 - algebraMap F K p.α ^ 2 ≠ 0 := by
    rw [← map_pow, ← map_pow, ← map_sub, map_ne_zero]
    have : p.α ^ 3 - p.α ^ 2 = p.α ^ 2 * (p.α - 1) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hα0) hα10
  have hΛK : algebraMap F K p.l ^ pwScaleExp K = algebraMap F K p.Λ := by rw [hΛ, map_pow]
  have hne : p.r * p.γ ^ 9 ≠ 0 := mul_ne_zero hr (pow_ne_zero _ hγ)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨topo_row1 b hb p hΛK, topo_row2 b hb p hΛK, topo_row3 b hb p nx hΛK⟩,
    ⟨?_, ?_⟩, ⟨not_interV_row1 b hb p hne, not_interV_row2 b hb p hne⟩⟩
  · exact rowLanguage_of_base_mixed b _ (base_row1 b hb p) (mixed_row1_raw b hb p hPK hDK hA2 hΛK)
  · exact rowLanguage_of_base_mixed b _ (base_row2 b p) (mixed_row2_raw b hb p hPK hA3 hΛK)
  · exact rowLanguage_of_base_mixed b _ (base_row3 b p nx) (mixed_row3_raw b hb p nx)
  · rw [rowExpTerm_row1 b hb p, map_ne_zero]; exact hne
  · rw [rowExpTerm_row2 b hb p, map_ne_zero]; exact hne

end Assembled

/-! ## The concrete instance: `𝔽 = ZMod 7`, `𝕂 = GaloisField 7 3`, compiler basis -/

section Concrete

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Concrete parameters: `z = 3`, `atom = 5`, `ts = 2`, **`reqIdx = 1`**, `α_walk = 2`,
**`γ = 2`**, `ioPole = 1`, `interPole = 1`, walk `γ = 3`, `λ = 2`, `Λ = λ² = 4`. -/
def p7 : Params (ZMod 7) where
  z := 3
  a := 5
  t := 2
  r := 1
  α := 2
  γ := 2
  io := 1
  ip := 1
  wγ := 3
  l := 2
  Λ := 4

abbrev K7 : Type := GaloisField 7 3

noncomputable instance : Fintype K7 := Fintype.ofFinite _
noncomputable instance : DecidableEq K7 := Classical.decEq _
instance : CharP K7 (ringChar K7) := ringChar.charP K7

theorem finrank_K7 : Module.finrank (ZMod 7) K7 = 3 := GaloisField.finrank 7 (by norm_num)

noncomputable abbrev b7 : Module.Basis (Fin 3) (ZMod 7) K7 :=
  TraceGen.compilerBasis finrank_K7

theorem b7_zero : b7 0 = 1 := TraceGen.compilerBasis_zero finrank_K7

theorem pwScaleExp_K7 : pwScaleExp K7 = 2 := by
  haveI : CharP K7 7 := charP_of_injective_algebraMap (algebraMap (ZMod 7) K7).injective 7
  rw [pwScaleExp, ringChar.eq K7 7]
  decide

/-- The concrete pole values: ten-slot `intermediate` pole `6`, IO denominator `6`,
`γ⁹·reqIdx = 1` (so the uniform-β pole would be `5`). -/
theorem p7_values : poleF p7 = 6 ∧ denF p7 = 6 ∧ p7.r * p7.γ ^ 9 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The concrete receipt** at `γ = 2 ≠ 0`, `reqIdx = 1 ≠ 0` over `ZMod 7` /
`GaloisField 7 3` with the compiler basis. -/
theorem gamma_nonvacuity_K7 (nx : Row (ZMod 7)) :
    (RowLanguage b7 (env1 p7) ∧ RowLanguage b7 (env2 p7) ∧ RowLanguage b7 (env3 p7 nx)) ∧
    (FmemTopo (lab b7 p7 (env1 p7)) (one (lab b7 p7 (env2 p7))) ∧
      FmemTopo (lab b7 p7 (env2 p7)) (one (lab b7 p7 (env3 p7 (row3 p7)))) ∧
      FmemTopo (lab b7 p7 (env3 p7 nx)) (fun _ => none)) ∧
    (rowExpTermEnv (env1 p7) ((gatherEnv b7 memoryCol0 (env1 p7)).chal 4) ≠ 0 ∧
      rowExpTermEnv (env2 p7) ((gatherEnv b7 memoryCol0 (env2 p7)).chal 4) ≠ 0) ∧
    (¬ interV (lab b7 p7 (env1 p7)).2.1 (lab b7 p7 (env1 p7)).2.2 ∧
      ¬ interV (lab b7 p7 (env2 p7)).2.1 (lab b7 p7 (env2 p7)).2.2) := by
  refine gamma_nonvacuity b7 b7_zero p7 (by decide) (by decide) (by decide) (by decide)
    ?_ (by decide) (by decide) nx
  rw [pwScaleExp_K7]; decide

/-- The concrete `γ` of the receipt is the family env's slot-4 value, and it is nonzero. -/
theorem gamma_K7 : (gatherEnv b7 memoryCol0 (env1 p7)).chal 4 = algebraMap (ZMod 7) K7 2 ∧
    algebraMap (ZMod 7) K7 2 ≠ 0 := by
  refine ⟨gchal b7 b7_zero _ _ _ _ 4, ?_⟩
  rw [map_ne_zero]; decide

end Concrete

end

end Nock.RedTeam.Batch729

#print axioms Nock.RedTeam.Batch729.gamma_nonvacuity
#print axioms Nock.RedTeam.Batch729.gamma_nonvacuity_K7
#print axioms Nock.RedTeam.Batch729.gamma_K7
#print axioms Nock.RedTeam.Batch729.rowLanguage_of_family
#print axioms Nock.RedTeam.Batch729.lblMAt_eq_env
#print axioms Nock.RedTeam.Batch729.rowExpTerm_eq_env
