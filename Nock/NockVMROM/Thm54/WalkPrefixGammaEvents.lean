/-
  Nock/NockVMROM/Thm54/WalkPrefixGammaEvents.lean

  The prefix-route whole-table γ-collision events,
  read off committed node vectors.  Both Finsets
  are functions of the TRACE (the node / child / fanout columns) and of no coin.
-/
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.MemoryWalkLabel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.WalkPrefixGammaEvents

open scoped Classical
open Nock
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.MemoryWalkLabel

noncomputable section

/-- Compute whole-table γ-collision bound: `h · (10 − 1) = 9N`. -/
def computePrefixGammaBound (N : ℕ) : ℕ := 9 * N

/-- Memory forest whole-table γ-collision bound: `h · (6 − 1) = 5M`. -/
def memoryPrefixGammaBound (M : ℕ) : ℕ := 5 * M

theorem computePrefixGammaBound_eq (N : ℕ) : computePrefixGammaBound N = 9 * N := rfl
theorem memoryPrefixGammaBound_eq (M : ℕ) : memoryPrefixGammaBound M = 5 * M := rfl

section Lift
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem card_filter_gamma_const_le (bad : Finset K) (d : ℕ) (hb : bad.card ≤ d) :
    (Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ bad)).card ≤
      d * Fintype.card K ^ 3 := by
  have hsub : Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ bad) ⊆
      (Finset.univ : Finset (K × (K × K))).biUnion
        (fun t => bad.image (fun g => ((t.1, g), t.2))) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine Finset.mem_biUnion.mpr ⟨(ω.1.1, ω.2), Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨ω.1.2, hω, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun _ _ => Finset.card_image_le.trans hb)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring_nf
  exact le_rfl

/-- Compute prefix γ-event: `γ ∈ prefixBadGammas V Cv fo h`. -/
def computePrefixGammaEvent (V : ℕ → Fin 10 → K) (Cv : ℕ → ℕ → Fin 10 → K)
    (fo : ℕ → ℕ) (h : ℕ) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ prefixBadGammas V Cv fo h)

theorem mem_computePrefixGammaEvent_iff (V : ℕ → Fin 10 → K) (Cv : ℕ → ℕ → Fin 10 → K)
    (fo : ℕ → ℕ) (h : ℕ) (ω : JointCoins K) :
    ω ∈ computePrefixGammaEvent V Cv fo h ↔
      gamma ω ∈ prefixBadGammas V Cv fo h := by
  simp [computePrefixGammaEvent]

/-- The Finset is a function of `(V, Cv, fo, h)` alone — no coin enters the
node vectors. -/
theorem computePrefixGammaEvent_congr {V V' : ℕ → Fin 10 → K}
    {Cv Cv' : ℕ → ℕ → Fin 10 → K} {fo fo' : ℕ → ℕ} {h : ℕ}
    (hV : V = V') (hCv : Cv = Cv') (hfo : fo = fo') :
    computePrefixGammaEvent V Cv fo h = computePrefixGammaEvent V' Cv' fo' h := by
  subst hV hCv hfo; rfl

theorem card_computePrefixGammaEvent_le (V : ℕ → Fin 10 → K) (Cv : ℕ → ℕ → Fin 10 → K)
    (fo : ℕ → ℕ) (h : ℕ) :
    (computePrefixGammaEvent V Cv fo h).card ≤
      computePrefixGammaBound h * Fintype.card K ^ 3 := by
  refine card_filter_gamma_const_le _ (computePrefixGammaBound h) ?_
  refine (prefixBadGammas_card_le (node_size := 10) V Cv fo h).trans ?_
  simp only [computePrefixGammaBound]
  omega

/-- Memory forest prefix γ-event: `γ ∈ forestPrefixBadGammas V Cv fo kroots h`. -/
def memoryPrefixGammaEvent (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K =>
    gamma ω ∈ forestPrefixBadGammas V Cv fo kroots h)

theorem mem_memoryPrefixGammaEvent_iff (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) (ω : JointCoins K) :
    ω ∈ memoryPrefixGammaEvent V Cv fo kroots h ↔
      gamma ω ∈ forestPrefixBadGammas V Cv fo kroots h := by
  simp [memoryPrefixGammaEvent]

theorem memoryPrefixGammaEvent_congr {V V' : ℕ → Fin 6 → K}
    {Cv Cv' : ℕ → ℕ → Fin 6 → K} {fo fo' : ℕ → ℕ} {kroots h : ℕ}
    (hV : V = V') (hCv : Cv = Cv') (hfo : fo = fo') :
    memoryPrefixGammaEvent V Cv fo kroots h =
      memoryPrefixGammaEvent V' Cv' fo' kroots h := by
  subst hV hCv hfo; rfl

theorem card_memoryPrefixGammaEvent_le (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) :
    (memoryPrefixGammaEvent V Cv fo kroots h).card ≤
      memoryPrefixGammaBound h * Fintype.card K ^ 3 := by
  refine card_filter_gamma_const_le _ (memoryPrefixGammaBound h) ?_
  refine (forestPrefixBadGammas_card_le (node_size := 6) V Cv fo kroots h).trans ?_
  simp only [memoryPrefixGammaBound]
  omega

end Lift

/-! ## Committed-table wrappers (trace columns only) -/

section Committed
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

/-- 1-indexed committed compute node vectors from `computeSourceEnv`. -/
def committedComputeV (envs : Fin N → Env K) (i : ℕ) : Fin 10 → K :=
  if h : 1 ≤ i ∧ i - 1 < N then rowLabelVec (envs ⟨i - 1, h.2⟩) else 0

/-- 1-indexed committed compute child vectors. -/
def committedComputeCv (envs : Fin N → Env K) (i l : ℕ) : Fin 10 → K :=
  if h : 1 ≤ i ∧ i - 1 < N then rowChildVec (envs ⟨i - 1, h.2⟩) (l - 1) else 0

/-- **The compute prefix γ-event of a committed table.**  `V`/`Cv`/`fo` are
`rowLabelVec` / `rowChildVec` / `foOf` — functions of the trace columns
(`rowLabelVec_congr`, `rowChildVec_congr`, `foOf` via `rowFanout_congr`). -/
def computePrefixGammaEventOf (envs : Fin N → Env K) : Finset (JointCoins K) :=
  computePrefixGammaEvent (committedComputeV envs) (committedComputeCv envs)
    (foOf envs) N

theorem computePrefixGammaEventOf_eq_prefix (envs : Fin N → Env K) (ω : JointCoins K) :
    ω ∈ computePrefixGammaEventOf envs ↔
      gamma ω ∈ prefixBadGammas (committedComputeV envs) (committedComputeCv envs)
        (foOf envs) N :=
  mem_computePrefixGammaEvent_iff _ _ _ _ _

/-- The event is invariant under a trace-column rewrite of every row. -/
theorem computePrefixGammaEventOf_congr {envs envs' : Fin N → Env K}
    (h : ∀ i : Fin N, (envs i).trace = (envs' i).trace ∧
      (envs i).traceNext = (envs' i).traceNext) :
    computePrefixGammaEventOf envs = computePrefixGammaEventOf envs' := by
  have hV : committedComputeV envs = committedComputeV envs' := by
    funext i; unfold committedComputeV
    split_ifs with hi
    · exact rowLabelVec_congr (h ⟨i - 1, hi.2⟩).1 (h ⟨i - 1, hi.2⟩).2
    · rfl
  have hCv : committedComputeCv envs = committedComputeCv envs' := by
    funext i l; unfold committedComputeCv
    split_ifs with hi
    · exact rowChildVec_congr (h ⟨i - 1, hi.2⟩).1 (h ⟨i - 1, hi.2⟩).2 _
    · rfl
  have hfo : foOf envs = foOf envs' := by
    funext i; unfold foOf
    split_ifs with hi
    · simp only [rowFanout, rowStateOf_congr (h ⟨i - 1, hi.2⟩).1]
    · rfl
  exact computePrefixGammaEvent_congr hV hCv hfo

theorem card_computePrefixGammaEventOf_le (envs : Fin N → Env K) :
    (computePrefixGammaEventOf envs).card ≤
      computePrefixGammaBound N * Fintype.card K ^ 3 := by
  unfold computePrefixGammaEventOf
  exact card_computePrefixGammaEvent_le _ _ _ _

end Committed

section MemoryCommitted
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {M : ℕ}

/-- Caller-supplied committed memory node / child / fanout.  The package
wrapper fills these from `memoryBaseEnv` / `memoryLabelVec`; the event
itself still mentions no coin. -/
def memoryPrefixGammaEventOf (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots : ℕ) (h : ℕ) : Finset (JointCoins K) :=
  memoryPrefixGammaEvent V Cv fo kroots h

theorem memoryPrefixGammaEventOf_eq (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) :
    memoryPrefixGammaEventOf V Cv fo kroots h =
      memoryPrefixGammaEvent V Cv fo kroots h :=
  rfl

/-- The memory event is a function of the committed vectors alone. -/
theorem memoryPrefixGammaEventOf_congr {V V' : ℕ → Fin 6 → K}
    {Cv Cv' : ℕ → ℕ → Fin 6 → K} {fo fo' : ℕ → ℕ} {kroots h : ℕ}
    (hV : V = V') (hCv : Cv = Cv') (hfo : fo = fo') :
    memoryPrefixGammaEventOf V Cv fo kroots h =
      memoryPrefixGammaEventOf V' Cv' fo' kroots h :=
  memoryPrefixGammaEvent_congr hV hCv hfo

theorem card_memoryPrefixGammaEventOf_le (V : ℕ → Fin 6 → K) (Cv : ℕ → ℕ → Fin 6 → K)
    (fo : ℕ → ℕ) (kroots h : ℕ) :
    (memoryPrefixGammaEventOf V Cv fo kroots h).card ≤
      memoryPrefixGammaBound h * Fintype.card K ^ 3 :=
  card_memoryPrefixGammaEvent_le _ _ _ _ _

end MemoryCommitted

/-! ## Committed memory wrappers from `memorySourceEnv` / `memoryBaseEnv` -/

section MemoryEnv
variable {F K : Type} [Field F] [Field K] [Fintype K] [DecidableEq K] [DecidableEq F] {M : ℕ}

/-- Own-row `x^mem` from the K-trace parent cell and the F-selector state tag.
Roles `0,1,2,4,3` are the parent noun / axis pair (`MemoryWalkLabel.labelCoordAt`). -/
def memRowLabelVec (eK : Env K) (eF : Env F) : Fin 6 → K
  | ⟨0, _⟩ => MemoryTable.mstateTagField (WalkTilingEvents.memRowStateOf eF)
  | ⟨1, _⟩ => eK.trace 0
  | ⟨2, _⟩ => eK.trace 1
  | ⟨3, _⟩ => eK.trace 2
  | ⟨4, _⟩ => eK.trace 4
  | ⟨5, _⟩ => eK.trace 3

/-- Declared child slot `j`: hosted tag at roles `45`/`46`,
cell at `5..9` / `10..14`. -/
def memRowChildVec (eK : Env K) (j : Fin 2) : Fin 6 → K
  | ⟨0, _⟩ => eK.trace (45 + (j : ℕ))
  | ⟨1, _⟩ => eK.trace (5 + 5 * (j : ℕ))
  | ⟨2, _⟩ => eK.trace (5 + 5 * (j : ℕ) + 1)
  | ⟨3, _⟩ => eK.trace (5 + 5 * (j : ℕ) + 2)
  | ⟨4, _⟩ => eK.trace (5 + 5 * (j : ℕ) + 4)
  | ⟨5, _⟩ => eK.trace (5 + 5 * (j : ℕ) + 3)

theorem memRowLabelVec_congr {eK eK' : Env K} {eF eF' : Env F}
    (hK : eK.trace = eK'.trace) (hF : eF.trace = eF'.trace) :
    memRowLabelVec eK eF = memRowLabelVec eK' eF' := by
  funext k; fin_cases k <;> simp [memRowLabelVec, hK, WalkTilingEvents.memRowStateOf, hF]

theorem memRowChildVec_congr {eK eK' : Env K} (hK : eK.trace = eK'.trace) (j : Fin 2) :
    memRowChildVec eK j = memRowChildVec eK' j := by
  funext k; fin_cases k <;> simp [memRowChildVec, hK]

/-- 1-indexed committed memory node vectors. -/
def committedMemoryV (envsK : Fin M → Env K) (envsF : Fin M → Env F) (i : ℕ) : Fin 6 → K :=
  if h : 1 ≤ i ∧ i - 1 < M then
    memRowLabelVec (envsK ⟨i - 1, h.2⟩) (envsF ⟨i - 1, h.2⟩)
  else 0

/-- 1-indexed committed memory child vectors (`l` 1-indexed, as `flatBlksV`). -/
def committedMemoryCv (envsK : Fin M → Env K) (i l : ℕ) : Fin 6 → K :=
  if h : 1 ≤ i ∧ i - 1 < M then
    if hl : l - 1 < 2 then memRowChildVec (envsK ⟨i - 1, h.2⟩) ⟨l - 1, hl⟩ else 0
  else 0

/-- **The memory prefix γ-event of a committed table.**  `V`/`Cv`/`fo` are
functions of the trace columns (`memRowLabelVec_congr`, `memRowChildVec_congr`,
`foOfMem` via selectors). -/
def memoryPrefixGammaEventOfEnvs (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots : ℕ) : Finset (JointCoins K) :=
  memoryPrefixGammaEvent (committedMemoryV envsK envsF) (committedMemoryCv envsK)
    (WalkTilingEvents.foOfMem envsF) kroots M

theorem memoryPrefixGammaEventOfEnvs_eq_prefix (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) (ω : JointCoins K) :
    ω ∈ memoryPrefixGammaEventOfEnvs envsK envsF kroots ↔
      gamma ω ∈ forestPrefixBadGammas (committedMemoryV envsK envsF)
        (committedMemoryCv envsK) (WalkTilingEvents.foOfMem envsF) kroots M :=
  mem_memoryPrefixGammaEvent_iff _ _ _ _ _ _

theorem memoryPrefixGammaEventOfEnvs_congr {envsK envsK' : Fin M → Env K}
    {envsF envsF' : Fin M → Env F} {kroots : ℕ}
    (hK : ∀ i : Fin M, (envsK i).trace = (envsK' i).trace)
    (hF : ∀ i : Fin M, (envsF i).trace = (envsF' i).trace) :
    memoryPrefixGammaEventOfEnvs envsK envsF kroots =
      memoryPrefixGammaEventOfEnvs envsK' envsF' kroots := by
  have hV : committedMemoryV envsK envsF = committedMemoryV envsK' envsF' := by
    funext i; unfold committedMemoryV
    split_ifs with hi
    · exact memRowLabelVec_congr (hK ⟨i - 1, hi.2⟩) (hF ⟨i - 1, hi.2⟩)
    · rfl
  have hCv : committedMemoryCv envsK = committedMemoryCv envsK' := by
    funext i l; unfold committedMemoryCv
    split_ifs
    · exact memRowChildVec_congr (hK ⟨i - 1, by omega⟩) _
    · rfl
    · rfl
  have hfo : WalkTilingEvents.foOfMem envsF = WalkTilingEvents.foOfMem envsF' := by
    funext i
    unfold WalkTilingEvents.foOfMem
    split_ifs with hi
    · have hst : WalkTilingEvents.memRowStateOf (envsF ⟨i - 1, hi.2⟩) =
          WalkTilingEvents.memRowStateOf (envsF' ⟨i - 1, hi.2⟩) := by
        unfold WalkTilingEvents.memRowStateOf
        rw [hF]
      simp only [hst]
    · rfl
  exact memoryPrefixGammaEvent_congr hV hCv hfo

theorem card_memoryPrefixGammaEventOfEnvs_le (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) :
    (memoryPrefixGammaEventOfEnvs envsK envsF kroots).card ≤
      memoryPrefixGammaBound M * Fintype.card K ^ 3 := by
  unfold memoryPrefixGammaEventOfEnvs
  exact card_memoryPrefixGammaEvent_le _ _ _ _ _

end MemoryEnv

end

end Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
