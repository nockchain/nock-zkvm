/-
  Nock/NockVMROM/Thm54/P8Core/PartAMemoryChip12.lean

* The six walk gates at slot `9`: `walkAlphaChallenge12 = .Var .challenge 9`; the two line gates through
    `walkBoundarySubst12` / `walkSubst12`; `walkCount1InGate12`, `walkAccInitInGate12`,
    `walkCountStepInGate12`, `walkAccStepInGate12` through `childInnerSum12` / `childSumAt12` /
    `childSumCC12` / `cmAt12` / `selectorCM12`.
  * `mixedTransitionGates12_eq_rename`: the twelve-coin mixed bucket IS the deployed bucket with
    challenge slot `3 ↔ 9` swapped (`renameChal walkSlotSwap`), by `rfl` — so no other gate moved.
  * `memorySourceTemplate12`, `sourceMemoryRAP12`, `namedSourceMemoryRAP12`,
    `namedFinalMemoryRAP12` (`205/156/4/1`, unchanged numerals), and
    `DeployedChipFamily12.memoryChipAt12`.
  * **The transport** `namedFinalMemoryRAP12_satisfies_iff`: the twelve-coin chip at `chalVal` is
    satisfied by `Q` iff the deployed chip at `chalVal ∘ walkRawSwap` is; at a tuple,
    `memoryChipAt12_satisfies_iff`: iff the deployed chip at `walkView11 c`.
  * The honest walk-gate lemmas at slot `9` (`MemoryWalkLabelCanonical` ported):
    `canonical_inGateWalkGates12`.

  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartATuple12
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.P8Core.PartAReadSets
import Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Nock.NockVMROM.Thm54.PartA12

open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.MemoryTable
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The six walk gates at memory slot `9` -/

section Gates

variable {F : Type} [Field F]

open MemoryWalkLabel in
/-- Walk-α of the twelve-coin chip: memory `𝕂` challenge index `9` (was `3`). -/
def walkAlphaChallengeIndex12 : ℕ := 9

open MemoryWalkLabel in
def walkAlphaChallenge12 : MixedExpr F := .Var .challenge walkAlphaChallengeIndex12

open MemoryWalkLabel in
/-- `Σ_{k=1}^{fanout} αW^k · RLC^γ(children(i,k,·))` at slot `9`. -/
def childInnerSum12 (r : RowReader F) : ℕ → MixedExpr F
  | 0 => .Const 0
  | 1 => .Mul (.Pow walkAlphaChallenge12 1) (childRLCAt r 0)
  | 2 =>
      .Add (.Mul (.Pow walkAlphaChallenge12 1) (childRLCAt r 0))
        (.Mul (.Pow walkAlphaChallenge12 2) (childRLCAt r 1))
  | _ => .Const 0

open MemoryWalkLabel in
def childSumAt12 (r : RowReader F) (st : MState) : MixedExpr F :=
  childInnerSum12 r (fanoutMem st)

open MemoryWalkLabel in
def childSumCC12 (r : RowReader F) : MixedExpr F := selSum r (childSumAt12 r)

open MemoryWalkLabel in
def cmAt12 (st : MState) : MixedExpr F := .Pow walkAlphaChallenge12 (fanoutMem st)

open MemoryWalkLabel in
def selectorCM12 (r : RowReader F) : MixedExpr F := selSum r cmAt12

open MemoryWalkLabel in
/-- `first · (count(1) − initial_count · cm(1))`, `cm` at slot `9`. -/
def walkCount1InGate12 : MixedExpr F :=
  .Scale firstMaskBase (.Sub countCur (.Mul initialCountPub (selectorCM12 curReader)))

open MemoryWalkLabel in
/-- `first · (acc(1) − initial_count · cc(1))`, `cc` at slot `9`. -/
def walkAccInitInGate12 : MixedExpr F :=
  .Scale firstMaskBase
    (.Sub accCur (.Mul initialCountPub (childSumCC12 curReader)))

open MemoryWalkLabel in
/-- `(1 − last) · (count(i+1) − count(i) · cm(i+1))`, `cm` at slot `9`. -/
def walkCountStepInGate12 : MixedExpr F :=
  .Scale notLastBase (.Sub countNext (.Mul countCur (selectorCM12 nextReader)))

open MemoryWalkLabel in
/-- `dequeueMask·ln·RLC^γ(x^mem) + notLast·(Δacc − count·cc)`, `cc` at slot `9`. -/
def walkAccStepInGate12 : MixedExpr F :=
  .Add
    (.Scale dequeueMaskCur (.Mul lnNext (labelRLC nextReader)))
    (.Scale notLastBase
      (.Sub (.Sub accNext accCur) (.Mul countCur (childSumCC12 nextReader))))

def inGateWalkGates12 : List (MixedExpr F) :=
  [walkCount1InGate12, walkAccInitInGate12, walkCountStepInGate12, walkAccStepInGate12]

/-- The walk transition substitution with walk-α at memory slot `9`. -/
def walkSubst12 : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 6 then extVar .traceCur (31 + i)
      else if i = 6 then rootMaskE else .Const 0
  | .traceNext, i =>
      if i < 6 then extVar .traceNext (31 + i)
      else if i = 6 then rootMaskENext else .Const 0
  | .challenge, 0 => .Var .challenge 9
  | .challenge, _ + 1 => .Const 0
  | .publicVal, 0 => .Var .publicVal 0
  | .publicVal, 1 => .Const 0
  | .publicVal, _ + 2 => .Const 0

/-- The walk boundary substitution with walk-α at memory slot `9`. -/
def walkBoundarySubst12 : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 6 then extVar .traceCur (31 + i)
      else if i = 6 then rootMaskE else .Const 0
  | .traceNext, _ => .Const 0
  | .challenge, 0 => .Var .challenge 9
  | .challenge, _ + 1 => .Const 0
  | .publicVal, 0 => .Var .publicVal 0
  | .publicVal, 1 => .Const 0
  | .publicVal, _ + 2 => .Const 0

/-- The walk boundary gates at slot `9` (`ln1`, `count1`, `accInit`). -/
def walkInitGates12 : List (MixedExpr F) :=
  [.Scale (bcur 4) (MixedCoordinateCompiler.MixedExpr.ofExpr (Trans.walkLn1.subst walkBoundarySubst12)),
   walkCount1InGate12, walkAccInitInGate12]

/-- The walk transition gates at slot `9` (`lnStep`, `countStep`, `accStep`). -/
def walkStepGates12 : List (MixedExpr F) :=
  [.Scale (.sub (.const 1) (bcur 5)) (MixedCoordinateCompiler.MixedExpr.ofExpr (Trans.walkLnStep.subst walkSubst12)),
   walkCountStepInGate12, walkAccStepInGate12]

def walkGates12 : List (MixedExpr F) := walkInitGates12 ++ walkStepGates12 ++ [walkTerminal]

end Gates

section Bucket

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

def paperKGatesCore12 : List (MixedExpr F) :=
  rapMemGates (K := K) ++ baseTypedClassGates (K := K) ++ bottomPins (K := K)
    ++ [intermediateChain] ++ walkGates12 ++ ioCoreGates

def paperKGates12 : List (MixedExpr F) :=
  paperKGatesCore12 (K := K) (F := F) ++ paperEndpointGates (F := F) ++
    MemoryWalkLabel.queueWitnessGates (F := F)

/-- **The twelve-coin memory mixed bucket** (50 gates; the six walk gates at slot `9`). -/
def mixedTransitionGates12 (_b : Basis (Fin 3) F K) : List (MixedExpr F) :=
  paperKGates12 (K := K) (F := F) ++ [haltAtomMixed]

end Bucket

/-! ## 2. Challenge renaming -/

section Rename

variable {F : Type} [Field F]

/-- Rename the `𝕂` challenge slots of a mixed gate (base-field leaves untouched). -/
def renameChal (σ : ℕ → ℕ) : MixedExpr F → MixedExpr F
  | .Var .challenge i => .Var .challenge (σ i)
  | .Var .traceCur i => .Var .traceCur i
  | .Var .traceNext i => .Var .traceNext i
  | .Var .publicVal i => .Var .publicVal i
  | .Lift g => .Lift g
  | .Scale g u => .Scale g (renameChal σ u)
  | .Const c => .Const c
  | .Add x y => .Add (renameChal σ x) (renameChal σ y)
  | .Sub x y => .Sub (renameChal σ x) (renameChal σ y)
  | .Neg x => .Neg (renameChal σ x)
  | .Mul x y => .Mul (renameChal σ x) (renameChal σ y)
  | .Pow x n => .Pow (renameChal σ x) n

theorem degree_renameChal (σ : ℕ → ℕ) : ∀ g : MixedExpr F, (renameChal σ g).degree = g.degree
  | .Var kind i => by cases kind <;> rfl
  | .Lift _ => rfl
  | .Scale g u => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ u]
  | .Const _ => rfl
  | .Add x y => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ x,
      degree_renameChal σ y]
  | .Sub x y => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ x,
      degree_renameChal σ y]
  | .Neg x => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ x]
  | .Mul x y => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ x,
      degree_renameChal σ y]
  | .Pow x n => by simp only [renameChal, MixedExpr.degree, degree_renameChal σ x]

variable {K : Type} [Field K] [Algebra F K]

/-- **Renaming is re-indexing the challenge environment.** -/
theorem eval_renameChal (σ : ℕ → ℕ) (eK : Env K) (eF : Env F) :
    ∀ g : MixedExpr F,
      (renameChal σ g).eval eK eF = g.eval { eK with chal := fun i => eK.chal (σ i) } eF
  | .Var kind i => by cases kind <;> rfl
  | .Lift _ => rfl
  | .Scale g u => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF u]
  | .Const _ => rfl
  | .Add x y => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF x,
      eval_renameChal σ eK eF y]
  | .Sub x y => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF x,
      eval_renameChal σ eK eF y]
  | .Neg x => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF x]
  | .Mul x y => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF x,
      eval_renameChal σ eK eF y]
  | .Pow x n => by simp only [renameChal, MixedExpr.eval, eval_renameChal σ eK eF x]

/-- A coefficient expression with no raw challenge evaluates independently of `chal`. -/
theorem coeff_eval_congr (e e' : Env F) (ht : e'.trace = e.trace) (hn : e'.traceNext = e.traceNext)
    (hp : e'.pub = e.pub) :
    ∀ c : CoeffExpr F, PartAReadSets.coeffChals c = [] → c.eval e' = c.eval e
  | .const _, _ => rfl
  | .var .traceCur i, _ => by simp [CoeffExpr.eval, ht]
  | .var .traceNext i, _ => by simp [CoeffExpr.eval, hn]
  | .var .challenge i, h => by simp [PartAReadSets.coeffChals] at h
  | .var .publicVal i, _ => by simp [CoeffExpr.eval, hp]
  | .add a b, h => by
      simp only [PartAReadSets.coeffChals, List.append_eq_nil_iff] at h
      simp only [CoeffExpr.eval, coeff_eval_congr e e' ht hn hp a h.1,
        coeff_eval_congr e e' ht hn hp b h.2]
  | .sub a b, h => by
      simp only [PartAReadSets.coeffChals, List.append_eq_nil_iff] at h
      simp only [CoeffExpr.eval, coeff_eval_congr e e' ht hn hp a h.1,
        coeff_eval_congr e e' ht hn hp b h.2]
  | .mul a b, h => by
      simp only [PartAReadSets.coeffChals, List.append_eq_nil_iff] at h
      simp only [CoeffExpr.eval, coeff_eval_congr e e' ht hn hp a h.1,
        coeff_eval_congr e e' ht hn hp b h.2]
  | .neg a, h => by
      simp only [PartAReadSets.coeffChals] at h
      simp only [CoeffExpr.eval, coeff_eval_congr e e' ht hn hp a h]
  | .pow a n, h => by
      simp only [PartAReadSets.coeffChals] at h
      simp only [CoeffExpr.eval, coeff_eval_congr e e' ht hn hp a h]

/-- A mixed gate with no raw base-field challenge evaluates independently of the base `chal`. -/
theorem mixed_eval_congr_F (eK : Env K) (e e' : Env F) (ht : e'.trace = e.trace)
    (hn : e'.traceNext = e.traceNext) (hp : e'.pub = e.pub) :
    ∀ g : MixedExpr F, PartAReadSets.mixedRawChals g = [] → g.eval eK e' = g.eval eK e
  | .Var kind i, _ => by cases kind <;> rfl
  | .Lift c, h => by
      simp only [PartAReadSets.mixedRawChals] at h
      simp only [MixedExpr.eval, coeff_eval_congr e e' ht hn hp c h]
  | .Scale c u, h => by
      simp only [PartAReadSets.mixedRawChals, List.append_eq_nil_iff] at h
      simp only [MixedExpr.eval, coeff_eval_congr e e' ht hn hp c h.1,
        mixed_eval_congr_F eK e e' ht hn hp u h.2]
  | .Const _, _ => rfl
  | .Add x y, h => by
      simp only [PartAReadSets.mixedRawChals, List.append_eq_nil_iff] at h
      simp only [MixedExpr.eval, mixed_eval_congr_F eK e e' ht hn hp x h.1,
        mixed_eval_congr_F eK e e' ht hn hp y h.2]
  | .Sub x y, h => by
      simp only [PartAReadSets.mixedRawChals, List.append_eq_nil_iff] at h
      simp only [MixedExpr.eval, mixed_eval_congr_F eK e e' ht hn hp x h.1,
        mixed_eval_congr_F eK e e' ht hn hp y h.2]
  | .Neg x, h => by
      simp only [PartAReadSets.mixedRawChals] at h
      simp only [MixedExpr.eval, mixed_eval_congr_F eK e e' ht hn hp x h]
  | .Mul x y, h => by
      simp only [PartAReadSets.mixedRawChals, List.append_eq_nil_iff] at h
      simp only [MixedExpr.eval, mixed_eval_congr_F eK e e' ht hn hp x h.1,
        mixed_eval_congr_F eK e e' ht hn hp y h.2]
  | .Pow x n, h => by
      simp only [PartAReadSets.mixedRawChals] at h
      simp only [MixedExpr.eval, mixed_eval_congr_F eK e e' ht hn hp x h]

end Rename

section Equations

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **No other gate moved**: the twelve-coin bucket is the deployed bucket with the `𝕂` challenge
slots `3 ↔ 9` swapped.  Only the six walk gates read slot `3` (`slot3_readers`, L1), and no
deployed gate reads slot `9`, so the swap is the identity on the other 44. -/
theorem mixedTransitionGates12_eq_rename (b : Basis (Fin 3) F K) :
    mixedTransitionGates12 (F := F) (K := K) b =
      (mixedTransitionGates (F := F) (K := K) b).map (renameChal walkSlotSwap) := rfl

/-- The four in-gate walk gates likewise. -/
theorem inGateWalkGates12_eq_rename :
    inGateWalkGates12 (F := F) = (MemoryWalkLabel.inGateWalkGates (F := F)).map
      (renameChal walkSlotSwap) := rfl

/-- The six twelve-coin walk gates read slot `9`, never slot `3` (measured by `mixedSlots`). -/
theorem walkGates12_slots :
    (walkGates12 (F := F)).map PartAReadSets.mixedSlots =
      (walkGates (F := F)).map (fun g => (PartAReadSets.mixedSlots g).map walkSlotSwap) := rfl

theorem walkGates12_read_slot9 :
    (walkGates12 (F := F)).map (fun g => (PartAReadSets.mixedSlots g).contains 9) =
      [true, true, true, true, true, true, false] := rfl

theorem walkGates12_unread_slot3 :
    (walkGates12 (F := F)).all (fun g => !(PartAReadSets.mixedSlots g).contains 3) = true := rfl

theorem mixedTransitionGates12_length (b : Basis (Fin 3) F K) :
    (mixedTransitionGates12 (F := F) (K := K) b).length = 50 := by
  rw [mixedTransitionGates12_eq_rename, List.length_map, mixedTransitionGates_length]

theorem mixedTransitionGates12_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ mixedTransitionGates12 (F := F) (K := K) b, g.degree ≤ 4 := by
  intro g hg
  rw [mixedTransitionGates12_eq_rename, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  rw [degree_renameChal]
  exact mixedTransitionGates_degree b g' hg'

/-! ## 3. The twelve-coin template and chips -/

/-- The memory source template with the twelve-coin mixed bucket (every other field verbatim). -/
def memorySourceTemplate12 (b : Basis (Fin 3) F K) : ChipTemplate F where
  rounds := 1
  rounds_pos := by omega
  baseColsOf := fun _ => 6
  extColsOf := fun _ => 58
  baseTransition := baseTransitionGates b
  extTransition := []
  mixedTransition := mixedTransitionGates12 b
  extDeg1 := degreeOneEndpoints
  extDeg3 := degreeThreeEndpoints
  equalityChecks := equalityChecks b
  baseTransition_deg := baseTransitionGates_degree b
  extTransition_deg := by intro g hg; cases hg
  mixedTransition_deg := mixedTransitionGates12_degree b
  extDeg1_deg := degreeOneEndpoints_degree
  extDeg3_deg := degreeThreeEndpoints_degree
  equalityChecks_deg := equalityChecks_degree b

def sourceMemoryRAP12 {h : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  expandChipTail (memorySourceTemplate12 b) b chalVal pubVal orbit H 2

def namedSourceMemoryRAP12 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) : FixedPreprocessingRAP F where
  rap := sourceMemoryRAP12 b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by
    show 0 < (memorySourceTemplate12 b).rounds
    exact (memorySourceTemplate12 b).rounds_pos
  fixedCount := 4
  preprocessingIndex :=
    { toFun := fun j =>
        if h3 : (j : ℕ) = 3 then ⟨154, by change 154 < 182; omega⟩
        else if h2 : (j : ℕ) = 2 then ⟨153, by change 153 < 182; omega⟩
        else ⟨4 + (j : ℕ), by
          change 4 + (j : ℕ) < 182
          have hj : (j : ℕ) < 4 := j.isLt
          omega⟩
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first | rfl | cases hij }
  preprocessing
    | 0 => OptimizedMemoryCanonicalTrace.firstRowMask nodes
    | 1 => OptimizedMemoryCanonicalTrace.lastRowMask nodes
    | 2 => OptimizedMemoryCanonicalTrace.rootRowMask nodes kMem
    | 3 => OptimizedMemoryCanonicalTrace.dequeueRowMask nodes kMem

/-- **The twelve-coin memory chip** (residual padding as `namedFinalMemoryRAP`). -/
def namedFinalMemoryRAP12 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) : FixedPreprocessingRAP F :=
  let S := namedSourceMemoryRAP12 hn nodes b chalVal pubVal orbit kMem
  RAPPadding.padFixedPreprocessing S
    (RAPPadding.firstRoundExtra S.rap S.rounds_pos
      (RAPPadding.memoryResidualColumns 3))
    (RAPPadding.memoryResidualTransitionGates 3)

/-! ## 4. The transport -/

theorem memoryCol0_challenge (idx : ℕ) : memoryCol0 .challenge idx = 6 + 3 * idx := rfl

theorem memorySourceTemplate12_col0 (b : Basis (Fin 3) F K) :
    (memorySourceTemplate12 b).col0 3 = memoryCol0 := by
  funext kind idx
  simp [ChipTemplate.col0, ChipTemplate.baseCols, memorySourceTemplate12, memoryCol0] <;>
    first | rfl | decide

theorem memorySourceTemplate_col0' (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).col0 3 = memoryCol0 := by
  funext kind idx
  simp [ChipTemplate.col0, ChipTemplate.baseCols, memorySourceTemplate, memoryCol0] <;>
    first | rfl | decide

/-- Gathering a swapped physical environment is re-indexing the gathered challenges. -/
theorem gather_swap (b : Basis (Fin 3) F K) (E : Env F) :
    gatherEnv b memoryCol0 { E with chal := fun j => E.chal (walkRawSwap j) } =
      { gatherEnv b memoryCol0 E with
          chal := fun i => (gatherEnv b memoryCol0 E).chal (walkSlotSwap i) } := by
  show Env.mk _ _ _ _ = Env.mk _ _ _ _
  congr 1
  funext idx
  simp only [gatherEnv, memoryCol0_challenge]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [walkRawSwap_coord idx k k.isLt]

theorem baseTransitionGates_chalFree (b : Basis (Fin 3) F K) :
    ∀ g ∈ baseTransitionGates b, PartAReadSets.coeffChals g = [] := by
  have h : (baseTransitionGates b).map PartAReadSets.coeffChals = [[], [], [], [], [], []] := rfl
  intro g hg
  have hm : PartAReadSets.coeffChals g ∈ (baseTransitionGates b).map PartAReadSets.coeffChals :=
    List.mem_map_of_mem hg
  rw [h] at hm
  simpa using hm

theorem mixedTransitionGates_rawFree (b : Basis (Fin 3) F K) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) b, PartAReadSets.mixedRawChals g = [] := by
  intro g hg
  have hm : PartAReadSets.mixedRawChals g ∈
      (mixedTransitionGates (F := F) (K := K) b).map PartAReadSets.mixedRawChals :=
    List.mem_map_of_mem hg
  rw [PartAReadSets.memoryMixed_noRawChallenge b] at hm
  exact List.eq_of_mem_replicate hm

theorem sourceMemoryRAP12_w {h : ℕ} (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (sourceMemoryRAP12 b cv pv orbit H).w = 182 := rfl

theorem sourceMemoryRAP_w {h : ℕ} (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (sourceMemoryRAP b cv pv orbit H).w = 182 := rfl

/-- **Source transport.**  The twelve-coin source chip at `chalVal` is satisfied by `P` iff the
deployed source chip at `chalVal ∘ walkRawSwap` is satisfied by a trace with the same columns.
(The two traces are kept separate so that no unifier ever compares the two chips.) -/
theorem sourceMemoryRAP12_satisfies_iff {h : ℕ} (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (P : Fin (sourceMemoryRAP12 b cv pv orbit H).w → F[X])
    (P' : Fin (sourceMemoryRAP b (cv ∘ walkRawSwap) pv orbit H).w → F[X])
    (hP : ∀ (i : ℕ) (h1 : i < (sourceMemoryRAP12 b cv pv orbit H).w)
      (h2 : i < (sourceMemoryRAP b (cv ∘ walkRawSwap) pv orbit H).w), P ⟨i, h1⟩ = P' ⟨i, h2⟩) :
    (sourceMemoryRAP12 b cv pv orbit H).Satisfies P ↔
      (sourceMemoryRAP b (cv ∘ walkRawSwap) pv orbit H).Satisfies P' := by
  have hw12 := sourceMemoryRAP12_w b cv pv orbit H
  have hw' := sourceMemoryRAP_w b (cv ∘ walkRawSwap) pv orbit H
  unfold sourceMemoryRAP12 at P hP ⊢
  unfold sourceMemoryRAP at P' hP ⊢
  rw [expandChipTail_satisfies_iff_language, expandChipTail_satisfies_iff_language,
    memorySourceTemplate12_col0, memorySourceTemplate_col0']
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  set E := Reify.envOfTrace P orbit.ω x cv pv with hE
  set E' := Reify.envOfTrace P' orbit.ω x (cv ∘ walkRawSwap) pv with hE'
  have htr : E'.trace = E.trace := by
    funext i
    simp only [hE, hE', Reify.envOfTrace]
    by_cases hi : i < 182
    · have h1 : i < (expandChipTail (memorySourceTemplate12 b) b cv pv orbit H 2).w := hi
      have h2 : i < (expandChipTail (memorySourceTemplate b) b (cv ∘ walkRawSwap) pv orbit H 2).w := hi
      rw [dif_pos h1, dif_pos h2, hP i h1 h2]
    · have h1 : ¬ i < (expandChipTail (memorySourceTemplate12 b) b cv pv orbit H 2).w := hi
      have h2 : ¬ i < (expandChipTail (memorySourceTemplate b) b (cv ∘ walkRawSwap) pv orbit H 2).w := hi
      rw [dif_neg h1, dif_neg h2]
  have hnx : E'.traceNext = E.traceNext := by
    funext i
    simp only [hE, hE', Reify.envOfTrace]
    by_cases hi : i < 182
    · have h1 : i < (expandChipTail (memorySourceTemplate12 b) b cv pv orbit H 2).w := hi
      have h2 : i < (expandChipTail (memorySourceTemplate b) b (cv ∘ walkRawSwap) pv orbit H 2).w := hi
      rw [dif_pos h1, dif_pos h2, hP i h1 h2]
    · have h1 : ¬ i < (expandChipTail (memorySourceTemplate12 b) b cv pv orbit H 2).w := hi
      have h2 : ¬ i < (expandChipTail (memorySourceTemplate b) b (cv ∘ walkRawSwap) pv orbit H 2).w := hi
      rw [dif_neg h1, dif_neg h2]
  have hpb : E'.pub = E.pub := rfl
  have hEE : E' = { E with chal := fun j => E.chal (walkRawSwap j) } := by
    have h0 : E' = Env.mk E'.trace E'.traceNext E'.chal E'.pub := rfl
    rw [h0, htr, hnx]
    rfl
  have heq12 : (memorySourceTemplate12 b).equalityChecks = [] := rfl
  have heq : (memorySourceTemplate b).equalityChecks = [] := rfl
  have hext12 : (memorySourceTemplate12 b).extTransition ++ (memorySourceTemplate12 b).extDeg1 ++
      (memorySourceTemplate12 b).extDeg3 = [] := rfl
  have hext : (memorySourceTemplate b).extTransition ++ (memorySourceTemplate b).extDeg1 ++
      (memorySourceTemplate b).extDeg3 = [] := rfl
  rw [heq12, heq, hext12, hext]
  refine and_congr ?_ (and_congr ⟨fun _ g hg => by simp at hg, fun _ g hg => by simp at hg⟩
    (and_congr ⟨fun _ g hg => by simp at hg, fun _ g hg => by simp at hg⟩ ?_))
  · show (∀ g ∈ baseTransitionGates b, g.eval E = 0) ↔
      (∀ g ∈ baseTransitionGates b, g.eval E' = 0)
    exact forall₂_congr fun g hg => by
      rw [coeff_eval_congr E E' htr hnx hpb g (baseTransitionGates_chalFree b g hg)]
  · show (∀ g ∈ mixedTransitionGates12 (F := F) (K := K) b,
        g.eval (gatherEnv b memoryCol0 E) E = 0) ↔
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) b, g.eval (gatherEnv b memoryCol0 E') E' = 0)
    rw [mixedTransitionGates12_eq_rename, List.forall_mem_map, hEE, gather_swap]
    refine forall₂_congr fun g hg => ?_
    have key : ∀ eK : Env K,
        g.eval eK { E with chal := fun j => E.chal (walkRawSwap j) } = g.eval eK E := fun eK =>
      mixed_eval_congr_F eK E { E with chal := fun j => E.chal (walkRawSwap j) } rfl rfl rfl g
        (mixedTransitionGates_rawFree b g hg)
    rw [eval_renameChal, key]

theorem namedFinalMemoryRAP12_w {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (namedFinalMemoryRAP12 hn nodes b cv pv orbit kMem).rap.w = 205 := by
  show 182 + RAPPadding.extraWidth _ = 205
  rw [RAPPadding.extraWidth_firstRoundExtra]
  rfl

/-- **Final transport.**  The twelve-coin memory chip at `chalVal` accepts `Q` iff the deployed
memory chip at `chalVal ∘ walkRawSwap` accepts a trace with the same columns. -/
theorem namedFinalMemoryRAP12_satisfies_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ)
    (Q : Fin (namedFinalMemoryRAP12 hn nodes b cv pv orbit kMem).rap.w → F[X])
    (Q' : Fin (namedFinalMemoryRAP hn nodes b (cv ∘ walkRawSwap) pv orbit kMem).rap.w → F[X])
    (hQ : ∀ (i : ℕ) (h1 : i < (namedFinalMemoryRAP12 hn nodes b cv pv orbit kMem).rap.w)
      (h2 : i < (namedFinalMemoryRAP hn nodes b (cv ∘ walkRawSwap) pv orbit kMem).rap.w),
      Q ⟨i, h1⟩ = Q' ⟨i, h2⟩) :
    RAP.SatisfiesWithPreprocessing (namedFinalMemoryRAP12 hn nodes b cv pv orbit kMem) Q ↔
      RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP hn nodes b (cv ∘ walkRawSwap) pv orbit kMem) Q' := by
  unfold namedFinalMemoryRAP12 at Q hQ ⊢
  unfold namedFinalMemoryRAP at Q' hQ ⊢
  dsimp only
  refine (RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ _).trans
    (Iff.trans ?_ (RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ _).symm)
  refine and_congr (sourceMemoryRAP12_satisfies_iff b cv pv orbit _ _ _ ?_) ?_
  · intro i h1 h2
    exact hQ i _ _
  · refine forall_congr' fun j => ?_
    fin_cases j
    · show Q ⟨4, _⟩ = _ ↔ Q' ⟨4, _⟩ = _
      erw [hQ 4 _ _]; rfl
    · show Q ⟨5, _⟩ = _ ↔ Q' ⟨5, _⟩ = _
      erw [hQ 5 _ _]; rfl
    · show Q ⟨153, _⟩ = _ ↔ Q' ⟨153, _⟩ = _
      erw [hQ 153 _ _]; rfl
    · show Q ⟨154, _⟩ = _ ↔ Q' ⟨154, _⟩ = _
      erw [hQ 154 _ _]; rfl

end Equations

/-! ## 5. The twelve-coin chip family over the tuple -/

namespace DeployedChipFamily12

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

/-- **The twelve-coin deployed memory chip at tuple `c`**: `chalVal` is
`memoryChalValOfTuple12 b c` (walk coin at slot `9`). -/
def memoryChipAt12 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (c : OptimizedProductionChallengeTuple12 K F) (kMem : ℕ) : FixedPreprocessingRAP F :=
  namedFinalMemoryRAP12 hn nodes b (memoryChalValOfTuple12 b c) pubVal orbit kMem

/-- **Tuple transport.**  The twelve-coin chip at `c` accepts `Q` iff the deployed chip at the
memory view `walkView11 c` accepts a trace with the same columns. -/
theorem memoryChipAt12_satisfies_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (c : OptimizedProductionChallengeTuple12 K F) (kMem : ℕ)
    (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X])
    (Q' : Fin (DeployedChipFamily.memoryChipAt hn nodes b pubVal orbit (walkView11 c) kMem).rap.w →
      F[X])
    (hQ : ∀ (i : ℕ) (h1 : i < (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w)
      (h2 : i < (DeployedChipFamily.memoryChipAt hn nodes b pubVal orbit (walkView11 c) kMem).rap.w),
      Q ⟨i, h1⟩ = Q' ⟨i, h2⟩) :
    RAP.SatisfiesWithPreprocessing (memoryChipAt12 hn nodes b pubVal orbit c kMem) Q ↔
      RAP.SatisfiesWithPreprocessing
        (DeployedChipFamily.memoryChipAt hn nodes b pubVal orbit (walkView11 c) kMem) Q' := by
  unfold memoryChipAt12 at Q hQ ⊢
  unfold DeployedChipFamily.memoryChipAt at Q' hQ ⊢
  revert Q' hQ
  rw [← memoryChalValOfTuple12_swap]
  intro Q' hQ
  exact namedFinalMemoryRAP12_satisfies_iff hn nodes b _ pubVal orbit kMem Q Q' hQ

end DeployedChipFamily12

/-! ## 6. The honest walk-gate lemmas at slot `9` (`MemoryWalkLabelCanonical` ported) -/

section Canonical

open OptimizedMemoryCanonicalSatisfaction MemoryWalkLabelCanonical OptimizedMemorySameExecution

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- The canonical gathered environment at a swapped chalVal is the re-indexed one. -/
theorem canonicalGatheredEnv_swap (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (i : Fin R.problem.cfg.memRows) :
    canonicalGatheredEnv A nodes b (cv ∘ walkRawSwap) pv orbit i =
      { canonicalGatheredEnv A nodes b cv pv orbit i with
          chal := fun j => (canonicalGatheredEnv A nodes b cv pv orbit i).chal (walkSlotSwap j) } := by
  unfold canonicalGatheredEnv
  rw [memorySourceTemplate_col0']
  exact gather_swap b (canonicalPhysicalEnv A nodes b cv pv orbit i)

/-- **The four in-gate walk gates at slot `9` vanish on every canonical memory row**, under the
coordinate pins at the swapped chalVal (whose walk pin is the slot-`9` coordinate of `chalVal`,
`walkChallenge12_of_pins`). -/
theorem canonical_inGateWalkGates12 (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (P : MemoryChipAssignment A)
    (pins : ExactMemoryCoordinatePins A b (cv ∘ walkRawSwap) pv)
    (halign : MemoryOrbitAligned nodes orbit) (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ inGateWalkGates12 (F := F),
      g.eval (canonicalGatheredEnv A nodes b cv pv orbit i)
        (canonicalPhysicalEnv A nodes b cv pv orbit i) = 0 := by
  rw [inGateWalkGates12_eq_rename, List.forall_mem_map]
  intro g hg
  rw [eval_renameChal, ← canonicalGatheredEnv_swap]
  have hF : (canonicalPhysicalEnv A nodes b (cv ∘ walkRawSwap) pv orbit i) =
      { canonicalPhysicalEnv A nodes b cv pv orbit i with
          chal := fun j => (canonicalPhysicalEnv A nodes b cv pv orbit i).chal (walkRawSwap j) } :=
    rfl
  have hraw : PartAReadSets.mixedRawChals g = [] := by
    simp only [MemoryWalkLabel.inGateWalkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> rfl
  rw [mixed_eval_congr_F _ (canonicalPhysicalEnv A nodes b (cv ∘ walkRawSwap) pv orbit i)
    (canonicalPhysicalEnv A nodes b cv pv orbit i) rfl rfl rfl g hraw]
  exact canonical_inGateWalkGates A nodes hnodes b (cv ∘ walkRawSwap) pv orbit P pins halign i g hg

/-- What the swapped pins say at slot `9`: the walk pin is the slot-`9` coordinate of `cv`. -/
theorem walkChallenge12_of_pins (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (cv pv : ℕ → F)
    (pins : ExactMemoryCoordinatePins A b (cv ∘ walkRawSwap) pv) :
    (∑ k : Fin 3, cv (6 + 3 * 9 + (k : ℕ)) • b k) = R.memoryWalkAlpha := by
  rw [← pins.walkChallenge]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := walkRawSwap_coord 3 k k.isLt
  simp only [Function.comp_apply, this]
  rfl

end Canonical

end

end Nock.NockVMROM.Thm54.PartA12
