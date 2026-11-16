import Nock.NockVMROM.Thm54.NockGigaRAP
import Nock.NockVMROM.Thm54.IOChipSoundness

/-!
# The giga-RAP with the **prover-committed finite-field** IO chips substituted in

`NockGigaRAP.lean` assembles the two chips of one Nock proof out of the *symbolic* IO AIRs
`Trans.ioProgAIR` / `Trans.ioMemAIR`, whose per-row fraction column is verifier-reconstructed as
`SetEq.frac` over `RatFunc L` and which therefore carry `numChallenges = 0` and **no inverse
gate**.  `IOChipSoundness.io_lio_of_satisfies` proves the hostile direction of the LogUp argument
for the *other* pair — `FiniteIO.finiteIOProgAIR m` / `finiteIOMemAIR m`, `m + 4` columns, two
sampled challenges, one public terminal, with a genuine inverse gate.  This module reassembles the
two combined AIRs on that pair, so the soundness theorem applies to the *assembled* object.

## The substitution, in numbers

|  | `numTraceCols` | `numChallenges` | `numPublic` | constraints |
|---|---|---|---|---|
| `Trans.ioProgAIR`      | 2 | 0 | 1 | 3 |
| `FiniteIO.finiteIOProgAIR m` | `m + 4` | 2 | 1 | 4 |
| `Trans.ioMemAIR`       | 3 | 0 | 2 | 3 |
| `FiniteIO.finiteIOMemAIR m`  | `m + 4` | 2 | 1 | 6 |

At the record width `m = 8` (`Walk.rlc` over `Fin 8`; `interRecords` is a
`FiniteIO.PreChallengeRecords K 9`, `PairedRecordCountedEvent.lean:200`) that is `12` columns per
IO block, so `computeCombinedAIR`'s `102` becomes `112` and `memoryCombinedAIR`'s `44` becomes
`53`.  The memory side also *loses* a public value (`2 → 1`), so its `numPublic` drops `4 → 3`.

## What becomes live, and where the placement lives

`NockGigaRAP.lean:157` says of the mem-IO challenge map "`ioMemAIR.numChallenges = 0`, so this map
is vacuous", and `ComputeStagedTable.lean:59` says the same for the prog side.  With the finite
chips the map is **not** vacuous: each IO block reads two challenge slots — `chal 0` the record-RLC
coin `γ` and `chal 1` the LogUp pole (`FiniteFieldIOAIR.lean:58`, `ioRowEnv`'s `chal`) — which must
land somewhere in the proof's coin space.

**They are not among `nockChronology`'s eight coins.**  That is wrong twice over: slots `6` and `7` are the memory table's
own internal `intermediate` pole and record-RLC coin — the two components of
`PairedRecordCountedEvent.interCoins` (`:210`), whose disclosure receipt
`interCoins_is_the_table_pole_not_the_io_sample` (`PairedRecordCountedEvent.lean:243`) says they
are *not* the `RAP_prog-IO` sample of the paper — and this tree pins `ChallengeVector.β := 0`
(`GenTierAConfig769.lean:89`), so a placement onto slot `6` would make the "sampled" pole the
constant `0`.  The two IO coins are two **new** slots of the ten-coin chronology
`IOCoinReconciliation.Chronology.nockChronologyWithIO` (`IOCoinReconciliation.lean:459`), riding
the final verifier message: after `Com(IO_prog)` and before `acc_prog`.

So the coin space is **not** decided in this module: the AIRs take the declared coin count `nc`
and the renaming `fC` as parameters, and `GigaRAPIOSlots.lean` — which imports this module and
`IOCoinReconciliation` — carries `IOSlots` over `Fin 10`, the canonical placement
`![ioGammaSlot, ioPoleSlot]`, the two staged chips, and the composition with
`IOCoinReconciliation.io_lio_of_satisfies_at_production_coins`.

## One column moves block

The symbolic IO block's second column is a *row fraction*, whose honest value
`SetEq.frac` reads no verifier coin, so it was an **ext** (round-1) column
(`ComputeStagedTable.lean:853`, `NockGigaRAP.lean:360`).  The finite chip's column `1` is the
committed **reciprocal** `1/(pole + RLC^γ(record))`, which reads both sampled coins, so it is a
**mega-ext** (round-2) column.  That is why the new width vectors are `![11, 88, 13]` and
`![9, 26, 18]` rather than the old `![11, 80, 11]` / `![9, 19, 16]` with `10` (resp. `9`) columns
simply appended to round 1.
-/

namespace Nock.NockVMROM.Thm54.GigaFinite

variable {K : Type*} [Field K]

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.Reified.Trans
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.FiniteIO
open scoped Polynomial

/-! ## 1. The schedule facts the placement has to respect

The **placement itself lives downstream**, in `GigaRAPIOSlots.lean`, because the two
`RAP_prog-IO` coins of the paper are *not* among `nockChronology`'s eight: slots `6` and `7`
are the memory table's own `β` and `γ` (the two components of
`PairedRecordCountedEvent.interCoins`, `:210`), and `interCoins` is explicitly not the IO sample
(`interCoins_is_the_table_pole_not_the_io_sample`, `PairedRecordCountedEvent.lean:243`).  So the
IO coins are two *new* slots on the ten-coin chronology
`IOCoinReconciliation.Chronology.nockChronologyWithIO` (`IOCoinReconciliation.lean:459`), and this
module carries only the coin-free part: the AIRs (generic in the declared coin count `nc` and in
the renaming `fC`), the census, the degree, and the fold.

What survives here are the three facts about `nockSampledAfter` that the ten-slot schedule
inherits through `Chronology.withIO_restricts` (`IOCoinReconciliation.lean:475`). -/

/-- Every coin of `nockChronology` is delivered by one of the two verifier messages, hence is
available to any round-`2` column. -/
theorem nockSampledAfter_lt_two : ∀ j : Fin 8, (nockSampledAfter j : ℕ) < 2 := by decide

/-- The round-`1`-usable coins of the compute chip. -/
theorem computeRoundOne_coins : ∀ j : Fin 8, j ∈ ({1, 2, 3, 4} : Finset (Fin 8)) →
    (nockSampledAfter j : ℕ) < 1 := by decide

/-- The round-`1`-usable coin of the memory chip. -/
theorem memoryRoundOne_coins : ∀ j : Fin 8, j ∈ ({1} : Finset (Fin 8)) →
    (nockSampledAfter j : ℕ) < 1 := by decide

/-- **The teeth of injectivity of a placement.**  Had the two IO coins been placed on one slot,
every challenge valuation would force `gamma = pole`; the LogUp pole would be the compression coin
itself.  Stated on the bare renaming, so it applies to any coin space. -/
theorem collapsed_placement_identifies_coins {K : Type*} [Field K]
    (f : ℕ → ℕ) (hf : f 0 = f 1) (cv : ℕ → K) : cv (f 0) = cv (f 1) := by rw [hf]

/-! ### Why the placement is a `remapBlock` and not always a `shiftBlock`

`Expr.remapBlock` with a constant challenge offset **is** `Expr.shiftBlock`
(`Expr.remapBlock_eq_shiftBlock`, `NockGigaRAP.lean:103`), so nothing about the walk blocks had to
be reproved.  A constant offset cannot express an arbitrary placement, though: it sends the
record-RLC coin to `offC` and the pole to `offC + 1`, in that order, so no offset realizes a
placement that puts the pole *before* the record-RLC coin.  `GigaRAPIOSlots.lean` exhibits both —
the canonical placement `(8, 9)` **is** the shift by `8`, and its transpose `(9, 8)` is a legal
placement that is not a shift. -/

/-- A constant challenge offset is a placement, definitionally. -/
theorem shift_is_a_placement (offC : ℕ) (e : Expr) :
    e.remapBlock ComputeChip.ioTraceOff (· + offC) ComputeChip.ioPubOff
      = e.shiftBlock ComputeChip.ioTraceOff offC ComputeChip.ioPubOff :=
  congrFun (Expr.remapBlock_eq_shiftBlock _ _ _) e

/-! ## 2. The variable-range facts of the two finite IO chips

These are the finite analogues of `ComputeChip.ioProgAIR_varsBelow` (`ComputeStagedTable.lean:357`,
columns `< 2`, no challenges, publics `< 1`) and `GigaChips.ioMemAIR_varsBelow`
(`NockGigaRAP.lean:240`, columns `< 3`, no challenges, publics `< 2`).  The bounds move to
columns `< m + 4`, challenges `< 2`, publics `< 1`, and — unlike the symbolic ones, which are
`rfl` on a closed term — they are proved **for every `m`**, by induction through the record-RLC
gate. -/

/-- The reified record-RLC gate reads challenge `0` and the record columns `base … base + m − 1`
and nothing else. -/
theorem rlcExpr_varsBelow (nc np : ℕ) (hc : 0 < nc) :
    ∀ (m base nt : ℕ), base + m ≤ nt →
      (Nock.NockVMROM.Thm54.FiniteIO.rlcExpr m base).varsBelow nt nc np = true := by
  intro m
  induction m with
  | zero => intro base nt _; rfl
  | succ k ih =>
    intro base nt h
    simp only [Nock.NockVMROM.Thm54.FiniteIO.rlcExpr, Expr.varsBelow, Nock.Reified.chl,
      Nock.Reified.tc, Bool.and_eq_true, Nat.blt_eq]
    exact ⟨ih base nt (by omega), hc, by omega⟩

/-- **Every `finiteIOProgAIR m` gate reads only columns `< m + 4`, challenges `< 2`, public `0`.**
Generic in `m`. -/
theorem finiteIOProgAIR_varsBelow (m : ℕ) :
    (finiteIOProgAIR m).constraints.all (fun c => c.expr.varsBelow (m + 4) 2 1) = true := by
  simp only [finiteIOProgAIR, List.all_cons, List.all_nil, ioAccInit, ioInvPin, ioProgAccStep,
    ioTerm, Expr.varsBelow, Nock.Reified.chl, Nock.Reified.tc, Nock.Reified.Trans.tn,
    Nock.Reified.Trans.pubv, Bool.and_eq_true, Nat.blt_eq, Bool.and_true]
  exact ⟨by omega, ⟨⟨by omega, rlcExpr_varsBelow 2 1 (by omega) m 4 (m + 4) (by omega)⟩,
      by omega⟩, ⟨⟨by omega, by omega⟩, by omega⟩, by omega, by omega⟩

/-- **Every `finiteIOMemAIR m` gate reads only columns `< m + 4`, challenges `< 2`, public `0`.**
Generic in `m`. -/
theorem finiteIOMemAIR_varsBelow (m : ℕ) :
    (finiteIOMemAIR m).constraints.all (fun c => c.expr.varsBelow (m + 4) 2 1) = true := by
  simp only [finiteIOMemAIR, List.all_cons, List.all_nil, ioAccInit, ioInvPin, ioMemAccStep,
    ioMultBool, ioMultInvPin, ioTerm, Expr.varsBelow, Nock.Reified.chl, Nock.Reified.tc,
    Nock.Reified.Trans.tn, Nock.Reified.Trans.pubv, Bool.and_eq_true, Nat.blt_eq, Bool.and_true]
  refine ⟨by omega, ⟨⟨by omega, rlcExpr_varsBelow 2 1 (by omega) m 4 (m + 4) (by omega)⟩,
      by omega⟩, ?_⟩
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ## 3. The two combined AIRs with the finite IO chips substituted in -/

/-- **The combined compute AIR with the prover-committed prog-IO chip.**

The declared challenge-interface size is the parameter `nc`: the combined AIR's coin space is the
*proof's* coin space, and how many coins that is depends on the chronology the chips are staged
over, not on this AIR's constraint list.  `nc` is inert for satisfaction — `airToRAP`
(`Nock/Framework/NockInstances.lean:307`) never reads `AIR.numChallenges` — so every census and
degree statement below is generic in it, and `GigaRAPIOSlots.lean` instantiates it at the ten
coins of `IOCoinReconciliation.Chronology.nockChronologyWithIO`.  It is **not** `8`: none of
`nockChronology`'s eight coins is the `RAP_prog-IO` pair of the paper (see the module header). -/
def computeCombinedFiniteAIR (nc m : ℕ) (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols  := m + 104
  numChallenges := nc
  numPublic     := 3
  constraints :=
    computeAIRchained.constraints
      ++ walkAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
            ComputeChip.walkPubOff⟩)
      ++ (finiteIOProgAIR m).constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff⟩)

/-- **The combined memory AIR with the prover-committed mem-IO chip.**

`numPublic` **drops** from `memoryCombinedAIR`'s `4` to `3`: the symbolic `ioMemAIR` had two
publics (`responses`, `out_mem`), the finite chip has one (the shared terminal). -/
noncomputable def memoryCombinedFiniteAIR (nc m : ℕ) (fC : ℕ → ℕ) : Reified.AIR where
  numTraceCols  := m + 46
  numChallenges := nc
  numPublic     := 3
  constraints :=
    (memoryAIRchained (K := K)).constraints.map
        (fun c => ⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩)
      ++ walkAIR.constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩)
      ++ (finiteIOMemAIR m).constraints.map
          (fun c => ⟨c.kind, c.expr.remapBlock memIoTraceOff fC memIoPubOff⟩)

@[simp] theorem computeCombinedFiniteAIR_numTraceCols (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).numTraceCols = m + 104 := rfl
@[simp] theorem computeCombinedFiniteAIR_numChallenges (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).numChallenges = nc := rfl
@[simp] theorem computeCombinedFiniteAIR_numPublic (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).numPublic = 3 := rfl
@[simp] theorem memoryCombinedFiniteAIR_numTraceCols (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols = m + 46 := rfl
@[simp] theorem memoryCombinedFiniteAIR_numChallenges (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).numChallenges = nc := rfl
@[simp] theorem memoryCombinedFiniteAIR_numPublic (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).numPublic = 3 := rfl

/-- At the record width `m = 8` the compute chip is **112** columns wide (was `102`). -/
theorem computeCombinedFiniteAIR_width_eight (nc : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc 8 fC).numTraceCols = 112 := rfl

/-- At the record width `m = 8` the memory chip is **54** columns wide (was `44`). -/
theorem memoryCombinedFiniteAIR_width_eight (nc : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc 8 fC).numTraceCols = 54 := rfl

/-! ### The census, measured

Every count below is generic in `m` and in the placement `fC`: neither the number of constraints
nor their kinds depends on the record width or on where the coins sit. -/

set_option maxRecDepth 400000 in
/-- **538 constraints**: `527 + 7 + 4` (was `537 = 527 + 7 + 3`; the finite prog chip adds the
inverse gate). -/
theorem computeCombinedFiniteAIR_num_constraints (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).constraints.length = 538 := by rfl

set_option maxRecDepth 400000 in
/-- **93 constraints**: `80 + 7 + 6` (was `90 = 80 + 7 + 3`; the finite mem chip adds the inverse
gate, the multiplicity booleanity and the multiplicity-inverse gate). -/
theorem memoryCombinedFiniteAIR_num_constraints (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.length = 93 := by rfl

set_option maxRecDepth 400000 in
/-- **The compute per-kind census.**  `.row` is unchanged at compute's `526` — every finite IO gate
is `.boundary`/`.transition`/`.terminal`.  `.transition` moves `5 → 6`: compute's `ln` hand-off,
the walk's three steps, and now **two** prog-IO transitions (the inverse pin and the accumulator
step) where the symbolic chip had one.  `.boundary` (`4`) and `.terminal` (`2`) are unchanged. -/
theorem computeCombinedFiniteAIR_kind_census (nc m : ℕ) (fC : ℕ → ℕ) :
    ((computeCombinedFiniteAIR nc m fC).constraints.filter (fun c => c.kind == .row)).length = 526 ∧
      ((computeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .transition)).length = 6 ∧
      ((computeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .boundary)).length = 4 ∧
      ((computeCombinedFiniteAIR nc m fC).constraints.filter
        (fun c => c.kind == .terminal)).length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- **The memory per-kind census.**  `.row` unchanged at `75`; `.transition` moves `5 → 8` (the
memory LogUp chaining gate, the walk's three steps, and the finite chip's four: inverse pin,
multiplicity booleanity, multiplicity-inverse pin, accumulator step); `.boundary` (`7`) and
`.terminal` (`3`) unchanged. -/
theorem memoryCombinedFiniteAIR_kind_census (nc m : ℕ) (fC : ℕ → ℕ) :
    (((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.filter (fun c => c.kind == .row)).length = 75 ∧
      (((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.filter
        (fun c => c.kind == .transition)).length = 8 ∧
      (((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.filter
        (fun c => c.kind == .boundary)).length = 7 ∧
      (((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.filter
        (fun c => c.kind == .terminal)).length = 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 400000 in
/-- The same compute census through `kindSeg`, the form `SegmentedRAPParams.rap` consumes. -/
theorem computeCombinedFiniteAIR_kindSeg_census (nc m : ℕ) (fC : ℕ → ℕ) :
    (kindSeg (computeCombinedFiniteAIR nc m fC) .row).constraints.length = 526 ∧
      (kindSeg (computeCombinedFiniteAIR nc m fC) .transition).constraints.length = 6 ∧
      (kindSeg (computeCombinedFiniteAIR nc m fC) .boundary).constraints.length = 4 ∧
      (kindSeg (computeCombinedFiniteAIR nc m fC) .terminal).constraints.length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 400000 in
/-- The same memory census through `kindSeg`. -/
theorem memoryCombinedFiniteAIR_kindSeg_census (nc m : ℕ) (fC : ℕ → ℕ) :
    (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .row).constraints.length = 75 ∧
      (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .transition).constraints.length = 8 ∧
      (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .boundary).constraints.length = 7 ∧
      (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .terminal).constraints.length = 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `526 + 6 + 4 + 2 = 538`.  Derived from the two censuses rather than by one large kernel
reduction (which exceeds the heartbeat budget). -/
theorem computeCombinedFiniteAIR_census_total (nc m : ℕ) (fC : ℕ → ℕ) :
    (kindSeg (computeCombinedFiniteAIR nc m fC) .row).constraints.length
        + (kindSeg (computeCombinedFiniteAIR nc m fC) .transition).constraints.length
        + (kindSeg (computeCombinedFiniteAIR nc m fC) .boundary).constraints.length
        + (kindSeg (computeCombinedFiniteAIR nc m fC) .terminal).constraints.length
      = (computeCombinedFiniteAIR nc m fC).constraints.length := by
  obtain ⟨h1, h2, h3, h4⟩ := computeCombinedFiniteAIR_kindSeg_census nc m fC
  rw [h1, h2, h3, h4, computeCombinedFiniteAIR_num_constraints]

/-- `75 + 8 + 7 + 3 = 93`. -/
theorem memoryCombinedFiniteAIR_census_total (nc m : ℕ) (fC : ℕ → ℕ) :
    (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .row).constraints.length
        + (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .transition).constraints.length
        + (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .boundary).constraints.length
        + (kindSeg ((memoryCombinedFiniteAIR (K := K)) nc m fC) .terminal).constraints.length
      = ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints.length := by
  obtain ⟨h1, h2, h3, h4⟩ := memoryCombinedFiniteAIR_kindSeg_census (K := K) nc m fC
  have hl := memoryCombinedFiniteAIR_num_constraints (K := K) nc m fC
  rw [h1, h2, h3, h4, hl]

/-! ### The constraint degree

`AIR.maxDegree` of the substituted AIRs **cannot** be obtained by kernel reduction the way
`computeCombinedAIR_maxDegree` (`ComputeStagedTable.lean:326`) is: with a symbolic placement `fC`
the `whnf` of the fold does not terminate inside the heartbeat budget (measured: it exceeds
`2000000` heartbeats even at `m = 8`, while the same statement at `fC = id` reduces fine).  So the
degree is computed *structurally* instead, which also makes it generic in `m` and `fC`. -/

/-- The running maximum `AIR.maxDegree` folds. -/
def degFold (l : List Reified.Constraint) : ℕ :=
  l.foldr (fun c acc => max c.expr.degree acc) 0

theorem maxDegree_eq_degFold (air : Reified.AIR) : air.maxDegree = degFold air.constraints := rfl

theorem degFold_append (a b : List Reified.Constraint) :
    degFold (a ++ b) = max (degFold a) (degFold b) := by
  induction a with
  | nil => simp [degFold]
  | cons c t ih =>
    simp only [degFold, List.cons_append, List.foldr_cons] at *
    rw [ih, ← max_assoc]

/-- Block placement by an arbitrary challenge renaming is a rename, so it does not move the fold. -/
theorem degFold_map_remap (offT : ℕ) (fC : ℕ → ℕ) (offP : ℕ) (l : List Reified.Constraint) :
    degFold (l.map (fun c => ⟨c.kind, c.expr.remapBlock offT fC offP⟩)) = degFold l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, degFold, List.foldr_cons] at *
    rw [ih, Expr.degree_remapBlock]

theorem degFold_map_shift (offT offC offP : ℕ) (l : List Reified.Constraint) :
    degFold (l.map (fun c => ⟨c.kind, c.expr.shiftBlock offT offC offP⟩)) = degFold l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, degFold, List.foldr_cons] at *
    rw [ih, Expr.degree_shiftBlock]

/-- **The substituted compute AIR's degree is the max of its three blocks' degrees**, for every
record width and every placement. -/
theorem computeCombinedFiniteAIR_maxDegree_eq (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).maxDegree
      = max (max computeAIRchained.maxDegree walkAIR.maxDegree)
          (finiteIOProgAIR m).maxDegree := by
  simp only [maxDegree_eq_degFold]
  show degFold ((_ ++ _) ++ _) = _
  rw [degFold_append, degFold_append, degFold_map_shift, degFold_map_remap]

/-- Likewise on the memory side. -/
theorem memoryCombinedFiniteAIR_maxDegree_eq (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).maxDegree
      = max (max (memoryAIRchained (K := K)).maxDegree walkAIR.maxDegree)
          (finiteIOMemAIR m).maxDegree := by
  simp only [maxDegree_eq_degFold]
  show degFold ((_ ++ _) ++ _) = _
  rw [degFold_append, degFold_append, degFold_map_remap, degFold_map_remap,
    degFold_map_remap]

/-- The record-RLC gate is degree `≤ 1` in trace variables: `chal 0 ^ c` is degree `0`. -/
theorem rlcExpr_degree_le_one :
    ∀ (m base : ℕ), (Nock.NockVMROM.Thm54.FiniteIO.rlcExpr m base).degree ≤ 1 := by
  intro m
  induction m with
  | zero => intro base; exact Nat.zero_le 1
  | succ k ih =>
    intro base
    show max ((Nock.NockVMROM.Thm54.FiniteIO.rlcExpr k base).degree) _ ≤ 1
    refine max_le (ih base) ?_
    show k * 0 + 1 ≤ 1
    omega

/-- **Both finite IO chips are degree `≤ 2`, for every `m`.**  The inverse gate is the only
degree-`2` gate: `(pole + RLC^γ(record)) · inv`. -/
theorem finiteIOProgAIR_maxDegree_le (m : ℕ) : (finiteIOProgAIR m).maxDegree ≤ 2 := by
  show max _ (max _ (max _ (max _ 0))) ≤ 2
  refine max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioAccInit, Nock.Reified.tc,
    Expr.degree]) (max_le ?_ (max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioProgAccStep,
      Nock.Reified.tc, Nock.Reified.Trans.tn, Expr.degree])
    (max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioTerm, Nock.Reified.tc,
      Nock.Reified.Trans.pubv, Expr.degree]) (Nat.zero_le 2))))
  show max (max 0 ((Nock.NockVMROM.Thm54.FiniteIO.rlcExpr m 4).degree) + 1) 0 ≤ 2
  have := rlcExpr_degree_le_one m 4
  omega

theorem finiteIOMemAIR_maxDegree_le (m : ℕ) : (finiteIOMemAIR m).maxDegree ≤ 2 := by
  show max _ (max _ (max _ (max _ (max _ (max _ 0))))) ≤ 2
  refine max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioAccInit, Nock.Reified.tc,
    Expr.degree]) (max_le ?_ (max_le
      (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioMultBool, Nock.Reified.tc, Expr.degree])
      (max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioMultInvPin, Nock.Reified.tc,
        Expr.degree])
      (max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioMemAccStep, Nock.Reified.tc,
        Nock.Reified.Trans.tn, Expr.degree])
      (max_le (by norm_num [Nock.NockVMROM.Thm54.FiniteIO.ioTerm, Nock.Reified.tc,
        Nock.Reified.Trans.pubv, Expr.degree]) (Nat.zero_le 2))))))
  show max (max 0 ((Nock.NockVMROM.Thm54.FiniteIO.rlcExpr m 4).degree) + 1) 0 ≤ 2
  have := rlcExpr_degree_le_one m 4
  omega

/-- **Substituting the finite chip does not raise the constraint degree** — for *every* record
width `m` and *every* placement `fC`.  The maximum stays `computeAIRchained`'s `4`
(`Counts.lean:199`). -/
theorem computeCombinedFiniteAIR_maxDegree (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).maxDegree = 4 := by
  rw [computeCombinedFiniteAIR_maxDegree_eq]
  have hc : computeAIRchained.maxDegree = 4 := computeAIRchained_maxDegree
  have hw : walkAIR.maxDegree = 2 := by rfl
  have hi := finiteIOProgAIR_maxDegree_le m
  omega

/-- Likewise on the memory side: the maximum stays `memoryAIRchained`'s `4`. -/
theorem memoryCombinedFiniteAIR_maxDegree (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).maxDegree = 4 := by
  rw [memoryCombinedFiniteAIR_maxDegree_eq]
  have hc : (memoryAIRchained (K := K)).maxDegree = 4 := memoryAIRchained_maxDegree (K := K)
  have hw : walkAIR.maxDegree = 2 := by rfl
  have hi := finiteIOMemAIR_maxDegree_le m
  omega

set_option maxRecDepth 400000 in
/-- The compute block still survives folding verbatim — it is a literal prefix. -/
theorem computeCombinedFiniteAIR_compute_prefix (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).constraints.take 527 = computeAIRchained.constraints := by rfl

/-! ## 4. The block projections and the fold, generic in `m` and in the placement

Everything in this section is stated from **kinded vanishing** — `∀ c ∈ air.constraints, ∀ x ∈
q.domain c.kind, c.expr.eval … = 0`, the right-hand side of `StagedChip.satisfies_iff_kinded` —
so it needs neither the round schedule nor a concrete record width.  `GigaRAPIOSlots.lean`
instantiates it at the chips. -/

variable {L : Type*} [Field L]

theorem finProgChipWidth (nc m : ℕ) (fC : ℕ → ℕ) :
    (computeCombinedFiniteAIR nc m fC).numTraceCols = m + 104 := rfl

theorem finMemChipWidth (nc m : ℕ) (fC : ℕ → ℕ) :
    ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols = m + 46 := rfl

/-- The compute-table block of a substituted combined compute trace: columns `0…93`. -/
def finComputeBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) : Fin 94 → L[X] :=
  fun i => P ⟨i, by have := i.isLt; rw [finProgChipWidth]; omega⟩

/-- The compute-walk block: columns `94…99`. -/
def finWalkBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) : Fin 6 → L[X] :=
  fun i => P ⟨i + 94, by have := i.isLt; rw [finProgChipWidth]; omega⟩

/-- **The finite prog-IO block**: columns `100 … 103 + m`, the `m + 4` committed columns of
`finiteIOProgAIR m` (accumulator, reciprocal, the two multiplicity slots, then the record). -/
def finProgIoBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) :
    Fin (m + 4) → L[X] :=
  fun i => P ⟨i + 100, by have := i.isLt; rw [finProgChipWidth]; omega⟩

/-- The memory-table block of a substituted combined memory trace: columns `0…35`. -/
def finMemBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) : Fin 36 → L[X] :=
  fun i => P ⟨i, by have := i.isLt; rw [finMemChipWidth]; omega⟩

/-- The memory-walk block: columns `36…41`. -/
def finMemWalkBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) : Fin 6 → L[X] :=
  fun i => P ⟨i + 36, by have := i.isLt; rw [finMemChipWidth]; omega⟩

/-- **The finite mem-IO block**: columns `42 … 45 + m`. -/
def finMemIoBlock {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) :
    Fin (m + 4) → L[X] :=
  fun i => P ⟨i + 42, by have := i.isLt; rw [finMemChipWidth]; omega⟩

/-! ### Environment agreement, one block at a time -/

theorem eval_finCompute_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 94 5 0 = true) :
    e.eval (envOfTrace P ω x cv pv) = e.eval (envOfTrace (finComputeBlock P) ω x cv pv) := by
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have hw : i < m + 104 := by omega
    simp [envOfTrace, finComputeBlock, hw, hi]
  · intro i hi
    have hw : i < m + 104 := by omega
    simp [envOfTrace, finComputeBlock, hw, hi]

theorem eval_finWalk_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 6 1 2 = true) :
    (e.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
        ComputeChip.walkPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (finWalkBlock P) ω x
          (fun i => cv (i + ComputeChip.walkChalOff)) pv) := by
  rw [Reified.Expr.shiftBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have hw2 : i < m + 10 := by omega
    simp [Reified.Env.remap, Reified.blockShift, envOfTrace, finWalkBlock,
      ComputeChip.walkTraceOff, ComputeChip.walkPubOff, hw2, hi]
  · intro i hi
    have hw2 : i < m + 10 := by omega
    simp [Reified.Env.remap, Reified.blockShift, envOfTrace, finWalkBlock,
      ComputeChip.walkTraceOff, ComputeChip.walkPubOff, hw2, hi]

/-- **The prog-IO block, now with a live challenge map.**  Where `eval_io_block`
(`ComputeStagedTable.lean:598`) could leave the block's challenge valuation a *free parameter* —
`ioProgAIR.numChallenges = 0` — the finite chip reads two slots, so the recovered valuation is
`cv ∘ fC`: precisely the composition the placement determines. -/
theorem eval_finProgIo_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow (m + 4) 2 1 = true) :
    (e.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff).eval
        (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (finProgIoBlock P) ω x (fun i => cv (fC i))
          (fun i => pv (i + ComputeChip.ioPubOff))) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have hw2 : i < m + 4 := hi
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finProgIoBlock,
      ComputeChip.ioTraceOff, ComputeChip.ioPubOff, hw2]
  · intro i hi
    have hw2 : i < m + 4 := hi
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finProgIoBlock,
      ComputeChip.ioTraceOff, ComputeChip.ioPubOff, hw2]

theorem eval_finMem_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 36 9 0 = true) :
    (e.remapBlock memTraceOff memChalMap memPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (finMemBlock P) ω x (fun i => cv (memChalMap i)) pv) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl)
    (fun i hi => absurd hi (by omega))
  · intro i hi
    have hw : i < m + 46 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemBlock, memTraceOff, hw, hi]
  · intro i hi
    have hw : i < m + 46 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemBlock, memTraceOff, hw, hi]

theorem eval_finMemWalk_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow 6 1 2 = true) :
    (e.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (finMemWalkBlock P) ω x (fun i => cv (memWalkChalMap i)) pv) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have hw2 : i < m + 10 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemWalkBlock, memWalkTraceOff,
      memWalkPubOff, hw2, hi]
  · intro i hi
    have hw2 : i < m + 10 := by omega
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemWalkBlock, memWalkTraceOff,
      memWalkPubOff, hw2, hi]

/-- **The mem-IO block, now with a live challenge map.**  `NockGigaRAP.lean:566`'s
`eval_mem_io_block` carries a *second* free challenge valuation `cv'` precisely because
`ioMemAIR.numChallenges = 0`; here there is no such freedom. -/
theorem eval_finMemIo_block {nc m : ℕ} {fC : ℕ → ℕ}
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X]) (ω x : L)
    (cv pv : ℕ → L) (e : Reified.Expr) (he : e.varsBelow (m + 4) 2 1 = true) :
    (e.remapBlock memIoTraceOff fC memIoPubOff).eval (envOfTrace P ω x cv pv)
      = e.eval (envOfTrace (finMemIoBlock P) ω x (fun i => cv (fC i))
          (fun i => pv (i + memIoPubOff))) := by
  rw [Reified.Expr.remapBlock, Reified.Expr.eval_mapVars]
  refine Reified.Expr.eval_congr_of_varsBelow e he ?_ ?_ (fun i _ => rfl) (fun i _ => rfl)
  · intro i hi
    have hw2 : i < m + 4 := hi
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemIoBlock, memIoTraceOff,
      memIoPubOff, hw2]
  · intro i hi
    have hw2 : i < m + 4 := hi
    simp [Reified.Env.remap, Reified.blockRemap, envOfTrace, finMemIoBlock, memIoTraceOff,
      memIoPubOff, hw2]

/-! ### The block memberships -/

theorem finCompute_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ computeAIRchained.constraints) : c ∈ (computeCombinedFiniteAIR nc m fC).constraints := by
  simp only [computeCombinedFiniteAIR, List.mem_append]
  exact Or.inl (Or.inl hc)

theorem finWalk_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ walkAIR.constraints) :
    (⟨c.kind, c.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
        ComputeChip.walkPubOff⟩ : Reified.Constraint)
      ∈ (computeCombinedFiniteAIR nc m fC).constraints := by
  simp only [computeCombinedFiniteAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

theorem finProgIo_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ (finiteIOProgAIR m).constraints) :
    (⟨c.kind, c.expr.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff⟩ :
        Reified.Constraint)
      ∈ (computeCombinedFiniteAIR nc m fC).constraints := by
  simp only [computeCombinedFiniteAIR, List.mem_append, List.mem_map]
  exact Or.inr ⟨c, hc, rfl⟩

theorem finMem_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ (memoryAIRchained (K := K)).constraints) :
    (⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩ : Reified.Constraint)
      ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints := by
  simp only [memoryCombinedFiniteAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨c, hc, rfl⟩)

theorem finMemWalk_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ walkAIR.constraints) :
    (⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩ :
        Reified.Constraint)
      ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints := by
  simp only [memoryCombinedFiniteAIR, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

theorem finMemIo_mem_combined {nc m : ℕ} {fC : ℕ → ℕ} {c : Reified.Constraint}
    (hc : c ∈ (finiteIOMemAIR m).constraints) :
    (⟨c.kind, c.expr.remapBlock memIoTraceOff fC memIoPubOff⟩ : Reified.Constraint)
      ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints := by
  simp only [memoryCombinedFiniteAIR, List.mem_append, List.mem_map]
  exact Or.inr ⟨c, hc, rfl⟩

/-! ### The fold: the six block RAPs, recovered

Each of the six is stated in **agreement form** — the recovered RAP may use any parameters sharing
the combined chip's `ω` and per-kind domains and agreeing with it on the block's own challenge and
public slots.  For the two IO blocks the challenge agreement is `qi.chalVal i = q.chalVal (fC i)`;
this is the hypothesis that was *absent* from `fold_gives_io` / `fold_gives_memIo`, whose IO chips
had no challenges to agree about. -/

theorem fold_gives_finCompute {nc m : ℕ} {fC : ℕ → ℕ} (q qc : SegmentedRAPParams L)
    (hω : qc.ω = q.ω) (hcv : ∀ i, i < 5 → qc.chalVal i = q.chalVal i)
    (hdom : ∀ kind, qc.domain kind = q.domain kind)
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ (computeCombinedFiniteAIR nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qc.rap computeAIRchained kind).Satisfies (finComputeBlock P) := by
  show ∀ kind, (airToRAP (kindSeg computeAIRchained kind) qc.chalVal qc.pubVal qc.eDeg qc.hExp
      qc.ω qc.βcoset (qc.domain kind) qc.βcoset_ne_zero qc.hExp_pos).Satisfies (finComputeBlock P)
  refine (segmented_is_kinded computeAIRchained qc.chalVal qc.pubVal qc.eDeg qc.hExp qc.ω
    qc.βcoset qc.βcoset_ne_zero qc.hExp_pos qc.domain (finComputeBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 94 5 0 = true :=
    (List.all_eq_true.mp ComputeChip.computeAIRchained_varsBelow) c hc
  have hzero := h c (finCompute_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  refine Eq.trans ?_ hzero
  refine Eq.trans ?_ (eval_finCompute_block P q.ω x q.chalVal q.pubVal c.expr hvb).symm
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => absurd hi (by omega))

theorem fold_gives_finWalk {nc m : ℕ} {fC : ℕ → ℕ} (q qw : SegmentedRAPParams L)
    (hω : qw.ω = q.ω)
    (hcv : ∀ i, i < 1 → qw.chalVal i = q.chalVal (i + ComputeChip.walkChalOff))
    (hpv : ∀ i, i < 2 → qw.pubVal i = q.pubVal (i + ComputeChip.walkPubOff))
    (hdom : ∀ kind, qw.domain kind = q.domain kind)
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ (computeCombinedFiniteAIR nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qw.rap walkAIR kind).Satisfies (finWalkBlock P) := by
  show ∀ kind, (airToRAP (kindSeg walkAIR kind) qw.chalVal qw.pubVal qw.eDeg qw.hExp
      qw.ω qw.βcoset (qw.domain kind) qw.βcoset_ne_zero qw.hExp_pos).Satisfies (finWalkBlock P)
  refine (segmented_is_kinded walkAIR qw.chalVal qw.pubVal qw.eDeg qw.hExp qw.ω
    qw.βcoset qw.βcoset_ne_zero qw.hExp_pos qw.domain (finWalkBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c hc
  have hzero : (c.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
      ComputeChip.walkPubOff).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    h ⟨c.kind, c.expr.shiftBlock ComputeChip.walkTraceOff ComputeChip.walkChalOff
        ComputeChip.walkPubOff⟩ (finWalk_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_finWalk_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

/-- **The hook.**  This is `ComputeStagedTable.lean:688`'s `fold_gives_io` re-proved at
`finiteIOProgAIR m`, and its conclusion is *literally* the hypothesis `hsatP` of
`IOChipSoundness.io_lio_of_satisfies` (`IOChipSoundness.lean:413`).  The new hypothesis is `hcv`:
the two coin slots the finite chip reads must be the two the placement `fC` sends them to. -/
theorem fold_gives_finProgIo {nc m : ℕ} {fC : ℕ → ℕ} (q qi : SegmentedRAPParams L)
    (hω : qi.ω = q.ω) (hcv : ∀ i, i < 2 → qi.chalVal i = q.chalVal (fC i))
    (hpv : ∀ i, i < 1 → qi.pubVal i = q.pubVal (i + ComputeChip.ioPubOff))
    (hdom : ∀ kind, qi.domain kind = q.domain kind)
    (P : Fin (computeCombinedFiniteAIR nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ (computeCombinedFiniteAIR nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qi.rap (finiteIOProgAIR m) kind).Satisfies (finProgIoBlock P) := by
  show ∀ kind, (airToRAP (kindSeg (finiteIOProgAIR m) kind) qi.chalVal qi.pubVal qi.eDeg qi.hExp
      qi.ω qi.βcoset (qi.domain kind) qi.βcoset_ne_zero qi.hExp_pos).Satisfies (finProgIoBlock P)
  refine (segmented_is_kinded (finiteIOProgAIR m) qi.chalVal qi.pubVal qi.eDeg qi.hExp qi.ω
    qi.βcoset qi.βcoset_ne_zero qi.hExp_pos qi.domain (finProgIoBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow (m + 4) 2 1 = true :=
    (List.all_eq_true.mp (finiteIOProgAIR_varsBelow m)) c hc
  have hzero : (c.expr.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    h ⟨c.kind, c.expr.remapBlock ComputeChip.ioTraceOff fC ComputeChip.ioPubOff⟩
      (finProgIo_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_finProgIo_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

theorem fold_gives_finMem {nc m : ℕ} {fC : ℕ → ℕ} (q qm : SegmentedRAPParams L)
    (hω : qm.ω = q.ω) (hcv : ∀ i, i < 9 → qm.chalVal i = q.chalVal (memChalMap i))
    (hdom : ∀ kind, qm.domain kind = q.domain kind)
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qm.rap (memoryAIRchained (K := K)) kind).Satisfies (finMemBlock P) := by
  show ∀ kind, (airToRAP (kindSeg (memoryAIRchained (K := K)) kind) qm.chalVal qm.pubVal qm.eDeg qm.hExp
      qm.ω qm.βcoset (qm.domain kind) qm.βcoset_ne_zero qm.hExp_pos).Satisfies (finMemBlock P)
  refine (segmented_is_kinded (memoryAIRchained (K := K)) qm.chalVal qm.pubVal qm.eDeg qm.hExp qm.ω
    qm.βcoset qm.βcoset_ne_zero qm.hExp_pos qm.domain (finMemBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 36 9 0 = true :=
    (List.all_eq_true.mp memoryAIRchained_varsBelow) c hc
  have hzero : (c.expr.remapBlock memTraceOff memChalMap memPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    h ⟨c.kind, c.expr.remapBlock memTraceOff memChalMap memPubOff⟩
      (finMem_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_finMem_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => absurd hi (by omega))

theorem fold_gives_finMemWalk {nc m : ℕ} {fC : ℕ → ℕ} (q qw : SegmentedRAPParams L)
    (hω : qw.ω = q.ω) (hcv : ∀ i, i < 1 → qw.chalVal i = q.chalVal (memWalkChalMap i))
    (hpv : ∀ i, i < 2 → qw.pubVal i = q.pubVal (i + memWalkPubOff))
    (hdom : ∀ kind, qw.domain kind = q.domain kind)
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qw.rap walkAIR kind).Satisfies (finMemWalkBlock P) := by
  show ∀ kind, (airToRAP (kindSeg walkAIR kind) qw.chalVal qw.pubVal qw.eDeg qw.hExp
      qw.ω qw.βcoset (qw.domain kind) qw.βcoset_ne_zero qw.hExp_pos).Satisfies (finMemWalkBlock P)
  refine (segmented_is_kinded walkAIR qw.chalVal qw.pubVal qw.eDeg qw.hExp qw.ω
    qw.βcoset qw.βcoset_ne_zero qw.hExp_pos qw.domain (finMemWalkBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow 6 1 2 = true :=
    (List.all_eq_true.mp ComputeChip.walkAIR_varsBelow) c hc
  have hzero : (c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    h ⟨c.kind, c.expr.remapBlock memWalkTraceOff memWalkChalMap memWalkPubOff⟩
      (finMemWalk_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_finMemWalk_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

/-- **The memory-side hook**, the analogue of `fold_gives_finProgIo`: its conclusion is `hsatM` of
`IOChipSoundness.io_lio_of_satisfies`. -/
theorem fold_gives_finMemIo {nc m : ℕ} {fC : ℕ → ℕ} (q qi : SegmentedRAPParams L)
    (hω : qi.ω = q.ω) (hcv : ∀ i, i < 2 → qi.chalVal i = q.chalVal (fC i))
    (hpv : ∀ i, i < 1 → qi.pubVal i = q.pubVal (i + memIoPubOff))
    (hdom : ∀ kind, qi.domain kind = q.domain kind)
    (P : Fin ((memoryCombinedFiniteAIR (K := K)) nc m fC).numTraceCols → L[X])
    (h : ∀ c ∈ ((memoryCombinedFiniteAIR (K := K)) nc m fC).constraints, ∀ x ∈ q.domain c.kind,
        c.expr.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0) :
    ∀ kind, (qi.rap (finiteIOMemAIR m) kind).Satisfies (finMemIoBlock P) := by
  show ∀ kind, (airToRAP (kindSeg (finiteIOMemAIR m) kind) qi.chalVal qi.pubVal qi.eDeg qi.hExp
      qi.ω qi.βcoset (qi.domain kind) qi.βcoset_ne_zero qi.hExp_pos).Satisfies (finMemIoBlock P)
  refine (segmented_is_kinded (finiteIOMemAIR m) qi.chalVal qi.pubVal qi.eDeg qi.hExp qi.ω
    qi.βcoset qi.βcoset_ne_zero qi.hExp_pos qi.domain (finMemIoBlock P)).mpr ?_
  intro c hc x hx
  have hvb : c.expr.varsBelow (m + 4) 2 1 = true :=
    (List.all_eq_true.mp (finiteIOMemAIR_varsBelow m)) c hc
  have hzero : (c.expr.remapBlock memIoTraceOff fC memIoPubOff).eval
      (envOfTrace P q.ω x q.chalVal q.pubVal) = 0 :=
    h ⟨c.kind, c.expr.remapBlock memIoTraceOff fC memIoPubOff⟩
      (finMemIo_mem_combined hc) x (by rw [hdom] at hx; exact hx)
  rw [eval_finMemIo_block P q.ω x q.chalVal q.pubVal c.expr hvb] at hzero
  refine Eq.trans ?_ hzero
  exact Reified.Expr.eval_congr_of_varsBelow c.expr hvb
    (fun _ _ => rfl) (fun _ _ => by rw [hω]; rfl)
    (fun i hi => hcv i hi) (fun i hi => hpv i hi)

/-! ## 5. The round schedules at the record width `m = 8`

`m = 8` is the record width of this development: `Walk.rlc` compresses a `Fin node_size → K`
(`Walk.lean:198`) at `node_size = 8`, `NockVM.encRec` has the eight coordinates
`root.(size,dyck,leaf)`, `child.(size,dyck,leaf)`, `axis`, `ts` (read off `rlc_encRec`,
`PairedRecordCountedEvent.lean:216`), and `interRecords` is a `PreChallengeRecords K 9`
(`:200`).  So each IO block is `12` columns wide and the chips are `112` and `53` columns.

### Two columns change block, and one of them is a surprise

* the finite chip's **reciprocal** column (block column `1`) reads both sampled coins, so it is
  round `2`; the symbolic chip's row *fraction* read none and was round `1`;
* the **eighth record coordinate is `ts`** (`rlc_encRec`), the record timestamp `ln(i−1)·α^k`, so block column `4 + 7 = 11` reads the timestamp base and is round
  `2` — exactly as the memory table's own `mem.ts` column is (`mem_ts_column_round_two`,
  `NockGigaRAP.lean:342`).  Committing the record columns wholesale to the ext block would have
  declared that this column reads no round-1 coin, which is false.

The other seven record coordinates are fingerprints and the axis, which read the NPR seed `z` or
nothing, so they are round `1`; the two multiplicity columns are counts and are round `1` as
well.

The two `StagedChip`s themselves are built in `GigaRAPIOSlots.lean`, on the ten-coin chronology:
they need a `columnChallenges` field, and naming the coins is exactly what this module cannot do
(see the header). -/

/-- The **thirteen** mega-ext columns of the substituted compute chip: the eleven of
`ComputeChip.megaExtCols` (`ComputeStagedTable.lean:378`) plus the reciprocal `101` and the record
timestamp `111`. -/
def finMegaExtCols : List ℕ := [65, 66, 74, 82, 90, 94, 95, 96, 98, 99, 100, 101, 111]

theorem finMegaExtCols_nodup : finMegaExtCols.Nodup := by decide
theorem finMegaExtCols_length : finMegaExtCols.length = 13 := rfl

/-- The round assignment of the substituted compute chip. -/
def finComputeRoundOf (c : Fin 113) : Fin 3 :=
  if (c : ℕ) < 11 then 0 else if (c : ℕ) ∈ finMegaExtCols then 2 else 1

/-- **The substituted compute schedule.**  `width_eq` is a field, so `11 / 89 / 13` are the actual
column-fibre cardinalities, checked by `decide`. Form R record width `m = 9` is `113` columns. -/
def finComputeSchedule : RoundSchedule 113 3 where
  roundOf := finComputeRoundOf
  width := ![11, 89, 13]
  width_eq := by decide

theorem finComputeSchedule_width : finComputeSchedule.width = ![11, 89, 13] := rfl

/-- `w = Σ_r w_RAP(r)`: `11 + 89 + 13 = 113`. -/
theorem finComputeSchedule_total : (113 : ℕ) = ∑ r, finComputeSchedule.width r :=
  finComputeSchedule.total_width

/-- The ten coin-free columns of the substituted memory chip (form R `C'` at 35). -/
def finMemBaseCols : List ℕ := [0, 1, 2, 3, 19, 20, 21, 22, 29, 35]

/-- The **eighteen** mega-ext columns of the substituted memory chip: the sixteen of
`GigaChips.memMegaExtCols` (`NockGigaRAP.lean:280`) plus the reciprocal `43` and the record
timestamp `53`. -/
def finMemMegaExtCols : List ℕ :=
  [7, 8, 12, 13, 17, 18, 30, 31, 32, 33, 36, 37, 38, 40, 41, 42, 43, 53]

theorem finMemMegaExtCols_nodup : finMemMegaExtCols.Nodup := by decide
theorem finMemMegaExtCols_length : finMemMegaExtCols.length = 18 := rfl

/-- The round assignment of the substituted memory chip. -/
def finMemRoundOf (c : Fin 55) : Fin 3 :=
  if (c : ℕ) ∈ finMemBaseCols then 0 else if (c : ℕ) ∈ finMemMegaExtCols then 2 else 1

/-- **The substituted memory schedule.**  `10 / 27 / 18`, checked by `decide`. Form R `m = 9` is
`55` columns. -/
def finMemorySchedule : RoundSchedule 55 3 where
  roundOf := finMemRoundOf
  width := ![10, 27, 18]
  width_eq := by decide

theorem finMemorySchedule_width : finMemorySchedule.width = ![10, 27, 18] := rfl

/-- `w = Σ_r w_RAP(r)`: `10 + 27 + 18 = 55`. -/
theorem finMemorySchedule_total : (55 : ℕ) = ∑ r, finMemorySchedule.width r :=
  finMemorySchedule.total_width

/-- The reciprocal column of each chip is round `2`, where the symbolic row fraction was round `1`
(`ComputeStagedTable.lean:853`, `NockGigaRAP.lean:360`). -/
theorem reciprocal_columns_round_two :
    finComputeRoundOf 101 = 2 ∧ finMemRoundOf 43 = 2 := by decide

/-- The record's eighth coordinate is the timestamp, so it is round `2` on both chips. -/
theorem record_timestamp_columns_round_two :
    finComputeRoundOf 111 = 2 ∧ finMemRoundOf 53 = 2 := by decide

/-- The two multiplicity columns and the seven coin-light record coordinates are round `1`. -/
theorem finProgIo_ext_columns_round_one :
    finComputeRoundOf 102 = 1 ∧ finComputeRoundOf 103 = 1 ∧ finComputeRoundOf 104 = 1 ∧
      finComputeRoundOf 105 = 1 ∧ finComputeRoundOf 106 = 1 ∧ finComputeRoundOf 107 = 1 ∧
      finComputeRoundOf 108 = 1 ∧ finComputeRoundOf 109 = 1 ∧ finComputeRoundOf 110 = 1 := by
  decide

theorem finMemIo_ext_columns_round_one :
    finMemRoundOf 44 = 1 ∧ finMemRoundOf 45 = 1 ∧ finMemRoundOf 46 = 1 ∧
      finMemRoundOf 47 = 1 ∧ finMemRoundOf 48 = 1 ∧ finMemRoundOf 49 = 1 ∧
      finMemRoundOf 50 = 1 ∧ finMemRoundOf 51 = 1 ∧ finMemRoundOf 52 = 1 := by decide

/-- The accumulator column of each IO block stays round `2`. -/
theorem accumulator_columns_round_two :
    finComputeRoundOf 100 = 2 ∧ finMemRoundOf 42 = 2 := by decide


end Nock.NockVMROM.Thm54.GigaFinite

section Audit

open Nock.NockVMROM.Thm54.GigaFinite

#check @computeCombinedFiniteAIR
#check @memoryCombinedFiniteAIR
#check @computeCombinedFiniteAIR_num_constraints
#check @memoryCombinedFiniteAIR_num_constraints
#check @computeCombinedFiniteAIR_kind_census
#check @memoryCombinedFiniteAIR_kind_census
#check @finComputeSchedule
#check @finMemorySchedule
#check @fold_gives_finProgIo
#check @fold_gives_finMemIo

#print axioms Nock.NockVMROM.Thm54.GigaFinite.nockSampledAfter_lt_two
#print axioms Nock.NockVMROM.Thm54.GigaFinite.shift_is_a_placement
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finMegaExtCols_nodup
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finMemMegaExtCols_nodup
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finProgIo_ext_columns_round_one
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finMemIo_ext_columns_round_one
#print axioms Nock.NockVMROM.Thm54.GigaFinite.rlcExpr_varsBelow
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finiteIOProgAIR_varsBelow
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finiteIOMemAIR_varsBelow
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_num_constraints
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_num_constraints
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_kind_census
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_kind_census
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_kindSeg_census
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_kindSeg_census
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_census_total
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_census_total
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_maxDegree
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_maxDegree
#print axioms Nock.NockVMROM.Thm54.GigaFinite.computeCombinedFiniteAIR_width_eight
#print axioms Nock.NockVMROM.Thm54.GigaFinite.memoryCombinedFiniteAIR_width_eight
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finComputeSchedule_total
#print axioms Nock.NockVMROM.Thm54.GigaFinite.finMemorySchedule_total
#print axioms Nock.NockVMROM.Thm54.GigaFinite.reciprocal_columns_round_two
#print axioms Nock.NockVMROM.Thm54.GigaFinite.record_timestamp_columns_round_two
#print axioms Nock.NockVMROM.Thm54.GigaFinite.accumulator_columns_round_two
#print axioms Nock.NockVMROM.Thm54.GigaFinite.eval_finProgIo_block
#print axioms Nock.NockVMROM.Thm54.GigaFinite.eval_finMemIo_block
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finCompute
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finWalk
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finProgIo
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finMem
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finMemWalk
#print axioms Nock.NockVMROM.Thm54.GigaFinite.fold_gives_finMemIo

end Audit
