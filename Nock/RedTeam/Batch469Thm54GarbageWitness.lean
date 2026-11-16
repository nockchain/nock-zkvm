/-
  Nock/RedTeam/Batch469Thm54GarbageWitness.lean

  **Garbage beyond the prefix EXISTS at the walk gates and at
  Nock's `F_comp`; at the full deployed chip it is UNCONFIRMED.**

  The
  candidate that survives `F` is the SELF-CALLING CORE: `OP_9` `*[a 9 b 0 1]` with
  `/[b a] = [9 b 0 1]`.  Its children are
  `sf1 = *[a 0 1] = a` (a leaf) and `sf2 = *[a /[b a]] = *[a 9 b 0 1]` — ITSELF.  Honest Nock
  diverges on it, so no honest trace contains it; nothing in the per-row verifier `V_comp`
  says so, because `sf2_f` is read only through the memory record `mr3 = (sf1_e, sf2_f, b)`
  (`memBlk`, `:1879-1882`), i.e. through the IO argument, not row-locally.

  `fo = (0, 0, 2, 0, 2)`, `h = 5` — row 1 the honest root (a leaf
  program), row 2 a leaf `L`, row 3 the self-caller `N` with children `(L, N)`, row 4 a leaf
  `L'`, row 5 a self-caller `M` with children `(L', M)`.  Then `Sf = (0,0,2,2,4)`,
  `1 + Sf 5 = 5 = h` (tiling HOLDS), `BFSValid` fails at row 2, `prefixLen = 1`.

  Compiled here:
  * A. `garbage_isFullBFT`: the polynomial identity holds for the shape (so `WalkSat` with the
    recognizer inputs accepts it at EVERY `α`, `garbage_walkSat_all_alpha`), with `¬ BFSValid`,
    tiling, and `prefixLen fo5 5 = 1` (`garbage_prefixLen`); `garbage_rows_beyond_prefix`.
  * B. `selfCaller_Fcomp`: a concrete `OP_9` row `N` with `Fcomp N (L, N, ⊥)`, and
    `leaf_Fcomp`: `Fcomp L ⊥` — the shape passes Nock's `L_comp` row-locally, so
    `reconTree` machinery would accept the garbage rows as `RVT`-nodes if they were reachable.
    `selfCaller_childVec_self`: the declared child vector of slot 2 IS the row's own label
    vector (hosted tag `9`) — the walk identity `cur 3 = chld' 3 2` at the vector level.
  * C. A full
    `199`-column trace is NOT built here, and no gate is shown to reject it.
-/
import Nock.WalkPrefix
import Nock.NockVM
import Nock.NockVMROM.Thm54.ComputeWalkLabel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch469

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.ComputeWalkLabel

/-! ## A. The shape at the walk gates -/

/-- `fo = (0, 0, 2, 0, 2)`. -/
def fo5 : ℕ → ℕ := fun i => if i = 3 ∨ i = 5 then 2 else 0

theorem Sf_fo5_5 : Sf fo5 5 = 4 := by decide

theorem fo5_tiling : Sf fo5 5 + 1 = 5 := by decide

theorem fo5_not_bfsValid : ¬ BFSValid fo5 5 := by
  intro hv
  have := hv 2 (by norm_num) (by norm_num)
  simp [Sf, fo5] at this

/-- The queue empties after row 1: the prefix is the root alone. -/
theorem garbage_prefixLen : prefixLen fo5 5 = 1 := by
  have h1 : 1 ≤ prefixLen fo5 5 := one_le_prefixLen fo5 (by norm_num)
  have h2 : prefixLen fo5 5 < 2 := by
    by_contra hge
    have hge : 2 ≤ prefixLen fo5 5 := not_lt.mp hge
    have hv := bfsValid_prefixLen fo5 5
    have := hv 2 (by norm_num) hge
    simp [Sf, fo5] at this
  omega

/-- Rows `2..5` lie beyond the prefix. -/
theorem garbage_rows_beyond_prefix : ∀ i, 2 ≤ i → i ≤ 5 → prefixLen fo5 5 < i := by
  intro i h2 _; rw [garbage_prefixLen]; omega

/-- Row 3's children are positions `2` and `3` (itself); row 5's are `4` and `5` (itself). -/
theorem garbage_child_positions :
    firstC fo5 3 = 2 ∧ firstC fo5 3 + 1 = 3 ∧ firstC fo5 5 = 4 ∧ firstC fo5 5 + 1 = 5 := by
  decide

section Walk
variable {K : Type} [Field K]

/-- The node column `(R, L, N, L', M)` and the declared children `3 ↦ (L, N)`, `5 ↦ (L', M)`. -/
def cur5 (R L N L' M : K) : ℕ → K := fun i =>
  if i = 1 then R else if i = 2 then L else if i = 3 then N else if i = 4 then L' else
  if i = 5 then M else 0

def chld5 (L N L' M : K) : ℕ → ℕ → K := fun i l =>
  if i = 3 ∧ l = 1 then L else if i = 3 ∧ l = 2 then N else
  if i = 5 ∧ l = 1 then L' else if i = 5 ∧ l = 2 then M else 0

theorem sum_Icc_one_two (f : ℕ → K[X]) : ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self,
    Finset.sum_singleton]

/-- **The polynomial identity `node_list = node_queue_5` HOLDS for the garbage shape.** -/
theorem garbage_isFullBFT (R L N L' M : K) :
    IsFullBFT (cur5 R L N L' M) (chld5 L N L' M) fo5 5 := by
  unfold IsFullBFT nodeListP nodeQueueP queueTerm
  have h5 : Finset.Icc (1 : ℕ) 5 = {1, 2, 3, 4, 5} := by decide
  have hs2 : ∑ i ∈ Finset.Icc 1 2, fo5 i = 0 := by decide
  have hs4 : ∑ i ∈ Finset.Icc 1 4, fo5 i = 2 := by decide
  rw [h5]
  simp only [fo5, cur5, chld5]
  norm_num [Sf, sum_Icc_one_two, hs2, hs4]
  ring

/-- **Accepted at EVERY `α` with the recognizer inputs** (`seed = α·R`, `initial_count = α`),
`out_walk = 0` — the walk gates do not see the orphan cycles. -/
theorem garbage_walkSat_all_alpha (R L N L' M α : K) :
    ∃ ln count acc : ℕ → K,
      WalkSat (cur5 R L N L' M) (chld5 L N L' M) fo5 ln count acc α (R * α) α 5 ∧ acc 5 = 0 := by
  obtain ⟨ln, count, acc, hw⟩ :=
    walkSat_exists (cur5 R L N L' M) (chld5 L N L' M) fo5 α (R * α) α (by norm_num : 1 ≤ 5)
  refine ⟨ln, count, acc, hw, ?_⟩
  exact walk_completeness hw (by simp [cur5]) rfl (garbage_isFullBFT R L N L' M)

/-- The α-event is EMPTY for this shape: no coin catches it. -/
theorem garbage_alpha_event_empty (R L N L' M : K) [Fintype K] [DecidableEq K] :
    walkPrefixAlphaEvent (cur5 R L N L' M) (chld5 L N L' M) fo5 5 = ∅ := by
  unfold walkPrefixAlphaEvent
  rw [if_pos (garbage_isFullBFT R L N L' M)]

end Walk

/-! ## B. The shape at Nock's `F_comp` -/

section Fside
variable {K : Type} [Field K]

/-- Fingerprint of the formula `[0 1]` (`OP_0` on axis `1`). -/
def f01 (z : K) : FP K := FP.cons z (FP.atomFP z 0) (FP.atomFP z 1)

/-- Fingerprint of the formula `[9 b 0 1]`: head `9`, tail `[b [0 1]]`. -/
def f9 (z b : K) : FP K := FP.cons z (FP.atomFP z 9) (FP.cons z (FP.atomFP z b) (f01 z))

/-- The leaf `L = *[a 0 1]` with `/[1 a] = a`: an `OP_0` row with `s = e = a`. -/
def leafPub (z lnp α : K) (a : FP K) : Pub K :=
  { state := .s0, s := a, f := f01 z, e := a,
    sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0,
    sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := lnp, ln := lnp * α ^ 2,
    mr1 := ⟨f01 z, FP.atomFP z 1, 3, lnp * α⟩, mr2 := ⟨a, a, 1, lnp * α ^ 2⟩,
    mr3 := MemRec.zero }

def leafDec (z : K) : Dec K :=
  { f_h := FP.atomFP z 0, f_t := FP.atomFP z 1, f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 }

def inp5 (z α : K) : Inputs K := { α := α, z := z, a := 0, b := 0, c := 0 }

def leafLbl (z lnp α : K) (a : FP K) : State × DTcomp K :=
  (.s0, (inp5 z α, leafPub z lnp α a, leafDec z))

/-- **The self-calling core `N = *[a 9 b 0 1]`** with `/[b a] = [9 b 0 1]` (declared through
`mr3 = (a, [9 b 0 1], b)`): `sf1 = (a, [0 1], a)`, `sf2 = (a, [9 b 0 1], e)` = its OWN `(s,f,e)`. -/
def selfPub (z b lnp α : K) (a e : FP K) : Pub K :=
  { state := .s9, s := a, f := f9 z b, e := e,
    sf1_st := some 0, sf1_s := a, sf1_f := f01 z, sf1_e := a,
    sf2_st := some 9, sf2_s := a, sf2_f := f9 z b, sf2_e := e,
    sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := lnp, ln := lnp * α ^ 3,
    mr1 := ⟨f9 z b, FP.cons z (FP.atomFP z b) (f01 z), 3, lnp * α⟩,
    mr2 := ⟨FP.cons z (FP.atomFP z b) (f01 z), FP.atomFP z b, 2, lnp * α ^ 2⟩,
    mr3 := ⟨a, f9 z b, b, lnp * α ^ 3⟩ }

def selfDec (z b : K) : Dec K :=
  { f_h := FP.atomFP z 9, f_t := FP.cons z (FP.atomFP z b) (f01 z), f_th := FP.atomFP z b,
    f_tt := f01 z, f_tth := 0, f_ttt := 0 }

def selfLbl (z b lnp α : K) (a e : FP K) : State × DTcomp K :=
  (.s9, (inp5 z α, selfPub z b lnp α a e, selfDec z b))

/-- The leaf passes `F_comp` with no children. -/
theorem leaf_Fcomp (z lnp α : K) (a : FP K) : Fcomp (leafLbl z lnp α a) (fun _ => none) := by
  refine ⟨rfl, ⟨rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [leafLbl, SVhead, leafPub, leafDec, headAtom, State.toNat, inp5]
  · simp [leafLbl, memBlk, leafPub, leafDec, inp5]
  · simp [leafLbl, evalV, leafPub, sfz1, sfz2, sfz3]
  · intro i; simp [leafLbl, fanoutComp]
  · intro i hi; simp [leafLbl, fanoutComp] at hi

/-- **The self-caller passes `F_comp` with children `(L, N, ⊥)` — ITSELF in slot 2.**
Row-locally nothing distinguishes it from an honest `OP_9` row; `sf2_f = [9 b 0 1]` is
what the memory record `mr3 = (a, [9 b 0 1], b)` claims `/[b a]` to be,
which only the IO argument can check. -/
theorem selfCaller_Fcomp (z b lnp α : K) (a e : FP K) :
    Fcomp (selfLbl z b lnp α a e)
      (fun j : Fin 3 => if (j : ℕ) = 0 then some (leafLbl z lnp α a)
        else if (j : ℕ) = 1 then some (selfLbl z b lnp α a e) else none) := by
  refine ⟨rfl, ⟨rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [selfLbl, SVhead, selfPub, selfDec, headAtom, State.toNat, inp5]
  · simp [selfLbl, memBlk, selfPub, selfDec, inp5]
  · simp [selfLbl, evalV, selfPub, selfDec, sfz3, inp5]
  · intro i; fin_cases i <;> simp [selfLbl, fanoutComp]
  · intro i hi
    fin_cases i
    · simp [sfTriple, selfPub, leafLbl, leafPub, selfLbl]
    · simp [sfTriple, selfPub, selfLbl]
    · simp [selfLbl, fanoutComp] at hi

/-- The declared child vector of slot 2 (hosted tag `9`) IS the row's own `LT_comp` label
vector: `cur 3 = chld' 3 2` at the vector level, for every `γ`. -/
theorem selfCaller_childVec_self (z b lnp α : K) (a e : FP K) (tags : Fin 3 → K)
    (ht : tags 1 = 9) :
    childVec (selfPub z b lnp α a e) tags 1 = labelVecOfPub (selfPub z b lnp α a e) := by
  funext k
  fin_cases k <;> simp [childVec, labelVecOfPub, sfTriple, selfPub, stateTagField, ht]

/-- The hosted tags the self-caller declares (`Option A`): `(0, 9, ⊥)`. -/
theorem selfCaller_sfState (z b lnp α : K) (a e : FP K) :
    sfState (selfPub z b lnp α a e) 0 = 0 ∧ sfState (selfPub z b lnp α a e) 1 = 9 ∧
      sfState (selfPub z b lnp α a e) 2 = (nullStateTag : K) := by
  simp [sfState, selfPub]

end Fside

/-! ## C. Status at the deployed chip -/

/-- What was checked and what was not.  No `199`-column trace is built; no gate is shown to
reject the shape; the only candidates are non-row-local. -/
def deployedChipStatus : List (String × String) :=
  [("walk gates (Batch459::deployed_walkSat)", "do not reject: garbage_walkSat_all_alpha"),
    ("V_comp row-local (Fcomp)", "do not reject: selfCaller_Fcomp, leaf_Fcomp"),
    ("finalAccTerminal (acc_after(last) = requests) + IO.LIO", "candidate excluder; not measured"),
    ("full trace at computeChipAt c", "NOT built; acceptance UNCONFIRMED")]

theorem deployedChipStatus_length : deployedChipStatus.length = 4 := by decide

/-- Records the garbage rows would need served (`mr2`/`mr3` of `selfPub`, `mr2` of `leafPub`). -/
def garbageRecordsNeeded : List String :=
  ["(a, b, [9 b 0 1]) from the self-caller's mr3", "([b 0 1], 2, b) from its mr2",
    "(a, 1, a) from the leaf's mr2", "([9 b 0 1], 3, [b 0 1]) from its mr1 (always-on)"]

/-- Classification of census #5's exposure after this batch. -/
def classification : String :=
  "CONFIRMED at WalkSat and at F_comp; UNCONFIRMED as an accepted trace at computeChipAt c"

end Nock.RedTeam.Batch469

#print axioms Nock.RedTeam.Batch469.garbage_isFullBFT
#print axioms Nock.RedTeam.Batch469.garbage_walkSat_all_alpha
#print axioms Nock.RedTeam.Batch469.garbage_prefixLen
#print axioms Nock.RedTeam.Batch469.selfCaller_Fcomp
#print axioms Nock.RedTeam.Batch469.leaf_Fcomp
#print axioms Nock.RedTeam.Batch469.selfCaller_childVec_self
