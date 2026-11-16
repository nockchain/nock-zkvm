/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/LeafBoundF.lean

  **`leafBoundF`, the field-run window of a claim, and `calls` from it.**

  The calls at depth `d` are the finite set `callsAt q S0 F0 d`,
  defined recursively over the depth through `kidsOf` (one arm per `CallTreeF` constructor, the
  dependent kids read off the run result `resF`, which is well defined by `evalFBy_det`).
  `callTreeF_mem_callsAt` shows every `CallTreeF` call is listed, so `callsWithin_leafBoundF`
  discharges `RootGoodFJoin.CallsWithin` at every depth budget `D ≤ N` and window `W ≥ leafBoundF`.
-/
import Nock.NockVMROM.Thm54.P8Core.RootGoodFJoin

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.FieldEmbedding
open Nock.NockVMROM.Thm54.SVGenuineF (CallTreeF)
open Nock.NockVMROM.Thm54.ComputedWindow (condBit)

noncomputable section

open Classical in
/-- The field-run result of `(s, f)`, when some fuel succeeds (unique by `evalFBy_det`). -/
def resF (q : ℕ) (s f : Noun) : Option Noun :=
  if h : ∃ n r, evalFBy q n s f = some r then some (Classical.choose (Classical.choose_spec h))
  else none

theorem resF_of {q n : ℕ} {s f r : Noun} (h : evalFBy q n s f = some r) : resF q s f = some r := by
  have hex : ∃ n r, evalFBy q n s f = some r := ⟨n, r, h⟩
  unfold resF
  rw [dif_pos hex]
  congr 1
  exact SVInductionGenericF.evalFBy_det (Classical.choose_spec (Classical.choose_spec hex)) h

/-- The leaves of the run result (`0` when none). -/
def resLeaves (q : ℕ) (s f : Noun) : ℕ :=
  match resF q s f with
  | some r => r.leaves
  | none => 0

theorem resLeaves_of {q n : ℕ} {s f r : Noun} (h : evalFBy q n s f = some r) :
    resLeaves q s f = r.leaves := by
  simp [resLeaves, resF_of h]

/-- The calls one level below `(s, f)`: one arm per `CallTreeF` constructor. -/
def kidsOf (q : ℕ) (s : Noun) : Noun → Finset (Noun × Noun)
  | .cell (.cell b c) e => {(s, .cell b c), (s, e)}
  | .cell (.atom 2) (.cell b c) =>
      {(s, b), (s, c)} ∪
        (match resF q s b, resF q s c with
         | some sb, some sc => {(sb, sc)}
         | _, _ => ∅)
  | .cell (.atom 3) t => {(s, t)}
  | .cell (.atom 4) t => {(s, t)}
  | .cell (.atom 5) (.cell b c) => {(s, b), (s, c)}
  | .cell (.atom 6) (.cell b (.cell c e)) =>
      {(s, b)} ∪
        (match resF q s b with
         | some r => {(s, if condBit r = 0 then c else e)}
         | none => ∅)
  | .cell (.atom 7) (.cell b c) =>
      {(s, b)} ∪ (match resF q s b with | some sb => {(sb, c)} | none => ∅)
  | .cell (.atom 8) (.cell b c) =>
      {(s, b)} ∪ (match resF q s b with | some sb => {(.cell sb s, c)} | none => ∅)
  | .cell (.atom 9) (.cell (.atom ax) c) =>
      {(s, c)} ∪
        (match resF q s c with
         | some core => (match Noun.slot ax core with | some arm => {(core, arm)} | none => ∅)
         | none => ∅)
  | _ => ∅

/-- The calls at depth `d`. -/
def callsAt (q : ℕ) (S0 F0 : Noun) : ℕ → Finset (Noun × Noun)
  | 0 => {(S0, F0)}
  | d + 1 => (callsAt q S0 F0 d).biUnion fun p => kidsOf q p.1 p.2

theorem mem_callsAt_succ {q : ℕ} {S0 F0 : Noun} {d : ℕ} {s f : Noun} {p : Noun × Noun}
    (h : (s, f) ∈ callsAt q S0 F0 d) (hp : p ∈ kidsOf q s f) : p ∈ callsAt q S0 F0 (d + 1) :=
  Finset.mem_biUnion.mpr ⟨(s, f), h, hp⟩

/-- **Every call of the field call tree is listed.** -/
theorem callTreeF_mem_callsAt {q : ℕ} {S0 F0 : Noun} {d : ℕ} {s f : Noun}
    (h : CallTreeF q S0 F0 d s f) : (s, f) ∈ callsAt q S0 F0 d := by
  induction h with
  | root => simp [callsAt]
  | consL _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | consR _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op2L _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op2R _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op2App _ hb hc ih => exact mem_callsAt_succ ih (by simp [kidsOf, resF_of hb, resF_of hc])
  | op3 _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op4 _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op5L _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op5R _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op6C _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op6T _ hb ih => exact mem_callsAt_succ ih (by simp [kidsOf, resF_of hb])
  | op7H _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op7M _ hb ih => exact mem_callsAt_succ ih (by simp [kidsOf, resF_of hb])
  | op8H _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op8M _ hb ih => exact mem_callsAt_succ ih (by simp [kidsOf, resF_of hb])
  | op9C _ ih => exact mem_callsAt_succ ih (by simp [kidsOf])
  | op9I _ hc ha ih => exact mem_callsAt_succ ih (by simp [kidsOf, resF_of hc, ha])

/-- The leaf measure of one call. -/
def callLeaves (q : ℕ) (p : Noun × Noun) : ℕ :=
  max p.1.leaves (max p.2.leaves (resLeaves q p.1 p.2))

/-- **The field-run window of a claim** at depth budget `N`: a function of `(q, N, x)` only. -/
def leafBoundF (q N : ℕ) (x : P8PublicClaim) : ℕ :=
  max 1 (max x.result.leaves
    (((Finset.range N).biUnion (callsAt q x.subject x.formula)).sup (callLeaves q)))

theorem one_le_leafBoundF (q N : ℕ) (x : P8PublicClaim) : 1 ≤ leafBoundF q N x :=
  le_max_left _ _

theorem result_le_leafBoundF (q N : ℕ) (x : P8PublicClaim) :
    x.result.leaves ≤ leafBoundF q N x :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- **`calls` from the claim alone**: every call at depth `< D ≤ N` is inside any `W ≥ leafBoundF`. -/
theorem callsWithin_leafBoundF {q N D W : ℕ} (x : P8PublicClaim) (hD : D ≤ N)
    (hW : leafBoundF q N x ≤ W) :
    RootGoodFJoin.CallsWithin q x.subject x.formula D W := by
  intro d s f hd hc
  have hmem : (s, f) ∈ (Finset.range N).biUnion (callsAt q x.subject x.formula) :=
    Finset.mem_biUnion.mpr ⟨d, Finset.mem_range.mpr (by omega), callTreeF_mem_callsAt hc⟩
  have hle : callLeaves q (s, f) ≤ leafBoundF q N x :=
    (Finset.le_sup (f := callLeaves q) hmem).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hl := hle.trans hW
  simp only [callLeaves] at hl
  refine ⟨(le_max_left _ _).trans hl, ((le_max_left _ _).trans (le_max_right _ _)).trans hl, ?_⟩
  intro n r hr
  rw [← resLeaves_of hr]
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans hl

end

end Nock.NockVMROM.Thm54.SVFrame
