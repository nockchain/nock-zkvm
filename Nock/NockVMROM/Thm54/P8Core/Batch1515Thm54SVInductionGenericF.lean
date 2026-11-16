/-
  Nock/NockVMROM/Thm54/P8Core/Batch1515Thm54SVInductionGenericF.lean

  **The join-generic helpers of
  `Batch1171`'s induction at the field join, and the field evaluator facts the induction uses.**

  * `evalFBy_boundedBy` — the field evaluator keeps `BoundedBy q` (`1 < q`): the field twin of
    `Batch1091.evalGBy_bounded`, with NO run hypothesis on the guard (OP4 wraps mod `q`).
  * `evalFBy_det` — two successful field runs of the same inputs agree (fuel monotonicity).
  * `kid_e_bind` — a chip-ready kid's field root evaluation binds its `e` (`Batch1171.kid_e_bind`
    without `Good`).
  * `censusOK_of_not_mem` / `windowOK_of_not_mem` — `Batch1111.censusOK_of_ev` / `windowOK_of_ev`
    at ANY skeleton `S` with `S.computeTree = T` (the package forms fix `T` = the Nat join).
  * `kid_evalF` / `kid_eval_boundedF` — a field-genuine kid's evaluation is its inputs' field run
    (any fuel), and is `BoundedBy q` when its inputs are: the field twins of `Batch1171.kid_eval` /
    `kid_eval_bounded`, which needed the guarded honest run.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1514Thm54SVAlignmentF
import Nock.NockVMROM.Thm54.P8Core.Batch1171Thm54C2InductionPositional
import Nock.NockVMROM.Thm54.P8EventEv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVInductionGenericF

open Nock
open Nock.Noun
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVJoinAssemblyF
open Nock.NockVMROM.Thm54.SVReadyFuelF
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.NockVMROM.Thm54.SVAlignmentF
open Nock.RedTeam
open Nock.FieldEmbedding
open Nock.NockVMROM.Thm54.TraceGen

/-! ## The field evaluator -/

/-- **The field evaluator keeps nouns over 𝔽**. -/
theorem evalFBy_boundedBy (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalFBy q fuel s f = some r → BoundedBy q r := by
  intro fuel
  induction fuel with
  | zero => intro s f r _ _ hG; simp [evalFBy] at hG
  | succ fuel ih =>
    intro s f r hs hf hG
    match f with
    | .atom a => simp [evalFBy] at hG
    | .cell (.cell b c) d =>
        obtain ⟨hfbc, hfd⟩ := hf
        simp only [evalFBy] at hG
        cases hbc : evalFBy q fuel s (.cell b c) with
        | none => rw [hbc] at hG; simp at hG
        | some l =>
          cases hd : evalFBy q fuel s d with
          | none => rw [hbc, hd] at hG; simp at hG
          | some r' =>
            rw [hbc, hd] at hG
            simp only [Option.some.injEq] at hG
            subst hG
            exact ⟨ih s _ l hs hfbc hbc, ih s d r' hs hfd hd⟩
    | .cell (.atom op) tail =>
        obtain ⟨-, hft⟩ := hf
        match op with
        | 0 =>
            simp only [evalFBy] at hG
            match tail with
            | .atom ax => exact slot_boundedBy q ax s hs hG
            | .cell _ _ => simp at hG
        | 1 =>
            simp only [evalFBy] at hG
            obtain rfl := Option.some.inj hG
            exact hft
        | 2 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at hG
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    exact ih sb sc r (ih s b sb hs hfb hb) (ih s c sc hs hfc hc) hG
            | .atom _ => simp [evalFBy] at hG
        | 3 =>
            simp only [evalFBy] at hG
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              simp only [Option.map_some, Option.some.injEq] at hG
              subst hG
              exact wut_boundedBy hq v
        | 4 =>
            simp only [evalFBy] at hG
            cases ht : evalFBy q fuel s tail with
            | none => rw [ht] at hG; simp at hG
            | some v =>
              rw [ht] at hG
              cases v with
              | cell _ _ => simp [lusFBy] at hG
              | atom n =>
                simp only [Option.bind_some, lusFBy, Option.some.injEq] at hG
                subst hG
                exact Nat.mod_lt _ (by omega)
        | 5 =>
            match tail with
            | .cell b c =>
                simp only [evalFBy] at hG
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  cases hc : evalFBy q fuel s c with
                  | none => rw [hb, hc] at hG; simp at hG
                  | some sc =>
                    rw [hb, hc] at hG
                    simp only [Option.some.injEq] at hG
                    subst hG
                    exact tis_boundedBy hq sb sc
            | .atom _ => simp [evalFBy] at hG
        | 6 =>
            match tail with
            | .cell b (.cell c d) =>
                obtain ⟨hfb, hfc, hfd⟩ := hft
                simp only [evalFBy] at hG
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some vb =>
                  rw [hb] at hG
                  match vb, hG with
                  | .atom 0, hG => exact ih s c r hs hfc hG
                  | .atom 1, hG => exact ih s d r hs hfd hG
                  | .atom (n+2), hG => simp at hG
                  | .cell _ _, hG => simp at hG
            | .cell b (.atom _) => simp [evalFBy] at hG
            | .atom _ => simp [evalFBy] at hG
        | 7 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at hG
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  exact ih sb c r (ih s b sb hs hfb hb) hfc hG
            | .atom _ => simp [evalFBy] at hG
        | 8 =>
            match tail with
            | .cell b c =>
                obtain ⟨hfb, hfc⟩ := hft
                simp only [evalFBy] at hG
                cases hb : evalFBy q fuel s b with
                | none => rw [hb] at hG; simp at hG
                | some sb =>
                  rw [hb] at hG
                  exact ih (.cell sb s) c r ⟨ih s b sb hs hfb hb, hs⟩ hfc hG
            | .atom _ => simp [evalFBy] at hG
        | 9 =>
            match tail with
            | .cell (.atom ax) c =>
                obtain ⟨-, hfc⟩ := hft
                simp only [evalFBy] at hG
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some core =>
                  rw [hc] at hG
                  dsimp only at hG
                  have hBcore := ih s c core hs hfc hc
                  cases harm : slot ax core with
                  | none => rw [harm] at hG; simp at hG
                  | some arm =>
                    rw [harm] at hG
                    dsimp only at hG
                    exact ih core arm r hBcore (slot_boundedBy q ax core hBcore harm) hG
            | .cell (.cell _ _) _ => simp [evalFBy] at hG
            | .atom _ => simp [evalFBy] at hG
        | 10 =>
            match tail with
            | .cell (.cell (.atom ax) c) d =>
                obtain ⟨⟨-, hfc⟩, hfd⟩ := hft
                simp only [evalFBy] at hG
                cases hc : evalFBy q fuel s c with
                | none => rw [hc] at hG; simp at hG
                | some new =>
                  cases hd : evalFBy q fuel s d with
                  | none => rw [hc, hd] at hG; simp at hG
                  | some old =>
                    rw [hc, hd] at hG
                    exact edit_boundedBy q ax new old (ih s c new hs hfc hc) (ih s d old hs hfd hd) hG
            | .cell (.cell (.cell _ _) _) _ => simp [evalFBy] at hG
            | .cell (.atom _) _ => simp [evalFBy] at hG
            | .atom _ => simp [evalFBy] at hG
        | 11 =>
            match tail with
            | .cell (.cell hd clue) body =>
                obtain ⟨⟨-, hfclue⟩, hfbody⟩ := hft
                simp only [evalFBy] at hG
                cases hcl : evalFBy q fuel s clue with
                | none => rw [hcl] at hG; simp at hG
                | some vc =>
                  rw [hcl] at hG
                  exact ih s body r hs hfbody hG
            | .cell (.atom hint) body =>
                obtain ⟨-, hfbody⟩ := hft
                simp only [evalFBy] at hG
                exact ih s body r hs hfbody hG
            | .atom _ => simp [evalFBy] at hG
        | (n+12) => simp [evalFBy] at hG

/-- Two successful field runs of the same inputs agree. -/
theorem evalFBy_det {q n m : ℕ} {s f r r' : Noun} (h : evalFBy q n s f = some r)
    (h' : evalFBy q m s f = some r') : r = r' := by
  have a := GlobalOpcodeScheduling.evalFBy_mono (le_max_left n m) h
  have b := GlobalOpcodeScheduling.evalFBy_mono (le_max_right n m) h'
  rw [a] at b
  exact Option.some.inj b

/-- (`FieldEmbedding.agreeBy` + `evalFBy_det`.) -/
theorem evalN_of_holdsF {q : ℕ} (hq : 1 < q) {x : P8PublicClaim} (hx : HoldsF q x)
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, evalGBy q fuel x.subject x.formula = some r) :
    ∃ fuel, Nock.evalN fuel x.subject x.formula = some x.result := by
  obtain ⟨fuel, r, hG⟩ := hguard
  obtain ⟨hN, hF, -⟩ := agreeBy q hq fuel _ _ r hs hf hG
  obtain ⟨fuel', hF'⟩ := hx
  have : x.result = r := evalFBy_det hF' hF
  exact ⟨fuel, this ▸ hN⟩

variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
set_option hygiene false in
/-- The FIELD C2 join at the modulus `q` in scope at the use site. -/
local notation "J" => c2JoinFuelF q (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## The record facts of `Batch1171` at the field join -/

theorem J_label_eq {q : ℕ} (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J n t s f).label =
      c2SkeletonRowF q sv ax t.label.1.1 t.label.2 s f ((J n t s f).children.map NTree.label) := by
  cases n <;> cases t <;> rfl

def c2RecF (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State) (S : ℕ) (subj formula : Noun)
    (kids : List ComputeRowSkeleton) : ℕ → MemRecSkeleton := fun i =>
  let ft := nounTail formula
  let fth := nounHead ft
  let ftt := nounTail ft
  let ftth := nounHead ftt
  match st, i with
  | _, 0 => ⟨formula, ft, 3⟩
  | .s0, 1 => ⟨subj, op0ResF sv' ax' S subj, ax' (S + 2)⟩
  | .s2, 1 | .s5, 1 | .s7, 1 | .s8, 1 | .s9, 1 => ⟨ft, fth, 2⟩
  | .s6, 1 => ⟨ft, fth, 2⟩
  | .s6, 2 => ⟨ftt, ftth, 2⟩
  | .s9, 2 => ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax' (S + 3)⟩
  | _, _ => dummyMemRec

section c2RecF
variable (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
theorem c2RecF_0 (st : State) (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax st S s f kids 0 = ⟨f, nounTail f, 3⟩ := by
  cases st <;> rfl
theorem c2RecF_s0_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s0 S s f kids 1 = ⟨s, op0ResF sv ax S s, ax (S + 2)⟩ := rfl
theorem c2RecF_s2_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s2 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s5_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s5 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s6_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s6 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s6_2 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s6 S s f kids 2 =
      ⟨nounTail (nounTail f), nounHead (nounTail (nounTail f)), 2⟩ := rfl
theorem c2RecF_s7_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s7 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s8_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s8 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s9_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s9 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2RecF_s9_2 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2RecF sv ax .s9 S s f kids 2 =
      ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax (S + 3)⟩ := rfl
end c2RecF

theorem memoryRecord_eq {q : ℕ} (st : State) (S : ℕ) (subj formula : Noun)
    (kids : List ComputeRowSkeleton) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount
      (c2SkeletonRowF q sv ax st S subj formula kids).state) :
    (c2SkeletonRowF q sv ax st S subj formula kids).memoryRecord j hj =
      c2RecF sv ax st S subj formula kids j := by
  rcases j with ⟨j, hj3⟩
  cases st <;> (rcases j with _ | _ | _ | j <;> rfl)

theorem J_rec {q : ℕ} (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount (J n t s f).label.state) :
    (J n t s f).label.memoryRecord j hj =
      c2RecF sv ax t.label.1.1 t.label.2 s f ((J n t s f).children.map NTree.label) j := by
  have e := J_label_eq (sv := sv) (ax := ax) (q := q) n t s f
  simp only [e] at hj ⊢
  exact memoryRecord_eq _ _ _ _ _ j hj

/-! ## Kid facts without the honest run -/

/-- **A chip-ready kid's FIELD root evaluation binds its `e`** (`Batch1171.kid_e_bind`). -/
theorem kid_e_bind {z : K} {q : ℕ} [CharP K q] (hz : z ≠ 0)
    {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hR : C2ChipReady (sv := sv) (ax := ax) z q c s f) (hs : bindFP z s c.label.1.2.2.1.s) :
    bindFP z (J c.size c s f).label.evaluation c.label.1.2.2.1.e :=
  readyF_child_eval_binds (q := q) hz (c2JoinReadyF_of_chipReady hz hR hs) rfl

/-- **A field-genuine kid's evaluation is its inputs' field run** (at any successful fuel). -/
theorem kid_evalF {q : ℕ} {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun} {n : ℕ}
    (hG : GenuineSkelF q (J n c s f)) {fuel : ℕ} {r : Noun}
    (hr : evalFBy q fuel s f = some r) : (J n c s f).label.evaluation = r := by
  have h := genuineF_evalFBy hG
  rw [J_subject' (sv := sv) (ax := ax) (q := q), J_formula' (sv := sv) (ax := ax) (q := q)] at h
  exact evalFBy_det h hr

/-- **A field-genuine kid's evaluation is over 𝔽** when its inputs are (no run hypothesis). -/
theorem kid_eval_boundedF {q : ℕ} (hq : 1 < q) {c : NTree ((State × DTcomp K) × ℕ)}
    {s f : Noun} {n : ℕ} (hG : GenuineSkelF q (J n c s f))
    (bs : BoundedBy q s) (bf : BoundedBy q f) :
    BoundedBy q (J n c s f).label.evaluation := by
  have h := genuineF_evalFBy hG
  rw [J_subject' (sv := sv) (ax := ax) (q := q), J_formula' (sv := sv) (ax := ax) (q := q)] at h
  exact evalFBy_boundedBy q hq _ s f _ bs bf h

/-! ## `CensusOK` / `WindowOK` at any skeleton carrying a given compute tree

`Batch1111.censusOK_of_ev` / `windowOK_of_ev` are stated at a package's event skeleton, whose
compute tree is the NAT join.  These are the skeleton-generic forms: at any `S` whose compute tree
is `T` (for the standalone verifier: the field join, once the event over `V` is built on it — lane
L-C's choice), a coin outside the guarded census / size-window events of `S` gives the oracles at
every node of `T`. -/

section Oracles

variable [Fintype K] [CharP K (ringChar K)]

theorem row_of_inTree (S : SemanticSkeleton) {T : NTree ComputeRowSkeleton} (hS : S.computeTree = T)
    {v : NTree ComputeRowSkeleton} (hv : InTree T v) : v.label ∈ computeSkeletonRows S := by
  unfold computeSkeletonRows
  rw [hS]
  exact List.mem_map.2 ⟨v, (mem_bfsForest _ _).2 ⟨_, List.mem_singleton_self _, hv⟩, rfl⟩

theorem pair_mem_combined (S : SemanticSkeleton) {T : NTree ComputeRowSkeleton}
    (hS : S.computeTree = T) {v : NTree ComputeRowSkeleton} (hv : InTree T v)
    {cmp : SemanticTrace.ComparisonUse} (hc : cmp ∈ P8Census.skeletonComparisons (K := K) v.label) :
    cmp.pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S := by
  unfold EdgeComparisonCensus.combinedSkeletonPairs
  apply List.mem_append_left
  unfold BoundSemanticTrace.skeletonPairs
  apply List.mem_append_right
  refine List.mem_map.2 ⟨cmp, ?_, rfl⟩
  unfold P8Census.skeletonComparisonCensus
  rw [List.mem_flatMap]
  exact ⟨v.label, row_of_inTree S hS hv, hc⟩

/-- **`CensusOK` at every node**, outside the guarded census event of `S`. -/
theorem censusOK_of_not_mem (S : SemanticSkeleton) {T : NTree ComputeRowSkeleton}
    (hS : S.computeTree = T) {Λ : ℕ} {ω : JointCoins K}
    (hout : ω ∉ collisionFailureEvent (P8EventEv.guardedCensusEv K S Λ))
    {v : NTree ComputeRowSkeleton} (hv : InTree T v) :
    Batch1171.CensusOK (nprSeed ω) Λ v.label := by
  intro cmp hc hl hr
  by_contra hsep
  apply hout
  unfold collisionFailureEvent P8EventEv.guardedCensusEv
  rw [mem_liftSeed_iff]
  show nprSeed ω ∈ PreSeedCensus.pairBadSeeds _ _
  rw [PreSeedCensus.mem_pairBadSeeds_iff]
  exact ⟨cmp.pair, pair_mem_combined S hS hv hc, hl, hr, hsep⟩

/-- **`WindowOK` at every node**, outside the guarded size-window event of `S`. -/
theorem windowOK_of_not_mem (S : SemanticSkeleton) {T : NTree ComputeRowSkeleton}
    (hS : S.computeTree = T) {Λ : ℕ} {ω : JointCoins K} (hz : nprSeed ω ≠ 0)
    (hout : ω ∉ P8EventEv.guardedSizeWindowFailure (K := K) S Λ)
    {v : NTree ComputeRowSkeleton} (hv : InTree T v) :
    Batch1171.WindowOK (nprSeed ω) Λ v.label := by
  intro n hn hΛ
  refine P8EventEv.window_of_not_mem_guardedSizeWindowFailure _ _ ω hz hout n ?_ hΛ
  unfold SizeWindowCounting.skeletonSizeWindowNouns
  rw [List.mem_flatMap]
  exact ⟨v.label, row_of_inTree S hS hv, hn⟩

end Oracles

/-- The field join's root inputs are a call of the claim's call tree (the root of `root_goodF`'s
`InpF`). -/
theorem root_call (q : ℕ) (S0 F0 : Noun) : CallTreeF q S0 F0 0 S0 F0 := .root

end Nock.NockVMROM.Thm54.SVInductionGenericF
