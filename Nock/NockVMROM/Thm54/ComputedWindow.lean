/-
  Nock/NockVMROM/Thm54/ComputedWindow.lean

  What does hold is the split window `Λ3 = M + max(M, Λpkg)`, with computed
  nouns `≤ Λpkg := programLeafBound` **only inside the binding induction**.  This module is that
  induction's noun-level half.

  * `GenuineSkel T` — a built compute-skeleton tree whose every row obeys its Nock step: the formula has its
    opcode's shape (`FormulaShape`), the children's inputs are the ones the join
    `StrategyOfTraces.mapComputeJoinInFuel` passes down (`KidInputs`, built from the same
    `nounHead` / `nounTail` and sibling results, in the exec/AIR child order), and the row's
    evaluation is the opcode's output (`RowOutput`, the same cases as
    `StrategyOfTraces.joinEvaluation`).
  * **Theorem 1 (alignment), `genuine_aligned`.**  A genuine tree whose root inputs are the
    inputs of a successful generator run `genComputeSkeleton n s f =.ok (sub, r)` is aligned
    row-for-row with `airReorder sub` (the AIR/exec child order, `GenAirOrder.lean`), with equal
    state, subject, formula and evaluation, and `r` is its root evaluation.  Corollary
    `genuine_rows_le_programLeafBound`: every row noun is `≤ programLeafBound (airReorder sub)`,
    the compiler's `Λ` (`GenNockCompilesCarrier.lean` group 8).
  * **Theorem 2 (the computed-window induction), `computedWindow_row` + `honestCall_kid`.**
    At a row whose inputs are an honest call (`HonestCall`, top-down from the claim), the
    children's inputs are honest calls in **evaluation order** once the earlier siblings are
    genuine (`honestCall_kid`); and once every child is genuine (the IH: "the rows so far are
    bound"), every noun of every child — in particular every computed evaluation the row's
    window premises `hwin` / `hke` / `hfaith` / `hcondE` read — has `≤ Λpkg` leaves, and the
    row's honest output exists and is `≤ Λpkg` (`computedWindow_row`).  Neither carries a
    window premise of its own: the bound is read off the honest tree.

  **Rule 8(b).** Nothing here holds at every `(Qc, Qm)`.  The root `HonestCall` is route B's root = the claim.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenRomComplete
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderLinked
import Nock.NockVMROM.Thm54.BuildTFWindow
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.P8Core.ComputedWindow
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ComputedWindow

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

/-! ## §A  The genuine-row predicate -/

/-! ## §B  Alignment with the honest generated tree -/

variable {K : Type} [Field K]

/-! ## §C  Theorem 1 — the honest-tree alignment lemma -/

/-! ## §D  Theorem 2 — the computed-window induction -/

/-- **Theorem 2(b) — the computed window at one row, before the row is bound.**  At a row whose
inputs are an honest call, whose formula has its state's shape and whose children receive the
join's inputs: once every child is genuine (the induction hypothesis — "the rows so far are
bound"), every noun of every child subtree — in particular every computed evaluation the row's
window premises `hwin` / `hke` / `hfaith` / `hcondE` read — has `≤ Λpkg` leaves, and the row's
honest output exists, is the opcode's output from those children, and is `≤ Λpkg`.  No window
premise is assumed; the bound is read off the honest tree. -/
theorem computedWindow_row {G : NTree (GenComputeRow K)} {st : State} {subj f : Noun}
    {kids : List (NTree ComputeRowSkeleton)}
    (hcall : HonestCall G subj f) (hshape : FormulaShape st f)
    (hin : KidInputs st subj f (kids.map NTree.label))
    (hkids : ∀ k ∈ kids, GenuineSkel k) :
    (∃ e, RowOutput st subj f (kids.map NTree.label) e ∧
        e.leaves ≤ programLeafBound (airReorder G)) ∧
      ∀ k ∈ kids, ∀ u, InTree k u → RowNounsLe (programLeafBound (airReorder G)) u.label := by
  obtain ⟨n, sub, r, hgen, hG⟩ := hcall
  obtain ⟨hout, _, _, _, he, hall⟩ :=
    step_align hgen hshape hin (fun k hk => genuine_aligned (K := K) (hkids k hk))
  refine ⟨⟨r, hout, ?_⟩, ?_⟩
  · have hc := confined_inTree (traceConfined_of_leafBound
      (le_refl (programLeafBound (airReorder G)))) hG
    exact he ▸ hc.2.2
  · intro k hk
    obtain ⟨a, ha, hal⟩ := forall₂_exists_of_mem hall hk
    exact aligned_rows_le hal (InTree_trans hG (InTree.sub ha (InTree.here _)))

/-- **Theorem 2 — the computed-window induction, whole tree.**  Run Theorem 2(a)/(b) to the
leaves: a genuine built tree whose root is an honest call has every row noun within `Λpkg`.
This is the conclusion the binding induction accumulates row by row; it is NOT a statement about
arbitrary committed traces (rule 8(b)). -/
theorem computedWindow_tree {G : NTree (GenComputeRow K)} {T : NTree ComputeRowSkeleton}
    (hroot : HonestCall G T.label.subject T.label.formula) (hT : GenuineSkel T) :
    ∀ u, InTree T u → RowNounsLe (programLeafBound (airReorder G)) u.label :=
  genuine_rows_le_of_honestCall hroot hT

/-- The computed window feeds `Batch530`'s `hwin` premise: inside the certified power window
(`Λpkg < orderOf z`), a computed noun with `≤ Λpkg` leaves is a `SizeWindow` noun. -/
theorem sizeWindow_of_le {z : K} {n : Noun} {Λ : ℕ} (h1 : 1 < orderOf z)
    (hΛ : Λ < orderOf z) (hn : n.leaves ≤ Λ) : OpcodeSemantics.SizeWindow z n :=
  ⟨h1, lt_of_le_of_lt hn hΛ⟩

/-! ## §E  At the built strategy: `StrategyOfTraces.decodedSkeletonOf` -/

section Built

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open scoped Polynomial

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- `romTree` reads its termination proof only as a `Prop`: the package's
`romTree (evalGRom_le_evalRom hgrom)` (`GenNockCompilesCarrier.lean`) is every `romTree h`. -/
theorem romTree_proof_irrel {fuel : ℕ} {S Fm R : Noun}
    (h₁ h₂ : TraceGen.evalRom fuel S Fm = some R) :
    romTree (K := K) h₁ = romTree (K := K) h₂ := rfl

/-- **Theorem 1 at the built strategy.**  The compute tree of `decodedSkeletonOf P Qc Qm`
(= `(computeJoinOf P Qc Qm).computeTree`, the join `mapComputeJoin` over the reconstructed
traces), when genuine and rooted at the claim `(S, Fm)` of a terminating ROM run, is row for row
the honest AIR-order tree `airReorder (romTree hrom)`; its root evaluation is the honest result;
and every computed and decoded noun of every row is within the compiler's window
`programLeafBound (airReorder (romTree hrom))` (`hΛp`'s numeral). -/
theorem decodedSkeleton_aligned (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    {fuel : ℕ} {S Fm R : Noun} (hrom : TraceGen.evalRom fuel S Fm = some R)
    (hgen : GenuineSkel (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree)
    (hS : (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree.label.subject = S)
    (hF : (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree.label.formula = Fm) :
    R = (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree.label.evaluation ∧
      Aligned (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree
        (airReorder (romTree (K := K) hrom)) ∧
      ∀ u, InTree (StrategyOfTraces.decodedSkeletonOf P Qc Qm).computeTree u →
        RowNounsLe (programLeafBound (airReorder (romTree (K := K) hrom))) u.label :=
  genuine_rows_le_programLeafBound (romTree_spec (K := K) hrom) hgen hS hF

end Built

/-! ## §F  The split window `Λ3 = M + max(M, Λpkg)` and the S3 pair nouns -/

/-- The split window of the leaf-bound probe: served nouns `≤ M`, computed `≤ Λpkg`, mixed
served/computed cells `≤ M + max(M, Λpkg)`. -/
def window3 (M Λp : ℕ) : ℕ := M + max M Λp

theorem served_le_window3 {M Λp : ℕ} {n : Noun} (h : n.leaves ≤ M) :
    n.leaves ≤ window3 M Λp :=
  le_trans h (le_trans (le_max_left M Λp) (Nat.le_add_left _ _))

theorem computed_le_window3 {M Λp : ℕ} {n : Noun} (h : n.leaves ≤ Λp) :
    n.leaves ≤ window3 M Λp :=
  le_trans h (le_trans (le_max_right M Λp) (Nat.le_add_left _ _))

theorem window3_le_two_mul {M Λp S : ℕ} (hM : M ≤ S) (hΛ : Λp ≤ S) : window3 M Λp ≤ 2 * S := by
  unfold window3
  have : max M Λp ≤ S := max_le hM hΛ
  omega

theorem nounTail_leaves_le (n : Noun) : (tl n).leaves ≤ n.leaves := by
  cases n <;> simp [tl, StrategyOfTraces.nounTail, Noun.leaves]

theorem nounHead_leaves_le (n : Noun) : (hd n).leaves ≤ n.leaves := by
  cases n <;> simp [hd, StrategyOfTraces.nounHead, Noun.leaves]

/-- `tailCons` / `branchTailCons` right side under served decomposition: `cell f_th (tail f_t)`
with `f_th`, `f_t` served (each `≤ M`) has `≤ 2M` leaves (probe `LeafBound.tailCons_right_le`). -/
theorem tailCons_right_le {M : ℕ} (fth ft : Noun) (h1 : fth.leaves ≤ M) (h2 : ft.leaves ≤ M) :
    (Noun.cell fth (tl ft)).leaves ≤ 2 * M := by
  have := nounTail_leaves_le ft
  simp only [Noun.leaves]; omega

/-- `formulaCons` right side: `cell f_h f_t` with `f_h` the head of a row formula of `≤ Λ`
leaves and `f_t` served (`≤ M`): `≤ Λ + M` (probe `LeafBound.formulaCons_right_le`). -/
theorem formulaCons_right_le {Λ M : ℕ} (formula ft : Noun) (h1 : formula.leaves ≤ Λ)
    (h2 : ft.leaves ≤ M) : (Noun.cell (hd formula) ft).leaves ≤ Λ + M := by
  have := nounHead_leaves_le formula
  simp only [Noun.leaves]; omega

/-- Tightness of `2M − 1` for the tailCons cell (a hostile served `f_th` pointing at `f_t`'s own
node), so `Λ = M` is not available for that cell. -/
theorem tailCons_right_tight (X : Noun) :
    (Noun.cell (Noun.cell (.atom 0) X) (tl (Noun.cell (.atom 0) X))).leaves =
      2 * (Noun.cell (.atom 0) X).leaves - 1 := by
  simp only [tl, StrategyOfTraces.nounTail, Noun.leaves]; omega

theorem tailCons_right_le_window3 {M Λp : ℕ} (fth ft : Noun) (h1 : fth.leaves ≤ M)
    (h2 : ft.leaves ≤ M) : (Noun.cell fth (tl ft)).leaves ≤ window3 M Λp := by
  have := tailCons_right_le fth ft h1 h2
  unfold window3
  have : M ≤ max M Λp := le_max_left _ _
  omega

theorem formulaCons_right_le_window3 {M Λp : ℕ} (formula ft : Noun)
    (h1 : formula.leaves ≤ Λp) (h2 : ft.leaves ≤ M) :
    (Noun.cell (hd formula) ft).leaves ≤ window3 M Λp := by
  have := formulaCons_right_le formula ft h1 h2
  unfold window3
  have : Λp ≤ max M Λp := le_max_right _ _
  omega

/-- **The split-window corollary.**
* `equalityOperand` — every child evaluation of `u` (computed, Theorem 2);
* `formulaCons` — `u`'s formula (computed) and the mixed cell `cell (head formula) f_t`;
* `tailCons` / `branchTailCons` — `f_t` (served) and the mixed cell `cell f_th (tail f_t)`. -/
theorem s3_pair_nouns_le_window3 {G : NTree (GenComputeRow K)} {T : NTree ComputeRowSkeleton}
    (hroot : HonestCall G T.label.subject T.label.formula) (hT : GenuineSkel T)
    {u : NTree ComputeRowSkeleton} (hu : InTree T u) {M : ℕ} {ft fth : Noun}
    (hft : ft.leaves ≤ M) (hfth : fth.leaves ≤ M) :
    (∀ k ∈ u.children,
        k.label.evaluation.leaves ≤ window3 M (programLeafBound (airReorder G))) ∧
      u.label.formula.leaves ≤ window3 M (programLeafBound (airReorder G)) ∧
      (Noun.cell (hd u.label.formula) ft).leaves ≤
        window3 M (programLeafBound (airReorder G)) ∧
      ft.leaves ≤ window3 M (programLeafBound (airReorder G)) ∧
      (Noun.cell fth (tl ft)).leaves ≤ window3 M (programLeafBound (airReorder G)) := by
  have hrows := computedWindow_tree hroot hT
  refine ⟨fun k hk => ?_, computed_le_window3 (hrows u hu).2.1,
    formulaCons_right_le_window3 _ _ (hrows u hu).2.1 hft, served_le_window3 hft,
    tailCons_right_le_window3 _ _ hfth hft⟩
  exact computed_le_window3 (hrows k (InTree_trans hu (InTree.sub hk (InTree.here _)))).2.2

/-- A decoded pre-`z` noun at a
valid position has `≤ M ≤ window3 M Λp` leaves. -/
theorem decoded_le_window3 {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}
    (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) (Λp : ℕ)
    (envs : Fin M → Reified.Env F) (hM : 0 < M)
    (hvalid : BFSValidF kroots (PreSeedCensus.preFoOfEnvs envs hM) M) {i : ℕ} (hi : 1 ≤ i)
    (hiM : i ≤ M) :
    (PreSeedCensus.preZNounOfEnvs K q kroots envs hM i).leaves ≤ window3 M Λp :=
  served_le_window3 (PreSeedCensus.preZNounOfEnvs_leaves_le K q kroots envs hM hvalid hi hiM)

/-! `PreSeedCensus.pairBadSeeds_card_le` holds for every pair list at every `(Qc, Qm)` with no premise
(the guard sits inside `guardedPairs`), so pricing S3 at the fixed window `window3 M Λpkg` (fixed
by `P` and `M`, round 0) satisfies rule 8(b).  What the induction supplies is the guard at each
consumed pair, which turns `z ∉ pairBadSeeds` into the separation `SepSeed` the binding step
reads. -/

section Consume

variable [Fintype K] [DecidableEq K]

theorem sepSeed_of_guard {Λ : ℕ} {pairs : List (Noun × Noun)} {z : K}
    (hz : z ∉ PreSeedCensus.pairBadSeeds (K := K) Λ pairs) {p : Noun × Noun} (hp : p ∈ pairs)
    (h1 : p.1.leaves ≤ Λ) (h2 : p.2.leaves ≤ Λ) : GlobalCarryRecognizer.SepSeed z p.1 p.2 := by
  by_contra h
  exact hz ((PreSeedCensus.mem_pairBadSeeds_iff Λ pairs z).2 ⟨p, hp, h1, h2, h⟩)

/-- **S3 consumption at a genuine row.**  Outside the S3 event priced at `window3 M Λpkg`, every
S3 pair of a genuine row (honest root, served `f_t` / `f_th` within `M`) is separated. -/
theorem s3_pairs_separated {G : NTree (GenComputeRow K)} {T : NTree ComputeRowSkeleton}
    (hroot : HonestCall G T.label.subject T.label.formula) (hT : GenuineSkel T)
    {u : NTree ComputeRowSkeleton} (hu : InTree T u) {M : ℕ} {ft fth : Noun}
    (hft : ft.leaves ≤ M) (hfth : fth.leaves ≤ M) {pairs : List (Noun × Noun)} {z : K}
    (hz : z ∉ PreSeedCensus.pairBadSeeds (K := K)
      (window3 M (programLeafBound (airReorder G))) pairs) :
    ((u.label.formula, Noun.cell (hd u.label.formula) ft) ∈ pairs →
        GlobalCarryRecognizer.SepSeed z u.label.formula (Noun.cell (hd u.label.formula) ft)) ∧
      ((ft, Noun.cell fth (tl ft)) ∈ pairs →
        GlobalCarryRecognizer.SepSeed z ft (Noun.cell fth (tl ft))) ∧
      (∀ k₀ ∈ u.children, ∀ k₁ ∈ u.children,
        (k₀.label.evaluation, k₁.label.evaluation) ∈ pairs →
          GlobalCarryRecognizer.SepSeed z k₀.label.evaluation k₁.label.evaluation) := by
  obtain ⟨hkids, hf, hfc, hft3, htc⟩ :=
    s3_pair_nouns_le_window3 (K := K) hroot hT hu hft hfth
  exact ⟨fun hp => sepSeed_of_guard hz hp hf hfc, fun hp => sepSeed_of_guard hz hp hft3 htc,
    fun k₀ h₀ k₁ h₁ hp => sepSeed_of_guard hz hp (hkids k₀ h₀) (hkids k₁ h₁)⟩

end Consume

end Nock.NockVMROM.Thm54.ComputedWindow
