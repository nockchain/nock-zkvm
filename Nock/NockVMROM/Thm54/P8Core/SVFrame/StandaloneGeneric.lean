/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/StandaloneGeneric.lean

  No chip, package, timestamp, walk, Form R or
  `Tuple12` constant is named here: everything is over `(CF, MF)`.

  * `rec_struct` / `J_label`: the field C2 join's record axes are `joinRecordAxis` and its record
    children are determined by the root's slot at that axis (axes `3` / `2`: tail / head; OP0's read:
    the served noun at `keyOf .verify_child (S+2)`; OP9's arm: the join's second kid's formula,
    `sv .verify_child (S+3)`).
  * `recOK_row`: `Batch1171.RecOK` at a join row from, per record, a served root/child with the trace
    record's fingerprints, the slot at the record axis, a bounded root in the window and the
    record-pair separation.
  * `ctxW_of_accepts` — **the r2 `CtxWObligation`**: outside `allSummands V x y (jointSummands …)`,
    acceptance gives `RootGoodFJoin.CtxW` at the served oracle, `CF.axB0`, the window `windowW`
    (= `windowAt leafBoundF V msg`), `t := CF.tree V x Qc χ`, `D := t.size`:
    `hz` zero seed; `hq12` `Checks.hp` + `char_eq`; `hcast` `CharP`; `hW1` / `calls` `leafBoundF`;
    `hlow` the window summand; `hD` refl (and `t.size = (CF.shape …).size ≤ V.N` by `tree_shape`);
    `row` the premise `rowFactsAt CF`; `recs` `CF.node_records` + `MF.serves` + `MF.response_sound`
    + the record-pair census (+ the `ExtraPremises` below); `census` the NPR census summand.
  * `holdsF_of_accepts` — `root_holdsF` + the root-result bridge (`computeTreeBinds_of_chipReady`
    binds the join's root evaluation to the root row's `e`, `CF.root_binds` binds `claim.result`
    there, the root-result pair separates, both sides bounded) ⇒ `HoldsF (ringChar K) V.claim`.
  * **`standalone_generic`**: `rowFactsAt CF → ExtraPremises CF MF →
    StandaloneThm54Statement CF MF (jointSummandsStd CF MF)`; soundness is `union_prob_le` over the
    containment `{AcceptsV ∧ ¬ HoldsF} ⊆ ⋃ allSummands`; completeness is `union_prob_le` at the
    honest strategy (staged by the two `honest_staged`); `standalone_fixed`, the fixed-trace
    corollary via `tracesStaged_const`.

  **`ExtraPremises` (beyond I0 r2; reported, each a one-line obligation of the instance):**
  `reqCond` (the IO mechanism's condition on the compute request records, outside the two families'
  summands — `MF.serves` needs it and no field supplies it); `recKey_s9` (OP9's arm record is keyed
  at `keyOf .verify_child (S+3)`, the twin of r2's `recKey_s0`); `served_bounded` (the served roots
  are nouns over `𝔽`); `char_eq` (`ringChar Kfp = ringChar K`).

-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF CallTreeF)
open Nock.GlobalCarryRecognizer
open scoped Polynomial

theorem recRootOf_of_lt (v : SemanticStrategy.ComputeRowSkeleton) (j : Fin 3)
    (h : (j : ℕ) < Nock.Framework.recordCount v.state) :
    recRootOf v j = (v.memoryRecord j h).root := dif_pos h

noncomputable section

/-! ## 1. The join's records -/

theorem slot3_tail {n c : Noun} (h : Noun.slot 3 n = some c) : nounTail n = c := by
  cases n with
  | atom k => simp [Noun.slot] at h
  | cell a b => simp [Noun.slot] at h; simp [nounTail, h]

theorem slot2_head {n c : Noun} (h : Noun.slot 2 n = some c) : nounHead n = c := by
  cases n with
  | atom k => simp [Noun.slot] at h
  | cell a b => simp [Noun.slot] at h; simp [nounHead, h]

/-- **The join's record structure**: the record axis is `joinRecordAxis`, and the record child is
whatever the root's slot at that axis returns (given OP0's served read and OP9's arm). -/
theorem rec_struct (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (Sn : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount st) (ch : Noun)
    (hsl : Noun.slot (joinRecordAxis st ax Sn j)
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).root = some ch)
    (h0 : st = .s0 → (j : ℕ) = 1 → ch = op0ResF sv ax Sn subj)
    (h9 : st = .s9 → (j : ℕ) = 2 → ch = (kidSkel kids 1).formula) :
    ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).axis =
        joinRecordAxis st ax Sn j ∧
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).child = ch := by
  fin_cases j <;> cases st <;> simp [Nock.Framework.recordCount] at hj <;>
    first
      | exact ⟨rfl, slot3_tail hsl⟩
      | exact ⟨rfl, slot2_head hsl⟩
      | exact ⟨rfl, (h0 rfl rfl).symm⟩
      | exact ⟨rfl, (h9 rfl rfl).symm⟩


theorem rec_s0_1 (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (Sn : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount st) (hs : st = .s0) (hj1 : (j : ℕ) = 1) :
    ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).root = subj ∧
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).child = op0ResF sv ax Sn subj ∧
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).axis = ax (Sn + 2) ∧
      joinRecordAxis st ax Sn j = ax (Sn + 2) := by
  subst hs; rcases j with ⟨j, hj3⟩; simp only at hj1; subst hj1; exact ⟨rfl, rfl, rfl, rfl⟩


theorem rec_s9_2 (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (Sn : ℕ)
    (subj f : Noun) (kids : List ComputeRowSkeleton) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount st) (hs : st = .s9) (hj2 : (j : ℕ) = 2) :
    ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).root = (kidSkel kids 0).evaluation ∧
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).child = (kidSkel kids 1).formula ∧
      ((c2SkeletonRowF q sv ax st Sn subj f kids).memoryRecord j hj).axis = ax (Sn + 3) ∧
      joinRecordAxis st ax Sn j = ax (Sn + 3) := by
  subst hs; rcases j with ⟨j, hj3⟩; simp only at hj2; subst hj2; exact ⟨rfl, rfl, rfl, rfl⟩

section JoinLabel

variable {Kf : Type} [Field Kf] [DecidableEq Kf]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ} {q : ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuelF q (fun l : (State × DTcomp Kf) × ℕ => l.1.1)
  (fun l : (State × DTcomp Kf) × ℕ => l.2) sv ax

/-- The join's row at a node is the field skeleton row of the node's state and prefix; at an OP9
node with two children and positive fuel, the second kid's formula is the served arm. -/
theorem J_label (n : ℕ) (u : NTree ((State × DTcomp Kf) × ℕ)) (s f : Noun) :
    ∃ kids, (J n u s f).label = c2SkeletonRowF q sv ax u.label.1.1 u.label.2 s f kids ∧
      (u.label.1.1 = .s9 → u.children.length = 2 → 1 ≤ n →
        (kidSkel kids 1).formula = op9ArmF sv ax u.label.2 (kidSkel kids 0).evaluation) := by
  cases n with
  | zero =>
      cases u with
      | node row ch => exact ⟨[], rfl, fun _ _ h => absurd h (by omega)⟩
  | succ n =>
      cases u with
      | node row ch =>
          by_cases hs : row.1.1 = .s9 ∧ ch.length = 2
          · obtain ⟨hst, hlen⟩ := hs
            match ch, hlen with
            | [c0, c1], _ =>
                rw [SVJoinAssemblyF.J_s9 (sv := sv) (ax := ax) (q := q) s f row c0 c1 hst]
                dsimp only [NTree.label]
                rw [hst]
                refine ⟨_, rfl, fun _ _ _ => ?_⟩
                simp only [kidSkel, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
                exact SVJoinAssemblyF.J_formula (sv := sv) (ax := ax) (q := q) _ _ _ _
          · refine ⟨_, rfl, fun h1 h2 _ => absurd ⟨h1, h2⟩ hs⟩

end JoinLabel

/-- `Batch1171.traceRec` is the frame's `traceRecOf`. -/
theorem traceRec_eq {Kf : Type} [Field Kf] (row : (State × DTcomp Kf) × ℕ) (j : ℕ) :
    Nock.RedTeam.Batch1171.traceRec row j = traceRecOf row j := by
  rcases j with _ | _ | _ <;> rfl

/-! ## 2. `RecOK` at a join row -/

section RecOK

variable {Kf : Type} [Field Kf] [DecidableEq Kf] [Fintype Kf] [CharP Kf (ringChar Kf)]

/-- **`RecOK` at a field join row** from per-record served data. -/
theorem recOK_row (z : Kf) (q W : ℕ) (hcast : Set.InjOn (fun k : ℕ => (k : Kf)) (Set.Iio q))
    (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (row : (State × DTcomp Kf) × ℕ) (subj f : Noun)
    (kids : List ComputeRowSkeleton)
    (H : ∀ (j : Fin 3) (hj : (j : ℕ) < Nock.Framework.recordCount row.1.1),
      (∃ rt ch : Noun,
        enc z rt = (traceRecOf row j).root ∧ enc z ch = (traceRecOf row j).child ∧
        Noun.slot (joinRecordAxis row.1.1 ax row.2 j) rt = some ch ∧
        BoundedBy q rt ∧
        (((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root.leaves ≤ W →
          SepSeed z ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root rt) ∧
        (row.1.1 = .s0 → (j : ℕ) = 1 → ch = sv .verify_child (row.2 + 2)) ∧
        (row.1.1 = .s9 → (j : ℕ) = 2 →
          (kidSkel kids 1).formula = op9ArmF sv ax row.2 (kidSkel kids 0).evaluation ∧
            ch = sv .verify_child (row.2 + 3))) ∨

      ((((row.1.1 = .s0 ∧ (j : ℕ) = 1) ∨ (row.1.1 = .s9 ∧ (j : ℕ) = 2 ∧
          (kidSkel kids 1).formula = op9ArmF sv ax row.2 (kidSkel kids 0).evaluation)) ∧
        joinRecordAxis row.1.1 ax row.2 j = 1 ∧
        (traceRecOf row j).child = (traceRecOf row j).root)) ∨

      ((enc z ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root =
            (traceRecOf row j).root →
          ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root.leaves ≤ W →
          BoundedBy q ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root →
          ∃ ch : Noun, Noun.slot (joinRecordAxis row.1.1 ax row.2 j)
              ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root = some ch ∧
            enc z ch = (traceRecOf row j).child) ∧
        ¬ (row.1.1 = .s0 ∧ (j : ℕ) = 1) ∧ ¬ (row.1.1 = .s9 ∧ (j : ℕ) = 2))) :
    Nock.RedTeam.Batch1171.RecOK z q W row (c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids) := by
  intro j hj henc hW hb
  rw [traceRec_eq] at henc ⊢
  rcases H j hj with ⟨rt, ch, h1, h2, h3, hbrt, hsep, h0, h9⟩ | ⟨hid, hax1, hcr⟩ | ⟨hinl, hn0, hn9⟩
  rotate_left
  ·
    have hrec : ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).axis = 1 ∧
        ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).child =
          ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root := by
      rcases hid with ⟨hs0, hj1⟩ | ⟨hs9, hj2, hf9⟩
      · obtain ⟨hr, hc, ha, hja⟩ := rec_s0_1 q sv ax row.1.1 row.2 subj f kids j hj hs0 hj1
        have h2 : ax (row.2 + 2) = 1 := hja ▸ hax1
        exact ⟨ha.trans h2, by rw [hc, hr, op0ResF_of_eq subj h2]⟩
      · obtain ⟨hr, hc, ha, hja⟩ := rec_s9_2 q sv ax row.1.1 row.2 subj f kids j hj hs9 hj2
        have h3 : ax (row.2 + 3) = 1 := hja ▸ hax1
        exact ⟨ha.trans h3, by rw [hc, hr, hf9, op9ArmF_of_eq _ h3]⟩
    refine ⟨?_, ?_⟩
    · rw [hrec.1, hrec.2]; simp [Noun.slot]
    · rw [hrec.2, henc]; exact hcr.symm
  · obtain ⟨ch, hsl, hch2⟩ := hinl henc hW hb
    obtain ⟨hax, hch⟩ := rec_struct q sv ax row.1.1 row.2 subj f kids j hj ch hsl
      (fun a b => absurd ⟨a, b⟩ hn0) (fun a b => absurd ⟨a, b⟩ hn9)
    refine ⟨?_, ?_⟩
    · rw [hax, hch]; exact hsl
    · rw [hch]; exact hch2
  have hroot : ((c2SkeletonRowF q sv ax row.1.1 row.2 subj f kids).memoryRecord j hj).root = rt :=
    noun_eq_of_enc_eq z _ _ (hsep hW) hcast hb hbrt (henc.trans h1.symm)
  have hsl := h3
  rw [← hroot] at hsl

  have h0' : row.1.1 = .s0 → (j : ℕ) = 1 → ch = op0ResF sv ax row.2 subj := by
    intro hs0 hj1
    obtain ⟨hr, -, -, hja⟩ := rec_s0_1 q sv ax row.1.1 row.2 subj f kids j hj hs0 hj1
    by_cases ha : ax (row.2 + 2) = 1
    · rw [op0ResF_of_eq subj ha]
      rw [hja, ha, hr] at hsl
      simp only [Noun.slot, Option.some.injEq] at hsl
      exact hsl.symm
    · rw [op0ResF_of_ne subj ha]; exact h0 hs0 hj1
  have h9' : row.1.1 = .s9 → (j : ℕ) = 2 → ch = (kidSkel kids 1).formula := by
    intro hs9 hj2
    obtain ⟨hf9, hch9⟩ := h9 hs9 hj2
    obtain ⟨hr, -, -, hja⟩ := rec_s9_2 q sv ax row.1.1 row.2 subj f kids j hj hs9 hj2
    rw [hf9]
    by_cases ha : ax (row.2 + 3) = 1
    · rw [op9ArmF_of_eq _ ha]
      rw [hja, ha, hr] at hsl
      simp only [Noun.slot, Option.some.injEq] at hsl
      exact hsl.symm
    · rw [op9ArmF_of_ne _ ha]; exact hch9
  obtain ⟨hax, hch⟩ := rec_struct q sv ax row.1.1 row.2 subj f kids j hj ch hsl h0' h9'
  refine ⟨?_, ?_⟩
  · rw [hax, hch, hroot]; exact h3
  · rw [hch]; exact h2

end RecOK

/-! ## 3. The premises and the obligation -/

section Generic

variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp] [CharP Kfp (ringChar Kfp)]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {R : RecordView F K Kio Kfp Key C S hC m} {Z : SeedSpec Φ K Kfp} {I : IOCoinSpec Φ K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)

/-- **The compute instance's row obligation** (`CtxW.row`, M0 discharges it): outside the compute
summands, every node of the compute tree carries `Batch1171.RowFacts` at the B0 axis oracle. -/
def rowFactsAt : Prop :=
  ∀ (V : VerifierData F K hC S) (x : CF.Msg0) (ρ : Fin nAcc → Kio) (χ : Coins Φ K)
    (Q : Fin C.width → F[X])
    (h : RAP.SatisfiesWithPreprocessing (CF.chip V x ρ χ) (fun j => Q (Fin.cast (CF.chip_width V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ CF.summands V x, ¬ s.mem (Q, Qm) χ) →
    ∀ u, InTree (CF.tree V x Q χ) u →
      Nock.RedTeam.Batch1171.RowFacts (ax := CF.axB0 V x (b0 Q) (fun t => b0 (Qm t)))
        (Z.seed χ) (ringChar Kfp) u

/-- **The four premises beyond I0 r2** (each a one-line instance obligation; reported). -/
structure ExtraPremises : Prop where
  /-- The IO mechanism's condition on the compute request records (`MF.serves` needs it). -/
  reqCond : ∀ (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0) (ρ : Fin nAcc → Kio)
    (χ : Coins Φ K) (Q : Fin C.width → F[X])
    (h : RAP.SatisfiesWithPreprocessing (CF.chip V x ρ χ) (fun j => Q (Fin.cast (CF.chip_width V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ CF.summands V x ++ MF.summands V y, ¬ s.mem (Q, Qm) χ) →
    MF.reqCond V (fun a => (CF.reqFacts V x ρ χ Q h a).records) χ
  /-- OP9's arm record is keyed at the join's arm lookup (twin of `recKey_s0`). -/
  recKey_s9 : ∀ V x b S', CF.recKey V x b .s9 S' 2 = CF.keyOf V x b .verify_child (S' + 3)
  /-- The served roots are nouns over `𝔽`. -/
  served_bounded : ∀ V y b κ, κ ∈ MF.servedKeys V y b → BoundedBy (ringChar Kfp) (MF.servedRoot V y b κ)
  /-- The fingerprint field has the base characteristic. -/
  char_eq : ringChar Kfp = ringChar K

variable {CF MF}

theorem q_eq (hP : ExtraPremises CF MF) : ringChar Kfp = ringChar F :=
  hP.char_eq.trans (Algebra.ringChar_eq F K).symm

/-- The join at the full tree is the B0 join. -/
theorem join_eq_joinB0 (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (Qc : Fin C.width → F[X]) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]) (χ : Coins Φ K) :
    c2JoinFuelF (ringChar Kfp) (fun l : (State × DTcomp Kfp) × ℕ => l.1.1)
        (fun l : (State × DTcomp Kfp) × ℕ => l.2) (svB0 CF MF V x y (b0Tr (Qc, Qm)))
        (CF.axB0 V x (b0 Qc) (fun t => b0 (Qm t))) (CF.tree V x Qc χ).size (CF.tree V x Qc χ)
        V.claim.subject V.claim.formula =
      joinB0 CF MF V x y (b0Tr (Qc, Qm)) := by
  rw [c2JoinFuelF_factor]
  have hsh : mapNTree (fun l : (State × DTcomp Kfp) × ℕ => (l.1.1, l.2)) (CF.tree V x Qc χ) =
      CF.shape V x (b0 Qc) := CF.tree_shape V x Qc χ
  have hsz : (CF.tree V x Qc χ).size = (CF.shape V x (b0 Qc)).size := by
    rw [← hsh, size_mapNTree']
  rw [hsz, hsh]
  rfl

theorem tree_size_le (V : VerifierData F K hC S) (x : CF.Msg0) (Qc : Fin C.width → F[X])
    (χ : Coins Φ K) :
    (CF.tree V x Qc χ).size ≤ V.N := by
  have hsh : mapNTree (fun l : (State × DTcomp Kfp) × ℕ => (l.1.1, l.2)) (CF.tree V x Qc χ) =
      CF.shape V x (b0 Qc) := CF.tree_shape V x Qc χ
  rw [← size_mapNTree' (fun l : (State × DTcomp Kfp) × ℕ => (l.1.1, l.2)), hsh]
  exact CF.shape_size V x _

/-- The window is at least the field-run window and the memory window bound. -/
theorem leaf_le_windowW (V : VerifierData F K hC S) (y : MF.Msg0) :
    leafBoundF (ringChar Kfp) V.N V.claim ≤ windowW MF V y := le_max_left _ _

/-- **The r2 `CtxWObligation`**, discharged. -/
theorem ctxW_of_accepts (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF) (lowW : ℕ → ℕ)
    (hlowW : ∀ W, (SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W).card ≤ lowW W)
    (V : VerifierData F K hC S) (hV : V.Checks (consumerBound CF MF V) (ringChar Kio)) (msg : Messages CF MF) (χ : Coins Φ K)
    (hacc : AcceptsV V msg χ)
    (hout : ∀ s ∈ allSummands (CF := CF) (MF := MF) V msg.msg0C msg.msg0M
      (jointSummands CF MF lowW hlowW), ¬ s.mem (msg.traces χ) χ) :
    RootGoodFJoin.CtxW
      (sv := svB0 CF MF V msg.msg0C msg.msg0M (b0Tr (msg.Qc χ, msg.Qm χ)))
      (ax := CF.axB0 V msg.msg0C (b0 (msg.Qc χ)) (fun t => b0 (msg.Qm χ t)))
      (Z.seed χ) (ringChar Kfp) (windowW MF V msg.msg0M)
      (CF.tree V msg.msg0C (msg.Qc χ) χ).size
      (CF.tree V msg.msg0C (msg.Qc χ) χ) V.claim.subject V.claim.formula := by
  classical
  -- names
  set x := msg.msg0C with hx
  set y := msg.msg0M with hy
  set Qc := msg.Qc χ with hQc
  set Qm := msg.Qm χ with hQm
  set z := Z.seed χ with hz_def
  set W := windowW MF V y with hW_def
  set b := b0Tr (Qc, Qm) with hb_def
  have htr : msg.traces χ = (Qc, Qm) := rfl
  -- the summands, split
  have hCF : ∀ s ∈ CF.summands V x, ¬ s.mem (Qc, Qm) χ := fun s hs =>
    htr ▸ hout s (by simp [allSummands, hs])
  have hMF : ∀ s ∈ MF.summands V y, ¬ s.mem (Qc, Qm) χ := fun s hs =>
    htr ▸ hout s (by simp [allSummands, hs])
  have hJt : ∀ s ∈ jointSummands CF MF lowW hlowW V x y, ¬ s.mem (Qc, Qm) χ := fun s hs =>
    htr ▸ hout s (by simp [allSummands, hs])
  have hz0 : z ∉ ({0} : Finset Kfp) := fun h =>
    hJt (zeroSummand (F := F) (C := C) (S := S) (Z := Z)) (by simp [jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (zeroSummand (F := F) (C := C) (S := S) (Z := Z)).mem (Qc, Qm) χ)
  have hlow : z ∉ SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W := fun h =>
    hJt (lowSummand MF lowW hlowW V y) (by simp [jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (lowSummand MF lowW hlowW V y).mem (Qc, Qm) χ)
  have hcen : z ∉ PreSeedCensus.pairBadSeeds (K := Kfp) W (censusPairs CF MF V x y b) := fun h =>
    hJt (censusSummand CF MF V x y) (by simp [jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (censusSummand CF MF V x y).mem (Qc, Qm) χ)
  have hrec : z ∉ PreSeedCensus.pairBadSeeds (K := Kfp) W (recPairs CF MF V x y b) := fun h =>
    hJt (recSummand CF MF V x y) (by simp [jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (recSummand CF MF V x y).mem (Qc, Qm) χ)
  have hinl : z ∉ PreSeedCensus.pairBadSeeds (K := Kfp) W (inlinePairsList CF MF V x y b) := fun h =>
    hJt (inlineSummand CF MF V x y) (by simp [jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (inlineSummand CF MF V x y).mem (Qc, Qm) χ)
  -- the base facts
  have hq : ringChar Kfp = ringChar F := q_eq hP
  have hq25 : 25 ≤ ringChar Kfp := hq ▸ hV.hp
  have hcast : Set.InjOn (fun k : ℕ => (k : Kfp)) (Set.Iio (ringChar Kfp)) :=
    fun a ha b hb hab => CharP.natCast_injOn_Iio Kfp (ringChar Kfp) ha hb hab
  have hJ := join_eq_joinB0 (CF := CF) (MF := MF) V x y Qc Qm χ
  set t := CF.tree V x Qc χ with ht_def
  refine
    { hz := fun h => hz0 (by simp [h])
      hq12 := by omega
      hcast := hcast
      hW1 := (one_le_leafBoundF _ _ _).trans (leaf_le_windowW V y)
      hlow := ?_
      hD := le_rfl
      calls := callsWithin_leafBoundF V.claim (tree_size_le V x Qc χ) (leaf_le_windowW V y)
      row := hrow V x (msg.requests χ) χ Qc hacc.compute Qm hCF
      recs := ?_
      census := ?_ }
  · -- the low-order window
    intro d hd1 hdW hzd
    apply hlow
    unfold SizeWindowCounting.lowOrderRootSeeds
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdW⟩,
      (Polynomial.mem_nthRootsFinset (by omega) (1 : Kfp)).mpr hzd⟩
  · -- served records
    intro u s f hpr
    have hu : InTree t u := inTree_of_pr hpr
    have hR := hrow V x (msg.requests χ) χ Qc hacc.compute Qm hCF u hu
    obtain ⟨kids, hv, h9kids⟩ := J_label (sv := svB0 CF MF V x y b)
      (ax := CF.axB0 V x (b0 Qc) (fun t => b0 (Qm t))) (q := ringChar Kfp) u.size u s f
    -- the positional pairing with the shape
    have hpr' := pr_map (fun l : (State × DTcomp Kfp) × ℕ => (l.1.1, l.2)) hpr
    have hsh : mapNTree (fun l : (State × DTcomp Kfp) × ℕ => (l.1.1, l.2)) t = CF.shape V x (b0 Qc) :=
      CF.tree_shape V x Qc χ
    rw [hsh, hJ] at hpr'
    have hzip := pr_mem_zipLabels hpr'
    rw [mapNTree_label, hv] at hzip
    rw [hv]
    apply recOK_row z (ringChar Kfp) W hcast
    intro j hj
    by_cases hjin : (j : ℕ) < CF.inlineRecords u.label.1.1
    ·
      refine Or.inr (Or.inr ⟨fun henc hW hb => ?_, (CF.inline_not_read _ _ hjin).1,
        (CF.inline_not_read _ _ hjin).2⟩)
      refine CF.inline_records V x (msg.requests χ) χ Qc hacc.compute Qm hCF u hu j hjin hj W _
        henc hW hb ?_
      intro p hp hl1 hl2
      by_contra hns
      apply hinl
      rw [PreSeedCensus.mem_pairBadSeeds_iff]
      refine ⟨p, List.mem_flatMap.mpr ⟨_, hzip, List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩⟩,
        hl1, hl2, hns⟩
      simp only [c2SkeletonRowF_state]
      rw [if_pos hjin]
      rw [recRootOf_of_lt]
      exact hp
    rcases CF.node_records V x (msg.requests χ) χ Qc hacc.compute Qm hCF u hu j (Nat.le_of_not_lt hjin) hj
      with ⟨a, r, hr, hroot, hchild, hkey, haxis⟩ | ⟨hid, hax1, hcr⟩
    swap
    ·
      refine Or.inr (Or.inl ⟨?_, hax1, hcr⟩)
      rcases hid with hid | ⟨hs9, hj2⟩
      · exact Or.inl hid
      · have hlen : u.children.length = 2 := by rw [hR.arity, hs9]; rfl
        exact Or.inr ⟨hs9, hj2, h9kids hs9 hlen (Nock.RedTeam.Batch1021.ntree_size_pos u)⟩
    refine Or.inl ?_
    have hreqs := hP.reqCond V x y (msg.requests χ) χ Qc hacc.compute Qm
      (fun s hs => by
        rcases List.mem_append.mp hs with h | h
        · exact hCF s h
        · exact hMF s h)
    have hio : ∀ a', I.pair χ ∉ FiniteIO.IOFailureEventW
        ((CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a').records ++
            MF.internal V y Qm χ a') (liftWts (MF.respRecords V y Qm χ a')) := by
      intro a' hmem
      have hl1 := CF.reqFacts_length V x (msg.requests χ) χ Qc hacc.compute a'
      have hl3 := MF.internal_length V y (msg.requests χ) (msg.msg2M χ) χ Qm hacc.memory a'
      have hl2 := MF.ioFacts_length V y (msg.requests χ) (msg.msg2M χ) χ Qm hacc.memory a'
      rw [CF.reqFacts_records] at hl1 hmem
      rw [MF.ioFacts_records] at hl2
      apply hJt (ioSummand CF MF V x y a') (by simp [jointSummands])
      rw [ioSummand_mem]
      unfold ioEventAt
      rw [if_pos ⟨by rw [List.length_append]; exact Nat.add_le_add hl1 hl3, hl2⟩]
      exact hmem

    have hcnt : ∀ a', ((CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a').records ++
        MF.internal V y Qm χ a').length < ringChar Kio := by
      intro a'
      have hl1 := CF.reqFacts_length V x (msg.requests χ) χ Qc hacc.compute a'
      have hl3 := MF.internal_length V y (msg.requests χ) (msg.msg2M χ) χ Qm hacc.memory a'
      have hc := hV.hcons a'
      unfold consumerBound at hc
      rw [List.length_append]
      omega
    have hserv := MF.serves V y (msg.requests χ) (msg.msg2M χ) χ Qm hacc.memory Qc
      (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).records) hreqs
      (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).sum_eq)
      (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).ne_zero) hio hcnt hMF a r hr

    obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hserv
    obtain ⟨hκ, hsr, hsc, hsl⟩ :=
      MF.response_sound V y (msg.requests χ) (msg.msg2M χ) χ Qm hacc.memory Qc
        (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).records) hreqs
        (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).sum_eq)
        (fun a => (CF.reqFacts V x (msg.requests χ) χ Qc hacc.compute a).ne_zero) hio hcnt hMF a q hq
    rw [hqr] at hκ hsr hsc hsl
    rw [hkey] at hκ hsr hsc hsl
    rw [haxis] at hsl
    set κ := CF.recKey V x (b0 Qc) u.label.1.1 u.label.2 j with hκ_def
    refine ⟨MF.servedRoot V y (fun t => b0 (Qm t)) κ, MF.served V y (fun t => b0 (Qm t)) κ,
      ?_, ?_, hsl, hP.served_bounded V y _ κ hκ, ?_, ?_, ?_⟩
    · rw [← hsr, hroot]
    · rw [← hsc, hchild]
    · intro hWr
      by_contra hns
      apply hrec
      rw [PreSeedCensus.mem_pairBadSeeds_iff]
      refine ⟨_, List.mem_flatMap.mpr ⟨_, hzip, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩,
        ?_, ?_, ?_⟩
      · rw [recRootOf_of_lt]
        exact hWr
      · exact ((MF.served_leaves_le V y _ κ hκ).1.trans (MF.window_le V y _)).trans (le_max_right _ _)
      · rw [recRootOf_of_lt]
        exact hns
    · intro hs0 hj1
      have : κ = CF.keyOf V x (b0 Qc) .verify_child (u.label.2 + 2) := by
        rw [hκ_def, hs0]
        have := CF.recKey_s0 V x (b0 Qc) u.label.2
        rw [show (j : ℕ) = 1 from hj1] at *
        exact this
      rw [this]; rfl
    · intro hs9 hj2
      have hlen : u.children.length = 2 := by
        rw [hR.arity, hs9]; rfl
      refine ⟨h9kids hs9 hlen (Nock.RedTeam.Batch1021.ntree_size_pos u), ?_⟩
      have : κ = CF.keyOf V x (b0 Qc) .verify_child (u.label.2 + 3) := by
        rw [hκ_def, hs9]
        have := hP.recKey_s9 V x (b0 Qc) u.label.2
        rw [show (j : ℕ) = 2 from hj2] at *
        exact this
      rw [this]; rfl
  · -- the NPR census
    intro u s f _ hw
    rw [hJ] at hw
    intro c hc hl hr
    by_contra hsep
    apply hcen
    rw [PreSeedCensus.mem_pairBadSeeds_iff]
    refine ⟨c.pair, List.mem_flatMap.mpr ⟨_, (mem_bfsForest _ _).mpr
      ⟨_, List.mem_singleton_self _, hw⟩, List.mem_map.mpr ⟨c, hc, rfl⟩⟩, hl, hr, hsep⟩

/-- **The root-result bridge and the claim** (`rootResult_bridgeV`): outside the summands,
acceptance proves the claim under field semantics. -/
theorem holdsF_of_accepts (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF) (lowW : ℕ → ℕ)
    (hlowW : ∀ W, (SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W).card ≤ lowW W)
    (V : VerifierData F K hC S) (hV : V.Checks (consumerBound CF MF V) (ringChar Kio)) (msg : Messages CF MF) (χ : Coins Φ K)
    (hacc : AcceptsV V msg χ)
    (hout : ∀ s ∈ allSummands (CF := CF) (MF := MF) V msg.msg0C msg.msg0M
      (jointSummands CF MF lowW hlowW), ¬ s.mem (msg.traces χ) χ) :
    HoldsF (ringChar K) V.claim := by
  classical
  have C := ctxW_of_accepts hrow hP lowW hlowW V hV msg χ hacc hout
  set x := msg.msg0C
  set y := msg.msg0M
  set Qc := msg.Qc χ
  set Qm := msg.Qm χ
  set z := Z.seed χ
  set W := windowW MF V y
  set b := b0Tr (Qc, Qm)
  set t := CF.tree V x Qc χ
  have htr : msg.traces χ = (Qc, Qm) := rfl
  have hCF : ∀ s ∈ CF.summands V x, ¬ s.mem (Qc, Qm) χ := fun s hs =>
    htr ▸ hout s (by simp [allSummands, hs])
  have hroot : z ∉ PreSeedCensus.pairBadSeeds (K := Kfp) W (rootPairs CF MF V x y b) := fun h =>
    hout (rootSummand CF MF V x y) (by simp [allSummands, jointSummands]) ((seedSummand_mem Z _ _ _ _ χ).2 h :
      (rootSummand CF MF V x y).mem (Qc, Qm) χ)
  have hq : ringChar Kfp = ringChar F := q_eq hP
  have hq1 : 1 < ringChar Kfp := by have := hV.hp; omega
  have bs : BoundedBy (ringChar Kfp) V.claim.subject := hq ▸ hV.hclaim.1
  have bf : BoundedBy (ringChar Kfp) V.claim.formula := hq ▸ hV.hclaim.2.1
  have br : BoundedBy (ringChar Kfp) V.claim.result := hq ▸ hV.hclaim.2.2
  obtain ⟨hs, hf, he⟩ := CF.root_binds V x (msg.requests χ) χ Qc hacc.compute Qm hCF
  have hz : z ≠ 0 := C.hz
  obtain ⟨hR, hA⟩ := RootGoodFJoin.root_goodF C bs bf hs hf
  obtain ⟨fuel, hrun⟩ := RootGoodFJoin.root_holdsF C bs bf hs hf
  have hJ := join_eq_joinB0 (CF := CF) (MF := MF) V x y Qc Qm χ
  -- the root evaluation binds the root row's `e`
  have hb := SVReadyFuelF.computeTreeBinds_of_chipReady hz (le_refl t.size) hR hs
  have hrowb := hb.root
  rw [mapNTree_label] at hrowb
  have he1 := hrowb.2.2.2.2.2.1
  set ev := (c2JoinFuelF (ringChar Kfp) (fun l : (State × DTcomp Kfp) × ℕ => l.1.1)
    (fun l : (State × DTcomp Kfp) × ℕ => l.2) (svB0 CF MF V x y b)
    (CF.axB0 V x (b0 Qc) (fun t => b0 (Qm t))) t.size t V.claim.subject V.claim.formula).label.evaluation
    with hev
  have henc : enc z ev = enc z V.claim.result := by
    unfold bindFP at he1 he
    rw [← he1, ← he]
  have hevW : ev.leaves ≤ W :=
    (C.calls 0 _ _ (by have := Nock.RedTeam.Batch1021.ntree_size_pos t; omega) CallTreeF.root).2.2
      fuel ev hrun
  have hresW : V.claim.result.leaves ≤ W :=
    (result_le_leafBoundF _ _ _).trans (leaf_le_windowW V y)
  have hsep : SepSeed z ev V.claim.result := by
    by_contra hns
    apply hroot
    rw [PreSeedCensus.mem_pairBadSeeds_iff]
    refine ⟨(ev, V.claim.result), ?_, hevW, hresW, hns⟩
    simp only [rootPairs, List.mem_singleton]
    rw [hev, hJ]
  have hbe : BoundedBy (ringChar Kfp) ev :=
    SVInductionGenericF.evalFBy_boundedBy _ hq1 fuel _ _ ev bs bf hrun
  have heq : ev = V.claim.result := noun_eq_of_enc_eq z _ _ hsep C.hcast hbe br henc
  refine ⟨fuel, ?_⟩
  rw [← hP.char_eq, ← heq]
  exact hrun

/-! ## 4. The statement -/

/-- **`standalone_generic`, at any low-order weight.** -/
theorem standalone_generic_at (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF) (lowW : ℕ → ℕ)
    (hlowW : ∀ W, (SizeWindowCounting.lowOrderRootSeeds (K := Kfp) W).card ≤ lowW W) :
    StandaloneThm54Statement CF MF (jointSummands CF MF lowW hlowW) where
  soundness V hV msg hst := by
    classical
    have hsub : (Finset.univ.filter fun χ : Coins Φ K =>
          AcceptsV V msg χ ∧ ¬ HoldsF (ringChar K) V.claim) ⊆
        unionEvent (allSummands (CF := CF) (MF := MF) V msg.msg0C msg.msg0M
          (jointSummands CF MF lowW hlowW)) msg.traces := by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hno
      push Not at hno
      exact hχ.2 (holdsF_of_accepts hrow hP lowW hlowW V hV msg χ hχ.1 hno)
    have hpos : (0 : ℚ) ≤ Fintype.card (Coins Φ K) := by positivity
    refine le_trans (div_le_div_of_nonneg_right ?_ hpos) (union_prob_le _ msg.traces hst)
    exact_mod_cast Finset.card_le_card hsub
  completeness HC HM _ _ := by
    classical
    have hQ : TracesStaged Φ C S (fun χ => (CF.honestQ HC χ, MF.honestQ HM χ)) :=
      ⟨CF.honest_staged HC, fun t => MF.honest_staged HM t⟩
    have h := union_prob_le (CF.honestBad HC ++ MF.honestBad HM)
      (fun χ => (CF.honestQ HC χ, MF.honestQ HM χ)) hQ
    refine le_of_eq_of_le ?_ h
    congr 2

/-- **`standalone_generic`**. -/
theorem standalone_generic (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF) :
    StandaloneThm54Statement CF MF (jointSummandsStd CF MF) :=
  standalone_generic_at hrow hP _ (SizeWindowCounting.lowOrderRootSeeds_card_le (K := Kfp))

open Classical in
/-- **The fixed-trace corollary** (`tracesStaged_const`): traces fixed before all coins. -/
theorem standalone_fixed (hrow : rowFactsAt CF) (hP : ExtraPremises CF MF)
    (V : VerifierData F K hC S) (hV : V.Checks (consumerBound CF MF V) (ringChar Kio)) (qc : Fin C.width → F[X])
    (qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]) (x : CF.Msg0) (y : MF.Msg0)
    (requests : Coins Φ K → Fin nAcc → Kio) (msg2 : Coins Φ K → MF.Msg2) :
    ((Finset.univ.filter fun χ : Coins Φ K =>
        AcceptsV V (⟨fun _ => qc, fun _ => qm, x, y, requests, msg2⟩ : Messages CF MF) χ ∧
          ¬ HoldsF (ringChar K) V.claim).card : ℚ) / Fintype.card (Coins Φ K) ≤
      epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) :=
  (standalone_generic hrow hP).soundness V hV _ (tracesStaged_const (Φ := Φ) (K := K) (qc, qm))

end Generic

end

end Nock.NockVMROM.Thm54.SVFrame
