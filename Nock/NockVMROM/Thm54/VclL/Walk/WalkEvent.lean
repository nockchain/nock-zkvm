/-
  Nock/NockVMROM/Thm54/VclL/Walk/WalkEvent.lean

  `Nock/Walk.lean` is used unedited.

  * `walk_records_card`: `Walk_IOP_forest_final_card_of_label` over the coin field `𝕂`
    (`St = stateSep X 62`, `labelOf = Prod.snd`, `enc`, `enc_det`): the number of `(α, γ)` at which
    the forest walk accepts while some record is not the true slot is `≤ |𝕂|·h + |𝕂|·14h`, i.e.
    probability `≤ 15h/|𝕂|` over `|𝕂|²`.
  * `pairCoinSummand` (Census shape on coins `{i, j}`), `vclWalkSummand` on `frameVCL` coins
    `{0, 1}` = `(αC, γ)` (`MemSoundnessFamily.lean`'s `frameVCL`), reading `round1Coins` =
    `{z₁, z₂, a, b, c}`, disjointness by `decide`, weight `|𝕂|·15H`.
  * `records_outside_summand`: accepting at `(χ 0, χ 1)` outside the walk event ⟹ all records genuine.

  Hypotheses kept explicit for W2/W3: `WalkHyps` (the walk gates' round-0/1 facts), `RootGate`,
  `KeysExported`, and the summand's staging input `hconst`.
-/
import Nock.NockVMROM.Thm54.VclL.Walk.WalkChain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.WalkVCL

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)

/-! ## 1. The count over the COIN field `𝕂`, Walk.lean unedited -/

section Card
open Nock.NockVMROM.Thm54.T0Tower
variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod q) K] (δ : K) [Fact (¬ IsSquare δ)]

open scoped Classical in
/-- **The walk record count over `(α, γ) ∈ 𝕂 × 𝕂`** (forest seed, `initial_count = α^kroots`):
accepting while some walk record is NOT the true slot of its root happens at
`≤ |𝕂|·h + |𝕂|·14h` pairs, i.e. probability `≤ 15h/|𝕂|`; given the committed row facts (F on
every row, fanout, queue validity), the root gate, exported keys, and `z` outside T2 ∪ dyck-root. -/
theorem walk_records_card (hq : 2 ^ 63 < q) {z : Quad δ} (hz : z ≠ 0)
    {tb : List (CellRow q (Quad δ))} {vl : List (VKey (Quad δ))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (X : List (XKey (Quad δ))) (hX : KeysExported tb X)
    (lbl : ℕ → LT q (Quad δ)) (clab : ℕ → ℕ → LT q (Quad δ)) (fo : ℕ → ℕ) {kroots h : ℕ}
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ 2) (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h → F X 62 (lbl i)
      (fun j : Fin 2 => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hRG : RootGate X lbl kroots) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc δ (lbl i))) (fun i l => rlc p.2 (enc δ (clab i l))) fo
            ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc δ (lbl i)) * p.1 ^ i)
            (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ AllRecordsGenuine z tb X lbl h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (15 - 1)) := by
  refine le_trans (Finset.card_le_card ?_)
    (Walk_IOP_forest_final_card_of_label (stateSep (q := q) X 62) Prod.snd
      (F_respects X 62) (enc δ) (enc_det δ) lbl clab fo hk hSf hvalid harity hfo hFcommit)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun hG => hp.2.2 (records_of_reconGoal hq hz htab hT2 hdy hX hk hRG hG)⟩

end Card

/-! ## 2. The two-coin walk `BadSummand` (Census shape) at `frameVCL` coins `0, 1` = `αC, γ` -/

section Summand
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Any bad set of coin PAIRS `(χ i, χ j) ∈ 𝕂 × 𝕂` as a summand on coins `{i, j}`, reading `dep`. -/
noncomputable def pairCoinSummand (Φ : CoinFrame) (i j : Fin Φ.n) (dep : Finset (Fin Φ.n))
    (hdisj : Disjoint ({i, j} : Finset (Fin Φ.n)) dep) {Tr : Type}
    (Staged : (Coins Φ K → Tr) → Prop) (bad : Tr → Finset (K × K)) (W : ℕ)
    (hW : ∀ tr, (bad tr).card ≤ W)
    (hreads : ∀ Q, Staged Q → ReadsOnC Φ dep (fun χ => bad (Q χ))) :
    BadSummand Φ K Tr Staged where
  coins := {i, j}
  dep := dep
  disj := hdisj
  badSet tr _ := Finset.univ.filter fun f => (f ⟨i, by simp⟩, f ⟨j, by simp⟩) ∈ bad tr
  weight := W
  card_le tr _ := by
    refine le_trans ?_ (hW tr)
    refine Finset.card_le_card_of_injOn (fun f => (f ⟨i, by simp⟩, f ⟨j, by simp⟩)) ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      exact hf
    · intro f _ f' _ h
      simp only [Prod.mk.injEq] at h
      funext x
      obtain ⟨x, hx⟩ := x
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact h.1
      · rw [Finset.mem_singleton] at hx'; subst hx'; exact h.2
  readsOn Q hQ χ χ' hχ := by
    have e : bad (Q χ) = bad (Q χ') := hreads Q hQ χ χ' hχ
    dsimp only
    rw [e]

/-- The walk part of a trace: its committed rows (labels, child labels, fanouts, roots) and the
export keys its rows consume. -/
structure WalkData (q : ℕ) (Kfp : Type) where
  X : List (XKey Kfp)
  lbl : ℕ → LT q Kfp
  clab : ℕ → ℕ → LT q Kfp
  fo : ℕ → ℕ
  kroots : ℕ
  h : ℕ

variable {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] (δ : K) [Fact (¬ IsSquare δ)]

/-- The round-0/1 facts the walk gates give (W2's chip must prove these from the trace). -/
def WalkHyps (W : WalkData q (Quad δ)) : Prop :=
  1 ≤ W.kroots ∧ W.kroots + Sf W.fo W.h = W.h ∧ BFSValidF W.kroots W.fo W.h ∧
    (∀ i, W.fo i ≤ 2) ∧ (∀ i, 1 ≤ i → i ≤ W.h → W.fo i = fanout (W.lbl i).1) ∧
    (∀ i, 1 ≤ i → i ≤ W.h → F W.X 62 (W.lbl i)
      (fun j : Fin 2 => if (j : ℕ) < W.fo i then some (W.clab i (j + 1)) else none))

open scoped Classical in
/-- The walk event over `(α, γ) ∈ 𝕂 × 𝕂`. -/
noncomputable def walkEvent (W : WalkData q (Quad δ)) : Finset (K × K) :=
  Finset.univ.filter fun p : K × K => WalkHyps δ W ∧
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc p.2 (enc δ (W.lbl i))) (fun i l => rlc p.2 (enc δ (W.clab i l))) W.fo
        ln count acc p.1 (∑ i ∈ Finset.Icc 1 W.kroots, rlc p.2 (enc δ (W.lbl i)) * p.1 ^ i)
        (p.1 ^ W.kroots) W.h ∧ acc W.h = 0) ∧
    ¬ ForestReconGoal (stateSep (q := q) W.X 62) W.lbl W.kroots W.h

open scoped Classical in
theorem walkEvent_card (W : WalkData q (Quad δ)) {H : ℕ} (hH : W.h ≤ H) :
    (walkEvent δ W).card ≤ Fintype.card K * (15 * H) := by
  by_cases hyp : WalkHyps δ W
  · obtain ⟨hk, hSf, hvalid, harity, hfo, hF⟩ := hyp
    have hc := Walk_IOP_forest_final_card_of_label (stateSep (q := q) W.X 62) Prod.snd
      (F_respects W.X 62) (enc δ) (enc_det δ) W.lbl W.clab W.fo hk hSf hvalid harity hfo hF
    refine le_trans (Finset.card_le_card ?_) (hc.trans ?_)
    · intro p hp
      simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.2.1, hp.2.2⟩
    · have : Fintype.card K * W.h + Fintype.card K * (W.h * (15 - 1)) =
          Fintype.card K * (15 * W.h) := by ring_nf
      rw [this]
      exact Nat.mul_le_mul_left _ (by omega)
  · have : walkEvent δ W = ∅ := by
      ext p; simp [walkEvent, hyp]
    rw [this]; simp

/-- The `frameVCL` coins sampled after round 0 (`z₁ z₂ a b c`): what B0/B1 columns may read. -/
def round1Coins : Finset (Fin frameVCL.n) :=
  {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩}

theorem walkCoins_disjoint :
    Disjoint ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin frameVCL.n)) round1Coins := by
  decide

/-- **The walk summand**: coins `{0, 1}` = `(αC, γ)` of `frameVCL`, reading `{z₁, z₂, a, b, c}`
(the labels are B0/B1), weight `|𝕂| · 15H` over `|𝕂|²` (= `15H/|𝕂|`). -/
noncomputable def vclWalkSummand {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (walkOf : Tr → WalkData q (Quad δ)) (H : ℕ) (hH : ∀ tr, (walkOf tr).h ≤ H)
    (hconst : ∀ Q, Staged Q → ReadsOnC frameVCL round1Coins (fun χ => walkOf (Q χ))) :
    BadSummand frameVCL K Tr Staged :=
  pairCoinSummand frameVCL ⟨0, by decide⟩ ⟨1, by decide⟩ round1Coins walkCoins_disjoint Staged
    (fun tr => walkEvent δ (walkOf tr)) (Fintype.card K * (15 * H))
    (fun tr => walkEvent_card δ (walkOf tr) (hH tr))
    (fun Q hQ χ χ' hχ => by simp only [hconst Q hQ χ χ' hχ])

theorem vclWalkSummand_shape {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (walkOf : Tr → WalkData q (Quad δ)) (H : ℕ) (hH hconst) :
    (vclWalkSummand δ Staged walkOf H hH hconst).coins.card = 2 ∧
    (vclWalkSummand δ Staged walkOf H hH hconst).dep = round1Coins ∧
    (vclWalkSummand δ Staged walkOf H hH hconst).weight = Fintype.card K * (15 * H) :=
  ⟨Finset.card_pair (by decide), rfl, rfl⟩

theorem vclWalkSummand_mem_iff {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (walkOf : Tr → WalkData q (Quad δ)) (H : ℕ) (hH hconst) (tr : Tr) (χ : Coins frameVCL K) :
    (vclWalkSummand δ Staged walkOf H hH hconst).mem tr χ ↔
      (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∈ walkEvent δ (walkOf tr) := by
  exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- **Outside the walk summand, records are genuine**: at an accepting `(αC, γ) = (χ 0, χ 1)`,
`χ ∉` the summand's event, the walk facts, root gate, exported keys, `z` outside T2 ∪ dyck. -/
theorem records_outside_summand (hq : 2 ^ 63 < q) {z : Quad δ} (hz : z ≠ 0)
    {tb : List (CellRow q (Quad δ))} {vl : List (VKey (Quad δ))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (W : WalkData q (Quad δ)) (hX : KeysExported tb W.X) (hyp : WalkHyps δ W)
    (hRG : RootGate W.X W.lbl W.kroots) {α γ : K}
    (hacc : ∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc γ (enc δ (W.lbl i))) (fun i l => rlc γ (enc δ (W.clab i l))) W.fo
        ln count acc α (∑ i ∈ Finset.Icc 1 W.kroots, rlc γ (enc δ (W.lbl i)) * α ^ i)
        (α ^ W.kroots) W.h ∧ acc W.h = 0)
    (hout : (α, γ) ∉ walkEvent δ W) :
    AllRecordsGenuine z tb W.X W.lbl W.h := by
  have hG : ForestReconGoal (stateSep (q := q) W.X 62) W.lbl W.kroots W.h := by
    by_contra hng
    exact hout (by simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                   exact ⟨hyp, hacc, hng⟩)
  exact records_of_reconGoal hq hz htab hT2 hdy hX hyp.1 hRG hG

end Summand

end Nock.NockVMROM.Thm54.VclL.WalkVCL
