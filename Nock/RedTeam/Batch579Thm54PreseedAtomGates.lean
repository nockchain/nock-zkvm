/-
  Nock/RedTeam/Batch579Thm54PreseedAtomGates.lean

  **C3 of the pre-seed atom brief.**  Notes-only.  No production edit.

  Break attempts:
  * Distinct shapes have distinct Dyck words (`BTree.encode_injective`).
  * Atom-row selectors sit in the round-0 base block (`stateIndex.s1 = 1`).
  * `leaf₁ = leaf₂ = 0` is the power-basis specialisation of
    `leaf = algebraMap atom`; needed unless `coord b 1 = (1,0,0)`.
  * OP4 result is determined (`FP.inc`); OP3/OP5 results are `{0,1}`.
    A free column is required only for *underdetermined* atom leaves.
-/
import Nock.RedTeam.Batch578Thm54AdaptiveAtomForgery
import Nock.MemoryTable
import Nock.NockVMROM.Thm54.OptimizedComputeCodec
import Nock.NockVMROM.Thm54.CoordinateCompiler
import Nock.NockVMROM.Thm54.ComputeStagedTable
import Nock.AIR
import Nock.Dyck
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch579

open Nock
open Nock.ComputeTable
open Nock.GlobalCarryRecognizer
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.GigaChips
open Nock.RedTeam.Batch578
open scoped Classical Polynomial
attribute [local instance] Classical.propDecidable

variable {F K : Type*} [Field F] [Field K]

/-! ## Proposed gates (templates; no live column) -/

/-- Round-0 atom payload and the three coordinate pins of `leaf = algebraMap atom`
    under a basis with `coord b 1 = (1,0,0)`. -/
def leaf0MinusAtom (leafIdx atomIdx : ℕ) : CoeffExpr F :=
  .sub (.var .traceCur leafIdx) (.var .traceCur atomIdx)

def leaf1Zero (leafIdx : ℕ) : CoeffExpr F := .var .traceCur leafIdx
def leaf2Zero (leafIdx : ℕ) : CoeffExpr F := .var .traceCur leafIdx

def atomRowGate (selIdx : ℕ) (g : CoeffExpr F) : CoeffExpr F :=
  .mul (.var .traceCur selIdx) g

theorem leaf0MinusAtom_degree (leafIdx atomIdx : ℕ) :
    (leaf0MinusAtom (F := F) leafIdx atomIdx).degree = 1 := rfl

theorem leaf1Zero_degree (leafIdx : ℕ) :
    (leaf1Zero (F := F) leafIdx).degree = 1 := rfl

theorem leaf2Zero_degree (leafIdx : ℕ) :
    (leaf2Zero (F := F) leafIdx).degree = 1 := rfl

theorem atomRowGate_degree_le (selIdx : ℕ) (g : CoeffExpr F) :
    (atomRowGate selIdx g).degree = 1 + g.degree := rfl

/-- Honest atom fill: `enc z (atom k) = (z, 0, k)`. -/
theorem honest_atom_fill (z : K) (k : ℕ) :
    enc z (Noun.atom k) = FP.atomFP z (k : K) :=
  enc_atom z k

/-- The three proposed pins hold of an honest atom under `coord 1 = (1,0,0)`. -/
def HonestAtomPins (atom leaf0 leaf1 leaf2 : F) : Prop :=
  leaf0 = atom ∧ leaf1 = 0 ∧ leaf2 = 0

theorem honest_atom_pins_of_base (atom : F) :
    HonestAtomPins atom atom 0 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Gate evaluation: `leaf₀ − atom = 0` on a row env. -/
theorem leaf0MinusAtom_eval_zero (leafIdx atomIdx : ℕ) (env : Env F)
    (h : env.trace leafIdx = env.trace atomIdx) :
    (leaf0MinusAtom (F := F) leafIdx atomIdx).eval env = 0 := by
  simp [leaf0MinusAtom, CoeffExpr.eval, h]

theorem leaf1Zero_eval_zero (leafIdx : ℕ) (env : Env F)
    (h : env.trace leafIdx = 0) :
    (leaf1Zero (F := F) leafIdx).eval env = 0 := by
  simp [leaf1Zero, CoeffExpr.eval, h]

/-! ## C1 / C2 rejected once the leaf is pre-seed `𝔽` -/

/-- Forged formula with a *fixed* (pre-seed) leaf `L`. -/
noncomputable def fixedLeafFormula (z L : K) : FP K :=
  pair z (aFP z 3) (pair z (aFP z 1) (pair z (aFP z 1) (aFP z L)))

/-- Fixing the forged leaf *before* `z` turns the adaptive identity into a
    degree-2 equation `(L − x) z² = 2`. -/
theorem fixed_leaf_collision_equation (z x L : K) (hz : z ≠ 0)
    (heq : fixedLeafFormula z L = publicFormula z x) :
    (L - x) * z ^ 2 = 2 := by
  have h := congrArg FP.leaf heq
  simp [fixedLeafFormula, publicFormula, pair, aFP, FP.cons, FP.atomFP] at h
  rcases h with h | h
  · linear_combination h
  · exact (hz h).elim

theorem fixed_leaf_collisions_card_le_two
    [Fintype K] [DecidableEq K] (x L : K) (h2 : (2 : K) ≠ 0) :
    (Finset.univ.filter fun z : K =>
      z ≠ 0 ∧ fixedLeafFormula z L = publicFormula z x).card ≤ 2 := by
  classical
  by_cases hL : L = x
  · have hempty :
        (Finset.univ.filter fun z : K =>
          z ≠ 0 ∧ fixedLeafFormula z L = publicFormula z x) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hz, heq⟩
        have he := fixed_leaf_collision_equation z x L hz heq
        rw [hL, sub_self, zero_mul] at he
        exact (h2 he.symm).elim
      · intro hz
        simp at hz
    rw [hempty]
    simp
  · have hsub :
        (Finset.univ.filter fun z : K =>
          z ≠ 0 ∧ fixedLeafFormula z L = publicFormula z x) ⊆
          (Polynomial.nthRoots 2 (2 / (L - x))).toFinset := by
      intro z hz
      obtain ⟨hz0, heq⟩ := (Finset.mem_filter.mp hz).2
      have he := fixed_leaf_collision_equation z x L hz0 heq
      have hne : L - x ≠ 0 := sub_ne_zero.mpr hL
      have hpow : z ^ 2 = 2 / (L - x) := (eq_div_iff hne).mpr (by
        rw [mul_comm]
        exact he)
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide)).mpr hpow)
    exact (Finset.card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 (2 / (L - x))))

/-- A payload committed before the seed (constant in `z`) has at most two
    colliding seeds. -/
theorem preseed_leaf_collisions_card_le_two
    [Fintype K] [DecidableEq K]
    (x : K) (payload : K → K)
    (hfixed : ∀ z z', payload z = payload z') (h2 : (2 : K) ≠ 0) :
    (Finset.univ.filter fun z : K =>
      z ≠ 0 ∧ fixedLeafFormula z (payload z) = publicFormula z x).card ≤ 2 := by
  have heq :
      (Finset.univ.filter fun z : K =>
        z ≠ 0 ∧ fixedLeafFormula z (payload z) = publicFormula z x) =
        Finset.univ.filter (fun z : K =>
          z ≠ 0 ∧ fixedLeafFormula z (payload 0) = publicFormula z x) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfixed z 0]
  rw [heq]
  exact fixed_leaf_collisions_card_le_two x (payload 0) h2

/-! ## Soundness event: pre-seed census, `deg / |𝕂|` -/

/-- Collision event of a *fixed* (pre-seed) noun set.  Degree bound is the paper's
    `2(2Λ − 1)`, tightened in-tree to
    `2Λ − 1` (`NPR.collision_card_le_tight`). -/
theorem preseed_pair_card_le
    [Fintype K] [DecidableEq K] {Λ : ℕ}
    (n₁ n₂ : Noun) (hΛ₁ : n₁.leaves ≤ Λ) (hΛ₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁) ≠
      (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter fun z : K => NPR.fn n₁ z = NPR.fn n₂ z).card ≤ 2 * Λ - 1 :=
  NPR.collision_card_le_tight (K := K) Λ n₁ n₂ hΛ₁ hΛ₂ hne

/-- Live consumed census majorant `(3 + 19 · rows)(2Λ − 1)` vs a pre-seed pair
    bound `2Λ − 1`.  The pre-seed event is a *pair* bound; the consumed figure
    unions every comparison the skeleton lists. -/
theorem preseed_vs_consumed_majorant (rows Λ : ℕ) (_hΛ : 1 ≤ Λ) :
    2 * Λ - 1 ≤ (3 + 19 * rows) * (2 * Λ - 1) := by
  have : 1 ≤ 3 + 19 * rows := by omega
  exact Nat.le_mul_of_pos_left _ this

/-! ## Break attempts -/

/-- Distinct shapes have distinct Dyck words. -/
theorem distinct_shapes_distinct_dyck {n₁ n₂ : Noun} (h : n₁.shape ≠ n₂.shape) :
    n₁.dyckWord ≠ n₂.dyckWord := by
  intro hd
  exact h (BTree.encode_injective (by simpa [Noun.dyckWord] using hd))

/-- OP1 selector is base column 1 — round 0 of `nockChronology` (`ComputeStagedTable`). -/
theorem op1_selector_is_round_zero : (stateIndex .s1 : ℕ) = 1 := rfl

theorem op1_selector_lt_base : (stateIndex .s1 : ℕ) < 13 := by decide

/-- Seed coins `z, a, b, c` are sampled *after* the selector block. -/
theorem seed_after_selectors :
    nockSampledAfter zSlot = 0 := rfl

/-- Memory `halt` is an atom row: `size = z`, `dyck = 0`, leaf free until C3.
    the paper (body: "the parent is an atom"), `:2062-2064` (appendix `halt` block). -/
theorem halt_is_atom_shape (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (h : p.st = .halt) (heq : MemoryTable.eqBlk inp p) :
    p.pt.noun.size = inp.z ∧ p.pt.noun.dyck = 0 := by
  revert heq
  unfold MemoryTable.eqBlk
  rw [h]
  intro heq
  exact ⟨heq.1, heq.2.1⟩

/-- OP4 result is determined: `e = inc z sf1_e` (`evalV` `.s4`).  Not a free atom. -/
theorem op4_result_determined (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hst : pub.state = .s4) (h : evalV inp pub dec) :
    pub.e = FP.inc inp.z pub.sf1_e := by
  simp [evalV, hst] at h
  exact h.2.2.2.2.2.2

/-- OP3 result leaf is `{0,1}` (`qm`).  Not a free atom. -/
theorem op3_result_boolean (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hst : pub.state = .s3) (h : evalV inp pub dec) :
    pub.e.leaf = 0 ∨ pub.e.leaf = 1 := by
  simp [evalV, hst] at h
  have hqm : pub.e.leaf = FP.qm inp.z pub.sf1_e := h.2.2.2.2.2.2
  rw [hqm]
  simp [FP.qm]
  exact Or.comm.mp (em _)

/-- `atom ∈ 𝔽` as a *column type* does not force `leaf₁ = leaf₂ = 0`.
    The K-equation `leaf = algebraMap atom` is three `𝔽`-equations; the two
    zero gates are the power-basis specialisation `coord 1 = (1,0,0)`. -/
theorem algebraMap_is_smul_one (atom : F) [Algebra F K] :
    algebraMap F K atom = atom • (1 : K) :=
  Algebra.algebraMap_eq_smul_one atom

end Nock.RedTeam.Batch579

#print axioms Nock.RedTeam.Batch579.honest_atom_fill
#print axioms Nock.RedTeam.Batch579.fixed_leaf_collisions_card_le_two
#print axioms Nock.RedTeam.Batch579.preseed_leaf_collisions_card_le_two
#print axioms Nock.RedTeam.Batch579.preseed_pair_card_le
#print axioms Nock.RedTeam.Batch579.distinct_shapes_distinct_dyck
#print axioms Nock.RedTeam.Batch579.op4_result_determined
