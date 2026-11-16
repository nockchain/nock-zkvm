/-
  Nock/TableWFBounds.lean

  Completeness-layer corollary for the compute/memory table `WF` hypotheses
  (`ComputeTable.WF`, `MemoryTable.WF`) that the exact appendix `↔` lemmas
  `Lem:equiv_compute` and `Lem:equiv_mem`
  carry.

  Split of the three compute `WF` fields and the memory pole:

  * `size8` / `size11` are encoding: NPR sizes are `z`-powers and `z ≠ 0` (`not_accepts_zero`).  Deterministic; not
    Schwartz–Zippel.
  * `rlc5` and memory `pole_ne` are random-challenge events.  Counting measure
    over coins `(a,b,c)` and `(β,γ)` as in `Nock/NPR.lean`.

  Bound: over those coins,
    `Pr[all compute rows satisfy rlc5 ∧ all memory rows satisfy pole_ne]
       ≥ 1 − (N+L)/|K|`.
  On that event, honest NPR sizes assemble `WF`, and the existing exact `↔`
  inhabits the RAP.  Completeness exceptions of this shape already live as a
  *different layer* from algebraic `Language` membership
  (`DistinctCensusCompletenessLayers.lean`).
-/
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.NPR
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

open Classical

namespace Nock
namespace TableWFBounds

open ComputeTable (FP MemRec)
open MemoryTable (MState Cell)

variable {K : Type*} [Field K]

/-! ## Encoding sizes (`size8` / `size11`) — the paper

    Not a coin event.  Honest NPR `fn n z = (z^λ, …)` with `z ≠ 0` forces the
    size coordinates used by OP_8 / cons inverse gates. -/

/-- NPR size coordinate is a positive power of `z`. -/
theorem fn_size_ne_zero (n : Noun) (z : K) (hz : z ≠ 0) :
    (NPR.fn n z).1 ≠ 0 := by
  simpa [NPR.fn] using pow_ne_zero n.leaves hz

/-- Encoding hypothesis: a fingerprint's `size` is some `z`-power.  Honest NPR
    rows inhabit this via `fn_size_ne_zero` (`size = z^λ`). -/
def HonestSize (z : K) (fp : FP K) : Prop :=
  ∃ n : ℕ, fp.size = z ^ n

theorem honestSize_of_fn (n : Noun) (z : K) :
    HonestSize z ⟨(NPR.fn n z).1, (NPR.fn n z).2.1, (NPR.fn n z).2.2⟩ :=
  ⟨n.leaves, by simp [NPR.fn]⟩

theorem honestSize_ne_zero {z : K} {fp : FP K} (hz : z ≠ 0)
    (h : HonestSize z fp) : fp.size ≠ 0 := by
  obtain ⟨n, hn⟩ := h
  rw [hn]
  exact pow_ne_zero n hz

/-- OP_8 size non-vanishing from encoding.  Vacuous off `s8`. -/
theorem wf_size8_of_z_pows (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (hz : inp.z ≠ 0)
    (hs : HonestSize inp.z pub.s)
    (h2 : HonestSize inp.z pub.sf2_e) :
    pub.state = ComputeTable.State.s8 → pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0 :=
  fun _ => ⟨honestSize_ne_zero hz h2, honestSize_ne_zero hz hs⟩

/-- Cons size non-vanishing from encoding.  Vacuous off `cons`. -/
theorem wf_size11_of_z_pows (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (hz : inp.z ≠ 0)
    (h1 : HonestSize inp.z pub.sf1_e)
    (h2 : HonestSize inp.z pub.sf2_e) :
    pub.state = ComputeTable.State.cons →
      pub.sf1_e.size ≠ 0 ∧ pub.sf2_e.size ≠ 0 :=
  fun _ => ⟨honestSize_ne_zero hz h1, honestSize_ne_zero hz h2⟩

/-! ## OP_5 RLC coins `(a,b,c)` — the paper -/

/-- Compute-table equality-RLC coins.  Packed as `K × (K × K)` so `.1 = a`,
    `.2.1 = b`, `.2.2 = c`. -/
abbrev ComputeCoins (K : Type*) := K × K × K

def deltaSize (pub : ComputeTable.Pub K) : K := pub.sf1_e.size - pub.sf2_e.size
def deltaDyck (pub : ComputeTable.Pub K) : K := pub.sf1_e.dyck - pub.sf2_e.dyck
def deltaLeaf (pub : ComputeTable.Pub K) : K := pub.sf1_e.leaf - pub.sf2_e.leaf

/-- Live OP_5 row with unequal evaluation fingerprints (the only locus `rlc5` constrains). -/
def needsRlc5 (pub : ComputeTable.Pub K) : Prop :=
  pub.state = ComputeTable.State.s5 ∧ pub.sf1_e ≠ pub.sf2_e

def rlc5Form (a b c : K) (pub : ComputeTable.Pub K) : K :=
  a * deltaSize pub + b * deltaDyck pub + c * deltaLeaf pub

/-- The `WF.rlc5` field, uncurried. -/
def rlc5Holds (a b c : K) (pub : ComputeTable.Pub K) : Prop :=
  needsRlc5 pub → rlc5Form a b c pub ≠ 0

theorem rlc5Holds_iff_wf (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) :
    rlc5Holds inp.a inp.b inp.c pub ↔
      (pub.state = ComputeTable.State.s5 → pub.sf1_e ≠ pub.sf2_e →
        inp.a * (pub.sf1_e.size - pub.sf2_e.size)
          + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) ≠ 0) := by
  constructor
  · intro h hst hne; exact h ⟨hst, hne⟩
  · intro h ⟨hst, hne⟩; exact h hst hne

theorem fp_ne_of_some_delta {x y : FP K}
    (h : x.size - y.size ≠ 0 ∨ x.dyck - y.dyck ≠ 0 ∨ x.leaf - y.leaf ≠ 0) :
    x ≠ y := by
  rintro rfl
  simp at h

theorem some_delta_of_fp_ne {x y : FP K} (h : x ≠ y) :
    x.size - y.size ≠ 0 ∨ x.dyck - y.dyck ≠ 0 ∨ x.leaf - y.leaf ≠ 0 := by
  by_contra h0
  push Not at h0
  exact h (FP.ext (sub_eq_zero.mp h0.1) (sub_eq_zero.mp h0.2.1)
    (sub_eq_zero.mp h0.2.2))

def linearFormCoins (d1 d2 d3 : K) (p : ComputeCoins K) : K :=
  p.1 * d1 + p.2.1 * d2 + p.2.2 * d3

/-- Kernel chart when the size-delta is invertible.  The inverse is only
    consumed under `dᵢ ≠ 0`. -/
def embed1 (d1 d2 d3 : K) (bc : K × K) : ComputeCoins K :=
  (-d1⁻¹ * (bc.1 * d2 + bc.2 * d3), bc)

def embed2 (d1 d2 d3 : K) (ac : K × K) : ComputeCoins K :=
  (ac.1, (-d2⁻¹ * (ac.1 * d1 + ac.2 * d3), ac.2))

def embed3 (d1 d2 d3 : K) (ab : K × K) : ComputeCoins K :=
  (ab.1, (ab.2, -d3⁻¹ * (ab.1 * d1 + ab.2 * d2)))

theorem embed1_injective (d1 d2 d3 : K) :
    Function.Injective (embed1 d1 d2 d3) :=
  fun _ _ h => congrArg Prod.snd h

theorem embed2_injective (d1 d2 d3 : K) :
    Function.Injective (embed2 d1 d2 d3) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h3 := congrArg (fun p : ComputeCoins K => p.2.2) h
  exact Prod.ext h1 h3

theorem embed3_injective (d1 d2 d3 : K) :
    Function.Injective (embed3 d1 d2 d3) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun p : ComputeCoins K => p.2.1) h
  exact Prod.ext h1 h2

noncomputable section Count
variable [Fintype K] [DecidableEq K]

def kernel (d1 d2 d3 : K) : Finset (ComputeCoins K) :=
  Finset.univ.filter (fun p => linearFormCoins d1 d2 d3 p = 0)

theorem embed1_mem_kernel (d1 d2 d3 : K) (hd1 : d1 ≠ 0) (bc : K × K) :
    embed1 d1 d2 d3 bc ∈ kernel d1 d2 d3 := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [linearFormCoins, embed1]
  field_simp [hd1]
  ring

theorem embed2_mem_kernel (d1 d2 d3 : K) (hd2 : d2 ≠ 0) (ac : K × K) :
    embed2 d1 d2 d3 ac ∈ kernel d1 d2 d3 := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [linearFormCoins, embed2]
  field_simp [hd2]
  ring

theorem embed3_mem_kernel (d1 d2 d3 : K) (hd3 : d3 ≠ 0) (ab : K × K) :
    embed3 d1 d2 d3 ab ∈ kernel d1 d2 d3 := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [linearFormCoins, embed3]
  field_simp [hd3]
  ring

omit [Fintype K] [DecidableEq K] in
theorem eq_embed1_of_mem_kernel (d1 d2 d3 : K) (hd1 : d1 ≠ 0) {p : ComputeCoins K}
    (hp : linearFormCoins d1 d2 d3 p = 0) :
    p = embed1 d1 d2 d3 p.2 := by
  apply Prod.ext
  · have hsum : p.1 * d1 + (p.2.1 * d2 + p.2.2 * d3) = 0 := by
      simpa [linearFormCoins, add_assoc] using hp
    have hmul : p.1 * d1 = -(p.2.1 * d2 + p.2.2 * d3) :=
      add_eq_zero_iff_eq_neg.mp hsum
    calc
      p.1 = p.1 * d1 * d1⁻¹ := (mul_inv_cancel_right₀ hd1 p.1).symm
      _ = (-(p.2.1 * d2 + p.2.2 * d3)) * d1⁻¹ := by rw [hmul]
      _ = -d1⁻¹ * (p.2.1 * d2 + p.2.2 * d3) := by ring
  · rfl

omit [Fintype K] [DecidableEq K] in
theorem eq_embed2_of_mem_kernel (d1 d2 d3 : K) (hd2 : d2 ≠ 0) {p : ComputeCoins K}
    (hp : linearFormCoins d1 d2 d3 p = 0) :
    p = embed2 d1 d2 d3 (p.1, p.2.2) := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  have hsum : p.2.1 * d2 + (p.1 * d1 + p.2.2 * d3) = 0 := by
    refine Eq.trans ?_ hp
    simp only [linearFormCoins]
    ac_rfl
  have hmul : p.2.1 * d2 = -(p.1 * d1 + p.2.2 * d3) :=
    add_eq_zero_iff_eq_neg.mp hsum
  calc
    p.2.1 = p.2.1 * d2 * d2⁻¹ := (mul_inv_cancel_right₀ hd2 p.2.1).symm
    _ = (-(p.1 * d1 + p.2.2 * d3)) * d2⁻¹ := by rw [hmul]
    _ = -d2⁻¹ * (p.1 * d1 + p.2.2 * d3) := by ring

omit [Fintype K] [DecidableEq K] in
theorem eq_embed3_of_mem_kernel (d1 d2 d3 : K) (hd3 : d3 ≠ 0) {p : ComputeCoins K}
    (hp : linearFormCoins d1 d2 d3 p = 0) :
    p = embed3 d1 d2 d3 (p.1, p.2.1) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  have hsum : p.2.2 * d3 + (p.1 * d1 + p.2.1 * d2) = 0 := by
    refine Eq.trans ?_ hp
    simp only [linearFormCoins]
    ac_rfl
  have hmul : p.2.2 * d3 = -(p.1 * d1 + p.2.1 * d2) :=
    add_eq_zero_iff_eq_neg.mp hsum
  calc
    p.2.2 = p.2.2 * d3 * d3⁻¹ := (mul_inv_cancel_right₀ hd3 p.2.2).symm
    _ = (-(p.1 * d1 + p.2.1 * d2)) * d3⁻¹ := by rw [hmul]
    _ = -d3⁻¹ * (p.1 * d1 + p.2.1 * d2) := by ring

theorem kernel_eq_image_embed1 (d1 d2 d3 : K) (hd1 : d1 ≠ 0) :
    kernel d1 d2 d3 = Finset.univ.image (embed1 d1 d2 d3) := by
  ext p
  constructor
  · intro hp
    have hp' : linearFormCoins d1 d2 d3 p = 0 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _,
      (eq_embed1_of_mem_kernel d1 d2 d3 hd1 hp').symm⟩
  · intro hp
    obtain ⟨bc, _, rfl⟩ := Finset.mem_image.mp hp
    exact embed1_mem_kernel d1 d2 d3 hd1 bc

theorem kernel_eq_image_embed2 (d1 d2 d3 : K) (hd2 : d2 ≠ 0) :
    kernel d1 d2 d3 = Finset.univ.image (embed2 d1 d2 d3) := by
  ext p
  constructor
  · intro hp
    have hp' : linearFormCoins d1 d2 d3 p = 0 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨(p.1, p.2.2), Finset.mem_univ _,
      (eq_embed2_of_mem_kernel d1 d2 d3 hd2 hp').symm⟩
  · intro hp
    obtain ⟨ac, _, rfl⟩ := Finset.mem_image.mp hp
    exact embed2_mem_kernel d1 d2 d3 hd2 ac

theorem kernel_eq_image_embed3 (d1 d2 d3 : K) (hd3 : d3 ≠ 0) :
    kernel d1 d2 d3 = Finset.univ.image (embed3 d1 d2 d3) := by
  ext p
  constructor
  · intro hp
    have hp' : linearFormCoins d1 d2 d3 p = 0 :=
      (Finset.mem_filter.mp hp).2
    exact Finset.mem_image.mpr ⟨(p.1, p.2.1), Finset.mem_univ _,
      (eq_embed3_of_mem_kernel d1 d2 d3 hd3 hp').symm⟩
  · intro hp
    obtain ⟨ab, _, rfl⟩ := Finset.mem_image.mp hp
    exact embed3_mem_kernel d1 d2 d3 hd3 ab

theorem kernel_card (d1 d2 d3 : K) (hne : d1 ≠ 0 ∨ d2 ≠ 0 ∨ d3 ≠ 0) :
    (kernel d1 d2 d3).card = Fintype.card K * Fintype.card K := by
  rcases hne with h | h | h
  · rw [kernel_eq_image_embed1 d1 d2 d3 h,
      Finset.card_image_of_injective _ (embed1_injective d1 d2 d3),
      Finset.card_univ, Fintype.card_prod]
  · rw [kernel_eq_image_embed2 d1 d2 d3 h,
      Finset.card_image_of_injective _ (embed2_injective d1 d2 d3),
      Finset.card_univ, Fintype.card_prod]
  · rw [kernel_eq_image_embed3 d1 d2 d3 h,
      Finset.card_image_of_injective _ (embed3_injective d1 d2 d3),
      Finset.card_univ, Fintype.card_prod]

/-- Bad compute coins at one row: empty unless the row is live OP_5-unequal. -/
def badComputeAt (pub : ComputeTable.Pub K) : Finset (ComputeCoins K) :=
  Finset.univ.filter (fun p => needsRlc5 pub ∧ linearFormCoins (deltaSize pub)
    (deltaDyck pub) (deltaLeaf pub) p = 0)

theorem badComputeAt_eq_kernel (pub : ComputeTable.Pub K) (h : needsRlc5 pub) :
    badComputeAt pub = kernel (deltaSize pub) (deltaDyck pub) (deltaLeaf pub) := by
  ext p
  simp [badComputeAt, kernel, h]

theorem badComputeAt_empty (pub : ComputeTable.Pub K) (h : ¬ needsRlc5 pub) :
    badComputeAt pub = ∅ := by
  ext p
  simp [badComputeAt, h]

theorem rlc5Holds_iff_not_mem_bad (a b c : K) (pub : ComputeTable.Pub K) :
    rlc5Holds a b c pub ↔ (a, b, c) ∉ badComputeAt pub := by
  constructor
  · intro h hmem
    simp only [badComputeAt, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact h hmem.1 (by simpa [rlc5Form, linearFormCoins] using hmem.2)
  · intro h hn hf
    refine h ?_
    simp only [badComputeAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hn, by simpa [rlc5Form, linearFormCoins] using hf⟩

theorem badComputeAt_card_le (pub : ComputeTable.Pub K) :
    (badComputeAt pub).card ≤ Fintype.card K * Fintype.card K := by
  by_cases h : needsRlc5 pub
  · have hδ : deltaSize pub ≠ 0 ∨ deltaDyck pub ≠ 0 ∨ deltaLeaf pub ≠ 0 := by
      simpa [deltaSize, deltaDyck, deltaLeaf] using some_delta_of_fp_ne h.2
    rw [badComputeAt_eq_kernel pub h]
    exact (kernel_card (deltaSize pub) (deltaDyck pub) (deltaLeaf pub) hδ).le
  · rw [badComputeAt_empty pub h]
    exact Nat.zero_le _

def badComputeAny {n : ℕ} (rows : Fin n → ComputeTable.Pub K) :
    Finset (ComputeCoins K) :=
  Finset.univ.biUnion fun i : Fin n => badComputeAt (rows i)

theorem rlc5All_iff_not_mem_badAny {n : ℕ}
    (coins : ComputeCoins K) (rows : Fin n → ComputeTable.Pub K) :
    (∀ i, rlc5Holds coins.1 coins.2.1 coins.2.2 (rows i)) ↔
      coins ∉ badComputeAny rows := by
  simp [badComputeAny, Finset.mem_biUnion, rlc5Holds_iff_not_mem_bad]

theorem badComputeAny_card_le {n : ℕ} (rows : Fin n → ComputeTable.Pub K) :
    (badComputeAny rows).card ≤ n * (Fintype.card K * Fintype.card K) := by
  refine (Finset.card_biUnion_le).trans ?_
  have hsum :
      ∑ i : Fin n, (badComputeAt (rows i)).card ≤
        ∑ _i : Fin n, Fintype.card K * Fintype.card K :=
    Finset.sum_le_sum fun i _ => badComputeAt_card_le (rows i)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

omit [Field K] [DecidableEq K] in
theorem card_computeCoins :
    Fintype.card (ComputeCoins K) = Fintype.card K ^ 3 := by
  simp [ComputeCoins, Fintype.card_prod, pow_succ, pow_zero, mul_assoc]

/-- `Pr_{(a,b,c)}[∃ live OP_5 row with rlc5 failure] ≤ N/|K|`. -/
theorem badComputeAny_prob_le {n : ℕ} (rows : Fin n → ComputeTable.Pub K) :
    ((badComputeAny rows).card : ℚ) / (Fintype.card (ComputeCoins K) : ℚ)
      ≤ (n : ℚ) / (Fintype.card K : ℚ) := by
  haveI : Nonempty K := ⟨0⟩
  have hk : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card (ComputeCoins K) : ℚ) := by
    rw [card_computeCoins]; exact pow_pos hk 3
  have hnat :
      (badComputeAny rows).card * Fintype.card K ≤
        n * Fintype.card (ComputeCoins K) := by
    have hcard := badComputeAny_card_le rows
    have hmul := Nat.mul_le_mul_right (Fintype.card K) hcard
    rw [card_computeCoins]
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  rw [div_le_div_iff₀ hden hk]
  exact_mod_cast hnat

/-! ## Memory LogUp coins `(β, γ)` — the paper -/

/-- Memory-table LogUp coins `(β, γ)`.  Encoding seed `z` is not a coin here. -/
abbrev MemoryCoins (K : Type*) := K × K

def needsPole (p : MemoryTable.Pub K) : Prop :=
  p.st = MState.read_root ∨ p.st = MState.verify_child

def poleHolds (β γ : K) (p : MemoryTable.Pub K) : Prop :=
  needsPole p → MemoryTable.recRLC γ p.mem p.cprime - β ≠ 0

omit [Fintype K] [DecidableEq K] in
theorem poleHolds_iff_wf (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    poleHolds inp.β inp.γ p ↔
      ((p.st = MState.read_root ∨ p.st = MState.verify_child) →
        MemoryTable.pole inp p.mem p.cprime ≠ 0) := by
  simp [poleHolds, needsPole, MemoryTable.pole]

def embedPole (p : MemoryTable.Pub K) (γ : K) : MemoryCoins K :=
  (MemoryTable.recRLC γ p.mem p.cprime, γ)

omit [Fintype K] [DecidableEq K] in
theorem embedPole_injective (p : MemoryTable.Pub K) :
    Function.Injective (embedPole p) :=
  fun _ _ h => congrArg Prod.snd h

def badMemoryAt (p : MemoryTable.Pub K) : Finset (MemoryCoins K) :=
  Finset.univ.filter (fun q => needsPole p ∧ q.1 = MemoryTable.recRLC q.2 p.mem p.cprime)

theorem badMemoryAt_eq_image (p : MemoryTable.Pub K) (h : needsPole p) :
    badMemoryAt p = Finset.univ.image (embedPole p) := by
  ext q
  constructor
  · intro hq
    simp only [badMemoryAt, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine Finset.mem_image.mpr ⟨q.2, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact hq.2.symm
    · rfl
  · intro hq
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hq
    simp [badMemoryAt, embedPole, h]

theorem badMemoryAt_empty (p : MemoryTable.Pub K) (h : ¬ needsPole p) :
    badMemoryAt p = ∅ := by
  ext q
  simp [badMemoryAt, h]

theorem poleHolds_iff_not_mem_bad (β γ : K) (p : MemoryTable.Pub K) :
    poleHolds β γ p ↔ (β, γ) ∉ badMemoryAt p := by
  constructor
  · intro h hmem
    simp only [badMemoryAt, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hne : MemoryTable.recRLC γ p.mem p.cprime - β ≠ 0 := h hmem.1
    exact hne (sub_eq_zero.mpr (Eq.symm hmem.2))
  · intro h hn hf
    refine h ?_
    simp only [badMemoryAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hn, Eq.symm (sub_eq_zero.mp hf)⟩

theorem badMemoryAt_card_le (p : MemoryTable.Pub K) :
    (badMemoryAt p).card ≤ Fintype.card K := by
  by_cases h : needsPole p
  · rw [badMemoryAt_eq_image p h,
      Finset.card_image_of_injective _ (embedPole_injective p),
      Finset.card_univ]
  · rw [badMemoryAt_empty p h]
    exact Nat.zero_le _

def badMemoryAny {l : ℕ} (rows : Fin l → MemoryTable.Pub K) :
    Finset (MemoryCoins K) :=
  Finset.univ.biUnion fun i : Fin l => badMemoryAt (rows i)

theorem poleAll_iff_not_mem_badAny {l : ℕ}
    (coins : MemoryCoins K) (rows : Fin l → MemoryTable.Pub K) :
    (∀ i, poleHolds coins.1 coins.2 (rows i)) ↔ coins ∉ badMemoryAny rows := by
  simp [badMemoryAny, Finset.mem_biUnion, poleHolds_iff_not_mem_bad]

theorem badMemoryAny_card_le {l : ℕ} (rows : Fin l → MemoryTable.Pub K) :
    (badMemoryAny rows).card ≤ l * Fintype.card K := by
  refine (Finset.card_biUnion_le).trans ?_
  have hsum :
      ∑ i : Fin l, (badMemoryAt (rows i)).card ≤ ∑ _i : Fin l, Fintype.card K :=
    Finset.sum_le_sum fun i _ => badMemoryAt_card_le (rows i)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

omit [Field K] [DecidableEq K] in
theorem card_memoryCoins :
    Fintype.card (MemoryCoins K) = Fintype.card K ^ 2 := by
  simp [MemoryCoins, Fintype.card_prod, pow_two]

/-- `Pr_{(β,γ)}[∃ live LogUp row with pole = 0] ≤ L/|K|`. -/
theorem badMemoryAny_prob_le {l : ℕ} (rows : Fin l → MemoryTable.Pub K) :
    ((badMemoryAny rows).card : ℚ) / (Fintype.card (MemoryCoins K) : ℚ)
      ≤ (l : ℚ) / (Fintype.card K : ℚ) := by
  haveI : Nonempty K := ⟨0⟩
  have hk : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card (MemoryCoins K) : ℚ) := by
    rw [card_memoryCoins]; exact pow_pos hk 2
  have hnat :
      (badMemoryAny rows).card * Fintype.card K ≤
        l * Fintype.card (MemoryCoins K) := by
    have hcard := badMemoryAny_card_le rows
    have hmul := Nat.mul_le_mul_right (Fintype.card K) hcard
    rw [card_memoryCoins, pow_two]
    simpa [mul_assoc] using hmul
  rw [div_le_div_iff₀ hden hk]
  exact_mod_cast hnat

/-! ## Combined honest-row bound

    Coins `(a,b,c,β,γ)`. -/

abbrev WFJointCoins (K : Type*) := ComputeCoins K × MemoryCoins K

def badJoint {n l : ℕ}
    (crows : Fin n → ComputeTable.Pub K)
    (mrows : Fin l → MemoryTable.Pub K) : Finset (WFJointCoins K) :=
  (badComputeAny crows ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ badMemoryAny mrows)

omit [Field K] [DecidableEq K] in
theorem card_wfJointCoins :
    Fintype.card (WFJointCoins K) = Fintype.card K ^ 5 := by
  simp [WFJointCoins, ComputeCoins, MemoryCoins, Fintype.card_prod, pow_succ, pow_zero]
  ring

theorem badJoint_card_le {n l : ℕ}
    (crows : Fin n → ComputeTable.Pub K)
    (mrows : Fin l → MemoryTable.Pub K) :
    (badJoint crows mrows).card ≤ (n + l) * Fintype.card K ^ 4 := by
  refine (Finset.card_union_le _ _).trans ?_
  have hC := badComputeAny_card_le crows
  have hM := badMemoryAny_card_le mrows
  have hleft :
      (badComputeAny crows ×ˢ (Finset.univ : Finset (MemoryCoins K))).card ≤
        n * Fintype.card K ^ 4 := by
    calc
      (badComputeAny crows ×ˢ (Finset.univ : Finset (MemoryCoins K))).card
          = (badComputeAny crows).card * Fintype.card (MemoryCoins K) := by
            rw [Finset.card_product, Finset.card_univ]
      _ ≤ (n * (Fintype.card K * Fintype.card K)) * Fintype.card (MemoryCoins K) :=
            Nat.mul_le_mul_right _ hC
      _ = n * Fintype.card K ^ 4 := by
            rw [card_memoryCoins]; ring
  have hright :
      ((Finset.univ : Finset (ComputeCoins K)) ×ˢ badMemoryAny mrows).card ≤
        l * Fintype.card K ^ 4 := by
    calc
      ((Finset.univ : Finset (ComputeCoins K)) ×ˢ badMemoryAny mrows).card
          = Fintype.card (ComputeCoins K) * (badMemoryAny mrows).card := by
            rw [Finset.card_product, Finset.card_univ]
      _ ≤ Fintype.card (ComputeCoins K) * (l * Fintype.card K) :=
            Nat.mul_le_mul_left _ hM
      _ = l * Fintype.card K ^ 4 := by
            rw [card_computeCoins]; ring
  calc
    _ ≤ n * Fintype.card K ^ 4 + l * Fintype.card K ^ 4 := Nat.add_le_add hleft hright
    _ = (n + l) * Fintype.card K ^ 4 := by ring

/-- Honest-row bound: `Pr[∀ compute rlc5 ∧ ∀ memory pole_ne] ≥ 1 − (N+L)/|K|`
    over coins `(a,b,c,β,γ)`.  the paper. -/
theorem honest_row_prob_ge {n l : ℕ}
    (crows : Fin n → ComputeTable.Pub K)
    (mrows : Fin l → MemoryTable.Pub K) :
    (1 : ℚ) - ((badJoint crows mrows).card : ℚ) / (Fintype.card (WFJointCoins K) : ℚ)
      ≥ 1 - ((n + l : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  haveI : Nonempty K := ⟨0⟩
  have hk : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card (WFJointCoins K) : ℚ) := by
    rw [card_wfJointCoins]; exact pow_pos hk 5
  have hineq :
      ((badJoint crows mrows).card : ℚ) / (Fintype.card (WFJointCoins K) : ℚ)
        ≤ ((n + l : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
    have hnat :
        (badJoint crows mrows).card * Fintype.card K ≤
          (n + l) * Fintype.card (WFJointCoins K) := by
      have hcard := badJoint_card_le crows mrows
      have hmul := Nat.mul_le_mul_right (Fintype.card K) hcard
      rw [card_wfJointCoins]
      simpa [pow_succ, mul_assoc] using hmul
    rw [div_le_div_iff₀ hden hk]
    exact_mod_cast hnat
  exact sub_le_sub_left hineq 1

end Count

/-! ## Assemble `WF` on the honest-row event, then inhabit the RAP

    These wrap the existing exact `iff`s.  They do **not** replace them. -/

theorem computeWF_of_honest_sizes_and_rlc5
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (hz : inp.z ≠ 0)
    (hs : HonestSize inp.z pub.s)
    (h1 : HonestSize inp.z pub.sf1_e)
    (h2 : HonestSize inp.z pub.sf2_e)
    (h5 : rlc5Holds inp.a inp.b inp.c pub) :
    ComputeTable.WF inp pub where
  rlc5 := (rlc5Holds_iff_wf inp pub).mp h5
  size8 := wf_size8_of_z_pows inp pub hz hs h2
  size11 := wf_size11_of_z_pows inp pub hz h1 h2

theorem memoryWF_of_pole_ne
    (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (h : poleHolds inp.β inp.γ p) :
    MemoryTable.WF inp p where
  pole_ne := (poleHolds_iff_wf inp p).mp h

/-- Honest `V_comp` plus assembled `WF` inhabits `RAP_comp` by `equiv_compute`. -/
theorem honest_compute_inhabits_RAP
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K) (wf : ComputeTable.WF inp pub)
    (hv : ComputeTable.Vcomp inp pub dec) :
    ∃ ex, ComputeTable.RAPcomp inp pub dec ex :=
  (ComputeTable.equiv_compute inp pub dec wf).mpr hv

/-- Honest `V_mem` plus assembled `WF` inhabits `RAP_mem` by `equiv_mem`. -/
theorem honest_memory_inhabits_RAP
    (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (wf : MemoryTable.WF inp p) (hv : MemoryTable.Vmem inp p) :
    ∃ g, MemoryTable.RAPmem inp p g :=
  (MemoryTable.equiv_mem inp p wf).mpr hv


noncomputable def dummyCompute (st : ComputeTable.State) (s sf1e sf2e : FP K) :
    ComputeTable.Pub K :=
  { state := st, s := s, f := 0, e := 0
    sf1_s := 0, sf1_f := 0, sf1_e := sf1e
    sf2_s := 0, sf2_f := 0, sf2_e := sf2e
    sf3_s := 0, sf3_f := 0, sf3_e := 0
    ln_prev := 0, ln := 0
    mr1 := MemRec.zero, mr2 := MemRec.zero, mr3 := MemRec.zero }

def dummyMemory (st : MState) (mem : MemRec K) : MemoryTable.Pub K :=
  { st := st
    pt := Cell.zero, lc := Cell.zero, rc := Cell.zero
    lcSt := st, rcSt := st
    mem := mem, ipre := 0, icur := 0 }

@[simp] theorem recRLC_zero (γ : K) : MemoryTable.recRLC γ (MemRec.zero : MemRec K) = 0 := by
  simp [MemoryTable.recRLC, MemRec.zero]

/-! ## Non-vacuity over `ZMod 97` -/

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

abbrev F97 : Type := ZMod 97

namespace F97Witness

theorem op5_unequal_fps :
    FP.atomFP (1 : F97) 0 ≠ FP.atomFP 1 1 := by
  intro h
  have := congrArg FP.leaf h
  simp at this

theorem op5_needs :
    needsRlc5 (dummyCompute (K := F97) .s5 (FP.atomFP 1 0)
      (FP.atomFP 1 0) (FP.atomFP 1 1)) :=
  ⟨rfl, op5_unequal_fps⟩

/-- Live OP_5-unequal kernel has size `|K|²`; zero coins fail `rlc5`. -/
theorem op5_bad_card :
    (badComputeAt (dummyCompute (K := F97) .s5 (FP.atomFP 1 0)
      (FP.atomFP 1 0) (FP.atomFP 1 1))).card
      = Fintype.card F97 * Fintype.card F97 := by
  have h := op5_needs
  let pub := dummyCompute (K := F97) .s5 (FP.atomFP 1 0)
    (FP.atomFP 1 0) (FP.atomFP 1 1)
  have hδ : deltaSize pub ≠ 0 ∨ deltaDyck pub ≠ 0 ∨ deltaLeaf pub ≠ 0 := by
    simpa [deltaSize, deltaDyck, deltaLeaf] using some_delta_of_fp_ne h.2
  rw [badComputeAt_eq_kernel pub h]
  exact kernel_card (deltaSize pub) (deltaDyck pub) (deltaLeaf pub) hδ

theorem op5_zero_fails_rlc5 :
    ¬ rlc5Holds (0 : F97) 0 0
        (dummyCompute .s5 (FP.atomFP 1 0) (FP.atomFP 1 0) (FP.atomFP 1 1)) := by
  intro h
  have := h op5_needs
  simp [rlc5Form, deltaSize, deltaDyck, deltaLeaf, dummyCompute] at this

/-- OP_8 encoding sizes are `z`-powers; `size8` holds for every `(a,b,c)` once `z ≠ 0`. -/
theorem op8_honest_size (z : F97) :
    HonestSize z (FP.atomFP z 0) :=
  ⟨1, by simp [FP.atomFP, pow_one]⟩

theorem op8_size8_of_z_ne (z : F97) (hz : z ≠ 0) :
    let pub := dummyCompute (K := F97) .s8 (FP.atomFP z 0)
      (FP.atomFP z 0) (FP.atomFP z 0)
    pub.state = .s8 → pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0 :=
  wf_size8_of_z_pows ⟨0, z, 0, 0, 0⟩ _ hz (op8_honest_size z) (op8_honest_size z)

theorem two_ne_zero_F97 : (2 : F97) ≠ 0 := by decide

/-- Zero memory record: `pole = −β`, so the live-row bad set is `{β = 0} × K`. -/
theorem live_memory_bad_card :
    (badMemoryAt (dummyMemory (K := F97) .read_root MemRec.zero)).card
      = Fintype.card F97 := by
  have h : needsPole (dummyMemory (K := F97) .read_root MemRec.zero) :=
    Or.inl rfl
  rw [badMemoryAt_eq_image _ h,
    Finset.card_image_of_injective _ (embedPole_injective _),
    Finset.card_univ]

theorem live_memory_zero_beta_fails :
    ¬ poleHolds (0 : F97) 0 (dummyMemory .read_root MemRec.zero) := by
  intro h
  have := h (Or.inl rfl)
  simp [dummyMemory, MemoryTable.Pub.cprime, MemoryTable.recRLC, MemRec.zero] at this

end F97Witness

#print axioms fn_size_ne_zero
#print axioms wf_size8_of_z_pows
#print axioms wf_size11_of_z_pows
#print axioms rlc5Holds_iff_wf
#print axioms honest_row_prob_ge
#print axioms computeWF_of_honest_sizes_and_rlc5
#print axioms memoryWF_of_pole_ne
#print axioms honest_compute_inhabits_RAP
#print axioms honest_memory_inhabits_RAP
#print axioms F97Witness.op5_bad_card
#print axioms F97Witness.op5_zero_fails_rlc5
#print axioms F97Witness.op8_size8_of_z_ne
#print axioms F97Witness.live_memory_bad_card
#print axioms F97Witness.live_memory_zero_beta_fails

end TableWFBounds
end Nock
