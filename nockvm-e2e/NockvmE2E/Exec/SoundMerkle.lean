/-
  NockvmE2E/Exec/SoundMerkle.lean   (proof-only)

  L3 / L4 (Merkle part).  The flat verifier's per-tree root recursion (`Exec/Verify.lean` `goRoot`) is mirrored here over a
  `Skeleton` (`goSk`, total, structural) and shown to be the root VCVio's `getPutativeBatchRootAddressedWithHash` computes on the
  structured opening built from the same flat streams (`mkOpening`: dense selector, `SelectedValues`, pruned frontier).
  Then `merkleCheck` under a fixed table is the conjunction of these root comparisons.
-/
import NockvmE2E.Merkle.Opening
import NockvmE2E.Exec.Verify

open BinaryTree InductiveMerkleTree OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SM

open NockvmE2E.Merkle

section Flat

variable {D : Type}

/-- heap number of an internal node, given the heap number `idx` of the subtree's root -/
def heapIdx : {s : Skeleton} → SkeletonInternalIndex s → ℕ → ℕ
  | _, .ofInternal, idx => idx
  | _, .ofLeft a, idx => heapIdx a (2 * idx)
  | _, .ofRight a, idx => heapIdx a (2 * idx + 1)

/-- the dense selector of the leaves `lo, lo+1, …` marked by `isSel` -/
def selOf (isSel : ℕ → Bool) : (s : Skeleton) → ℕ → LeafData Bool s
  | .leaf, lo => .leaf (isSel lo)
  | .internal l r, lo => .internal (selOf isSel l lo) (selOf isSel r (lo + l.leafCount))

/-- the claimed values: `lv lo` at the selected leaf `lo` -/
def valsOf (lv : ℕ → D) : (s : Skeleton) → (sel : LeafData Bool s) → ℕ → SelectedValues D sel
  | _, .leaf true, lo => lv lo
  | _, .leaf false, _ => PUnit.unit
  | .internal sl sr, .internal l r, lo => (valsOf lv sl l lo, valsOf lv sr r (lo + sl.leafCount))

/-- the pruned frontier, consuming the sibling digests in pre-order (a sibling before the sub-opening it is pruned beside) -/
def mkProof : {s : Skeleton} → (sel : LeafData Bool s) → List D → Option (BatchProof D sel × List D)
  | _, .leaf true, sb => some (.leaf, sb)
  | _, .leaf false, _ => none
  | _, .internal l r, sb =>
      match hl : l.anySelected, hr : r.anySelected with
      | true, true => do
          let (pl, s1) ← mkProof l sb
          let (pr, s2) ← mkProof r s1
          some (.internalBoth pl pr, s2)
      | true, false =>
          match sb with
          | [] => none
          | sib :: sb' => do
              let (pl, s1) ← mkProof l sb'
              some (.pruneRight hr sib pl, s1)
      | false, true =>
          match sb with
          | [] => none
          | sib :: sb' => do
              let (pr, s1) ← mkProof r sb'
              some (.pruneLeft hl sib pr, s1)
      | false, false => none

/-- The flat root recursion of `Exec/Verify.lean` `goRoot`, over a skeleton: `has a b` = "some leaf in `[a, b)` is selected"
(the verifier's `lb` comparisons), `isSel` = leaf selected, `lv` = the claimed leaf digest, `sibs` = frontier digests; node digest
`nh idx l r` at heap number `idx`. -/
def goSk (nh : ℕ → D → D → D) (has : ℕ → ℕ → Bool) (isSel : ℕ → Bool) (lv : ℕ → D) :
    (s : Skeleton) → ℕ → ℕ → List D → Option (D × List D)
  | .leaf, _, lo, sb => if isSel lo then some (lv lo, sb) else none
  | .internal l r, idx, lo, sb =>
      match has lo (lo + l.leafCount), has (lo + l.leafCount) (lo + l.leafCount + r.leafCount) with
      | true, true => do
          let (a, s1) ← goSk nh has isSel lv l (2 * idx) lo sb
          let (b, s2) ← goSk nh has isSel lv r (2 * idx + 1) (lo + l.leafCount) s1
          some (nh idx a b, s2)
      | true, false =>
          match sb with
          | [] => none
          | sib :: sb' => do
              let (a, s1) ← goSk nh has isSel lv l (2 * idx) lo sb'
              some (nh idx a sib, s1)
      | false, true =>
          match sb with
          | [] => none
          | sib :: sb' => do
              let (b, s1) ← goSk nh has isSel lv r (2 * idx + 1) (lo + l.leafCount) sb'
              some (nh idx sib b, s1)
      | false, false => none

theorem goSk_sound (nh : ℕ → D → D → D) (has : ℕ → ℕ → Bool) (isSel : ℕ → Bool) (lv : ℕ → D)
    (hhas : ∀ (s : Skeleton) (lo : ℕ), has lo (lo + s.leafCount) = (selOf isSel s lo).anySelected) :
    ∀ (s : Skeleton) (idx lo : ℕ) (sb : List D) (r : D) (rest : List D),
      goSk nh has isSel lv s idx lo sb = some (r, rest) →
      ∃ pr, mkProof (selOf isSel s lo) sb = some (pr, rest) ∧
        AddressedMerkleTree.getPutativeBatchRootAddressedWithHash (fun a l r' => nh (heapIdx a idx) l r')
          (valsOf lv s (selOf isSel s lo) lo) pr = r := by
  intro s
  induction s with
  | leaf =>
      intro idx lo sb r rest h
      simp only [goSk] at h
      cases hs : isSel lo
      · simp [hs] at h
      · simp only [hs, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hsel : selOf isSel .leaf lo = .leaf true := by simp [selOf, hs]
        rw [hsel]
        exact ⟨.leaf, by simp [mkProof], by simp [valsOf, AddressedMerkleTree.getPutativeBatchRootAddressedWithHash]⟩
  | internal sl sr ihl ihr =>
      intro idx lo sb r rest h
      simp only [goSk] at h
      rw [hhas sl lo, hhas sr (lo + sl.leafCount)] at h
      simp only [selOf]
      cases hA : (selOf isSel sl lo).anySelected <;> cases hB : (selOf isSel sr (lo + sl.leafCount)).anySelected <;>
        simp only [hA, hB] at h
      · simp at h
      · cases sb with
        | nil => simp at h
        | cons sib sb' =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨b, s1⟩, hb, hr⟩ := h
          obtain ⟨pr, hpr, hroot⟩ := ihr (2 * idx + 1) (lo + sl.leafCount) sb' b s1 hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨.pruneLeft hA sib pr, ?_, ?_⟩
          · simp only [mkProof, hpr]
            split <;> first | rfl | simp_all
          · simp [valsOf, AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, hroot, heapIdx]
      · cases sb with
        | nil => simp at h
        | cons sib sb' =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨a, s1⟩, ha, hr⟩ := h
          obtain ⟨pl, hpl, hroot⟩ := ihl (2 * idx) lo sb' a s1 ha
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          refine ⟨.pruneRight hB sib pl, ?_, ?_⟩
          · simp only [mkProof, hpl]
            split <;> first | rfl | simp_all
          · simp [valsOf, AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, hroot, heapIdx]
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨a, s1⟩, ha, ⟨⟨b, s2⟩, hb, hr⟩⟩ := h
        obtain ⟨pl, hpl, hrootl⟩ := ihl (2 * idx) lo sb a s1 ha
        obtain ⟨pr, hpr, hrootr⟩ := ihr (2 * idx + 1) (lo + sl.leafCount) s1 b s2 hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨.internalBoth pl pr, ?_, ?_⟩
        · simp only [mkProof, hpl, hpr]
          split <;> first | rfl | simp_all
        · simp [valsOf, AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, hrootl, hrootr, heapIdx]

/-- an opening of every skeleton (leaf 0 of each subtree selected); only the junk default of `mkOpening` -/
def junkOpening [Inhabited D] : (s : Skeleton) → BatchOpening D s
  | .leaf => ⟨.leaf true, (default : D), .leaf⟩
  | .internal l r =>
      ⟨.internal (junkOpening l).selector (junkOpening r).selector,
        ((junkOpening l).values, (junkOpening r).values),
        .internalBoth (junkOpening l).proof (junkOpening r).proof⟩

/-- **L4 (Merkle part): the embedded opening** of a flat tree opening.  Total: when the frontier stream is malformed the junk
opening is returned; it is never reached when the flat check passed (`mkOpening_root`). -/
def mkOpening [Inhabited D] (isSel : ℕ → Bool) (lv : ℕ → D) (s : Skeleton) (sb : List D) : BatchOpening D s :=
  match mkProof (selOf isSel s 0) sb with
  | some (pr, []) => ⟨selOf isSel s 0, valsOf lv s (selOf isSel s 0) 0, pr⟩
  | _ => junkOpening s

theorem mkOpening_eq [Inhabited D] (isSel : ℕ → Bool) (lv : ℕ → D) (s : Skeleton) (sb : List D)
    (pr : BatchProof D (selOf isSel s 0)) (h : mkProof (selOf isSel s 0) sb = some (pr, [])) :
    mkOpening isSel lv s sb = ⟨selOf isSel s 0, valsOf lv s (selOf isSel s 0) 0, pr⟩ := by
  unfold mkOpening
  rw [h]

/-- **L3 (Merkle part).** If the flat root recursion (`goSk`, the skeleton form of `goRoot`) succeeds on a tree consuming the whole frontier
stream and returns `root`, then the embedded opening reconstructs `root` under node digest `nh (heap number)`, i.e. VCVio's addressed
putative root equals the flat root. -/
theorem mkOpening_root [Inhabited D] (nh : ℕ → D → D → D) (has : ℕ → ℕ → Bool) (isSel : ℕ → Bool) (lv : ℕ → D)
    (hhas : ∀ (s : Skeleton) (lo : ℕ), has lo (lo + s.leafCount) = (selOf isSel s lo).anySelected)
    (s : Skeleton) (sb : List D) (root : D) (h : goSk nh has isSel lv s 1 0 sb = some (root, [])) :
    AddressedMerkleTree.getPutativeBatchRootAddressedWithHash (fun a l r' => nh (heapIdx a 1) l r')
      (mkOpening isSel lv s sb).values (mkOpening isSel lv s sb).proof = root := by
  obtain ⟨pr, hpr, hroot⟩ := goSk_sound nh has isSel lv hhas s 1 0 sb root [] h
  rw [mkOpening_eq isSel lv s sb pr hpr]
  exact hroot

end Flat

section LB
open NockvmE2E.Exec.V (lb lbGo)

/-- binary search invariant: on `[lo,hi)` the entries `< x` form a prefix, then `lbGo` returns the boundary -/
theorem lbGo_spec (a : Array ℕ) (x : ℕ) :
    ∀ (f lo hi : ℕ), lo ≤ hi → hi - lo ≤ f → hi ≤ a.size →
      (∀ i j, lo ≤ i → i ≤ j → j < hi → a[j]! < x → a[i]! < x) →
      lo ≤ lbGo a x f lo hi ∧ lbGo a x f lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < lbGo a x f lo hi → a[i]! < x) ∧
      (∀ i, lbGo a x f lo hi ≤ i → i < hi → ¬ a[i]! < x) := by
  intro f
  induction f with
  | zero =>
    intro lo hi hlh hf hs hm
    have : hi = lo := by omega
    simp only [lbGo]
    refine ⟨le_refl _, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
  | succ f ih =>
    intro lo hi hlh hf hs hm
    simp only [lbGo]
    by_cases h : lo < hi
    · simp only [h, ite_true]
      by_cases hm' : a[(lo + hi) / 2]! < x
      · simp only [hm', ite_true]
        have := ih ((lo + hi) / 2 + 1) hi (by omega) (by omega) hs (fun i j h1 h2 h3 h4 => hm i j (by omega) h2 h3 h4)
        obtain ⟨h1, h2, h3, h4⟩ := this
        refine ⟨by omega, h2, fun i hi1 hi2 => ?_, h4⟩
        by_cases hc : i < (lo + hi) / 2 + 1
        · exact hm i ((lo + hi) / 2) hi1 (by omega) (by omega) hm'
        · exact h3 i (by omega) hi2
      · simp only [hm', ite_false]
        have := ih lo ((lo + hi) / 2) (by omega) (by omega) (by omega) (fun i j h1 h2 h3 h4 => hm i j h1 h2 (by omega) h4)
        obtain ⟨h1, h2, h3, h4⟩ := this
        refine ⟨h1, by omega, h3, fun i hi1 hi2 => ?_⟩
        by_cases hc : i < (lo + hi) / 2
        · exact h4 i hi1 hc
        · intro hlt
          exact hm' (hm ((lo + hi) / 2) i (by omega) (by omega) hi2 hlt)
    · simp only [h, ite_false]
      exact ⟨le_refl _, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩

/-- `lb` on a strictly increasing array: `a[i] < x ↔ i < lb a x` for `i < a.size` -/
theorem lb_spec (a : Array ℕ) (x : ℕ) (hs : a.toList.Pairwise (· < ·)) :
    lb a x ≤ a.size ∧ (∀ i, i < lb a x → a[i]! < x) ∧ (∀ i, lb a x ≤ i → i < a.size → ¬ a[i]! < x) := by
  have hmono : ∀ i j, 0 ≤ i → i ≤ j → j < a.size → a[j]! < x → a[i]! < x := by
    intro i j _ hij hj hx
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; exact hx
    · have := List.pairwise_iff_getElem.mp hs i j (by simpa using (by omega : i < a.size))
        (by simpa using hj) h
      have e1 : a[i]! = a[i]'(by omega) := by simp [show i < a.size by omega]
      have e2 : a[j]! = a[j]'hj := by simp [hj]
      rw [e1]; rw [e2] at hx
      simpa using lt_trans this hx
  have := lbGo_spec a x (a.size + 1) 0 a.size (by omega) (by omega) le_rfl hmono
  unfold lb
  obtain ⟨_, h2, h3, h4⟩ := this
  exact ⟨h2, fun i hi => h3 i (by omega) hi, fun i h1 h2 => h4 i h1 h2⟩

theorem mem_iff_lb (sel : Array ℕ) (hs : sel.toList.Pairwise (· < ·)) (x : ℕ) :
    sel[lb sel x]? = some x ↔ x ∈ sel.toList := by
  obtain ⟨h1, h2, h3⟩ := lb_spec sel x hs
  constructor
  · intro h
    have hlt : lb sel x < sel.size := by
      by_contra hc; rw [Array.getElem?_eq_none (by omega)] at h; simp at h
    rw [Array.getElem?_eq_getElem hlt] at h
    simp only [Option.some.injEq] at h
    rw [← h]; exact Array.getElem_mem_toList hlt
  · intro h
    obtain ⟨i, hi', rfl⟩ := Array.getElem_of_mem (Array.mem_def.mpr h)
    have e : sel[i]! = sel[i] := by simp [hi']
    have ha : lb sel sel[i] ≤ i := by
      by_contra hc
      have := h2 i (by omega); rw [e] at this; exact lt_irrefl _ this
    have hb : i ≤ lb sel sel[i] := by
      by_contra hc
      have hl : lb sel sel[i] < sel.size := by omega
      have := h3 (lb sel sel[i]) le_rfl hl
      have e2 : sel[lb sel sel[i]]! = sel[lb sel sel[i]] := by simp [hl]
      rw [e2] at this
      exact this (List.pairwise_iff_getElem.mp hs _ _ (by simpa using hl) (by simpa using hi') (by omega))
    have : lb sel sel[i] = i := le_antisymm ha hb
    rw [this, Array.getElem?_eq_getElem hi']

theorem has_iff_lb (sel : Array ℕ) (hs : sel.toList.Pairwise (· < ·)) (a b : ℕ) (hab : a ≤ b) :
    lb sel a < lb sel b ↔ ∃ y ∈ sel.toList, a ≤ y ∧ y < b := by
  obtain ⟨ha1, ha2, ha3⟩ := lb_spec sel a hs
  obtain ⟨hb1, hb2, hb3⟩ := lb_spec sel b hs
  constructor
  · intro h
    have hr : lb sel a < sel.size := by omega
    refine ⟨sel[lb sel a], Array.getElem_mem_toList hr, ?_, ?_⟩
    · have := ha3 (lb sel a) le_rfl hr
      have e : sel[lb sel a]! = sel[lb sel a] := by simp [hr]
      rw [e] at this; omega
    · have := hb2 (lb sel a) h
      have e : sel[lb sel a]! = sel[lb sel a] := by simp [hr]
      rw [e] at this; exact this
  · rintro ⟨y, hy, hay, hyb⟩
    obtain ⟨i, hi', rfl⟩ := Array.getElem_of_mem (Array.mem_def.mpr hy)
    have e : sel[i]! = sel[i] := by simp [hi']
    have h1 : lb sel a ≤ i := by
      by_contra hc
      have := ha2 i (by omega); rw [e] at this; omega
    have h2 : i < lb sel b := by
      by_contra hc
      have := hb3 i (by omega) hi'; rw [e] at this; exact this hyb
    omega

/-- the dense selector selects something in `[lo, lo + leafCount)` iff `isSel` holds there -/
theorem anySel_selOf (isSel : ℕ → Bool) : ∀ (s : Skeleton) (lo : ℕ),
    (selOf isSel s lo).anySelected = true ↔ ∃ i, lo ≤ i ∧ i < lo + s.leafCount ∧ isSel i = true := by
  intro s
  induction s with
  | leaf =>
    intro lo
    simp only [selOf, LeafData.anySelected, Skeleton.leafCount]
    constructor
    · intro h; exact ⟨lo, le_rfl, by omega, h⟩
    · rintro ⟨i, h1, h2, h3⟩; have : i = lo := by omega
      subst this; exact h3
  | internal l r ihl ihr =>
    intro lo
    simp only [selOf, LeafData.anySelected, Bool.or_eq_true, ihl, ihr, Skeleton.leafCount]
    constructor
    · rintro (⟨i, h1, h2, h3⟩ | ⟨i, h1, h2, h3⟩)
      · exact ⟨i, h1, by omega, h3⟩
      · exact ⟨i, by omega, by omega, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      by_cases hc : i < lo + l.leafCount
      · exact Or.inl ⟨i, h1, hc, h3⟩
      · exact Or.inr ⟨i, by omega, by omega, h3⟩

/-- **`hhas`** for the verifier's `lb` comparisons on a strictly increasing selection -/
theorem hhas_lb (sel : Array ℕ) (hs : sel.toList.Pairwise (· < ·)) :
    ∀ (s : Skeleton) (lo : ℕ),
      decide (lb sel lo < lb sel (lo + s.leafCount)) =
        (selOf (fun i => sel[lb sel i]? == some i) s lo).anySelected := by
  intro s lo
  rw [Bool.eq_iff_iff, decide_eq_true_eq, anySel_selOf, has_iff_lb sel hs lo _ (by omega)]
  constructor
  · rintro ⟨y, hy, h1, h2⟩; exact ⟨y, h1, h2, by simpa [mem_iff_lb sel hs] using hy⟩
  · rintro ⟨y, h1, h2, h3⟩; exact ⟨y, by simpa [mem_iff_lb sel hs] using h3, h1, h2⟩

end LB

section Link
open NockvmE2E.Exec.V (TSpec goRootF lb tagNode HFn Dg5)

/-- the skeleton of a `TSpec` over `cnt` leaves (fuel `f ≥ cnt`) -/
def skelOf (sp : TSpec) : ℕ → ℕ → Skeleton
  | 0, _ => .leaf
  | f + 1, cnt => if cnt == 1 then .leaf else
      .internal (skelOf sp f (sp.split cnt)) (skelOf sp f (cnt - sp.split cnt))

/-- the split function never degenerates (the verifier's `L == 0 || L ≥ cnt` guard is never hit) -/
def WfSpec (sp : TSpec) : Prop := ∀ c, 1 < c → 0 < sp.split c ∧ sp.split c < c

theorem leafCount_skelOf (sp : TSpec) (hw : WfSpec sp) :
    ∀ (f cnt : ℕ), 1 ≤ cnt → cnt ≤ f → (skelOf sp f cnt).leafCount = cnt := by
  intro f
  induction f with
  | zero => intro cnt h1 h2; omega
  | succ f ih =>
    intro cnt h1 h2
    simp only [skelOf]
    by_cases hc : cnt = 1
    · subst hc; simp [Skeleton.leafCount]
    · have hc' : (cnt == 1) = false := by simpa using hc
      obtain ⟨hL0, hL1⟩ := hw cnt (by omega)
      simp only [hc', Bool.false_eq_true, ite_false, Skeleton.leafCount]
      rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      omega

theorem goRootF_goSk (H : HFn) (sp : TSpec) (hw : WfSpec sp) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : ℕ) (d : Dg5) (s' : ℕ), 1 ≤ cnt → cnt ≤ f → s ≤ sibs.size →
      goRootF H sp j sel leaf sibs f idx lo cnt s = some (d, s') →
      s ≤ s' ∧ s' ≤ sibs.size ∧
      goSk (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (fun a b => decide (lb sel a < lb sel b))
        (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i)) (skelOf sp f cnt) idx lo (sibs.toList.drop s)
        = some (d, sibs.toList.drop s') := by
  intro f
  induction f with
  | zero => intro idx lo cnt s d s' h1 h2; omega
  | succ f ih =>
    intro idx lo cnt s d s' h1 h2 h3 h
    simp only [goRootF] at h
    by_cases hc : cnt = 1
    · subst hc
      simp only [beq_self_eq_true, ite_true] at h
      by_cases hs : (sel[lb sel lo]? == some lo) = true
      · simp only [hs, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨le_rfl, h3, ?_⟩
        simp [skelOf, goSk, hs]
      · simp only [hs, ite_false] at h; simp at h
    · have hc' : (cnt == 1) = false := by simpa using hc
      obtain ⟨hL0, hL1⟩ := hw cnt (by omega)
      have hg : ¬ ((sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true) := by simp; omega
      simp only [hc', Bool.false_eq_true, ite_false, hg] at h
      have lcl := leafCount_skelOf sp hw f (sp.split cnt) (by omega) (by omega)
      have lcr := leafCount_skelOf sp hw f (cnt - sp.split cnt) (by omega) (by omega)
      simp only [skelOf, hc', Bool.false_eq_true, ite_false, goSk, lcl, lcr]
      have e : lo + sp.split cnt + (cnt - sp.split cnt) = lo + cnt := by omega
      rw [e]
      have hL1' : sp.split cnt ≤ f := by omega
      have hR1' : cnt - sp.split cnt ≤ f := by omega
      generalize sp.split cnt = L at *
      have hdrop : ∀ (s0 : ℕ) (sib : Dg5), sibs[s0]? = some sib →
          List.drop s0 sibs.toList = sib :: List.drop (s0 + 1) sibs.toList := by
        intro s0 sib hs0
        have hlt : s0 < sibs.size := by
          by_contra hc; rw [Array.getElem?_eq_none (by omega)] at hs0; simp at hs0
        rw [Array.getElem?_eq_getElem hlt] at hs0
        simp only [Option.some.injEq] at hs0
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]
        simp [hs0]
      have hlt_of : ∀ (s0 : ℕ) (sib : Dg5), sibs[s0]? = some sib → s0 + 1 ≤ sibs.size := by
        intro s0 sib hs0
        by_contra hc; rw [Array.getElem?_eq_none (by omega)] at hs0; simp at hs0
      by_cases hab : lb sel lo < lb sel (lo + L) <;> by_cases hbc : lb sel (lo + L) < lb sel (lo + cnt)
      · have hh : (decide (lb sel (lo + L) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + L))) = true := by
          simp [hab, hbc]
        simp only [hh, ite_true] at h
        simp only [hab, hbc, decide_true]
        rcases h1 : goRootF H sp j sel leaf sibs f (2 * idx) lo L s with _ | ⟨x1, t1⟩
        · simp [h1] at h
        · rcases h2 : goRootF H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) t1 with _ | ⟨x2, t2⟩
          · simp [h1, h2] at h
          · simp [h1, h2] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨a1, b1, c1⟩ := ih (2 * idx) lo L s x1 t1 (by omega) hL1' h3 h1
            obtain ⟨a2, b2, c2⟩ := ih (2 * idx + 1) (lo + L) (cnt - L) t1 x2 t2 (by omega) hR1' b1 h2
            refine ⟨by omega, b2, ?_⟩
            simp only [c1, c2, bind, Option.bind]
            simp
      · have hh : ¬ (decide (lb sel (lo + L) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + L))) = true := by
          simp [hab, hbc]
        have hbc' : ¬ lb sel (lo + L) < lb sel (lo + cnt) := hbc
        simp only [hh, ite_false, gt_iff_lt, hab, hbc', ite_true] at h
        simp only [hab, decide_true, decide_false, hbc']
        rcases hs : sibs[s]? with _ | sib
        · simp [hs] at h
        · rw [hdrop s sib hs]
          rcases h1 : goRootF H sp j sel leaf sibs f (2 * idx) lo L (s + 1) with _ | ⟨x1, t1⟩
          · simp [hs, h1] at h
          · simp [hs, h1] at h
            obtain ⟨rfl, rfl⟩ := h
            have hs1 := hlt_of s sib hs
            obtain ⟨a1, b1, c1⟩ := ih (2 * idx) lo L (s + 1) x1 t1 (by omega) hL1' hs1 h1
            refine ⟨by omega, b1, ?_⟩
            simp only [c1, bind, Option.bind]
            simp
      · have hh : ¬ (decide (lb sel (lo + L) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + L))) = true := by
          simp [hab, hbc]
        have hab' : ¬ lb sel lo < lb sel (lo + L) := hab
        simp only [hh, ite_false, gt_iff_lt, hab', hbc, ite_true] at h
        simp only [hab', hbc, decide_true, decide_false]
        rcases hs : sibs[s]? with _ | sib
        · simp [hs] at h
        · rw [hdrop s sib hs]
          rcases h1 : goRootF H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) (s + 1) with _ | ⟨x1, t1⟩
          · simp [hs, h1] at h
          · simp [hs, h1] at h
            obtain ⟨rfl, rfl⟩ := h
            have hs1 := hlt_of s sib hs
            obtain ⟨a1, b1, c1⟩ := ih (2 * idx + 1) (lo + L) (cnt - L) (s + 1) x1 t1 (by omega) hR1' hs1 h1
            refine ⟨by omega, b1, ?_⟩
            simp only [c1, bind, Option.bind]
            simp
      · have hh : ¬ (decide (lb sel (lo + L) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + L))) = true := by
          simp [hab, hbc]
        simp only [hh, ite_false, gt_iff_lt, hab, hbc] at h
        simp at h

open NockvmE2E.Exec.V (goRoot) in
/-- **per-tree Merkle soundness of the flat check**: if the verifier's `goRoot` accepts (returns `root`, consumed the whole frontier) on a
strictly increasing selection, then the embedded opening's VCVio putative root (node digest `H ([tagNode, j, heapNumber] ++ l ++ r)`)
is `root`. -/
theorem merkle_of_goRoot (H : HFn) (sp : TSpec) (hw : WfSpec sp) (j : ℕ) (sel : Array ℕ)
    (hs : sel.toList.Pairwise (· < ·)) (leaf : ℕ → Dg5) (sibs : Array Dg5) (root : Dg5) (h1 : 1 ≤ sp.total)
    (h : goRoot H sp j sel leaf sibs 1 0 sp.total 0 = some (root, sibs.size)) :
    AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
      (fun a l r' => (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (heapIdx a 1) l r')
      (mkOpening (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i)) (skelOf sp sp.total sp.total) sibs.toList).values
      (mkOpening (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i)) (skelOf sp sp.total sp.total) sibs.toList).proof
      = root := by
  obtain ⟨_, _, hg⟩ := goRootF_goSk H sp hw j sel leaf sibs sp.total 1 0 sp.total 0 root sibs.size h1 le_rfl (Nat.zero_le _) h
  have hd : List.drop sibs.size sibs.toList = [] := by simp
  rw [List.drop_zero, hd] at hg
  exact mkOpening_root (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (fun a b => decide (lb sel a < lb sel b))
    (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i)) (hhas_lb sel hs) _ _ _ hg

theorem wf_friSpec (n : ℕ) : WfSpec (NockvmE2E.Exec.V.friSpec n) := by
  intro c hc; simp only [NockvmE2E.Exec.V.friSpec]; omega

theorem wf_ragSpec (W half : ℕ) (hW : 1 ≤ W) : WfSpec (NockvmE2E.Exec.V.ragSpec W half) := by
  intro c hc
  simp only [NockvmE2E.Exec.V.ragSpec]
  split_ifs <;> simp_all <;> omega

end Link

end NockvmE2E.Exec.SM

#print axioms NockvmE2E.Exec.SM.goSk_sound
#print axioms NockvmE2E.Exec.SM.mkOpening_root
#print axioms NockvmE2E.Exec.SM.hhas_lb
#print axioms NockvmE2E.Exec.SM.merkle_of_goRoot
#print axioms NockvmE2E.Exec.SM.wf_ragSpec
