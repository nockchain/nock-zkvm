/-

  * `combSlotsVal`: the value form of `ComplJ9ABalFA.combSlots` (top limb and limb `j` of a comb are the atoms).
  * `slot_limbAxis_top`, `slot_limbAxis`: at `ax = 1`.
  * `limbReads_sum`: for a big atom `n ∈ DD.bigs` (`p ≤ n`), the atom walk's reads of its limbs weigh
    `Σ_{limbReads n} WA9 δ DA χ = Σ_{limbRecs ((DA.H (atom n)).2) n} limbW`.
  * `axReadsK9_sum`: hence `Σ_{axReadsK9} WA9` = the big keys' `limbRecs` + the big `s10B` rows' `limbRecs`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalFA
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSL

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.GlobalCarryAxis (headOpt tailOpt slot_double slot_double_succ)
open Nock.V1J8.Gen (combOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx (limbW limbRecs)
open Nock.J9A.NounAx (top top_eq_length)

noncomputable section

/-- **Value form of the comb slots**: with the comb of `xs` (`≥ 2` limbs) at axis `ax ≥ 1`, the top limb sits at
`2^(L-1)·(ax+1) − 1` and limb `j < L−1` at `2^(j+1)·(ax+1) − 2`. -/
theorem combSlotsVal : ∀ (xs : List ℕ), 2 ≤ xs.length → ∀ (ax : ℕ) (n : Noun), 1 ≤ ax →
    Noun.slot ax n = some (combOf xs) →
    Noun.slot (2 ^ (xs.length - 1) * (ax + 1) - 1) n = some (.atom (xs.getD (xs.length - 1) 0)) ∧
      ∀ j, j < xs.length - 1 → Noun.slot (2 ^ (j + 1) * (ax + 1) - 2) n = some (.atom (xs.getD j 0))
  | [x, y], _, ax, n, hax, hn => by
    refine ⟨?_, fun j hj => ?_⟩
    · have e : 2 ^ ([x, y].length - 1) * (ax + 1) - 1 = 2 * ax + 1 := by simp; omega
      rw [e, slot_double_succ _ hax, hn]; simp [combOf, tailOpt]
    · have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      have e : 2 ^ (0 + 1) * (ax + 1) - 2 = 2 * ax := by simp; omega
      rw [e, slot_double _ hax, hn]; simp [combOf, headOpt]
  | x :: y :: z :: zs, _, ax, n, hax, hn => by
    have h1 : Noun.slot (2 * ax + 1) n = some (combOf (y :: z :: zs)) := by
      rw [slot_double_succ _ hax, hn, ComplJ9BBalF.combOf_cons3]; rfl
    obtain ⟨ht, hh⟩ := combSlotsVal (y :: z :: zs) (by simp) (2 * ax + 1) n (by omega) h1
    refine ⟨?_, fun j hj => ?_⟩
    · have e : 2 ^ ((x :: y :: z :: zs).length - 1) * (ax + 1) - 1
          = 2 ^ ((y :: z :: zs).length - 1) * (2 * ax + 1 + 1) - 1 := by
        have : (x :: y :: z :: zs).length - 1 = ((y :: z :: zs).length - 1) + 1 := by simp
        rw [this, pow_succ]; ring_nf
      rw [e, ht]
      simp
    · rcases j with _ | j
      · have e : 2 ^ (0 + 1) * (ax + 1) - 2 = 2 * ax := by simp; omega
        rw [e, slot_double _ hax, hn]; simp [combOf, headOpt]
      · have hj' : j < (y :: z :: zs).length - 1 := by simp at hj ⊢; omega
        have e : 2 ^ (j + 1 + 1) * (ax + 1) - 2 = 2 ^ (j + 1) * (2 * ax + 1 + 1) - 2 := by
          rw [pow_succ]; ring_nf
        rw [e, hh j hj']
        simp

/-- The top limb of the comb at axis `2^L − 1`. -/
theorem slot_limbAxis_top (xs : List ℕ) (h : 2 ≤ xs.length) :
    Noun.slot (2 ^ xs.length - 1) (combOf xs) = some (.atom (xs.getD (xs.length - 1) 0)) := by
  have h1 : Noun.slot 1 (combOf xs) = some (combOf xs) := by simp [Noun.slot]
  have := (combSlotsVal xs h 1 _ le_rfl h1).1
  have e : 2 ^ (xs.length - 1) * (1 + 1) - 1 = 2 ^ xs.length - 1 := by
    rw [← pow_succ]; congr 2; omega
  rwa [e] at this

/-- Limb `j < L − 1` of the comb at axis `2^(j+2) − 2`. -/
theorem slot_limbAxis (xs : List ℕ) (h : 2 ≤ xs.length) (j : ℕ) (hj : j < xs.length - 1) :
    Noun.slot (2 ^ (j + 2) - 2) (combOf xs) = some (.atom (xs.getD j 0)) := by
  have h1 : Noun.slot 1 (combOf xs) = some (combOf xs) := by simp [Noun.slot]
  have := (combSlotsVal xs h 1 _ le_rfl h1).2 j hj
  have e : 2 ^ (j + 1) * (1 + 1) - 2 = 2 ^ (j + 2) - 2 := by rw [← pow_succ]
  rwa [e] at this

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

include hpG

/-- **The big-limb bridge.**  For a big atom `n ∈ DD.bigs` (`p ≤ n`), the atom walk's reads of its limbs weigh the
limb records `limbRecs ((H (atom n)).2) n`. -/
theorem limbReads_sum {n : ℕ} (hn : n ∈ (DD).bigs) (hpn : p ≤ n) (χ : Coins frameJ8 K) :
    ((ComplJ9AData.limbReads n).map (WA9 δ (DA) χ)).sum =
      ((limbRecs (p := p) ((DA).H (.atom n)).2 n).map (limbW δ χ)).sum := by
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hn0 : n ≠ 0 := by
    have : 0 < p := (Fact.out : p.Prime).pos
    omega
  have hla := HonestPairX.two_le_length_limbs (a := n) (by omega)
  have hL := top_eq_length n hn0
  have hcomb := comb_mem_acs Rt hgen hpG hn hla
  have hroot : ((DA).H (.atom n)).2 = ComplJ8Data.rIAP p (DA).acs (combOf (Nock.Atoms.limbs n)) := by
    show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom n)).2 = _
    have : ¬ n < p := Nat.not_lt.mpr hpn
    simp only [ComplJ8Data.hdlP, this, if_false]
    exact ComplJ9BBalG.rootIdx_rIAP hpG (DD).acs hla
  have hlim : ∀ x ∈ Nock.Atoms.limbs n, x < p := fun x hx =>
    lt_of_lt_of_le ((Nock.Atoms.limbs_canonical n).1 x hx) hBp
  have hW : ∀ ax a, Noun.slot ax (combOf (Nock.Atoms.limbs n)) = some (.atom a) → a < p →
      WA9 δ (DA) χ (combOf (Nock.Atoms.limbs n), ax) =
        limbW δ χ (((DA).H (.atom n)).2, (ax : ZMod p), (0, (a : ZMod p))) := by
    intro ax a hs ha
    have hh : Nock.V1J8.Gen.hdl (DA).acs (.atom a) = (0, a) :=
      ComplJ9BBalV.hdl_small hpG _ a ha
    have hch : ComplJ8Data.chPP p (DA).acs (DA).rows (combOf (Nock.Atoms.limbs n), ax) = (0, a) := by
      simp [ComplJ8Data.chPP, hs, hh]
    simp only [WA9, hch, limbW]
    rw [show rIA (DA) (combOf (Nock.Atoms.limbs n)) = ((DA).H (.atom n)).2 from hroot.symm]
    simp
  have ha32 : ∀ i, n / 2 ^ (32 * i) % 2 ^ 32 < p := fun i =>
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by have : Nock.Atoms.B = 2 ^ 32 := rfl; omega)
  simp only [ComplJ9AData.limbReads, ComplJ9AData.limbAxes, limbRecs, List.map_cons, List.sum_cons, List.map_map]
  rw [hL]
  simp only [Nat.add_sub_cancel]
  refine congrArg₂ (· + ·) ?_ ?_
  · have ht := slot_limbAxis_top (Nock.Atoms.limbs n) hla
    rw [hL] at ht
    simp only [Nat.add_sub_cancel, ComplJ9AChains.limbs_getD] at ht
    rw [hW _ _ ht (ha32 _), Nat.cast_sub (Nat.one_le_two_pow)]
    simp
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    have hs := slot_limbAxis (Nock.Atoms.limbs n) hla i (by omega)
    simp only [ComplJ9AChains.limbs_getD] at hs
    try simp only [Function.comp_apply]
    rw [hW _ _ hs (ha32 _), Nat.cast_sub (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ i + 2 by omega); omega)]
    simp

omit hpG in
theorem sum_map_flatMap {α β M : Type} [AddCommMonoid M] (g : α → List β) (w : β → M) :
    ∀ L : List α, (((L.flatMap g).map w).sum) = (L.map fun a => ((g a).map w).sum).sum
  | [] => rfl
  | a :: L => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap g w L]

/-- **The J-9 A axis reads, weighed**: `Σ_{axReadsK9} WA9` = the distinct big keys' `limbRecs` plus the big `s10B`
rows' `limbRecs` (ids `(DA.H (atom n)).2`, which is `idOf9` at a big `n` by `idOf9_big`). -/
theorem axReadsK9_sum (χ : Coins frameJ8 K) :
    ((ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t)).map (WA9 δ (DA) χ)).sum =
      ((((ComplJ9AChainsRun.axKeys9 (rowsOfT9 t)).filter fun k => p ≤ k.2).map fun k =>
          ((limbRecs (p := p) ((DA).H (.atom k.2)).2 k.2).map (limbW δ χ)).sum).sum) +
      ((((rowsOfT9 t).toList.filter fun l => l.chip = .s10B ∧ p ≤ l.n).map fun l =>
          ((limbRecs (p := p) ((DA).H (.atom l.n)).2 l.n).map (limbW δ χ)).sum).sum) := by
  have key : ∀ a, (∃ l ∈ (rowsOfT9 t).toList, (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = a) → p ≤ a →
      a ∈ (DD).bigs := by
    intro a ha hp
    have hmem : a ∈ ComplJ9AData.bigAx9 p (rowsOfT9 t) := by
      simp only [ComplJ9AData.bigAx9, List.mem_filter, decide_eq_true_eq]
      exact ⟨ComplJ9AData.mem_axAtoms9.2 ha, hp⟩
    exact ComplJ9AData.bigAx9_sub_bigs Rt hgen a hmem
  unfold ComplJ9AChainsRun.axReadsK9
  rw [List.map_append, List.sum_append, sum_map_flatMap, sum_map_flatMap]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
    obtain ⟨hk, hp⟩ := List.mem_filter.mp hk
    have hp' : p ≤ k.2 := by simpa using hp
    obtain ⟨l, hl, hlk⟩ := ComplJ9AChainsRun.mem_axKeys9.1 hk
    have hn : (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = k.2 := by
      unfold ComplJ9AChainsRun.axKey9 at hlk
      cases hc : l.chip <;> rw [hc] at hlk <;> simp at hlk
      · subst hlk; exact ⟨Or.inl rfl, rfl⟩
      · subst hlk; exact ⟨Or.inr rfl, rfl⟩
    exact limbReads_sum δ Rt hgen hpG (key k.2 ⟨l, hl, hn⟩ hp') hp' χ
  · refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    obtain ⟨hl, hc⟩ := List.mem_filter.mp hl
    have hc' : l.chip = .s10B ∧ p ≤ l.n := by simpa using hc
    exact limbReads_sum δ Rt hgen hpG (key l.n ⟨l, hl, Or.inr hc'.1, rfl⟩ hc'.2) hc'.2 χ

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSL
#print axioms combSlotsVal
#print axioms slot_limbAxis_top
#print axioms slot_limbAxis
#print axioms limbReads_sum
#print axioms sum_map_flatMap
#print axioms axReadsK9_sum
end Axioms
