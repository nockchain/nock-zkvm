/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalFA.lean

  J-9 A, L7 balance: the atom-walk read facts for `hfxA`.
  * `combSlots`: every `limbAxes` axis (`≥ 2`) of a comb of `≥ 2` limbs is a defined slot of the comb.
  * `axReadsK9_facts`: every J-9 A axis read is a limb read of a big atom of `DD.bigs`.
  * `hallA_A` / `hwA_A`: the two facts `hallA`, `hwA` of `ComplJ9ABalF2.hfxA_A_of` for `DA`.
  * `hfxA_A`: the `hfxA` field at `BRun9A` (verbatim), via `ComplJ9ABalF2.hfxA_A_of`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalF2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalFA

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)
open Nock.GlobalCarryAxis (headOpt tailOpt slot_double slot_double_succ)
open Nock.V1J8.Gen (combOf)

noncomputable section

/-- **Slots of a comb**: with the comb of `xs` (`≥ 2` limbs) at axis `ax ≥ 1`, its top limb (the tail of the last
pair, relative axis `2^(L-1)·(ax+1) − 1`) and every other limb `j < L−1` (the head of the `j`-th pair,
`2^(j+1)·(ax+1) − 2`) are defined slots. -/
theorem combSlots : ∀ (xs : List ℕ), 2 ≤ xs.length → ∀ (ax : ℕ) (n : Noun), 1 ≤ ax →
    Noun.slot ax n = some (combOf xs) →
    (Noun.slot (2 ^ (xs.length - 1) * (ax + 1) - 1) n).isSome ∧
      ∀ j, j < xs.length - 1 → (Noun.slot (2 ^ (j + 1) * (ax + 1) - 2) n).isSome
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
      rw [slot_double_succ _ hax, hn, combOf_cons3]; rfl
    obtain ⟨ht, hh⟩ := combSlots (y :: z :: zs) (by simp) (2 * ax + 1) n (by omega) h1
    refine ⟨?_, fun j hj => ?_⟩
    · have e : 2 ^ ((x :: y :: z :: zs).length - 1) * (ax + 1) - 1
          = 2 ^ ((y :: z :: zs).length - 1) * (2 * ax + 1 + 1) - 1 := by
        have : (x :: y :: z :: zs).length - 1 = ((y :: z :: zs).length - 1) + 1 := by simp
        rw [this, pow_succ]; ring_nf
      rw [e]; exact ht
    · rcases j with _ | j
      · have e : 2 ^ (0 + 1) * (ax + 1) - 2 = 2 * ax := by simp; omega
        rw [e, slot_double _ hax, hn]; simp [combOf, headOpt]
      · have hj' : j < (y :: z :: zs).length - 1 := by simp at hj ⊢; omega
        have e : 2 ^ (j + 1 + 1) * (ax + 1) - 2 = 2 ^ (j + 1) * (2 * ax + 1 + 1) - 2 := by
          rw [pow_succ]; ring_nf
        rw [e]; exact hh j hj'

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf preadsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

include hpG

/-- The limb reads of a big atom of the run: axes `≥ 2`, defined slots of the comb, comb in `DD.acs`. -/
theorem limbReads_facts {a : ℕ} (ha : a ∈ (DD).bigs) (hpa : p ≤ a) :
    ∀ x ∈ ComplJ9AData.limbReads a, 2 ≤ x.2 ∧ (Noun.slot x.2 x.1).isSome ∧ x.1 ∈ (DD).acs := by
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hla := HonestPairX.two_le_length_limbs (a := a) (by omega)
  have hcomb := comb_mem_acs Rt hgen hpG ha hla
  set L := (Nock.Atoms.limbs a).length with hL
  obtain ⟨m, hm⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have h1 : Noun.slot 1 (combOf (Nock.Atoms.limbs a)) = some (combOf (Nock.Atoms.limbs a)) := by
    simp [Noun.slot]
  obtain ⟨ht, hh⟩ := combSlots _ hla 1 _ le_rfl h1
  intro x hx
  simp only [ComplJ9AData.limbReads, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [ComplJ9AData.limbAxes, List.mem_cons, List.mem_map, List.mem_range] at hy
  refine ⟨?_, ?_, hcomb⟩
  · rcases hy with rfl | ⟨j, hj, rfl⟩
    · have : 2 ^ 2 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      show 2 ≤ 2 ^ L - 1; omega
    · have : 2 ^ 2 ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      show 2 ≤ 2 ^ (j + 2) - 2; omega
  · rcases hy with rfl | ⟨j, hj, rfl⟩
    · have e : 2 ^ (L - 1) * (1 + 1) - 1 = 2 ^ L - 1 := by
        rw [← pow_succ]; congr 2; omega
      show (Noun.slot (2 ^ L - 1) _).isSome
      rw [← e]; exact ht
    · have e : 2 ^ (j + 1) * (1 + 1) - 2 = 2 ^ (j + 2) - 2 := by rw [← pow_succ]
      have := hh j (by omega)
      show (Noun.slot (2 ^ (j + 2) - 2) _).isSome
      rw [← e]; exact this

omit hpG in
/-- Every J-9 A axis read is a limb read of a big atom of `DD.bigs`. -/
theorem axReadsK9_facts : ∀ x ∈ ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t),
    ∃ a ∈ (DD).bigs, p ≤ a ∧ x ∈ ComplJ9AData.limbReads a := by
  have key : ∀ a, (∃ l ∈ (rowsOfT9 t).toList, (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = a) → p ≤ a →
      a ∈ (DD).bigs := by
    intro a ha hp
    have hmem : a ∈ ComplJ9AData.bigAx9 p (rowsOfT9 t) := by
      simp only [ComplJ9AData.bigAx9, List.mem_filter, decide_eq_true_eq]
      exact ⟨ComplJ9AData.mem_axAtoms9.2 ha, hp⟩
    exact ComplJ9AData.bigAx9_sub_bigs Rt hgen a hmem
  intro x hx
  simp only [ComplJ9AChainsRun.axReadsK9, List.mem_append, List.mem_flatMap, List.mem_filter,
    decide_eq_true_eq] at hx
  rcases hx with ⟨k, ⟨hk, hp⟩, hy⟩ | ⟨l, ⟨hl, hc, hp⟩, hy⟩
  · obtain ⟨l, hl, hlk⟩ := ComplJ9AChainsRun.mem_axKeys9.1 hk
    have hn : (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = k.2 := by
      unfold ComplJ9AChainsRun.axKey9 at hlk
      cases hc : l.chip <;> rw [hc] at hlk <;> simp at hlk
      · subst hlk; exact ⟨Or.inl rfl, rfl⟩
      · subst hlk; exact ⟨Or.inr rfl, rfl⟩
    exact ⟨k.2, key k.2 ⟨l, hl, hn⟩ hp, hp, hy⟩
  · exact ⟨l.n, key l.n ⟨l, hl, Or.inr hc, rfl⟩ hp, hp, hy⟩

/-- **`hallA`**: every J-9 A atom-walk read is at a path axis. -/
theorem hallA_A : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true := by
  intro x hx
  rw [ComplJ9ADataRec.j9aDataOf_preads] at hx
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨-, -, -, h2, -⟩ := preads_shape9 Rt hgen hpG x h
    exact isPathAx_of_two_le h2
  · obtain ⟨a, ha, hpa, hy⟩ := axReadsK9_facts Rt hgen x h
    exact isPathAx_of_two_le (limbReads_facts Rt hgen hpG ha hpa x hy).1

/-- **`hwA`**: every J-9 A atom-walk node is an atom cell of the table. -/
theorem hwA_A : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs := by
  rw [ComplJ9ADataRec.j9aDataOf_acs, ComplJ9ADataRec.j9aDataOf_preads]
  refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (ComplJ8Of.acs_pos (p := p) Rt hgen))
    (acs_closed_run Rt hgen hpG) ?_
  intro x hx _
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨a, ha, h1, -, h3⟩ := preads_shape9 Rt hgen hpG x h
    have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
    have hpa : p ≤ a := by
      have : a ∈ ComplJ8Data.bigsP p (DD).roots (DD).rows := ha
      exact ((ComplJ8Atom.mem_bigsP p _ _ a).mp this).2
    exact ⟨h1 ▸ comb_mem_acs Rt hgen hpG ha (HonestPairX.two_le_length_limbs (by omega)), h3⟩
  · obtain ⟨a, ha, hpa, hy⟩ := axReadsK9_facts Rt hgen x h
    obtain ⟨-, h2, h3⟩ := limbReads_facts Rt hgen hpG ha hpa x hy
    exact ⟨h3, h2⟩

/-- **`hfxA` at `BRun9A`** (the `hfxA` field, verbatim). -/
theorem hfxA_A (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsA 2 = ((BA).M χ).pubsV 0 ∧ ((BA).M χ).pubsA 3 = ((BA).M χ).pubsV 1 :=
  ComplJ9ABalF2.hfxA_A_of δ b Rt hgen hpG h31A hax9 hwalkA (hallA_A Rt hgen hpG) (hwA_A Rt hgen hpG)

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalFA

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalFA
#print axioms combSlots
#print axioms limbReads_facts
#print axioms axReadsK9_facts
#print axioms hallA_A
#print axioms hwA_A
#print axioms hfxA_A
end Axioms
