/-
  Nock/RedTeam/Batch1670Thm54VclLCore.lean

  Production: `P8Core/VclL/Table.lean`,
  `Census.lean`, `Chain.lean`.
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1670

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.T0Tower
open Nock.ComputeTable (FP)

/-! ## §A  B0 only; no relinking -/

#check @decodeB0
#check @preZNounOfTable

theorem decodeB0_strip {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]
    (t : List (CellRow q Kfp)) (fuel i : ℕ) :
    decodeB0 ((t.map strip).map (·.b0)) fuel i = decodeB0 (t.map (·.b0)) fuel i :=
  VclL.decodeB0_strip t fuel i

/-- Stripping is a real strip: every fingerprint column becomes `0`. -/
theorem strip_zeroes {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp] (c : CellRow q Kfp) :
    (strip c).p = 0 ∧ (strip c).l = 0 ∧ (strip c).r = 0 ∧ (strip c).b0 = c.b0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem served_of_b0 {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]
    (hq : 2 ^ 63 < q) {z z' : Kfp} (hz : z ≠ 0) (hz' : z' ≠ 0)
    {t t' : List (CellRow q Kfp)} {vl vl' : List (VKey Kfp)}
    (h : TableAccepts z t vl) (h' : TableAccepts z' t' vl')
    (hb0 : t.map (·.b0) = t'.map (·.b0)) :
    ∀ c ∈ t, ∀ c' ∈ t', c.b0.idx = c'.b0.idx →
      ∃ n, c.p = GlobalCarryRecognizer.enc z n ∧ c'.p = GlobalCarryRecognizer.enc z' n :=
  VclL.served_of_b0 hq hz hz' h h' hb0

/-! ## §B  At the tower -/

/-- `Quad δ` carries the `ZMod q`-algebra the atom gate needs (through `K`). -/
noncomputable example {q : ℕ} {K : Type} [Field K] [Algebra (ZMod q) K] (δ : K)
    [Fact (¬ IsSquare δ)] : Algebra (ZMod q) (Quad δ) := inferInstance

/-- **T1 at `Kfp = Quad δ`** (no new hypothesis). -/
theorem t1_at_tower {q : ℕ} [Fact q.Prime] (hq : 2 ^ 63 < q) {K : Type} [Field K]
    [Algebra (ZMod q) K] (δ : K) [Fact (¬ IsSquare δ)] {z : Quad δ} (hz : z ≠ 0)
    {t : List (CellRow q (Quad δ))} {vl : List (VKey (Quad δ))} (h : TableAccepts z t vl) :
    ∀ c ∈ t, ∃ n, preZNounOfTable (t.map (·.b0)) c.b0.idx = some n ∧
      c.p = GlobalCarryRecognizer.enc z n ∧ n.leaves = c.b0.mu + 1 ∧ n.leaves ≤ fuelChip ∧
      ∀ k ∈ n.leafList, k < q :=
  preZNounOfTable_sound hq hz h

/-! ## §C  Axioms -/

#print axioms Nock.NockVMROM.Thm54.VclL.mu_limbs_exact
#print axioms Nock.NockVMROM.Thm54.VclL.rowOK_mu
#print axioms Nock.NockVMROM.Thm54.VclL.rowOK_mu_lt
#print axioms Nock.NockVMROM.Thm54.VclL.decode_sound
#print axioms Nock.NockVMROM.Thm54.VclL.preZNounOfTable_sound
#print axioms Nock.NockVMROM.Thm54.VclL.row_genuine
#print axioms Nock.NockVMROM.Thm54.VclL.decodeB0_strip
#print axioms Nock.NockVMROM.Thm54.VclL.served_of_b0
#print axioms Nock.NockVMROM.Thm54.VclL.served_of_b0_same_seed
#print axioms Nock.NockVMROM.Thm54.VclL.child_mu_lt
#print axioms Nock.NockVMROM.Thm54.VclL.childRel_wf
#print axioms Nock.NockVMROM.Thm54.VclL.tableBadSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.VclL.decodedNouns_inj_of_not_mem
#print axioms Nock.NockVMROM.Thm54.VclL.censusBadSet_card_le
#print axioms Nock.NockVMROM.Thm54.VclL.tableCensusSummand_weight_le
#print axioms Nock.NockVMROM.Thm54.VclL.tableCensusSummand_mem_iff
#print axioms Nock.NockVMROM.Thm54.VclL.vclCensusSummand_shape
#print axioms Nock.NockVMROM.Thm54.VclL.chain_slot
#print axioms Nock.NockVMROM.Thm54.VclL.edge_exported_of_balanced
#print axioms Nock.NockVMROM.Thm54.VclL.chain_sound
#print axioms Nock.NockVMROM.Thm54.VclL.chain_sound_root
#print axioms Nock.NockVMROM.Thm54.VclL.chain_sound_of_census
#print axioms Nock.NockVMROM.Thm54.VclL.chain_needs_atom_pairs
#print axioms Nock.RedTeam.Batch1670.t1_at_tower


/-- An atom is never a B0-decoded noun (the decode always builds a cell). -/
theorem atom_not_decoded {q : ℕ} (t : List (CellRowB0 q)) (k : ℕ) : Noun.atom k ∉ decodedNouns t := by
  intro h
  obtain ⟨i, -, hd⟩ := mem_decodedNouns.mp h
  obtain ⟨a, b, hab⟩ := decodeB0_isCell t _ _ _ hd
  exact Noun.noConfusion hab

/-- So an atom-child/decoded-cell pair is listed by T2 only through the skeleton part. -/
theorem atom_pair_listed_only_via_skel {q : ℕ} (t : List (CellRowB0 q)) (skel : List Noun) (k : ℕ)
    (h : Noun.atom k ∈ censusNouns t skel) : Noun.atom k ∈ skel := by
  rcases List.mem_append.mp h with h | h
  · exact absurd h (atom_not_decoded t k)
  · exact h

#print axioms Nock.RedTeam.Batch1670.atom_not_decoded
#print axioms Nock.RedTeam.Batch1670.atom_pair_listed_only_via_skel

end Nock.RedTeam.Batch1670
