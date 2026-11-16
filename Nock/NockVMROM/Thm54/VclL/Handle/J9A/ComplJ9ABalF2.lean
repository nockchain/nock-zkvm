/-
J-9 A L7 balance, the atom fingerprint link `hfxA`.

  * `mxA_spec_gen`, `axT_eq_vxT9_gen`, `axT_zero_gen`, `balF2_gen`: J-9 B's `mxA_spec9` / `axT_eq_vxT9` /
    `axT_zero` / `balF2_run9` over any data record whose `mxA` is the generator's `wCounts` over `vs` and whose
    `vs` is the generator's atom walk over `preads` (the J-9 B forms read `j8DataOf` only through these two facts
    and the read-shape facts, which are now hypotheses).
  * `hfxA_A_of`: the `hfxA` field of `ComplJ9AObligations` at `BRun9A` (verbatim), from the J-9 A atom-walk read
    facts `hallA` (path axes) and `hwA` (every atom-walk node is an atom cell), plus binders `hax9 hwalkA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalGen
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalF2

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (idxRW walkRow0R wRowsBR wValsBR wColBR)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`mxA_spec9` over a record**: the atom export multiplicity counts the spec atom-walk rows at the generator's
serial. -/
theorem mxA_spec_gen (D : J8Data p Rg fuel s f r)
    (hmxA : D.mxA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs)
    (hvs : D.vs = (Nock.V1J8.Gen.walkGen (D.acs.headD (.atom 0)) D.preads).1)
    (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads D.preads, VclL.depthOf r.2 ≤ 62) (j : ℕ) (hj : j < D.acs.length) :
    D.mxA.getD j 0 = ((walkRows D.acs D.preads).filter fun t =>
      t.label.node.isCell && decide (gI (rIA D) D.acs (t.label.node, t.label.bits.length) = j)).length := by
  rw [hmxA, ComplJ8Data.wCounts_eq, ComplJ8Data.bumpAll0_getD _ _ _ hj, sumAt_wPairs, hvs]
  have hperm := walkGen_nodeLen_perm D.acs _ hall h62
  rw [(hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

/-- **`axT_eq_vxT9` over a record** (atom walk present). -/
theorem axT_eq_vxT9_gen (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ [])
    (hmxA : D.mxA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs)
    (hvs : D.vs = (Nock.V1J8.Gen.walkGen (D.acs.headD (.atom 0)) D.preads).1)
    (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
    (hcellsC : ∀ c ∈ D.acs, c.isCell = true) (χ : Coins frameJ8 K) :
    axT δ D χ = vxT9 δ D χ := by
  have h62 := ComplJ8Walk.walkDepth62 hwalkA
  have hspec := mxA_spec_gen D hmxA hvs hall h62
  set n := D.acs.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (aRows δ D χ j) 0))⁻¹ with hXG
  have hF : ∀ u ∈ walkRows D.acs D.preads, _ := fun u hu => idxRW_facts D u (hwcell u hu) (hcellsC _ (hwcell u hu))
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : vxT9 δ D χ = ((walkRows D.acs D.preads).map fun u => XG (idxRW D.acs (rIA D) u)).sum := by
    unfold vxT9
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem := wTrie_mem D.acs D.preads (Finset.mem_range.mp hk)
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vR9 δ D χ k)))⁻¹ = _
    rw [show vR9 δ D χ k = walkRow0R δ (GlobalCarryRecognizer.enc (zA δ χ)) D.acs (rIA D) D.preads
        (ChalsAZJ8.chalsAJ8Z δ χ 0) (ChalsAZJ8.chalsAJ8Z δ χ 1) k from rfl,
      wxKey_eqR δ (zA δ χ) (fun _ => none) D.acs (rIA D) D.preads (mvA D) (mxAF D) (fun _ => 0) _ _ k
        (hF _ hmem).1]
    rfl
  have hS := sum_serial n (fun u : NTree WN => idxRW D.acs (rIA D) u) XG (walkRows D.acs D.preads)
    (fun u hu => (hF u hu).2.1)
  have hC : axT δ D χ = ∑ j ∈ Finset.range n, ((mxAF D j : ℕ) : 𝕂′) * XG j := by
    unfold axT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
      ComplJ8Cell.cellRowB, liftQ, map_natCast,
      Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mxA.getD j 0 = _
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  rw [hcellsC _ (hwcell u hu), (hF u hu).2.2]
  simp

/-- **`axT_zero` over a record**: no atom-walk rows, no atom export. -/
theorem axT_zero_gen (D : J8Data p Rg fuel s f r)
    (hmxA : D.mxA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs) (hvs0 : D.vs = [])
    (χ : Coins frameJ8 K) : axT δ D χ = 0 := by
  unfold axT
  refine Finset.sum_eq_zero fun j hj => ?_
  have hm : D.mxA.getD j 0 = 0 := by
    rw [hmxA, ComplJ8Data.wCounts_eq, ComplJ8Data.bumpAll0_getD _ _ _ (Finset.mem_range.mp hj), hvs0]
    simp [ComplJ8Data.wPairs, ComplJ8Data.sumAt]
  simp only [xTermOf, cellFillInv, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
    ComplJ8Cell.cellRowB, liftQ, mxAF, hm,
    Nat.cast_zero, map_zero, zero_mul, add_zero]

/-- **`balF`'s atom / atom-walk clause over a record** (any orbit). -/
theorem balF2_gen (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h)
    (hmxA : D.mxA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs)
    (hvs : D.preads ≠ [] → D.vs = (Nock.V1J8.Gen.walkGen (D.acs.headD (.atom 0)) D.preads).1)
    (hvs0 : D.preads = [] → D.vs = [])
    (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
    (hcellsC : ∀ c ∈ D.acs, c.isCell = true) (χ : Coins frameJ8 K) :
    pubsAOf δ b D hA o χ 2 = pubsVOf9 δ b D o χ 0 ∧ pubsAOf δ b D hA o χ 3 = pubsVOf9 δ b D o χ 1 := by
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  obtain ⟨e2, e3⟩ := pubsAOf_23 δ b D hA o χ
  rw [e2, e3]
  by_cases h0 : D.preads = []
  · rw [axT_zero_gen δ D hmxA (hvs0 h0) χ]
    refine ⟨?_, ?_⟩
    · simp [pubsVOf9, pub2, h0, hz, Quad.re_mk]
    · simp [pubsVOf9, pub2, h0, hz, Quad.im_mk]
  · rw [axT_eq_vxT9_gen δ D h0 hmxA (hvs h0) hall hwalkA hwcell hcellsC χ]
    refine ⟨?_, ?_⟩
    · simp [pubsVOf9, pubsV09, pub2, h0]
    · simp [pubsVOf9, pubsV09, pub2, h0]

end Gen

/-! ## `hfxA` at `BRun9A` -/

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

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

/-- **`hfxA` at `BRun9A`** (the `hfxA` field, verbatim), from the J-9 A atom-walk read facts: `hallA` (every read
is at a path axis) and `hwA` (every atom-walk node is an atom cell of the table).  Binders `hax9 hwalkA`. -/
theorem hfxA_A_of (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hallA : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true)
    (hwA : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs) :
    ∀ χ, (BA).Good χ → ((BA).M χ).pubsA 2 = ((BA).M χ).pubsV 0 ∧ ((BA).M χ).pubsA 3 = ((BA).M χ).pubsV 1 := by
  intro χ _
  rw [ComplJ9AOfMem.pubsA_eq, ComplJ9AOfMem.pubsV_eq]
  have hvsdef : (DA).vs = (if (DA).preads.isEmpty then (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (DA).preads).1 := rfl
  refine balF2_gen δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) rfl
    (fun hne => ?_) (fun h0 => ?_) hallA (ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA) hwA
    (ComplJ8OfBal.acs_cell Rt hgen hpG) χ
  · rw [hvsdef, if_neg (by simpa using hne)]
    exact walkGen_dummy _ _ _ hne
  · rw [hvsdef, if_pos (by simp [h0])]

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalF2

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalF2
#print axioms mxA_spec_gen
#print axioms axT_eq_vxT9_gen
#print axioms axT_zero_gen
#print axioms balF2_gen
#print axioms hfxA_A_of
end Axioms
