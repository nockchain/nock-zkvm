/-

  * `preadsA_facts`: every J-9 A atom-walk read has its root in `DA.acs`, a defined slot, and axis `≥ 2`.
  * `vhP9_A`: the atom walk's handle-provide publics `PQ` at `BRun9A`'s orbit `orbJ8 DA` are the `WA9` total over
    `DA.preads` (J-9 B's `vhP9_total` at `DA`; binders `hax9 hwalkA`).
  * `vhP9_A_split`: `= Σ_{DD.preads} WA9 + Σ_{axReadsK9} WA9` (`j9aDataOf_preads`).
  * `vhP9_BA`: the same through `(BA.M χ).pubsV` (verbatim field form).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalFA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSV

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

noncomputable section

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

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A
local notation "oA" => orbJ8 (j9aDataOf p Rg Rt hgen) (hF_run Rt hgen hpG h31A)

omit h31A in
/-- Every J-9 A atom-walk read: root in `DA.acs`, defined slot, axis `≥ 2`. -/
theorem preadsA_facts (hpG : p = Nock.Atoms.p) :
    ∀ x ∈ (DA).preads, x.1 ∈ (DA).acs ∧ (Noun.slot x.2 x.1).isSome ∧ 2 ≤ x.2 := by
  intro x hx
  rw [ComplJ9ADataRec.j9aDataOf_preads] at hx
  rw [ComplJ9ADataRec.j9aDataOf_acs]
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨a, ha, h1, h2, h3⟩ := preads_shape9 Rt hgen hpG x h
    have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
    have hpa : p ≤ a := by
      have : a ∈ ComplJ8Data.bigsP p (DD).roots (DD).rows := ha
      exact ((ComplJ8Atom.mem_bigsP p _ _ a).mp this).2
    exact ⟨h1 ▸ comb_mem_acs Rt hgen hpG ha (HonestPairX.two_le_length_limbs (by omega)), h3, h2⟩
  · obtain ⟨a, ha, hpa, hy⟩ := ComplJ9ABalFA.axReadsK9_facts Rt hgen x h
    obtain ⟨h2, h3, h1⟩ := ComplJ9ABalFA.limbReads_facts Rt hgen hpG ha hpa x hy
    exact ⟨h1, h3, h2⟩

/-- **The atom walk's handle provide at `DA`, orbit `orbJ8 DA`** (every coin): the `PQ` publics are the `WA9` total
over `DA.preads`.  Binders `hax9 hwalkA`. -/
theorem vhP9_A (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsVOf9 δ b (DA) (oA) χ WalkHQ.pubPQ) (pubsVOf9 δ b (DA) (oA) χ (WalkHQ.pubPQ + 1)) =
      ((DA).preads.map (WA9 δ (DA) χ)).sum := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hwA := ComplJ9ABalFA.hwA_A Rt hgen hpG
  have hallA := ComplJ9ABalFA.hallA_A Rt hgen hpG
  have hfa := preadsA_facts Rt hgen hpG
  have hwd := ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA
  have hcl : ∀ c ∈ (DA).acs, c.isCell = true := by
    rw [ComplJ9ADataRec.j9aDataOf_acs]; exact acs_cell Rt hgen hpG
  have hlenA : (DA).acs.length < p := by
    have := (rows31_of_A h31A) _ (show (DA).acs.length ∈ sizesJ8 (DA) by simp [sizesJ8])
    have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    omega
  set D := DA with hD
  set o := oA with ho
  by_cases h0 : D.preads = []
  · have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    have h0' : (DA).preads = [] := h0
    simp [pubsVOf9, h0', hz]
  have h6 : pubsVOf9 δ b D o χ WalkHQ.pubPQ = pub2 δ (vhP9 δ b D o χ) 6 := by simp [pubsVOf9, h0, WalkHQ.pubPQ]
  have h7 : pubsVOf9 δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (vhP9 δ b D o χ) 7 := by
    simp [pubsVOf9, h0, WalkHQ.pubPQ]
  rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  have hmem : ∀ x ∈ VclL.pathReads D.preads, x ∈ D.preads := fun x hx =>
    (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  have hslot : ∀ x ∈ VclL.pathReads D.preads, (Noun.slot x.2 x.1).isSome := fun x hx =>
    (hfa x (hmem x hx)).2.1
  have hpre : ∀ u ∈ walkRows D.acs D.preads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hwd hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 63 = 4 * 2 ^ 61 := by norm_num
    omega
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  rw [vhP9_eq δ b D o h0 hinjV χ hlenA hwA hcl hpre,
    walk_provide_total (W9 δ D χ) D.acs D.preads hslot (fun _ => rfl), pathKind_of_all hallA]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  have hx2 : x.2 < p := by
    have hd := hwd x (List.mem_dedup.mpr (List.mem_filter.mpr ⟨hx, hallA x hx⟩))
    have := ComplJ8OfBalG.ax_lt_of_depth (by have := (hfa x hx).2.2; omega) hd
    have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    omega
  exact W9_eq δ D χ x.1 x.2 (hfa x hx).1 hlenA hx2 _

/-- The same total, split: the J-8 pair reads plus the axis (big-limb) reads. -/
theorem vhP9_A_split (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsVOf9 δ b (DA) (oA) χ WalkHQ.pubPQ) (pubsVOf9 δ b (DA) (oA) χ (WalkHQ.pubPQ + 1)) =
      ((DD).preads.map (WA9 δ (DA) χ)).sum +
        ((ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t)).map (WA9 δ (DA) χ)).sum := by
  rw [vhP9_A δ b Rt hgen hpG h31A hax9 hwalkA χ, ComplJ9ADataRec.j9aDataOf_preads, List.map_append,
    List.sum_append]

/-- **`pubsV PQ` at `BRun9A`** (verbatim field form). -/
theorem vhP9_BA (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsV WalkHQ.pubPQ)
        (((BA).M χ).pubsV (WalkHQ.pubPQ + 1)) = ((DA).preads.map (WA9 δ (DA) χ)).sum := by
  have eV : ((BA).M χ).pubsV = pubsVOf9 δ b (DA) (oA) χ := rfl
  rw [eV]
  exact vhP9_A δ b Rt hgen hpG h31A hax9 hwalkA χ

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSV

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSV
#print axioms preadsA_facts
#print axioms vhP9_A
#print axioms vhP9_A_split
#print axioms vhP9_BA
end Axioms
