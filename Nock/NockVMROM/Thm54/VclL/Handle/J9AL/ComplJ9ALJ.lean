/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALJ.lean

  **The J chip and the node facts at the J-9 AL overlay `DL`.**

  * `jOK_L`: `ComplJ9AOfMem.jOK_A8` at `DL = j9alDataOf p Rg Rt prims hgen`, with the prim-aware binder `hRtJ`
    (`hRt` on the non-primitive called ids only) feeding `ComplJ9ALData.jrows_gateL`.
  * `nodes_L`: `ComplJ9AOfMem.nodes_A8` at `DL` (J-8's `nodes_group`), under `Rows31 DL`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALJ

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.Jet.Prim (PrimOp)

noncomputable section

section Lanes
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hF : DvdOK (j9alDataOf p Rg Rt prims hgen)) (hC : 0 < (j9alDataOf p Rg Rt prims hgen).cells.length)
  (hA : 0 < (j9alDataOf p Rg Rt prims hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **The J chip at the overlay record** (`ComplJ9AOfMem.jOK_A8` at `DL`; the gates from `jrows_gateL` under the
prim-aware binder `hRtJ`). -/
theorem jOK_L
    (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hJ : famJ δ (DL) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (honestJ8Of δ b (DL) hF hC hA AV fams).Good χ) :
    let B := honestJ8Of δ b (DL) hF hC hA AV fams
    JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
      (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ) := by
  intro B
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (DL).jrows.length = 0
  · refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
    have hs : ∀ (g : Fin (DL).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
      intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
    have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
      (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
    have e : ∀ i, pubsJOf δ (DL) χ i = 0 := by
      intro i
      unfold pubsJOf
      rw [hs, hs]
      split_ifs <;> simp [pub2, hz.1, hz.2]
    exact ⟨e 0, e 1, e 2, e 3⟩
  · have hn : 0 < (DL).jrows.length := Nat.pos_of_ne_zero h0
    obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (DL).jrows.length)
      (le_two_pow_ht _ (by simp [sizesJ8]))
    have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DL).t]).length)] fams), χ ∉ e.1 := hχ
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (DL).jrows.get)
      (ComplJ8Jet.jKeysX (DL).jrows.get) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hJ, he⟩)))
    have := ComplJ8Jet.jOK_present_trJ δ b (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsJJ8 χ) (pubsJOf δ _ χ)
      (DL).jrows.get hinj hn hadj
      (fun i => ComplJ9ALData.jrows_gateL Rt prims hgen hp hRtJ _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])
    exact this

/-- **The node facts at the overlay record** (`ComplJ9AOfMem.nodes_A8` at `DL`, under `Rows31 DL`). -/
theorem nodes_L (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DL)) :
    ComplJ9AOfMem.NodesOK (honestJ8Of δ b (DL) hF hC hA AV fams).Pb := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmC : (DL).cells.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hmW : (walkRows (DL).cells (DL).reads).length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hmA : (DL).acs.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  obtain ⟨c1, c2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmC)
  obtain ⟨w1, w2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmW)
  obtain ⟨a1, a2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmA)
  have hWb := h31 _ hmW
  have hk := krW_le_rows (DL).cells (DL).reads
  have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  refine ⟨⟨c1, c2, ?_⟩, ⟨w1, w2, one_le_krW _ _, hk, ?_⟩, ⟨a1, a2, ComplJ9ATables.lt31 hp63 h31 hmA⟩⟩
  · rw [hrc]; exact ComplJ9ATables.lt31 hp63 h31 hmC
  · rw [hrc]; show krW _ _ + (walkRows _ _).length < p; omega

end Lanes

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALJ
