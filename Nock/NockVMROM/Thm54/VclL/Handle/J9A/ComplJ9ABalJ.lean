/-
J-9 A L7 balance: the J export key identity `hJA` (the `hJA` binder of `ComplJ9ABalG1.hGx_A_of`).

The J-9 A record `DA` has the J-8 record's `jrows`, `cells`, `acs`, `H` (`rfl`), only its walk data and multiplicities
differ.  J-8's `hJ_export` (at `j8DataOf`, any orbit) gives the key identity at the J-8 cell weight; here the cell weight
`GC` at `DA` and at `j8DataOf` agree at every serial `< |cells|` (both are the same `recDen` by `cellHx_eq`, `hH := rfl`),
and the serials are in range by `jReads_range`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalG1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalJ

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC cellHx_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalG1 (cells_kids_gen GA)

noncomputable section

section J9A
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DD" => j8DataOf p Rg Rt hgen

/-- The cell handle weight at `DA` and at `DD` agree at every serial `< |cells|`, at any orbit injective on the
cell count. -/
theorem GC_eq {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DA).cells.length)) (χ : Coins frameJ8 K) (j : ℕ)
    (hj : j < (DA).cells.length) :
    GC δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o χ j = GC δ b (DD) (ComplJ8Of.cells_pos Rt hgen) o χ j := by
  have hjD : j < (DD).cells.length := hj
  have hcl : ComplJ8Data.ClP (DD).cells [] := ComplJ8Data.cells_closed _
  obtain ⟨x, y, hxy, hx, hy⟩ := cells_kids_gen (DD).cells hcl
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) _ (List.getElem_mem hjD)
  have hxyA : (DA).cells[j] = Noun.cell x y := hxy
  have hxyD : (DD).cells[j] = Noun.cell x y := hxy
  simp only [GC]
  rw [cellHx_eq δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o hinj χ rfl j hj hxyA hx hy,
    cellHx_eq δ b (DD) (ComplJ8Of.cells_pos Rt hgen) o hinj χ rfl j hjD hxyD hx hy]
  rfl

variable (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

set_option maxHeartbeats 1000000 in
/-- **`hJA`**: the J export key identity at `GA` (the cell weight at `orbJ8 DA`), the `hJA` binder of
`ComplJ9ABalG1.hGx_A_of`, from the registry binder `hRt` (as in `balG1_run`). -/
theorem hJA_A
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) :
    ∀ row ∈ (DA).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) = GA δ b Rt hgen hpG h31A χ (κ.headD 0).val := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hlen : (DD).cells.length < p := by
    have h1 := rows31_of_A h31A (DA).cells.length hmC
    have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    show (DA).cells.length < p
    omega
  have hkN : ∀ x ∈ (DD).jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1 :=
    fun x hx => (Nock.Jet.ChipJ8.gate_facts x (ComplJ8Jet.jrows_gate_run Rt hgen hp0 hRt x hx)).2.2.2
  have hcalls : ∀ cl ∈ (DD).calls, (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r :=
    ComplJ8Jet.calls_of_hregC hgen Rt hRt
  set o := orbJ8 (DA) (hF_run Rt hgen hpG h31A) with ho
  have hinj := (powN_ok o (le_two_pow_ht (DA) hmC)).1
  intro row hrow κ hκ
  have hJ := ComplJ8OfBalG.hJ_export δ b Rt hgen o hinj χ hcalls hlen hkN row hrow κ hκ
  have hrg := ComplJ8Data.jReads_range p Rg Rt hgen hlen hkN ((κ.headD 0).val, 1)
    (List.mem_flatMap.mpr ⟨row, hrow, List.mem_map.mpr ⟨κ, hκ, rfl⟩⟩)
  rw [hJ]
  exact (GC_eq δ b Rt hgen o hinj χ _ hrg).symm

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalJ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalJ
#print axioms GC_eq
#print axioms hJA_A
end Axioms
