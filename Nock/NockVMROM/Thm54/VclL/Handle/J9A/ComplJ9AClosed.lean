/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AClosed.lean

* `obligations_of_runA`: every field of `ComplJ9AObligations` at the J-9 A honest record `BRun9A` (present AND
    absent axis / split chips: `BRun9A` is one record for both regimes, its chips switched by `axOnA t` / `spOnA p t`).
  * **`complJ9A_closed`**: `complJ9A_of_obligations` at `BRun9A`, with `RowsLe31A` discharged from `h31A`.
    Binders: `hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx h31A`; J-9 B's `hax` / `hwalk` are
    replaced by `hax9 : ProgAxOK9A` / `hwalk9 : WalkDepthOK9A` (each implied by J-9 B's, `ComplJ9ABinders`), `h31`
    by `h31A : Rows31A`. No inc-corner binder.  One record `BRun9A` in both regimes, so no presence case split
    (the binder set allows `BA` in both cases).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalP
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalO
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalS
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfStatic
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfBad
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOf
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARunFacts
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAbsentLift

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A Rows31A axOnA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

noncomputable section

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

/-- **Every obligation at `BRun9A`** (present and absent chips). -/
theorem obligations_of_runA (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31A : Rows31A (DA)) :
    ComplJ9AObligations δ b (BRun9A δ b Rt hgen hpG h31A) := by
  have hlen := ComplJ9ARunFacts.hlen_run Rt hgen hpG h31A
  have hsub := ComplJ9ARunFacts.sub9_run (p := p) Rt hgen
  have hrowsA := ComplJ9ARunFacts.hrowsA_run Rt hgen hpG hax9 hop5
  obtain ⟨⟨hinjC, hadjC, hnpC⟩, ⟨hinjW, hadjW, hkW, hknW, hkpW⟩, ⟨hinjA, hadjA, hnpA⟩⟩ :=
    ComplJ9AOfMem.nodes_A δ b Rt hgen hpG h31A
  obtain ⟨hlay, hsmall, huniq, hTpl, hnd, hidx, hrk, hlt⟩ :=
    ComplJ9AOfStatic.stat_A δ b Rt hgen hpG h31A hax9 hleaf hRt
  obtain ⟨hclI, hclR, hcen', hcellF⟩ := ComplJ9AOfStatic.claim_A δ b Rt hgen hpG h31A hleaf
  obtain ⟨hlenC, hlenA, hnAS, hbud, hbudV, hlenX⟩ := ComplJ9AOfStatic.budget_A δ b Rt hgen hpG h31A
  exact
  { hsatX := fun χ hχ => ComplJ9AOfComp.hsatXA δ b Rt hgen hpG h31A hax9 hop5 χ hχ
    hinjX := ComplJ9AOfComp.hinjXA δ b Rt hgen hpG h31A
    hadjX := ComplJ9AOfComp.hadjXA δ b Rt hgen hpG h31A
    hsatC := fun χ hχ => (ComplJ9AOfMem.cell_A δ b Rt hgen hpG h31A hleaf χ hχ).1
    hbindC := fun χ hχ => (ComplJ9AOfMem.cell_A δ b Rt hgen hpG h31A hleaf χ hχ).2
    hinjC := hinjC
    hadjC := hadjC
    hnpC := hnpC
    hsatW := fun χ hχ => (ComplJ9AOfMem.walk_A δ b Rt hgen hpG h31A hwalk9 χ hχ).1
    hbindW := fun χ hχ => (ComplJ9AOfMem.walk_A δ b Rt hgen hpG h31A hwalk9 χ hχ).2
    hinjW := hinjW
    hadjW := hadjW
    hkW := hkW
    hknW := hknW
    hkpW := hkpW
    hJk := fun χ hχ => ComplJ9AOfMem.j_A δ b Rt hgen hpG h31A hRt χ hχ
    hsatA := fun χ hχ => (ComplJ9AOfMem.atom_A δ b Rt hgen hpG h31A χ hχ).1.1
    hbindA := fun χ hχ => (ComplJ9AOfMem.atom_A δ b Rt hgen hpG h31A χ hχ).1.2
    hinjA := hinjA
    hadjA := hadjA
    hnpA := hnpA
    hsatL := fun χ hχ => (ComplJ9AOfMem.atom_A δ b Rt hgen hpG h31A χ hχ).2.1
    hbindL := fun χ hχ => (ComplJ9AOfMem.atom_A δ b Rt hgen hpG h31A χ hχ).2.2
    hVk := fun χ hχ => ComplJ9AOfMem.aw_A δ b Rt hgen hpG h31A hax9 hwalkA χ hχ
    hGx := ComplJ9ABalO.hGx_A δ b Rt hgen hpG h31A hax9 hop5 hsub hwalk9 hRt hrowsA
    hGp := fun χ hχ => ComplJ9ABalP.hGpA δ b Rt hgen hpG h31A hax9 hop5 hlen hwalk9 χ hχ
    hGS := fun χ hχ => ComplJ9ABalS.hGSA δ b Rt hgen hpG h31A hax9 hop5 hRt hwalk9 hwalkA χ hχ
    hsumC' := ComplJ9ABalO.hsumC_A δ b Rt hgen hpG h31A
    hbalA' := ComplJ9ABalO.hbalA_A δ b Rt hgen hpG h31A hax9 hwalkA
    hvalA0 := ComplJ9ABalO.hvalA0_A' δ b Rt hgen hpG h31A
    hfxC := ComplJ9ABalO.hfxC_A' δ b Rt hgen hpG h31A hwalk9
    hfxA := ComplJ9ABalO.hfxA_A' δ b Rt hgen hpG h31A hax9 hwalkA
    hlay := hlay
    hsmall := hsmall
    huniq := huniq
    hTpl := hTpl
    hnd := hnd
    hidx := hidx
    hrk := hrk
    hlt := hlt
    hclI := hclI
    hclR := hclR
    hcen' := hcen'
    hcellF := hcellF
    hlenC := hlenC
    hlenA := hlenA
    hnAS := hnAS
    hbud := hbud
    hbudV := hbudV
    hAXk := fun χ hχ => ComplJ9AOf.axOK_A δ b Rt hgen hpG h31A χ hχ
    hSPk := fun χ hχ => ComplJ9AOf.spOK_A δ b Rt hgen hpG h31A hax9 χ hχ
    hlenX := hlenX
    wt := ComplJ9AOfBad.wtA δ b Rt hgen hpG h31A
    staged := ComplJ9AOfBad.stagedA δ b Rt hgen hpG h31A
    fig := ComplJ9AOfBad.figA δ b Rt hgen hpG h31A }

/-- `RowsLe31A` at `BRun9A`, from `h31A`. -/
theorem rowsLe31A_runA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (DA)) : RowsLe31A (BRun9A δ b Rt hgen hpG h31A).Pb := by
  have hW : (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows (DA).cells (DA).reads).length ∈
      ComplJ9ARun.sizesA (DA) := List.mem_append_left _ (by simp [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.sizesJ8])
  exact ⟨⟨h31A _ (ComplJ9AOfStatic.mem_N9 Rt hgen), h31A _ (ComplJ9AOfStatic.mem_cells Rt hgen), h31A _ hW,
    h31A _ (ComplJ9AOfStatic.mem_jrows Rt hgen), h31A _ (ComplJ9AOfStatic.mem_acs Rt hgen),
    h31A _ (ComplJ9AOfStatic.mem_nV Rt hgen)⟩,
    h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen), h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen)⟩

open Classical in
/-- **The J-9 A completeness conclusion at `BRun9A`** (`complJ9A_of_obligations`, `RowsLe31A` discharged). -/
def ConclA (hpG : p = Nock.Atoms.p) (h31A : Rows31A (DA)) : Prop :=
  let B := BRun9A δ b Rt hgen hpG h31A
  (∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g)

open Classical in
/-- **`complJ9A_closed`: J-9 A general completeness at Goldilocks, chips on, nothing carried.**  For every
generated run `hgen` of every program over every verified registry `Rg` whose called jets are registered in
compiled form (`hRt`, `hregAx`), under the J-9 A axis binder `hax9` (every op-0 / op-9 / op-10 axis either J-9 B
admissible or served by the axis / split chip), `hop5`, the leaf binder `hleaf`, the J-9 A walk binder `hwalk9`
(reads still routed through the J-9 B walk), `hwalkA` (atom reads) and every table, old and new, `≤ 2^31` rows
(`h31A`); no inc-corner binder: at the run's J-9 A honest record `BRun9A` (axis chip present iff `axOnA t`, split
chip iff `spOnA p t`), honest acceptance by `AcceptsJ9A` at every good coin, `Pr[¬Good] ≤ ε_c`, staging `StJ9A`,
the claim holds, and at `|K| = cK` the figure `ε_c < 2^-120` with an accepting coin.  No presence case split is
needed: `BRun9A` switches its chips by `axOnA t` / `spOnA p t` itself and every obligation is proved at it in both
regimes. -/
theorem complJ9A_closed (hpG : p = Nock.Atoms.p) (hax9 : ProgAxOK9A p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31A : Rows31A (DA)) :
    let B := BRun9A δ b Rt hgen hpG h31A
    (∀ χ, B.Good χ → AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  intro B
  have O := obligations_of_runA δ b Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx h31A
  have hrows := rowsLe31A_runA δ b Rt hgen hpG h31A
  obtain ⟨h1, h2, h3, h4, h5⟩ := complJ9A_of_obligations δ b B O
  exact ⟨h1, h2, h3, h4, fun hcK => h5 hpG hcK hrows⟩

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed
#print axioms obligations_of_runA
#print axioms rowsLe31A_runA
#print axioms complJ9A_closed
end Axioms
