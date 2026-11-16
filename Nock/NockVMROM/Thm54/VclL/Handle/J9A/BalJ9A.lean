/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/BalJ9A.lean

  `JGenJ8.balJ8_frameJ8G` assumes `ext .p = []`; at J-9 A the axis chip consumes path records, so `.p` gets its own
  external sum `TextP` and the verifier check `hGp : ρ₄ + TextP = (pubW₆, pubW₇)`. `.x` is the J-8 telescope
  verbatim (cell providers, walk + J consumers, `hGx`); `.s` is given by its two sums and `ρ_s + TextS = TprovS`
  (S9 supplies them from the J / atom / atom-walk / axis / split telescopes and `hGS`).
  * **`balJ9A_frame`**: `BalJ8` at `pubVJ9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BalJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8 (provsX_sumQ provsP_sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8 (JChipOK extX_sumQG)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9 rhoX_pubVJ9)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd)

noncomputable section

section Frame
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`hbal` at the J-9 A frame** (`pubVJ9`): `.x` the J-8 telescope, `.p` with the axis path consumes `TextP`,
`.s` from its sums. -/
theorem balJ9A_frame (χ : SVFrame.Coins FrameJ8.frameJ8 K) (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS)
    (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (TextP : 𝕂′)
    (hP_ext : ((ext .p).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextP)
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 *
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum = TprovS)
    (hS_ext : ((ext .s).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 + TextP = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGs : ρS + TextS = TprovS) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ9 δ b c m ρ ρS χ) provs ext := by
  have hcv := coinsCV_J8 δ b χ
  intro bl
  rw [rhoX_pubVJ9 δ b c m ρ ρS χ bl]
  cases bl with
  | x =>
    have hx1 := extX_sumQG δ b _ kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
        ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm) nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hJk
        ((coinsJX_J8 δ χ).trans hcv.symm)
    have hx2 := provsX_sumQ δ b _ hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC
        ((mcoins_of_agree δ χ chalsC hchC).trans hcv.symm)
    rw [rhoX_x_J8, hextX, hprovX]
    convert hGx using 2 <;> first | exact hx1 | exact hx2
  | p =>
    have hp2 := provsP_sumQ δ b _ kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
        ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm)
    rw [rhoX_p_J8, hP_ext, hprovP]
    convert hGp using 1
    exact hp2
  | s =>
    rw [rhoX_s_J8, hS_ext, hS_prov]
    exact hGs

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.BalJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.BalJ9A
#print axioms balJ9A_frame
end Axioms
