/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BClosed.lean

  Binders: those of `complJ8_closed`, minus `hclA`.

  * `complJ9B_balV`: J-9 B completeness at `BRun9` with the `balV` field carried as a hypothesis; every other
    `OpenJ9B` field is a theorem (`atomOK_B9`, `ComplJ9BBalGRun.balG_run9`);
  * `balV_B9`: `BalV9` from `ComplJ9BBalV.balV_run9` (binders `hpG hax hop5 h31 hwalkA`);
  * **`complJ9B_closed`**: J-9 B general completeness at Goldilocks, nothing carried.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalGRun
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf mbCountsP bigIdOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (tripOf)

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf

noncomputable section

/-! ## The generator correspondence of the atom table's inputs -/

section GenData
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9A`'s atom-table inputs are the run's data** (Goldilocks, a jet-free run, as `genJ9A` requires): the
executor `runX` returns the generated tree's rows (`rowsOfT t`), and the cell list `cs`, the atom cell list `acsL`
(and so `GenJ9.mbCounts9 acsL cs c`, `j9_mb_eq` / `mbCountsP9_gen`) that `genJ9A` builds from them are
`j8DataOf`'s `cells` and `acs`. -/
theorem genJ9A_data (hpG : p = Nock.V1J8.Gen.P) (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = []) :
    Nock.V1J8.Gen.runX Rg.R fuel s f = some ⟨t, r, bfsForest [t], ComplJ8Data.rowsOfT t⟩ ∧
    Nock.V1J8.Gen.cellsOfRoots (Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t)) =
      (j8DataOf p Rg Rt hgen).cells ∧
    Nock.V1J8.Gen.acsOfD (Nock.V1J8.Gen.bigsOf (Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t))
        (ComplJ8Data.rowsOfT t))
        ((Nock.V1J8.Gen.incOps (ComplJ8Data.rowsOfT t)).any fun x => x.1 + 1 = Nock.V1J8.Gen.P) =
      (j8DataOf p Rg Rt hgen).acs := by
  subst hpG
  have hjn : ComplJ8Data.jNounsP Nock.V1J8.Gen.P Rt
      ((Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst).dedup
      (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)) = [] := by
    rw [hnc]; rfl
  refine ⟨by simp [Nock.V1J8.Gen.runX, hgen, ComplJ8Data.rowsOfT], ?_, ?_⟩
  · show _ = Nock.V1J8.Gen.cellsOfRoots (Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP _ Rt _ _)
    rw [hjn, List.append_nil]
  · show _ = ComplJ8Data.acsP _ (ComplJ8Data.bigsP _ (Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP _ Rt _ _) _) _
    rw [hjn, List.append_nil]
    rfl

end GenData

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))


local notation "DD" => j8DataOf p Rg Rt hgen

/-- The `balV` field of `OpenJ9B` at `BRun9`. -/
def BalV9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) : Prop :=
  ∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
    ((ClaimJ9.claimRecsJ9 δ χ (cJ s f r) ((BRun9 δ b Rt hgen hpG h31).M χ).m ++ AcceptsJ8P.pinRecsJ8 δ (BRun9 δ b Rt hgen hpG h31).Pb χ).map fun x =>
        (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsC 0) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMB) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA CellHQ.pubHQ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubC) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubXQ) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA 0 = 0 ∧ ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA 1 = 0)

open Classical in
/-- **J-9 B completeness at `BRun9`, `balV` carried**.  For every generated run `hgen` of every program
over every verified registry whose called jets are registered in compiled form (`hRt`, `hregAx`), under the run
binders `hax hop5`, the leaf binder `hleaf`, the walk-depth binders `hwalk hwalkA`, the row binder `h31`
(no claim-leaf binder: the claim may carry big atoms): at the
J-9 B honest record `BRun9`, honest acceptance by `AcceptsJ9V` at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the
claim holds, and at `|K| = cK` the figure `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9B_balV (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (DD))
    (hbalV : BalV9 δ b Rt hgen hpG h31) :
    let B := BRun9 δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ9B_run9 δ b Rt hgen hpG h31 hax hop5 hleaf hwalk hwalkA hRt
    { atomOK := atomOK_B9 δ b Rt hgen hpG h31 hax hop5,
      balG := ComplJ9BBalGRun.balG_run9 δ b Rt hgen hpG hax hop5 hRt h31 hwalk hwalkA,
      balV := hbalV }

/-- **`balV` at `BRun9`**. -/
theorem balV_B9 (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t) (h31 : Rows31 (DD))
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) : BalV9 δ b Rt hgen hpG h31 :=
  fun χ _ => ComplJ9BBalV.balV_run9 δ b Rt hgen hpG hax hop5 h31 hwalkA χ

open Classical in
/-- **`complJ9B_closed`: J-9 B general completeness at Goldilocks, nothing carried.**  For every generated run
`hgen` of every program over every verified registry `Rg` whose called jets are registered in compiled form (`hRt`,
`hregAx`), under the run binders `hax hop5`, the leaf binder `hleaf`, the walk-depth binders `hwalk` (reads) and
`hwalkA` (atom reads) and every table `≤ 2^31` rows (`h31`); no inc-corner binder
(no claim-leaf binder: the claim's subject, formula and result may hold big atoms): at the run's J-9 B honest
record `BRun9`, honest acceptance by `AcceptsJ9V` at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the claim holds,
and at `|K| = cK` the figure `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9B_closed (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (DD)) :
    let B := BRun9 δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) :=
  complJ9B_balV δ b Rt hgen hpG hax hop5 hleaf hwalk hwalkA hRt hregAx h31
    (balV_B9 δ b Rt hgen hpG hax hop5 h31 hwalkA)

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed
