/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8CompRun.lean

  **The `*_run` versions** of the compute lemmas of
  `ComplJ8Comp`, with `H`, `pd`, the BFS rows `W = bfsForest [t]` and the claim `cJ s f r` filled from
  `ComplJ8Data.j8DataOf p Rg Rt hgen`.  The generic lemmas stay in `ComplJ8Comp` / `ComplJ8CompPole`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompPole
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompRun

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
open Nock.NockVMROM.Thm54.SVFrame

noncomputable section

section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen

/-- The compute publics of the run's honest message. -/
abbrev pubRun (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  pubCOf δ b (DD).H (DD).pd (bfsForest [(DD).t]) (cJ s f r) χ

/-- The compute trace of the run. -/
abbrev trRun (χ : Coins frameJ8 K) {n : ℕ} (nodes : Fin n → ZMod p) : Fin 123 → (ZMod p)[X] :=
  trCOf δ b (DD).H (DD).pd (bfsForest [(DD).t]) (cJ s f r) χ nodes

/-- **`hH`** (L0's `hdlOK`). -/
theorem hH_run : HonestCompX.HdlOK (ringChar (ZMod p)) (DD).H :=
  ComplJ8Data.hdlOK p Rg Rt hgen

theorem hpub_run (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) (χ : Coins frameJ8 K) :
    pubRun δ b Rt hgen χ 0 = HonestCompX.hk (DD).H s ∧ pubRun δ b Rt hgen χ 1 = HonestCompX.hv (DD).H s ∧
    pubRun δ b Rt hgen χ 2 = HonestCompX.hk (DD).H f ∧ pubRun δ b Rt hgen χ 3 = HonestCompX.hv (DD).H f ∧
    pubRun δ b Rt hgen χ 4 = HonestCompX.hk (DD).H r ∧ pubRun δ b Rt hgen χ 5 = HonestCompX.hv (DD).H r := by
  have hH' : HonestCompX.HdlOK p (DD).H := by
    have := hH_run Rt hgen (p := p); rwa [ZMod.ringChar_zmod_n] at this
  exact hpub δ b (DD).pd _ hH' hcl χ

theorem hpS_run (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) (χ : Coins frameJ8 K) :
    limbVal b (pubRun δ b Rt hgen χ) ChipH.pubSeed =
      curW (F := ZMod p) (DD).H (bfsForest [(DD).t]) (InhabJ8Comp.γC0 b χ) 1 * InhabJ8Comp.αC0 b χ := by
  have hH' : HonestCompX.HdlOK p (DD).H := by
    have := hH_run Rt hgen (p := p); rwa [ZMod.ringChar_zmod_n] at this
  have hlab := genX_label hgen
  have hroot : tripOf (DD).t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, j8DataOf, hlab.1, hlab.2.1, hlab.2.2.1]
  exact hpS δ b (DD).pd _ hH' hcl rfl hroot χ

theorem hρ_run (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubRun δ b Rt hgen χ (pubOfA a + k) =
      coord b (accV b δ (DD).H (DD).pd (bfsForest [(DD).t]) (chalVJ8 b χ) (pubRun δ b Rt hgen χ) a
        (bfsForest [(DD).t]).length) k :=
  ComplJ8Comp.hρ δ b (DD).H (DD).pd _ (cJ s f r) χ

theorem hinjX_run {h n : ℕ} (hN : n = (bfsForest [(DD).t]).length) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (nodes : Fin n → ZMod p) (hn : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) (hle : n ≤ 2 ^ h) :
    Function.Injective nodes := hinjX_of orbit nodes hn hle

theorem hadjX_run {h n : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h) (nodes : Fin n → ZMod p)
    (hn : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) :
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω :=
  hadjX_of orbit nodes hn

theorem staged_trRun {n : ℕ} (nodes : Fin n → ZMod p) :
    StagedCols frameJ8 crC (fun χ => trRun δ b Rt hgen χ nodes) :=
  staged_trCOf δ b (DD).pd (bfsForest [(DD).t]) nodes

open Classical in
/-- **The compute chip at the run's data**: `computeChip_sat` with `H`, `pd`, `W`, the claim from `j8DataOf`;
`SmallX` from the binders `hax` / `hop5`; `hpair` (L3) and the good-coin events `hord`, `hnb` (L5) are taken. -/
theorem computeChip_sat_run
    (hax : ComplJ8.ProgAxOK p (DD).t) (hop5 : ComplJ8.ProgOp5OK p (DD).t) (hp16 : 16 ≤ p)
    (hpair : ∀ u, InTree (DD).t u → HonestCompX.isPair (DD).H (rowOfSkelX u.label) →
      HonestCompX.PairOK (F := ZMod p) ((DD).pd (rowOfSkelX u.label)))
    (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [(DD).t]).length) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 hh) (hnodes : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) (hle : n ≤ 2 ^ hh)
    (χ : Coins frameJ8 K)
    (hord : (bfsForest [(DD).t]).length ≤ orderOf (InhabJ8Comp.αC0 b χ))
    (hnb : ∀ j < n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      HonestSlotX.dVal b δ S (env0 (DD).H (DD).pd (bfsForest [(DD).t]) (chalVJ8 b χ) (pubRun δ b Rt hgen χ) j) ≠ 0 ∨
        HonestSlotX.aVal b δ S (env0 (DD).H (DD).pd (bfsForest [(DD).t]) (chalVJ8 b χ) (pubRun δ b Rt hgen χ) j) = 0) :
    RAP.SatisfiesWithPreprocessing
      (ChipHX.computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubRun δ b Rt hgen χ) orbit)
      (trRun δ b Rt hgen χ nodes) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hsm : ∀ u, InTree (DD).t u → HonestRowX.SmallX (ringChar (ZMod p)) (rowOfSkelX u.label) := by
    rw [hrc]; exact ComplJ8.smallX_of_binders hax hop5
  exact computeChip_sat δ b (DD).hgen (DD).H (DD).pd (hH_run Rt hgen) (by rw [hrc]; exact hp16) hsm hpair hcl hn hN
    nodes orbit hnodes hle χ hord hnb

end Run
end
end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompRun
