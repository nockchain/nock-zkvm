/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptJ8.lean

  **`acceptsJ8_holdsN_compute`.**
  New module, additive.

  An accepted `computeChipVCLHX` trace (`RapWalkJ8.XCtx`: sat, injective `ω`-adjacent nodes, `17 < p`,
  the walk coins / publics as limb values), outside the compute walk events (`WalkTreeVSX.tileSet` at
  `α`, `cwEvent` at `(α, γ)`) and outside each handle-class balance's weighted IO failure event at the
  compute's `𝕂′` coins, under the J-8 balance identity `ServedJ8.BalJ8` (from `GoodCJ8` + the memory
  telescopes), with consumer counts `< p`, and with the memory providers' two obligations
  (`ProvOK` — every provided record is genuine; `ProvP AxOK` — every provided path record has its axis in
  `[2, 2^62)`), whose root row is a real row denoting the claim, proves `HoldsN` of the claim.

  The composition: `RapWalkJ8.cwalkX_of_sat` (the walk), `WalkTreeVSX.bfs_of_walk` / `tile_of_walk` /
  `goal_of_not_mem` (the forest goal), `RapWalkJ8.base_oh_of_sat` (`RowsAccX.base /.oh`),
  `ServedJ8.served_of_balancesJ8` (`RowsAccX.served`), `ServedJ8.ax_of_axOK` (`RowsAccX.ax`), then
  `WalkBridgeJ8.holdsN_of_walkJ8`.  `hden` is gone (`DenXJ8.hden_of_reqs`).

  `hprov` / `haxP` (per-kind provider lemmas),
  `hbal` (the memory telescopes + `GoodCJ8`), `hseed` (the seed public), the root-row claim binding
  `hs / hf / he` and `hreal`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8

open Nock Nock.Reified Nock.Edit Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (activeX RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

noncomputable section

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P
local notation "CV" => coinsCV b δ chalV

/-- The balance context of an accepted trace. -/
theorem bctx_of_xctx {α γ seed : K} (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) :
    BCtx hn nodes b δ chalV pubVal orbit P :=
  ⟨charX C, C.hsat, C.hinj, C.hadj⟩

/-- **The forest goal of the J-8 compute walk**, outside `tileSet` / `cwEvent`. -/
theorem goalJ8 {α γ seed : K} (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n) :
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) 1 n := by
  obtain ⟨ln, cnt, acc, hsat, hacc, hne, hterm⟩ := cwalkX_of_sat C hseed
  exact goal_of_not_mem _ (tile_of_walk hsat hterm hα) (bfs_of_walk hsat hne) ⟨ln, cnt, acc, hsat, hacc⟩ hw

/-- **An accepted J-8 compute trace proves `HoldsN` of the claim**, given
the memory side's balance identity and provider obligations (see the module docstring). -/
theorem acceptsJ8_holdsN_compute [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hR : R.Faithful) (hD : DenOKX p D)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (hprov : ∀ bl, ProvOK (p := p) (K := K) D R limbA bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX (EN 0)).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN 0) xS) = some x.subject) (hf : D (hdV (EN 0) xF) = some x.formula)
    (he : D (hdV (EN 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  have hp4 : 4 < p := by omega
  have B := bctx_of_xctx C
  have hOK := served_of_balancesJ8 B hp4 hbal hout hcount hprov
  have hAx := servedP_of_balancesJ8 B hp4 hbal hout hcount haxP
  obtain ⟨hbase, hoh⟩ := base_oh_of_sat C
  have A : RowsAccX n (fun r => EN r) (fun r => stX (EN r)) D R limbA :=
    { base := hbase
      oh := hoh
      served := hOK
      ax := fun r hr hst => by
        have h12 := hoh r hr
        rw [hst] at h12
        exact ax_of_axOK (hbase r hr) h12 (hAx r hr) }
  exact holdsN_of_walkJ8 (K := K) hp hR hD hn A (goalJ8 C hseed hα hw) hreal x hs hf he

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8
