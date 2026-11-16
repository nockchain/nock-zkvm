/-
  Nock/NockVMROM/Thm54/VclL/Handle/BalSJ8.lean

  **The P7x / P7s glue — `BalJ8` at `frameJ8`'s
  verifier data with the `s` side discharged.**  New module, additive.

  `VerJ8.balJ8_frameJ8` (P7x) took the `s` terminals `TprovS / TextS`, their two telescope identities and the
  verifier's `s` equation `ρ_s + TextS = TprovS` as named hypotheses.
  * `TextS := Σ (ext.s)`, `TprovS := Σ (provs.s)` at `coinsCV (chalVJ8 b χ)`, so `hS_prov / hS_ext` are `rfl`;
  * the `s` equation is `ServiceJ8.balS_of_goodS'` at `provs.s = jProv ++ (pad8 inc ++ pad8 aw)`,
    `ext.s = jCons`, after `rhoX_s_J8` (`ρ_s = ρS`);
  * its coin premises are `coinsJ_J8` (the J chip at `chalsJJ8 χ`) and `acoins_of_agree` / `mcoins_of_agree`
    (the atom table and the atom walk agree with `chalsMJ8 χ` at the handle leaves `33..36`, like `hchC / hchW`);
  * the verifier's `s` check is `GoodS` on the publics only: `ρS + (pubJ₀, pubJ₁) = (pubA₈, pubA₉) + (pubV₆, pubV₇)`
    (`goodS_frameJ8_iff`).

  Main theorem: **`balJ8_frameJ8S`** — `BalJ8` at `(chalVJ8 b χ, pubVJ8 …)` from the four public equations
  (`hGx`, `hGp`, `hGS`) and the five accepted memory-side traces (cell, walk, J, atom table, atom walk).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BalSJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 rhoX)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (GoodS pad8 atomIncProvs balS_of_goodS')
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)

noncomputable section

section Frame
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom table's handle coins at any vector agreeing with `chalsMJ8` at the leaves `33..36`. -/
theorem acoins_of_agree (χ : Coins frameJ8 K) (chals : ℕ → K)
    (h : ∀ j, 33 ≤ j → j ≤ 36 → chals j = chalsMJ8 δ χ j) :
    AtomServedQ.acoins δ chals = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) :=
  mcoins_of_agree δ χ chals h

/-- **The verifier's `s` check at `frameJ8`**: `GoodS` at `pubVJ8` is `ρS + (pubJ₀, pubJ₁) = (pubA₈, pubA₉) +
(pubV₆, pubV₇)`. -/
theorem goodS_frameJ8_iff (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    (pubsJ pubsA pubsV : ℕ → K) :
    GoodS (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) (pubsJ := pubsJ) (pubsA := pubsA)
        (pubsW := pubsV) ↔
      ρS + Quad.mk _ (pubsJ 0) (pubsJ 1) =
        Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
          Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)) := by
  unfold GoodS
  rw [rhoX_s_J8]

/-- **`BalJ8` at `frameJ8`'s verifier data, the `s` side discharged** (the P7x / P7s glue).  The verifier's four
public equations `hGx` (x), `hGp` (p), `hGS` (s) and the five accepted memory-side traces — the cell table
`cellChipHQKW`, the J-8 walk `walkChipJ8`, the J chip `jetChipJ8` at `chalsJJ8 χ`, the atom table `atomChipHQ`, the
atom walk `walkChipHQK` — each memory vector agreeing with `chalsMJ8 χ` at the handle leaves `33..36`, give the
J-8 balance identity at `provs.x = cellProvsW`, `ext.x = walkXReqs ++ jRd`, `provs.p = walkPProvs`, `ext.p = []`,
`provs.s = jProv ++ (pad8 atomIncProvs ++ pad8 walkPProvs_A)`, `ext.s = jCons`. -/
theorem balJ8_frameJ8S (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hchA : ∀ j, 33 ≤ j → j ≤ 36 → chalsA j = chalsMJ8 δ χ j)
    -- the atom walk
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hchV : ∀ j, 33 ≤ j → j ≤ 36 → chalsV j = chalsMJ8 δ χ j)
    -- the wiring
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++
        pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)))
    (hextS : ext .s = jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1))) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provs ext := by
  have hcv := coinsCV_J8 δ b χ
  have hS := balS_of_goodS' (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ)
    (provs := provs) (ext := ext) hprovS hextS ((goodS_frameJ8_iff χ c m ρ ρS pubsJ pubsA pubsV).2 hGS)
    ((coinsJ_J8 δ χ).trans hcv.symm) ((acoins_of_agree χ chalsA hchA).trans hcv.symm)
    ((mcoins_of_agree δ χ chalsV hchV).trans hcv.symm)
    hsatJ hbindJ hinjJ hnJ hadjJ hsatA hbindA hinjA hadjA hsatV hbindV hinjV hadjV
  rw [rhoX_s_J8] at hS
  exact balJ8_frameJ8 χ c m ρ ρS hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC
    kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW
    nodesJ orbitJ pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ hprovX hextX hprovP hextP _ _ rfl rfl hGx hGp hS

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.BalSJ8
