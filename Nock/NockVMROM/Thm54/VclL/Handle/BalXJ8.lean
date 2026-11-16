/-
  Nock/NockVMROM/Thm54/VclL/Handle/BalXJ8.lean

  New module, additive.

  * **`ext_served`**: on an accepted `computeChipVCLHX` trace, under `BalJ8`, outside each balance's weighted IO
    failure event at the compute coins `CV = (γH′, ρH′)` and with consumer counts `< p`, every key of the OTHER
    consumers `ext bl` is a provider key of `bl` (the served lemma for the non-compute consumers; the
    `ServedJ8.servedP_of_balancesJ8` pattern, read on the `ext` half of `reqsJ8`).
  * **`extX_sumQ`**: the `x` consumers other than the compute, `ServeH.walkXReqs (walkChipJ8) ++ jRd (jetChipJ8)`,
    sum at a common coin pair `κ` (the walk's `mcoins` and the J chip's `coinsJX`, both `= κ`) to
    `(pubW₄, pubW₅) + (pubJ₂, pubJ₃)` — `T_ext.x` (`walkJ8_reqs_sumQ` + `RapJetJ8.jet_export_sum`).
  * **`provsX_sumQ`**: the `x` providers `cellProvsW (cellChipHQKW)` sum at `κ` (`= mcoins` of the cell chip) to
    `(pubC₄, pubC₅)` — `T_prov.x` (`cellW_provs_sumQ`).
  * `provsP_sumQ`: `T_prov.p` (`walkJ8_provs_sumQ`) at `κ`.
  * **`TprovJ8` / `TextJ8`** (the concrete terminals the memory chips publish) and **`balJ8_of_goodJ8`**: the
    verifier's check `GoodCJ8 (TprovJ8 …) (TextJ8 …)` gives `BalJ8` at the J-8 wiring (`provs.x = cellProvsW`,
    `ext.x = walkXReqs ++ jRd`, `provs.p = walkPProvs`, `ext.p = []`), with the three chips' coins identified
    with the compute's `CV` (`hκC`, `hκW`, `hκJ`, named) and the `s` telescopes named.
  * **`hRd_of_balX`**: with `ext.x = wX ++ jRd` and `ProvOK ….x (provs.x)`, JB's `hRd` (every `rp / sl /
    sr` row's record is genuine) — `RapJetJ8.rd_recOK` fed by `ext_served`.
  * **`hRd_of_cellX`**: the same with `provs.x = cellProvsW …` and the provider obligation discharged by
    `ProvXJ8.provOK_x` (its hypotheses passed through).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTeleJ8
import Nock.Jet.RapJetJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX compReqsX_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 reqsJ8 liftP ProvP ProvOK den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW cellW_provs_sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd rowsJ coinsJX)

noncomputable section

/-! ## 1. The served lemma for the other consumers -/

section Served
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **The other consumers are served**: on an accepted `computeChipVCLHX` trace, under the balance identity,
outside each balance's weighted IO failure event at the compute coins and with consumer counts `< p`, every key
of `ext bl` is a provider key of `bl`. -/
theorem ext_served [CharP 𝕂′ p] (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (bl : Bal) : ∀ c ∈ ext bl, c ∈ (provs bl).map Prod.fst := by
  have hd : ∀ bl, ∀ r ∈ reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, compress ⟨(CV).gamma, (CV).pole⟩ r ≠ 0 :=
    fun bl => TeleC.den_ne_of_out _ _ _ _ (hout bl)
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress CV (liftRec (L := 𝕂′) r) ≠ 0 :=
    fun bl r hr => hd bl _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (hd bl)
      (den_prov_ne_of_out _ _ _ _ (hout bl)) ?_ (hcount bl) (hout bl)
    have h1 := compReqsX_sum C hne bl
    have h2 := hbal bl
    unfold reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro c hc
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp
    (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

end Served

/-! ## 2. The `x` terminals: `T_ext.x` (walk + J reads) and `T_prov.x` (cell) -/

section Terminals
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`T_ext.x`**: the walk's export consumes and the J reads, at a common coin pair `κ` (the walk's handle
coins `mcoins` and the J export coins `coinsJX`, both `= κ`), sum to `(pubW₄, pubW₅) + (pubJ₂, pubJ₃)`. -/
theorem extX_sumQ (κ : IOCoins 𝕂′)
    -- the walk chip (instance 1)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hκW : mcoins δ chalsW = κ)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    (hκJ : coinsJX δ chalsJ = κ) :
    ((ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ).map
        fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3) := by
  rw [List.map_append, List.sum_append]
  congr 1
  · rw [← hκW]
    exact WalkTeleJ8.walkJ8_reqs_sumQ δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
  · rw [← hκJ]
    exact Nock.Jet.RapJetJ8.jet_export_sum hsatJ hbindJ hinjJ hnJ hadjJ

/-- **`T_prov.x`**: the cell export providers `cellProvsW` of an accepted `cellChipHQKW` trace, weighted by `mh`,
sum at `κ` (`= mcoins` of the cell chip) to `(pubC₄, pubC₅)`. -/
theorem provsX_sumQ (κ : IOCoins 𝕂′)
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hκC : mcoins δ chalsC = κ) :
    ((cellProvsW b nodesC orbitC chalsC pubsC QC).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)) := by
  rw [← hκC]
  exact cellW_provs_sumQ δ b hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC

/-- **`T_prov.p`** at `κ` (`= mcoins` of the walk chip): `walkJ8_provs_sumQ`. -/
theorem provsP_sumQ (κ : IOCoins 𝕂′)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hκW : mcoins δ chalsW = κ) :
    ((ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)) := by
  rw [← hκW]
  exact WalkTeleJ8.walkJ8_provs_sumQ δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW

end Terminals

/-! ## 3. The verifier's check on the concrete terminals, and JB's `hRd` -/

section Assembly
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **The providers' terminals `T_prov`** the memory chips publish: `x` = the cell table's `(pubC₄, pubC₅)`, `p` =
the walk's `(pubW₆, pubW₇)`, `s` = the service terminal `TprovS`. -/
def TprovJ8 (pubsC pubsW : ℕ → K) (TprovS : 𝕂′) : Bal → 𝕂′
  | .x => Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1))
  | .p => Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1))
  | .s => TprovS

/-- **The other consumers' terminals `T_ext`**: `x` = the walk's `(pubW₄, pubW₅)` plus the J reads' `(pubJ₂, pubJ₃)`,
`p` = `0` (no other consumer), `s` = `TextS`. -/
def TextJ8 (pubsW pubsJ : ℕ → K) (TextS : 𝕂′) : Bal → 𝕂′
  | .x => Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)
  | .p => 0
  | .s => TextS

/-- **JB's `hRd` from the `x` balance**: on an accepted compute trace under `BalJ8`, outside the IO events at the
compute coins with counts `< p`, if the J reads are among the `x` consumers (`ext.x = walkXReqs ++ jRd`) and the
`x` providers satisfy `ProvOK`, every `rp / sl / sr` row's record `(h_N.v, h_L, h_R)` is genuine. -/
theorem hRd_of_balX [CharP 𝕂′ p] (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p} {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ} {chalsJ pubsJ : ℕ → K}
    {lay : Fin nJ → PRow} {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}
    (wX : List (Fin 5 → K))
    (hextX : ext .x = wX ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hprovX : ProvOK (p := p) (K := K) D Rg limbA .x (provs .x)) :
    ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x) :=
  Nock.Jet.RapJetJ8.rd_recOK (provs .x) hprovX fun c hc =>
    ext_served C hbal hout hcount .x c (by rw [hextX]; exact List.mem_append_right _ hc)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

theorem balJ8_of_goodJ8
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hκC : mcoins δ chalsC = CV)
    -- the walk chip
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hκW : mcoins δ chalsW = CV)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    (hκJ : coinsJX δ chalsJ = CV)
    -- the wiring
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    -- the service balance
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      TprovS)
    (hS_ext : ((ext .s).map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    -- the verifier's check
    (hG : ServedJ8.GoodCJ8 (b := b) (δ := δ) (pubVal := pubVal) (TprovJ8 pubsC pubsW TprovS)
      (TextJ8 pubsW pubsJ TextS)) :
    BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext := by
  refine ServedJ8.balJ8_of_good hG ?_ ?_
  · intro bl
    cases bl with
    | x =>
      rw [hextX]
      exact extX_sumQ δ b CV kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hκW
        nodesJ orbitJ chalsJ pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ hκJ
    | p => rw [hextP]; rfl
    | s => exact hS_ext
  · intro bl
    cases bl with
    | x =>
      rw [hprovX]
      exact provsX_sumQ δ b CV hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hκC
    | p =>
      rw [hprovP]
      exact provsP_sumQ δ b CV kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hκW
    | s => exact hS_prov

end Assembly


/-! ## 4. `hRd` with the cell export providers' obligation discharged by `provOK_x` -/

section CellX
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
open Nock.ComputeTable (FP)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))] [Fact (ringChar (ZMod p)).Prime]
  [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **JB's `hRd`, discharged** at the J-8 wiring `provs.x = cellProvsW`, `ext.x = walkXReqs ++ jRd`: the `x`
providers' obligation is `ProvXJ8.provOK_x` (under its hypotheses: the cell table's two-provider validity balance
outside its IO event, the atom-root external keys, `AtomLeaves`, the encoder facts), the served step is
`ext_served`, the record step `RapJetJ8.rd_recOK`.  The denotation is `denK tb extA` of the accepted cell table. -/
theorem hRd_of_cellX [CharP 𝕂′ p] (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    -- the J chip and the wiring of `x`
    {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p} {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ} {chalsJ pubsJ : ℕ → K}
    {lay : Fin nJ → PRow} {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}
    (wX : List (Fin 5 → K))
    (hextX : ext .x = wX ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    -- the cell table (`provOK_x`'s hypotheses)
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (hp2 : 2 < p) (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hnp : nC < ringChar (ZMod p))
    (γ ρ : 𝕂′) (hok : ChalsOK δ chalsC γ ρ 11)
    (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (houtC : (γ, ρ) ∉ FiniteIO.IOFailureEventW
      (reqs ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC (restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcountC : (reqs ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hcons : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    (extA : ℕ → Option Noun) (hvp : AtomLeaves E vp extA)
    (Rg : Nock.Jet.Registry) (limbA : ℕ → ℕ → ℕ × ℕ)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC) :
    ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK (denK ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) extA) Rg limbA
        ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x) := by
  have hpx := ProvXJ8.provOK_x δ b hnC nodesC orbitC chalsC pubsC hp2 hq hz QC hsatC hbindC hinjC hadjC hnp γ ρ hok
    reqs xs hsum houtC hxne hcountC vp hx hvp0 E hcons hE extA hvp Rg limbA
  rw [← hprovX] at hpx
  exact hRd_of_balX C hbal hout hcount wX hextX hpx

end CellX

end

end Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8
