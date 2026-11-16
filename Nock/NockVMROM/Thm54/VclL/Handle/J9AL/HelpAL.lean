/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/HelpAL.lean

  **Two twins for the J-9 AL core.**
  * `hHXW9AL`: `ServedXJ9A.hHXW9` with `ext .x = (walkXReqs ++ wA) ++ jRd` (the ALU export reads `wA` in the middle).
  * `served_JALG`: `ServeAL.served_JAL` with the J chip present OR absent (`JGenJ8.JChipOK`, through
    `jet_tagged_sumG`), so the ALU's service consumes are served whether or not a J chip is present.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ServedXJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ServeAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HelpAL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (compReqsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP BalJ8 den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd jProv jCons coinsJ)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedXJ9A (ext_served9)

noncomputable section

section HXW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **`hHXW9` with the ALU export reads** in the middle of `ext .x`. -/
theorem hHXW9AL [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0)
    (hout : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext .x) (liftP (provs .x)))
    (hcount : (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext .x).length < p)
    (hp2 : 2 < p)
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow) (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (wA : List (Fin 5 → K))
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = (ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ wA) ++
      jRd b nodesJ orbitJ chalsJ pubsJ lay PJ) :
    ∀ j < nW, ∃ c' ∈ cellTableOf δ b nodesC orbitC chalsC pubsC (restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c'.b0 := by
  have hs := ext_served9 C hbal hne .x hout hcount
  refine LinkJ8Q1H.hHXW_of_served δ b hnC nodesC orbitC chalsC pubsC kroots hnW nodesW orbitW chalsW pubsW hp2
    QC hsatC QW fun j => ?_
  have hc : ServeH.keyVec5 (K := K) WalkHC.xKeyH (wEF b nodesW orbitW chalsW pubsW QW j) ∈ ext .x := by
    rw [hextX]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange j)))
  have := hs _ hc
  rwa [hprovX] at this

end HXW

section Eff
open Nock.Jet Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8 Nock.Jet.RegJ8R Nock.Jet.PinJ8 Nock.Jet.FibreJ8 Nock.Jet.SubJ8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "JP" => jProv b nodes orbit chals pubs lay P

/-- **`ServeAL.served_JAL` with the J chip present or absent.** -/
theorem served_JALG [CharP 𝕂′ p] (hJk : JGenJ8.JChipOK δ b nodes orbit chals pubs lay P)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ c ∈ reqO, c ∈ (JP ++ provO).map Prod.fst := by
  set reqs := (reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)) with hreqs
  set provs := liftS (δ := δ) (JP ++ provO) with hprovs
  have hts := JGenJ8.jet_tagged_sumG hJk
  have hsum : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    simp only [hreqs, hprovs, liftS, List.map_map, Function.comp_def, List.map_append, List.sum_append]
    have e1 := hts
    change (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum +
        ((jCons b nodes orbit chals pubs lay P).map fun c =>
          (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      ((jProv b nodes orbit chals pubs lay P).map fun q =>
          algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum +
        (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum
    rw [e1]
    linear_combination hG
  have hout' := hout
  rw [mem_IOFailureEventW_iff] at hout'
  push Not at hout'
  have hserved : ∀ r ∈ reqs, r ∈ provs.map Prod.fst := by
    intro r hr
    have := served_effective (p := p) reqs provs ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩
      (TeleC.den_ne_of_out reqs (effP provs) _ _ hout) (ServedJ8.den_prov_ne_of_out reqs (effP provs) _ _ hout)
      hsum (by simpa [hreqs] using hcount) hout'.1 hout'.2.2 r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
    exact List.mem_map_of_mem (List.mem_of_mem_filter hq)
  intro c hc
  have hmem : liftRec (L := 𝕂′) c ∈ reqs := List.mem_map_of_mem (List.mem_append_left _ hc)
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  rw [hprovs, liftS] at hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

end Eff

end

end Nock.NockVMROM.Thm54.VclL.Handle.HelpAL
