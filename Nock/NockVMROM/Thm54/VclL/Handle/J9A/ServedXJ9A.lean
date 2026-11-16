/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ServedXJ9A.lean

  J-8 derives `hHXW` from `walkX_servedZG9`, which reads the J-8 compute chip (`AcceptsJ9ZG`);
  here the same served argument runs over the twin `computeChipVCLHX9` (`BCtx9`, `compReqsX9_sum`):
  * `served9` — under the balance identity at a balance `bl`, outside its IO event, every request (compute or
    external) is a provider key;
  * `ext_served9` — every external consume of `bl` is a provider key (unlifted);
  * **`hHXW9`** — with the `.x` wiring of S8 (`provs .x = cellProvsW`, `ext .x = walkXReqs ++ jRd`), every J-8 walk
    row's export record is a row of the decoded cell table (`LinkJ8Q1H.hHXW_of_served`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServedXJ9A

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
open Nock.Jet.RapJetJ8 (jRd)

noncomputable section

section Served
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **Served at one balance**: every request of `bl` (compute or external) is a provider key. -/
theorem served9 [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0)
    (bl : Bal)
    (hout : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p) :
    ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
  refine ServeH.served_of_balance (p := p) _ _ _ _ (TeleC.den_ne_of_out _ _ _ _ hout)
    (den_prov_ne_of_out _ _ _ _ hout) ?_ hcount hout
  have h1 := compReqsX9_sum C hne bl
  have h2 := hbal bl
  unfold reqsJ9 liftP
  rw [List.map_map, List.map_append, List.sum_append, List.map_map]
  simp only [Function.comp_def] at h1 ⊢
  rw [h1]
  exact h2

/-- Every external consume of `bl` is (unlifted) a provider key. -/
theorem ext_served9 [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0)
    (bl : Bal)
    (hout : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p) :
    ∀ c ∈ ext bl, c ∈ (provs bl).map Prod.fst := by
  intro c hc
  have hs := served9 C hbal hne bl hout hcount _
    (List.mem_map_of_mem (List.mem_append_right _ hc))
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hs
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

end Served

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

/-- **`hHXW` over the twin compute**: with the S8 `.x` wiring, every J-8 walk row's export record is a row of the
decoded cell table. -/
theorem hHXW9 [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
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
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ) :
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
    exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange j))
  have := hs _ hc
  rwa [hprovX] at this

end HXW

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServedXJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ServedXJ9A
#print axioms served9
#print axioms ext_served9
#print axioms hHXW9
end Axioms
