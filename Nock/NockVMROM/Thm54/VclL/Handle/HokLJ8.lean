/-
  Nock/NockVMROM/Thm54/VclL/Handle/HokLJ8.lean

  **Card J-8a R4b : `hok` at the variant chip, and the `CorJ8I` twin with `hok`
  derived.**  New module, additive.

  * **`hok_of_gatesL`**: on an `atomChipHQL`-accepted trace (read as `toHQ`), under `Reads`, `SmallU`, the serials,
    no inc past the table, `LimbsBounded`, boolean `wR` and the served export consume `ConsumeServedQ`, EVERY inc row
    satisfies `ChainOK`.  At a row below the last: `chainOK_of_gatesU` with the next row read through the
    adjacency.  At the LAST row: the ruled gate `isL · c_out = 0` (`AtomChipHQL.cout_last`) gives `c_out = 0`, so
    the next-row relations are vacuous (R3b's finding: without the gate `hok` is not derivable there).  The
    old copy's limb `l_o < B` comes from `OldGenuine` (`oldGenuine_of_servedU`) and g1.
  * **`hok_valReader`**: the same at the canonical reader `LinkQ2J8.valReader` (`hRA`, `hrn`, `hwRA`, `hidxA`,
    `hB`, `SmallU` all discharged: Q2 / R3b), from `nA ≤ 2^62`, `ValidityServed`, `ConsumeServedQ`.
  * **`acceptsJ8_holdsN_finalL`**: `CorJ8I.acceptsJ8_holdsN_final'` at the VARIANT atom chip (`QA = toHQ QL`,
    `QL` accepted by `atomChipHQL`), with `hsA` restated as `SmallU` and **`hok` dropped** (derived inside from
    the export balance `hbalA houtA hcountA` through `consumeServedQ_of_balance` and `hok_of_gatesL`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CorJ8IU
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HokLJ8

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_entry7 atomIncProvs provP_append)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.Atoms (val)

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8 (axOK_x axOK_s)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8A (acceptsJ8_holdsN')
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (hAW_of_atomWalk' AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA hDen_extA hD0_denK hchain_of_served)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB denOKX_extB hDenB_extB atomInc_provOKB hAW_extB)
open Nock.Jet.ChipJ8 (provK Accepted)
open Nock.Jet.PinJ8 (pinKey pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (hReg_of_pinR denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (RecOKI atomInc_provOKI hAW_extBI hDenB'_extB)

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.ChainUJ8 (hchain_of_servedU atomInc_provOKIU agree_atomU chainOK_of_gatesU
  oldGenuine_of_servedU)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU smallU_valReader hidxA_valReader hB_valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ atomChipHQL_sat atomChipHQL_bind cout_last)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ReadsNext ChainOK LimbsBounded ConsumeServedQ)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (consumeServedQ_of_balance)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader hRA_valReader hrn_valReader hwRA_valReader)
open Nock.Atoms (B)

/-! ## 1. `hok` at the variant chip -/

section Hok
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}

/-- **`hok` from the gates at the variant chip** (every inc row, the last one included). -/
theorem hok_of_gatesL (hq : 2 ^ 63 < p)
    {QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}
    (hsat : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbind : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    {rA : ℕ → ARow}
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA
      (toHQ δ b hnA nodesA orbitA chalsA pubsA QL) k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (hcs : ConsumeServedQ (AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA
      (toHQ δ b hnA nodesA orbitA chalsA pubsA QL)) nA) :
    ∀ j, (rA j).inc = 1 → ChainOK rA j := by
  set QA := toHQ δ b hnA nodesA orbitA chalsA pubsA QL with hQA
  have hsatA := atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsat
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have env_lt : ∀ i : Fin nA, AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA i =
      AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA i := AtomServedQ.atomEnvN_lt b hnA nodesA orbitA chalsA pubsA QA
  intro j hinc
  have hj : j < nA := by
    by_contra h
    have := hrn j (by omega)
    omega
  have hgen := oldGenuine_of_servedU hq' (env := AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA)
    (n := nA) (r := rA)
    (fun k hk => by rw [show k = ((⟨k, hk⟩ : Fin nA) : ℕ) from rfl, env_lt]; exact hRA ⟨k, hk⟩)
    (fun k hk => by rw [show k = ((⟨k, hk⟩ : Fin nA) : ℕ) from rfl, env_lt]; exact (AtomCombJ8.atom_g23 hsatA ⟨k, hk⟩).1)
    (fun k _ => hwRA k) (fun k hk => hsA ⟨k, hk⟩) (fun k hk => hidxA ⟨k, hk⟩) hcs j hj hinc
  have hlO : (rA j).lO < B := by rw [← hgen.1]; exact (hB _).1
  have hnext : (rA j).cout = 1 → j + 1 < nA := by
    intro h1
    by_contra hlt
    have h0 := cout_last δ b hnA nodesA orbitA chalsA pubsA QL hsat hbind hinj ⟨j, hj⟩ (by simp; omega)
    rw [(hRA ⟨j, hj⟩).cout] at h0
    have h1' : (rA j).cout = 1 := h1
    simp [h1'] at h0
  refine chainOK_of_gatesU hq' (e := AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA ⟨j, hj⟩)
    (fun g hg => AtomServedQ.atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsatA ⟨j, hj⟩ g
      (List.mem_append_right _ hg))
    (hRA ⟨j, hj⟩) (fun h1 => ?_) (hsA ⟨j, hj⟩) (fun h1 => hsA ⟨j + 1, hnext h1⟩) (hidxA ⟨j, hj⟩) (hwRA j) hinc
    ⟨(hB j).1, hlO⟩
  have hj1 := hnext h1
  have Rn := hRA ⟨j + 1, hj1⟩
  have nx := fun c => AtomServedQ.aEF_next δ b hnA nodesA orbitA chalsA pubsA QA hadj ⟨j, hj⟩ hj1 c
  exact ⟨by rw [nx]; exact Rn.idxO, by rw [nx]; exact Rn.inc, by rw [nx]; exact Rn.aL, by rw [nx]; exact Rn.wR,
    by rw [nx]; exact Rn.aR⟩

end Hok

section Reader
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}

/-- **`hok` at the canonical reader** of a variant-accepted trace: every reader field discharged (Q2, R3b). -/
theorem hok_valReader (hq : 2 ^ 63 < p) (hn62 : nA ≤ 2 ^ 62)
    {QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}
    (hsat : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbind : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hserved : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA (toHQ δ b hnA nodesA orbitA chalsA pubsA QL))))
    (hcs : ConsumeServedQ (AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA
      (toHQ δ b hnA nodesA orbitA chalsA pubsA QL)) nA) :
    ∀ j, (valReader (AtomServedQ.aEF b nodesA orbitA chalsA pubsA (toHQ δ b hnA nodesA orbitA chalsA pubsA QL)) j).inc = 1 →
      ChainOK (valReader (AtomServedQ.aEF b nodesA orbitA chalsA pubsA (toHQ δ b hnA nodesA orbitA chalsA pubsA QL))) j := by
  have hsatA := atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsat
  have hbindA := atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbind
  have hnp : nA < p := by omega
  exact hok_of_gatesL hq hsat hbind hinj hadj (hRA_valReader _)
    (smallU_valReader (by omega) hn62 hsatA hbindA hinj hadj hserved hcs)
    (hidxA_valReader hsatA hbindA hinj hadj hnp) (hrn_valReader _) (hB_valReader (by omega) hsatA)
    (hwRA_valReader _ fun k => LinkQ2J8.atom_wR_bool hsatA k) hcs

end Reader

/-! ## 2. The corollary at the variant chip, `hok` derived -/

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`acceptsJ8_holdsN_finalL`**: `CorJ8I.acceptsJ8_holdsN_final'` at the variant atom chip `atomChipHQL` (`QA = toHQ
QL`), with `hsA` restated as `SmallU` and WITHOUT `hok` (derived: `hok_of_gatesL`, `ConsumeServedQ` from the export
balance).  Every other hypothesis and the conclusion are the original's. -/
theorem acceptsJ8_holdsN_finalL [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    -- the compute trace
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
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
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
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
    -- the wiring (the pins are `s` consumes)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++
        pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + ((pinCons (p := p) (K := K) regs idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)))
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hpG : p = Nock.Atoms.p)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- the atom walk
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)))
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)
        (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
      (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K)
      (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
        (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r))) n)
    (hreal : (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)).isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j := by
    have hcs := consumeServedQ_of_balance δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA wreqs
      hbalA houtA hcountA
    subst hQA
    exact hok_of_gatesL (by omega) hsatL hbindL hinjA hadjA hRA hsA hidxA hrn hB hwRA hcs
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq : 2 ^ 63 < p := by omega
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have hp2 : 2 < p := by omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  set tC := (cellTableOf δ b nodesC orbitC chalsC pubsC
    (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0) with htC
  -- the cell table: two-provider acceptance, `x` / `p` providers
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b hnC nodesC orbitC chalsC pubsC QC hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b hnC nodesC orbitC chalsC pubsC QC hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b hnC nodesC orbitC chalsC pubsC _ hF' hq' hzC hsatC0 hbindC0
    hinjC hadjC hnpC γV ρV hokC reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0
  have htbC : (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length ≤ ringChar (ZMod p) := by
    simp only [cellTableOf, List.length_ofFn]; exact hnpC.le
  have hX := provPA_of_provOK (comb := combN) (limbA := fun _ _ => (0, 0)) (by decide)
    (ProvXJ8.provOK_x δ b hnC nodesC orbitC chalsC pubsC hp2 hq' hzC QC hsatC hbindC hinjC hadjC hnpC γV ρV hokC
      reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0 E hconsE hE (extB p rA) hvp Rg (fun _ _ => (0, 0)))
  have hP := provPA_of_provOK (comb := combN) (limbA := fun _ _ => (0, 0)) (by decide)
    (WalkKJ8.provOK_p δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW hkW hknW hkpW hq'
      hconsE hE htabC hvp hEinj htbC hXW hHXW houtW Rg (fun _ _ => (0, 0)))
  have hPax := WalkKJ8.provAx_p δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW hkW hknW
    hkpW hq' houtW
  -- the registry: `hclaim` from the cell side, `hReg` from the pin
  have hvpr : ∀ k ∈ vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hclaim := Nock.Jet.PinJ8.regClaims_provided δ b hnC nodesC orbitC chalsC pubsC
    (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC) hF' hsatC0 hbindC0 hinjC hadjC γV ρV hokC
    reqsC xsC hsumC houtC hxneC hcountC vp hxC hvpr (Ef := fun id => E (Nock.Jet.Autogen.compile p (Rt id)))
    hpinC hlt
  have hRegP := fun (hAcc : Accepted Rt regs ids (rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)) hpin =>
    hReg_of_pinR hrc hq hconsE hE htabC hvp hAcc hnd hidx hpin hclaim hrk hinjE
  -- the atom table: `hold`, `hchain`, the inc heads at `extB`
  have hwL : ∀ k : Fin nA, (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k).trace Cell.wL = 0 :=
    fun k => (atom_g23 hsatA k).1
  have hchain := hchain_of_servedU δ b hnA nodesA orbitA chalsA pubsA hq' QA hsatA hbindA hinjA hadjA wreqs hbalA
    houtA hcountA hRA hsA hidxA hwL hrn hB hwRA hok
  have hI : ProvP (p := p) (K := K) (RecOKI (denK tC (extB p rA)) Rg combN) .s
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)) :=
    atomInc_provOKIU (Rg := Rg) hq hsatA hRA hsA hidxA
      (hD0_denK tC (extB p rA)) (hDenB_extB tC p rA) (hDenB'_extB tC p rA) hchain hpG
  -- the atom walk at `extB`
  have hTA := AtomChipHQ.atomTable_accepts δ b hnA nodesA orbitA chalsA pubsA hF' hq' hzA QA hsatA hbindA hinjA
    hadjA (by rw [hrc]; exact hnpA) hservedA []
  have htab : TableAccepts (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) [] := by rw [hyV.1, hyV.2]; exact hTA
  have hzV : Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3) ≠ 0 := by rw [hyV.1, hyV.2]; exact hzA
  have hser := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsatA) hF'
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbindA) hinjA hadjA
    (by rw [hrc]; exact hnpA)
  have htb : (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).length ≤ ringChar (ZMod p) := by
    simp only [cellTableOf, List.length_ofFn]; rw [hrc]; exact hnpA.le
  have hag : ∀ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).map (·.b0), AgreeRow c (rA c.idx) :=
    fun c hc => (agree_atomU hq hsatA hRA hsA hidxA hB (fun k => hwRA k) c hc).2
  have hAW := hAW_extBI δ krootsV b hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hkV hknV
    hkpV hq' hzV htab hseedsV hXV hHXV houtV hser htb hag tC Rg
  exact FinalJ8I.acceptsJ8_holdsN_EI (comb := combN) (hD := denOKX_extB tC p rA) (hX := hX) (hP := hP)
    (hPax := hPax) (hRegP := hRegP) (hI := hI) (hAW := hAW)
    χ c m ρ ρS C hp hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC kroots hnW nodesW orbitW
    chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW nodesJ orbitJ pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ
    hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hchA krootsV hnV nodesV orbitV chalsV pubsV QV
    hsatV hbindV hinjV hadjV hchV hprovX hextX hprovP hextP hprovS hextS hGx hGp hGS hout houtS hcount hRg
    hlay hsmall huniq hTpl hseed hα hw hreal x hs hf he

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.HokLJ8
