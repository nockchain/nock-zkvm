/-
  Nock/NockVMROM/Thm54/VclL/Handle/JGenJ8.lean

  * **`JChipOK`**: the verifier's J-chip block — either the J chip is PRESENT (the five conjuncts `AcceptsJ8''`
    carried: `Satisfies`, `BindsPreprocessing`, injective nodes, `0 < nJ`, adjacent nodes), or it is ABSENT:
    `nJ = 0` and the four J publics read by the verifier's equations are `0` (`pubsJ 0..3 = 0`).
  * With `nJ = 0` every J list is empty (`rowsJ_nil`, `jCons_nil`, `jProv_nil`, `jRd_nil`, `jProvE_nil`).
  * **`jet_export_sumG`** / **`jet_tagged_sumG`**: the two J telescopes the soundness chain consumes, under
    `JChipOK` (present: `RapJetJ8.jet_export_sum` / `jet_tagged_sum`; absent: both sides are `0`).
  * **`extX_sumQG`**, **`balJ8_of_goodJ8G`**, **`balJ8_frameJ8G`**: `BalXJ8.extX_sumQ`, `BalXJ8.balJ8_of_goodJ8`,
    `VerJ8.balJ8_frameJ8` with the J chip's five hypotheses replaced by `JChipOK`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
import Nock.Jet.SubJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BalXJ8 (TprovJ8 TextJ8 provsX_sumQ provsP_sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.Jet.ChipJ8 (jetChipJ8 PRow)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ coinsJ coinsJX)

noncomputable section

/-! ## 1. The block and the empty lists -/

section Def
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K)

/-- **The J chip, present or absent.**  Present: the five conjuncts of `AcceptsJ8''` (`hsatJ hbindJ hinjJ hnJ
hadjJ`).  Absent: no J row (`nJ = 0`) and the J publics the verifier's equations read are `0`. -/
def JChipOK {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ)
    (chalsJ pubsJ : ℕ → K) (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]) : Prop :=
  ((jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ ∧
      (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ ∧ Function.Injective nodesJ ∧
      0 < nJ ∧ ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω) ∨
    (nJ = 0 ∧ pubsJ 0 = 0 ∧ pubsJ 1 = 0 ∧ pubsJ 2 = 0 ∧ pubsJ 3 = 0)

variable {δ b} {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p} {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ}
  {chalsJ pubsJ : ℕ → K} {lay : Fin nJ → PRow}
  {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}

theorem finRange_nil (h0 : nJ = 0) : List.finRange nJ = [] :=
  List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, h0])

theorem rowsJ_nil (h0 : nJ = 0) : rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ = [] :=
  List.eq_nil_of_length_eq_zero (by rw [rowsJ, List.length_ofFn, h0])

theorem jCons_nil (h0 : nJ = 0) : jCons b nodesJ orbitJ chalsJ pubsJ lay PJ = [] := by
  rw [jCons, finRange_nil h0, List.flatMap_nil]

theorem jProv_nil (h0 : nJ = 0) : jProv b nodesJ orbitJ chalsJ pubsJ lay PJ = [] := by
  rw [jProv, finRange_nil h0, List.flatMap_nil]

theorem jRd_nil (h0 : nJ = 0) : jRd b nodesJ orbitJ chalsJ pubsJ lay PJ = [] := by
  rw [jRd, finRange_nil h0, List.flatMap_nil]

/-- **`JChipOK` with a non-empty J table is the present block.** -/
theorem present_of_pos (hJk : JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ) (hpos : 0 < nJ) :
    (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ ∧
      (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ ∧ Function.Injective nodesJ ∧
      0 < nJ ∧ ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω := by
  rcases hJk with h | h
  · exact h
  · exact absurd h.1 (by omega)

end Def

/-! ## 2. The J telescopes under `JChipOK` -/

section Tele
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p}
  {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ} {chalsJ pubsJ : ℕ → K} {lay : Fin nJ → PRow}
  {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J export reads' telescope** (`jet_export_sum`), present or absent. -/
theorem jet_export_sumG (hJk : JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ) :
    ((jRd b nodesJ orbitJ chalsJ pubsJ lay PJ).map fun c =>
        (compress (coinsJX δ chalsJ) (liftRec (L := 𝕂′) c))⁻¹).sum = Quad.mk _ (pubsJ 2) (pubsJ 3) := by
  rcases hJk with ⟨h1, h2, h3, h4, h5⟩ | ⟨h0, -, -, h2, h3⟩
  · exact Nock.Jet.RapJetJ8.jet_export_sum h1 h2 h3 h4 h5
  · rw [jRd_nil h0, h2, h3, Quad.mk_zero']; rfl

/-- **The J share of the service balance** (`jet_tagged_sum`), present or absent. -/
theorem jet_tagged_sumG (hJk : JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ) :
    ((jCons b nodesJ orbitJ chalsJ pubsJ lay PJ).map fun c =>
        (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) c))⁻¹).sum =
      Quad.mk _ (pubsJ 0) (pubsJ 1) + ((jProv b nodesJ orbitJ chalsJ pubsJ lay PJ).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  rcases hJk with ⟨h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, -, -⟩
  · exact Nock.Jet.RapJetJ8.jet_tagged_sum h1 h2 h3 h4 h5
  · rw [jCons_nil h0, jProv_nil h0, h1, h2, Quad.mk_zero']; simp

/-- With no J row the effective J service providers are empty. -/
theorem jProvE_nil [DecidableEq K] [DecidableEq 𝕂′] (h0 : nJ = 0) (provO : List ((Fin 8 → K) × K)) :
    Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ) (chals := chalsJ) (pubs := pubsJ)
      (lay := lay) (P := PJ) provO = [] := by
  rw [Nock.Jet.SubJ8.jProvE, jProv_nil h0, List.filter_nil]

end Tele

/-! ## 3. The `x` terminal and `BalJ8` under `JChipOK` -/

section Terminals
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`BalXJ8.extX_sumQ` with `JChipOK`.** -/
theorem extX_sumQG (κ : IOCoins 𝕂′)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hκW : mcoins δ chalsW = κ)
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hκJ : coinsJX δ chalsJ = κ) :
    ((ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ).map
        fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3) := by
  rw [List.map_append, List.sum_append]
  congr 1
  · rw [← hκW]
    exact WalkTeleJ8.walkJ8_reqs_sumQ δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
  · rw [← hκJ]
    exact jet_export_sumG hJk

end Terminals

section Assembly
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV

/-- **`BalXJ8.balJ8_of_goodJ8` with `JChipOK`.** -/
theorem balJ8_of_goodJ8G
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hκC : mcoins δ chalsC = CV)
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hκW : mcoins δ chalsW = CV)
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hκJ : coinsJX δ chalsJ = CV)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      TprovS)
    (hS_ext : ((ext .s).map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    (hG : ServedJ8.GoodCJ8 (b := b) (δ := δ) (pubVal := pubVal) (TprovJ8 pubsC pubsW TprovS)
      (TextJ8 pubsW pubsJ TextS)) :
    BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext := by
  refine ServedJ8.balJ8_of_good hG ?_ ?_
  · intro bl
    cases bl with
    | x =>
      rw [hextX]
      exact extX_sumQG δ b CV kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hκW
        nodesJ orbitJ chalsJ pubsJ lay PJ hJk hκJ
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

section Frame
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`VerJ8.balJ8_frameJ8` with `JChipOK`.** -/
theorem balJ8_frameJ8G (χ : SVFrame.Coins FrameJ8.frameJ8 K) (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS)
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
    (hextP : ext .p = [])
    (TprovS TextS : 𝕂′)
    (hS_prov : ((provs .s).map fun q => algebraMap K 𝕂′ q.2 *
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum = TprovS)
    (hS_ext : ((ext .s).map fun r =>
      (compress (TeleCQ.coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = TextS)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGs : ρS + TextS = TprovS) :
    BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provs ext := by
  have hcv := coinsCV_J8 δ b χ
  refine balJ8_of_goodJ8G hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC
    ((mcoins_of_agree δ χ chalsC hchC).trans hcv.symm)
    kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW
    ((mcoins_of_agree δ χ chalsW hchW).trans hcv.symm)
    nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hJk ((coinsJX_J8 δ χ).trans hcv.symm)
    hprovX hextX hprovP hextP TprovS TextS hS_prov hS_ext ?_
  exact (goodCJ8_iff c m ρ ρS χ pubsC pubsW pubsJ TprovS TextS).2 ⟨hGx, hGp, hGs⟩

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8
