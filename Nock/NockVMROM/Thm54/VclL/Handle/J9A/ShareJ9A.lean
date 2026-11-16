/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ShareJ9A.lean

  For each optional chip the gated list is `if <flag> then <list> else []` (exactly `RR49A`'s gating), and every S8
  obligation about that share is proved by casing the chip's `…ChipOK` disjunction once:
  * axis (`AXChipOK`): `axShare_h7` (`NotJ7`), `axShare_svc` (S8's `hsvc`, through `svcAx_present` / `svcAx_absent`),
    `axShare_sumS` (limb consumes − `TAG_ax` provides = `pubAXs`), `axShare_sumP` (path consumes = `pubAXp`);
  * split (`SPChipOK`): `svA`, `nSA`, `pSA` and `spShare_ne0`, `spShare_lt`, `spShare_nAS`, `spShare_h7`, `spShare_prov`,
    `spShare_sum` (= `pubSPs`);
  * atom walk (`AWChipOK`): `awShare_h7`, `awShare_prov`, `awShare_sum` (= `pubPQ` of the atom walk);
  * `balS_J9A`: S8's `.s` balance `ρS + Σ ext_s = Σ provs_s` from `hGS` and the five share sums (pure algebra);
  * `axLists_qAX`, `splitProvs_qSP`: the chip views' lists are `RealIOJ9A`'s coin-free `…Of` lists.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HokJ9AG9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.BalJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisTeleJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SplitTeleJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LinkV1J9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (DenOKX9)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_entry7 pad8_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A (NotJ7 notJ7_of_tag)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 (axTag_entry7 split_entry7)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvNewX9 (splitSV provP_split)
open Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A (splitSV_ne0 splitSV_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow)
open Nock.J9A.NounAx (valId)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

noncomputable section

section Shares
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-! ## 1. The axis share -/

section Axis
variable {axOn : Bool} {hX nX : ℕ} {hnX : 0 < nX} {nodesX : Fin nX → ZMod p}
  {orbitX : StrictOrbitDomain (ZMod p) 3 hX} {chalsX pubsX : ℕ → K}
  {QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X]}

theorem axShare_h7 (hpG : p = Nock.Atoms.p) (hAX : AXChipOK δ b axOn hnX nodesX orbitX chalsX pubsX QX) :
    ∀ q ∈ (if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []), NotJ7 (p := p) q.1 := by
  have hp5 : 5 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  rcases hAX with ⟨hon, -⟩ | ⟨hoff, -⟩
  · subst hon
    exact fun q hq => notJ7_of_tag (t := 5) hp5 (by norm_num) (by norm_num) (by omega)
      (axTag_entry7 b nodesX orbitX chalsX pubsX QX q hq)
  · subst hoff
    exact fun q hq => by cases hq

/-- **S8's `hsvc` for the flag-gated axis share.** -/
theorem axShare_svc (hpG : p = Nock.Atoms.p) (hAX : AXChipOK δ b axOn hnX nodesX orbitX chalsX pubsX QX)
    {V : ℕ → Option ℕ} {pI pW pS : List ((Fin 8 → K) × K)} {extS : List (Fin 8 → K)}
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hW : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hsubS : ∀ c ∈ (if axOn then AxisChipJ9.axLimbReqs b nodesX orbitX chalsX pubsX QX else []), c ∈ extS)
    (hsubP : ∀ c ∈ (if axOn then AxisChipJ9.axPathReqs b nodesX orbitX chalsX pubsX QX else []), c ∈ extP) :
    ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), DenOKX9 p D V →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p pP →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI →
      ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ →
      (∀ c ∈ extS, c ∈ (pJ ++ pI ++ pW ++
        (if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []) ++ pS).map Prod.fst) →
      (∀ c ∈ extP, c ∈ pP.map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s
        (pJ ++ pI ++ pW ++ (if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []) ++ pS) := by
  rcases hAX with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, -⟩
  · subst hon
    have hsubS' : ∀ i : Fin nX,
        AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extS :=
      fun i => hsubS _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have hsubP' : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
        AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extP := by
      intro i hz
      refine hsubP _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
      rw [if_neg (by rw [hz, sub_zero]; exact one_ne_zero)]
      exact List.mem_singleton_self _
    exact HokJ9AG9.svcAx_present hpG hnX nodesX orbitX chalsX pubsX QX hsat hbind hinj hadj hW hS hsubS' hsubP'
  · subst hoff
    exact HokJ9AG9.svcAx_absent hW hS

/-- **The axis service sum, gated**: Σ limb consumes − Σ `TAG_ax` provides = `pubAXs` (`0` when absent). -/
theorem axShare_sumS (hAX : AXChipOK δ b axOn hnX nodesX orbitX chalsX pubsX QX) :
    ((if axOn then AxisChipJ9.axLimbReqs b nodesX orbitX chalsX pubsX QX else []).map fun r =>
        (compress (⟨Quad.mk _ (chalsX 33) (chalsX 35), Quad.mk _ (chalsX 34) (chalsX 36)⟩ : IOCoins 𝕂′)
          (liftRec (L := 𝕂′) r))⁻¹).sum -
      ((if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chalsX 33) (chalsX 35), Quad.mk _ (chalsX 34) (chalsX 36)⟩ :
          IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsX AxisChipJ9.pubAXs) (pubsX (AxisChipJ9.pubAXs + 1)) := by
  rcases hAX with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, h1, h2, -, -⟩
  · subst hon
    exact AxisTeleJ9.axis_service_sumQ δ b hnX nodesX orbitX chalsX pubsX QX hsat hbind hinj hadj
  · subst hoff
    rw [h1, h2, Quad.mk_zero']
    simp

/-- **The axis path sum, gated**: Σ path consumes = `pubAXp` (`0` when absent). -/
theorem axShare_sumP (hAX : AXChipOK δ b axOn hnX nodesX orbitX chalsX pubsX QX) :
    ((if axOn then AxisChipJ9.axPathReqs b nodesX orbitX chalsX pubsX QX else []).map fun r =>
        (compress (⟨Quad.mk _ (chalsX 33) (chalsX 35), Quad.mk _ (chalsX 34) (chalsX 36)⟩ : IOCoins 𝕂′)
          (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubsX AxisChipJ9.pubAXp) (pubsX (AxisChipJ9.pubAXp + 1)) := by
  rcases hAX with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, -, -, h3, h4⟩
  · subst hon
    exact AxisTeleJ9.axis_path_sumQ δ b hnX nodesX orbitX chalsX pubsX QX hsat hbind hinj hadj
  · subst hoff
    rw [h3, h4, Quad.mk_zero']
    simp

end Axis

/-! ## 2. The split share -/

section Split
variable (nA : ℕ) (spOn : Bool) {hS nS : ℕ} (hnS : 0 < nS) (nodesS : Fin nS → ZMod p)
  (orbitS : StrictOrbitDomain (ZMod p) 3 hS) (chalsS pubsS : ℕ → K)
  (QS : Fin (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.w → (ZMod p)[X])

/-- The split values of the flag-gated share. -/
abbrev svA : ℕ → Option ℕ :=
  if spOn then splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS else fun _ => none

/-- The split row count of the flag-gated share. -/
abbrev nSA : ℕ := if spOn then nS else 0

/-- The split providers of the flag-gated share. -/
abbrev pSA : List ((Fin 8 → K) × K) :=
  if spOn then SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS else []

variable {nA spOn hnS nodesS orbitS chalsS pubsS QS}

theorem spShare_ne0 (hp32 : 2 ^ 32 < p) (hSP : SPChipOK δ b nA spOn hnS nodesS orbitS chalsS pubsS QS) :
    ∀ s v, svA nA spOn hnS nodesS orbitS chalsS pubsS QS s = some v → v ≠ 0 := by
  rcases hSP with ⟨hon, hsat, -⟩ | ⟨hoff, -⟩
  · subst hon
    exact splitSV_ne0 δ nA b hnS nodesS orbitS chalsS pubsS QS hp32 hsat
  · subst hoff
    intro s v h; cases h

theorem spShare_lt : ∀ s v, svA nA spOn hnS nodesS orbitS chalsS pubsS QS s = some v → s < nSA spOn (nS := nS) := by
  cases spOn
  · intro s v h; cases h
  · exact splitSV_lt δ nA b hnS nodesS orbitS chalsS pubsS QS

theorem spShare_nAS (hp63 : 2 ^ 63 < p) (hnAS : nA + nS < 2 ^ 57) : 64 * (nA + nSA spOn (nS := nS)) ≤ p := by
  cases spOn <;> simp [nSA] <;> omega

theorem spShare_h7 : ∀ q ∈ pSA nA spOn hnS nodesS orbitS chalsS pubsS QS, q.1 ⟨7, by norm_num⟩ = 0 := by
  cases spOn
  · intro q hq; cases hq
  · exact split_entry7 b nodesS orbitS chalsS pubsS QS

theorem spShare_prov (hp32 : 2 ^ 32 < p) (hnAS : nA + nS < p)
    (hSP : SPChipOK δ b nA spOn hnS nodesS orbitS chalsS pubsS QS) (rA : ℕ → ARow) :
    ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (svA nA spOn hnS nodesS orbitS chalsS pubsS QS)) Rg combN) .s
        (pSA nA spOn hnS nodesS orbitS chalsS pubsS QS) := by
  rcases hSP with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, -⟩
  · subst hon
    exact fun D Rg => provP_split δ nA b hnS nodesS orbitS chalsS pubsS QS D Rg rA hp32 hsat hbind hinj hadj hnAS
  · subst hoff
    exact fun D Rg q hq => by cases hq

theorem spShare_sum (hSP : SPChipOK δ b nA spOn hnS nodesS orbitS chalsS pubsS QS) :
    ((pSA nA spOn hnS nodesS orbitS chalsS pubsS QS).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chalsS 33) (chalsS 35), Quad.mk _ (chalsS 34) (chalsS 36)⟩ :
          IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsS SplitChipJ9.pubSPs) (pubsS (SplitChipJ9.pubSPs + 1)) := by
  rcases hSP with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, h1, h2⟩
  · subst hon
    exact SplitTeleJ9.split_provs_sumQ δ nA b hnS nodesS orbitS chalsS pubsS QS hsat hbind hinj hadj
  · subst hoff
    rw [h1, h2, Quad.mk_zero']
    simp [pSA]

end Split

/-! ## 3. The atom-walk share -/

section AW
variable {krootsV : ℕ} {hV nV : ℕ} {hnV : 0 < nV} {nodesV : Fin nV → ZMod p}
  {orbitV : StrictOrbitDomain (ZMod p) 3 hV} {chalsV pubsV : ℕ → K}
  {QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X]}

/-- The atom-walk providers of the root-count-gated share (`AWChipOK`: present iff `1 ≤ krootsV`). -/
abbrev pWA (krootsV : ℕ) (l : List ((Fin 5 → K) × K)) : List ((Fin 8 → K) × K) :=
  if 1 ≤ krootsV then pad8 l else []

theorem awShare_h7 : ∀ q ∈ pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV),
    q.1 ⟨7, by norm_num⟩ = 0 := by
  unfold pWA
  split_ifs
  · exact pad8_entry7 _
  · intro q hq; cases hq

theorem awShare_prov {nA : ℕ} {rA : ℕ → ARow}
    (hpres : 1 ≤ krootsV → ∀ (sv : ℕ → Option ℕ) (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s
        (pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV))) :
    ∀ (sv : ℕ → Option ℕ) (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s
        (pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)) := by
  intro sv D Rg
  by_cases h : 1 ≤ krootsV
  · have e : pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) =
        pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) := if_pos h
    rw [e]; exact hpres h sv D Rg
  · have e : pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) = [] := if_neg h
    rw [e]; exact HokJ9AG9.provP_nil

theorem awShare_sum (hVk : AWChipOK δ b krootsV hnV nodesV orbitV chalsV pubsV QV) :
    ((pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨Quad.mk _ (chalsV 33) (chalsV 35), Quad.mk _ (chalsV 34) (chalsV 36)⟩ :
          IOCoins 𝕂′) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)) := by
  rcases hVk with ⟨hsat, hbind, hinj, hadj, hk, -⟩ | ⟨h0, -, -, -, -, h1, h2⟩
  · have e : pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) =
        pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) := if_pos hk
    rw [e, pad8_sum]
    exact WalkTeleJ8.walkHQK_provs_sumQ δ krootsV b hnV nodesV orbitV chalsV pubsV QV hsat hbind hinj hadj
  · have e : pWA krootsV (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) = [] :=
      if_neg (show ¬ 1 ≤ krootsV by omega)
    rw [e, h1, h2, Quad.mk_zero']
    simp

end AW

/-! ## 4. The `.s` balance (algebra) -/

/-- **S8's `.s` balance** `ρS + Σ ext_s = Σ provs_s` at the S8 wiring `ext_s = pins ++ eA ++ jCons`,
`provs_s = jProv ++ (inc ++ pW ++ pX ++ pS)`, from `hGS` and the five share sums. -/
theorem balS_J9A (κ : IOCoins 𝕂′) (ρS : 𝕂′) (pins eA jC : List (Fin 8 → K))
    (jP pI pW pX pS : List ((Fin 8 → K) × K)) (J0 MI VPQ AXs SPs : 𝕂′)
    (hGS : ρS + (pins.map fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum + J0 + AXs = MI + VPQ + SPs)
    (h3 : (jC.map fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum =
      J0 + (jP.map fun q => algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hI : (pI.map fun q => algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum = MI)
    (hW : (pW.map fun q => algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum = VPQ)
    (hX : (eA.map fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum -
      (pX.map fun q => algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum = AXs)
    (hS : (pS.map fun q => algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum = SPs) :
    ρS + ((pins ++ eA ++ jC).map fun r => (compress κ (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((jP ++ (pI ++ pW ++ pX ++ pS)).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress κ (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  simp only [List.map_append, List.sum_append]
  linear_combination hGS + h3 + hX - hI - hW - hS

end Shares

/-! ## 5. The chip views' lists are the coin-free `…Of` lists -/

section Views
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p))

theorem axLists_qAX (chals pubs : ℕ → K) :
    AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX chals pubs (qAX δ b Pb tr chals pubs) = axLimbReqsOf b Pb tr ∧
      AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX chals pubs (qAX δ b Pb tr chals pubs) = axPathReqsOf b Pb tr ∧
      AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX chals pubs (qAX δ b Pb tr chals pubs) = axTagProvsOf b Pb tr := by
  obtain ⟨h1, h2, h3⟩ := AxisTeleJ9.axLists_chals_free b Pb.nodesX Pb.orbitX chals pubs (qAX δ b Pb tr chals pubs)
  exact ⟨h1.trans rfl, h2.trans rfl, h3.trans rfl⟩

theorem splitProvs_qSP (chals pubs : ℕ → K) :
    SplitChipJ9.splitProvs b Pb.nodesS Pb.orbitS chals pubs (qSP δ b Pb tr chals pubs) = splitProvsOf b Pb tr :=
  (SplitTeleJ9.splitProvs_chals_free b Pb.nodesS Pb.orbitS chals pubs (qSP δ b Pb tr chals pubs)).trans rfl

end Views

end

end Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A
#print axioms axShare_h7
#print axioms axShare_svc
#print axioms axShare_sumS
#print axioms axShare_sumP
#print axioms spShare_ne0
#print axioms spShare_lt
#print axioms spShare_nAS
#print axioms spShare_h7
#print axioms spShare_prov
#print axioms spShare_sum
#print axioms awShare_h7
#print axioms awShare_prov
#print axioms awShare_sum
#print axioms balS_J9A
#print axioms axLists_qAX
#print axioms splitProvs_qSP
end Axioms
