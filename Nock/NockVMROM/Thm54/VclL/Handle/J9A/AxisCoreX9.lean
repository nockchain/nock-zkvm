/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/AxisCoreX9.lean

* `ext_served9` — the twin of `BalXJ8.ext_served` at `BCtx9`: every other-consumer key of `ext bl` is a provider
    key (the S1 `hsv`).
  * `acceptsJ9A_holdsN_axisI9` — `HoldsX9.acceptsJ9A_holdsN_computeI9` with the `.s` provider obligation produced
    by the two-pass service assembly `AxisSoundX9.provP_service9` (S1–S4) from the axis chip, given the J-8
    providers' `RecOK9I` and the atom walk / split providers' `RecOK9`; the axis limb consumes are in `ext .s`,
    the axis path consumes in `ext .p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HoldsX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisSoundX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9

open Nock Nock.Reified Nock.Edit Nock.Walk
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 ProvP AxOK liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (compReqsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (tileSet)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (encT)
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.StrictExtension
open Nock.Jet (Registry HoldsN)
open Polynomial Module

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN9" => CompReqsX9.envsN9 hn nodes orbit chalV pubVal P
local notation "CV" => coinsCV b δ chalV

/-- **The other consumers are served at the twin** (twin of `BalXJ8.ext_served`). -/
theorem ext_served9 [CharP 𝕂′ p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (bl : Bal) : ∀ c ∈ ext bl, c ∈ (provs bl).map Prod.fst := by
  have hd : ∀ bl, ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, compress ⟨(CV).gamma, (CV).pole⟩ r ≠ 0 :=
    fun bl => TeleC.den_ne_of_out _ _ _ _ (hout bl)
  have hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0 :=
    fun bl r hr => hd bl _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (hd bl)
      (den_prov_ne_of_out _ _ _ _ (hout bl)) ?_ (hcount bl) (hout bl)
    have h1 := compReqsX9_sum C hne bl
    have h2 := hbal bl
    unfold reqsJ9 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro c hc
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp
    (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

/-- The `.p` clause of `RecOK9I` is `RecOK`'s path clause. -/
theorem recOK9I_p {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry} (a b' c d : ℕ)
    (hr : RecOK9I D V R combN ([a, b', c, d], .p)) :
    ∃ Rt C, D (1, a) = some Rt ∧ D (c, d) = some C ∧ Noun.slot b' Rt = some C := by
  have h := hr (pre9_off (by decide))
  have hc : recClass ([a, b', c, d], Bal.p) = 0 := rfl
  unfold RecOK9 at h
  rw [hc, if_neg (by omega), if_neg (by omega)] at h
  exact h

/-- **S8 middle layer: the compute core with the axis chip.** -/
theorem acceptsJ9A_holdsN_axisI9 [DecidableEq (ZMod p)] [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry}
    (hR : R.Faithful) (hD : DenOKX9 p D V)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    -- the axis chip
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    -- the providers
    {pJ pI pW pS : List ((Fin 8 → K) × K)}
    (hprovS : provs .s = pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ pS)
    (hJ : ProvP (p := p) (K := K) (RecOK9I D V R combN) .s pJ)
    (hI : ProvP (p := p) (K := K) (RecOK9I D V R combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V R combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V R combN) .s pS)
    (hprovX : ProvP (p := p) (K := K) (RecOK9I D V R combN) .x (provs .x))
    (hprovP : ProvP (p := p) (K := K) (RecOK9I D V R combN) .p (provs .p))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    -- the axis consumes
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .s)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .p)
    (hreal : (stX9 (EN9 0)).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN9 0) xS) = some x.subject) (hf : D (hdV (EN9 0) xF) = some x.formula)
    (he : D (hdV (EN9 0) xE) = some x.result) : HoldsN x := by
  have B := bctx9_of_xctx C
  have hsv := ext_served9 B hbal hout hcount
  have hsvS : ∀ c ∈ ext .s, c ∈ (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ pS).map
      Prod.fst := by
    intro c hc; have := hsv .s c hc; rwa [hprovS] at this
  have h9 := AxisSoundX9.provP_service9 δ b hnX nodesX orbitX chalsX pubsX QX hpG hsatX hbindX hinjX hadjX R hD
    hJ hI hW hS hsvS hsubS (fun a b' c d hr => recOK9I_p a b' c d hr) (hsv .p) hsubP hprovP
  have hprov : ∀ bl, ProvP (p := p) (K := K) (RecOK9I D V R combN) bl (provs bl) := by
    intro bl
    cases bl with
    | x => exact hprovX
    | p => exact hprovP
    | s => rw [hprovS]; exact h9
  exact acceptsJ9A_holdsN_computeI9 C hpG hR hD hseed hα hw hbal hout hcount hprov haxP hreal x hs hf he

end Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9

open Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9 in
#print axioms ext_served9
open Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9 in
#print axioms acceptsJ9A_holdsN_axisI9
