/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServiceJ8.lean

  **The SERVICE balance `s` of the J-8 frame.**

  The compute chip `computeChipVCLHX` consumes into the service balance `s` (width `mOf.s = 8`); its
  providers are the J chip (`jProv`: in-chip tag-last provides and the `TAG_jet` provides), the atom
  table's inc-record heads (multiplicity `mi`, terminal `(pub₈, pub₉)`) and the atom-walk's `walkRecA`
  records (multiplicity `mL / mR`, terminal `(pub₆, pub₇)`); its other consumer is the J chip
  (`jCons`).  So `provs.s = jProv ++ provO`, `ext.s = jCons`.

  * §1 `provP_append`: a provider obligation splits over `++`.
  * §2 **The J side from the compute's `s` balance**: `jet_hG_of_balJ8` (the merged identity `hG` of
    `RapJetJ8.bal_of_service`), `jet_hout_of_out` / `jet_hcount_of_count` (its IO-event and count
    premises are the compute's `s` premises, verbatim), hence **`jetAccepted_of_balJ8`** (J-3b `Accepted`)
    and **`jetProvOK_of_balJ8`** (`ProvP RecOK.s jProv`) with JB's `hG / hout / hcount` discharged; the
    one coin premise is `hcoins : coinsJ δ χ_J = coinsCV b δ chalV` (the J tagged coins ARE the compute's
    `(γH′, ρH′)`, a frame-wiring identity, item 3); **`provOK_s`**: `ProvOK.s (provs.s)` from the J half
    and the other providers' half.
  * §3 **Zero padding `5 → 8`** (`pad8`): sums, nonzero denominators and the IO terms are unchanged
    (`DenXJ8.compress_padK`); entry `7` of a padded key is `0` — JB's **`hO7`** for every padded list
    (`pad8_entry7`).
  * §4 **The atom table's inc heads**: `atomIncProvs` (`(incKey, mi)` on the rows with `mi ≠ 0`; a zero-weight
    row's key is unconstrained, so it is left out of the provider list), **`atomIncProvs_sum`**
    (`Σ mi·den⁻¹ = (pub₈, pub₉)` at the handle coins, the `miAcc` telescope), `atomIncProvs_den`.
  * §5 **The `s` balance from the verifier check**: `GoodS` (`ρ_s + T_J = T_inc + T_AW`, publics only)
    with the three telescopes and the coin identifications ⇒ the `s` component of `BalJ8` at
    `provs.s = jProv ++ pad8 inc ++ pad8 aw`, `ext.s = jCons` (**`balS_of_goodS`**).
-/
import Nock.Jet.RapJetJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTeleJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.Jet Nock.Jet.Autogen Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK compReqsX compReqsX_sum compress_padK liftRec_padK)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)

noncomputable section

/-! ## 1. A provider obligation splits over `++` -/

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

theorem provP_append {Φ : List ℕ × Bal → Prop} {bl : Bal} {l₁ l₂ : List ((Fin (mOf bl) → K) × K)} :
    ProvP (p := p) Φ bl (l₁ ++ l₂) ↔ ProvP (p := p) Φ bl l₁ ∧ ProvP (p := p) Φ bl l₂ := by
  unfold ProvP
  constructor
  · intro h
    exact ⟨fun q hq => h q (List.mem_append_left _ hq), fun q hq => h q (List.mem_append_right _ hq)⟩
  · rintro ⟨h₁, h₂⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h₁ q hq
    · exact h₂ q hq

end Gen

/-! ## 2. The J side of the service balance from the compute's `s` balance -/

section Service
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}
  {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p} {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ} {chalsJ pubsJ : ℕ → K}
  {lay : Fin nJ → PRow} {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV
local notation "JP" => jProv b nodesJ orbitJ chalsJ pubsJ lay PJ
local notation "JC" => jCons b nodesJ orbitJ chalsJ pubsJ lay PJ
local notation "CRs" => compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
  (orbit := orbit) (P := P) Bal.s

/-- The compute's `s` consumes, as `Fin 8` keys (`mOf.s = 8`). -/
abbrev compS : List (Fin 8 → K) := CRs

theorem rhoX_s : rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.s =
    Quad.mk (algebraMap (ZMod p) K δ) (Compute.LogUp.limbVal b pubVal (TeleCQX.balCols Bal.s).2.1)
      (Compute.LogUp.limbVal b pubVal (TeleCQX.balCols Bal.s).2.2.2) := rfl

/-- **JB's merged identity `hG`** from the compute's `s` balance.  With `provs.s = jProv ++ provO`,
`ext.s = jCons` and the J tagged coins equal to the compute's handle coins: the J terminal plus the
compute's own `s` consumes equals the other providers (`T_J + Σ_compute = Σ_provO`).  The compute's
consumes telescope to `ρ_s` (`compReqsX_sum`), the J consumes to `T_J + Σ jProv` (`jet_tagged_sum`). -/
theorem jet_hG_of_balJ8 (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress CV (liftRec (L := 𝕂′) r) ≠ 0)
    (provO : List ((Fin 8 → K) × K)) (hps : provs Bal.s = JP ++ provO) (hes : ext Bal.s = JC)
    (hcoins : coinsJ δ chalsJ = CV)
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω) :
    Quad.mk _ (pubsJ 0) (pubsJ 1) +
        ((compS (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal)
          (orbit := orbit) (P := P)).map fun c => (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  have h1 := compReqsX_sum C hne Bal.s
  have h2 := hbal Bal.s
  have h3 := jet_tagged_sum hsatJ hbindJ hinjJ hnJ hadjJ
  rw [hcoins] at h3 ⊢
  rw [hps, hes, rhoX_s] at h2
  have h2' : Quad.mk (algebraMap (ZMod p) K δ) (Compute.LogUp.limbVal b pubVal (TeleCQX.balCols Bal.s).2.1)
        (Compute.LogUp.limbVal b pubVal (TeleCQX.balCols Bal.s).2.2.2) +
      (List.map (fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹) JC).sum =
      (List.map (fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹) JP).sum +
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    rw [← List.sum_append, ← List.map_append]; exact h2
  change (List.map (fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹) CRs).sum = _ at h1
  change _ + (List.map (fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹) CRs).sum = _
  linear_combination h1 + h2' - h3

/-- **JB's `hout`** is the compute's `s` IO premise, verbatim (same lists, same coins). -/
theorem jet_hout_of_out
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (provO : List ((Fin 8 → K) × K)) (hps : provs Bal.s = JP ++ provO) (hes : ext Bal.s = JC)
    (hcoins : coinsJ δ chalsJ = CV)
    (hout : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext Bal.s) (liftP (provs Bal.s))) :
    ((coinsJ δ chalsJ).gamma, (coinsJ δ chalsJ).pole) ∉
      IOFailureEventW (((compS (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal)
          (orbit := orbit) (P := P)) ++ JC).map (liftRec (L := 𝕂′)))
        ((JP ++ provO).map fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)) := by
  rw [hcoins]
  unfold reqsJ8 liftP at hout
  rw [hps, hes] at hout
  exact hout

/-- **JB's `hcount`** is the compute's `s` count premise. -/
theorem jet_hcount_of_count
    {ext : (bl : Bal) → List (Fin (mOf bl) → K)} (hes : ext Bal.s = JC)
    (hcount : (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext Bal.s).length < p) :
    ((compS (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal)
          (orbit := orbit) (P := P)) ++ JC).length < p := by
  unfold reqsJ8 at hcount
  rw [hes, List.length_map] at hcount
  exact hcount

/-- **J-3b `Accepted` from the compute's `s` balance**: JB's `accepted_of_service` with `reqO` the
compute's `s` consumes and `hG / hout / hcount` discharged by the compute side. -/
theorem jetAccepted_of_balJ8 [CharP 𝕂′ p] (hp3 : 3 < p) (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext Bal.s).length < p)
    (provO : List ((Fin 8 → K) × K)) (hps : provs Bal.s = JP ++ provO) (hes : ext Bal.s = JC)
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hcoins : coinsJ δ chalsJ = CV)
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup) :
    Accepted R regs ids (rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ) := by
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress CV (liftRec (L := 𝕂′) r) ≠ 0 :=
    fun bl r hr => TeleC.den_ne_of_out _ _ _ _ (hout bl) _
      (List.mem_map_of_mem (List.mem_append_left _ hr))
  exact accepted_of_service hp3 hsatJ hbindJ hinjJ hnJ hadjJ hlay hsmall huniq _ provO hO7
    (jet_hG_of_balJ8 C hbal hne provO hps hes hcoins hsatJ hbindJ hinjJ hnJ hadjJ)
    (jet_hout_of_out provO hps hes hcoins (hout Bal.s))
    (jet_hcount_of_count hes hcount)

/-- **`JetProvOK` from the compute's `s` balance** (JB's `jetProvOK_of_sat` with `hG / hout / hcount`
discharged).  Remaining premises: the public-layout checks `hlay / hsmall / huniq`, `hO7` on the other
providers (a theorem for every zero-padded list, `pad8_entry7`), the coin identity `hcoins`, and the
memory-side facts `hD / hTpl / hRd / hReg / hSub` of `jetProvOK`. -/
theorem jetProvOK_of_balJ8 [CharP 𝕂′ p] (hp3 : 3 < p) (C : BCtx hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext Bal.s).length < p)
    (provO : List ((Fin 8 → K) × K)) (hps : provs Bal.s = JP ++ provO) (hes : ext Bal.s = JC)
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hcoins : coinsJ δ chalsJ = CV)
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (hSub : ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, r.pre.kd = .call →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S) :
    ProvP (p := p) (K := K) (RecOK D Rg limbA) .s JP :=
  jetProvOK hp3 (jetAccepted_of_balJ8 hp3 C hbal hout hcount provO hps hes hO7 hcoins hsatJ hbindJ hinjJ hnJ
    hadjJ hlay hsmall huniq) hD hTpl hRd hReg hSub

/-- **`ProvOK.s`**: the service providers `provs.s = jProv ++ provO` are genuine when the J half is
(`jetProvOK_of_balJ8`) and the other providers are. -/
theorem provOK_s {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} (provO : List ((Fin 8 → K) × K))
    (hps : provs Bal.s = JP ++ provO)
    (hJ : ProvP (p := p) (K := K) (RecOK D Rg limbA) .s JP)
    (hO : ProvP (p := p) (K := K) (RecOK D Rg limbA) .s provO) :
    ProvOK (p := p) (K := K) D Rg limbA .s (provs Bal.s) := by
  show ProvP (p := p) (K := K) (RecOK D Rg limbA) .s (provs Bal.s)
  rw [hps]
  exact provP_append.mpr ⟨hJ, hO⟩

end Service

/-! ## 3. Zero padding `5 → 8` -/

section Pad
variable {K : Type} [Field K]

/-- Zero-pad a weighted provider list from width `5` to the service width `8`. -/
def pad8 (l : List ((Fin 5 → K) × K)) : List ((Fin 8 → K) × K) := l.map fun q => (padK q.1, q.2)

/-- **JB's `hO7`** for a padded list: entry `7` of every key is `0`. -/
theorem pad8_entry7 (l : List ((Fin 5 → K) × K)) : ∀ q ∈ pad8 l, q.1 ⟨7, by norm_num⟩ = 0 := by
  intro q hq
  obtain ⟨q', -, rfl⟩ := List.mem_map.mp hq
  simp [padK]

variable {L : Type} [Field L] [Algebra K L]

theorem pad8_compress (coins : IOCoins L) (v : Fin 5 → K) :
    compress coins (liftRec (L := L) (padK (m' := 8) v)) = compress coins (liftRec (L := L) v) := by
  rw [liftRec_padK, compress_padK coins (by norm_num)]

/-- Padding does not move the weighted sum. -/
theorem pad8_sum (coins : IOCoins L) (l : List ((Fin 5 → K) × K)) :
    ((pad8 l).map fun q => algebraMap K L q.2 * (compress coins (liftRec (L := L) q.1))⁻¹).sum =
      (l.map fun q => algebraMap K L q.2 * (compress coins (liftRec (L := L) q.1))⁻¹).sum := by
  unfold pad8
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, pad8_compress]

/-- Padding keeps the denominators nonzero. -/
theorem pad8_den (coins : IOCoins L) (l : List ((Fin 5 → K) × K))
    (h : ∀ q ∈ l, compress coins (liftRec (L := L) q.1) ≠ 0) :
    ∀ q ∈ pad8 l, compress coins (liftRec (L := L) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  rw [pad8_compress]
  exact h q' hq'

end Pad

/-! ## 4. The atom table's inc-record heads -/

section Inc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (AtomChipHQ.atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

open AtomServedQ AtomChipHQ

/-- **The atom table's inc-record providers**: `(incKey, mi)` on every row with `mi ≠ 0` (the `miAcc`
accumulator).  Zero-weight rows are left out: they add `0` to the sum, and their key is unconstrained
(the head gate `mi·(1 − inc − conv)` only binds rows with `mi ≠ 0`), so the provider obligation
`ProvP` is stated over the weighted rows. -/
def atomIncProvs [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 5 → K) × K) :=
  (List.finRange n).flatMap fun i =>
    if (aEF b nodes orbit chals pubs Q' i).trace mi = 0 then [] else
      [(ServeH.keyVec5 incKey (aEF b nodes orbit chals pubs Q' i),
        algebraMap F K ((aEF b nodes orbit chals pubs Q' i).trace mi))]

theorem incKey_len : (incKey : List (CoeffExpr F)).length = 5 := by simp [incKey]

theorem gate_inv_inc : QE.sub (QE.mul δF (QE.var miInv) (HQ.denKeyQ δF incKey)) QE.one ∈ qList δF := by
  simp [qList, atomQ]

/-- **The inc providers' weighted `𝕂′` sum is the terminal `(pub₈, pub₉)`** (the `miAcc` telescope). -/
theorem atomIncProvs_sum [DecidableEq F] (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((atomIncProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (acoins δF chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) := by
  rw [← atom_tele δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj mi miInv miAcc pubMI
    (by simp [qList, atomQ]) (by simp [qList, atomQ]) (by simp [qList, atomQ])]
  rw [atomIncProvs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(atom_inv δF b hn nodes orbit chals pubs Q hsat _ _ (gate_inv_inc δF) i).2,
    aDen_eq δF b hn nodes orbit chals pubs Q _ incKey_len]
  by_cases h0 : (aEF b nodes orbit chals pubs Q i).trace mi = 0
  · rw [if_pos h0, h0]; simp [liftQ]
  · rw [if_neg h0]; simp [liftQ]

theorem atomIncProvs_den [DecidableEq F] (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ atomIncProvs b nodes orbit chals pubs Q, compress (acoins δF chals) (liftRec (L := 𝕂′) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  split_ifs at hi with h0
  · simp at hi
  rw [List.mem_singleton] at hi
  subst hi
  rw [← aDen_eq δF b hn nodes orbit chals pubs Q _ incKey_len]
  exact (atom_inv δF b hn nodes orbit chals pubs Q hsat _ _ (gate_inv_inc δF) i).1

end Inc

/-! ## 5. The `s` balance from the verifier check -/

section BalS
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p}
  {hJ nJ : ℕ} {nodesJ : Fin nJ → ZMod p} {orbitJ : StrictOrbitDomain (ZMod p) 3 hJ} {chalsJ pubsJ : ℕ → K}
  {lay : Fin nJ → PRow} {PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X]}
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}
  {kroots hW nW : ℕ} {hnW : 0 < nW} {nodesW : Fin nW → ZMod p} {orbitW : StrictOrbitDomain (ZMod p) 3 hW}
  {chalsW pubsW : ℕ → K}
  {QW : Fin (walkChipHQK δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "CV" => coinsCV b δ chalV
local notation "JP" => jProv b nodesJ orbitJ chalsJ pubsJ lay PJ
local notation "JC" => jCons b nodesJ orbitJ chalsJ pubsJ lay PJ
local notation "INC" => atomIncProvs b nodesA orbitA chalsA pubsA QA
local notation "AW" => ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW

/-- **The other service providers** `provO`: the atom table's inc heads and the atom-walk's `walkRecA`
records, zero-padded to the service width `8`. -/
abbrev provOS : List ((Fin 8 → K) × K) := pad8 INC ++ pad8 AW

/-- **`GoodS`, the verifier's service check** on the published terminals: the compute's `ρ_s` plus the J
terminal equals the atom table's inc terminal plus the atom-walk's provide terminal. -/
def GoodS : Prop :=
  rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.s + Quad.mk (algebraMap (ZMod p) K δ) (pubsJ 0) (pubsJ 1) =
    Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1))

/-- `hO7` for the other service providers. -/
theorem provOS_entry7 : ∀ q ∈ (provOS (nodesA := nodesA) (orbitA := orbitA) (chalsA := chalsA)
    (pubsA := pubsA) (QA := QA) (nodesW := nodesW) (orbitW := orbitW) (chalsW := chalsW) (pubsW := pubsW)
    (QW := QW) (b := b) : List ((Fin 8 → K) × K)), q.1 ⟨7, by norm_num⟩ = 0 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact pad8_entry7 _ q hq
  · exact pad8_entry7 _ q hq

/-- **The `s` component of `BalJ8`** from the verifier check `GoodS` and the three memory telescopes
(`jet_tagged_sum`, `atomIncProvs_sum`, `walkHQK_provs_sumQ`), with the three chips' handle coins identified
with the compute's (`hcJ`, `hcA`, `hcW`; frame wiring). -/
theorem balS_of_goodS (hgood : GoodS (b := b) (δ := δ) (pubVal := pubVal) (pubsJ := pubsJ) (pubsA := pubsA)
      (pubsW := pubsW))
    (hcJ : coinsJ δ chalsJ = CV) (hcA : AtomServedQ.acoins δ chalsA = CV)
    (hcW : BalanceVSQ.mcoins δ chalsW = CV)
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hsatW : (walkChipHQK δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipHQK δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω) :
    rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.s +
        (List.map (fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹) JC).sum =
      (List.map (fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹)
        (JP ++ (pad8 INC ++ pad8 AW))).sum := by
  have h3 := jet_tagged_sum hsatJ hbindJ hinjJ hnJ hadjJ
  have hI := atomIncProvs_sum δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA
  have hW := WalkTeleJ8.walkHQK_provs_sumQ δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW
  rw [hcJ] at h3
  rw [hcA] at hI
  rw [hcW] at hW
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, pad8_sum, pad8_sum, h3, hI, hW]
  unfold GoodS at hgood
  linear_combination hgood

/-- **`BalJ8` from its three components.** -/
theorem balJ8_of_parts {chalV' : ℕ → ZMod p}
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hx : rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.x +
        ((ext Bal.x).map fun r => (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provs Bal.x).map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hp : rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.p +
        ((ext Bal.p).map fun r => (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provs Bal.p).map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hs : rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.s +
        ((ext Bal.s).map fun r => (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provs Bal.s).map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ chalV') (liftRec (L := 𝕂′) q.1))⁻¹).sum) :
    BalJ8 (b := b) (δ := δ) (chalV := chalV') (pubVal := pubVal) provs ext := by
  intro bl
  cases bl
  · exact hx
  · exact hp
  · exact hs

/-- **The `s` component in `BalJ8` form** at `provs.s = jProv ++ provOS`, `ext.s = jCons`. -/
theorem balS_of_goodS' {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)}
    {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hps : provs Bal.s = JP ++ (pad8 INC ++ pad8 AW)) (hes : ext Bal.s = JC)
    (hgood : GoodS (b := b) (δ := δ) (pubVal := pubVal) (pubsJ := pubsJ) (pubsA := pubsA)
      (pubsW := pubsW))
    (hcJ : coinsJ δ chalsJ = CV) (hcA : AtomServedQ.acoins δ chalsA = CV)
    (hcW : BalanceVSQ.mcoins δ chalsW = CV)
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hsatW : (walkChipHQK δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipHQK δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω) :
    rhoX (b := b) (δ := δ) (pubVal := pubVal) Bal.s +
        ((ext Bal.s).map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provs Bal.s).map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  rw [hps, hes]
  exact balS_of_goodS hgood hcJ hcA hcW hsatJ hbindJ hinjJ hnJ hadjJ hsatA hbindA hinjA hadjA hsatW hbindW
    hinjW hadjW

end BalS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8
