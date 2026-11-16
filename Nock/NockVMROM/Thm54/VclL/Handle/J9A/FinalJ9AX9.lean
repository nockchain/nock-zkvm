/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/FinalJ9AX9.lean

* The `.s` providers are `jProv ++ (pI ++ pW ++ TAG_ax ++ pS)` (jet, inc, atom walk, axis, split); the `.s`
    other consumers `pinCons ++ eA ++ jCons` (`eA` holds the axis limb consumes, `hsubS`).
  * The balance identity `hbal` is a PARAMETER (S8: provider lists as parameters; S9 supplies it from the verifier's
    public equations and the chip telescopes); the J share `hG` follows from `hbal .s`, the compute telescope
    `compReqsX9_sum` and `jet_tagged_sumG`.
  * The effective providers, as in `FinalJ9IG`: `provsE := withS provs (jProvE provO ++ provOE provO)`.
  * J: `SubJ9A.bal_of_serviceE9` / `pin_servedE9` (the `TAG_ax` providers' entry `7` is `5`, not a J tag),
    `accepted_of_sat`, then `ProvKindsX9.jetProv9` at `D` (`hRd` from the `.x` providers served at `BCtx9`).
  * The axis service: `AxisSoundX9.provP_service9` at `jProvE provO ++ pI ++ pW ++ TAG_ax ++ pS` (every `.s`
    consumer is served by the effective list, a sublist up to the filter).
  * The core: `HoldsX9.acceptsJ9A_holdsN_computeI9` at `provsE`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisCoreX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProvKindsX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SubJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8E
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8
import Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9

open Nock Nock.Reified Nock.Edit Nock.Walk
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 ProvP AxOK liftP rhoX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (compReqsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (tileSet)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (encT)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8E (withS provP_filter)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8 (axOK_x axOK_s)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (provP_append)
open Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A (NotJ7 notJ7_of_tag notJ7_of_zero)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9 (ext_served9 recOK9I_p)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB provK Accepted)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ coinsJ accepted_of_sat)
open Nock.Jet.FibreJ8 (effP)
open Nock.Jet.PinJ8 (pinKey pinCons)
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.StrictExtension
open Nock.Jet (Registry HoldsN)
open Polynomial Module

noncomputable section

/-! ## 1. Entry `7` of the axis and split keys -/

section Keys
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]
  {h n : ℕ} (b : Basis (Fin 3) F K) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem axTag_entry7 {w : ℕ} (Q' : Fin w → F[X]) :
    ∀ q ∈ AxisChipJ9.axTagProvs b nodes orbit chals pubs Q',
      q.1 ⟨7, by norm_num⟩ = algebraMap F K ((5 : ℕ) : F) := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  split_ifs at hi with h0
  · simp at hi
  · simp only [List.mem_singleton] at hi
    subst hi
    simp [AxisChipJ9.keyVecL, AxisChipJ9.tagKey, AxisChipJ9.tagAx, CoeffExpr.eval]

theorem split_entry7 {w : ℕ} (Q' : Fin w → F[X]) :
    ∀ q ∈ SplitChipJ9.splitProvs b nodes orbit chals pubs Q', q.1 ⟨7, by norm_num⟩ = 0 := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  split_ifs at hi with h0
  · simp at hi
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
      simp [SplitChipJ9.keyVecL, SplitChipJ9.key2, SplitChipJ9.key3, CoeffExpr.eval]

end Keys

/-! ## 2. The S8 effective layer -/

theorem mem_shift {α : Type} {a : α} {J I W X S : List α} (h : a ∈ I ++ W ++ X ++ S) :
    a ∈ J ++ I ++ W ++ X ++ S := by
  simp only [List.mem_append] at h ⊢; tauto

theorem mem_shiftJ {α : Type} {a : α} {J I W X S : List α} (h : a ∈ J) : a ∈ J ++ I ++ W ++ X ++ S := by
  simp only [List.mem_append]; tauto

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN9" => CompReqsX9.envsN9 hn nodes orbit chalV pubVal P
local notation "CV" => coinsCV b δ chalV

/-- **S8 effective layer, generic in the axis share** (`pX` and its service step `hsvc`). -/
theorem acceptsJ9A_holdsN_EIG9 [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hcJ : coinsJ δ chalsJ = CV)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the wiring
    {pI pW pX pS : List ((Fin 8 → K) × K)} {eA : List (Fin 8 → K)} {wX : List (Fin 5 → K)}
    (h7I : ∀ q ∈ pI, q.1 ⟨7, by norm_num⟩ = 0) (h7W : ∀ q ∈ pW, q.1 ⟨7, by norm_num⟩ = 0)
    (h7S : ∀ q ∈ pS, q.1 ⟨7, by norm_num⟩ = 0) (h7X : ∀ q ∈ pX, NotJ7 (p := p) q.1)
    (hprovS : provs .s = jProv b nodesJ orbitJ chalsJ pubsJ lay PJ ++
      (pI ++ pW ++ pX ++ pS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hextX : ext .x = wX ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    -- the IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation and the provider obligations
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Registry} (hRg : Rg.Faithful) (hD : DenOKX9 p D V)
    (hXp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .x (provs .x))
    (hPp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p (provs .p))
    (hPax : ProvP (p := p) (K := K) AxOK .p (provs .p))
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hsvc : ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ →
      (∀ c ∈ ext .s, c ∈ (pJ ++ pI ++ pW ++ pX ++ pS).map Prod.fst) →
      (∀ c ∈ ext .p, c ∈ (provs .p).map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s (pJ ++ pI ++ pW ++ pX ++ pS))
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the compute walk and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) n)
    (hreal : (stX9 (EN9 0)).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN9 0) xS) = some x.subject) (hf : D (hdV (EN9 0) xF) = some x.formula)
    (he : D (hdV (EN9 0) xE) = some x.result) : HoldsN x := by
  have B := bctx9_of_xctx C
  have hp20 : 20 < p := C.hp
  have hp3 : 3 < p := by omega
  have hp5 : 5 < p := by omega
  -- the other service providers
  obtain ⟨provO, hpO⟩ : ∃ l, l = pI ++ pW ++ pX ++ pS :=
    ⟨_, rfl⟩
  have hO7J : ∀ q ∈ provO, NotJ7 (p := p) q.1 := by
    intro q hq
    rw [hpO] at hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · exact notJ7_of_zero (by omega) (h7I q hq)
    · exact notJ7_of_zero (by omega) (h7W q hq)
    · exact h7X q hq
    · exact notJ7_of_zero (by omega) (h7S q hq)
  rw [← hpO] at hprovS
  -- denominators of the compute consumes
  have hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress CV (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ houtS _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .x (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .p (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hc := compReqsX9_sum B hne .s
  change _ = rhoX (b := b) (δ := δ) (pubVal := pubVal) .s at hc
  -- the compute's `s` consumes as `Fin 8` keys
  obtain ⟨cS, hcS⟩ : ∃ l : List (Fin 8 → K), l = compReqsX9 (K := K) hn nodes orbit chalV pubVal P .s :=
    ⟨_, rfl⟩
  have hc8 : (cS.map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum =
      rhoX (b := b) (δ := δ) (pubVal := pubVal) .s := by
    rw [hcS]; exact hc
  -- the J share
  have hG : Quad.mk _ (pubsJ 0) (pubsJ 1) +
      ((cS ++ pinCons (p := p) (K := K) regs idx ++ eA).map fun r =>
          (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) r))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chalsJ) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    have h3 := JGenJ8.jet_tagged_sumG hJk
    rw [hcJ] at h3 ⊢
    have hS' : rhoX (b := b) (δ := δ) (pubVal := pubVal) .s +
        (List.map (α := Fin 8 → K) (fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
        (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
          (compress CV (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := hbal .s
    rw [hprovS, hextS, List.map_append, List.map_append, List.map_append, List.sum_append, List.sum_append,
      List.sum_append] at hS'
    rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
    linear_combination hS' - h3 + hc8
  have houtJ : ((coinsJ δ chalsJ).gamma, (coinsJ δ chalsJ).pole) ∉
      IOFailureEventW (((cS ++ pinCons (p := p) (K := K) regs idx ++ eA) ++
          jCons b nodesJ orbitJ chalsJ pubsJ lay PJ).map (liftRec (L := 𝕂′)))
        (effP (Nock.Jet.SubJ8.liftS (δ := δ) (jProv b nodesJ orbitJ chalsJ pubsJ lay PJ ++ provO))) := by
    rw [hcJ, List.append_assoc, List.append_assoc]
    have h : ((CV).gamma, (CV).pole) ∉
        IOFailureEventW (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s)))
          (effP (liftP (m := 8) (provs .s))) := by
      rw [hcS]; exact houtS
    rw [hextS, hprovS, List.append_assoc] at h
    exact h
  have hcountJ : ((cS ++ pinCons (p := p) (K := K) regs idx ++ eA) ++
        jCons b nodesJ orbitJ chalsJ pubsJ lay PJ).length < p := by
    have h : (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s))).length < p := by
      rw [hcS]; exact hcount .s
    rw [hextS, List.length_map] at h
    change (cS ++ (pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ chalsJ pubsJ lay PJ)).length < p
      at h
    simp only [List.length_append] at h ⊢
    omega
  -- the effective provider family
  set provsE := withS provs (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO ++
    Nock.Jet.SubJ8.provOE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) with hprovsE
  have hbalE : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provsE ext := by
    intro bl
    cases bl with
    | x => exact hbal .x
    | p => exact hbal .p
    | s =>
      have he := Nock.Jet.SubJ8.balance_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
        (fun k => (compress CV k)⁻¹)
      simp only [Nock.Jet.SubJ8.liftS, List.map_map, Function.comp_def] at he
      have h0 : _ + (List.map (α := Fin 8 → K) (fun r => (compress CV
          (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
          (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
            (compress CV (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := hbal .s
      rw [hprovS, he] at h0
      exact h0
  have houtE : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provsE bl)) := by
    intro bl
    cases bl with
    | x => exact hout .x (by intro h; cases h)
    | p => exact hout .p (by intro h; cases h)
    | s =>
      have hl := Nock.Jet.SubJ8.liftS_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
      have hl' : liftP (p := p) (K := K) (δ := δ) (provsE .s) = effP (liftP (p := p) (K := K) (δ := δ) (provs .s)) := by
        rw [hprovS]; exact hl
      rw [hl']
      exact houtS
  have hsv := ext_served9 B hbalE houtE hcount
  -- the J providers
  have hXok : ProvP (p := p) (K := K) (RecOK D Rg (fun _ _ => (0, 0))) .x (provsE .x) := by
    intro q hq l hl hlt hk
    have h := hXp q hq l hl hlt hk (pre9_off (by decide))
    have hc0 : recClass (l, Bal.x) = 0 := rfl
    unfold RecOK9 at h
    rw [hc0, if_neg (by omega), if_neg (by omega)] at h
    exact h
  have hRd := Nock.Jet.RapJetJ8.rd_recOK (provsE .x) hXok fun c hc =>
    hsv .x c (by rw [hextX]; exact List.mem_append_right _ hc)
  have hJp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s
      (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) := by
    rcases hJk with ⟨hsatJ, hbindJ, hinjJ, hnJ, hadjJ⟩ | ⟨h0, -⟩
    · have hbalJ := SubJ9A.bal_of_serviceE9 hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7J hG houtJ hcountJ
      have hAcc := accepted_of_sat hsatJ hbindJ hinjJ hlay hsmall huniq hbalJ
      have hpinS := SubJ9A.pin_servedE9 hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7J hG houtJ hcountJ
        (regs := regs) (idx := idx) (fun y hy => List.mem_append_left _ (List.mem_append_right _ hy))
      have hReg := hRegP hAcc hpinS
      exact ProvKindsX9.jetProv9 hp5 hAcc hD.base hTpl hRd hReg provO
    · rw [JGenJ8.jProvE_nil h0]
      intro q hq
      cases hq
  -- the axis service at `jProvE ++ pI ++ pW ++ TAG_ax ++ pS`
  have hsvS : ∀ c ∈ ext .s, c ∈ (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO ++ pI ++ pW ++
        pX ++ pS).map Prod.fst := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hsv .s c hc)
    refine List.mem_map_of_mem ?_
    have hq' : q ∈ Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO ++
        Nock.Jet.SubJ8.provOE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJ) (pubs := pubsJ) (lay := lay) (P := PJ) provO := hq
    rcases List.mem_append.mp hq' with hJq | hOq
    · exact mem_shiftJ hJq
    · have hO := List.mem_of_mem_filter hOq
      rw [hpO] at hO
      exact mem_shift hO
  have h9 := hsvc _ hJp hsvS (hsv .p)
  have hO' : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s provO := by
    intro q hq
    refine h9 q ?_
    rw [hpO] at hq
    exact mem_shift hq
  have hprovE : ∀ bl, ProvP (p := p) (K := K) (RecOK9I D V Rg combN) bl (provsE bl) := by
    intro bl
    cases bl with
    | x => exact hXp
    | p => exact hPp
    | s => exact provP_append.mpr ⟨hJp, provP_filter _ hO'⟩
  have haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provsE bl) := by
    intro bl
    cases bl with
    | x => intro q _ l _ _ _; exact axOK_x l
    | p => exact hPax
    | s => intro q _ l _ _ _; exact axOK_s l
  exact acceptsJ9A_holdsN_computeI9 C hpG hRg hD hseed hα hw hbalE houtE hcount hprovE haxP hreal x hs hf he

/-- **S8 effective layer, axis chip PRESENT** (`hsvc` by `AxisSoundX9.provP_service9`). -/
theorem acceptsJ9A_holdsN_EIX9 [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hcJ : coinsJ δ chalsJ = CV)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the axis chip
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    -- the wiring
    {pI pW pS : List ((Fin 8 → K) × K)} {eA : List (Fin 8 → K)} {wX : List (Fin 5 → K)}
    (h7I : ∀ q ∈ pI, q.1 ⟨7, by norm_num⟩ = 0) (h7W : ∀ q ∈ pW, q.1 ⟨7, by norm_num⟩ = 0)
    (h7S : ∀ q ∈ pS, q.1 ⟨7, by norm_num⟩ = 0)
    (hprovS : provs .s = jProv b nodesJ orbitJ chalsJ pubsJ lay PJ ++
      (pI ++ pW ++ AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ pS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hextX : ext .x = wX ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ eA)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .p)
    -- the IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation and the provider obligations
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Registry} (hRg : Rg.Faithful) (hD : DenOKX9 p D V)
    (hXp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .x (provs .x))
    (hPp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p (provs .p))
    (hPax : ProvP (p := p) (K := K) AxOK .p (provs .p))
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the compute walk and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) n)
    (hreal : (stX9 (EN9 0)).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN9 0) xS) = some x.subject) (hf : D (hdV (EN9 0) xF) = some x.formula)
    (he : D (hdV (EN9 0) xE) = some x.result) : HoldsN x := by
  have hp5 : 5 < p := by have := C.hp; omega
  refine acceptsJ9A_holdsN_EIG9 C hpG hbal nodesJ orbitJ chalsJ pubsJ lay PJ hJk hcJ h7I h7W h7S
    (fun q hq => notJ7_of_tag (t := 5) hp5 (by norm_num) (by norm_num) (by omega)
      (axTag_entry7 b nodesX orbitX chalsX pubsX QX q hq))
    hprovS hextS hextX hout houtS hcount hRg hD hXp hPp hPax hI hW hS ?_ hlay hsmall huniq hTpl hRegP
    hseed hα hw hreal x hs hf he
  intro pJ hJp hsvS hsvP
  have hsubS' : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .s :=
    fun i => by rw [hextS]; exact List.mem_append_left _ (List.mem_append_right _ (hsubS i))
  exact AxisSoundX9.provP_service9 δ b hnX nodesX orbitX chalsX pubsX QX hpG hsatX hbindX hinjX hadjX Rg hD
    hJp hI hW hS hsvS hsubS' (fun a b' c d hr => recOK9I_p a b' c d hr) hsvP hsubP hPp

/-- **S8 effective layer, axis chip ABSENT** (no `TAG_ax` provider; `hsvc` is the plain append). -/
theorem acceptsJ9A_holdsN_EIA9 [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hcJ : coinsJ δ chalsJ = CV)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the wiring
    {pI pW pS : List ((Fin 8 → K) × K)} {eA : List (Fin 8 → K)} {wX : List (Fin 5 → K)}
    (h7I : ∀ q ∈ pI, q.1 ⟨7, by norm_num⟩ = 0) (h7W : ∀ q ∈ pW, q.1 ⟨7, by norm_num⟩ = 0)
    (h7S : ∀ q ∈ pS, q.1 ⟨7, by norm_num⟩ = 0)
    (hprovS : provs .s = jProv b nodesJ orbitJ chalsJ pubsJ lay PJ ++
      (pI ++ pW ++ [] ++ pS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ chalsJ pubsJ lay PJ)
    (hextX : ext .x = wX ++ jRd b nodesJ orbitJ chalsJ pubsJ lay PJ)
    -- the IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation and the provider obligations
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Registry} (hRg : Rg.Faithful) (hD : DenOKX9 p D V)
    (hXp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .x (provs .x))
    (hPp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p (provs .p))
    (hPax : ProvP (p := p) (K := K) AxOK .p (provs .p))
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ chalsJ pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the compute walk and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) n)
    (hreal : (stX9 (EN9 0)).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN9 0) xS) = some x.subject) (hf : D (hdV (EN9 0) xF) = some x.formula)
    (he : D (hdV (EN9 0) xE) = some x.result) : HoldsN x := by
  refine acceptsJ9A_holdsN_EIG9 (pX := []) C hpG hbal nodesJ orbitJ chalsJ pubsJ lay PJ hJk hcJ h7I h7W h7S
    (fun q hq => by simp at hq)
    hprovS hextS hextX hout houtS hcount hRg hD hXp hPp hPax hI hW hS ?_ hlay hsmall huniq hTpl hRegP
    hseed hα hw hreal x hs hf he
  intro pJ hJp _ _
  have hnil : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s ([] : List ((Fin 8 → K) × K)) :=
    fun q hq => by cases hq
  exact provP_append.mpr ⟨provP_append.mpr ⟨provP_append.mpr ⟨provP_append.mpr ⟨hJp, hI⟩,
    ProvNewX9.provP_I hW⟩, hnil⟩, ProvNewX9.provP_I hS⟩

end

end Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 in
#print axioms acceptsJ9A_holdsN_EIG9
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 in
#print axioms acceptsJ9A_holdsN_EIX9
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 in
#print axioms acceptsJ9A_holdsN_EIA9
