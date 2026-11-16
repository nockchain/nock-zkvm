/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/TwinRowSemIJ8.lean

 Extraction twins of the compute-half theorems of `RowSemIJ8`. Each twin has the hypotheses of the source theorem and
 a conclusion that also exposes the intermediate objects the source proof builds and then discards.

 * `genuineTree_of_walkJ8I`: from `RowsAccXI`, the forest goal and a root whose handles denote the claim, there
 is a row tree whose labels are the rows of the compute walk, which satisfies `RowsOKX` under the first-row
 relabelling `relabX`, and whose decoded form is `GenuineNX`.
 * `acceptsJ8_holdsN_computeI_ex`: `acceptsJ8_holdsN_computeI` returning the row accumulator `RowsAccXI`, the
 forest goal, and the tree of `genuineTree_of_walkJ8I`, together with `HoldsN`.
 The corollaries `holdsN_of_walkJ8I_of_twin` and `acceptsJ8_holdsN_computeI_of_ex` re-derive the source theorems.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8

open Nock Nock.Reified Nock.Edit Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
open Nock.Jet (Registry)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8

noncomputable section

section Tree2
open Nock.Walk Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8 (halvingOK_of_child)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun}
  {R : Nock.Jet.Registry} {comb : ℕ → Noun}

open scoped Classical in
/-- The first-row relabelling: a label that is the label of some row `i` in `[1, n]` is read as the row at the
first such `i`; any other label keeps its own row. -/
def relabX (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (l : StateX × RowVSX) : RowVSX :=
  if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf (rowsWX E st) i then
    rowOfX (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2

/-- The tree and facts exposed by `genuineTree_of_walkJ8I`. -/
def TreeFacts (K : Type) (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (D : HX → Option Noun)
    (R : Nock.Jet.Registry) : Prop :=
  ∃ t : NTree (StateX × RowVSX),
    (t.label = lblOf (rowsWX E st) 1 ∧
      (∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i) ∧
      (∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX u.label.2)) ∧
    relabX n E st t.label = rowOfX (E 0) (st 0) ∧
    RowsOKX (relabX n E st) p D R t ∧
    GenuineNX R (mapT (fun l => rx D (relabX n E st l)) t)

/-- **`holdsN_of_walkJ8I`, with the tree exposed**: the tree of row labels, the first-row relabelling's
`RowsOKX`, and the `GenuineNX` of the decoded tree. -/
theorem genuineTree_of_walkJ8I [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D)
    (hn : 1 ≤ n) (A : RowsAccXI n E st D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hreal : (st 0).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : TreeFacts K n E st D R := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨t, hroot, hrow, hlink⟩ :=
    tree_of_goal (K := K) p hp0 (rowsWX E st) hn (fun i _ _ => smallR_rowW _ _) hG
  let rw : StateX × RowVSX → RowVSX := fun l =>
    if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf (rowsWX E st) i then
      rowOfX (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      rw u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    have h := hrow u hu
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [rw, dif_pos h]⟩
  have hrt : rw t.label = rowOfX (E 0) (st 0) := by
    have h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t.label = lblOf (rowsWX E st) i := ⟨1, le_rfl, hn, hroot⟩
    have h1 : Nat.find h = 1 := le_antisymm (Nat.find_min' h ⟨le_rfl, hn, hroot⟩) (Nat.find_spec h).1
    simp only [rw, dif_pos h, h1]
  have hok : RowsOKXI rw p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      rw [hrw]
      exact rowSemXI_of_chip hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
        (A.served _ (by omega)) (fun hs => halving_of_treeI hp A hrow hlink hu hui hs rfl)
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (rw c.label).trip) = u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_treeI hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]

  have hs' : D (rw t.label).s = some x.subject := by rw [hrt]; exact hs
  have hrow' : RowsOKX rw p D R t := rowsOKX_of_I rw hD t hok (by simp [hs'])
  exact ⟨t, ⟨hroot, hrow, hlink⟩, hrt, hrow', genuineNX_of_rowsX rw hD t hrow' (by simp [hs'])⟩

/-- Sanity: the twin implies `holdsN_of_walkJ8I`. -/
theorem holdsN_of_walkJ8I_of_twin [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D)
    (hn : 1 ≤ n) (A : RowsAccXI n E st D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hreal : (st 0).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  obtain ⟨t, -, hrt, hrow, -⟩ := genuineTree_of_walkJ8I (K := K) hp hR hD hn A hG hreal x hs hf he
  exact holdsN_of_rowsVSX (relabX n E st) hR hD t hrow (by rw [hrt]; exact hreal) x (by rw [hrt]; exact hs)
    (by rw [hrt]; exact hf) (by rw [hrt]; exact he)

end Tree2

section Accept
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8 (bctx_of_xctx goalJ8)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P
local notation "CV" => coinsCV b δ chalV

/-- **`acceptsJ8_holdsN_computeI`, with the intermediate objects exposed**: the row accumulator, the forest
goal, the row tree of `genuineTree_of_walkJ8I`, and `HoldsN`. -/
theorem acceptsJ8_holdsN_computeI_ex [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hR : R.Faithful) (hD : DenOKX p D)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (hprov : ∀ bl, ProvP (p := p) (K := K) (RecOKI D R comb) bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX (EN 0)).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN 0) xS) = some x.subject) (hf : D (hdV (EN 0) xF) = some x.formula)
    (he : D (hdV (EN 0) xE) = some x.result) :
    RowsAccXI n (fun r => EN r) (fun r => stX (EN r)) D R comb ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) 1 n ∧
    TreeFacts K n (fun r => EN r) (fun r => stX (EN r)) D R ∧ Nock.Jet.HoldsN x := by
  have hp4 : 4 < p := by omega
  have B := bctx_of_xctx C
  have hOK := servedP_of_balancesJ8 B hp4 hbal hout hcount hprov
  have hAx := servedP_of_balancesJ8 B hp4 hbal hout hcount haxP
  obtain ⟨hbase, hoh⟩ := base_oh_of_sat C
  have A : RowsAccXI n (fun r => EN r) (fun r => stX (EN r)) D R comb :=
    { base := hbase
      oh := hoh
      served := hOK
      ax := fun r hr hst => by
        have h12 := hoh r hr
        rw [hst] at h12
        exact ax_of_axOK (hbase r hr) h12 (hAx r hr) }
  have hG := goalJ8 C hseed hα hw
  exact ⟨A, hG, genuineTree_of_walkJ8I (K := K) hp hR hD hn A hG hreal x hs hf he,
    holdsN_of_walkJ8I (K := K) hp hR hD hn A hG hreal x hs hf he⟩

/-- Sanity: the twin implies `acceptsJ8_holdsN_computeI`. -/
theorem acceptsJ8_holdsN_computeI_of_ex [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hR : R.Faithful) (hD : DenOKX p D)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (hprov : ∀ bl, ProvP (p := p) (K := K) (RecOKI D R comb) bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX (EN 0)).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN 0) xS) = some x.subject) (hf : D (hdV (EN 0) xF) = some x.formula)
    (he : D (hdV (EN 0) xE) = some x.result) : Nock.Jet.HoldsN x :=
  (acceptsJ8_holdsN_computeI_ex C hp hR hD hseed hα hw hbal hout hcount hprov haxP hreal x hs hf he).2.2.2

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8.genuineTree_of_walkJ8I
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8.acceptsJ8_holdsN_computeI_ex
