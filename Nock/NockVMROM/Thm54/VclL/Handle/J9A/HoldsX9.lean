/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HoldsX9.lean

* **`chainChild_state9`** — a twin row with an atom formula handle (`xF.k = 0`) is an old `s10L` / `s10T` row:
    on old states the J-8 gate (through `baseHoldsX_of_X9`); on `s0B` / `s10B` the twin's `svXFX9` reads
    `xF.k − 1 + s10L + s10T = 0`; on `s10S` it reads `(xF.k − 2)(xF.k − 3) = 0` (obligation 3, halving).
  * **`halvingOK_of_child9`**, **`halving_of_tree9I`** — `HalvingOK` at every old `s10L` node of the walk tree
    (obligation 3).
  * **`holdsN_of_walk9I`** — the walk tree (`WalkTreeX9.tree_of_goal9`) with the guarded row semantics
    (`RowSemSatX9.rowSemX9I_of_chip`) and the label link over the 20 states (obligation 4), through
    `LocalVSX9I.holdsN_of_rowsVSX9I`.
  * **`acceptsJ9A_holdsN_computeI9`** — the twin of `RowSemIJ8.acceptsJ8_holdsN_computeI` at `computeChipVCLHX9`:
    an accepted twin compute trace (`RapWalkX9.XCtx`), the compute balance identity, outside the compute IO
    events, with the providers' guarded obligation `ProvP (RecOK9I D V R combN)` and the path axis obligation
    `ProvP AxOK`, proves `HoldsN` of the claim the root row denotes (obligation 5 through
    `TeleX9.servedP_of_balancesJ9`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WalkBridgeX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemSatX9
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9

open Nock Nock.Reified Nock.Edit Nock.Walk
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc prodL)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (HalvingOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.Jet (Registry HoldsN)

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The chain child (obligation 3) -/

theorem natCast_ne_zero_of_lt {k : ℕ} (hk0 : k ≠ 0) (hk : k < p) : ((k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hk0 (Nat.eq_zero_of_dvd_of_lt h hk)

/-- **A twin row with an atom formula handle is an old `s10L` / `s10T` row.** -/
theorem chainChild_state9 (hp : 6 < p) {env : Env (ZMod p)} (hB : BaseHoldsX9 env) {cs : CSt}
    (hOH : OneHotAt9 env (csIdx cs)) (hk : env.trace xF.k = 0) :
    cs = .old .s10L ∨ cs = .old .s10T := by
  have hsv := arith_of_base9 hB (g := svXFX9) (by decide +kernel)
  cases cs with
  | old st =>
    have hN := hOH.newOff (stIdx_lt st)
    have hB8 := baseHoldsX_of_X9 hB hN
    have hOH8 : OneHotAt env (stIdx st) := fun i hi =>
      hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
    rcases HalvingTreeJ8.chainChild_state hB8 hOH8 hk with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  | s0B =>
    exfalso
    have h12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (by decide)
    have h13 : env.trace sS10T = 0 := hOH.zero (by decide +kernel) (by decide)
    have h25 : env.trace sS10S = 0 := hOH.zero (by decide +kernel) (by decide)
    simp only [svXFX9, svXF8, oneMinus, prodL, List.foldr, cc, evalQX, h12, h13, h25, hk] at hsv
    norm_num at hsv
  | s10B =>
    exfalso
    have h12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (by decide)
    have h13 : env.trace sS10T = 0 := hOH.zero (by decide +kernel) (by decide)
    have h25 : env.trace sS10S = 0 := hOH.zero (by decide +kernel) (by decide)
    simp only [svXFX9, svXF8, oneMinus, prodL, List.foldr, cc, evalQX, h12, h13, h25, hk] at hsv
    norm_num at hsv
  | s10S =>
    exfalso
    have h25 : env.trace sS10S = 1 := hOH.one (by decide +kernel)
    simp only [svXFX9, svXF8, oneMinus, prodL, List.foldr, cc, evalQX, h25, hk] at hsv
    have h6 : ((6 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hsv
    exact natCast_ne_zero_of_lt (by norm_num) hp h6

/-- **`HalvingOK` on an `s10L` parent from its twin chain child** (twin of `halvingOK_of_child`). -/
theorem halvingOK_of_child9 (hp : 2 ^ 63 + 1 < p) {pe ce : Env (ZMod p)} (hB : BaseHoldsX9 ce)
    {csc : CSt} (hOH : OneHotAt9 ce (csIdx csc)) (hk : ce.trace xF.k = 0)
    (hv : ce.trace xF.v = pe.trace vX)
    (hax : csc = .old .s10L → 2 ≤ (ce.trace xM.v).val ∧ (ce.trace xM.v).val < 2 ^ 62) :
    HalvingOK pe .s10L := by
  rcases chainChild_state9 (by omega) hB hOH hk with rfl | rfl
  · have hN := hOH.newOff (stIdx_lt .s10L)
    have hOH8 : OneHotAt ce (stIdx .s10L) := fun i hi =>
      hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
    exact HalvingTreeJ8.halvingOK_of_child hp (baseHoldsX_of_X9 hB hN) hOH8 hk hv (fun _ => hax rfl)
  · have hN := hOH.newOff (stIdx_lt .s10T)
    have hOH8 : OneHotAt ce (stIdx .s10T) := fun i hi =>
      hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
    exact HalvingTreeJ8.halvingOK_of_child hp (baseHoldsX_of_X9 hB hN) hOH8 hk hv (fun h => by cases h)

/-! ## 2. The tree -/

section Tree
variable {K : Type} [Field K]

/-- **The per-row hypotheses of the twin extraction at the guarded obligation `RecOK9I`.** -/
structure RowsAccX9I (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → CSt) (D : HX → Option Noun)
    (V : ℕ → Option ℕ) (R : Registry) : Prop where
  base : ∀ r < n, BaseHoldsX9 (E r)
  oh : ∀ r < n, OneHotAt9 (E r) (csIdx (st r))
  served : ∀ r < n, ∀ x ∈ activeX9 (E r), RecOK9I D V R combN x
  ax : ∀ r < n, st r = .old .s10L → 2 ≤ ((E r).trace xM.v).val ∧ ((E r).trace xM.v).val < 2 ^ 62

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → CSt} {D : HX → Option Noun} {V : ℕ → Option ℕ}
  {R : Registry}

/-- **`HalvingOK` at every old `s10L` node of the twin walk tree** (twin of `halving_of_treeI`). -/
theorem halving_of_tree9I (hp : 2 ^ 63 + 1 < p) (A : RowsAccX9I n E st D V R)
    {t : NTree (CSt × RowVSX9)}
    (hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf9 (rowsWX9 E st) i)
    (hlink : ∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX9 u.label.2)
    {u : NTree (CSt × RowVSX9)} (hu : InTree t u) {i : ℕ} (hui : u.label = lblOf9 (rowsWX9 E st) i)
    (hs : st (i - 1) = .old .s10L) : HalvingOK (E (i - 1)) .s10L := by
  have hl := hlink u hu
  rw [hui] at hl
  simp only [lblOf9, rowsWX9, hs, kidsX9_rowW9_s10L] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_map, List.length_cons, List.length_nil] at hlen
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  rw [hc] at hl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  have hcin : InTree t c := inTree_trans hu (InTree.sub (by rw [hc]; simp) (InTree.here _))
  obtain ⟨j, hj1, hjn, hcj⟩ := hrow c hcin
  rw [hcj] at hl
  simp only [lblOf9, rowsWX9] at hl
  rw [rowW9_trip] at hl
  simp only [rowOfX9, RowVSX9.trip, rowOfX, RowVSX.trip, hdV, Prod.mk.injEq] at hl
  obtain ⟨-, ⟨hk, hv⟩, -⟩ := hl
  exact halvingOK_of_child9 hp (A.base _ (by omega)) (A.oh _ (by omega)) (ZMod.val_eq_zero _ |>.mp hk)
    (ZMod.val_injective _ hv) (A.ax _ (by omega))

/-- **`holdsN_of_walkJ8I` at the twin** (design S8, tree half): an accepted twin compute walk whose rows meet
`RowsAccX9I` and whose root is a real row denoting the claim proves `HoldsN` of the claim. -/
theorem holdsN_of_walk9I [CharP K p] (hpG : p = Nock.Atoms.p) (hR : R.Faithful) (hD : DenOKX9 p D V)
    (hn : 1 ≤ n) (A : RowsAccX9I n E st D V R)
    (hG : ForestReconGoal (stVS9 K) (lblOf9 (rowsWX9 E st)) 1 n)
    (hreal : (st 0).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : HoldsN x := by
  classical
  have hp : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨t, hroot, hrow, hlink⟩ :=
    tree_of_goal9 (K := K) p hp0 (rowsWX9 E st) hn (fun i _ _ => ⟨smallR9_rowW9 _ _, wf9_rowW9 _ _⟩) hG
  let rw : CSt × RowVSX9 → RowVSX9 := fun l =>
    if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf9 (rowsWX9 E st) i then
      rowOfX9 (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf9 (rowsWX9 E st) i ∧
      rw u.label = rowOfX9 (E (i - 1)) (st (i - 1)) := by
    intro u hu
    have h := hrow u hu
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [rw, dif_pos h]⟩
  have hrt : rw t.label = rowOfX9 (E 0) (st 0) := by
    have h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t.label = lblOf9 (rowsWX9 E st) i := ⟨1, le_rfl, hn, hroot⟩
    have h1 : Nat.find h = 1 := le_antisymm (Nat.find_min' h ⟨le_rfl, hn, hroot⟩) (Nat.find_spec h).1
    simp only [rw, dif_pos h, h1]
  have hok : RowsOKX9I rw p D V R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      rw [hrw]
      refine rowSemX9I_of_chip hpG hD (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
        (A.served _ (by omega)) (fun st' hcs hs10 => ?_)
      subst hs10
      exact halving_of_tree9I hp A hrow hlink hu hui hcs rfl
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (rw c.label).trip) = u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf9, rowsWX9, rowW9_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf9, rowsWX9]
      by_cases hs : st (i - 1) = .old .s10L
      · have hH := halving_of_tree9I hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX9_rowW9_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW9_of_ne _ hs]
  exact holdsN_of_rowsVSX9I rw hR hD t hok (by rw [hrt]; exact hreal) x (by rw [hrt]; exact hs)
    (by rw [hrt]; exact hf) (by rw [hrt]; exact he)

end Tree

/-! ## 3. The compute assembly -/

section Accept
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 ProvP AxOK liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (tileSet)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (encT)
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.StrictExtension
open Polynomial Module
variable [DecidableEq (ZMod p)] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN9" => CompReqsX9.envsN9 hn nodes orbit chalV pubVal P
local notation "CV" => coinsCV b δ chalV

/-- The balance context of an accepted twin trace (`oh` from `ohE9`). -/
theorem bctx9_of_xctx {α γ seed : K} (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) :
    BCtx9 hn nodes b δ chalV pubVal orbit P :=
  ⟨charX9 C, C.hsat, C.hinj, C.hadj, fun _ hr => ⟨_, csIdx_mem _, ohE9 C hr⟩⟩

/-- **`ax_of_axOK` at an old `s10L` twin row.** -/
theorem ax_of_axOK9 {env : Env (ZMod p)} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env (csIdx (.old .s10L)))
    (hA : ∀ x ∈ activeX9 env, AxOK x) :
    2 ≤ (env.trace xM.v).val ∧ (env.trace xM.v).val < 2 ^ 62 := by
  have hN := hOH.newOff (stIdx_lt .s10L)
  have hOH8 : OneHotAt env 12 := fun i hi => hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
  exact ServedJ8.ax_of_axOK (baseHoldsX_of_X9 hB hN) hOH8 (fun x hx => hA x (by rw [activeX9_eq hN]; exact hx))

/-- **Design S8, compute half, guarded** (twin of `RowSemIJ8.acceptsJ8_holdsN_computeI`): the provider
obligation is `hprov : ProvP (RecOK9I D V R combN)`. -/
theorem acceptsJ9A_holdsN_computeI9 [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
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
    (hprov : ∀ bl, ProvP (p := p) (K := K) (RecOK9I D V R combN) bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX9 (EN9 0)).sem.isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN9 0) xS) = some x.subject) (hf : D (hdV (EN9 0) xF) = some x.formula)
    (he : D (hdV (EN9 0) xE) = some x.result) : HoldsN x := by
  have hp4 : 4 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have B := bctx9_of_xctx C
  have hOK := servedP_of_balancesJ9 B hp4 hbal hout hcount hprov
  have hAx := servedP_of_balancesJ9 B hp4 hbal hout hcount haxP
  obtain ⟨hbase, hoh⟩ := base_oh_of_sat9 C
  have A : RowsAccX9I n (fun r => EN9 r) (fun r => stX9 (EN9 r)) D V R :=
    { base := hbase
      oh := hoh
      served := hOK
      ax := fun r hr hst => by
        have h12 := hoh r hr
        rw [hst] at h12
        exact ax_of_axOK9 (hbase r hr) h12 (hAx r hr) }
  exact holdsN_of_walk9I (K := K) hpG hR hD hn A (goalJ9A C hseed hα hw) hreal x hs hf he

end Accept

end Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9

open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9 in
#print axioms chainChild_state9
open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9 in
#print axioms halving_of_tree9I
open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9 in
#print axioms holdsN_of_walk9I
open Nock.NockVMROM.Thm54.VclL.Handle.HoldsX9 in
#print axioms acceptsJ9A_holdsN_computeI9
