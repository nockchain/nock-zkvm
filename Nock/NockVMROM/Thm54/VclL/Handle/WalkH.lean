/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkH.lean

**Which label:** the walk's label KEEPS its fingerprints (`fp node`, `fp root`,
  W1's `enc`), because the priced walk event `walkEvent` and its injectivity
  (`Walk_IOP_forest_final_card_of_label`, label determination through `enc`) are stated over those
  labels; changing the label would change the priced event.  The twin EXPORTS handles:
  each walk row also consumes the cell table's handle-export record `(idx, kL, vL, kR, vR)` (the
  record `ProvideH.cellTemplateH` provides) and provides two handle walk records
  `(rootIdx, 2·prefix + b, k_b, v_b)` (`ChipH.walkRec`'s shape).

  * `enc_inj_decoded_or_atom` — outside T2 ∪ the dyck-root event, `enc z` is injective on the
    decoded nouns together with the atom children (the atom/atom case by `leaf`, values `< p`);
  * `walkH_of_reconGoal` — the model form: under the walk's ForestReconGoal (the existing chain
    argument, `chain_sound`, nothing new priced), every handle record a row emits names, through
    `denH`, the slot `/[2·prefix + b]` of its root `denH (1, rootIdx)`;
  * `walkTemplateH` / `walkChipH` — the twin: `walkTemplate` + `kL vL kR vR` (base `21..24`) + five
    `𝕂`-roles (handle-export consume inverse, two handle-record provide inverses, two accumulators);
    **MEASURED `w = 151` (`walkChipH_width`)**.  It keeps the fingerprint path-record provides of the
    original (they become vestigial: nothing consumes them at VCLH); without them the width would be
    `151 − 18 = 133` (UNCONFIRMED: no chip is built for that variant, the restriction route below
    needs the original's gates intact);
  * `walkH_records_genuine` — the chip form (twin of `records_genuine_of_chip`): the restriction of
    a twin-accepted trace is walk-chip accepted (`ProvideH.expandChip_restrict`), so W1/W2/W3's
    theorems apply unchanged; at the walk coins outside the SAME `walkEvent`, every handle record
    the twin provides is genuine.  Remaining inputs, as `records_genuine_of_chip`'s: table-side
    (`TableAccepts`, T2, dyck, `KeysExported`) and the handle-export lookup's existence form `hHX`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ProvideH
import Nock.NockVMROM.Thm54.VclL.Chips.WalkAcceptW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Fingerprint injectivity on decoded nouns and atom children -/

section Model
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]
  [Fact q.Prime]

theorem enc_inj_decoded_or_atom (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {tb : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0))) {a c : Noun}
    (ha : a ∈ decodedNouns (tb.map (·.b0)) ∨ a ∈ AtomChildren tb)
    (hc : c ∈ decodedNouns (tb.map (·.b0)) ∨ c ∈ AtomChildren tb)
    (he : GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z c) : a = c := by
  have hinj := decodedNouns_inj_of_not_mem hq hz h [] hT2
  have hatom := hatom_of_not_mem_dyck hq hz h hdy
  rcases ha with ha | ha <;> rcases hc with hc | hc
  · exact hinj a ha c hc he
  · exact absurd he.symm (hatom c hc a ha)
  · exact absurd he (hatom a ha c hc)
  · have hat : ∀ n ∈ AtomChildren tb, ∃ x : ZMod q, n = .atom x.val := by
      rintro n ⟨r, -, hr⟩
      rcases hr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
    obtain ⟨x, rfl⟩ := hat a ha
    obtain ⟨y, rfl⟩ := hat c hc
    haveI : CharP Kfp q := charP_of_injective_algebraMap (algebraMap (ZMod q) Kfp).injective q
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    have hl := congrArg FP.leaf he
    rw [GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom] at hl
    have hcast : ((x.val : ℕ) : Kfp) = ((y.val : ℕ) : Kfp) := hl
    have hmod := (CharP.natCast_eq_natCast Kfp q).mp hcast
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at hmod
    rw [hmod]

/-- **The handle walk records of a row, model form.**  Under the walk's `ForestReconGoal` (with
the root gate and exported keys, outside T2 ∪ the dyck-root event), for every row `i`, every key
`k` with the row's node, every handle-export record served at `k`'s serial, and every side `b`:
the handle record `(rootIdx, 2·prefix + b, h_b)` names a slot of its root through `denH`. -/
theorem walkH_of_reconGoal (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {tb : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    {X : List (XKey Kfp)} (hX : KeysExported tb X)
    {lbl : ℕ → LT q Kfp} {kroots hh : ℕ} (hk : 1 ≤ kroots) (hRG : RootGate X lbl kroots)
    (hG : ForestReconGoal (stateSep (q := q) X 62) lbl kroots hh) :
    ∀ i, 1 ≤ i → i ≤ hh → ∀ k ∈ X, k.1 = (lbl i).2.node → ∀ hl hr : VHandle,
      (∃ c ∈ tb, (k.2.2.2, hl, hr) = exportRec c.b0) → ∀ b : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (lbl i).2.ridx = (ri : ZMod q) ∧
        denH (tb.map (·.b0)) (true, ri) = some rt ∧
        denH (tb.map (·.b0)) (if b then hr else hl) = some nn ∧
        Noun.slot (2 * (lbl i).2.pre + bitZ b).val rt = some nn := by
  have hq' : 2 ^ (62 + 1) ≤ q := by omega
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro i hi1 hih k hkX hki hl hr ⟨c', hc', hrec⟩ b
  obtain ⟨ρ, hρ1, hρk, es, hesX, -, hax, hroot, hridx, hend⟩ :=
    chain_tuple_of_reconGoal hq' hk (fun j hj1 hjk => (hRG j hj1 hjk).1) hG i hi1 hih k hkX hki b
  obtain ⟨-, k0, hk0, hk0n, hk0i⟩ := hRG ρ hρ1 hρk
  obtain ⟨c, hc, hci, hcp, -, -⟩ := hX k0 hk0
  obtain ⟨L, R, hdec, hp, -⟩ := row_genuine hq hz h hc
  have hpe : (lbl ρ).2.node = GlobalCarryRecognizer.enc z (.cell L R) := by
    rw [← hk0n, ← hcp, hp]
  rw [hpe] at hend
  have hexp : ∀ e ∈ es, EdgeExported tb e := by
    intro e he
    obtain ⟨c'', hc'', h1, h2, h3, h4⟩ := hX _ (hesX e he)
    exact ⟨c'', hc'', h1, h2, h3, h4⟩
  obtain ⟨nn, hnn, -, hslot, hmem⟩ := chain_sound hq hz h
    (decodedNouns_inj_of_not_mem hq hz h [] hT2) (hatom_of_not_mem_dyck hq hz h hdy) es
    (.cell L R) (Or.inl (mem_decodedNouns_of hdec)) hexp _ hend
  -- the handle row is the key's row (functional serials)
  obtain ⟨c1, hc1, hc1i, -, hc1l, hc1r⟩ := hX k hkX
  have hidx : c'.b0.idx = k.2.2.2 := (congrArg Prod.fst hrec).symm
  have hcc : c1 = c' := serial_functional_rows h.serial hc1 hc' (by rw [hc1i, hidx])
  subst hcc
  have hlr : hl = hL c1.b0 ∧ hr = hR c1.b0 := by
    have := congrArg Prod.snd hrec
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨L1, R1, hd1, -, hl1, hr1, hLw, hLa, hRw, hRa⟩ := row_genuine hq hz h hc1
  have hdL : denH (tb.map (·.b0)) (hL c1.b0) = some L1 := by
    unfold hL
    cases hw : c1.b0.wL
    · simp [denH, hLa hw]
    · simp [denH, hLw hw]
  have hdR : denH (tb.map (·.b0)) (hR c1.b0) = some R1 := by
    unfold hR
    cases hw : c1.b0.wR
    · simp [denH, hRa hw]
    · simp [denH, hRw hw]
  have hmL : L1 ∈ decodedNouns (tb.map (·.b0)) ∨ L1 ∈ AtomChildren tb := by
    cases hw : c1.b0.wL
    · exact Or.inr ⟨c1, hc1, Or.inl ⟨hw, hLa hw⟩⟩
    · exact Or.inl (mem_decodedNouns_of (hLw hw))
  have hmR : R1 ∈ decodedNouns (tb.map (·.b0)) ∨ R1 ∈ AtomChildren tb := by
    cases hw : c1.b0.wR
    · exact Or.inr ⟨c1, hc1, Or.inr ⟨hw, hRa hw⟩⟩
    · exact Or.inl (mem_decodedNouns_of (hRw hw))
  refine ⟨c.b0.idx, .cell L R, nn, by rw [hridx, hk0i, hci], hdec, ?_, by rw [hax]; exact hslot⟩
  rw [hlr.1, hlr.2]
  cases b
  · have htg : tgt k false = GlobalCarryRecognizer.enc z L1 := by
      show k.2.1 = _; rw [← hc1l, hl1]
    have := enc_inj_decoded_or_atom hq hz h hT2 hdy hmem hmL (by rw [hnn, htg])
    simp only [Bool.false_eq_true, ↓reduceIte, hdL, this]
  · have htg : tgt k true = GlobalCarryRecognizer.enc z R1 := by
      show k.2.2.1 = _; rw [← hc1r, hr1]
    have := enc_inj_decoded_or_atom hq hz h hT2 hdy hmem hmR (by rw [hnn, htg])
    simp only [↓reduceIte, hdR, this]

end Model

/-! ## 2. The walk twin `walkTemplateH` -/

namespace WalkHC

section Gates
variable {F : Type} [Field F]

/-- Base columns of the child handles (after the original's `21`). -/
def kL : ℕ := 21
def vL : ℕ := 22
def kR : ℕ := 23
def vR : ℕ := 24
/-- `𝕂`-roles after the original's `37`. -/
def hxInv : ℕ := 37
def hpInvL : ℕ := 38
def hpInvR : ℕ := 39
def hxAcc : ℕ := 40
def hpAcc : ℕ := 41
/-- Terminal publics (`𝕂` leaves; UNCONFIRMED frame wiring, as the coins `hGam`, `hRho`). -/
def pubX : ℕ := 4
def pubP : ℕ := 5

/-- The consumed handle-export key `(idx, kL, vL, kR, vR)`. -/
def xKeyH : List (CoeffExpr F) := [cv WChip.idx, cv kL, cv vL, cv kR, cv vR]
/-- The provided handle walk records `(rootIdx, 2·prefix + b, k_b, v_b)`. -/
def recLH : List (CoeffExpr F) := [cv WChip.ridx, .mul (.const 2) (cv WChip.pre), cv kL, cv vL]
def recRH : List (CoeffExpr F) :=
  [cv WChip.ridx, .add (.mul (.const 2) (cv WChip.pre)) (.const 1), cv kR, cv vR]

abbrev vK (r : ℕ) : MixedExpr F := .Var .traceCur r
abbrev vKn (r : ℕ) : MixedExpr F := .Var .traceNext r

def pTermH (cur : Bool) : MixedExpr F :=
  if cur then .Add (.Scale (cv WChip.mL) (vK hpInvL)) (.Scale (cv WChip.mR) (vK hpInvR))
  else .Add (.Scale (nv WChip.mL) (vKn hpInvL)) (.Scale (nv WChip.mR) (vKn hpInvR))

/-- **The handle gates** (`𝕂`, `9`): three inverses, two accumulators' init / step / terminal. -/
def gates : List (MixedExpr F) :=
  [ .Sub (.Mul (vK hxInv) (CellH.denKey xKeyH)) (.Const 1),
    .Sub (.Mul (vK hpInvL) (CellH.denKey recLH)) (.Const 1),
    .Sub (.Mul (vK hpInvR) (CellH.denKey recRH)) (.Const 1),
    .Scale (cv WChip.isF) (.Sub (vK hxAcc) (vK hxInv)),
    .Scale (notE (cv WChip.isL)) (.Sub (.Sub (vKn hxAcc) (vK hxAcc)) (vKn hxInv)),
    .Scale (cv WChip.isL) (.Sub (vK hxAcc) (.Var .publicVal pubX)),
    .Scale (cv WChip.isF) (.Sub (vK hpAcc) (pTermH true)),
    .Scale (notE (cv WChip.isL)) (.Sub (.Sub (vKn hpAcc) (vK hpAcc)) (pTermH false)),
    .Scale (cv WChip.isL) (.Sub (vK hpAcc) (.Var .publicVal pubP)) ]

/-- Booleanity of the two kind bits. -/
def baseH : List (CoeffExpr F) := [boolE (cv kL), boolE (cv kR)]

theorem gates_deg_all : (gates (F := F)).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, pTermH, CellH.denKey, CellH.rlcH, xKeyH, recLH, recRH, MixedExpr.degree,
    CoeffExpr.degree]

theorem mixed_deg (δF : F) (kroots : ℕ) :
    ∀ g ∈ WChip.mixedGates δF kroots ++ gates (F := F), g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact walkMixed_deg δF kroots g hg
  · simpa using List.all_eq_true.mp gates_deg_all g hg

theorem base_deg (kroots : ℕ) : ∀ g ∈ WChip.baseGates (F := F) kroots ++ baseH, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact walkBase_deg kroots g hg
  · simp [baseH] at hg; rcases hg with rfl | rfl <;> simp [CoeffExpr.degree]

end Gates

end WalkHC

section Template
variable {F : Type} [Field F]

/-- **The walk twin template**: base `25 / 0 / 0`, `𝕂`-roles `0 / 24 / 18`. -/
def walkTemplateH (δF : F) (kroots : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![25, 0, 0]
  extColsOf := ![0, 24, 18]
  baseTransition := WChip.baseGates kroots ++ WalkHC.baseH
  extTransition := []
  mixedTransition := WChip.mixedGates δF kroots ++ WalkHC.gates
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := WalkHC.base_deg kroots
  extTransition_deg := by simp
  mixedTransition_deg := WalkHC.mixed_deg δF kroots
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem walkTemplateH_baseCols (δF : F) (kroots : ℕ) : (walkTemplateH δF kroots).baseCols = 25 := by
  show (∑ r : Fin 3, (![25, 0, 0] : Fin 3 → ℕ) r) = 25
  decide
theorem walkTemplateH_extCols (δF : F) (kroots : ℕ) : (walkTemplateH δF kroots).extCols = 42 := by
  show (∑ r : Fin 3, (![0, 24, 18] : Fin 3 → ℕ) r) = 42
  decide

theorem walkBase_below (kroots : ℕ) : ∀ g ∈ WChip.baseGates (F := F) kroots, colsBelow 21 g = true := by
  intro g hg
  simp only [WChip.baseGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hg
  rcases hg with (h | h | h | h | h | h | h | h | h | h | h | h | h) | ⟨i, hi, rfl⟩
  all_goals first
    | (subst h; simp [colsBelow, WChip.isF, WChip.isL, WChip.rM, WChip.idx, WChip.pre, WChip.ridx,
        WChip.len, WChip.cL, WChip.cR, WChip.e, WChip.q, WChip.qinv, WChip.u, WChip.bt, WChip.bit0];
        done)
    | (subst h
       have hb := colsBelow_bitSum (F := F) 21 WChip.bit0 6 (by simp [WChip.bit0])
       simp [colsBelow, hb, WChip.len]; done)
    | (simp [colsBelow, boolE, WChip.bit0]; exact decide_eq_true (by omega))

theorem walkMixed_below (δF : F) (kroots : ℕ) :
    ∀ g ∈ WChip.mixedGates δF kroots, mixBelow 37 21 g = true := by
  have hall : (WChip.mixedGates δF kroots).all (mixBelow 37 21) = true := by
    simp [WChip.mixedGates, WChip.walkGates, WChip.qEqs, WChip.xKey, WChip.recL, WChip.recR,
      WChip.pTerm, WChip.curW, WChip.childLW, WChip.childRW, WChip.afoW, WChip.ccW, WChip.αk,
      WChip.αE, WChip.γE, WChip.rlcW, WChip.sumME, WChip.vecAt, List.ofFn_succ, QE.gates, QE.var,
      QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale,
      QE.rlc, QE.gpow, QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den,
      rQ, mixBelow, colsBelow, List.zipIdx, WChip.pR, WChip.lR, WChip.rR, WChip.rootR, WChip.lnR,
      WChip.cntR, WChip.accR, WChip.xInv, WChip.pInvL, WChip.pInvR, WChip.xAcc, WChip.pAcc,
      WChip.isF, WChip.isL, WChip.rM, WChip.idx, WChip.pre, WChip.ridx, WChip.len, WChip.cL,
      WChip.cR, WChip.e, WChip.mL, WChip.mR]
  intro g hg
  exact List.all_eq_true.mp hall g hg

end Template

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The walk twin chip** (masks `isFirst isLast rootMask` at `0..2`, as `walkChip`). -/
def walkChipH (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (walkTemplateH δF kroots) b (slotVal b 25 chals) (slotVal b 25 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 3
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 25 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes
    | 2 => rootRowMaskW nodes kroots

variable (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **The walk twin's width, MEASURED: `151`** (`132 + 4` handle columns `+ 5 𝕂`-roles). -/
theorem walkChipH_width : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w = 151 := by
  show (walkTemplateH δF kroots).baseCols + (walkTemplateH δF kroots).extCols * 3 = 151
  rw [walkTemplateH_baseCols, walkTemplateH_extCols]

theorem walkH_shift : ∀ j < (walkTemplate δF kroots).width 3,
    shiftCol 21 25 j < (walkTemplateH δF kroots).width 3 :=
  shift_lt _ _ 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateH_baseCols δF kroots) (by omega)
    (by rw [walkTemplate_extCols, walkTemplateH_extCols]; omega)

/-- The restriction of a twin trace to the original walk chip's `132` columns. -/
def restrictWalk (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 21 25 (walkH_shift δF kroots) Q

variable (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

theorem walkChipH_restrict_sat
    (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q) := by
  have hR : (walkTemplate δF kroots).extCols = 37 := walkTemplate_extCols δF kroots
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateH δF kroots) 21 25 (walkTemplate_baseCols δF kroots)
    (walkTemplateH_baseCols δF kroots) (by omega)
    (by rw [hR, walkTemplateH_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl Q hsat

theorem walkChipH_restrict_bind
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj
  · exact hj

/-- Row `j`'s base environment on the twin. -/
def walkEnvFH (j : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (if hj : j < n then nodes ⟨j, hj⟩ else nodes ⟨0, hn⟩)
    (slotVal b 25 chals) (slotVal b 25 pubs)

theorem walkEnvFH_trace (j : ℕ) {c : ℕ} (hc : c < 21) :
    (walkEnvFH δF kroots b hn nodes orbit chals pubs Q j).trace c =
      (walkEnvF b hn nodes orbit chals pubs (restrictWalk δF kroots b hn nodes orbit chals pubs Q) j).trace c := by
  have hw : (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 :=
    (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1
  have h0 : c < (walkChip δF kroots b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : c < (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w := by
    rw [walkChipH_width]; omega
  simp only [walkEnvFH, walkEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictWalk, restrictQ]
  congr 2
  apply Fin.ext
  simp [shiftCol, hc]

/-- The child handle of side `b` a twin row carries: `(kL, vL)` or `(kR, vR)` through `natOf`. -/
def childHOf [DecidableEq F] (eF : Env F) (bb : Bool) : VHandle :=
  if bb then (decide (eF.trace WalkHC.kR = 1), natOf (eF.trace WalkHC.vR))
  else (decide (eF.trace WalkHC.kL = 1), natOf (eF.trace WalkHC.vL))

end Chip

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

open scoped Classical in
/-- **`walkH_records_genuine`** (the twin of W2's `records_genuine_of_chip`).  On a trace accepted
by the walk twin, at the walk coins `(αC, γ) = (χ₀, χ₁)` outside W1's (unchanged) `walkEvent`,
with the table-side inputs of `records_genuine_of_chip` and the handle-export lookup's existence
form `hHX` (every row's consumed `(idx, kL, vL, kR, vR)` is `exportRec` of a table row): for every
walk row `i` and side `b`, the handle record the row provides — root serial `rootIdx`, axis
`2·prefix + b`, child handle `childHOf b` — names `/[2·prefix + b]` of `denH (1, rootIdx)`. -/
theorem walkH_records_genuine
    (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
    (hq : 2 ^ 63 < ringChar F) {z : Quad (algebraMap F K δF)} (hz : z ≠ 0)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vl : List (VKey (Quad (algebraMap F K δF)))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFH δF kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFH δF kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFH δF kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalk δF kroots b hn nodes orbit chals pubs Q))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalk δF kroots b hn nodes orbit chals pubs Q)
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧
        denH (tb.map (·.b0)) (true, ri) = some rt ∧
        denH (tb.map (·.b0)) (childHOf (walkEnvFH δF kroots b hn nodes orbit chals pubs Q (i - 1)) bb)
          = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn := by
  intro W i hi1 hin bb
  set Q0 := restrictWalk δF kroots b hn nodes orbit chals pubs Q
  have hsat0 := walkChipH_restrict_sat δF kroots b hn nodes orbit chals pubs Q hsat
  have hbind0 := walkChipH_restrict_bind δF kroots b hn nodes orbit chals pubs Q hbind
  have hp64 : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  have hyp := walkHyps_of_chip δF kroots b hn nodes orbit chals pubs Q0 hsat0 hbind0 hinj hadj hF
    hk hkn hkp hp64
  have hRG := rootGate_of_chip δF kroots b hn nodes orbit chals pubs Q0 hsat0 hbind0 hinj hF hkn hp64
  have hacc := walk_accepts_of_chip δF kroots b hn nodes orbit chals pubs Q0 hsat0 hbind0 hinj hadj
    hF hk hkn
  have hG : ForestReconGoal (stateSep (q := ringChar F) W.X 62) W.lbl W.kroots W.h := by
    by_contra hng
    exact hout (by simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                   exact ⟨hyp, hacc, hng⟩)
  have hj : i - 1 < n := by omega
  set eK := walkEnvK δF kroots b hn nodes orbit chals pubs Q0 (i - 1)
  set eF := walkEnvF b hn nodes orbit chals pubs Q0 (i - 1)
  have hkX : keyRow δF eK eF ∈ W.X := List.mem_ofFn.mpr ⟨⟨i - 1, hj⟩, rfl⟩
  have hki : (keyRow δF eK eF).1 = (W.lbl i).2.node := rfl
  obtain ⟨c, hc, hrec⟩ := hHX (i - 1) hj
  have hidx : natOf ((walkEnvFH δF kroots b hn nodes orbit chals pubs Q (i - 1)).trace WChip.idx) =
      (keyRow δF eK eF).2.2.2 := by
    show _ = natOf (eF.trace WChip.idx)
    rw [walkEnvFH_trace δF kroots b hn nodes orbit chals pubs Q (i - 1) (by decide)]
  rw [hidx] at hrec
  exact walkH_of_reconGoal hq hz htab hT2 hdy hX hk hRG hG i hi1 hin (keyRow δF eK eF) hkX hki
    _ _ ⟨c, hc, hrec⟩ bb |>.imp fun ri ⟨rt, nn, h1, h2, h3, h4⟩ =>
      ⟨rt, nn, h1, h2, by cases bb <;> simpa [childHOf] using h3, h4⟩

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle
