/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomWalkAW.lean

  `walkChipHQK` (the ternary-kind `𝕂′` walk twin, 166 columns) instantiated a SECOND time, at the
  atom table's coins: the same challenge vector (`chals 0, 1 = (alpha, gamma)`, `chals 2, 3` = `y`),
  the atom table's rows as the consumed export records (`xKeyH = (idx, kL, vL, kR, vR)`, which on the
  atom table is `keyH = (idx, 0, aL, wR, valR)`: `wL = 0`, g2), and its own publics:
  `4/5` the export terminal, `6/7` the provide terminal `term_AW`.

  * `restrictWalkK` / `walkChipHQK_restrict_sat` / `_bind`: a `walkChipHQK`-accepted trace restricted to
    the original `walkChip` columns is accepted by `walkChip` (`expandChip_restrict`: the restriction
    twin step; the ternary gates only ADD to the base list).
  * `atomWalkChip`, `atomWalkChip_width` (166, rfl);
  * `walkRecA`: the provided record `(rootIdx, 2·prefix + b, k_b, v_b)`, 4 entries, untagged;
    `walkRecA_eval` (the chip's `recLH/recRH` evaluate to it), `walkRecA_len`, the key-disjointness
    length facts against the 5-entry export key;
  * `pubsAW`, `pubsAW_termAW` (the terminal public);
  * `atomWalk_W1` (WalkHyps, RootGate, WalkSat from the chip, i.e. the premises of `walkEvent`'s
    complement) and `atomWalk_records_genuine` (the twin of `walkH_records_genuine`, outside the SAME
    `walkEvent`, with the table side `TableAccepts` at `y`, supplied by `atomTable_accepts`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The restriction twin step -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem walkHQK_shift : ∀ j < (walkTemplate δF kroots).width 3,
    shiftCol 21 25 j < (walkTemplateHQK δF kroots).width 3 :=
  shift_lt _ _ 21 25 (walkTemplate_baseCols δF kroots) (walkTemplateHQK_baseCols δF kroots) (by omega)
    (by rw [walkTemplate_extCols, walkTemplateHQK_extCols]; omega)

/-- The restriction of a `walkChipHQK` trace to the original walk chip's `132` columns. -/
def restrictWalkK (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 21 25 (walkHQK_shift δF kroots) Q

/-- **Restriction**: `walkChipHQK` acceptance ⇒ original `walkChip` acceptance of the restriction. -/
theorem walkChipHQK_restrict_sat (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q) := by
  have hR : (walkTemplate δF kroots).extCols = 37 := walkTemplate_extCols δF kroots
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots)
    (walkTemplateHQK δF kroots) 21 25 (walkTemplate_baseCols δF kroots)
    (walkTemplateHQK_baseCols δF kroots) (by omega)
    (by rw [hR, walkTemplateHQK_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact walkMixed_below δF kroots g hg⟩)
    rfl rfl Q hsat

theorem walkChipHQK_restrict_bind (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj
  · exact hj

/-- **The atom-walk chip at `y`**: `walkChipHQK` at the atom table's challenge vector and its own
publics (`4/5` export terminal, `6/7` the provide terminal `term_AW`). -/
abbrev atomWalkChip : FixedPreprocessingRAP F :=
  walkChipHQK δF kroots b hn nodes orbit chals pubs

/-- Width `166` (`rfl`, 0 new chip columns over `walkChipHQ`). -/
theorem atomWalkChip_width : (atomWalkChip δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
  walkChipHQK_width δF kroots b hn nodes orbit chals pubs

end Chip

/-! ## 2. `walkRecA`: the provided record and its key shape -/

section Rec
variable {F : Type} [Field F]

/-- **`walkRecA`**: the record side `bb` of a walk row provides, `(rootIdx, 2·prefix + b, k_b, v_b)`,
four entries, no tag (the chip's fixed key shape). -/
def walkRecA (ridx pre kb vb : F) (bb : Bool) : List F :=
  [ridx, 2 * pre + (if bb then 1 else 0), kb, vb]

theorem walkRecA_len (ridx pre kb vb : F) (bb : Bool) : (walkRecA ridx pre kb vb bb).length = 4 := rfl

/-- The chip's provide keys `recLH / recRH` evaluate to `walkRecA` (the wiring of the provide). -/
theorem walkRecA_eval (e : Env F) :
    (WalkHC.recLH : List (CoeffExpr F)).map (fun g => g.eval e) =
      walkRecA (e.trace WChip.ridx) (e.trace WChip.pre) (e.trace WalkHC.kL) (e.trace WalkHC.vL) false ∧
    (WalkHC.recRH : List (CoeffExpr F)).map (fun g => g.eval e) =
      walkRecA (e.trace WChip.ridx) (e.trace WChip.pre) (e.trace WalkHC.kR) (e.trace WalkHC.vR) true := by
  constructor <;> simp [WalkHC.recLH, WalkHC.recRH, walkRecA, CoeffExpr.eval, cv]

/-- Key shapes: provided records have `4` entries; the consumed atom export key has `5`
(`idx, kL, vL, kR, vR`), so a tagged (`≥ 5`-entry) service key never equals a `walkRecA` key. -/
theorem walkRecA_shapes :
    (WalkHC.recLH : List (CoeffExpr F)).length = 4 ∧ (WalkHC.recRH : List (CoeffExpr F)).length = 4 ∧
    (WalkHC.xKeyH : List (CoeffExpr F)).length = 5 := ⟨rfl, rfl, rfl⟩

end Rec

/-! ## 3. Publics: the terminal -/

section Pubs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The atom-walk publics**: `pubsWHQ` with `4/5 = yHA` (export terminal) and `6/7 = tAW`
(the provide terminal `term_AW`, in place of the cell walk's `ρ₄`). -/
def pubsAW (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yHA tAW : Quad (algebraMap F K δF)) (i : ℕ) : K :=
  if i = 6 then Quad.re _ tAW else if i = 7 then Quad.im _ tAW else pubsWHQ δF ρ y yHA i

theorem pubsAW_termAW (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yHA tAW : Quad (algebraMap F K δF)) :
    pubsAW δF ρ y yHA tAW 6 = Quad.re _ tAW ∧ pubsAW δF ρ y yHA tAW 7 = Quad.im _ tAW := by
  simp [pubsAW]

theorem pubsAW_export (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yHA tAW : Quad (algebraMap F K δF)) :
    pubsAW δF ρ y yHA tAW 4 = Quad.re _ yHA ∧ pubsAW δF ρ y yHA tAW 5 = Quad.im _ yHA := by
  simp [pubsAW, pubsWHQ]

end Pubs

/-! ## 4. -/

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- Row `j`'s base environment on the twin. -/
def walkEnvFA (j : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (if hj : j < n then nodes ⟨j, hj⟩ else nodes ⟨0, hn⟩)
    (slotVal b 25 chals) (slotVal b 25 pubs)

theorem walkEnvFA_trace (j : ℕ) {c : ℕ} (hc : c < 21) :
    (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j).trace c =
      (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs Q) j).trace c := by
  have hw : (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 :=
    (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1
  have h0 : c < (walkChip δF kroots b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : c < (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w := by
    rw [walkChipHQK_width]; omega
  simp only [walkEnvFA, walkEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictWalkK, restrictQ]
  congr 2
  apply Fin.ext
  simp [shiftCol, hc]

variable (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
  (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
  (hq : 2 ^ 63 < ringChar F)

include hsat hbind hinj hadj hF hk hkn hkp hq in
theorem atomWalk_W1 :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)
    WalkHyps (algebraMap F K δF) W ∧ RootGate W.X W.lbl W.kroots ∧
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc (chals 1) (enc (algebraMap F K δF) (W.lbl i)))
        (fun i l => rlc (chals 1) (enc (algebraMap F K δF) (W.clab i l))) W.fo
        ln count acc (chals 0)
        (∑ i ∈ Finset.Icc 1 W.kroots, rlc (chals 1) (enc (algebraMap F K δF) (W.lbl i)) * chals 0 ^ i)
        (chals 0 ^ W.kroots) W.h ∧ acc W.h = 0) := by
  intro W
  have hsat0 := walkChipHQK_restrict_sat δF kroots b hn nodes orbit chals pubs Q hsat
  have hbind0 := walkChipHQK_restrict_bind δF kroots b hn nodes orbit chals pubs Q hbind
  have hp64 : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  exact ⟨walkHyps_of_chip δF kroots b hn nodes orbit chals pubs _ hsat0 hbind0 hinj hadj hF
      hk hkn hkp hp64,
    rootGate_of_chip δF kroots b hn nodes orbit chals pubs _ hsat0 hbind0 hinj hF hkn hp64,
    walk_accepts_of_chip δF kroots b hn nodes orbit chals pubs _ hsat0 hbind0 hinj hadj hF hk hkn⟩

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **`atomWalk_records_genuine`** (the twin of `walkH_records_genuine` for the atom-walk instance).
On a trace accepted by `walkChipHQK` at the atom table's coins, at `(αC, γ) = (chals 0, chals 1)`
outside the SAME `walkEvent`, with the table side `TableAccepts` at `y` (for the atom table:
`atomTable_accepts`) and the handle-export lookup's existence form `hHX`, every handle record
`walkRecA` a row provides names `/[2·prefix + b]` of `denH (1, rootIdx)`. -/
theorem atomWalk_records_genuine {z : Quad (algebraMap F K δF)} (hz : z ≠ 0)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vl : List (VKey (Quad (algebraMap F K δF)))} (htab : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs Q))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧
        denH (tb.map (·.b0)) (true, ri) = some rt ∧
        denH (tb.map (·.b0)) (childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q (i - 1)) bb)
          = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn := by
  intro W i hi1 hin bb
  set Q0 := restrictWalkK δF kroots b hn nodes orbit chals pubs Q
  obtain ⟨hyp, hRG, hacc⟩ := atomWalk_W1 δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF
    hk hkn hkp hq
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
  have hidx : natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs Q (i - 1)).trace WChip.idx) =
      (keyRow δF eK eF).2.2.2 := by
    show _ = natOf (eF.trace WChip.idx)
    rw [walkEnvFA_trace δF kroots b hn nodes orbit chals pubs Q (i - 1) (by decide)]
  rw [hidx] at hrec
  exact walkH_of_reconGoal hq hz htab hT2 hdy hX hk hRG hG i hi1 hin (keyRow δF eK eF) hkX hki
    _ _ ⟨c, hc, hrec⟩ bb |>.imp fun ri ⟨rt, nn, h1, h2, h3, h4⟩ =>
      ⟨rt, nn, h1, h2, by cases bb <;> simpa [childHOf] using h3, h4⟩

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- Remaining inputs, as in `walkH_records_genuine`: `hT2`, `hdy`, `hX` (KeysExported),
`hHX` (handle-export lookup, existence form), plus the atom table's `hserved`; none is proved here. -/
theorem atomWalk_records_genuine_atom
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → F) (orbitA : StrictOrbitDomain F 3 hA)
    (pubsA : ℕ → K)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (QA : Fin (AtomChipHQ.atomChipHQ δF b hnA nodesA orbitA chals pubsA).rap.w → F[X])
    (hsatA : (AtomChipHQ.atomChipHQ δF b hnA nodesA orbitA chals pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δF b hnA nodesA orbitA chals pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnpA : nA < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodesA orbitA chals pubsA
      (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA)))
    (vl : List (VKey (Quad (algebraMap F K δF))))
    (hT2 : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ∉ tableBadSeeds fuelChip
      ((cellTableOf δF b nodesA orbitA chals pubsA
        (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA)).map (·.b0)) [])
    (hdy : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ∉ cellDyckRootSeeds fuelChip
      ((cellTableOf δF b nodesA orbitA chals pubsA
        (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA)).map (·.b0)))
    (hX : KeysExported (cellTableOf δF b nodesA orbitA chals pubsA
        (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA))
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ cellTableOf δF b nodesA orbitA chals pubsA
        (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA),
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs Q))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧
        denH ((cellTableOf δF b nodesA orbitA chals pubsA
          (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA)).map (·.b0)) (true, ri) = some rt ∧
        denH ((cellTableOf δF b nodesA orbitA chals pubsA
          (AtomChipHQ.restrictAtomCell δF b hnA nodesA orbitA chals pubsA QA)).map (·.b0))
          (childHOf (walkEnvFA δF kroots b hn nodes orbit chals pubs Q (i - 1)) bb) = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn :=
  atomWalk_records_genuine δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq
    hz (AtomChipHQ.atomTable_accepts δF b hnA nodesA orbitA chals pubsA hF hq hz QA hsatA hbindA hinjA
      hadjA hnpA hserved vl) hT2 hdy hX hHX hout

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
