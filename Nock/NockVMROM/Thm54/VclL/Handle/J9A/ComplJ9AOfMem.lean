/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AOfMem.lean

The obligation fields `hsatC hbindC hinjC hadjC hnpC` (cell), `hsatW hbindW hinjW hadjW hkW hknW hkpW` (walk),
  `hJk` (J chip), `hsatA hbindA hsatL hbindL hinjA hadjA hnpA` (atom table), `hVk` (atom walk) of
  `ComplJ9AObl.ComplJ9AObligations` at `B := BRun9A …`, each in exactly the field's form.

  Asking
    the kernel to compare `qM δ b BRun9A.Pb.toPubJ8 …` with `qM δ b B8A.Pb …` makes it compare the two `PubJ8`
    records argument-first, i.e. `htA DA` with `htJ8 DA`. Here every transfer goes through a GENERIC lemma
    (`cellX walkX jX atomX atomLX awX nodesX`) over variables `P P' : PubJ8 p`, `tr tr' : TrJ8`, with the record
    relation as an equation `P' = updC P h' n' hn' nodes' orbit'` (the compute-part update) and the trace / public
    components as equations; inside, `subst` and a projection-level `qM`/`qW`/… rewrite. The instances of those
    equations at the run (`Pb_eq`, `trM_eq … trV_eq`, `pubsC_eq … pubsV_eq`) are `rfl` lemmas that only unfold the
    record to its constructor and compare fields that are syntactically the same terms (no height comparison).
  * The B8A-level facts: `cellOK_runA`, `walkOK_runA`, `awOK_runA`, `jOK_A8` (twin of J-9 B's
    `jOK_run9` at `DA`), `atomOK_A8`, `nodes_A8` (twin of
    J-8's `nodes_group` at `DA`).
  Binders: `hpG h31A` (the record's), `hleaf` (cell), `hwalk9` (walk), `hRt` (J),
  `hax9 hwalkA` (atom walk); `hp63` is derived from `hpG` (`ComplJ9AChains.hp63_of_G`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfMem

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

noncomputable section

/-! ## 1. Generic transfers (variables only: the kernel never sees a concrete height) -/

section Generic
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The compute-part update of a public layout** (`h n hn nodes orbit` replaced; the memory tables kept). -/
def updC (P : PubJ8 p) (h' n' : ℕ) (hn' : 0 < n') (nodes' : Fin n' → ZMod p)
    (orbit' : StrictOrbitDomain (ZMod p) 3 h') : PubJ8 p :=
  { P with h := h', n := n', hn := hn', nodes := nodes', orbit := orbit' }

variable {P P' : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} {h' n' : ℕ} {hn' : 0 < n'} {nodes' : Fin n' → ZMod p}
  {orbit' : StrictOrbitDomain (ZMod p) 3 h'}

/-- The cell table, transferred. -/
theorem cellX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.M = tr.M)
    (hp : pubs' = pubs)
    (H : (CellTwinKW.cellChipHQKW δ b P.hnC P.nodesC P.orbitC chals pubs).rap.Satisfies (qM δ b P tr chals pubs) ∧
      (CellTwinKW.cellChipHQKW δ b P.hnC P.nodesC P.orbitC chals pubs).BindsPreprocessing (qM δ b P tr chals pubs)) :
    (CellTwinKW.cellChipHQKW δ b P'.hnC P'.nodesC P'.orbitC chals pubs').rap.Satisfies (qM δ b P' tr' chals pubs') ∧
      (CellTwinKW.cellChipHQKW δ b P'.hnC P'.nodesC P'.orbitC chals pubs').BindsPreprocessing
        (qM δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qM δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qM δ b P tr chals pubs := hT
  rw [e]
  exact H

/-- The J-8 walk, transferred. -/
theorem walkX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.W = tr.W)
    (hp : pubs' = pubs)
    (H : (WalkJ8.walkChipJ8 δ P.kroots b P.hnW P.nodesW P.orbitW chals pubs).rap.Satisfies (qW δ b P tr chals pubs) ∧
      (WalkJ8.walkChipJ8 δ P.kroots b P.hnW P.nodesW P.orbitW chals pubs).BindsPreprocessing
        (qW δ b P tr chals pubs)) :
    (WalkJ8.walkChipJ8 δ P'.kroots b P'.hnW P'.nodesW P'.orbitW chals pubs').rap.Satisfies
        (qW δ b P' tr' chals pubs') ∧
      (WalkJ8.walkChipJ8 δ P'.kroots b P'.hnW P'.nodesW P'.orbitW chals pubs').BindsPreprocessing
        (qW δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qW δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qW δ b P tr chals pubs := by
    funext j
    show tr'.W _ = tr.W _
    rw [hT]
    rfl
  rw [e]
  exact H

/-- The J chip, transferred. -/
theorem jX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.J = tr.J)
    (hp : pubs' = pubs)
    (H : JGenJ8.JChipOK δ b P.nodesJ P.orbitJ chals pubs P.lay (qJ δ b P tr chals pubs)) :
    JGenJ8.JChipOK δ b P'.nodesJ P'.orbitJ chals pubs' P'.lay (qJ δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qJ δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qJ δ b P tr chals pubs := by
    funext j
    show tr'.J _ = tr.J _
    rw [hT]
    rfl
  rw [e]
  exact H

/-- The atom table (`atomChipHQ`), transferred. -/
theorem atomX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.A = tr.A)
    (hp : pubs' = pubs)
    (H : (AtomChipHQ.atomChipHQ δ b P.hnA P.nodesA P.orbitA chals pubs).rap.Satisfies (qA δ b P tr chals pubs) ∧
      (AtomChipHQ.atomChipHQ δ b P.hnA P.nodesA P.orbitA chals pubs).BindsPreprocessing (qA δ b P tr chals pubs)) :
    (AtomChipHQ.atomChipHQ δ b P'.hnA P'.nodesA P'.orbitA chals pubs').rap.Satisfies (qA δ b P' tr' chals pubs') ∧
      (AtomChipHQ.atomChipHQ δ b P'.hnA P'.nodesA P'.orbitA chals pubs').BindsPreprocessing
        (qA δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qA δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qA δ b P tr chals pubs := by
    funext j
    show tr'.A _ = tr.A _
    rw [hT]
    rfl
  rw [e]
  exact H

/-- The atom table (`atomChipHQL`), transferred. -/
theorem atomLX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.A = tr.A)
    (hp : pubs' = pubs)
    (H : (AtomChipHQL.atomChipHQL δ b P.hnA P.nodesA P.orbitA chals pubs).rap.Satisfies (qAL δ b P tr chals pubs) ∧
      (AtomChipHQL.atomChipHQL δ b P.hnA P.nodesA P.orbitA chals pubs).BindsPreprocessing
        (qAL δ b P tr chals pubs)) :
    (AtomChipHQL.atomChipHQL δ b P'.hnA P'.nodesA P'.orbitA chals pubs').rap.Satisfies
        (qAL δ b P' tr' chals pubs') ∧
      (AtomChipHQL.atomChipHQL δ b P'.hnA P'.nodesA P'.orbitA chals pubs').BindsPreprocessing
        (qAL δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qAL δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qAL δ b P tr chals pubs := by
    funext j
    show tr'.A _ = tr.A _
    rw [hT]
    rfl
  rw [e]
  exact H

/-- The atom walk, transferred. -/
theorem awX (chals pubs pubs' : ℕ → K) (hP : P' = updC P h' n' hn' nodes' orbit') (hT : tr'.V = tr.V)
    (hp : pubs' = pubs)
    (H : AcceptsJ8V.AWChipOK δ b P.krootsV P.hnV P.nodesV P.orbitV chals pubs (qV δ b P tr chals pubs)) :
    AcceptsJ8V.AWChipOK δ b P'.krootsV P'.hnV P'.nodesV P'.orbitV chals pubs' (qV δ b P' tr' chals pubs') := by
  subst hP
  subst pubs'
  have e : qV δ b (updC P h' n' hn' nodes' orbit') tr' chals pubs = qV δ b P tr chals pubs := by
    funext j
    show tr'.V _ = tr.V _
    rw [hT]
    rfl
  rw [e]
  exact H

/-- The node facts of the cell table, the J-8 walk and the atom table (as `ComplJ8Of.nodes_group` states them). -/
def NodesOK (P : PubJ8 p) : Prop :=
  (Function.Injective P.nodesC ∧
      (∀ (i : Fin P.nC) (hi : (i : ℕ) + 1 < P.nC), P.nodesC ⟨(i : ℕ) + 1, hi⟩ = P.nodesC i * P.orbitC.ω) ∧
      P.nC < ringChar (ZMod p)) ∧
    (Function.Injective P.nodesW ∧
      (∀ (i : Fin P.nW) (hi : (i : ℕ) + 1 < P.nW), P.nodesW ⟨(i : ℕ) + 1, hi⟩ = P.nodesW i * P.orbitW.ω) ∧
      1 ≤ P.kroots ∧ P.kroots ≤ P.nW ∧ P.kroots + P.nW < ringChar (ZMod p)) ∧
    (Function.Injective P.nodesA ∧
      (∀ (i : Fin P.nA) (hi : (i : ℕ) + 1 < P.nA), P.nodesA ⟨(i : ℕ) + 1, hi⟩ = P.nodesA i * P.orbitA.ω) ∧
      P.nA < p)

/-- The node facts, transferred. -/
theorem nodesX (hP : P' = updC P h' n' hn' nodes' orbit') (H : NodesOK P) : NodesOK P' := by
  subst hP
  exact H

end Generic

/-! ## 2. -/

section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-! The `pubs*` equations go through the concrete field value (`pubsCOf …`): a direct `rfl` between the two
projections makes the kernel compare the two `MsgJ8'` records first, whose `ρ` fields differ (`ρA` vs `ρCOf`), and
it times out (measured). -/


/-- The public data of `BRun9A` is that of `B8A` with the cell-table entry updated (`updC`). -/
theorem Pb_eq : (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 =
    updC (B8A δ b Rt hgen hpG h31A).Pb (htA (DA)) (N9 t) (BRun9A δ b Rt hgen hpG h31A).Pb.hn
      (powN (oA Rt hgen hpG h31A) (N9 t)) (oA Rt hgen hpG h31A) := rfl

theorem trM_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.M = ((B8A δ b Rt hgen hpG h31A).tr χ).M := rfl
theorem trW_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.W = ((B8A δ b Rt hgen hpG h31A).tr χ).W := rfl
theorem trJ_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.J = ((B8A δ b Rt hgen hpG h31A).tr χ).J := rfl
theorem trA_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.A = ((B8A δ b Rt hgen hpG h31A).tr χ).A := rfl
theorem trV_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8.V = ((B8A δ b Rt hgen hpG h31A).tr χ).V := rfl

theorem pubsC_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC = ((B8A δ b Rt hgen hpG h31A).M χ).pubsC :=
  (show ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC = pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ from rfl).trans (show pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsC from rfl)
theorem pubsW_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW = ((B8A δ b Rt hgen hpG h31A).M χ).pubsW :=
  (show ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW = pubsWOf δ b (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ from rfl).trans (show pubsWOf δ b (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsW from rfl)
theorem pubsJ_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsJ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsJ :=
  (show ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsJ = pubsJOf δ (DA) χ from rfl).trans (show pubsJOf δ (DA) χ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsJ from rfl)
theorem pubsA_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA = ((B8A δ b Rt hgen hpG h31A).M χ).pubsA :=
  (show ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA = pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ from rfl).trans (show pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsA from rfl)
theorem pubsV_eq (χ : Coins frameJ8 K) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsV = ((B8A δ b Rt hgen hpG h31A).M χ).pubsV :=
  (show ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsV = ComplJ9BBalF.pubsVOf9 δ b (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ from rfl).trans (show ComplJ9BBalF.pubsVOf9 δ b (DA) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ = ((B8A δ b Rt hgen hpG h31A).M χ).pubsV from rfl)

end Run

/-! ## 3. -/

section Lanes
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hF : DvdOK (j9aDataOf p Rg Rt hgen)) (hC : 0 < (j9aDataOf p Rg Rt hgen).cells.length)
  (hA : 0 < (j9aDataOf p Rg Rt hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

local notation "DA" => j9aDataOf p Rg Rt hgen


/-- The jet table is well-formed at `honestJ8Of` at a good coin, given the registry facts `hRt` and `famJ ∈ fams`. -/
theorem jOK_A8
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hJ : famJ δ (DA) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (honestJ8Of δ b (DA) hF hC hA AV fams).Good χ) :
    let B := honestJ8Of δ b (DA) hF hC hA AV fams
    JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
      (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ) := by
  intro B
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (DA).jrows.length = 0
  · refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
    have hs : ∀ (g : Fin (DA).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
      intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
    have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
      (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
    have e : ∀ i, pubsJOf δ (DA) χ i = 0 := by
      intro i
      unfold pubsJOf
      rw [hs, hs]
      split_ifs <;> simp [pub2, hz.1, hz.2]
    exact ⟨e 0, e 1, e 2, e 3⟩
  · have hn : 0 < (DA).jrows.length := Nat.pos_of_ne_zero h0
    obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (DA).jrows.length)
      (le_two_pow_ht _ (by simp [sizesJ8]))
    have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DA).t]).length)] fams), χ ∉ e.1 := hχ
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (DA).jrows.get)
      (ComplJ8Jet.jKeysX (DA).jrows.get) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hJ, he⟩)))
    have := ComplJ8Jet.jOK_present_trJ δ b (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsJJ8 χ) (pubsJOf δ _ χ)
      (DA).jrows.get hinj hn hadj
      (fun i => ComplJ8Jet.jrows_gate_run Rt hgen hp hRt _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])
    exact this


/-- `NodesOK` holds for the public data of `honestJ8Of`, when `2^63 < p` and the rows are below `2^31`. -/
theorem nodes_A8 (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DA)) :
    NodesOK (honestJ8Of δ b (DA) hF hC hA AV fams).Pb := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hmW : (walkRows (DA).cells (DA).reads).length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hmA : (DA).acs.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  obtain ⟨c1, c2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmC)
  obtain ⟨w1, w2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmW)
  obtain ⟨a1, a2⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmA)
  have hWb := h31 _ hmW
  have hk := krW_le_rows (DA).cells (DA).reads
  have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  refine ⟨⟨c1, c2, ?_⟩, ⟨w1, w2, one_le_krW _ _, hk, ?_⟩, ⟨a1, a2, ComplJ9ATables.lt31 hp63 h31 hmA⟩⟩
  · rw [hrc]; exact ComplJ9ATables.lt31 hp63 h31 hmC
  · rw [hrc]; show krW _ _ + (walkRows _ _).length < p; omega

end Lanes

/-! ## 4. The obligation fields at `BRun9A` -/

section Fields
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen


/-- A `BRun9A`-good coin lies outside every event of every family in `famsJA`. -/
theorem goodJA {χ : Coins frameJ8 K} (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ∀ L ∈ famsJA δ b Rt hgen hpG h31A, ∀ e ∈ L, χ ∉ e.ev :=
  fun L hL => good_fam δ b Rt hgen hpG h31A hχ L (List.mem_append_left _ hL)

/-- **The cell table at `BRun9A`** (`hsatC`, `hbindC` at a good coin). -/
theorem cell_A (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots) (χ : Coins frameJ8 K)
    (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    (CellTwinKW.cellChipHQKW δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnC (BRun9A δ b Rt hgen hpG h31A).Pb.nodesC
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitC (chalsMJ8 δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC).rap.Satisfies
      (qM δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnC (BRun9A δ b Rt hgen hpG h31A).Pb.nodesC
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitC (chalsMJ8 δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC).BindsPreprocessing
      (qM δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsC) :=
  cellX δ b (chalsMJ8 δ χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trM_eq δ b Rt hgen hpG h31A χ)
    (pubsC_eq δ b Rt hgen hpG h31A χ)
    (ComplJ9ATables.cellOK_runA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (ComplJ9ADataRec.acsA_pos Rt hgen)
      (ComplJ9ATables.AVA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen))
      (famsJA δ b Rt hgen hpG h31A) hpG (ComplJ9AChains.hp63_of_G hpG) hleaf
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      χ (good_B8 δ b Rt hgen hpG h31A hχ))

/-- **The J-8 walk at `BRun9A`** (`hsatW`, `hbindW` at a good coin). -/
theorem walk_A (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (χ : Coins frameJ8 K)
    (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    (WalkJ8.walkChipJ8 δ (BRun9A δ b Rt hgen hpG h31A).Pb.kroots b (BRun9A δ b Rt hgen hpG h31A).Pb.hnW
        (BRun9A δ b Rt hgen hpG h31A).Pb.nodesW (BRun9A δ b Rt hgen hpG h31A).Pb.orbitW (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW).rap.Satisfies
      (qW δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW) ∧
    (WalkJ8.walkChipJ8 δ (BRun9A δ b Rt hgen hpG h31A).Pb.kroots b (BRun9A δ b Rt hgen hpG h31A).Pb.hnW
        (BRun9A δ b Rt hgen hpG h31A).Pb.nodesW (BRun9A δ b Rt hgen hpG h31A).Pb.orbitW (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW).BindsPreprocessing
      (qW δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8 (chalsMJ8 δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW) :=
  walkX δ b (chalsMJ8 δ χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trW_eq δ b Rt hgen hpG h31A χ)
    (pubsW_eq δ b Rt hgen hpG h31A χ)
    (ComplJ9ATables.walkOK_runA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (ComplJ9ADataRec.acsA_pos Rt hgen)
      (ComplJ9ATables.AVA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen))
      (famsJA δ b Rt hgen hpG h31A) (ComplJ9AChains.hp63_of_G hpG) (h31_run Rt hgen h31A)
      (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9)
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))))
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))
      χ (good_B8 δ b Rt hgen hpG h31A hχ))

/-- **The J chip at `BRun9A`** (`hJk` at a good coin). -/
theorem j_A
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    JGenJ8.JChipOK δ b (BRun9A δ b Rt hgen hpG h31A).Pb.nodesJ (BRun9A δ b Rt hgen hpG h31A).Pb.orbitJ (chalsJJ8 χ)
      ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsJ (BRun9A δ b Rt hgen hpG h31A).Pb.lay
      (qJ δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8 (chalsJJ8 χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsJ) :=
  jX δ b (chalsJJ8 χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trJ_eq δ b Rt hgen hpG h31A χ)
    (pubsJ_eq δ b Rt hgen hpG h31A χ)
    (jOK_A8 δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (ComplJ9ADataRec.acsA_pos Rt hgen)
      (ComplJ9ATables.AVA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen))
      (famsJA δ b Rt hgen hpG h31A) hRt
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      χ (good_B8 δ b Rt hgen hpG h31A hχ))


/-- **The atom chips at `B8A`**: at a `BRun9A`-good coin, both `atomChipHQ` and `atomChipHQL` satisfy their RAPs (and the first binds its preprocessing). -/
theorem atom_A8
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    let B := B8A δ b Rt hgen hpG h31A
    ((AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA)) ∧
    ((AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA)) := by
  intro B
  have hin := goodJA δ b Rt hgen hpG h31A hχ
  have H := ComplJ9ATables.atomOK_runA δ b Rt hgen hpG (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen)
    (h31_run Rt hgen h31A) χ
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
    (hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])))
  exact ⟨⟨H.1, H.2.1⟩, ⟨H.2.2.1, H.2.2.2⟩⟩

/-- **The atom table at `BRun9A`** (`hsatA hbindA hsatL hbindL` at a good coin). -/
theorem atom_A
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ((AtomChipHQ.atomChipHQ δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnA (BRun9A δ b Rt hgen hpG h31A).Pb.nodesA
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA).rap.Satisfies
      (qA δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8
        (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnA (BRun9A δ b Rt hgen hpG h31A).Pb.nodesA
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA).BindsPreprocessing
      (qA δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8
        (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA)) ∧
    ((AtomChipHQL.atomChipHQL δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnA (BRun9A δ b Rt hgen hpG h31A).Pb.nodesA
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA).rap.Satisfies
      (qAL δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8
        (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b (BRun9A δ b Rt hgen hpG h31A).Pb.hnA (BRun9A δ b Rt hgen hpG h31A).Pb.nodesA
        (BRun9A δ b Rt hgen hpG h31A).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ)
        ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA).BindsPreprocessing
      (qAL δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8
        (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsA)) := by
  have H := atom_A8 δ b Rt hgen hpG h31A χ hχ
  exact ⟨atomX δ b (ChalsAZJ8.chalsAJ8Z δ χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trA_eq δ b Rt hgen hpG h31A χ)
      (pubsA_eq δ b Rt hgen hpG h31A χ) H.1,
    atomLX δ b (ChalsAZJ8.chalsAJ8Z δ χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trA_eq δ b Rt hgen hpG h31A χ)
      (pubsA_eq δ b Rt hgen hpG h31A χ) H.2⟩

/-- **The atom walk at `BRun9A`** (`hVk` at a good coin). -/
theorem aw_A (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    AcceptsJ8V.AWChipOK δ b (BRun9A δ b Rt hgen hpG h31A).Pb.krootsV (BRun9A δ b Rt hgen hpG h31A).Pb.hnV
      (BRun9A δ b Rt hgen hpG h31A).Pb.nodesV (BRun9A δ b Rt hgen hpG h31A).Pb.orbitV (ChalsAZJ8.chalsAJ8Z δ χ)
      ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsV
      (qV δ b (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 ((BRun9A δ b Rt hgen hpG h31A).tr χ).toJ8
        (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9A δ b Rt hgen hpG h31A).M χ).pubsV) :=
  awX δ b (ChalsAZJ8.chalsAJ8Z δ χ) _ _ (Pb_eq δ b Rt hgen hpG h31A) (trV_eq δ b Rt hgen hpG h31A χ)
    (pubsV_eq δ b Rt hgen hpG h31A χ)
    (ComplJ9ATables.awOK_runA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (ComplJ9ADataRec.acsA_pos Rt hgen) (famsJA δ b Rt hgen hpG h31A) (ComplJ9AChains.hp63_of_G hpG)
      (h31_run Rt hgen h31A) hax9 hwalkA
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
      χ (good_B8 δ b Rt hgen hpG h31A hχ))

/-- **The node facts at `BRun9A`** (`hinjC hadjC hnpC`, `hinjW hadjW hkW hknW hkpW`, `hinjA hadjA hnpA`). -/
theorem nodes_A : NodesOK (BRun9A δ b Rt hgen hpG h31A).Pb.toPubJ8 :=
  nodesX (Pb_eq δ b Rt hgen hpG h31A)
    (nodes_A8 δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (ComplJ9ADataRec.acsA_pos Rt hgen)
      (ComplJ9ATables.AVA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen))
      (famsJA δ b Rt hgen hpG h31A) (ComplJ9AChains.hp63_of_G hpG) (h31_run Rt hgen h31A))

end Fields

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfMem

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfMem
#print axioms Pb_eq
#print axioms jOK_A8
#print axioms nodes_A8
#print axioms cell_A
#print axioms walk_A
#print axioms j_A
#print axioms atom_A
#print axioms aw_A
#print axioms nodes_A
end Axioms
