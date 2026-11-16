/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/WalkForestP1.lean

 **Trace uniqueness on the P1 fragment: the walk table's rows are a BFS forest.**

 Outside the walk chip's α-event `walkEvent` (at the coins `(χ₀, χ₁)`, over the walk data of the `bitFix`ed,
 restricted trace, the event `walkJ8_records_genuine` is stated at), an accepted J-8 walk trace has:
 * the walk hypotheses `WalkHyps` (BFS queue validity, the tiling `kroots + Σ fo = n`, fanout = `cL + cR`, the
 in-gate child relation `F` with the consumed export keys),
 * the root gate `RootGate` (`prefix = 1`, `len = 0`, `root = node`, `rootIdx = idx` on rows `1..kroots`),
 * **`ForestReconGoal`**: there are `kroots` trees, each `RVT F` (every child label is the child step
 `(2·prefix + b, rootIdx, len + 1, root, fp = tgt k b)` of its parent under the parent's consumed export key `k`
 and the child flags), whose BFS order lists exactly the row labels `lbl 1, …, lbl n`, with fanout = number of
 children and the leaves exactly the flag-free labels; and the trees' roots are the rows `1..kroots`.

 Nothing is re-derived: `walkChipJ8_to_HQK` (the J-8 chip to the ternary twin through `bitFix`), `atomWalk_W1`
 (the three premises of `walkEvent`'s complement from the chip) and `roots_are_rows` are the existing soundness
 machinery; the forest is the complement of the priced walk event.

 * §1 `walkJ8_forest` (chip level) and `walkJ8_forest_roots` (the roots are rows `1..kroots`).
 * §2 `walkJ8_forest_of_accepts`: the same at an `AcceptsJ8V` trace (its walk view `qW`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

/-! ## 1. Chip level -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- The walk data the walk event is priced over: the `bitFix`ed J-8 trace restricted to the walk chip's
columns. -/
abbrev walkW : WalkData (ringChar F) (Quad (algebraMap F K δF)) :=
  walkDataOf δF kroots b hn nodes orbit chals pubs
    (AtomWalkAW.restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q))

open scoped Classical in
/-- **The forest lemma (chip level).** An accepted J-8 walk trace, at walk coins `(χ₀, χ₁)` outside the walk event,
has the walk hypotheses, the root gate and the BFS-forest characterisation `ForestReconGoal` of its row labels. -/
theorem walkJ8_forest
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F) (hq : 2 ^ 63 < ringChar F)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF) (walkW δF kroots b hn nodes orbit chals pubs Q)) :
    let W := walkW δF kroots b hn nodes orbit chals pubs Q
    WalkHyps (algebraMap F K δF) W ∧ RootGate W.X W.lbl W.kroots ∧
      ForestReconGoal (stateSep (q := ringChar F) W.X 62) W.lbl W.kroots W.h := by
  intro W
  have hp : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  obtain ⟨hyp, hRG, hacc⟩ := AtomWalkAW.atomWalk_W1 δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj hF
    hk hkn hkp hq
  refine ⟨hyp, hRG, ?_⟩
  by_contra hng
  exact hout (by simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                 exact ⟨hyp, hacc, hng⟩)

open scoped Classical in
/-- **The forest, with its roots at rows `1..kroots`**: `kroots` trees, each `RVT F`, whose BFS labels are the rows'
labels `lbl 1 .. lbl n` (fanout = children, leaves = flag-free), each tree's root label being the label of a row in
`1..kroots` (and that row satisfying the root gate). -/
theorem walkJ8_forest_roots
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hF : GeneratedField.PrimeFieldElems F)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F) (hq : 2 ^ 63 < ringChar F)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF) (walkW δF kroots b hn nodes orbit chals pubs Q)) :
    let W := walkW δF kroots b hn nodes orbit chals pubs Q
    ∃ ts : List (NTree (St × DT (ringChar F) (Quad (algebraMap F K δF)))),
      ts.length = kroots ∧ (∀ t ∈ ts, RVT (WalkVCL.F (q := ringChar F) W.X 62) t) ∧
      (bfsForest ts).map NTree.label = (List.range' 1 n).map W.lbl ∧
      (∀ t ∈ bfsForest ts, (stateSep (q := ringChar F) W.X 62).fanout t.label.1 = t.children.length) ∧
      (∀ t ∈ bfsForest ts, t.isLeaf ↔ (stateSep (q := ringChar F) W.X 62).Sleaf t.label.1) ∧
      (∀ r ∈ ts, ∃ i, 1 ≤ i ∧ i ≤ kroots ∧ r.label = W.lbl i ∧ RootOK (W.lbl i).2) := by
  intro W
  obtain ⟨-, hRG, hG⟩ := walkJ8_forest δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn
    hkp hq hout
  obtain ⟨ts, hlen, hrvt, hlab, hfan, hleaf⟩ := hG
  refine ⟨ts, hlen, hrvt, hlab, hfan, hleaf, fun r hr => ?_⟩
  obtain ⟨i, hi1, hik, he⟩ := roots_are_rows hlen hk hlab r hr
  exact ⟨i, hi1, hik, he, (hRG i hi1 hik).1⟩

end Chip

/-! ## 2. At an accepted J-8 tuple -/

section Accepts
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame

open scoped Classical in
/-- **The forest lemma at an `AcceptsJ8V` trace**: its walk view `qW` (layout `Pb`, coins `chalsMJ8 δ χ`, publics
`M.pubsW`), outside the walk event, has the walk hypotheses, the root gate and `ForestReconGoal`. The size facts
`1 ≤ kroots ≤ nW`, `kroots + nW < p` are hypotheses (they hold at `canonPb` of the canonical sizes). -/
theorem walkJ8_forest_of_accepts {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8}
    {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkW δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :
    let W := walkW δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
    WalkHyps (algebraMap (ZMod p) K δ) W ∧ RootGate W.X W.lbl W.kroots ∧
      ForestReconGoal (stateSep (q := ringChar (ZMod p)) W.X 62) W.lbl W.kroots W.h :=
  walkJ8_forest δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hA.hsatW hA.hbindW hA.hinjW
    hA.hadjW (GeneratedField.primeFieldElems_zmod p) hk hkn hkp hq hout

end Accepts

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1.walkJ8_forest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1.walkJ8_forest_roots
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1.walkJ8_forest_of_accepts
