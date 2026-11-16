/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8AW.lean

  One chip template (`walkChipHQK` at the atom walk's roots),
  data as parameters.

  * **`awOK_present`**: at `krootsV ≥ 1` the atom walk's honest trace (`WalkTraceHQ.walkTraceHQ`, kinds in `{0,1,2}`)
    is accepted and bound by `walkChipHQK` (`HonestK8.walkTwinK_accepted`), so `AWChipOK` holds in its present form.
    Inputs: the 39th's walk chip honest at the atom-walk reads with its preprocessing (`hok`, the same lemma the J-8
    walk takes from L2), the kinds, the three non-vanishing denominators (bad events), the two terminals (balances),
    the nodes and the root count.
  * **`awOK_absent`**: at `krootsV = 0` (no op-5 row compares two big atoms) `AWChipOK` holds for ANY trace once the
    six atom-walk publics are `0`.
  * **`awOK_list`**: the atom walk at the SPEC rows (`walkRows` / `krW` of the atom cell list and the atom-walk
    reads), from L2's `walkOk_honest_list` (needs `WalkDepthOK preads`: every atom-walk read of depth `≤ 61`).
  * **Staging**: `stA_gen` (the honest atom-table trace is staged at `crA`, given the cell part's base columns
    coin-free and its round-1 roles reading only round-`0` coins), `stV_gen` (the honest atom-walk trace at `crW`).
  * **The J-8 instance** `atomOK_j8`: the generator's atom table of every generated run at Goldilocks
    (`rowsJ8` = `tabOf` of L0's `acs` / `info` / `mb`) is accepted and bound by both atom chip views, from the run
    binders, the cell part carrying the generator's cell data (`hcol`) and L2's `hsat0`, the denominators and the
    terminals (`ComplJ8Atom.valid_j8` + `row_cell` + `atomOK_of_rows`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Module
open scoped Polynomial

noncomputable section

section AW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
  (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chals pubs : ℕ → K)
  (col : ℕ → Fin nV → ZMod p) (kLv vLv kRv vRv : Fin nV → ZMod p)

/-- **The atom walk, present** (`krootsV ≥ 1`): the honest walk trace is accepted and bound by `walkChipHQK`, so
`AWChipOK` holds. -/
theorem awOK_present (hinj : Function.Injective nodesV)
    (hadj : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hok : RAP.SatisfiesWithPreprocessing (walkChipOk δ krootsV b hnV nodesV orbitV chals pubs true)
      (fun j => honestQ hnV nodesV col 132
        (Fin.cast (walkChipOk_w δ krootsV b hnV nodesV orbitV chals pubs true) j)))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δ krootsV b hnV nodesV orbitV chals pubs WalkHC.xKeyH col kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δ krootsV b hnV nodesV orbitV chals pubs WalkHC.recLH col kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δ krootsV b hnV nodesV orbitV chals pubs WalkHC.recRH col kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range nV,
      (WalkTraceHQ.dN δ krootsV b hnV nodesV orbitV chals pubs col kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range nV,
      (liftQ δ (WalkTraceH.cN j (col WChip.mL)) *
          (WalkTraceHQ.dN δ krootsV b hnV nodesV orbitV chals pubs col kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δ (WalkTraceH.cN j (col WChip.mR)) *
          (WalkTraceHQ.dN δ krootsV b hnV nodesV orbitV chals pubs col kLv vLv kRv vRv WalkHC.recRH j)⁻¹))
    (hk1 : 1 ≤ krootsV) (hk2 : krootsV ≤ nV) (hk3 : krootsV + nV < ringChar (ZMod p)) :
    AWChipOK δ b krootsV hnV nodesV orbitV chals pubs
      (fun j => WalkTraceHQ.walkTraceHQ δ krootsV b hnV nodesV orbitV chals pubs col kLv vLv kRv vRv
        (Fin.cast (walkChipHQK_width δ krootsV b hnV nodesV orbitV chals pubs) j)) := by
  obtain ⟨hsat, hbind⟩ := HonestK8.walkTwinK_accepted δ krootsV b hnV nodesV orbitV chals pubs col kLv vLv kRv vRv
    hinj hadj hok hkL hkR hpX hpL hpR hpubX hpubP
  exact Or.inl ⟨hsat, hbind, hinj, hadj, hk1, hk2, hk3⟩

/-- **The atom walk, absent** (`krootsV = 0`): `AWChipOK` holds for any trace once the six atom-walk publics the
verifier reads are `0`. -/
theorem awOK_absent (h0 : krootsV = 0)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chals pubs).rap.w → (ZMod p)[X])
    (hp : pubs 0 = 0 ∧ pubs 1 = 0 ∧ pubs WalkHQ.pubXQ = 0 ∧ pubs (WalkHQ.pubXQ + 1) = 0 ∧
      pubs WalkHQ.pubPQ = 0 ∧ pubs (WalkHQ.pubPQ + 1) = 0) :
    AWChipOK δ b krootsV hnV nodesV orbitV chals pubs QV :=
  Or.inr ⟨h0, hp⟩

end AW

/-! ## Staging: the honest atom-table and atom-walk traces are staged (`StJ8`'s `A` and `V` parts) -/

section Stage
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (crA crW)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage (all_of_two zero_of_one)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- **The honest atom-table trace is staged** (`crA`): the cell part's base columns are coin-free and its round-1
roles (`130 .. 183`) read only the coins sampled after round `0`; the added columns `newB` are coin-free; every
round-`2` column is free. -/
theorem stA_gen {nA hA : ℕ} (hnA : 0 < nA) (nodes : Fin nA → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : Coins frameJ8 K → ℕ → K) (col : Coins frameJ8 K → ℕ → Fin nA → ZMod p)
    (newB : ℕ → Fin nA → ZMod p)
    (hc0 : ∀ χ χ', ∀ k < 130, col χ k = col χ' k)
    (hc1 : ∀ χ χ', (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → ∀ k < 184, col χ k = col χ' k) :
    StagedCols frameJ8 crA (fun χ (j : Fin 349) =>
      HonestA8.atomTraceHQ δ b hnA nodes orbit (chalsA χ) (pubsA χ) (col χ) newB j) := by
  intro j χ χ' h
  by_cases h2 : 259 ≤ (j : ℕ)
  · rw [all_of_two χ χ' (crA j) (by simp only [crA]; split_ifs <;> omega) h]
  · unfold HonestA8.atomTraceHQ
    refine honestQ_congr _ _ _ _ _ _ ?_
    have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
    funext i
    simp only [HonestA8.colA, extColF, hW]
    by_cases h1 : (j : ℕ) < 130
    · simp only [if_pos h1]; rw [hc0 χ χ' j h1]
    · simp only [if_neg h1]
      by_cases h3 : (j : ℕ) < 205
      · simp only [if_pos h3, HonestA8.newFull, if_pos (show (j : ℕ) < 313 by omega)]
      · have h4 : (j : ℕ) < 238 + (205 - 130) := by omega
        simp only [if_neg h3, if_pos h4]
        rw [hc1 χ χ' (zero_of_one χ χ' (crA j) (by simp only [crA]; split_ifs <;> omega) h) _ (by omega)]

/-- **The honest atom-walk trace is staged** (`crW`): the 39th walk columns' base (`< 21`) coin-free, their
round-1 roles (`21 .. 92`) read only round-`0` coins; `kL vL kR vR` coin-free; round `2` free. -/
theorem stV_gen (krootsV : ℕ) {nV hV : ℕ} (hnV : 0 < nV) (nodes : Fin nV → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : Coins frameJ8 K → ℕ → K)
    (col : Coins frameJ8 K → ℕ → Fin nV → ZMod p) (kLv vLv kRv vRv : Fin nV → ZMod p)
    (hc0 : ∀ χ χ', ∀ k < 21, col χ k = col χ' k)
    (hc1 : ∀ χ χ', (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) → ∀ k < 93, col χ k = col χ' k) :
    StagedCols frameJ8 crW (fun χ (j : Fin 166) =>
      WalkTraceHQ.walkTraceHQ δ krootsV b hnV nodes orbit (chalsV χ) (pubsV χ) (col χ) kLv vLv kRv vRv
        (Fin.cast (WalkTraceHQ.walkTemplateHQ_width δ krootsV).symm j)) := by
  intro j χ χ' h
  by_cases h2 : 97 ≤ (j : ℕ)
  · rw [all_of_two χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) h]
  · unfold WalkTraceHQ.walkTraceHQ
    refine honestQ_congr _ _ _ _ _ _ ?_
    have hW : (walkTemplate δ krootsV).width 3 = 132 := WalkTraceH.walkTemplate_width δ krootsV
    funext i
    simp only [WalkTraceHQ.colHQ, extColF, hW, Fin.val_cast]
    by_cases h1 : (j : ℕ) < 21
    · simp only [if_pos h1]; rw [hc0 χ χ' j h1]
    · simp only [if_neg h1]
      by_cases h3 : (j : ℕ) < 25
      · simp only [if_pos h3, WalkTraceHQ.new, show ¬ (136 ≤ (j : ℕ) ∧ (j : ℕ) < 166) by omega, if_false,
          and_false]
      · have h4 : (j : ℕ) < 132 + (25 - 21) := by omega
        simp only [if_neg h3, if_pos h4]
        rw [hc1 χ χ' (zero_of_one χ χ' (crW j) (by simp only [crW]; split_ifs <;> omega) h) _ (by omega)]

end Stage

/-! ## The J-8 instance: the generator's atom table at a good coin -/

section J8Inst
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ pubMB pubC pubMI mb inc mi)
open Nock.Edit Nock.Edit.GenX

variable {K : Type} [Field K] [Algebra (ZMod Nock.Atoms.p) K] [FiniteDimensional (ZMod Nock.Atoms.p) K]
  [Fintype K] (δ : ZMod Nock.Atoms.p) [Fact (¬ IsSquare (algebraMap (ZMod Nock.Atoms.p) K δ))]
  (b : Basis (Fin 3) (ZMod Nock.Atoms.p) K)
  (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  {hA : ℕ} (hn : 0 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length)
  (nodes : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)
  (orbit : StrictOrbitDomain (ZMod Nock.Atoms.p) 3 hA) (chals pubs : ℕ → K)
  (col : ℕ → Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)

/-- The honest atom rows of a generated run (`tabOf` of L0's data). -/
abbrev rowsJ8 : ℕ → NRow :=
  (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info
    (j8DataOf Nock.Atoms.p Rg Rt hgen).mb (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).row

/-- **The generator's atom table at a good coin** (J-8 instance, Goldilocks): `atomChipHQ` and `atomChipHQL` are
satisfied and bound by the honest trace `atomTraceHQ … col (newOf rowsJ8)`.  Inputs: the run binders and
`hcor` (no inc corner, GLA fix (B); the J-8 name `atomOK_j8` under `complJ8`'s binders is in `ComplJ8OfAtom`); the cell
part `col` carries the generator's cell data of `acs` (`hcol`, as `GenMem.cellD`) and is accepted by `cellChipHQ`
(`hsat0`, L2's lemma at the atom cell list); the three non-vanishing atom denominators (bad events); the three
atom terminals (balances); the nodes. -/
theorem atomOK_j8_gen (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin _) (hi : (i : ℕ) + 1 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      col Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.idR i = (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs
        (j8DataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ))
        : ZMod Nock.Atoms.p) ∧
      col Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p))
    (hsat0 : (cellChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹) :
    (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) ∧
      (atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)))) := by
  have hv := valid_j8_gen Rg Rt hgen hax hop5 hN
  have hg := genHyp_j8 Rg Rt hgen hax hop5 hN
  obtain ⟨hok, hlast⟩ := AtomTab.rows_ok hv (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) rfl
  have hB : Nock.Atoms.B < ringChar (ZMod Nock.Atoms.p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nock.Atoms.B_lt_p
  refine atomOK_of_rows δ b hn nodes orbit chals pubs col hinj hadj hB (rowsJ8 Rg Rt hgen) (fun i => ?_) hok hlast
    hsat0 hz1 hz2 hz3 hpMB hpC hpMI
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcol i
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := row_cell _ _ _ _ hg (j8DataOf Nock.Atoms.p Rg Rt hgen).info i i.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e1.symm
  · rw [c2]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e6.symm
  · rw [c3]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e4.symm
  · rw [c4]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e5.symm
  · rw [c5]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e2.symm
  · rw [c6]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e3.symm

end J8Inst

/-! ## The atom walk at the SPEC rows (`walkRows` / `krW` of the atom-walk reads; L2's `walkOk_honest_list`) -/

section AWList
open Nock.NockVMROM.Thm54.VclL.GenWalk (krW walkRows one_le_krW krW_le_rows)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
  (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom walk at the spec rows** (`krootsV = krW cells preads ≥ 1`, `nV = |walkRows cells preads|`): the honest
atom-walk trace (L2's `wColB` at the atom cell list `cells` and the atom-walk reads `preads`) is accepted and bound
by `walkChipHQK`, so `AWChipOK` holds.  Inputs: L2's `walkOk_honest_list` hypotheses (depth `≤ 61` reads
`WalkDepthOK preads`, the IO poles and terminals), the child kinds, the handle poles and terminals. -/
theorem awOK_list (z γ ρ : 𝕂′) (cells : List Noun) (preads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin nV → ZMod p)
    (hq : 2 ^ 63 < ringChar (ZMod p)) (hcells : cells.length < ringChar (ZMod p))
    (h61 : WalkDepthOK preads) (hkp : krW cells preads + (walkRows cells preads).length < ringChar (ZMod p))
    (hN : nV = (walkRows cells preads).length)
    (hinj : Function.Injective nodesV)
    (hadj : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hok : ChalsOK δ chals γ ρ 11)
    (hx : ∀ j < nV, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δ (wRowsB δ chals z cells preads j)) ≠ 0)
    (hL : ∀ j < nV, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δ (wRowsB δ chals z cells preads j)) ≠ 0)
    (hR : ∀ j < nV, FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δ (wRowsB δ chals z cells preads j)) ≠ 0)
    (hXt : ∑ k ∈ Finset.range nV, (walkFillInv δ γ ρ (wRowsB δ chals z cells preads k)).xInv =
      Quad.mk _ (pubs 0) (pubs 1))
    (hPt : ∑ k ∈ Finset.range nV, wpTermV δ (walkFillInv δ γ ρ (wRowsB δ chals z cells preads k)) =
      Quad.mk _ (pubs 2) (pubs 3))
    (hkL : ∀ i, kLv i = 0 ∨ kLv i = 1 ∨ kLv i = 2) (hkR : ∀ i, kRv i = 0 ∨ kRv i = 1 ∨ kRv i = 2)
    (hpX : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.xKeyH
      (wColB δ b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpL : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.recLH
      (wColB δ b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpR : ∀ i, WalkTraceHQ.dRow δ (krW cells preads) b hnV nodesV orbitV chals pubs WalkHC.recRH
      (wColB δ b chals z γ ρ cells preads) kLv vLv kRv vRv i ≠ 0)
    (hpubX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = ∑ j ∈ Finset.range nV,
      (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColB δ b chals z γ ρ cells preads)
        kLv vLv kRv vRv WalkHC.xKeyH j)⁻¹)
    (hpubP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) = ∑ j ∈ Finset.range nV,
      (liftQ δ (WalkTraceH.cN j (wColB (n := nV) δ b chals z γ ρ cells preads WChip.mL)) *
          (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColB δ b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recLH j)⁻¹ +
        liftQ δ (WalkTraceH.cN j (wColB (n := nV) δ b chals z γ ρ cells preads WChip.mR)) *
          (WalkTraceHQ.dN δ (krW cells preads) b hnV nodesV orbitV chals pubs (wColB δ b chals z γ ρ cells preads)
            kLv vLv kRv vRv WalkHC.recRH j)⁻¹)) :
    AWChipOK δ b (krW cells preads) hnV nodesV orbitV chals pubs
      (fun j => WalkTraceHQ.walkTraceHQ δ (krW cells preads) b hnV nodesV orbitV chals pubs
        (wColB δ b chals z γ ρ cells preads) kLv vLv kRv vRv
        (Fin.cast (walkChipHQK_width δ (krW cells preads) b hnV nodesV orbitV chals pubs) j)) :=
  awOK_present δ b (krW cells preads) hnV nodesV orbitV chals pubs _ kLv vLv kRv vRv hinj hadj
    (walkOk_honest_list δ b hnV nodesV orbitV chals pubs z γ ρ cells preads
      (GeneratedField.primeFieldElems_zmod p) hq hcells h61 hkp hN hinj hadj hok hx hL hR hXt hPt)
    hkL hkR hpX hpL hpR hpubX hpubP (one_le_krW cells preads) (hN ▸ krW_le_rows cells preads) (by omega)

end AWList

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
