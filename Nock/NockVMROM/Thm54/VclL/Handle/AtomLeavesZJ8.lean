/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomLeavesZJ8.lean

* §1 the `mb ≠ 0` forms (`mbVp_row` names rows with `mb ≠ 0`; P12's lemmas asked `mb = 1`):
    **`bnd_of_mb'`**, **`extB_mb'`**, **`atomLeaves_extB_of_mb'`**.
  * §2 `restr_traceK`: the restricted cell table's `𝕂` columns `< 32` are the atom chip's.
  * §3 **`mbVp_atomLeaves`**: every key `(⟨zAt, 0, leaf⟩, 0, 0, idx)` of `mbVp` is `encZY z y (atom v)` with
    `extB p r idx = atom v`: the row decodes (T1, `row_genuine` on `atomTable_accepts`) to the comb of a denoted
    limb list `l` (`denH_denotes`), so its fingerprint leaf at `y` is `leafVal y (val l)` (`G5J8.leaf_eq_leafVal`),
    and g4 on the exported row makes `val l ≥ p` and `extB` read it (`extB_mb'`).
  * §4 **`hvp_of_mb`**: the `LinkJ8` field `hvp : AtomLeaves (encJ8 δ χ) vp (extB p rA)` at
    `vp = mbVp … (chalsAJ8Z δ χ) …`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
import Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8
import Nock.NockVMROM.Thm54.VclL.Handle.G5J8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesZJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ atomGates bnd LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (TopNZ atom_g23 agree_atom denH_denotes denotes_len restr_trace)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF aEK atom_base aEK_chal)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB extB_of_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesBJ8 (big_of_bnd topNZ_of_gates)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY atomLeaves_of_g5)
open Nock.ComputeTable (FP)
open Nock.Atoms (val B)

noncomputable section

/-! ## 1. The `mb ≠ 0` forms -/

section Gates
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA

/-- **g4 (`bnd mb`) at an exported row (`mb ≠ 0`), read in ℕ.** -/
theorem bnd_of_mb' (hq : 2 ^ 63 < p) (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small) (k : Fin nA)
    (hmb : (AE k).trace AtomChipHQ.mb ≠ 0) :
    (r k).wR = 0 → (r k).aR = B - 1 ∧ (r k).aL ≠ 0 := by
  intro hw
  have hqF : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hq
  have ce : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → ((x : ℕ) : ZMod p) = y → x = y :=
    fun hx hy e => AtomChipHQ.cast_inj hqF hx hy e
  have hg := atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat k
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have g4a := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR))) (.sub (cv Cell.aR) (.const (AtomChipHQ.Bf - 1))) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g4b := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR)))
      (.sub (.mul (cv Cell.aL) (cv AtomChipHQ.invB)) (.const 1)) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  simp only [notE, cv, CoeffExpr.eval] at g4a g4b
  have hRk := hR k
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hs k
  rw [hRk.wR, hw, Nat.cast_zero, sub_zero, mul_one] at g4a g4b
  have g4a' := (mul_eq_zero.mp g4a).resolve_left hmb
  have g4b' := (mul_eq_zero.mp g4b).resolve_left hmb
  refine ⟨?_, ?_⟩
  · apply ce (by omega) (by norm_num [B])
    rw [← hRk.aR, sub_eq_zero.mp g4a', AtomChipHQ.Bf_eq, Nat.cast_sub (by norm_num [B]), Nat.cast_one]
  · intro h0
    rw [hRk.aL, h0, Nat.cast_zero, zero_mul, zero_sub] at g4b'
    exact one_ne_zero (neg_eq_zero.mp g4b')

/-- **An exported (`mb ≠ 0`) row is big and `extB` reads it.** -/
theorem extB_mb' (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small)
    (hT : TopNZ r) (k : Fin nA) (hmb : (AE k).trace AtomChipHQ.mb ≠ 0) {l : List ℕ} (hd : Denotes r k l) :
    p ≤ val l ∧ extB p r k = some (.atom (val l)) := by
  have hb : p ≤ val l := by rw [hpG]; exact big_of_bnd hT (bnd_of_mb' hq hsat hR hs k hmb) hd
  exact ⟨hb, extB_of_denotes hd hb⟩

/-- **`AtomLeaves` at `extB p rA` from g4**, every key naming an `mb ≠ 0` row (the shape `mbVp_row` gives). -/
theorem atomLeaves_extB_of_mb' {Kfp : Type} [Field Kfp] {E : Noun → FP Kfp} {vp : List (VKey Kfp)}
    (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (hA : AtomLeaves E vp (AtomDenJ8.extA r))
    (hvpRow : ∀ k ∈ vp, ∃ i : Fin nA, (AE i).trace AtomChipHQ.mb ≠ 0 ∧ k.2.2.2 = i) :
    AtomLeaves E vp (extB p r) := by
  have hT := topNZ_of_gates hsat hR hTout
  refine AtomLeavesBJ8.atomLeaves_extB hA fun k hk l hl => ?_
  obtain ⟨i, hmb, hi⟩ := hvpRow k hk
  rw [hi] at hl
  exact (extB_mb' hq hpG hsat hR hs hT i hmb hl).1

end Gates

/-! ## 2. The restricted cell table's `𝕂` columns -/

section Restr
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
  (chalsA pubsA : ℕ → K)
  (QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])

/-- The restricted cell table's `𝕂` column `r < 32` is the atom chip's. -/
theorem restr_traceK (i : Fin nA) {r : ℕ} (hr : r < 32) :
    (cellEnvK δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)
      i).trace r = (aEK δ b nodesA orbitA chalsA pubsA QA i).trace r := by
  have hw : (cellChip δ b hnA nodesA orbitA chalsA pubsA).rap.w = 225 :=
    (cellChip_fingerprint δ b hnA nodesA orbitA chalsA pubsA).1
  simp only [cellEnvK, aEK, gatherEnv, ChipTemplate.col0, cellTemplate_baseCols,
    AtomChipHQ.atomTemplateHQ_baseCols]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  erw [cellEnvF, AtomChipHQ.restrictAtomCell,
    envOfTrace_restrict_trace (cv' := slotVal b 205 chalsA) (pv' := slotVal b 205 pubsA) _ _ _ _ _ _ _ _
      (by rw [hw]; omega)]
  simp only [shiftCol, if_neg (show ¬ (129 + 3 * r + (k : ℕ) < 129) by omega)]
  congr 1
  omega

end Restr

/-! ## 3. `mbVp` keys are atom leaves at `extB` -/

/-- A3's comb and P11's comb are the same function. -/
theorem combL_eq : ∀ l : List ℕ, AtomCombJ8.combL l = G5J8.combL l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [AtomCombJ8.combL, G5J8.combL, combL_eq (b :: l)]

section Leaves
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
  (chalsA pubsA : ℕ → K)
  (QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA

variable {δ b hnA nodesA orbitA chalsA pubsA QA} in
/-- **`AtomLeaves` of the exported keys at `extB`** (g4 + g5 + T1), at any atom vector whose leaves `37 / 38`
carry `z`. -/
theorem mbVp_atomLeaves (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small)
    (hidx : ∀ k : Fin nA, (r k).idx = k) (hB : LimbsBounded r) (hwR : ∀ k : Fin nA, (r k).wR ≤ 1)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (z : 𝕂′) (hzAt : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 37) (chalsA 38) = z) :
    AtomLeaves (encZY z (Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3)))
      (AcceptsJ8P.mbVp δ b nodesA orbitA chalsA pubsA QA) (extB p r) := by
  set y := Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) with hyd
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  intro k hk
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hk
  split_ifs at hi with h0
  · simp at hi
  rw [List.mem_singleton] at hi
  subst hi
  have Ri := hR i
  obtain ⟨s1, -⟩ := hs i
  have hidxv : ((AE i).trace Cell.idx).val = i := by
    rw [Ri.idx, ZMod.val_natCast, hidx i, Nat.mod_eq_of_lt (by omega)]
  -- T1 on the atom table
  have hT := AtomChipHQ.atomTable_accepts δ b hnA nodesA orbitA chalsA pubsA hF (by rw [hrc]; exact hq) hy QA
    hsat hbind hinj hadj (by rw [hrc]; exact hnp) hserved []
  set c := cellRowOf δ (cellEnvK δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i)
      (cellEnvF b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i) with hc
  have hcm : c ∈ cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) := List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨L, Rn, hd, hp, -⟩ := Nock.NockVMROM.Thm54.VclL.row_genuine (by rw [hrc]; exact hq) hy hT hcm
  have hcidx : c.b0.idx = i := by
    simp only [hc, cellRowOf, cellB0Of]
    rw [restr_trace δ b hnA nodesA orbitA chalsA pubsA QA i (by decide), Ri.idx,
      natOf_natCast hF (by rw [hrc]; omega), hidx i]
  have hser := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsat) hF
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbind) hinj hadj
    (by rw [hrc]; exact hnp)
  have hag := agree_atom hq hsat hR hs hidx hB hwR
  obtain ⟨l, hl, hTl, -⟩ := denH_denotes hser (fun c hc => (hag c hc).2) (i := i)
    (by rw [denH_cell, ← hcidx]; exact hd)
  have hTZ := topNZ_of_gates hsat hR hTout
  obtain ⟨hbig, hext⟩ := extB_mb' hq hpG hsat hR hs hTZ i h0 hl
  -- the leaf column is the row fingerprint's leaf
  have hleaf : (QE.var (Cell.pR + 4) : QE (ZMod p)).ev δ (aEK δ b nodesA orbitA chalsA pubsA QA i) (AE i) =
      c.p.leaf := by
    simp only [hc, cellRowOf, QFP.ev, QFP.var, ev_var]
    rw [restr_traceK δ b hnA nodesA orbitA chalsA pubsA QA i (by decide),
      restr_traceK δ b hnA nodesA orbitA chalsA pubsA QA i (by decide)]
  have hne : l ≠ [] := by
    intro e; have := denotes_len hl; rw [e] at this; simp at this
  have hlv : c.p.leaf = Nock.Atoms.leafVal y (val l) := by
    rw [hp, hTl, combL_eq]
    exact G5J8.leaf_eq_leafVal (GlobalCarryRecognizer.enc y) y
      (fun u v => GlobalCarryRecognizer.enc_cons hy u v) hne
      (fun a _ => GlobalCarryRecognizer.enc_atom y a) (hl.bounded hB) (hpG ▸ hbig)
  refine ⟨rfl, rfl, val l, ?_, ?_⟩
  · simp only; rw [hidxv]; exact hext
  · simp only [AcceptsJ8P.mbFP, encZY, FP.atomFP]
    rw [hleaf, hlv]
    congr 1
    simp only [AtomChipHQ.zAt, ev_chal, aEK_chal]
    exact hzAt

end Leaves

/-! ## 4. `hvp` at the rewired vector -/

section HVP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_y chalsAJ8Z_zAt)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {pubsA : ℕ → K}

/-- **`hvp` (the `LinkJ8` field) at the rewired atom vector**: the exported keys read from the committed
`mb` rows (`toMsgJ8`'s `vp`) are atom leaves of `encJ8 δ χ = encZY z y` at `extB p rA`. -/
theorem hvp_of_mb (χ : Coins frameJ8 K)
    {QA : Fin (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).rap.w → (ZMod p)[X]}
    (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p)
    (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b nodesA orbitA (chalsAJ8Z δ χ) pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA QA)))
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (aEF b nodesA orbitA (chalsAJ8Z δ χ) pubsA QA k) (r k))
    (hs : ∀ k : Fin nA, (r k).Small)
    (hidx : ∀ k : Fin nA, (r k).idx = k) (hB : LimbsBounded r) (hwR : ∀ k : Fin nA, (r k).wR ≤ 1)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0) :
    AtomLeaves (AcceptsJ8.encJ8 δ χ) (AcceptsJ8P.mbVp δ b nodesA orbitA (chalsAJ8Z δ χ) pubsA QA) (extB p r) := by
  have h := mbVp_atomLeaves hq hpG hsat hbind hinj hadj hnp hy hserved hR hs hidx hB hwR hTout
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (chalsAJ8Z_zAt δ χ)
  rwa [chalsAJ8Z_y δ χ] at h

end HVP

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesZJ8
