/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalA.lean

  **J-9 AL completeness, part 4: the atom/cell export publics of the mixed record.**
  The mixed record takes `pubsC pubsJ pubsA` from the J-8 overlay record `B8L` at `DL`
  but everything else from `BA`; the four fields `hbalA' hvalA0 hfxC hfxA` compare `(B8L.M χ).pubsA / pubsC`
  with `BA`'s walk publics.  `DL` differs from `DA` in the J layer, the three multiplicities `mv mh mb`; the
  atom table's `mb` column (196) is the only column of the atom row environment below `205` that changes, and
  no atom publics `0 .. 5, 10, 11` read it, so those publics are those of `DA` (`pubsA_L`), whatever the
  orbit (`aHx_orb`, `cX_orb`-style).  The cell export publics `2 / 3` do not read `mv`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalV2
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalA

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalX
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (ezA aHx cX)
open Nock.Jet.Prim (PrimOp)

noncomputable section

section Transfer
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen

theorem newOf_mb_congr {n : ℕ} (rows : ℕ → ComplJ8Atom.NRow) (m : ℕ → ℕ) (c : ℕ) (hc : c ≠ 196) (i : Fin n) :
    ComplJ8Atom.newOf (F := ZMod p) (n := n) (fun j => { rows j with mb := m j }) c i =
      ComplJ8Atom.newOf (F := ZMod p) (n := n) rows c i := by
  unfold ComplJ8Atom.newOf
  by_cases h1 : c < 162
  · simp only [h1, if_true]
  by_cases h2 : c < 194
  · simp only [h1, h2, if_true, if_false]
  by_cases h3 : c = 194
  · simp only [h1, h2, h3, if_true, if_false]
  by_cases h4 : c = 195
  · simp only [h1, h2, h3, h4, if_true, if_false]
  simp only [h1, h2, h3, h4, hc, if_false]

/-- The atom row table's columns other than the `mb` column (`196`) are the base's. -/
theorem newBA_ne_mb (c : ℕ) (hc : c ≠ 196) (i : Fin (DA).acs.length) : newBA (DL) c i = newBA (DA) c i :=
  newOf_mb_congr (n := (DA).acs.length) (ComplJ8Atom.tabOf (DA).acs (DA).info (DA).mb (DA).rows).row
    (fun j => (DL).mb.getD j 0) c hc i

/-- **The atom row environment's current row below `205` (but for the `mb` column) is the base's**, whatever the
orbits and publics. -/
theorem ezA_trace_LA (hA : 0 < (DA).acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (DA).acs.length)) (hinj' : Function.Injective (powN o' (DA).acs.length))
    (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (i : Fin (DA).acs.length) : ∀ j < 205, j ≠ 196 →
      (ezA δ b (DL) hA o χ pubs i).trace j = (ezA δ b (DA) hA o' χ pubs' i).trace j := by
  intro j hj hj196
  have hw : j < (AtomChipHQ.atomTemplateHQ δ).width 3 := by rw [HonestA8.atomTemplateHQ_width]; omega
  have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
  have hcol : HonestA8.colZ δ (colAH δ b (DL) hA o χ pubs) (newBA (DL)) j =
      HonestA8.colZ δ (colAH δ b (DA) hA o' χ pubs') (newBA (DA)) j := by
    funext i'
    simp only [HonestA8.colZ, extColF, hW, HonestA8.newZ]
    split_ifs with h1 h2 h3
    · exact congrFun (colAH_orb δ b (DA) hA o o' χ pubs pubs' j (by omega)) i'
    · exact newBA_ne_mb Rt hgen prims j hj196 i'
    · rfl
  have e1 : (ezA δ b (DL) hA o χ pubs i).trace j =
      fullCol hA (HonestA8.colZ δ (colAH δ b (DL) hA o χ pubs) (newBA (DL))) j i :=
    env_trace hA (powN o _) hinj _ o.ω _ _ i hw
  have e2 : (ezA δ b (DA) hA o' χ pubs' i).trace j =
      fullCol hA (HonestA8.colZ δ (colAH δ b (DA) hA o' χ pubs') (newBA (DA))) j i :=
    env_trace hA (powN o' _) hinj' _ o'.ω _ _ i hw
  rw [e1, e2]
  unfold fullCol
  split_ifs <;> first | exact congrFun hcol i | rfl

/-- The pole-free part of the inc denominator is the base's (read set `200 .. 203`, no `mb`). -/
theorem cX_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (DA).acs.length)) (hinj' : Function.Injective (powN o' (DA).acs.length))
    (χ : Coins frameJ8 K) (j : ℕ) :
    cX δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o j χ =
      cX δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' j χ := by
  unfold cX
  by_cases hj : j < (DA).acs.length
  · have hjL : j < (DL).acs.length := hj
    rw [dif_pos hjL, dif_pos hj]
    have hz := fun k hk hk' => ezA_trace_LA δ b Rt hgen prims (ComplJ9ADataRec.acsA_pos Rt hgen) o o' hinj hinj' χ
      (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ)
      (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ) ⟨j, hj⟩ k hk hk'
    have e : ServeH.keyVec5 (K := K) AtomChipHQ.oldKey
        (ezA δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
          (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ) ⟨j, hjL⟩) =
        ServeH.keyVec5 (K := K) AtomChipHQ.oldKey
        (ezA δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ
          (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ) ⟨j, hj⟩) := by
      have e0 := hz 200 (by norm_num) (by norm_num)
      have e1 := hz 201 (by norm_num) (by norm_num)
      have e2 := hz 202 (by norm_num) (by norm_num)
      have e3 := hz 203 (by norm_num) (by norm_num)
      funext c
      fin_cases c
      · simp only [ServeH.keyVec5, AtomChipHQ.oldKey, cv]
        exact congrArg _ e0
      · simp [ServeH.keyVec5, AtomChipHQ.oldKey, CoeffExpr.eval]
      · simp only [ServeH.keyVec5, AtomChipHQ.oldKey, cv]
        exact congrArg _ e1
      · simp only [ServeH.keyVec5, AtomChipHQ.oldKey, cv]
        exact congrArg _ e2
      · simp only [ServeH.keyVec5, AtomChipHQ.oldKey, cv]
        exact congrArg _ e3
    rw [e]
  · have hjL : ¬ j < (DL).acs.length := hj
    rw [dif_neg hjL, dif_neg hj]

theorem hqSum_eq (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (P : ℕ → K) :
    ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
        (CellTraceHQ.dN δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) P (aCol δ b D χ) (mhvA D) j)⁻¹ =
      ∑ j ∈ Finset.range D.acs.length,
        liftQ δ (CellTraceH.mN (mhvA D) j) * (ComplJ8Bad.ρH δ χ + aHx δ b D hA o j χ)⁻¹ := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [CellTraceHQ.dN, dif_pos hj']
  rw [ComplJ8OfAtom.aRow_split δ b D hA o χ _ ⟨j, hj'⟩]

theorem dNat_dC_eq (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (j : ℕ) (hj : j < D.acs.length) :
    HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
        (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)) j =
      ComplJ8Bad.ρH δ χ + cX δ b D hA o j χ := by
  unfold HonestA8.dNat
  rw [dif_pos hj, ComplJ8OfAtom.dC_eq]
  unfold cX
  rw [dif_pos hj]

/-- **The atom publics `0 .. 3`** are the base's (they read neither `mv`, `mh`, `mb`, nor the orbit). -/
theorem pubsA_lo_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (χ : Coins frameJ8 K) (k : ℕ) (hk : k < 4) :
    pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ k =
      pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ k := by
  have hL := ComplJ8OfAtom.pubsA_lo δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
  have hA := ComplJ8OfAtom.pubsA_lo δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ
  by_cases h2 : k < 2
  · rw [hL.1 k h2, hA.1 k h2]
    rfl
  · rw [hL.2.1 k (by omega) hk, hA.2.1 k (by omega) hk]
    rfl

/-- **The atom cell part's handle export** is the base's, at any two injective orbits. -/
theorem pubsA_hq_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (DA).acs.length)) (hinj' : Function.Injective (powN o' (DA).acs.length))
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ CellHQ.pubHQ)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ CellHQ.pubHQ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ (CellHQ.pubHQ + 1)) := by
  obtain ⟨-, -, tL, -, -, -⟩ := ComplJ8OfAtom.atomTerms δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
  obtain ⟨-, -, tA, -, -, -⟩ := ComplJ8OfAtom.atomTerms δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ
  rw [tL, tA, hqSum_eq, hqSum_eq]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : aHx δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o j χ =
      aHx δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' j χ :=
    aHx_orb δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o o' hinj hinj' j χ
  rw [e]
  rfl

/-- **The atom inc terminal** is the base's, at any two injective orbits (the inc row's read set avoids `mb`). -/
theorem pubsA_inc_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (DA).acs.length)) (hinj' : Function.Injective (powN o' (DA).acs.length))
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ AtomChipHQ.pubC)
        (pubsAOf δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ (AtomChipHQ.pubC + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ AtomChipHQ.pubC)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ (AtomChipHQ.pubC + 1)) := by
  obtain ⟨-, -, -, -, tL, -⟩ := ComplJ8OfAtom.atomTerms δ b (DL) (ComplJ9ALData.acsL_pos Rt prims hgen) o χ
  obtain ⟨-, -, -, -, tA, -⟩ := ComplJ8OfAtom.atomTerms δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o' χ
  rw [tL, tA]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have hjL : j < (DL).acs.length := hj'
  rw [dNat_dC_eq δ b (DL) _ o χ j hjL, dNat_dC_eq δ b (DA) _ o' χ j hj', cX_LA δ b Rt hgen prims o o' hinj hinj' χ j]
  have hc : HonestA8.cNat j (newBA (DL) AtomChipHQ.inc) = HonestA8.cNat j (newBA (DA) AtomChipHQ.inc) := by
    unfold HonestA8.cNat
    rw [dif_pos hjL, dif_pos hj']
    exact newBA_ne_mb Rt hgen prims AtomChipHQ.inc (by decide) ⟨j, hj'⟩
  rw [hc]

/-- **The cell export publics `2 / 3`** are the base's (they read the fingerprint export, not `mv`). -/
theorem pubsC_x_LA {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (χ : Coins frameJ8 K) (k : ℕ) (hk : 2 ≤ k) (hk4 : k < 4) :
    pubsCOf δ b (DL) (ComplJ9ALData.cellsL_pos Rt prims hgen) o χ k =
      pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o' χ k := by
  have e : cxT δ (DL) χ = cxT δ (DA) χ := by
    unfold cxT
    refine Finset.sum_congr rfl fun k hk => ?_
    rfl
  simp only [pubsCOf, pubsC0, if_pos hk4, show ¬ k < 2 by omega, if_false, e]

end Transfer

/-! ## The four fields at the mixed record -/

section Fields
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))
  (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A

include hpG h31A h31

theorem hinj_LA : Function.Injective (powN (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) (DA).acs.length) ∧
    Function.Injective (powN (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (DA).acs.length) := by
  have hmL : (DL).acs.length ∈ sizesJ8 (DL) := by simp [sizesJ8]
  have hmA : (DA).acs.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  exact ⟨(powN_ok (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) (le_two_pow_ht (DL) hmL)).1,
    (powN_ok (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (le_two_pow_ht (DA) hmA)).1⟩

/-- **`hvalA0` at the mixed record**: the atom validity publics `0 / 1` of the overlay record. -/
theorem hvalA0_L (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA 0 = 0 ∧ ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA 1 = 0 := by
  have h := ComplJ9ABalGen.hvalA0_A δ b Rt hgen hpG h31A χ hχ
  have e : ∀ k, k < 4 → ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA k = ((BA).M χ).pubsA k := fun k hk =>
    pubsA_lo_LA δ b Rt hgen prims _ _ χ k hk
  rw [e 0 (by norm_num), e 1 (by norm_num)]
  exact h

/-- **`hfxA` at the mixed record**. -/
theorem hfxA_L (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA 2 = ((BA).M χ).pubsV 0 ∧
      ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA 3 = ((BA).M χ).pubsV 1 := by
  have h := ComplJ9ABalFA.hfxA_A δ b Rt hgen hpG h31A hax9 hwalkA χ hχ
  have e : ∀ k, k < 4 → ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA k = ((BA).M χ).pubsA k := fun k hk =>
    pubsA_lo_LA δ b Rt hgen prims _ _ χ k hk
  rw [e 2 (by norm_num), e 3 (by norm_num)]
  exact h

/-- **`hfxC` at the mixed record**. -/
theorem hfxC_L (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    ((B8L δ b Rt hgen prims hpG h31).M χ).pubsC 2 = ((BA).M χ).pubsW 0 ∧
      ((B8L δ b Rt hgen prims hpG h31).M χ).pubsC 3 = ((BA).M χ).pubsW 1 := by
  have h := ComplJ9ABalGen.hfxC_A_of δ b Rt hgen hpG h31A hwalk9 (ComplJ9ABalW.hslotA hgen)
    (ComplJ9ABalW.hrootA hgen) χ hχ
  have e : ∀ k, 2 ≤ k → k < 4 → ((B8L δ b Rt hgen prims hpG h31).M χ).pubsC k = ((BA).M χ).pubsC k :=
    fun k hk hk4 => pubsC_x_LA δ b Rt hgen prims _ _ χ k hk hk4
  rw [e 2 (by norm_num) (by norm_num), e 3 (by norm_num) (by norm_num)]
  exact h

/-- **`hbalA'` at the mixed record**: the atom export balance, the atom table from the overlay record and the
walk's handle import from the base. -/
theorem hbalA_L (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    Quad.mk (algebraMap (ZMod p) K δ) (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA CellHQ.pubHQ)
        (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA AtomChipHQ.pubC)
          (((B8L δ b Rt hgen prims hpG h31).M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsV WalkHQ.pubXQ) (((BA).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  obtain ⟨hiL, hiA⟩ := hinj_LA Rt hgen prims hpG h31A h31
  have h := ComplJ9ABalO.hbalA_A δ b Rt hgen hpG h31A hax9 hwalkA χ hχ
  have eL : ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA = pubsAOf δ b (DL)
      (ComplJ9ALData.acsL_pos Rt prims hgen) (orbJ8 (DL) (hFL Rt hgen prims hpG h31)) χ := rfl
  have eA : ((BA).M χ).pubsA = pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen)
      (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ := rfl
  rw [eA] at h
  rw [eL, pubsA_hq_LA δ b Rt hgen prims _ _ hiL hiA χ, pubsA_inc_LA δ b Rt hgen prims _ _ hiL hiA χ]
  exact h

end Fields

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalA
