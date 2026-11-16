/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHMemSat.lean

  **Honest link, file 1: the cell table, the J chip and the atom table at the J-9 AL data `DL`,
  restated at an ARBITRARY orbit `o`.**
  Twins of `GenPortJ9AHMemSat.cellOK_run_at` / `jOK_at` / `jOK_absent_at` and `GenPortJ9AHMemSat2.atomOK_runAo`, with
  `j9aDataOf` replaced by `j9alDataOf` and the base-case proofs of `ComplJ9ALTables.cellOK_L` / `atomOK_L`
  (`orbJ8 _ hF` replaced by `o`; `hinj hadj` supplied).  The J binder is the prim-aware `hRtJ`
  (`ComplJ9ALData.jrows_gateL`).  The coin hypotheses are the family-wise `∀ e ∈ fam, χ ∉ e.ev`; `hin_B8L` turns
  `(B8L …).Good χ` into them.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALTables
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMemSat

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM qJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables (lt31)
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 0. The coin hypothesis -/

section Good
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

/-- **`B8L.Good χ` gives every family of the lanes' list** (the `ComplJ8Bad.good_spec` step of `cellOK_L`). -/
theorem hin_B8L (χ : Coins frameJ8 K) (hχ : (ComplJ9ALRun.B8L δ b Rt hgen prims hpG h31).Good χ) :
    ∀ L ∈ ComplJ9ALRun.famsJL δ b Rt hgen prims hpG h31, ∀ e ∈ L, χ ∉ e.ev := by
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j9alDataOf p Rg Rt prims hgen).t]).length)]
      (ComplJ9ALRun.famsJL δ b Rt hgen prims hpG h31)), χ ∉ e.1 := hχ
  exact fun L hL e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))

end Good

/-! ## 1. The cell table at `DL`, arbitrary orbit -/

section Cell
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **`GenPortJ9AHMemSat.cellOK_run_at` at `DL`** (arbitrary orbit `o`; nodes `powN o n`, `hinj hadj` as
hypotheses).  The cell table's `mv`/`mh` are the overlay's bumped counts, read only through the poles
`famCellV`/`famCellH` (generic in the data) and the publics. -/
theorem cellOK_run_atL (hC : 0 < (DL).cells.length)
    (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DL).cells.length))
    (hadj : ∀ (i : Fin (DL).cells.length) (hi : (i : ℕ) + 1 < (DL).cells.length),
      powN o (DL).cells.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DL).cells.length i * o.ω)
    (χ : Coins frameJ8 K)
    (hV : ∀ e ∈ famCellV δ (DL) (K := K), χ ∉ e.ev)
    (hH : ∀ e ∈ famCellH δ b (DL) hC o (K := K), χ ∉ e.ev) :
    (CellTwinKW.cellChipHQKW δ b hC (powN o (DL).cells.length) o (chalsMJ8 δ χ)
        (pubsCOf δ b (DL) hC o χ)).rap.Satisfies
      (ComplJ8Enc.cellTrME δ b hC (powN o (DL).cells.length) o (chalsMJ8 δ) (pubsCOf δ b (DL) hC o)
        (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf (DL)) (DL).cells (mvF (DL)) (mxF (DL)) (fun _ => 0) (mhF (DL)) χ) ∧
    (CellTwinKW.cellChipHQKW δ b hC (powN o (DL).cells.length) o (chalsMJ8 δ χ)
        (pubsCOf δ b (DL) hC o χ)).BindsPreprocessing
      (ComplJ8Enc.cellTrME δ b hC (powN o (DL).cells.length) o (chalsMJ8 δ) (pubsCOf δ b (DL) hC o)
        (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf (DL)) (DL).cells (mvF (DL)) (mxF (DL)) (fun _ => 0) (mhF (DL)) χ) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  obtain ⟨hz, hrows⟩ := famCellV_good δ (DL) χ hV
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN o _) o (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC o χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC o χ) 4) (pub2 δ (chT δ b _ hC o χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC o χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC o χ)]

end Cell

/-! ## 2. The J chip at `DL`, arbitrary orbit -/

section JChip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **The J chip, absent case at any orbit** (`GenPortJ9AHMemSat.jOK_absent_at` at `DL`). -/
theorem jOK_absent_atL (h0 : (DL).jrows.length = 0) (χ : Coins frameJ8 K)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (PJ : Fin (Nock.Jet.ChipJ8.jetChipJ8 δ b (powN o (DL).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DL) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DL).jrows.get)).rap.w → Polynomial (ZMod p)) :
    JGenJ8.JChipOK δ b (powN o (DL).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DL) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DL).jrows.get) PJ := by
  refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
  have hs : ∀ (g : Fin (DL).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
    intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
    (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
  have e : ∀ i, pubsJOf δ (DL) χ i = 0 := by
    intro i
    unfold pubsJOf
    rw [hs, hs]
    split_ifs <;> simp [pub2, hz.1, hz.2]
  exact ⟨e 0, e 1, e 2, e 3⟩

/-- **`GenPortJ9AHMemSat.jOK_at` at `DL`**: the J chip at any orbit, present or absent.  The binder is the
prim-aware `hRtJ` (`hRt` on the non-primitive called ids only, `ComplJ9ALData.jrows_gateL`). -/
theorem jOK_atL
    (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : 0 < (DL).jrows.length → Function.Injective (powN o (DL).jrows.length))
    (hadj : 0 < (DL).jrows.length → ∀ (i : Fin (DL).jrows.length) (hi : (i : ℕ) + 1 < (DL).jrows.length),
      powN o (DL).jrows.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DL).jrows.length i * o.ω)
    (χ : Coins frameJ8 K)
    (hJ : ∀ e ∈ famJ δ (DL) (K := K), χ ∉ e.ev) :
    JGenJ8.JChipOK δ b (powN o (DL).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DL) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DL).jrows.get)
      (fun j => ComplJ8Jet.trJ δ b (powN o (DL).jrows.length) (chalsJJ8 χ) (DL).jrows.get
        (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width δ b (powN o (DL).jrows.length) o (chalsJJ8 χ)
          (pubsJOf δ (DL) χ) (Nock.Jet.ChipJ8T.HonestRAP.layJ (DL).jrows.get)) j)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (DL).jrows.length = 0
  · exact jOK_absent_atL δ b Rt prims hgen h0 χ o _
  · have hn : 0 < (DL).jrows.length := Nat.pos_of_ne_zero h0
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (DL).jrows.get)
      (ComplJ8Jet.jKeysX (DL).jrows.get) χ hJ
    exact ComplJ8Jet.jOK_present_trJ δ b (powN o _) o (chalsJJ8 χ) (pubsJOf δ _ χ)
      (DL).jrows.get (hinj hn) hn (hadj hn)
      (fun i => ComplJ9ALData.jrows_gateL Rt prims hgen hp hRtJ _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])

end JChip

/-! ## 3. The atom table (both views) at `DL`, arbitrary orbit -/

section AtomL
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables (genHypA genHyp_mbXA acs_okA atomOK_mbA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALTables (genHyp_mbL rows_leL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf p Rg Rt prims hgen

/-- **`GenPortJ9AHMemSat2.atomOK_runAo` at `DL`** (`ComplJ9ALTables.atomOK_L` at an arbitrary orbit `o`; `hinj hadj`
supplied; the bumped `mb` meets `GenHyp` by `genHyp_mbL`, so no hypothesis beyond `hpG`, `Rows31 DL` is added). -/
theorem atomOK_runLo (hpG : p = Nock.Atoms.p) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hA : 0 < (DL).acs.length) (h31 : Rows31 (DL))
    (hinj : Function.Injective (powN o (DL).acs.length))
    (hadj : ∀ (i : Fin (DL).acs.length) (hi : (i : ℕ) + 1 < (DL).acs.length),
      powN o (DL).acs.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DL).acs.length i * o.ω)
    (χ : Coins frameJ8 K)
    (gZ : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) (gV : ∀ e ∈ famAV δ (DL) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAH δ b (DL) hA o (K := K), χ ∉ e.ev)
    (gMB : ∀ e ∈ famMB δ b (DL) hA o (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b (DL) hA o (K := K), χ ∉ e.ev)
    (gMI : ∀ e ∈ famMI δ b (DL) hA o (K := K), χ ∉ e.ev) :
    let P := pubsAOf δ b (DL) hA o χ
    let tr := HonestA8.atomTraceHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (DL) hA o χ P)
      (newBA (DL))
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies tr ∧
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing tr ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) := by
  intro P tr
  subst hpG
  have hz := famAZ_good δ χ gZ
  have hv := famAV_good δ (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) χ gV
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ gH gMB gC gMI P
  have hmA9 : (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs.length ∈ sizesJ8 (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) := by
    simp [sizesJ8]
  have hN := rows_leL Rt prims hgen h31
  obtain ⟨hcell, hrank, htl⟩ := acs_okA Rg Rt hgen hN (h31 _ hmA9)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN o _) o (chalsAJ8Z δ χ) P (γV δ χ) (ρV δ χ)
    (zA δ χ) (fun _ => none) (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _)
    hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs.length,
      let y := (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs[(i : ℕ)]
      colAH δ b _ hA o χ P Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).acs
            (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ P i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  exact atomOK_mbA δ b Rg Rt hgen hA (powN o _) o (chalsAJ8Z δ χ) P
    (colAH δ b (j9alDataOf Nock.Atoms.p Rg Rt prims hgen) hA o χ P)
    (j9alDataOf Nock.Atoms.p Rg Rt prims hgen).mb (genHyp_mbL Rg Rt prims hgen hN) hinj hadj hcol hsat0
    hpMB hpC hpMI tMB tC tMI

end AtomL

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMemSat
