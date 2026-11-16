/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ARun.lean

* Sizes: `N9 t` (the twin compute rows, `bfsForest [genX9T t]`), `nXOf` (axis rows: the chain table of
    `axChains9`, or one dummy row when absent), `nSOf` (split rows: one per field axis atom, or one dummy row);
    `sizesA D = sizesJ8 D ++ [N9, nX, nS]`, the height `htA D` over all of them, `Rows31A D`, `DvdA D` (from
    `hpG` and `Rows31A`), the orbit `orbA`.
  * Orbits: the J-8 memory tables (cell, walk, J, atom, atom walk) keep `orbJ8 DA`; the twin compute chip, the axis chip and the split chip share `orbA DA` (height `htA DA ≥ htJ8 DA`).
  * `BRun9A δ b Rt hgen hpG h31A : HonestJ9A`: compute = `polyX9` on `bfsForest [genX9T t]` with
    `idOf9 nA H fieldAx9`, message `m ρ ρS` = `mCOf`, the `accV9` totals; the memory tables from `B8A =
    honestJ8Of DA … (AVA …) famsJA` by projection; axis = `polyAx` of the chain table (`pubsXOf`), present iff
    `axKeys9 ≠ []`; split = `polySC` at `vSA` (the field axis atoms, ids `nA + i`) and `mSA` (consumer counts);
    rows / `g` canonical; `bad` = the two walk-coin orders (`N8`, `N9`) and the families `famsJA ++ famsNew`
    (`famAX`, `famSP`, the twin slot poles `compPoles9`).
  * Good-coin transfers: `good_B8`, `good_fam`, `good_ord8`, `good_ord9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AObl
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABase
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChipsOK
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompPole
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReadsAt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 axChains9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A RowsLe31A)

noncomputable section

/-! ## 1. Sizes, the common height of the new chips, the binders -/

section Sizes
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The twin compute rows of a J-8 tree. -/
abbrev W9 (t : NTree SkelX) : List (NTree LX9) := bfsForest [genX9T t]

/-- The twin compute row count (sealed: comparisons with the J-8 sizes fail fast). -/
irreducible_def N9 (t : NTree SkelX) : ℕ := (W9 t).length

/-- The axis chip is present iff some row reads a big (`≥ 2^62`) axis. -/
def axOnA (t : NTree SkelX) : Bool := !(axKeys9 (rowsOfT9 t)).isEmpty

/-- The split chip is present iff some row reads a field (`2^62 ≤ · < p`) axis. -/
def spOnA (p : ℕ) (t : NTree SkelX) : Bool := !(fieldAx9 p (rowsOfT9 t)).isEmpty

/-- The honest axis chains (`nA` the atom table's row count, `H` the handle map). -/
abbrev csA (p : ℕ) [Fact p.Prime] (nA : ℕ) (H : Noun → ℕ × ℕ) (t : NTree SkelX) :
    List (ComplJ9AAxisRows.ChainSpec (ZMod p)) :=
  axChains9 p nA H (rowsOfT9 t)

/-- The axis rows: the chain table, or one dummy row when absent. -/
def nXOf (p : ℕ) [Fact p.Prime] (nA : ℕ) (H : Noun → ℕ × ℕ) (t : NTree SkelX) : ℕ :=
  if axOnA t = true then (ComplJ9AAxisRows.tableRows (csA p nA H t)).length else 1

/-- The split rows: one per field axis atom, or one dummy row when absent. -/
def nSOf (p : ℕ) (t : NTree SkelX) : ℕ :=
  if spOnA p t = true then (splitVals9 p (rowsOfT9 t)).length else 1

theorem nXOf_eq {p : ℕ} [Fact p.Prime] {nA : ℕ} {H : Noun → ℕ × ℕ} {t : NTree SkelX} (h : axOnA t = true) :
    nXOf p nA H t = (ComplJ9AAxisRows.tableRows (csA p nA H t)).length := by
  simp only [nXOf, h, ite_true]

theorem nSOf_eq {p : ℕ} {t : NTree SkelX} (h : spOnA p t = true) :
    nSOf p t = (splitVals9 p (rowsOfT9 t)).length := by
  simp only [nSOf, h, ite_true]

theorem nSOf_pos (p : ℕ) (t : NTree SkelX) : 0 < nSOf p t := by
  unfold nSOf
  split_ifs with h
  · simp only [spOnA, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    exact List.length_pos_iff.mpr h
  · exact Nat.one_pos

theorem nXOf_pos {p : ℕ} [Fact p.Prime] (nA : ℕ) (H : Noun → ℕ × ℕ) {R : Nock.Jet.Registry} {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX R fuel s f = some (t, r)) : 0 < nXOf p nA H t := by
  unfold nXOf
  split_ifs with h
  · simp only [axOnA, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ h
    rw [ComplJ9AChainsRun.axChains9_table_length]
    have hbig := (ComplJ9AChainsRun.axKeys9_read hgen hk).1
    have h0 : k.2 ≠ 0 := by
      have : (0 : ℕ) < 2 ^ 62 := by positivity
      omega
    have hne : Nock.Atoms.limbs k.2 ≠ [] := by
      unfold Nock.Atoms.limbs
      exact Nat.digits_ne_nil_iff_ne_zero.mpr h0
    have hpos : 0 < (Nock.Atoms.limbs k.2).length := List.length_pos_iff.mpr hne
    have hle : (Nock.Atoms.limbs k.2).length ≤
        ((axKeys9 (rowsOfT9 t)).map fun k => (Nock.Atoms.limbs k.2).length).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨k, hk, rfl⟩)
    omega
  · exact Nat.one_pos

/-- **The J-9 A sizes**: the six J-8 tables of `D`, the twin compute rows, the axis rows, the split rows. -/
def sizesA (D : J8Data p Rg fuel s f r) : List ℕ :=
  sizesJ8 D ++ [N9 D.t, nXOf p D.acs.length D.H D.t, nSOf p D.t]

/-- **The J-9 A row binder**: every table, old and new, has `≤ 2^31` rows. -/
def Rows31A (D : J8Data p Rg fuel s f r) : Prop := ∀ x ∈ sizesA D, x ≤ 2 ^ 31

/-- The height of the new chips' common orbit: the least `h ≥ 1` with every table (old and new) `≤ 2^h`. -/
irreducible_def htA (D : J8Data p Rg fuel s f r) : ℕ := max 1 (Nat.clog 2 ((sizesA D).foldr max 0))

theorem le_foldr_max : ∀ (L : List ℕ), ∀ x ∈ L, x ≤ L.foldr max 0
  | [], x, hx => absurd hx List.not_mem_nil
  | a :: L, x, hx => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max L x h) (le_max_right _ _)

theorem foldr_max_le : ∀ (L : List ℕ) (m : ℕ), (∀ x ∈ L, x ≤ m) → L.foldr max 0 ≤ m
  | [], _, _ => Nat.zero_le _
  | a :: L, m, h => by
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (foldr_max_le L m fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem le_two_pow_htA (D : J8Data p Rg fuel s f r) {x : ℕ} (hx : x ∈ sizesA D) : x ≤ 2 ^ htA D :=
  calc x ≤ (sizesA D).foldr max 0 := le_foldr_max _ x hx
    _ ≤ 2 ^ Nat.clog 2 ((sizesA D).foldr max 0) := Nat.le_pow_clog (by norm_num) _
    _ ≤ 2 ^ htA D := Nat.pow_le_pow_right (by norm_num) (by rw [htA_def]; exact le_max_right _ _)

theorem one_le_htA (D : J8Data p Rg fuel s f r) : 1 ≤ htA D := by rw [htA_def]; exact le_max_left _ _

theorem sizesJ8_sub (D : J8Data p Rg fuel s f r) : ∀ x ∈ sizesJ8 D, x ∈ sizesA D :=
  fun x hx => List.mem_append_left _ hx

theorem rows31_of_A {D : J8Data p Rg fuel s f r} (h : Rows31A D) : Rows31 D :=
  fun x hx => h x (sizesJ8_sub D x hx)

theorem htJ8_le_htA (D : J8Data p Rg fuel s f r) : htJ8 D ≤ htA D := by
  rw [htA_def]
  unfold htJ8 szJ8
  refine max_le_max le_rfl (Nat.clog_mono_right _ ?_)
  exact foldr_max_le _ _ fun x hx => le_foldr_max _ x (sizesJ8_sub D x hx)

theorem htA_le (D : J8Data p Rg fuel s f r) (h : Rows31A D) : htA D ≤ 31 := by
  rw [htA_def]
  exact max_le (by norm_num) (Nat.clog_le_of_le_pow (foldr_max_le _ _ h))

/-- The divisibility side condition of the new chips' orbit. -/
def DvdA (D : J8Data p Rg fuel s f r) : Prop := 3 * 2 ^ htA D ∣ p - 1

theorem dvdA_of_rows (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (h : Rows31A D) : DvdA D := by
  unfold DvdA
  have hg := goldilocks_dvd
  rw [← hpG] at hg
  exact (mul_dvd_mul_left 3 (pow_dvd_pow 2 ((htA_le D h).trans (by norm_num)))).trans hg

theorem dvdOK_of_A {D : J8Data p Rg fuel s f r} (h : DvdA D) : DvdOK D :=
  (mul_dvd_mul_left 3 (pow_dvd_pow 2 (htJ8_le_htA D))).trans h

/-- The new chips' common orbit. -/
def orbA (D : J8Data p Rg fuel s f r) (hF : DvdA D) : StrictOrbitDomain (ZMod p) 3 (htA D) :=
  orbitOf (htA D) (one_le_htA D) (by rw [ZMod.card]; exact hF)

end Sizes

/-! ## 2. The honest record -/

section Rec
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (accV9 polyX9 env0)
open Nock.NockVMROM.Thm54.VclL.HonestSatX9 (accW9)
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (lnClosed cntClosed)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DA" => j9aDataOf p Rg Rt hgen

/-! ### The binders' consequences -/

variable (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

include hpG h31A in
theorem dvdA_run : DvdA (DA) := dvdA_of_rows hpG _ h31A
include hpG h31A in
theorem hF_run : DvdOK (DA) := dvdOK_of_A (dvdA_run Rt hgen hpG h31A)
include h31A in
theorem h31_run : Rows31 (DA) := rows31_of_A h31A

/-- The new chips' orbit of the run. -/
abbrev oA : StrictOrbitDomain (ZMod p) 3 (htA (DA)) := orbA (DA) (dvdA_run Rt hgen hpG h31A)

/-- The atom table's row count (the split chip's id offset). -/
abbrev nAA : ℕ := (DA).acs.length

/-- The twin compute rows' `TAG_ax` id map. -/
abbrev idOfA : ℕ → ℕ := idOf9 p (DA).acs.length (DA).H (fieldAx9 p (rowsOfT9 t))

/-- The axis rows of the run. -/
abbrev nXA : ℕ := nXOf p (DA).acs.length (DA).H t

/-- The split rows of the run. -/
abbrev nSA : ℕ := nSOf p t

theorem nXA_pos : 0 < nXA (p := p) Rt hgen := nXOf_pos _ _ hgen



/-- **The J-8 families at `DA`** (J-9 B's `famsAll9` pattern, at the J-9 A data, with the J-9 A atom walk). -/
abbrev famsJA : List (List (BadSpec K)) :=
  famsOf δ b (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen) ++
    ComplJ9BOf.famsA9 δ b (DA) (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen)


abbrev B8A : HonestJ8 p K δ Rg fuel s f r :=
  honestJ8Of δ b (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen)
    (ComplJ9ADataRec.acsA_pos Rt hgen)
    (ComplJ9ATables.AVA δ b Rt hgen (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.acsA_pos Rt hgen))
    (famsJA δ b Rt hgen hpG h31A)

/-! ### The public layout -/

/-- **The J-9 A public layout of the run.** -/
def PbA : PubJ9A p :=
  { toPubJ8 :=
      { PbOf (DA) (hF_run Rt hgen hpG h31A) (ComplJ9ADataRec.cellsA_pos Rt hgen) (ComplJ9ADataRec.acsA_pos Rt hgen) with
        h := htA (DA), n := N9 t, hn := by rw [N9_def]; exact bfs_pos' (genX9T t),
        nodes := powN (oA Rt hgen hpG h31A) (N9 t), orbit := oA Rt hgen hpG h31A }
    hX := htA (DA), nX := nXA (p := p) Rt hgen, hnX := nXA_pos (p := p) Rt hgen,
    nodesX := powN (oA Rt hgen hpG h31A) _, orbitX := oA Rt hgen hpG h31A,
    hS := htA (DA), nS := nSOf p t, hnS := nSOf_pos p t,
    nodesS := powN (oA Rt hgen hpG h31A) _, orbitS := oA Rt hgen hpG h31A,
    axOn := axOnA t, spOn := spOnA p t }
where
  bfs_pos' (u : NTree LX9) : 0 < (bfsForest [u]).length :=
    List.length_pos_of_mem ((mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, InTree.here _⟩)

/-! ### The compute message and trace -/

/-- The walk / LogUp coins of the compute chip. -/
abbrev αA (χ : Coins frameJ8 K) : K := InhabJ8Comp.αC0 b χ
abbrev γA (χ : Coins frameJ8 K) : K := InhabJ8Comp.γC0 b χ

/-- The six accumulator totals of the twin (read at the zero public vector; `accV9` reads no public). -/
def accTA (χ : Coins frameJ8 K) (a : ℕ) : K :=
  accV9 b δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (chalVJ8 b χ) (fun _ => 0) a (N9 t)

/-- The compute message's `ρ` (accumulators `0..3`). -/
def ρA (χ : Coins frameJ8 K) : Fin 5 → 𝕂′ := fun i =>
  if (i : ℕ) = 3 then Quad.mk _ (accTA δ b Rt hgen χ 0) (accTA δ b Rt hgen χ 1)
  else if (i : ℕ) = 4 then Quad.mk _ (accTA δ b Rt hgen χ 2) (accTA δ b Rt hgen χ 3) else 0

/-- The compute message's `ρS` (accumulators `4, 5`). -/
def ρSA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (accTA δ b Rt hgen χ 4) (accTA δ b Rt hgen χ 5)

/-- The compute message's claim handles. -/
abbrev mA : FrameVS.ClaimMsgVS := ComplJ8Comp.mCOf (DA).H (cJ s f r)

/-- **The twin compute publics** (`pubVJ9` at the honest message). -/
def pubCA (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  ClaimJ9.pubVJ9 δ b (cJ s f r) (mA (p := p) Rt hgen) (ρA δ b Rt hgen χ) (ρSA δ b Rt hgen χ) χ

/-- **The honest walk node value** (`ComplJ9AReadsAt.nodeV9` at the coin's `γ`). -/
abbrev nodeVA (χ : Coins frameJ8 K) : NTree LX9 → K :=
  ComplJ9AReadsAt.nodeV9 (F := ZMod p) (DA).H (DA).pd (idOfA (p := p) Rt hgen) (γA b χ)


/-- **The honest twin compute trace, sealed** (`polyX9` at the closed-form walk columns, width `137`). -/
irreducible_def trCA (χ : Coins frameJ8 K) {n : ℕ}
    (nodes : Fin n → ZMod p) : Fin 137 → (ZMod p)[X] :=
  polyX9 b δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (chalVJ8 b χ) (pubCA δ b Rt hgen χ)
    (lnClosed (αA b χ)) (cntClosed (Walk.foCol (W9 t)) (αA b χ) (αA b χ))
    (accW9 (nodeVA b Rt hgen χ) (W9 t) (αA b χ)) nodes 137

/-! ### The axis chip -/

theorem nXA_eq (h : axOnA t = true) :
    nXA (p := p) Rt hgen = (ComplJ9AAxisRows.tableRows (csA p (DA).acs.length (DA).H t)).length := nXOf_eq h

/-- The axis publics (`pubsXOf` when present, `0` when absent). -/
def pubsXA (χ : Coins frameJ8 K) : ℕ → K :=
  if h : axOnA t = true then
    ComplJ9AChipsOK.pubsXOf δ (nXA_pos (p := p) Rt hgen) (csA p (DA).acs.length (DA).H t) (nXA_eq (p := p) Rt hgen h) χ
  else fun _ => 0

/-- The axis trace (`polyAx` of the chain table when present, `0` when absent). -/
def trXA (χ : Coins frameJ8 K) : Fin 52 → (ZMod p)[X] :=
  if h : axOnA t = true then fun j =>
    ComplJ9AAxisH.polyAx δ b (nXA_pos (p := p) Rt hgen) (powN (oA Rt hgen hpG h31A) (nXA (p := p) Rt hgen)) (oA Rt hgen hpG h31A)
      (chalsMJ8 δ χ) (pubsXA δ Rt hgen χ)
      (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows (csA p (DA).acs.length (DA).H t))
        (nXA_pos (p := p) Rt hgen) (nXA_eq (p := p) Rt hgen h)) j
  else fun _ => 0

/-! ### The split chip -/

/-- The split values: the field axis atoms (`0` on the dummy row). -/
def vSA (i : Fin (nSOf p t)) : ℕ := (splitVals9 p (rowsOfT9 t)).getD i 0

/-- **The split multiplicities**: the number of axis chains (one per
distinct `(root, axis)` key) whose axis is the row's field axis atom — each such chain consumes both limb records
`(nA + i, 2, 0, lo)` and `(nA + i, 3, 0, hi)` once. -/
def mSA (i : Fin (nSOf p t)) : ℕ :=
  ((axKeys9 (rowsOfT9 t)).filter (·.2 = vSA (p := p) i)).length +
    ((rowsOfT9 t).toList.filter fun l => l.chip = .s10B ∧ l.n = vSA (p := p) i).length

/-- The split publics (`pubsSOf` when present, `0` when absent). -/
def pubsSA (χ : Coins frameJ8 K) : ℕ → K :=
  if spOnA p t = true then
    ComplJ9AChipsOK.pubsSOf δ (nAA (p := p) Rt hgen) (vSA (p := p) (t := t)) (mSA (p := p) (t := t)) χ
  else fun _ => 0

/-- The split trace (`polySC` when present, `0` when absent). -/
def trSA (χ : Coins frameJ8 K) : Fin 90 → (ZMod p)[X] :=
  if spOnA p t = true then fun j =>
    ComplJ9ASplitH.polySC δ (nAA (p := p) Rt hgen) b (nSOf_pos p t) (powN (oA Rt hgen hpG h31A) (nSOf p t))
      (oA Rt hgen hpG h31A) (chalsMJ8 δ χ) (pubsSA δ Rt hgen χ) (vSA (p := p) (t := t)) (mSA (p := p) (t := t)) j
  else fun _ => 0

/-! ### The message, the traces, the rows -/

/-- **The honest J-9 A message at a coin.** -/
def MA (χ : Coins frameJ8 K) : MsgJ9A' p K δ :=
  { toMsgJ8' := { ((B8A δ b Rt hgen hpG h31A).M χ) with ρ := ρA δ b Rt hgen χ, ρS := ρSA δ b Rt hgen χ }
    pubsX := pubsXA δ Rt hgen χ
    pubsS := pubsSA δ Rt hgen χ }

/-- **The honest J-9 A traces at a coin.** -/
def trA9 (χ : Coins frameJ8 K) : TrJ9A (ZMod p) :=
  { C := trCA δ b Rt hgen χ (PbA Rt hgen hpG h31A).nodes
    M := ((B8A δ b Rt hgen hpG h31A).tr χ).M
    W := ((B8A δ b Rt hgen hpG h31A).tr χ).W
    J := ((B8A δ b Rt hgen hpG h31A).tr χ).J
    A := ((B8A δ b Rt hgen hpG h31A).tr χ).A
    V := ((B8A δ b Rt hgen hpG h31A).tr χ).V
    X := trXA δ b Rt hgen hpG h31A χ
    S := trSA δ b Rt hgen hpG h31A χ }

/-- **The canonical J-9 A rows**: J-8's canonical rows with the axis rows charged to `N` (`BudJ9A.p1`), `AX = nX`,
`SP = nS`. -/
def rowsA9 (Pb : PubJ9A p) : RowsJ9A :=
  { toRowsJ8 := { ComplJ8Comp.canonRows Pb.toPubJ8 extraRows with N := Pb.n + Pb.nX }, AX := Pb.nX, SP := Pb.nS }

/-! ### The bad events -/

section Poles
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompPole (slotPoles)

/-- **The twin compute chip's slot pole events**: for every row `j < n` and every twin slot, the slot's pole events
at the coin-free row environment (J-8's `compPoles` over `slotsX9`). -/
def compPoles9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (n : ℕ) : List (BadSpec K) :=
  (List.range n).flatMap fun j => (ChipHX9.slotsX9 (F := ZMod p)).flatMap fun S =>
    slotPoles δ S (env0 H pd idOf W (fun _ => (0 : ZMod p)) (fun _ => 0) j)

end Poles

/-- The axis completeness events (`famAX` when present). -/
def famAXA : List (BadSpec K) :=
  if h : axOnA t = true then
    ComplJ9AChipsOK.famAX δ (nXA_pos (p := p) Rt hgen) (csA p (DA).acs.length (DA).H t) (nXA_eq (p := p) Rt hgen h)
  else []

/-- The split completeness events (`famSP`, always: `2 nS` pins). -/
def famSPA : List (BadSpec K) := ComplJ9AChipsOK.famSP δ (nAA (p := p) Rt hgen) (vSA (p := p) (t := t))

/-- **The new families**: the axis events, the split events, the twin slot poles. -/
def famsNew : List (List (BadSpec K)) :=
  [famAXA δ Rt hgen, famSPA δ Rt hgen,
    compPoles9 δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (N9 t)]

/-- The J-8 compute rows. -/
abbrev N8 : ℕ := (bfsForest [(DA).t]).length

/-- **The bad list of the run**: the walk-coin order at `N8` and at `N9` (the twin walk),
then the families. -/
def badSA : List (BadSpec K) :=
  badList [(⟨13, by decide⟩, N8 (p := p) Rt hgen), (⟨13, by decide⟩, N9 t)]
    (famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen)

/-- **The J-9 A honest record of the run** (walk node value `nodeV9`). -/
def BRun9A : HonestJ9A p K δ Rg fuel s f r where
  t := t
  hgen := hgen
  Pb := PbA Rt hgen hpG h31A
  M := MA δ b Rt hgen hpG h31A
  tr := trA9 δ b Rt hgen hpG h31A
  rows := rowsA9 (PbA Rt hgen hpG h31A)
  g := ComplJ8Comp.canonG (PbA Rt hgen hpG h31A).toPubJ8
  bad := badOf (badSA δ b Rt hgen hpG h31A)

/-! ### Good coins -/


theorem good_spec' {χ : Coins frameJ8 K} (h : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ∀ e ∈ badSA δ b Rt hgen hpG h31A, χ ∉ e.ev :=
  fun e he => h _ (List.mem_map.mpr ⟨e, he, rfl⟩)


theorem good_B8 {χ : Coins frameJ8 K} (h : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    (B8A δ b Rt hgen hpG h31A).Good χ := by
  have hg := good_spec' δ b Rt hgen hpG h31A h
  intro e he
  obtain ⟨sp, hs, rfl⟩ := List.mem_map.mp he
  refine hg sp ?_
  simp only [badSA, badList, List.mem_append, List.mem_map, List.mem_flatten, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with ⟨o, ho, rfl⟩ | ⟨L, hL, hsL⟩
  · exact Or.inl ⟨o, Or.inl ho, rfl⟩
  · exact Or.inr ⟨L, Or.inl hL, hsL⟩

/-- **Outside every family event.** -/
theorem good_fam {χ : Coins frameJ8 K} (h : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ∀ L ∈ famsJA δ b Rt hgen hpG h31A ++ famsNew δ Rt hgen, ∀ e ∈ L, χ ∉ e.ev :=
  fun L hL e he => good_spec' δ b Rt hgen hpG h31A h e
    (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))

/-- **The twin walk-coin order.** -/
theorem good_ord9 {χ : Coins frameJ8 K} (h : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    N9 t ≤ orderOf (χ ⟨13, by decide⟩) := by
  have := good_spec' δ b Rt hgen hpG h31A h (BadSpec.ord ⟨13, by decide⟩ (N9 t))
    (List.mem_append_left _ (by simp))
  simpa [BadSpec.ev] using this

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
#print axioms nXOf_pos
#print axioms nSOf_pos
#print axioms htJ8_le_htA
#print axioms dvdA_of_rows
#print axioms BRun9A
#print axioms good_B8
#print axioms good_fam
#print axioms good_ord9
end Axioms
