/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALRun.lean

  **J-9 AL completeness: the mixed honest record of a run.**

  * §2 coin-free table facts: `tbR_fst` (the base rows of the honest ALU table do not read the limb coin `y`),
    `aluLen`, `tbR_length`, `rowAt_tbR_fst`, `preL_indep` (the honest preprocessing is coin-free).
  * §3 the J-row monotonicity: `jrows_len_le` (the J rows of the overlay are at most the J-9 A J rows) and
    **`rows31L_of_A : Rows31A DA → Rows31A DL`**.  So the size binder of the ALU is only `Rows31AL := aluLen ≤ 2^31`.
  * §4 the record: the ALU orbit (`htL`, `orbL`, `nLRun := aluLen + 1`), `PbAL` / `PbL` (§0's mixed public layout),
    `pubsLOf`, `MAL`, `trAL`, `rowsAL`, `gL`, `badAL`, and the read-back `rfl` lemmas.
  * §5 good-coin transfers `goodAL_BA`, `goodAL_B8L`, `goodAL_famAL`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfBad
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatBlock
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg (preLOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AluPoles (yOf famAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 0. The J generator's row count (generic) -/

section JLen
open Nock.Jet.ChipJ8
open Nock.Jet.Interp (JNode nodesOf)
variable {p : ℕ} [Fact p.Prime]

theorem chainWG_length (hd : Noun → ZMod p × ZMod p) (c dst : ℕ) :
    ∀ (src ctr : ℕ) (bs : List Bool) (x : Noun), (chainWG hd c dst src ctr bs x).length = bs.length + 1
  | _, _, [], _ => rfl
  | src, ctr, b :: bs, x => by
    simp only [chainWG, List.length_cons, chainWG_length hd c dst _ _ bs]

/-- The row count of one template node (handle-, call-, counter- and subject-free). -/
def nodeLen (nd : JNode) : ℕ :=
  (nodeWG (p := p) (fun _ => (0, 0)) 0 0 0 (fun _ => .atom 0) (.atom 0) nd).length

theorem nodeWG_length (hd : Noun → ZMod p × ZMod p) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) :
    (nodeWG hd c S ctr lk s nd).length = nodeLen (p := p) nd := by
  unfold nodeLen
  cases h : nd.op <;> simp only [nodeWG, h, chainWG_length, List.length_cons, List.length_nil]

theorem nodesWG_length (hd : Noun → ZMod p × ZMod p) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ∀ (ctr : ℕ) (nds : List JNode), (nodesWG hd c S lk s ctr nds).length = (nds.map (nodeLen (p := p))).sum
  | _, [] => rfl
  | ctr, nd :: nds => by
    simp only [nodesWG, List.length_append, nodeWG_length, nodesWG_length hd c S lk s _ nds, List.map_cons,
      List.sum_cons]

/-- The row count of one call block: it reads only the template. -/
def blkLen (T : Nock.Jet.Autogen.Tpl) : ℕ := ((nodesOf T).map (nodeLen (p := p))).sum + 1

theorem blockWG_length (hd : Noun → ZMod p × ZMod p) (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) (s : Noun) :
    (blockWG hd R c i s).length = blkLen (p := p) (R i) := by
  simp only [blockWG, List.length_cons, nodesWG_length, blkLen]

theorem honestJ8G_length (hd : Noun → ZMod p × ZMod p) (R : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ)
    (calls : List (ℕ × Noun)) :
    (honestJ8G hd R regs calls).length = regs.length + (calls.map fun x => blkLen (p := p) (R x.1)).sum := by
  simp only [honestJ8G, List.length_append, List.length_map, List.length_flatMap]
  congr 1
  have : ∀ e ∈ calls.zipIdx, (match e with | ((i, s), c) => blockWG hd R c i s).length =
      (fun x : ℕ × Noun => blkLen (p := p) (R x.1)) e.1 := by
    rintro ⟨⟨i, s⟩, c⟩ -
    exact blockWG_length hd R c i s
  rw [List.map_congr_left this]
  rw [show (fun a : (ℕ × Noun) × ℕ => (fun x : ℕ × Noun => blkLen (p := p) (R x.1)) a.1) =
      (fun x : ℕ × Noun => blkLen (p := p) (R x.1)) ∘ Prod.fst from rfl, ← List.map_map]
  congr 2
  exact List.zipIdx_map_fst 0 calls

end JLen

/-! ## 1. The IFACE block -/

section Iface
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.NockVMROM.Thm54.VclL.GenWalk

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
include hpG h31 in
theorem hFL : DvdOK (DL) := ComplJ9ARun.dvdOK_of_A (ComplJ9ARun.dvdA_of_rows hpG _ h31)
abbrev psRun : List (ℕ × PrimOp) := ComplJ9ALData.primsC prims ((DA).calls.map Prod.fst)
abbrev vcRun : ℕ → ℕ := ComplJ9ALData.idxPOf (DA).cells prims
abbrev mRun : ℕ → ℕ := fun id =>
  ((ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t)).countP fun x => x.1 = id) + 1   -- mP = c+1
abbrev tbR (y : Quad (algebraMap (ZMod p) K δ)) :=
  AluSatRun.tblRun δ Rt prims hgen (psRun (p := p) Rt hgen prims) (vcRun (p := p) Rt hgen prims) (mRun (t := t) prims) y
abbrev famsJL := famsOf δ b (DL) (hFL Rt hgen prims hpG h31) (cellsL_pos Rt prims hgen) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) (hFL Rt hgen prims hpG h31) (acsL_pos Rt prims hgen)
abbrev AVL := ComplJ9BBalF.avOf9 δ b (DL) (hFL Rt hgen prims hpG h31)
  (avOf δ b (DL) (hFL Rt hgen prims hpG h31) (acsL_pos Rt prims hgen))
abbrev B8L := honestJ8Of δ b (DL) (hFL Rt hgen prims hpG h31) (cellsL_pos Rt prims hgen) (acsL_pos Rt prims hgen)
  (AVL δ b Rt hgen prims hpG h31) (famsJL δ b Rt hgen prims hpG h31)
-- ALU terminals, n abstract (padding rows contribute 0):
--   SV n χ := ∑ i : Fin n, AluSatRows.tV δ (chalsALJ8 δ χ) (tbR (yOf δ χ)) i     (likewise SS with tS, SX with tX)

/-- The ALU validity terminal over `n` rows. -/
abbrev SV (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tV δ (chalsALJ8 δ χ) (tbR δ Rt hgen prims (yOf δ χ)) i
/-- The ALU service terminal over `n` rows. -/
abbrev SS (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tS δ (chalsALJ8 δ χ) (tbR δ Rt hgen prims (yOf δ χ)) i
/-- The ALU export terminal over `n` rows. -/
abbrev SX (n : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  ∑ i : Fin n, AluSatRows.tX δ (chalsALJ8 δ χ) (tbR δ Rt hgen prims (yOf δ χ)) i

/-! ## 2. Coin-free table facts -/

theorem zipB_fst (pN : ℕ) (y : Quad (algebraMap (ZMod p) K δ)) (cl : CallL) :
    (zipB δ pN y cl).map Prod.fst = (blockB (F := ZMod p) pN cl) := by
  unfold zipB
  exact List.map_fst_zip (by rw [blockQ_length (F := ZMod p)])

/-- **The base rows of the honest ALU table do not read the limb coin.** -/
theorem tbR_fst (y y' : Quad (algebraMap (ZMod p) K δ)) :
    (tbR δ Rt hgen prims y).map Prod.fst = (tbR δ Rt hgen prims y').map Prod.fst := by
  simp only [tbR, AluSatRun.tblRun, tblP, List.map_append, List.map_map, List.map_flatMap, zipB_fst]

/-- The ALU table length (coin-free). -/
abbrev aluLen : ℕ := (tbR δ Rt hgen prims (0 : Quad (algebraMap (ZMod p) K δ))).length

theorem tbR_length (y : Quad (algebraMap (ZMod p) K δ)) : (tbR δ Rt hgen prims y).length = aluLen (K := K) δ Rt hgen prims := by
  have := congrArg List.length (tbR_fst δ Rt hgen prims y (0 : Quad (algebraMap (ZMod p) K δ)))
  simpa only [List.length_map] using this

theorem getD_fst {α β : Type} (l : List (α × β)) (d : α × β) (i : ℕ) : (l.getD i d).1 = (l.map Prod.fst).getD i d.1 := by
  rw [List.getD_map]

theorem rowAt_tbR_fst (y : Quad (algebraMap (ZMod p) K δ)) (i : ℕ) :
    (rowAt δ (tbR δ Rt hgen prims y) i).1 = (rowAt δ (tbR δ Rt hgen prims (0 : Quad (algebraMap (ZMod p) K δ))) i).1 := by
  unfold rowAt
  rw [getD_fst, getD_fst, tbR_fst δ Rt hgen prims y (0 : Quad (algebraMap (ZMod p) K δ))]

/-- **The honest preprocessing is coin-free.** -/
theorem preL_indep {n : ℕ} (nodes : Fin n → ZMod p) (y : Quad (algebraMap (ZMod p) K δ)) :
    preLOf δ nodes (tbR δ Rt hgen prims y) = preLOf δ nodes (tbR δ Rt hgen prims (0 : Quad (algebraMap (ZMod p) K δ))) := by
  funext k
  unfold preLOf
  simp only [rowAt_tbR_fst]

/-! ## 3. The J rows of the overlay: `Rows31A DL` from `Rows31A DA` -/

theorem mvFixP_length (rows : List (Nock.Jet.ChipJ8.CRow (ZMod p))) (pins : List (List (ZMod p))) :
    (ComplJ8Data.mvFixP p rows pins).length = rows.length := by
  simp [ComplJ8Data.mvFixP]

theorem jrowsA_eq : (DA).jrows = ComplJ8Data.mvFixP p (Nock.Jet.ChipJ8.honestJ8G (ComplJ8Data.hJd p (DA).cells (DA).acs)
    Rt (DA).regs (DA).calls) (ComplJ8Data.pinsOfP p (DA).regs (DA).idx) := rfl

theorem regsA_eq : (DA).regs = ((DA).calls.map Prod.fst).dedup := rfl

/-- **J-row monotonicity**: the overlay's J rows (J calls only) are at most the J-9 A J rows (all calls). -/
theorem jrows_len_le : (DL).jrows.length ≤ (DA).jrows.length := by
  rw [F_jrows, jrowsA_eq, mvFixP_length, mvFixP_length, honestJ8G_length, honestJ8G_length]
  have hc : (DL).calls = jCallsP (prims.map Prod.fst) (DA).calls := rfl
  refine Nat.add_le_add ?_ ?_
  · rw [F_regs, regsA_eq, hc]
    refine (List.nodup_dedup _).length_le_of_subset fun x hx => ?_
    rw [List.mem_dedup] at hx ⊢
    exact ((List.filter_sublist.map Prod.fst).subset) hx
  · rw [hc, F_Rt]
    exact (List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- **`Rows31A DL` follows from `Rows31A DA`** (no `Rows31A DL` binder is needed). -/
theorem rows31L_of_A (h31A : Rows31A (DA)) : Rows31A (DL) := by
  have hj := jrows_len_le (p := p) Rt hgen prims
  have hj31 : (DA).jrows.length ≤ 2 ^ 31 := h31A _ (by simp [sizesA, sizesJ8])
  intro x hx
  have e : sizesA (DL) = [(bfsForest [(DA).t]).length, (DA).cells.length, (walkRows (DA).cells (DA).reads).length,
      (DL).jrows.length, (DA).acs.length, nVOf (DA), N9 t, nXOf p (DA).acs.length (DA).H t, nSOf p t] := rfl
  rw [e] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h31A _ (by simp [sizesA, sizesJ8])
  · exact h31A _ (by simp [sizesA, sizesJ8])
  · exact h31A _ (by simp [sizesA, sizesJ8])
  · omega
  · exact h31A _ (by simp [sizesA, sizesJ8])
  · exact h31A _ (by simp [sizesA, sizesJ8])
  · exact h31A _ (List.mem_append_right _ List.mem_cons_self)
  · exact h31A _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact h31A _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- **The ALU size binder `h31L`** (the shrunk form: `Rows31A DL` is `rows31L_of_A`). -/
def Rows31AL : Prop := aluLen (K := K) δ Rt hgen prims ≤ 2 ^ 31

/-! ## 4. The record -/

/-- The ALU rows: the table plus one spare row (`hnL`). -/
abbrev nLRun : ℕ := aluLen (K := K) δ Rt hgen prims + 1

/-- The ALU orbit height: `clog₂ nL`, at least `1`, capped at `32` (Goldilocks' two-adicity). -/
def htL : ℕ := min 32 (max 1 (Nat.clog 2 (nLRun (K := K) δ Rt hgen prims)))

theorem one_le_htL : 1 ≤ htL (K := K) δ Rt hgen prims := by
  unfold htL; exact le_min (by norm_num) (le_max_left _ _)

theorem htL_le : htL (K := K) δ Rt hgen prims ≤ 32 := by unfold htL; exact min_le_left _ _

include hpG in
theorem dvdL : 3 * 2 ^ htL (K := K) δ Rt hgen prims ∣ Fintype.card (ZMod p) - 1 := by
  rw [ZMod.card]
  have hg := goldilocks_dvd
  rw [← hpG] at hg
  exact (mul_dvd_mul_left 3 (pow_dvd_pow 2 (htL_le (K := K) δ Rt hgen prims))).trans hg

/-- The ALU orbit. -/
def orbL : StrictOrbitDomain (ZMod p) 3 (htL (K := K) δ Rt hgen prims) :=
  orbitOf (htL (K := K) δ Rt hgen prims) (one_le_htL (K := K) δ Rt hgen prims) (dvdL (K := K) δ Rt hgen prims hpG)

/-- The ALU row nodes. -/
abbrev nodesLRun : Fin (nLRun (K := K) δ Rt hgen prims) → ZMod p :=
  powN (orbL (K := K) δ Rt hgen prims hpG) (nLRun (K := K) δ Rt hgen prims)

theorem nL_le_pow (h31L : Rows31AL (K := K) δ Rt hgen prims) :
    nLRun (K := K) δ Rt hgen prims ≤ 2 ^ htL (K := K) δ Rt hgen prims := by
  have hn : nLRun (K := K) δ Rt hgen prims ≤ 2 ^ 32 := by
    unfold Rows31AL at h31L; simp only [nLRun]; omega
  have hc : Nat.clog 2 (nLRun (K := K) δ Rt hgen prims) ≤ 32 := Nat.clog_le_of_le_pow hn
  have hm : max 1 (Nat.clog 2 (nLRun (K := K) δ Rt hgen prims)) ≤ 32 := max_le (by norm_num) hc
  have e : htL (K := K) δ Rt hgen prims = max 1 (Nat.clog 2 (nLRun (K := K) δ Rt hgen prims)) := by
    unfold htL; exact min_eq_right hm
  rw [e]
  exact (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

theorem nodesL_ok (h31L : Rows31AL (K := K) δ Rt hgen prims) :
    Function.Injective (nodesLRun (K := K) δ Rt hgen prims hpG) ∧
      ∀ (i : Fin (nLRun (K := K) δ Rt hgen prims)) (hi : (i : ℕ) + 1 < nLRun (K := K) δ Rt hgen prims),
        nodesLRun (K := K) δ Rt hgen prims hpG ⟨(i : ℕ) + 1, hi⟩ =
          nodesLRun (K := K) δ Rt hgen prims hpG i * (orbL (K := K) δ Rt hgen prims hpG).ω :=
  powN_ok _ (nL_le_pow (K := K) δ Rt hgen prims h31L)

/-- **The mixed J-9 A layout** (§0): `BA.Pb` with the cell / J / atom layout and the J fields of `B8L.Pb`. -/
def PbAL : PubJ9A p :=
  { (BA).Pb with
    hC := (B8L δ b Rt hgen prims hpG h31).Pb.hC, nC := (B8L δ b Rt hgen prims hpG h31).Pb.nC,
    hnC := (B8L δ b Rt hgen prims hpG h31).Pb.hnC, nodesC := (B8L δ b Rt hgen prims hpG h31).Pb.nodesC,
    orbitC := (B8L δ b Rt hgen prims hpG h31).Pb.orbitC,
    hJ := (B8L δ b Rt hgen prims hpG h31).Pb.hJ, nJ := (B8L δ b Rt hgen prims hpG h31).Pb.nJ,
    nodesJ := (B8L δ b Rt hgen prims hpG h31).Pb.nodesJ, orbitJ := (B8L δ b Rt hgen prims hpG h31).Pb.orbitJ,
    lay := (B8L δ b Rt hgen prims hpG h31).Pb.lay,
    hA := (B8L δ b Rt hgen prims hpG h31).Pb.hA, nA := (B8L δ b Rt hgen prims hpG h31).Pb.nA,
    hnA := (B8L δ b Rt hgen prims hpG h31).Pb.hnA, nodesA := (B8L δ b Rt hgen prims hpG h31).Pb.nodesA,
    orbitA := (B8L δ b Rt hgen prims hpG h31).Pb.orbitA,
    Rt := (B8L δ b Rt hgen prims hpG h31).Pb.Rt, regs := (B8L δ b Rt hgen prims hpG h31).Pb.regs,
    ids := (B8L δ b Rt hgen prims hpG h31).Pb.ids, idx := (B8L δ b Rt hgen prims hpG h31).Pb.idx,
    rk := (B8L δ b Rt hgen prims hpG h31).Pb.rk }

/-- **The J-9 AL public layout of the run** (§0; one record, `aluOn = true`). -/
def PbL : PubJ9AL p :=
  { toPubJ9A := PbAL δ b Rt hgen prims hpG h31A h31
    hL := htL (K := K) δ Rt hgen prims
    nL := nLRun (K := K) δ Rt hgen prims
    hnL := Nat.succ_pos _
    nodesL := nodesLRun (K := K) δ Rt hgen prims hpG
    orbitL := orbL (K := K) δ Rt hgen prims hpG
    aluOn := true
    prims := psRun (p := p) Rt hgen prims
    idxP := idxPOf (DL).cells prims
    rkP := rkPOf prims
    preL := preLOf δ (nodesLRun (K := K) δ Rt hgen prims hpG) (tbR δ Rt hgen prims (0 : Quad (algebraMap (ZMod p) K δ))) }

/-- **The ALU publics** at a coin: `SV / SS / SX` over the `nL` rows at `pubALv / pubALs / pubALx` (`+ 1`). -/
def pubsLOf (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if i < 2 then pub2 δ (SV δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ) i
  else if i < 4 then pub2 δ (SS δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ) i
  else if i < 6 then pub2 δ (SX δ Rt hgen prims (nLRun (K := K) δ Rt hgen prims) χ) i else 0

/-- **The J-9 AL honest message** (§0): `BA.M` with the cell / J / atom publics of `B8L.M`, plus the ALU publics. -/
def MAL (χ : Coins frameJ8 K) : MsgJ9AL' p K δ :=
  { toMsgJ9A' := { ((BA).M χ) with
      pubsC := ((B8L δ b Rt hgen prims hpG h31).M χ).pubsC
      pubsJ := ((B8L δ b Rt hgen prims hpG h31).M χ).pubsJ
      pubsA := ((B8L δ b Rt hgen prims hpG h31).M χ).pubsA }
    pubsL := pubsLOf δ Rt hgen prims χ }

/-- The honest ALU trace polynomials at a coin (`polyAL` at `chalsALJ8`, the limb coin `yOf`). -/
def trLOf (χ : Coins frameJ8 K) :
    Fin (AluSZChipJ9.aluSZChipJ9 δ b (PbL δ b Rt hgen prims hpG h31A h31).hnL
      (PbL δ b Rt hgen prims hpG h31A h31).nodesL (PbL δ b Rt hgen prims hpG h31A h31).orbitL (chalsALJ8 δ χ)
      (pubsLOf δ Rt hgen prims χ) (PbL δ b Rt hgen prims hpG h31A h31).preL).rap.w → (ZMod p)[X] :=
  polyAL δ b (PbL δ b Rt hgen prims hpG h31A h31).hnL (PbL δ b Rt hgen prims hpG h31A h31).nodesL
    (PbL δ b Rt hgen prims hpG h31A h31).orbitL (chalsALJ8 δ χ) (pubsLOf δ Rt hgen prims χ)
    (PbL δ b Rt hgen prims hpG h31A h31).preL (tbR δ Rt hgen prims (yOf δ χ))
    (r2AL δ (chalsALJ8 δ χ) (tbR δ Rt hgen prims (yOf δ χ)))

/-- Generic mixing of two J-9 A traces plus an ALU trace (kept generic so its read-backs are cheap for the kernel:
`C W V X S` of `T`, `M J A` of `T'`). -/
def mixTr {F : Type} [Field F] (T : TrJ9A F) (T' : TraceJ8.TrJ8 F) (L : Fin wAL → F[X]) : TrJ9AL F :=
  { toTrJ9A := { T with M := T'.M, J := T'.J, A := T'.A }, L := L }

section MixTr
variable {F : Type} [Field F] (T : TrJ9A F) (T' : TraceJ8.TrJ8 F) (L : Fin wAL → F[X])
theorem mixTr_C : (mixTr T T' L).C = T.C := rfl
theorem mixTr_W : (mixTr T T' L).W = T.W := rfl
theorem mixTr_V : (mixTr T T' L).V = T.V := rfl
theorem mixTr_X : (mixTr T T' L).X = T.X := rfl
theorem mixTr_S : (mixTr T T' L).S = T.S := rfl
theorem mixTr_M : (mixTr T T' L).M = T'.M := rfl
theorem mixTr_J : (mixTr T T' L).J = T'.J := rfl
theorem mixTr_A : (mixTr T T' L).A = T'.A := rfl
end MixTr

/-- **The J-9 AL honest traces** (§0): `BA.tr` with the cell / J / atom traces of `B8L.tr`, plus the ALU trace. -/
def trAL (χ : Coins frameJ8 K) : TrJ9AL (ZMod p) :=
  mixTr ((BA).tr χ) ((B8L δ b Rt hgen prims hpG h31).tr χ)
    (fun j => trLOf δ b Rt hgen prims hpG h31A h31 χ (Fin.cast (AluSZChipJ9.aluSZ_width_eq δ b _ _ _ _ _ _).symm j))

/-- The canonical J-9 AL rows. -/
def rowsAL : RowsJ9AL :=
  { toRowsJ9A := ComplJ9ARun.rowsA9 (PbL δ b Rt hgen prims hpG h31A h31).toPubJ9A,
    AL := (PbL δ b Rt hgen prims hpG h31A h31).nL }

/-- The canonical budget. -/
def gL : ℕ := ComplJ8Comp.canonG (PbL δ b Rt hgen prims hpG h31A h31).toPubJ8

/-- **The J-9 AL bad list (specs)**: J-9 A's, the J-8 families at `DL`, the ALU poles at `nL` rows. -/
def badSAL : List (BadSpec K) :=
  ComplJ9ARun.badSA δ b Rt hgen hpG h31A ++ (famsJL δ b Rt hgen prims hpG h31).flatten ++
    famAL δ (tbR δ Rt hgen prims) (nLRun (K := K) δ Rt hgen prims)

/-- **The J-9 AL bad events of the run.** -/
def badAL : List (Finset (Coins frameJ8 K) × ℚ) := badOf (badSAL δ b Rt hgen prims hpG h31A h31)

/-! ### Read-backs -/

theorem PbL_toPubJ9A : (PbL δ b Rt hgen prims hpG h31A h31).toPubJ9A = PbAL δ b Rt hgen prims hpG h31A h31 := rfl
theorem PbL_hC : (PbL δ b Rt hgen prims hpG h31A h31).hC = (B8L δ b Rt hgen prims hpG h31).Pb.hC := rfl
theorem PbL_nC : (PbL δ b Rt hgen prims hpG h31A h31).nC = (B8L δ b Rt hgen prims hpG h31).Pb.nC := rfl
theorem PbL_hJ : (PbL δ b Rt hgen prims hpG h31A h31).hJ = (B8L δ b Rt hgen prims hpG h31).Pb.hJ := rfl
theorem PbL_nJ : (PbL δ b Rt hgen prims hpG h31A h31).nJ = (B8L δ b Rt hgen prims hpG h31).Pb.nJ := rfl
theorem PbL_hA : (PbL δ b Rt hgen prims hpG h31A h31).hA = (B8L δ b Rt hgen prims hpG h31).Pb.hA := rfl
theorem PbL_nA : (PbL δ b Rt hgen prims hpG h31A h31).nA = (B8L δ b Rt hgen prims hpG h31).Pb.nA := rfl
theorem PbL_Rt : (PbL δ b Rt hgen prims hpG h31A h31).Rt = (B8L δ b Rt hgen prims hpG h31).Pb.Rt := rfl
theorem PbL_regs : (PbL δ b Rt hgen prims hpG h31A h31).regs = (B8L δ b Rt hgen prims hpG h31).Pb.regs := rfl
theorem PbL_ids : (PbL δ b Rt hgen prims hpG h31A h31).ids = (B8L δ b Rt hgen prims hpG h31).Pb.ids := rfl
theorem PbL_idx : (PbL δ b Rt hgen prims hpG h31A h31).idx = (B8L δ b Rt hgen prims hpG h31).Pb.idx := rfl
theorem PbL_rk : (PbL δ b Rt hgen prims hpG h31A h31).rk = (B8L δ b Rt hgen prims hpG h31).Pb.rk := rfl
theorem PbL_n : (PbL δ b Rt hgen prims hpG h31A h31).n = (BA).Pb.n := rfl
theorem PbL_nW : (PbL δ b Rt hgen prims hpG h31A h31).nW = (BA).Pb.nW := rfl
theorem PbL_nV : (PbL δ b Rt hgen prims hpG h31A h31).nV = (BA).Pb.nV := rfl
theorem PbL_nX : (PbL δ b Rt hgen prims hpG h31A h31).nX = (BA).Pb.nX := rfl
theorem PbL_nS : (PbL δ b Rt hgen prims hpG h31A h31).nS = (BA).Pb.nS := rfl
theorem PbL_aluOn : (PbL δ b Rt hgen prims hpG h31A h31).aluOn = true := rfl
theorem PbL_prims : (PbL δ b Rt hgen prims hpG h31A h31).prims = psRun (p := p) Rt hgen prims := rfl
theorem PbL_idxP : (PbL δ b Rt hgen prims hpG h31A h31).idxP = vcRun (p := p) Rt hgen prims := rfl
theorem PbL_rkP : (PbL δ b Rt hgen prims hpG h31A h31).rkP = rkPOf prims := rfl
theorem PbL_nL : (PbL δ b Rt hgen prims hpG h31A h31).nL = aluLen (K := K) δ Rt hgen prims + 1 := rfl


theorem trAL_M (χ : Coins frameJ8 K) :
    (trAL δ b Rt hgen prims hpG h31A h31 χ).M = ((B8L δ b Rt hgen prims hpG h31).tr χ).M := mixTr_M _ _ _
theorem trAL_J (χ : Coins frameJ8 K) :
    (trAL δ b Rt hgen prims hpG h31A h31 χ).J = ((B8L δ b Rt hgen prims hpG h31).tr χ).J := mixTr_J _ _ _
theorem trAL_A (χ : Coins frameJ8 K) :
    (trAL δ b Rt hgen prims hpG h31A h31 χ).A = ((B8L δ b Rt hgen prims hpG h31).tr χ).A := mixTr_A _ _ _

theorem trAL_C (χ : Coins frameJ8 K) : (trAL δ b Rt hgen prims hpG h31A h31 χ).C = ((BA).tr χ).C :=
  mixTr_C _ _ _
theorem trAL_W (χ : Coins frameJ8 K) : (trAL δ b Rt hgen prims hpG h31A h31 χ).W = ((BA).tr χ).W :=
  mixTr_W _ _ _
theorem trAL_V (χ : Coins frameJ8 K) : (trAL δ b Rt hgen prims hpG h31A h31 χ).V = ((BA).tr χ).V :=
  mixTr_V _ _ _
theorem trAL_X (χ : Coins frameJ8 K) : (trAL δ b Rt hgen prims hpG h31A h31 χ).X = ((BA).tr χ).X :=
  mixTr_X _ _ _
theorem trAL_S (χ : Coins frameJ8 K) : (trAL δ b Rt hgen prims hpG h31A h31 χ).S = ((BA).tr χ).S :=
  mixTr_S _ _ _

/-! ## 5. Good-coin transfers -/

theorem goodAL_spec {χ : Coins frameJ8 K} (h : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31, χ ∉ e.1) :
    ∀ sp ∈ badSAL δ b Rt hgen prims hpG h31A h31, χ ∉ sp.ev :=
  fun sp hs => h _ (List.mem_map.mpr ⟨sp, hs, rfl⟩)

/-- **Good for `BA`.** -/
theorem goodAL_BA {χ : Coins frameJ8 K} (h : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31, χ ∉ e.1) :
    (BA).Good χ := by
  intro e he
  obtain ⟨sp, hs, rfl⟩ := List.mem_map.mp he
  exact goodAL_spec δ b Rt hgen prims hpG h31A h31 h sp
    (List.mem_append_left _ (List.mem_append_left _ hs))

/-- **Good for `B8L`** (its walk order `(13, N8)` is `badSA`'s first order). -/
theorem goodAL_B8L {χ : Coins frameJ8 K} (h : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31, χ ∉ e.1) :
    (B8L δ b Rt hgen prims hpG h31).Good χ := by
  have hg := goodAL_spec δ b Rt hgen prims hpG h31A h31 h
  intro e he
  obtain ⟨sp, hs, rfl⟩ := List.mem_map.mp he
  refine hg sp ?_
  rcases List.mem_append.mp hs with h1 | h2
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h1
    simp only [List.mem_singleton] at ho
    subst ho
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    exact List.mem_map.mpr ⟨(⟨13, by decide⟩, N8 (p := p) Rt hgen), List.mem_cons_self, rfl⟩
  · exact List.mem_append_left _ (List.mem_append_right _ h2)

/-- **Outside every ALU pole event.** -/
theorem goodAL_famAL {χ : Coins frameJ8 K} (h : ∀ e ∈ badAL δ b Rt hgen prims hpG h31A h31, χ ∉ e.1) :
    ∀ e ∈ famAL δ (tbR δ Rt hgen prims) (nLRun (K := K) δ Rt hgen prims), χ ∉ e.ev :=
  fun e he => goodAL_spec δ b Rt hgen prims hpG h31A h31 h e (List.mem_append_right _ he)

end Iface

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALRun
