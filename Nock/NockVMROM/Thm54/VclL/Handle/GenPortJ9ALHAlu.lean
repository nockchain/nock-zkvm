/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHAlu.lean

  **Honest link, part 1: the executable ALU filler `GenAluE.aluGenE` computes the
  honest ALU table `AluSatRows.tblP`.**
  * §1 (b) `blockQE_toQ`: `K6.toQ` (row-wise `qQ`) of the executable round-1 block `blockQE p y cl` is the honest
    `blockQ p (toQ y) cl` (homomorphism inductions over `evRE hornerE packVE hornerQ1E slot*E latchOfE slotDE hdrDE
    laneDE runSumsE laneHLE`);
  * §2 the table: `tbE` (= `tblP` at the exec's preg rows and calls, limb coin `toQ (yE χe)`), its base rows are the
    exec's `aluRowsB`, its `𝕂′` rows are `qQ` of the exec's `qs` (`rowAt_tbE_fst` / `rowAt_tbE_snd`);
  * §3 (c) the round-2 values: the exec's five inverses are the honest `dV⁻¹ … dX⁻¹`, its three row terms `tV tS tX`,
    its three inclusive prefix sums `accN`, at every row `i < N`;
  * §4 (d) the publics: `Σ` over the exec's `N = 3·2^h` rows is the honest `Σ_{i : Fin N}`;
  * §5 (a) data: `pregsOf cs (primsC prims ids) ids = pregsP (primsC prims ids) (idxPOf cs prims) mOf` with
    `mOf id = (pcallsR pids rows).countP (·.1 = id) + 1` (= `ComplJ9ALRun.mRun`), and `callsLOf` at `primsC prims ids`
    is `callsLOf` at `prims`, for `ids = (callsOf rows).map Prod.fst`, `pc = pcallsR pids rows`.
-/
import Nock.V1J9AL.GenAluE
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatPreg
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluPoles
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.V1J9AL.GenAluE
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. (b) The `K6 → 𝕂′` port of the round-1 rows -/

section Round1

/-- A `K6` pair in `𝕂′`. -/
def pQ (x : K6 × K6) : KQ × KQ := (K6.toQ x.1, K6.toQ x.2)
/-- A `K6` triple in `𝕂′`. -/
def tQ (x : K6 × K6 × K6) : KQ × KQ × KQ := (K6.toQ x.1, K6.toQ x.2.1, K6.toQ x.2.2)
/-- **A `K6` round-1 row in `𝕂′`.** -/
def qQ (q : QRow K6) : QRow KQ :=
  ⟨K6.toQ q.H, K6.toQ q.HO, K6.toQ q.L, K6.toQ q.D1, K6.toQ q.D2, K6.toQ q.S1, K6.toQ q.S2, K6.toQ q.RL,
    K6.toQ q.RO⟩

theorem qQ_zero : qQ QRow.zero = QRow.zero := by
  simp only [qQ, QRow.zero, K6.toQ_zero]

theorem toQ_nK (n : ℕ) : K6.toQ (nK n) = (n : KQ) := by
  unfold nK
  rw [GenPortJ9AChips.toQ_zq]
  simp only [VclL.Chips.ChipRAP.liftQ, map_natCast]

theorem toQ_iK (z : ℤ) : K6.toQ (iK z) = (z : KQ) := by
  unfold iK
  rw [GenPortJ9AChips.toQ_zq]
  simp only [VclL.Chips.ChipRAP.liftQ, map_intCast]

theorem toQ_evRE (y : K6) : ∀ l : List ℤ, K6.toQ (evRE y l) = evR (K6.toQ y) l
  | [] => K6.toQ_zero
  | d :: ds => by rw [evRE, evR, K6.toQ_add, K6.toQ_mul, toQ_iK, toQ_evRE y ds]

theorem toQ_hornerE (y : K6) (ws : List ℕ) : K6.toQ (hornerE y ws) = horner (K6.toQ y) ws :=
  toQ_evRE y (zl ws)

theorem toQ_hornerFromE (y : K6) (ws : List ℕ) (i : ℕ) :
    K6.toQ (hornerFromE y ws i) = hornerFrom (K6.toQ y) ws i :=
  toQ_hornerE y (ws.drop i)

theorem toQ_foldl_add : ∀ (l : List K6) (a : K6), K6.toQ (l.foldl (· + ·) a) = K6.toQ a + (l.map K6.toQ).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, toQ_foldl_add l (a + x), K6.toQ_add, List.map_cons, List.sum_cons, add_assoc]

theorem toQ_packVE (y : K6) (w : ℕ) : K6.toQ (packVE y w) = packV (K6.toQ y) w := by
  unfold packVE packV
  rw [toQ_foldl_add, K6.toQ_zero, zero_add, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, K6.toQ_mul, toQ_nK, toQ_powE]

theorem toQ_hornerQ1E (y : K6) : ∀ ws : List ℕ, K6.toQ (hornerQ1E y ws) = hornerQ1 (K6.toQ y) ws
  | [] => K6.toQ_zero
  | w :: ws => by
    rw [hornerQ1E, hornerQ1, K6.toQ_add, K6.toQ_mul, toQ_packVE, toQ_powE, toQ_hornerQ1E y ws]

theorem toQ_slotHE (y : K6) (s : SlotL) (i : ℕ) : K6.toQ (slotHE y s i) = slotH (K6.toQ y) s i := by
  unfold slotHE slotH
  split_ifs
  · exact toQ_hornerQ1E y _
  · exact K6.toQ_zero
  · exact toQ_hornerFromE y _ i

theorem toQ_slotHOE (y : K6) (s : SlotL) (i : ℕ) : K6.toQ (slotHOE y s i) = slotHO (K6.toQ y) s i := by
  unfold slotHOE slotHO
  split_ifs
  · exact K6.toQ_zero
  · exact toQ_hornerFromE y _ i

theorem toQ_slotLE (y : K6) (s : SlotL) : K6.toQ (slotLE y s) = slotL (K6.toQ y) s := by
  unfold slotLE slotL
  split_ifs
  · rw [K6.toQ_mul, K6.toQ_sub, toQ_nK, toQ_slotHE]
  · exact toQ_hornerE y _

theorem pQ_latchOfE (p : ℕ) (y : K6) (cl : CallL) : pQ (latchOfE p y cl) = latchOf p (K6.toQ y) cl := by
  unfold latchOfE latchOf
  rcases (slotsOf p cl).find? (fun s => isF1 cl.op s) with _ | s
  · simp only [pQ, K6.toQ_zero]
  · simp only [pQ, toQ_slotLE, toQ_slotHOE]

theorem pQ_slotDE (p : ℕ) (y : K6) (cl : CallL) (s : SlotL) : pQ (slotDE p y cl s) = AluHonestRows.slotD p (K6.toQ y) cl s := by
  have hl := pQ_latchOfE p y cl
  simp only [pQ, Prod.ext_iff] at hl
  unfold slotDE AluHonestRows.slotD
  split_ifs
  · simp only [pQ, K6.toQ_add, K6.toQ_mul, K6.toQ_sub, toQ_nK, toQ_iK, toQ_slotLE, toQ_slotHOE, hl.1, hl.2]
  · simp only [pQ, K6.toQ_mul, toQ_iK, toQ_slotLE]

theorem pQ_hdrDE (cl : CallL) : pQ (hdrDE cl) = hdrD (Q := KQ) cl := by
  unfold hdrDE hdrD
  simp only [pQ]
  split_ifs <;> simp [K6.toQ_sub, K6.toQ_one, K6.toQ_zero, toQ_nK]

theorem laneDE_toQ (p : ℕ) (y : K6) (cl : CallL) : (laneDE p y cl).map pQ = laneD p (K6.toQ y) cl := by
  unfold laneDE laneD
  rw [List.map_flatMap]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  split_ifs
  · exact pQ_slotDE p y cl s
  · simp only [pQ, K6.toQ_zero]

theorem runSumsE_toQ : ∀ (acc : K6 × K6) (ds : List (K6 × K6)),
    (runSumsE acc ds).map pQ = runSums (pQ acc) (ds.map pQ)
  | _, [] => rfl
  | acc, d :: ds => by
    rw [runSumsE, List.map_cons, List.map_cons, runSums, runSumsE_toQ _ ds]
    simp only [pQ, K6.toQ_add]

theorem laneHLE_toQ (y : K6) (cl : CallL) (p : ℕ) : (laneHLE y cl p).map tQ = laneHL (K6.toQ y) cl p := by
  unfold laneHLE laneHL
  rw [List.map_flatMap]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, tQ, toQ_slotHE, toQ_slotHOE]
  split_ifs
  · rw [toQ_slotLE]
  · rw [K6.toQ_zero]

/-- **(b) The executable round-1 block is the honest one**, row by row through `qQ`. -/
theorem blockQE_toQ (p : ℕ) (y : K6) (cl : CallL) : (blockQE p y cl).map qQ = blockQ p (K6.toQ y) cl := by
  unfold blockQE blockQ
  dsimp only
  rw [← pQ_latchOfE, ← pQ_hdrDE, ← laneHLE_toQ, ← laneDE_toQ, ← runSumsE_toQ, List.map_cons]
  simp only [List.zip_map, List.map_map]
  refine congrArg₂ List.cons ?_ (List.map_congr_left fun x _ => rfl)
  simp only [qQ, pQ, K6.toQ_zero]

end Round1

/-! ## 2. The table -/

section Table
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

/-- The exec's base rows (`aluGenE`'s `base`). -/
abbrev baseE (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) : List (BRow (ZMod p)) :=
  aluRowsB p (pregsOf cs ps ids) (callsLOf cs Hm ps pc)

/-- The exec's round-1 rows (`aluGenE`'s `qs`). -/
def qsE (y : K6) (npreg : ℕ) (cls : List CallL) : List (QRow K6) :=
  List.replicate npreg QRow.zero ++ cls.flatMap (blockQE p y) ++ [QRow.zero]

theorem qsE_toQ (y : K6) (npreg : ℕ) (cls : List CallL) :
    (qsE y npreg cls).map qQ = aluRowsQ p (K6.toQ y) npreg cls := by
  simp only [qsE, aluRowsQ, List.map_append, List.map_replicate, qQ_zero, List.map_flatMap, blockQE_toQ,
    List.map_cons, List.map_nil]

/-- **The honest table at the exec's data**: `tblP` at the limb coin `toQ y`. -/
abbrev tbE (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    List (BRow (ZMod p) × QRow KQ) :=
  tblP (K := KC) deltaF p (K6.toQ y) pregs cls

theorem zipB_fst' (y : KQ) (cl : CallL) :
    (zipB (K := KC) deltaF p y cl).map Prod.fst = blockB (F := ZMod p) p cl :=
  List.map_fst_zip (by rw [blockQ_length (F := ZMod p)])

theorem zipB_snd' (y : KQ) (cl : CallL) :
    (zipB (K := KC) deltaF p y cl).map Prod.snd = blockQ p y cl :=
  List.map_snd_zip (by rw [blockQ_length (F := ZMod p)])

theorem map_fst_pair {α β : Type} (b : β) : ∀ l : List α, l.map (Prod.fst ∘ fun r => (r, b)) = l
  | [] => rfl
  | a :: l => by rw [List.map_cons, map_fst_pair b l]; rfl

theorem map_snd_pair {α β : Type} (b : β) : ∀ l : List α, l.map (Prod.snd ∘ fun r => (r, b)) = List.replicate l.length b
  | [] => rfl
  | a :: l => by rw [List.map_cons, map_snd_pair b l]; rfl

theorem tbE_fst (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    (tbE y pregs cls).map Prod.fst = aluRowsB p pregs cls := by
  simp only [tbE, tblP, aluRowsB, List.map_append, List.map_map, List.map_flatMap, zipB_fst', List.map_cons,
    List.map_nil]
  rw [map_fst_pair]

theorem tbE_snd (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    (tbE y pregs cls).map Prod.snd = aluRowsQ p (K6.toQ y) pregs.length cls := by
  simp only [tbE, tblP, aluRowsQ, List.map_append, List.map_map, List.map_flatMap, zipB_snd', List.map_cons,
    List.map_nil]
  rw [map_snd_pair]

theorem tbE_length (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    (tbE y pregs cls).length = (aluRowsB p pregs cls).length := by
  rw [← tbE_fst y pregs cls, List.length_map]

/-- **Row `i`'s base row is the exec's** (every `i`; both default to `padRow`). -/
theorem rowAt_tbE_fst (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) :
    (rowAt (K := KC) deltaF (tbE y pregs cls) i).1 = (aluRowsB p pregs cls).getD i padRow := by
  unfold rowAt
  rw [← tbE_fst y pregs cls, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (tbE y pregs cls)[i]? <;> rfl

/-- **Row `i`'s `𝕂′` row is `qQ` of the exec's** (every `i`; both default to `0`). -/
theorem rowAt_tbE_snd (y : K6) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) :
    (rowAt (K := KC) deltaF (tbE y pregs cls) i).2 = qQ ((qsE y pregs.length cls).getD i QRow.zero) := by
  unfold rowAt
  have h := congrArg (fun l => l[i]?) (tbE_snd y pregs cls)
  rw [← qsE_toQ] at h
  simp only [List.getElem?_map] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases h1 : (tbE y pregs cls)[i]? with _ | a <;> rcases h2 : (qsE y pregs.length cls)[i]? with _ | b <;>
    rw [h1, h2] at h <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h
  · exact qQ_zero.symm
  · exact h

end Table

/-! ## 3. (c) The round-2 values -/

section Round2
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.Reified Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8 chalsALJ8_ok chalsALJ8_zAt chalsALJ8_agree valKey
  keyRgE opRecE keyJetE keyXE keyRgRE opRecRE keyJetRE keyXRE reE tagRgP tagOp)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- The roles of a `K6` round-1 row, in the chip's order. -/
def rolesQ (q : QRow K6) : List K6 := [q.H, q.HO, q.L, q.D1, q.D2, q.S1, q.S2, q.RL, q.RO]

theorem equiv_symm_toQ (x : K6) :
    (Quad.equiv (algebraMap (ZMod p) KC deltaF)).symm (K6.toQ x) = (K3.toK x.re, K3.toK x.im) :=
  equiv_symm_mk (K := KC) deltaF _ _

theorem kvec_qQ (q : QRow K6) (j : ℕ) (hj : j < 18) :
    kvec deltaF (qQ q) j =
      if j % 2 = 0 then K3.toK ((rolesQ q).getD (j / 2) 0).re else K3.toK ((rolesQ q).getD (j / 2) 0).im := by
  interval_cases j <;> simp [kvec, qQ, rolesQ, QRow.role] <;>
    first | exact congrArg Prod.fst (equiv_symm_toQ _) | exact congrArg Prod.snd (equiv_symm_toQ _)

/-- The honest model environments of a row `(r, qQ q)`. -/
def eKq (χe : CoinsE) (q : QRow K6) : Env KC :=
  ⟨kvec deltaF (qQ q), fun _ => 0, chalsALJ8 deltaF (toχ χe), fun _ => 0⟩
def eFr (r : BRow (ZMod p)) : Env (ZMod p) := envB r.col (fun _ => 0)

/-- The exec validity denominator of a row. -/
def dVE (χe : CoinsE) (r : BRow (ZMod p)) (q : QRow K6) : K6 :=
  compressE (γVE χe) (ρVE χe) (fun c : Fin 5 =>
    match (c : ℕ) with
    | 0 => zE χe
    | 1 => 0
    | 2 => q.L
    | 3 => 0
    | _ => Nock.V1J9A.GenAxE.zq r.sv)
/-- The exec handle-key denominator of an 8-entry key. -/
def hkE (χe : CoinsE) (l : List (ZMod p)) : K6 := compressE (γHE χe) (ρHE χe) (keyOf (m := 8) l)
/-- The exec export denominator of a row. -/
def dXE (χe : CoinsE) (r : BRow (ZMod p)) : K6 :=
  compressE (γHE χe) (ρHE χe) (keyOf (m := 5) [r.vS, r.kA, r.vA, r.kB, r.vB])

theorem laneRow_eq (χe : CoinsE) (r : BRow (ZMod p)) (q : QRow K6) :
    laneRow χe r q =
      (Nock.V1J9A.GenAxE.zq r.aV * (dVE χe r q)⁻¹,
        Nock.V1J9A.GenAxE.zq (r.sH - r.sP * r.mP) * (hkE χe [r.idc, r.kc, r.vc, 0, 0, 0, 0, 7])⁻¹ +
          Nock.V1J9A.GenAxE.zq (r.sH - r.sP * r.mP) * (hkE χe [r.idc, r.opc, 0, 0, 0, 0, 0, 6])⁻¹ -
          Nock.V1J9A.GenAxE.zq (r.sH * r.mJ) * (hkE χe [r.idc, r.kc, r.vc, r.kS, r.vS, r.kE, r.vE, 3])⁻¹,
        Nock.V1J9A.GenAxE.zq r.sH * (dXE χe r)⁻¹,
        (dVE χe r q)⁻¹, (hkE χe [r.idc, r.kc, r.vc, 0, 0, 0, 0, 7])⁻¹, (hkE χe [r.idc, r.opc, 0, 0, 0, 0, 0, 6])⁻¹,
        (hkE χe [r.idc, r.kc, r.vc, r.kS, r.vS, r.kE, r.vE, 3])⁻¹, (dXE χe r)⁻¹) := rfl

theorem toQ_zq' (x : ZMod p) : K6.toQ (Nock.V1J9A.GenAxE.zq x) = liftQ (K := KC) deltaF x :=
  GenPortJ9AChips.toQ_zq x

/-- **The validity denominator.** -/
theorem toQ_dVE (χe : CoinsE) (r : BRow (ZMod p)) (q : QRow K6) :
    K6.toQ (dVE χe r q) = (den deltaF (valKey : List (QE (ZMod p)))).ev deltaF (eKq χe q) (eFr r) := by
  have hok : ChalsOK deltaF (eKq χe q).chal (Quad.mk _ (toχ χe WeightsJ8.c4) (toχ χe WeightsJ8.c6))
      (Quad.mk _ (toχ χe WeightsJ8.c5) (toχ χe WeightsJ8.c7))
      5 := chalsOK_mono deltaF (show 5 ≤ 11 by norm_num) (chalsALJ8_ok deltaF (toχ χe))
  rw [den_ev_compress' deltaF (valKey : List (QE (ZMod p))) (m := 5) rfl _ _ _ _ hok, dVE, toQ_compressE]
  congr 1
  funext c
  have hz := chalsALJ8_zAt deltaF (toχ χe)
  fin_cases c
  · simp only [keyVec, valKey, AtomChipHQ.zAt, ev_chal]
    exact hz.symm
  · simp only [keyVec, valKey, List.getD_cons_succ, List.getD_cons_zero, ev_zero]; exact K6.toQ_zero
  · simp only [keyVec, valKey, List.getD_cons_succ, List.getD_cons_zero, ev_var, eKq, AluSZChipJ9.L]
    rw [kvec_qQ q 4 (by decide), kvec_qQ q 5 (by decide)]
    rfl
  · simp only [keyVec, valKey, List.getD_cons_succ, List.getD_cons_zero, ev_zero]; exact K6.toQ_zero
  · simp only [keyVec, valKey, List.getD_cons_succ, List.getD_cons_zero, ev_base]
    rw [toQ_zq']
    rfl

theorem coinsQ_eKq (χe : CoinsE) (q : QRow K6) :
    TeleHQ.coinsQ deltaF (eKq χe q) = (⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩ :
      FiniteIO.IOCoins KQ) :=
  AluPoles.coinsQ_AL deltaF (toχ χe) [] 0

/-- A handle-key denominator, from the key's evaluation. -/
theorem toQ_hkE_of (χe : CoinsE) (q : QRow K6) (r : BRow (ZMod p)) {m : ℕ} (key : List (CoeffExpr (ZMod p)))
    (hk : key.length ≤ m) (v : List (ZMod p))
    (hv : ∀ c : Fin m, (key.getD c (.const 0)).eval (eFr r) = v.getD c 0) :
    K6.toQ (compressE (γHE χe) (ρHE χe) (keyOf (m := m) v)) =
      (HQ.denKeyQ deltaF key).ev deltaF (eKq χe q) (eFr r) := by
  rw [AxisTeleJ9.denKeyQ_evL deltaF _ _ m key hk, coinsQ_eKq, toQ_compressE]
  congr 1
  funext c
  rw [keyOf, toQ_zq', ← hv c]
  rfl

theorem toQ_dR (χe : CoinsE) (q : QRow K6) (r : BRow (ZMod p)) :
    K6.toQ (hkE χe [r.idc, r.kc, r.vc, 0, 0, 0, 0, 7]) =
      (HQ.denKeyQ deltaF (keyRgE : List (CoeffExpr (ZMod p)))).ev deltaF (eKq χe q) (eFr r) :=
  toQ_hkE_of χe q r _ (by simp [keyRgE, keyRgRE]) _ fun c => by
    fin_cases c <;> simp [keyRgE, keyRgRE, reE, eFr, envB, CoeffExpr.eval, tagRgP]

theorem toQ_dO (χe : CoinsE) (q : QRow K6) (r : BRow (ZMod p)) :
    K6.toQ (hkE χe [r.idc, r.opc, 0, 0, 0, 0, 0, 6]) =
      (HQ.denKeyQ deltaF (opRecE : List (CoeffExpr (ZMod p)))).ev deltaF (eKq χe q) (eFr r) :=
  toQ_hkE_of χe q r _ (by simp [opRecE, opRecRE]) _ fun c => by
    fin_cases c <;> simp [opRecE, opRecRE, reE, eFr, envB, CoeffExpr.eval, tagOp]

theorem toQ_dJ (χe : CoinsE) (q : QRow K6) (r : BRow (ZMod p)) :
    K6.toQ (hkE χe [r.idc, r.kc, r.vc, r.kS, r.vS, r.kE, r.vE, 3]) =
      (HQ.denKeyQ deltaF (keyJetE : List (CoeffExpr (ZMod p)))).ev deltaF (eKq χe q) (eFr r) :=
  toQ_hkE_of χe q r _ (by simp [keyJetE, keyJetRE]) _ fun c => by
    fin_cases c <;> simp [keyJetE, keyJetRE, reE, eFr, envB, CoeffExpr.eval]

theorem toQ_dX (χe : CoinsE) (q : QRow K6) (r : BRow (ZMod p)) :
    K6.toQ (dXE χe r) = (HQ.denKeyQ deltaF (keyXE : List (CoeffExpr (ZMod p)))).ev deltaF (eKq χe q) (eFr r) :=
  toQ_hkE_of χe q r _ (by simp [keyXE, keyXRE]) _ fun c => by
    fin_cases c <;> simp [keyXE, keyXRE, reE, eFr, envB, CoeffExpr.eval]

/-! ### At a table row -/

variable (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ)

local notation "TB" => tbE (yE χe) pregs cls
local notation "CH" => chalsALJ8 deltaF (toχ χe)

/-- Row `i`'s exec base row. -/
def rbE (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) : BRow (ZMod p) :=
  (aluRowsB p pregs cls).getD i padRow
/-- Row `i`'s exec round-1 row. -/
def rqE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) : QRow K6 :=
  (qsE (yE χe) pregs.length cls).getD i QRow.zero

theorem eKM_tbE : eKM deltaF CH TB i = eKq χe (rqE χe pregs cls i) := by
  unfold eKM eKq; rw [rowAt_tbE_snd]; rfl

theorem eFM_tbE : eFM deltaF TB i = eFr (rbE pregs cls i) := by
  unfold eFM eFr; rw [rowAt_tbE_fst]; rfl

theorem rowAt_fst_rbE : (rowAt (K := KC) deltaF TB i).1 = rbE pregs cls i := rowAt_tbE_fst _ _ _ _

theorem toQ_dV_at : K6.toQ (dVE χe (rbE pregs cls i) (rqE χe pregs cls i)) = dV deltaF CH TB i := by
  rw [toQ_dVE, ← eKM_tbE, ← eFM_tbE]; rfl
theorem toQ_dR_at (r : BRow (ZMod p)) (hr : r = rbE pregs cls i) :
    K6.toQ (hkE χe [r.idc, r.kc, r.vc, 0, 0, 0, 0, 7]) = dR deltaF CH TB i := by
  subst hr; rw [toQ_dR χe (rqE χe pregs cls i), ← eKM_tbE, ← eFM_tbE]; rfl
theorem toQ_dO_at (r : BRow (ZMod p)) (hr : r = rbE pregs cls i) :
    K6.toQ (hkE χe [r.idc, r.opc, 0, 0, 0, 0, 0, 6]) = dO deltaF CH TB i := by
  subst hr; rw [toQ_dO χe (rqE χe pregs cls i), ← eKM_tbE, ← eFM_tbE]; rfl
theorem toQ_dJ_at (r : BRow (ZMod p)) (hr : r = rbE pregs cls i) :
    K6.toQ (hkE χe [r.idc, r.kc, r.vc, r.kS, r.vS, r.kE, r.vE, 3]) = dJ deltaF CH TB i := by
  subst hr; rw [toQ_dJ χe (rqE χe pregs cls i), ← eKM_tbE, ← eFM_tbE]; rfl
theorem toQ_dX_at : K6.toQ (dXE χe (rbE pregs cls i)) = dX deltaF CH TB i := by
  rw [toQ_dX χe (rqE χe pregs cls i), ← eKM_tbE, ← eFM_tbE]; rfl

/-- **The three row terms.** -/
theorem toQ_tV_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).1 = tV (n := n) deltaF CH TB ⟨i, hi⟩ := by
  show K6.toQ (Nock.V1J9A.GenAxE.zq (rbE pregs cls i).aV * (dVE χe (rbE pregs cls i) (rqE χe pregs cls i))⁻¹) = _
  rw [K6.toQ_mul, K6.toQ_inv, toQ_zq', toQ_dV_at]
  unfold tV; rw [rowAt_fst_rbE]

theorem toQ_tS_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.1 = tS (n := n) deltaF CH TB ⟨i, hi⟩ := by
  rw [laneRow_eq]
  simp only [K6.toQ_mul, K6.toQ_inv, K6.toQ_add, K6.toQ_sub, toQ_zq']
  rw [toQ_dR_at χe pregs cls i _ rfl, toQ_dO_at χe pregs cls i _ rfl, toQ_dJ_at χe pregs cls i _ rfl]
  unfold tS wSv; rw [rowAt_fst_rbE]

theorem toQ_tX_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.1 = tX (n := n) deltaF CH TB ⟨i, hi⟩ := by
  show K6.toQ (Nock.V1J9A.GenAxE.zq (rbE pregs cls i).sH * (dXE χe (rbE pregs cls i))⁻¹) = _
  rw [K6.toQ_mul, K6.toQ_inv, toQ_zq', toQ_dX_at]
  unfold tX; rw [rowAt_fst_rbE]

/-- **The five inverses** (`qv2 0 … 4`). -/
theorem toQ_invV_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.2.1 = qv2 (n := n) deltaF CH TB 0 ⟨i, hi⟩ := by
  show K6.toQ (dVE χe (rbE pregs cls i) (rqE χe pregs cls i))⁻¹ = (dV deltaF CH TB i)⁻¹
  rw [K6.toQ_inv, toQ_dV_at]
theorem toQ_invR_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.2.2.1 = qv2 (n := n) deltaF CH TB 1 ⟨i, hi⟩ := by
  show K6.toQ (hkE χe [(rbE pregs cls i).idc, (rbE pregs cls i).kc, (rbE pregs cls i).vc, 0, 0, 0, 0, 7])⁻¹ =
    (dR deltaF CH TB i)⁻¹
  rw [K6.toQ_inv, toQ_dR_at χe pregs cls i _ rfl]
theorem toQ_invO_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.2.2.2.1 =
      qv2 (n := n) deltaF CH TB 2 ⟨i, hi⟩ := by
  show K6.toQ (hkE χe [(rbE pregs cls i).idc, (rbE pregs cls i).opc, 0, 0, 0, 0, 0, 6])⁻¹ = (dO deltaF CH TB i)⁻¹
  rw [K6.toQ_inv, toQ_dO_at χe pregs cls i _ rfl]
theorem toQ_invJ_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.2.2.2.2.1 =
      qv2 (n := n) deltaF CH TB 3 ⟨i, hi⟩ := by
  show K6.toQ (hkE χe [(rbE pregs cls i).idc, (rbE pregs cls i).kc, (rbE pregs cls i).vc, (rbE pregs cls i).kS,
    (rbE pregs cls i).vS, (rbE pregs cls i).kE, (rbE pregs cls i).vE, 3])⁻¹ = (dJ deltaF CH TB i)⁻¹
  rw [K6.toQ_inv, toQ_dJ_at χe pregs cls i _ rfl]
theorem toQ_invX_at {n : ℕ} (hi : i < n) :
    K6.toQ (laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)).2.2.2.2.2.2.2 =
      qv2 (n := n) deltaF CH TB 4 ⟨i, hi⟩ := by
  show K6.toQ (dXE χe (rbE pregs cls i))⁻¹ = (dX deltaF CH TB i)⁻¹
  rw [K6.toQ_inv, toQ_dX_at]

end Round2

/-! ## 4. (c)+(d) Prefix sums and the publics over the padded rows -/

section Sums
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- `inclSums` of a row-indexed list: the honest `accN`. -/
theorem toQ_incl_accN {N : ℕ} (f : ℕ → K6) (t : Fin N → KQ) (ht : ∀ j (hj : j < N), K6.toQ (f j) = t ⟨j, hj⟩)
    (i : ℕ) (hi : i < N) :
    K6.toQ ((Nock.V1J9A.GenAxE.inclSums ((List.range N).map f)).getD i 0) = accN t i := by
  rw [GenPortJ9AChips.toQ_inclSums_getD _ _ (by simpa using hi)]
  unfold accN
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < N := by have := Finset.mem_range.mp hj; omega
  rw [tN, dif_pos hj', ← ht j hj']
  simp [List.getD_eq_getElem?_getD, hj']

/-- A sum over the padded rows: the honest `Σ_{i : Fin N}`. -/
theorem toQ_foldl_sum {N : ℕ} (f : ℕ → K6) (t : Fin N → KQ) (ht : ∀ j (hj : j < N), K6.toQ (f j) = t ⟨j, hj⟩) :
    K6.toQ (((List.range N).map f).foldl (· + ·) 0) = ∑ i : Fin N, t i := by
  rw [GenPortJ9AChips.toQ_foldl_zero, ← Fin.sum_univ_eq_sum_range (fun j => K6.toQ (f j)) N]
  exact Finset.sum_congr rfl fun i _ => ht i i.2

end Sums

/-! ## 5. (a) The data equality of the preg builders and of the calls -/

section Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg (pregsP)

theorem primsC_idem (prims : List (ℕ × PrimOp)) (ids : List ℕ) : primsC (primsC prims ids) ids = primsC prims ids := by
  simp [primsC, List.filter_filter]

theorem find_filter_ids (ids : List ℕ) {id : ℕ} (h : id ∈ ids) : ∀ prims : List (ℕ × PrimOp),
    (prims.filter fun q => decide (q.1 ∈ ids)).find? (fun q => decide (q.1 = id)) =
      prims.find? (fun q => decide (q.1 = id))
  | [] => rfl
  | a :: as => by
    by_cases ha : a.1 ∈ ids
    · rw [List.filter_cons_of_pos (by simpa using ha), List.find?_cons, List.find?_cons, find_filter_ids ids h as]
    · rw [List.filter_cons_of_neg (by simpa using ha), List.find?_cons, find_filter_ids ids h as]
      have : ¬ a.1 = id := fun e => ha (e ▸ h)
      simp [this]

theorem opOf_primsC (prims : List (ℕ × PrimOp)) (ids : List ℕ) {id : ℕ} (h : id ∈ ids) :
    opOf (primsC prims ids) id = opOf prims id := by
  unfold opOf primsC
  rw [find_filter_ids ids h]

theorem idxPOf_primsC (cs : List Noun) (prims : List (ℕ × PrimOp)) (ids : List ℕ) {id : ℕ} (h : id ∈ ids) :
    idxPOf cs (primsC prims ids) id = idxPOf cs prims id := by
  unfold idxPOf; rw [opOf_primsC prims ids h]

/-- The primitive calls' ids are call ids. -/
theorem pcallsR_mem_ids (pids : List ℕ) (rows : Array Nock.Edit.GenX.RowNX) :
    ∀ x ∈ pcallsR pids rows, x.1 ∈ (Nock.V1J8.Gen.callsOf rows).map Prod.fst := by
  intro x hx
  have h := pcallsR_fst pids rows
  have hm : (x.1, x.2.1) ∈ aCallsP pids (Nock.V1J8.Gen.callsOf rows) := h ▸ List.mem_map_of_mem hx
  exact List.mem_map.mpr ⟨_, (aCallsP_sub pids _ _ hm).1, rfl⟩

/-- The count of a primitive id among the call ids is its count among the primitive calls. -/
theorem count_ids_eq (pids : List ℕ) (rows : Array Nock.Edit.GenX.RowNX) {id : ℕ} (h : id ∈ pids) :
    ((Nock.V1J8.Gen.callsOf rows).map Prod.fst).count id = (pcallsR pids rows).countP (fun x => x.1 = id) := by
  have e1 : (pcallsR pids rows).countP (fun x => x.1 = id) =
      ((pcallsR pids rows).map (fun x => (x.1, x.2.1))).countP (fun c => c.1 = id) := by
    rw [List.countP_map]; rfl
  rw [e1, pcallsR_fst, aCallsP, List.countP_filter, List.count, List.countP_map]
  congr 1
  funext c
  by_cases hc : c.1 = id
  · simp [hc, h]
  · simp [hc]

/-- **(a) The preg rows of the generator are `pregsP`** at `ps = primsC prims ids`, `vcOf = idxPOf cs prims`,
`mOf id = (pcallsR pids rows).countP (·.1 = id) + 1` (the shapes of `ComplJ9ALRun.psRun / vcRun / mRun`). -/
theorem pregsOf_eq {F : Type} [Field F] (cs : List Noun) (prims : List (ℕ × PrimOp))
    (rows : Array Nock.Edit.GenX.RowNX) :
    (pregsOf cs (primsC prims ((Nock.V1J8.Gen.callsOf rows).map Prod.fst))
        ((Nock.V1J8.Gen.callsOf rows).map Prod.fst) : List (BRow F)) =
      pregsP (primsC prims ((Nock.V1J8.Gen.callsOf rows).map Prod.fst)) (idxPOf cs prims)
        (fun id => (pcallsR (prims.map Prod.fst) rows).countP (fun x => x.1 = id) + 1) := by
  unfold pregsOf pregsP
  rw [primsC_idem]
  refine List.map_congr_left fun q hq => ?_
  have hq' := List.mem_filter.mp hq
  have hid : q.1 ∈ (Nock.V1J8.Gen.callsOf rows).map Prod.fst := by simpa using hq'.2
  have hp : q.1 ∈ prims.map Prod.fst := List.mem_map_of_mem hq'.1
  rw [idxPOf_primsC cs prims _ hid, count_ids_eq _ rows hp]

/-- **(a) The calls of the generator** (`callsLOf` at `primsC prims ids`) are `callsLOf` at `prims`. -/
theorem callsLOf_eq (cs : List Noun) (Hm : Noun → ℕ × ℕ) (prims : List (ℕ × PrimOp))
    (rows : Array Nock.Edit.GenX.RowNX) :
    callsLOf cs Hm (primsC prims ((Nock.V1J8.Gen.callsOf rows).map Prod.fst)) (pcallsR (prims.map Prod.fst) rows) =
      callsLOf cs Hm prims (pcallsR (prims.map Prod.fst) rows) := by
  unfold callsLOf
  refine List.map_congr_left fun x hx => ?_
  have h := pcallsR_mem_ids _ rows x hx
  rw [opOf_primsC prims _ h, idxPOf_primsC cs prims _ h]

end Data

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu
