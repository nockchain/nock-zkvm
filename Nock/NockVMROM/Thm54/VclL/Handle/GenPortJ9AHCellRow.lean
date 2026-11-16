/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCellRow.lean

-/
import Nock.V1J8.FillCell
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

theorem hdN'_eq : hdN' = Nock.NockVMROM.Thm54.VclL.hdN := by funext n; cases n <;> rfl
theorem tlN'_eq : tlN' = Nock.NockVMROM.Thm54.VclL.tlN := by funext n; cases n <;> rfl
theorem bigIdOf_eq (acsL : List Noun) : bigIdOf acsL = ComplJ8Data.bigIdOfP P acsL := by
  funext n; cases n <;> rfl

theorem idxD_eq' : ∀ (cs : List Noun) (n : Noun), idxD cs n = cs.idxOf n
  | [], _ => rfl
  | c :: cs, n => by
    by_cases h : c = n
    · subst h; simp [idxD]
    · simp [idxD, h, List.idxOf_cons, idxD_eq' cs n]

theorem idxOf_mem (cs : List Noun) (n : Noun) (h : n ∈ cs) : idxOf cs n = cs.idxOf n := by
  simp [idxOf, h, idxD_eq']

section
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

theorem toQ_zE (χe : CoinsE) : K6.toQ (zE χe) = ComplJ8Of.zJ deltaF (toχ χe) := rfl
theorem toQ_γVE (χe : CoinsE) : K6.toQ (γVE χe) = ComplJ8Of.γV deltaF (toχ χe) := rfl
theorem toQ_ρVE (χe : CoinsE) : K6.toQ (ρVE χe) = ComplJ8Of.ρV deltaF (toχ χe) := rfl

theorem toQ_encE (χe : CoinsE) (n : Noun) :
    (encE (zE χe) (yE χe) n).toQ = ComplJ8Of.encR deltaF (toχ χe) n := by
  rw [encE_spec]; rfl

theorem toQ_rkK (mu : ℕ) :
    K6.toQ (rkK mu) = Quad.mk _ (algebraMap (ZMod P) KC ((mu % 2 ^ 62 : ℕ) : ZMod P))
      (algebraMap (ZMod P) KC ((mu / 2 ^ 62 : ℕ) : ZMod P)) := by
  rw [rkK, toQ_mk, toK_g3, toK_g3, toZ_natG, toZ_natG]; rfl

/-! ## Handle bridge -/

theorem hdlB_kind (cs acsL : List Noun) (n : Noun) (hm : ∀ x y, n = .cell x y → n ∈ cs) :
    (((hdlB cs acsL n).1 : ℕ) : ZMod P) =
      ComplJ8Cell.wOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) n +
        ComplJ8Cell.kbOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) n := by
  rw [← bigIdOf_eq]
  cases n with
  | atom v =>
    by_cases hv : v < P
    · simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, bigIdOf, hv, Noun.isCell]
    · simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, bigIdOf, hv, Noun.isCell]
      norm_num
  | cell a b =>
    simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, bigIdOf, Noun.isCell]

theorem hdlB_val (cs acsL : List Noun) (n : Noun) (hm : ∀ x y, n = .cell x y → n ∈ cs) :
    (((hdlB cs acsL n).2 : ℕ) : ZMod P) =
      ComplJ8Cell.wOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) n *
          ComplJ8Cell.idOf (F := ZMod P) cs (ComplJ8Data.bigIdOfP P acsL) n +
        (1 - ComplJ8Cell.wOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) n) *
          ComplJ8Cell.aOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) n := by
  rw [← bigIdOf_eq]
  cases n with
  | atom v =>
    by_cases hv : v < P
    · simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.idOf, ComplJ8Cell.aOf, ComplJ8Cell.isBig, bigIdOf, hv,
        Noun.isCell]
    · simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.idOf, ComplJ8Cell.aOf, ComplJ8Cell.isBig, bigIdOf, hv,
        Noun.isCell]
  | cell a b =>
    have hmem := hm a b rfl
    simp [hdlB, ComplJ8Cell.wOf, ComplJ8Cell.idOf, ComplJ8Cell.aOf, ComplJ8Cell.isBig, bigIdOf,
      Noun.isCell, idxOf_mem cs _ hmem]

/-! ## Per-row bridges -/

noncomputable abbrev Rrow (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    CellVals (ZMod P) (Quad (algebraMap (ZMod P) KC deltaF)) :=
  ComplJ8Enc.cellRowBE deltaF (ComplJ8Of.encR deltaF (toχ χe)) (ComplJ8Of.zJ deltaF (toχ χe))
    (ComplJ8Data.bigIdOfP P acsL) cs (fun j => mv.getD j 0) (fun j => mx.getD j 0) (fun _ => 0) n j

abbrev dRow (χe : CoinsE) (cs acsL : List Noun) (n : Noun) (j : ℕ) : CellD :=
  cellDB (coOf χe) (yE χe) (hdlB cs acsL) (bigIdOf acsL) cs n j

theorem toQ_pE (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    (dRow χe cs acsL n j).pE.toQ = (Rrow χe cs acsL mv mx n j).p :=
  toQ_encE χe n

theorem toQ_lE (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    (dRow χe cs acsL n j).lE.toQ = (Rrow χe cs acsL mv mx n j).l := by
  have := toQ_encE χe (hdN' n)
  rw [hdN'_eq] at this
  exact this

theorem toQ_rE (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    (dRow χe cs acsL n j).rE.toQ = (Rrow χe cs acsL mv mx n j).r := by
  have := toQ_encE χe (tlN' n)
  rw [tlN'_eq] at this
  exact this

noncomputable abbrev Fi (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    CellVals (ZMod P) (Quad (algebraMap (ZMod P) KC deltaF)) :=
  cellFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (Rrow χe cs acsL mv mx n j)

theorem toQ_vInv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    K6.toQ (dRow χe cs acsL n j).vInv = (Fi χe cs acsL mv mx n j).vInv := by
  have hp := toQ_pE χe cs acsL mv mx n j
  show K6.toQ (compressE (coOf χe).γ (coOf χe).ρ _)⁻¹ = (FiniteIO.compress (m := 5) _ _)⁻¹
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact toQ_rkK _
  · exact toQ_lq j

theorem idL_eq (cs acsL : List Noun) (c : Noun) (hm : ∀ x y, c = .cell x y → c ∈ cs) :
    (((if c.isCell then idxOf cs c else (bigIdOf acsL c).getD 0 : ℕ)) : ZMod P) =
      ComplJ8Cell.idOf (F := ZMod P) cs (ComplJ8Data.bigIdOfP P acsL) c := by
  rw [← bigIdOf_eq]
  cases c with
  | atom v => simp [ComplJ8Cell.idOf, Noun.isCell]
  | cell a b => simp [ComplJ8Cell.idOf, Noun.isCell, idxOf_mem cs _ (hm a b rfl)]

theorem flag_w (acsL : List Noun) (c : Noun) :
    flag (c.isCell || (bigIdOf acsL c).isSome) =
      ComplJ8Cell.wOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) c := by
  rw [← bigIdOf_eq]
  cases c with
  | atom v => simp [flag, ComplJ8Cell.wOf, ComplJ8Cell.isBig, Noun.isCell]
  | cell a b => simp [flag, ComplJ8Cell.wOf, ComplJ8Cell.isBig, Noun.isCell, bigIdOf]

theorem flag_kb (acsL : List Noun) (c : Noun) :
    flag ((bigIdOf acsL c).isSome) =
      ComplJ8Cell.kbOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) c := by
  rw [← bigIdOf_eq]
  cases c with
  | atom v => simp [flag, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, Noun.isCell]
  | cell a b => simp [flag, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, Noun.isCell, bigIdOf]

theorem aV_eq (acsL : List Noun) (c : Noun) :
    (if (bigIdOf acsL c).isSome then (0 : ZMod P) else (atomV c : ZMod P)) =
      ComplJ8Cell.aOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) c := by
  rw [← bigIdOf_eq]
  cases c with
  | atom v => simp [ComplJ8Cell.aOf, ComplJ8Cell.isBig, Noun.isCell, atomV]
  | cell a b => simp [ComplJ8Cell.aOf, ComplJ8Cell.isBig, Noun.isCell, bigIdOf, atomV]

theorem childInv_eq (χe : CoinsE) (cs acsL : List Noun) (c : Noun) (hm : ∀ x y, c = .cell x y → c ∈ cs) :
    K6.toQ (if c.isCell || (bigIdOf acsL c).isSome then
        (compressE (coOf χe).γ (coOf χe).ρ ![(encE (zE χe) (yE χe) c).size, (encE (zE χe) (yE χe) c).dyck,
          (encE (zE χe) (yE χe) c).leaf, rkK c.internal,
          lq (if c.isCell then idxOf cs c else (bigIdOf acsL c).getD 0)])⁻¹ else 0) =
      liftQ (K := KC) deltaF (ComplJ8Cell.wOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) c) *
        (FiniteIO.compress (m := 5)
          (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
          ![(ComplJ8Of.encR deltaF (toχ χe) c).size, (ComplJ8Of.encR deltaF (toχ χe) c).dyck,
            (ComplJ8Of.encR deltaF (toχ χe) c).leaf,
            Quad.mk _ (algebraMap (ZMod P) KC ((c.internal % 2 ^ 62 : ℕ) : ZMod P))
              (algebraMap (ZMod P) KC ((c.internal / 2 ^ 62 : ℕ) : ZMod P)),
            liftQ (K := KC) deltaF (ComplJ8Cell.idOf (F := ZMod P) cs (ComplJ8Data.bigIdOfP P acsL) c)])⁻¹ := by
  have hw := flag_w acsL c
  have hid := idL_eq cs acsL c hm
  have he := toQ_encE χe c
  by_cases hc : (c.isCell || (bigIdOf acsL c).isSome) = true
  · rw [if_pos hc, ← hw, flag, if_pos hc]
    have h1 : liftQ (K := KC) deltaF (1 : ZMod P) = 1 := by rw [liftQ, map_one, map_one]
    rw [h1, one_mul, K6.toQ_inv, toQ_compressE]
    congr 2
    funext i
    fin_cases i
    · exact congrArg ComputeTable.FP.size he
    · exact congrArg ComputeTable.FP.dyck he
    · exact congrArg ComputeTable.FP.leaf he
    · exact toQ_rkK _
    · show K6.toQ (lq _) = _
      rw [toQ_lq, hid]
      rfl
  · rw [if_neg hc, ← hw, flag, if_neg hc]
    have h0 : liftQ (K := KC) deltaF (0 : ZMod P) = 0 := by rw [liftQ, map_zero, map_zero]
    rw [K6.toQ_zero, h0, zero_mul]

theorem children_mem (cs : List Noun) (hcl : ComplJ8Data.ClP cs []) (a b : Noun) (hn : Noun.cell a b ∈ cs) :
    (∀ x y, a = .cell x y → a ∈ cs) ∧ (∀ x y, b = .cell x y → b ∈ cs) :=
  hcl a b hn (List.not_mem_nil)

theorem toQ_lInv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) (hn : n ∈ cs)
    (hcs : ∀ c ∈ cs, c.isCell = true) (hcl : ComplJ8Data.ClP cs []) :
    K6.toQ (dRow χe cs acsL n j).lInv = (Fi χe cs acsL mv mx n j).lInv := by
  have h := hcs n hn
  cases n with
  | atom v => simp [Noun.isCell] at h
  | cell a b =>
    exact childInv_eq χe cs acsL a (children_mem cs hcl a b hn).1

theorem toQ_rInv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) (hn : n ∈ cs)
    (hcs : ∀ c ∈ cs, c.isCell = true) (hcl : ComplJ8Data.ClP cs []) :
    K6.toQ (dRow χe cs acsL n j).rInv = (Fi χe cs acsL mv mx n j).rInv := by
  have h := hcs n hn
  cases n with
  | atom v => simp [Noun.isCell] at h
  | cell a b =>
    exact childInv_eq χe cs acsL b (children_mem cs hcl a b hn).2

theorem toQ_xInv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j s : ℕ) :
    K6.toQ (compressE (coOf χe).γ (coOf χe).ρ
      ![(dRow χe cs acsL n j).pE.size, (dRow χe cs acsL n j).pE.dyck, (dRow χe cs acsL n j).pE.leaf,
        (dRow χe cs acsL n j).lE.size, (dRow χe cs acsL n j).lE.dyck, (dRow χe cs acsL n j).lE.leaf,
        (dRow χe cs acsL n j).rE.size, (dRow χe cs acsL n j).rE.dyck, (dRow χe cs acsL n j).rE.leaf,
        lq j, lq s])⁻¹ =
      (FiniteIO.compress (m := 11) (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (xKeyOf deltaF (Rrow χe cs acsL mv mx n j) (s : ZMod P)))⁻¹ := by
  have hp := toQ_pE χe cs acsL mv mx n j
  have hl := toQ_lE χe cs acsL mv mx n j
  have hr := toQ_rE χe cs acsL mv mx n j
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact toQ_lq j
  · exact toQ_lq s

theorem toQ_x0Inv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    K6.toQ (dRow χe cs acsL n j).x0Inv = (Fi χe cs acsL mv mx n j).x0Inv := by
  have := toQ_xInv χe cs acsL mv mx n j 0
  rw [Nat.cast_zero] at this
  exact this

theorem toQ_x1Inv (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    K6.toQ (dRow χe cs acsL n j).x1Inv = (Fi χe cs acsL mv mx n j).x1Inv := by
  have := toQ_xInv χe cs acsL mv mx n j 1
  rw [Nat.cast_one] at this
  exact this

theorem getD_rep (m j : ℕ) : (Array.replicate m 0).getD j 0 = 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split_ifs <;> rfl

theorem toQ_vTermD (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) (hn : n ∈ cs)
    (hcs : ∀ c ∈ cs, c.isCell = true) (hcl : ComplJ8Data.ClP cs []) :
    K6.toQ (vTermD mv (dRow χe cs acsL n j)) = vTermOf deltaF (Fi χe cs acsL mv mx n j) := by
  show K6.toQ (lq (mv.getD j 0) * (dRow χe cs acsL n j).vInv - (dRow χe cs acsL n j).lInv -
    (dRow χe cs acsL n j).rInv) = _
  rw [K6.toQ_sub, K6.toQ_sub, K6.toQ_mul, toQ_lq, toQ_vInv, toQ_lInv χe cs acsL mv mx n j hn hcs hcl,
    toQ_rInv χe cs acsL mv mx n j hn hcs hcl]
  rfl

theorem toQ_xTermD (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) (n : Noun) (j : ℕ) :
    K6.toQ (xTermD mx (Array.replicate cs.length 0) (dRow χe cs acsL n j)) =
      xTermOf deltaF (Fi χe cs acsL mv mx n j) := by
  show K6.toQ (lq (mx.getD j 0) * (dRow χe cs acsL n j).x0Inv +
    lq ((Array.replicate cs.length 0).getD j 0) * (dRow χe cs acsL n j).x1Inv) = _
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq, toQ_x0Inv, toQ_x1Inv, getD_rep]
  rfl

theorem rankBit_cast (mu k : ℕ) :
    (((Nock.V1J8.Gen.rankBit mu k : ℕ)) : ZMod P) =
      Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rankBit (F := ZMod P) mu k := by
  unfold Nock.V1J8.Gen.rankBit Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rankBit two62
  split_ifs <;> simp

theorem colDB_base (χe : CoinsE) (cs acsL : List Noun) (mv mx mh : Array ℕ) (n : Noun) (j : ℕ)
    (hn : n ∈ cs) (hcs : ∀ c ∈ cs, c.isCell = true) (hcl : ComplJ8Data.ClP cs [])
    (va xa ha : K6) (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    cellColDB (bigIdOf acsL) cs.length mv mx (Array.replicate cs.length 0) mh (dRow χe cs acsL n j)
        va xa ha c = (Rrow χe cs acsL mv mx n j).base c := by
  have h := hcs n hn
  cases n with
  | atom v => simp [Noun.isCell] at h
  | cell a b =>
  obtain ⟨ha', hb'⟩ := children_mem cs hcl a b hn
  have hL := idL_eq cs acsL a ha'
  have hR := idL_eq cs acsL b hb'
  have fL := flag_w acsL a
  have fR := flag_w acsL b
  have aL := aV_eq acsL a
  have aR := aV_eq acsL b
  have kL := flag_kb acsL a
  have kR := flag_kb acsL b
  unfold cellColDB
  simp only [dRow, cellDB, hdN', tlN']
  by_cases c5 : c = 5
  · subst c5; exact fL
  by_cases c6 : c = 6
  · subst c6; exact fR
  by_cases c7 : c = 7
  · subst c7; exact aL
  by_cases c8 : c = 8
  · subst c8; exact aR
  have n130 : c ≠ 130 := by omega
  have n131 : c ≠ 131 := by omega
  rw [if_neg c5, if_neg c6, if_neg c7, if_neg c8, if_neg n130, if_neg n131]
  unfold cellColD
  rw [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ 1 by omega), if_pos hc]
  unfold cellBaseD
  simp only [dRow, cellDB, hdN', tlN']
  rcases (show (2 ≤ c ∧ c < 18) ∨ c = 128 ∨ (18 ≤ c ∧ c < 128) by omega) with hr | hr | hr
  · obtain ⟨_, hr⟩ := hr
    interval_cases c
    · rfl
    · exact hL
    · exact hR
    · omega
    · omega
    · omega
    · omega
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · subst hr
    show (((Array.replicate cs.length 0).getD j 0 : ℕ) : ZMod P) = _
    rw [getD_rep]; rfl
  · obtain ⟨h18, h128⟩ := hr
    simp only [if_neg (show c ≠ 2 by omega), if_neg (show c ≠ 3 by omega), if_neg (show c ≠ 4 by omega),
      if_neg (show c ≠ 5 by omega), if_neg (show c ≠ 6 by omega), if_neg (show c ≠ 7 by omega),
      if_neg (show c ≠ 8 by omega), if_neg (show c ≠ 9 by omega), if_neg (show c ≠ 10 by omega),
      if_neg (show c ≠ 11 by omega), if_neg (show c ≠ 12 by omega), if_neg (show c ≠ 13 by omega),
      if_neg (show c ≠ 14 by omega), if_neg (show c ≠ 15 by omega), if_neg (show c ≠ 16 by omega),
      if_neg (show c ≠ 17 by omega), if_neg (show c ≠ 128 by omega), if_pos h128, CellVals.base]
    exact rankBit_cast _ _

theorem toQ_hTermD (χe : CoinsE) (cs acsL : List Noun) (mh : Array ℕ) (n : Noun) (j : ℕ) :
    K6.toQ (hTermD mh (dRow χe cs acsL n j)) =
      liftQ (K := KC) deltaF ((mh.getD j 0 : ℕ) : ZMod P) * K6.toQ (dRow χe cs acsL n j).ivH := by
  show K6.toQ (lq (mh.getD j 0) * (dRow χe cs acsL n j).ivH) = _
  rw [K6.toQ_mul, toQ_lq]

end

#print axioms hdN'_eq
#print axioms tlN'_eq
#print axioms bigIdOf_eq
#print axioms idxD_eq'
#print axioms idxOf_mem
#print axioms toQ_zE
#print axioms toQ_γVE
#print axioms toQ_ρVE
#print axioms toQ_encE
#print axioms toQ_rkK
#print axioms hdlB_kind
#print axioms hdlB_val
#print axioms toQ_pE
#print axioms toQ_lE
#print axioms toQ_rE
#print axioms toQ_vInv
#print axioms idL_eq
#print axioms flag_w
#print axioms flag_kb
#print axioms aV_eq
#print axioms childInv_eq
#print axioms children_mem
#print axioms toQ_lInv
#print axioms toQ_rInv
#print axioms toQ_xInv
#print axioms toQ_x0Inv
#print axioms toQ_x1Inv
#print axioms getD_rep
#print axioms toQ_vTermD
#print axioms toQ_xTermD
#print axioms rankBit_cast
#print axioms colDB_base
#print axioms toQ_hTermD

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
