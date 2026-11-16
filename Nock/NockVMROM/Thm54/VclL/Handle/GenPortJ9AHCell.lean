/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCell.lean

  Generic in `cs acsL mv mx mh` (child-closed list of cells), at ANY injective nodes / orbit / publics. Instantiation: `p := P`, `K := KC`, `δ := deltaF`, `b := powerBasis3`, `χ := toχ χe`. Does NOT import `GenPortJ9AChips` (the scan lemmas are copied, renamed). -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellKey

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-! ## 1. Generic list / scan lemmas -/

theorem scanK6_eq' (l : List K6) : Gen.scanK6 l = (List.scanl (· + ·) 0 l).tail := by
  have key : ∀ (l : List K6) (a : K6) (pre : List K6),
      (l.foldl (fun (st : List K6 × K6) x => (st.1 ++ [st.2 + x], st.2 + x)) (pre, a)).1 =
        pre ++ (List.scanl (· + ·) a l).tail := by
    intro l
    induction l with
    | nil => intro a pre; simp
    | cons x l ih =>
      intro a pre
      rw [List.foldl_cons, ih, List.scanl_cons, List.tail_cons]
      cases l <;> simp [List.scanl]
  unfold Gen.scanK6
  rw [key]; simp

theorem scanK6_length' (l : List K6) : (Gen.scanK6 l).length = l.length := by
  rw [scanK6_eq']; simp

theorem toQ_scanl_getD' : ∀ (l : List K6) (a : K6) (i : ℕ), i < l.length →
    K6.toQ ((List.scanl (· + ·) a l).getD (i + 1) 0) =
      K6.toQ a + ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0)
  | [], a, i, h => by simp at h
  | x :: t, a, 0, _ => by
    rw [List.scanl_cons, List.getD_cons_succ]
    cases t <;> simp [List.scanl_cons, K6.toQ_add]
  | x :: t, a, j + 1, h => by
    have ih := toQ_scanl_getD' t (a + x) j (by simpa using h)
    rw [List.scanl_cons, List.getD_cons_succ, ih, K6.toQ_add]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    abel

theorem toQ_scanK6_getD' (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((Gen.scanK6 l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [scanK6_eq']
  have := toQ_scanl_getD' l 0 i hi
  rw [K6.toQ_zero, zero_add] at this
  rw [← this]
  have e : ∀ L : List K6, L.tail.getD i 0 = L.getD (i + 1) 0 := by
    intro L; cases L <;> simp
  rw [e]

theorem toQ_lastK6 (l : List K6) (n : ℕ) (hn : n = l.length) (hn0 : 0 < n) (F : ℕ → KQ)
    (hF : ∀ j < n, K6.toQ (l.getD j 0) = F j) :
    K6.toQ (Gen.lastK6 (Gen.scanK6 l)) = ∑ j ∈ Finset.range n, F j := by
  have hlen : (Gen.scanK6 l).length = n := by rw [scanK6_length', hn]
  have hl : Gen.lastK6 (Gen.scanK6 l) = (Gen.scanK6 l).getD (n - 1) 0 := by
    unfold Gen.lastK6
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
    simp [List.getD_eq_getElem?_getD]
  rw [hl, toQ_scanK6_getD' l (n - 1) (by omega)]
  have : n - 1 + 1 = n := by omega
  rw [this]
  exact Finset.sum_congr rfl fun j hj => hF j (Finset.mem_range.mp hj)

/-! ## 2. The table, its size, its rows -/

/-- The executable row data of the table. -/
abbrev dsL (χe : CoinsE) (cs acsL : List Noun) : List CellD :=
  (cs.zipIdx 0).map fun (n, j) => cellDB (coOf χe) (yE χe) (hdlB cs acsL) (bigIdOf acsL) cs n j

theorem cellGenB_size (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun)
    (mv mx mx1 mh : Array ℕ) : (cellGenB k y H big cs mv mx mx1 mh).1.size = cs.length := by
  unfold cellGenB
  simp

theorem dsL_length (χe : CoinsE) (cs acsL : List Noun) : (dsL χe cs acsL).length = cs.length := by
  simp [dsL]

theorem dsB_getD (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun) (j : ℕ)
    (hj : j < cs.length) (d0 : CellD) :
    ((cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j).getD j d0 =
      cellDB k y H big cs (cs.getD j (.atom 0)) j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem map_getD_dsL (χe : CoinsE) (cs acsL : List Noun) (F : CellD → K6) (j : ℕ) (hj : j < cs.length) :
    ((dsL χe cs acsL).map F).getD j 0 = F (dRow χe cs acsL (cs.getD j (.atom 0)) j) := by
  have hj' : j < (dsL χe cs acsL).length := by rw [dsL_length]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj']
  simp only [Option.map_some, Option.getD_some]
  congr 1
  simp [dsL, dRow, List.getElem_map, List.getElem_zipIdx, List.getD_eq_getElem?_getD, hj]

theorem getD_mem (cs : List Noun) (j : ℕ) (hj : j < cs.length) : cs.getD j (.atom 0) ∈ cs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

/-! ## 3. Honest rows and the handle bridge -/

section Honest
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

/-- The honest filled rows at the executable data. -/
noncomputable abbrev VB (χe : CoinsE) (cs acsL : List Noun) (mv mx : Array ℕ) {n : ℕ} :
    Fin n → CellVals (ZMod P) (Quad (algebraMap (ZMod P) KC deltaF)) :=
  ComplJ8Enc.valsBE deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
    (ComplJ8Of.encR deltaF (toχ χe)) (ComplJ8Of.zJ deltaF (toχ χe)) (ComplJ8Data.bigIdOfP P acsL) cs
    (fun j => mv.getD j 0) (fun j => mx.getD j 0) (fun _ => 0)

/-- The handle multiplicities as base-field values. -/
abbrev mhv (mh : Array ℕ) {n : ℕ} : Fin n → ZMod P := fun i => ((mh.getD i 0 : ℕ) : ZMod P)

theorem ivH_eq (χe : CoinsE) (cs acsL : List Noun) (hcl : ComplJ8Data.ClP cs []) (mv mx : Array ℕ)
    (n : Noun) (hn : n ∈ cs) (hcs : ∀ c ∈ cs, c.isCell = true) (j : ℕ) :
    K6.toQ (dRow χe cs acsL n j).ivH =
      (FiniteIO.compress (⟨ComplJ8Bad.γH deltaF (toχ χe), ComplJ8Bad.ρH deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (BalanceQ.liftRec (K := KC) (fun c => algebraMap (ZMod P) KC
          (![(Rrow χe cs acsL mv mx n j).idx,
             (Rrow χe cs acsL mv mx n j).wL + ComplJ8Cell.kbOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) (hdN n),
             (Rrow χe cs acsL mv mx n j).wL * (Rrow χe cs acsL mv mx n j).idL +
               (1 - (Rrow χe cs acsL mv mx n j).wL) * (Rrow χe cs acsL mv mx n j).aL,
             (Rrow χe cs acsL mv mx n j).wR + ComplJ8Cell.kbOf (F := ZMod P) (ComplJ8Data.bigIdOfP P acsL) (tlN n),
             (Rrow χe cs acsL mv mx n j).wR * (Rrow χe cs acsL mv mx n j).idR +
               (1 - (Rrow χe cs acsL mv mx n j).wR) * (Rrow χe cs acsL mv mx n j).aR] c))))⁻¹ := by
  have h := hcs n hn
  cases n with
  | atom v => simp [Noun.isCell] at h
  | cell a b =>
  obtain ⟨ha', hb'⟩ := children_mem cs hcl a b hn
  have ka := hdlB_kind cs acsL a ha'
  have va := hdlB_val cs acsL a ha'
  have kb := hdlB_kind cs acsL b hb'
  have vb := hdlB_val cs acsL b hb'
  show K6.toQ (compressE (coOf χe).γH (coOf χe).ρH
    ![lq j, (Nock.V1J8.Gen.hK (hdlB cs acsL) a).1, (Nock.V1J8.Gen.hK (hdlB cs acsL) a).2,
      (Nock.V1J8.Gen.hK (hdlB cs acsL) b).1, (Nock.V1J8.Gen.hK (hdlB cs acsL) b).2])⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact toQ_lq j
  · show K6.toQ (lq _) = _
    rw [toQ_lq, ka]; rfl
  · show K6.toQ (lq _) = _
    rw [toQ_lq, va]; rfl
  · show K6.toQ (lq _) = _
    rw [toQ_lq, kb]; rfl
  · show K6.toQ (lq _) = _
    rw [toQ_lq, vb]; rfl

theorem ivW_eqB (χe : CoinsE) (cs acsL : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true)
    (hcl : ComplJ8Data.ClP cs []) (mv mx mh : Array ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n = cs.length)
    (nodes : Fin n → ZMod P) (hinj : Function.Injective nodes) {h : ℕ} (orbit : StrictOrbitDomain (ZMod P) 3 h)
    (pubs : ℕ → KC) (i : Fin n) :
    HonestKW.ivW deltaF powerBasis3 hn0 nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
        (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
        (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs) i =
      K6.toQ (dRow χe cs acsL (cs.getD i (.atom 0)) i).ivH := by
  have hi : (i : ℕ) < cs.length := hn ▸ i.2
  unfold HonestKW.ivW
  rw [GenPortJ9AHCellKey.dRowW_closed deltaF powerBasis3 hn0 nodes orbit (toχ χe) hinj pubs _ _ _ _ i,
    ivH_eq χe cs acsL hcl mv mx _ (getD_mem cs i hi) hcs i]
  rfl

theorem avW_eqB (χe : CoinsE) (cs acsL : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true)
    (hcl : ComplJ8Data.ClP cs []) (mv mx mh : Array ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n = cs.length)
    (nodes : Fin n → ZMod P) (hinj : Function.Injective nodes) {h : ℕ} (orbit : StrictOrbitDomain (ZMod P) 3 h)
    (pubs : ℕ → KC) (i : Fin n) :
    HonestKW.avW deltaF powerBasis3 hn0 nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
        (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
        (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs) i =
      K6.toQ ((scanK6 ((dsL χe cs acsL).map (hTermD mh))).getD i 0) := by
  have hi : (i : ℕ) < cs.length := hn ▸ i.2
  have hlen : (i : ℕ) < ((dsL χe cs acsL).map (hTermD mh)).length := by
    rw [List.length_map, dsL_length]; exact hi
  rw [toQ_scanK6_getD' _ _ hlen]
  unfold HonestKW.avW
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := by have := Finset.mem_range.mp hj; have := i.2; omega
  have hjc : j < cs.length := hn ▸ hj'
  rw [map_getD_dsL χe cs acsL _ j hjc, toQ_hTermD, CellTraceH.mN, dif_pos hj']
  have hd : (HonestKW.dNW deltaF powerBasis3 hn0 nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
        (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
        (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs) j)⁻¹ =
      K6.toQ (dRow χe cs acsL (cs.getD j (.atom 0)) j).ivH := by
    have := ivW_eqB χe cs acsL hcs hcl mv mx mh hn0 hn nodes hinj orbit pubs ⟨j, hj'⟩
    unfold HonestKW.ivW at this
    rw [HonestKW.dNW, dif_pos hj']
    exact this
  rw [hd]

theorem toQ_acc (χe : CoinsE) (cs acsL : List Noun) (F : CellD → K6) (G : ℕ → KQ)
    (hG : ∀ j < cs.length, K6.toQ (F (dRow χe cs acsL (cs.getD j (.atom 0)) j)) = G j)
    (i : ℕ) (hi : i < cs.length) :
    K6.toQ ((scanK6 ((dsL χe cs acsL).map F)).getD i 0) = ∑ j ∈ Finset.range (i + 1), G j := by
  have hlen : i < ((dsL χe cs acsL).map F).length := by rw [List.length_map, dsL_length]; exact hi
  rw [toQ_scanK6_getD' _ _ hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjc : j < cs.length := by have := Finset.mem_range.mp hj; omega
  rw [map_getD_dsL χe cs acsL F j hjc]
  exact hG j hjc

theorem qslot_eqB (χe : CoinsE) (cs acsL : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true)
    (hcl : ComplJ8Data.ClP cs []) (mv mx : Array ℕ) {n : ℕ} (hn : n = cs.length) (i : Fin n) (s : ℕ)
    (hs : s < 16) :
    K6.toQ (qslotD (dRow χe cs acsL (cs.getD i (.atom 0)) i)
        ((scanK6 ((dsL χe cs acsL).map (vTermD mv))).getD i 0)
        ((scanK6 ((dsL χe cs acsL).map (xTermD mx (Array.replicate cs.length 0)))).getD i 0) s) =
      (VB (n := n) χe cs acsL mv mx i).qslot s := by
  have hi : (i : ℕ) < cs.length := hn ▸ i.2
  have hmem := getD_mem cs i hi
  have hp := toQ_pE χe cs acsL mv mx (cs.getD i (.atom 0)) i
  have hl := toQ_lE χe cs acsL mv mx (cs.getD i (.atom 0)) i
  have hr := toQ_rE χe cs acsL mv mx (cs.getD i (.atom 0)) i
  interval_cases s
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact toQ_vInv χe cs acsL mv mx _ i
  · exact toQ_lInv χe cs acsL mv mx _ i hmem hcs hcl
  · exact toQ_rInv χe cs acsL mv mx _ i hmem hcs hcl
  · exact toQ_x0Inv χe cs acsL mv mx _ i
  · show K6.toQ ((scanK6 ((dsL χe cs acsL).map (vTermD mv))).getD i 0) = _
    refine (toQ_acc χe cs acsL (vTermD mv)
      (fun j => vTermOf deltaF (Fi χe cs acsL mv mx (cs.getD j (.atom 0)) j))
      (fun j hj => toQ_vTermD χe cs acsL mv mx _ j (getD_mem cs j hj) hcs hcl) i hi).trans ?_
    rfl
  · show K6.toQ ((scanK6 ((dsL χe cs acsL).map (xTermD mx (Array.replicate cs.length 0)))).getD i 0) = _
    refine (toQ_acc χe cs acsL (xTermD mx (Array.replicate cs.length 0))
      (fun j => xTermOf deltaF (Fi χe cs acsL mv mx (cs.getD j (.atom 0)) j))
      (fun j hj => toQ_xTermD χe cs acsL mv mx _ j) i hi).trans ?_
    rfl
  · exact toQ_x1Inv χe cs acsL mv mx _ i

end Honest

section Cols
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

theorem cell_split (cs : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true) (i : ℕ) (hi : i < cs.length) :
    ∃ a b, cs.getD i (.atom 0) = .cell a b := by
  have h := hcs _ (getD_mem cs i hi)
  generalize cs.getD i (.atom 0) = m at h
  cases m with
  | atom v => simp [Noun.isCell] at h
  | cell a b => exact ⟨a, b, rfl⟩

end Cols

theorem cellGenB_get (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun)
    (mv mx mx1 mh : Array ℕ) (i c : ℕ) (hi : i < cs.length) (hc : c < 242) :
    ((cellGenB k y H big cs mv mx mx1 mh).1.getD i #[]).getD c 0 =
      cellColDB big cs.length mv mx mx1 mh
        (((cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j).getD i (cellDB k y H big cs (.atom 0) i))
        ((scanK6 (((cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j).map (vTermD mv))).getD i 0)
        ((scanK6 (((cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j).map (xTermD mx mx1))).getD i 0)
        ((scanK6 (((cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j).map (hTermD mh))).getD i 0) c := by
  unfold cellGenB
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some, Array.getElem?_ofFn, dif_pos hc]

section LHS

/-- resolve the `if` ladders of `cellColDB`/`cellColD` one at a time (`split_ifs` blows up on `ZMod P` data). -/
macro "ifres" : tactic =>
  `(tactic| (dsimp only
             repeat (first | rw [if_pos (by omega)] | rw [if_neg (by omega)])
             try rfl))

macro_rules
  | `(tactic| split_ifs <;> first | omega | rfl) => `(tactic| ifres)

theorem cellColDB_129 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) :
    cellColDB big D mv mx mx1 mh d va xa ha 129 = (mh.getD d.j 0 : ZMod P) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_130 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) :
    cellColDB big D mv mx mx1 mh d va xa ha 130 = flag (big d.l).isSome := by
  unfold cellColDB
  split_ifs <;> first | omega | rfl

theorem cellColDB_131 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) :
    cellColDB big D mv mx mx1 mh d va xa ha 131 = flag (big d.r).isSome := by
  unfold cellColDB
  split_ifs <;> first | omega | rfl

theorem cellColDB_132 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) :
    cellColDB big D mv mx mx1 mh d va xa ha 132 = ((d.muL % two62 + d.muL / two62 : ℕ) : ZMod P)⁻¹ := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_133 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) :
    cellColDB big D mv mx mx1 mh d va xa ha 133 = ((d.muR % two62 + d.muR / two62 : ℕ) : ZMod P)⁻¹ := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_role (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6)
    (c : ℕ) (h1 : 134 ≤ c) (h2 : c < 230) :
    cellColDB big D mv mx mx1 mh d va xa ha c =
      limbZ (if ((c - 134) / 3) % 2 = 0 then (qslotD d va xa (((c - 134) / 3) / 2)).re
        else (qslotD d va xa (((c - 134) / 3) / 2)).im) ((c - 134) % 3) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_ivre (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6)
    (c : ℕ) (h1 : 230 ≤ c) (h2 : c < 233) :
    cellColDB big D mv mx mx1 mh d va xa ha c = limbZ d.ivH.re (c - 230) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_ivim (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6)
    (c : ℕ) (h1 : 233 ≤ c) (h2 : c < 236) :
    cellColDB big D mv mx mx1 mh d va xa ha c = limbZ d.ivH.im (c - 233) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_avre (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6)
    (c : ℕ) (h1 : 236 ≤ c) (h2 : c < 239) :
    cellColDB big D mv mx mx1 mh d va xa ha c = limbZ ha.re (c - 236) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

theorem cellColDB_avim (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6)
    (c : ℕ) (h1 : 239 ≤ c) :
    cellColDB big D mv mx mx1 mh d va xa ha c = limbZ ha.im (c - 239) := by
  unfold cellColDB cellColD
  split_ifs <;> first | omega | rfl

end LHS

section Main
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

theorem cellGenB_cols (χe : CoinsE) (cs acsL : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true)
    (hcl : ComplJ8Data.ClP cs []) (mv mx mh : Array ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n = cs.length)
    (nodes : Fin n → ZMod P) (hinj : Function.Injective nodes) {h : ℕ} (orbit : StrictOrbitDomain (ZMod P) 3 h)
    (pubs : ℕ → KC) (i : Fin n) (c : ℕ) (hc : c < 242) :
    ((cellGenB (coOf χe) (yE χe) (hdlB cs acsL) (bigIdOf acsL) cs mv mx (Array.replicate cs.length 0) mh).1.getD i
        #[]).getD c 0 =
      fullCol hn0 (HonestKW.colW deltaF powerBasis3 (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
        (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs)
        (HonestKW.ivW deltaF powerBasis3 hn0 nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
          (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
          (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs))
        (HonestKW.avW deltaF powerBasis3 hn0 nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
          (cellCol deltaF powerBasis3 (VB χe cs acsL mv mx)) (mhv mh)
          (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P acsL) cs) (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P acsL) cs)))
        c i := by
  have hi : (i : ℕ) < cs.length := hn ▸ i.2
  have hmem := getD_mem cs i hi
  have hiv := ivW_eqB χe cs acsL hcs hcl mv mx mh hn0 hn nodes hinj orbit pubs i
  have hav := avW_eqB χe cs acsL hcs hcl mv mx mh hn0 hn nodes hinj orbit pubs i
  rw [cellGenB_get _ _ _ _ _ _ _ _ _ _ _ hi hc, dsB_getD _ _ _ _ cs i hi]
  obtain ⟨a, b, hab⟩ := cell_split cs hcs i hi
  by_cases h0 : c = 0
  · subst h0
    simp [cellColDB, cellColD, fullCol, flag, dRow, cellDB]
  by_cases h1 : c = 1
  · subst h1
    have e : ((i : ℕ) + 1 = cs.length) ↔ (i = ⟨n - 1, Nat.sub_lt hn0 (by omega)⟩) := by
      rw [Fin.ext_iff]; simp only; omega
    simp only [cellColDB, cellColD, fullCol, flag, dRow, cellDB]
    simp [e]
  simp only [fullCol, if_neg h0, if_neg h1, HonestKW.colW, extColF, CellTraceH.cellTemplate_width]
  by_cases hb : c < 129
  · rw [if_pos hb]
    simp only [cellCol, if_pos hb]
    exact colDB_base χe cs acsL mv mx mh _ i hmem hcs hcl _ _ _ c (by omega) hb
  rw [if_neg hb]
  by_cases h129 : c = 129
  · subst h129
    rw [cellColDB_129]
    simp [HonestKW.newW, dRow, cellDB, mhv]
  by_cases hk : c < 134
  · rw [if_pos hk]
    have e11 : (VB (n := n) χe cs acsL mv mx i).base 11 = (((a.internal % two62 : ℕ)) : ZMod P) := by
      show (Rrow χe cs acsL mv mx (cs.getD i (.atom 0)) i).base 11 = _
      rw [hab]; rfl
    have e12 : (VB (n := n) χe cs acsL mv mx i).base 12 = (((a.internal / two62 : ℕ)) : ZMod P) := by
      show (Rrow χe cs acsL mv mx (cs.getD i (.atom 0)) i).base 12 = _
      rw [hab]; rfl
    have e13 : (VB (n := n) χe cs acsL mv mx i).base 13 = (((b.internal % two62 : ℕ)) : ZMod P) := by
      show (Rrow χe cs acsL mv mx (cs.getD i (.atom 0)) i).base 13 = _
      rw [hab]; rfl
    have e14 : (VB (n := n) χe cs acsL mv mx i).base 14 = (((b.internal / two62 : ℕ)) : ZMod P) := by
      show (Rrow χe cs acsL mv mx (cs.getD i (.atom 0)) i).base 14 = _
      rw [hab]; rfl
    rcases (show c = 130 ∨ c = 131 ∨ c = 132 ∨ c = 133 by omega) with rfl | rfl | rfl | rfl
    · rw [cellColDB_130]
      simp only [HonestKW.newW, CellTwinK.kbL, if_neg (show (130 : ℕ) ≠ 129 by norm_num), if_true]
      show flag _ = ComplJ8Cell.kbOf _ (hdN (cs.getD i (.atom 0)))
      rw [hab]
      exact flag_kb acsL a
    · rw [cellColDB_131]
      simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, if_neg (show (131 : ℕ) ≠ 129 by norm_num),
        if_neg (show (131 : ℕ) ≠ 130 by norm_num), if_true]
      show flag _ = ComplJ8Cell.kbOf _ (tlN (cs.getD i (.atom 0)))
      rw [hab]
      exact flag_kb acsL b
    · rw [cellColDB_132]
      simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, Cell.loL, Cell.hiL,
        if_neg (show (132 : ℕ) ≠ 129 by norm_num), if_neg (show (132 : ℕ) ≠ 130 by norm_num),
        if_neg (show (132 : ℕ) ≠ 131 by norm_num), if_true]
      simp only [cellCol, if_pos (show (11 : ℕ) < 129 by norm_num), if_pos (show (12 : ℕ) < 129 by norm_num),
        e11, e12, ← Nat.cast_add]
      rw [hab]
      rfl
    · rw [cellColDB_133]
      simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, CellTwinK.invR, Cell.loR, Cell.hiR,
        if_neg (show (133 : ℕ) ≠ 129 by norm_num), if_neg (show (133 : ℕ) ≠ 130 by norm_num),
        if_neg (show (133 : ℕ) ≠ 131 by norm_num), if_neg (show (133 : ℕ) ≠ 132 by norm_num), if_true]
      simp only [cellCol, if_pos (show (13 : ℕ) < 129 by norm_num), if_pos (show (14 : ℕ) < 129 by norm_num),
        e13, e14, ← Nat.cast_add]
      rw [hab]
      rfl
  rw [if_neg hk]
  by_cases hr : c < 230
  · rw [if_pos (show c < 225 + (134 - 129) by omega), cellColDB_role _ _ _ _ _ _ _ _ _ _ c (by omega) hr]
    simp only [cellCol, if_neg (show ¬ (c - (134 - 129) < 129) by omega)]
    have e1 : c - (134 - 129) - 129 = c - 134 := by omega
    simp only [e1]
    unfold roleVal
    rw [← qslot_eqB χe cs acsL hcs hcl mv mx hn i _ (show ((c - 134) / 3) / 2 < 16 by omega)]
    split_ifs
    · rw [re_toQ, coord_K]
    · rw [im_toQ, coord_K]
  rw [if_neg (show ¬ c < 225 + (134 - 129) by omega)]
  simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, CellTwinK.invR,
    if_neg (show c ≠ 129 by omega), if_neg (show c ≠ 130 by omega), if_neg (show c ≠ 131 by omega),
    if_neg (show c ≠ 132 by omega), if_neg (show c ≠ 133 by omega)]
  rw [hiv, hav]
  by_cases a1 : c < 233
  · rw [cellColDB_ivre _ _ _ _ _ _ _ _ _ _ c (by omega) a1, if_pos ⟨by omega, a1⟩, coordN_toQ_re,
      Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg (show ¬ (230 ≤ c ∧ c < 233) by omega)]
  by_cases a2 : c < 236
  · rw [cellColDB_ivim _ _ _ _ _ _ _ _ _ _ c (by omega) a2, if_pos ⟨by omega, a2⟩, coordN_toQ_im,
      Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg (show ¬ (233 ≤ c ∧ c < 236) by omega)]
  by_cases a3 : c < 239
  · rw [cellColDB_avre _ _ _ _ _ _ _ _ _ _ c (by omega) a3, if_pos ⟨by omega, a3⟩, coordN_toQ_re,
      Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg (show ¬ (236 ≤ c ∧ c < 239) by omega), cellColDB_avim _ _ _ _ _ _ _ _ _ _ c (by omega),
    if_pos ⟨by omega, hc⟩, coordN_toQ_im, Nat.mod_eq_of_lt (by omega)]
  <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]

end Main

/-! ## 5. The publics -/

section Pubs
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem cRows_eq (χe : CoinsE) (D : ComplJ8Data.J8Data P Rg fuel s f r) (mv mx : Array ℕ)
    (hDv : D.mv = mv) (hDx : D.mx = mx) (j : ℕ) :
    ComplJ8Of.cRows deltaF D (toχ χe) j = Rrow χe D.cells D.acs mv mx (D.cells.getD j (.atom 0)) j := by
  subst hDv hDx
  rfl

theorem cellGenB_pubs (χe : CoinsE) (cs acsL : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true)
    (hcl : ComplJ8Data.ClP cs []) (mv mx mh : Array ℕ)
    (D : ComplJ8Data.J8Data P Rg fuel s f r) (hDc : D.cells = cs) (hDa : D.acs = acsL) (hDv : D.mv = mv)
    (hDx : D.mx = mx) (hDh : D.mh = mh) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.cells.length)) (j : ℕ) :
    K3.toK ((cellGenB (coOf χe) (yE χe) (hdlB cs acsL) (bigIdOf acsL) cs mv mx (Array.replicate cs.length 0) mh).2 j) =
      ComplJ8Of.pubsCOf deltaF powerBasis3 D hC o (toχ χe) j := by
  subst hDc hDa hDv hDx hDh
  have hmem : ∀ k < D.cells.length, D.cells.getD k (.atom 0) ∈ D.cells := fun k hk => getD_mem _ k hk
  have hV : K6.toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (vTermD D.mv)))) =
      ComplJ8Of.cvT deltaF D (toχ χe) := by
    rw [toQ_lastK6 _ D.cells.length (by simp [dsL_length]) hC
      (fun k => vTermOf deltaF (cellFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (ComplJ8Of.cRows deltaF D (toχ χe) k)))]
    · rfl
    · intro k hk
      rw [map_getD_dsL χe D.cells D.acs _ k hk, toQ_vTermD χe D.cells D.acs D.mv D.mx _ k (hmem k hk) hcs hcl,
        cRows_eq χe D D.mv D.mx rfl rfl k]
  have hX : K6.toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (xTermD D.mx (Array.replicate D.cells.length 0))))) =
      ComplJ8Of.cxT deltaF D (toχ χe) := by
    rw [toQ_lastK6 _ D.cells.length (by simp [dsL_length]) hC
      (fun k => xTermOf deltaF (cellFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (ComplJ8Of.cRows deltaF D (toχ χe) k)))]
    · rfl
    · intro k hk
      rw [map_getD_dsL χe D.cells D.acs _ k hk, toQ_xTermD χe D.cells D.acs D.mv D.mx _ k,
        cRows_eq χe D D.mv D.mx rfl rfl k]
  have hH : K6.toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (hTermD D.mh)))) =
      ComplJ8Of.chT deltaF powerBasis3 D hC o (toχ χe) := by
    unfold ComplJ8Of.chT
    rw [toQ_lastK6 _ D.cells.length (by simp [dsL_length]) hC
      (fun k => liftQ (K := KC) deltaF (CellTraceH.mN (fun i : Fin D.cells.length => (ComplJ8Of.mhF D i : ZMod P)) k) *
        (HonestKW.dNW deltaF powerBasis3 hC (ComplJ8Of.powN o _) o (chalsMJ8 deltaF (toχ χe))
          (ComplJ8Of.pubsC0 deltaF D (toχ χe)) (ComplJ8Of.cCol deltaF powerBasis3 D (toχ χe))
          (fun i : Fin D.cells.length => (ComplJ8Of.mhF D i : ZMod P)) (ComplJ8Cell.kbLB (ComplJ8Of.bigOf D) D.cells)
          (ComplJ8Cell.kbRB (ComplJ8Of.bigOf D) D.cells) k)⁻¹)]
    intro k hk
    have hk' : k < D.cells.length := hk
    rw [map_getD_dsL χe D.cells D.acs _ k hk, toQ_hTermD, CellTraceH.mN, dif_pos hk']
    have := ivW_eqB χe D.cells D.acs hcs hcl D.mv D.mx D.mh hC rfl (ComplJ8Of.powN o D.cells.length) hinj o
      (ComplJ8Of.pubsC0 deltaF D (toχ χe)) ⟨k, hk'⟩
    unfold HonestKW.ivW at this
    rw [HonestKW.dNW, dif_pos hk']
    rw [this]
  have hVre := (re_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (vTermD D.mv))))).symm.trans
    (congrArg (Quad.re _) hV)
  have hVim := (im_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (vTermD D.mv))))).symm.trans
    (congrArg (Quad.im _) hV)
  have hXre := (re_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (xTermD D.mx (Array.replicate D.cells.length 0)))))).symm.trans
    (congrArg (Quad.re _) hX)
  have hXim := (im_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (xTermD D.mx (Array.replicate D.cells.length 0)))))).symm.trans
    (congrArg (Quad.im _) hX)
  have hHre := (re_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (hTermD D.mh))))).symm.trans
    (congrArg (Quad.re _) hH)
  have hHim := (im_toQ (Gen.lastK6 (scanK6 ((dsL χe D.cells D.acs).map (hTermD D.mh))))).symm.trans
    (congrArg (Quad.im _) hH)
  unfold cellGenB
  dsimp only
  unfold ComplJ8Of.pubsCOf ComplJ8Of.pubsC0 ComplJ8Of.pub2
  by_cases h0 : j = 0
  · subst h0; simp only [Nat.reduceLT, Nat.reduceMod, ↓reduceIte]; exact hVre
  by_cases h1 : j = 1
  · subst h1; simp only [Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; exact hVim
  by_cases h2 : j = 2
  · subst h2; simp only [Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; exact hXre
  by_cases h3 : j = 3
  · subst h3; simp only [Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; exact hXim
  by_cases h4 : j = 4
  · subst h4; simp only [Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; exact hHre
  by_cases h5 : j = 5
  · subst h5; simp only [Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]; exact hHim
  · have n4 : ¬ j < 4 := by omega
    have n6 : ¬ j < 6 := by omega
    simp only [h0, h1, h2, h3, h4, h5, n4, n6, if_false]
    exact K3.toK_zero

theorem interp_cast {F : Type*} [Field F] {m n : ℕ} (e : m = n) (nodes v : Fin m → F) :
    Lagrange.interpolate (Finset.univ : Finset (Fin m)) nodes v =
      Lagrange.interpolate (Finset.univ : Finset (Fin n)) (nodes ∘ Fin.cast e.symm) (v ∘ Fin.cast e.symm) := by
  subst e
  rfl

end Pubs

#print axioms cellGenB_size
#print axioms dsB_getD
#print axioms ivW_eqB
#print axioms avW_eqB
#print axioms qslot_eqB
#print axioms cellGenB_cols
#print axioms cellGenB_pubs
#print axioms interp_cast

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
