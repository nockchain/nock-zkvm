/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkRow.lean

-/
import Nock.V1J8.FillCell
import Nock.V1J8.FillWalk
import Nock.V1J8.GenAtom
import Nock.V1J8.CheckJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRow

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk

theorem hdN'_eq : hdN' = Nock.NockVMROM.Thm54.VclL.hdN := by funext n; cases n <;> rfl
theorem tlN'_eq : tlN' = Nock.NockVMROM.Thm54.VclL.tlN := by funext n; cases n <;> rfl

theorem idxD_eq' : ∀ (cs : List Noun) (n : Noun), idxD cs n = cs.idxOf n
  | [], _ => rfl
  | c :: cs, n => by
    by_cases h : c = n
    · subst h; simp [idxD]
    · simp [idxD, h, List.idxOf_cons, idxD_eq' cs n]

theorem idxOf_mem (cs : List Noun) (n : Noun) (h : n ∈ cs) : idxOf cs n = cs.idxOf n := by
  simp [idxOf, h, idxD_eq']

/-- `idxN cs n = cs.idxOf n` on members and (with all of `cs` cells) on atoms. -/
theorem idxN_eq (cs : List Noun) (hcs : ∀ c ∈ cs, c.isCell = true) (n : Noun)
    (h : n ∈ cs ∨ n.isCell = false) : idxN cs n = cs.idxOf n := by
  cases n with
  | cell a b =>
    rcases h with h | h
    · exact idxOf_mem cs _ h
    · simp [Noun.isCell] at h
  | atom v =>
    have hn : Noun.atom v ∉ cs := fun hm => by have := hcs _ hm; simp [Noun.isCell] at this
    show cs.length = cs.idxOf (Noun.atom v)
    exact (List.idxOf_eq_length hn).symm

/-- The trie node's executable walk row. -/
def wrowOf (t : Walk.NTree WN) : Nock.V1J8.Gen.WRow :=
  ⟨t.label.node, t.label.root, VclL.axisFold t.label.bits, t.label.bits.length, t.label.cL, t.label.cR,
    t.label.mL, t.label.mR⟩

theorem foW_wrowOf (t : Walk.NTree WN) (ht : ∃ root n bs T, t = GenWalk.trie root n bs T) :
    foW (wrowOf t) = t.children.length := by
  obtain ⟨root, n, bs, T, rfl⟩ := ht
  rw [trie_fanout]
  rfl

theorem toK_chals (χe : CoinsE) (i : ℕ) :
    K3.toK (chalsMJ8E χe i) = VerJ8.chalsMJ8 deltaF (toχ χe) i := chalsMJ8E_spec χe i

section
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]

theorem toQ_encE (χe : CoinsE) (n : Noun) :
    (encE (zE χe) (yE χe) n).toQ = ComplJ8Of.encR deltaF (toχ χe) n := by
  rw [encE_spec]; rfl

variable (χe : CoinsE) (H : Noun → ℕ × ℕ) (cs : List Noun) (reads : List (Noun × ℕ)) (j : ℕ)

/-- The executable walk row data at the honest trie row `j`. -/
abbrev dW (χe : CoinsE) (H : Noun → ℕ × ℕ) (cs : List Noun) (reads : List (Noun × ℕ)) (j : ℕ) : WalkD :=
  walkDB (coOf χe) (yE χe) H (idxN cs) cs (wrowOf (wTrie cs reads j)) j

theorem toQ_wpE : (dW χe H cs reads j).pE.toQ =
    ComplJ8Of.encR deltaF (toχ χe) (wTrie cs reads j).label.node := toQ_encE χe _

theorem toQ_wlE : (dW χe H cs reads j).lE.toQ =
    ComplJ8Of.encR deltaF (toχ χe) (VclL.hdN (wTrie cs reads j).label.node) := by
  have := toQ_encE χe (hdN' (wTrie cs reads j).label.node)
  rw [hdN'_eq] at this
  exact this

theorem toQ_wrE : (dW χe H cs reads j).rE.toQ =
    ComplJ8Of.encR deltaF (toχ χe) (VclL.tlN (wTrie cs reads j).label.node) := by
  have := toQ_encE χe (tlN' (wTrie cs reads j).label.node)
  rw [tlN'_eq] at this
  exact this

theorem toQ_rootE : (dW χe H cs reads j).rootE.toQ =
    ComplJ8Of.encR deltaF (toχ χe) (wTrie cs reads j).label.root := toQ_encE χe _

variable (hcs : ∀ c ∈ cs, c.isCell = true)
include hcs

theorem walkDB_idx (hm : (wTrie cs reads j).label.node ∈ cs ∨ (wTrie cs reads j).label.node.isCell = false) :
    (dW χe H cs reads j).idx = cs.idxOf (wTrie cs reads j).label.node := by
  show wIdx (idxN cs) cs (wrowOf (wTrie cs reads j)) = _
  unfold wIdx
  split_ifs
  · exact idxN_eq cs hcs _ hm
  · exact idxN_eq cs hcs _ hm

theorem walkDB_ridx (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    (dW χe H cs reads j).ridx = cs.idxOf (wTrie cs reads j).label.root :=
  idxN_eq cs hcs _ hm

omit hcs in
theorem dW_w : (dW χe H cs reads j).w = wrowOf (wTrie cs reads j) := rfl

/-- The honest row values at trie row `j`. -/
noncomputable abbrev rowW (α γ : KC) : WalkVals (ZMod P) KC (Quad (algebraMap (ZMod P) KC deltaF)) :=
  ComplJ8Enc.walkRow0E deltaF (ComplJ8Of.encR deltaF (toχ χe)) cs reads α γ j

omit hcs in
theorem algQ (x : ZMod P) : algebraMap (ZMod P) (Quad (algebraMap (ZMod P) KC deltaF)) x =
    liftQ (K := KC) deltaF x := IsScalarTower.algebraMap_apply (ZMod P) KC _ x

omit hcs in
theorem algQ' (x : ZMod P) : algebraMap (ZMod P) (Quad ((AdjoinRoot.of cubicPoly) deltaF)) x =
    liftQ (K := KC) deltaF x := by
  first | exact IsScalarTower.algebraMap_apply (ZMod P) KC _ x | rfl | (simp only [liftQ]; rfl)

omit hcs in
theorem comb5 {R : Type*} [CommRing R] (ρ a b c d e : R) :
    ρ + (a + b + c + d + e) = ρ + (0 + a + b + c + d + e) := by
  rw [zero_add]

omit hcs in
theorem comb4 {R : Type*} [CommRing R] (ρ a b c d : R) :
    ρ + (a + b + c + d) = ρ + (0 + a + b + c + d) := by
  rw [zero_add]

omit hcs in
theorem hγQ(χe : CoinsE) : K6.toQ (γHE χe) = ComplJ8Bad.γH deltaF (toχ χe) := rfl
omit hcs in
theorem hρQ (χe : CoinsE) : K6.toQ (ρHE χe) = ComplJ8Bad.ρH deltaF (toχ χe) := rfl

theorem toQ_xInv (α γ : KC) (hm : (wTrie cs reads j).label.node ∈ cs ∨ (wTrie cs reads j).label.node.isCell = false) :
    K6.toQ (dW χe H cs reads j).xInv =
      (FiniteIO.compress (m := 11)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wxKeyV deltaF (rowW χe cs reads j α γ)))⁻¹ := by
  have hp := toQ_wpE χe H cs reads j
  have hl := toQ_wlE χe H cs reads j
  have hr := toQ_wrE χe H cs reads j
  have hi : liftQ (K := KC) deltaF (((dW χe H cs reads j).idx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe cs reads j α γ).idx := by
    rw [walkDB_idx χe H cs reads j hcs hm]; rfl
  show K6.toQ (compressE (coOf χe).γ (coOf χe).ρ _)⁻¹ = _
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
  · exact (toQ_lq _).trans hi
  · exact (toQ_lq 0).trans (by rw [Nat.cast_zero]; rfl)

theorem toQ_pInvL (α γ : KC) (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K6.toQ (dW χe H cs reads j).pInvL =
      (FiniteIO.compress (m := 8)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wrecLV deltaF (rowW χe cs reads j α γ)))⁻¹ := by
  have hq := toQ_rootE χe H cs reads j
  have hl := toQ_wlE χe H cs reads j
  have hi : liftQ (K := KC) deltaF (((dW χe H cs reads j).ridx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe cs reads j α γ).ridx := by
    rw [walkDB_ridx χe H cs reads j hcs hm]; rfl
  have hpre : liftQ (K := KC) deltaF ((2 * (dW χe H cs reads j).w.pre : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (2 * (rowW χe cs reads j α γ).pre) := by
    push_cast; rfl
  show K6.toQ (compressE (coOf χe).γ (coOf χe).ρ _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hq
  · exact congrArg ComputeTable.FP.dyck hq
  · exact congrArg ComputeTable.FP.leaf hq
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact (toQ_lq _).trans hpre
  · exact (toQ_lq _).trans hi

theorem toQ_pInvR (α γ : KC) (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K6.toQ (dW χe H cs reads j).pInvR =
      (FiniteIO.compress (m := 8)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wrecRV deltaF (rowW χe cs reads j α γ)))⁻¹ := by
  have hq := toQ_rootE χe H cs reads j
  have hr := toQ_wrE χe H cs reads j
  have hi : liftQ (K := KC) deltaF (((dW χe H cs reads j).ridx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe cs reads j α γ).ridx := by
    rw [walkDB_ridx χe H cs reads j hcs hm]; rfl
  have hpre : liftQ (K := KC) deltaF ((2 * (dW χe H cs reads j).w.pre + 1 : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (2 * (rowW χe cs reads j α γ).pre + 1) := by
    push_cast; rfl
  show K6.toQ (compressE (coOf χe).γ (coOf χe).ρ _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hq
  · exact congrArg ComputeTable.FP.dyck hq
  · exact congrArg ComputeTable.FP.leaf hq
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact (toQ_lq _).trans hpre
  · exact (toQ_lq _).trans hi

/-- The handle denominators at the exec side are `ρH + recDen`/`recDenP` (card: `toQ_hXi/hPLi/hPRi`). -/
theorem toQ_hXi (hm : (wTrie cs reads j).label.node ∈ cs ∨ (wTrie cs reads j).label.node.isCell = false) :
    K6.toQ (dW χe H cs reads j).hXi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDen 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((cs.idxOf (wTrie cs reads j).label.node : ℕ) : ZMod P),
          ((((H (VclL.hdN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P),
            (((H (VclL.hdN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P)),
          ((((H (VclL.tlN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P),
            (((H (VclL.tlN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P))))⁻¹ := by
  have hidx := walkDB_idx χe H cs reads j hcs hm
  show K6.toQ (compressE (coOf χe).γH (coOf χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hidx' : wIdx (idxN cs) cs (wrowOf (wTrie cs reads j)) = cs.idxOf (wTrie cs reads j).label.node := hidx
  congr 1
  rw [← hidx]
  simp [FiniteIO.compress, Walk.rlc, recDen, Fin.sum_univ_five, toQ_lq, algQ, hdN'_eq, tlN'_eq, Gen.hK,
    wrowOf, coOf, hγQ, hρQ, algQ']
  first
    | (rw [zero_add]; rfl)
    | (rw [zero_add]; simp only [algQ']; rfl)
    | (rw [zero_add]; simp only [algQ])
    | exact comb5 (R := Quad ((AdjoinRoot.of cubicPoly) deltaF)) _ _ _ _ _ _
    | exact comb4 (R := Quad ((AdjoinRoot.of cubicPoly) deltaF)) _ _ _ _ _

theorem toQ_hPLi (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K6.toQ (dW χe H cs reads j).hPLi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDenP 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((cs.idxOf (wTrie cs reads j).label.root : ℕ) : ZMod P),
          (2 * ((VclL.axisFold (wTrie cs reads j).label.bits : ℕ) : ZMod P)),
          ((((H (VclL.hdN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P),
            (((H (VclL.hdN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P))))⁻¹ := by
  have hridx := walkDB_ridx χe H cs reads j hcs hm
  show K6.toQ (compressE (coOf χe).γH (coOf χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hridx' : idxN cs (wTrie cs reads j).label.root = cs.idxOf (wTrie cs reads j).label.root := hridx
  congr 1
  simp [FiniteIO.compress, Walk.rlc, recDenP, Fin.sum_univ_four, toQ_lq, algQ, hdN'_eq, tlN'_eq, Gen.hK, hridx',
    wrowOf, coOf, hγQ, hρQ, algQ']
  first
    | (erw [zero_add]; rfl)
    | (erw [zero_add]; simp only [algQ'])
    | (congr 1; erw [zero_add]; rfl)
    | (exact (congrArg _ (by erw [zero_add]; rfl)))

theorem toQ_hPRi (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K6.toQ (dW χe H cs reads j).hPRi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDenP 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((cs.idxOf (wTrie cs reads j).label.root : ℕ) : ZMod P),
          (2 * ((VclL.axisFold (wTrie cs reads j).label.bits : ℕ) : ZMod P) + 1),
          ((((H (VclL.tlN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P),
            (((H (VclL.tlN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P))))⁻¹ := by
  have hridx := walkDB_ridx χe H cs reads j hcs hm
  show K6.toQ (compressE (coOf χe).γH (coOf χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hridx' : idxN cs (wTrie cs reads j).label.root = cs.idxOf (wTrie cs reads j).label.root := hridx
  congr 1
  simp [FiniteIO.compress, Walk.rlc, recDenP, Fin.sum_univ_four, toQ_lq, algQ, hdN'_eq, tlN'_eq, Gen.hK, hridx',
    wrowOf, coOf, hγQ, hρQ, algQ']
  first
    | (erw [zero_add]; rfl)
    | (erw [zero_add]; simp only [algQ'])
    | (congr 1; erw [zero_add]; rfl)
    | (exact (congrArg _ (by erw [zero_add]; rfl)))

omit hcs in
theorem toK_reim (x : K6) (y : KQ) (h : K6.toQ x = y) :
    K3.toK x.re = Quad.re _ y ∧ K3.toK x.im = Quad.im _ y := by
  subst h
  exact ⟨(Quad.re_mk _ _ _).symm, (Quad.im_mk _ _ _).symm⟩

omit hcs in
theorem toK_natG (n : ℕ) : K3.toK (g3 (natG n)) = algebraMap (ZMod P) KC (n : ZMod P) := by
  rw [toK_g3, toZ_natG]

theorem toK_curD (γ : K3) (γ' : KC) (hγ : K3.toK γ = γ')
    (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K3.toK (curD γ (dW χe H cs reads j)) =
      ComplJ8Enc.wNodeValE deltaF (ComplJ8Of.encR deltaF (toχ χe)) cs γ' (wTrie cs reads j) := by
  obtain ⟨p1, p2⟩ := toK_reim _ _ (congrArg ComputeTable.FP.size (toQ_wpE χe H cs reads j))
  obtain ⟨p3, p4⟩ := toK_reim _ _ (congrArg ComputeTable.FP.dyck (toQ_wpE χe H cs reads j))
  obtain ⟨p5, p6⟩ := toK_reim _ _ (congrArg ComputeTable.FP.leaf (toQ_wpE χe H cs reads j))
  obtain ⟨r1, r2⟩ := toK_reim _ _ (congrArg ComputeTable.FP.size (toQ_rootE χe H cs reads j))
  obtain ⟨r3, r4⟩ := toK_reim _ _ (congrArg ComputeTable.FP.dyck (toQ_rootE χe H cs reads j))
  obtain ⟨r5, r6⟩ := toK_reim _ _ (congrArg ComputeTable.FP.leaf (toQ_rootE χe H cs reads j))
  have hridx := walkDB_ridx χe H cs reads j hcs hm
  have hpre : (dW χe H cs reads j).w.pre = VclL.axisFold (wTrie cs reads j).label.bits := rfl
  have hlen : (dW χe H cs reads j).w.len = (wTrie cs reads j).label.bits.length := rfl
  subst hγ
  simp only [curD, Gen.rlcE, encW, ComplJ8Enc.wNodeValE, Walk.rlc, WalkVCL.enc, ComplJ8Enc.lblWE,
    ComplJ8Enc.dtWE, List.foldl,
    Fin.sum_univ_succ, Fin.sum_univ_zero, K3.toK_add, K3.toK_mul, K3.toK_zero, K3.toK_one, toK_natG, hpre,
    hridx, hlen, p1, p2, p3, p4, p5, p6, r1, r2, r3, r4, r5, r6]
  simp
  ring

/-- The honest base columns `3..11` of a walk row's values. -/
def baseColV {K Q : Type} (v : WalkVals (ZMod P) K Q) (c : ℕ) : ZMod P :=
  if c = 3 then v.idx else if c = 4 then v.pre else if c = 5 then v.ridx else if c = 6 then v.len
  else if c = 7 then v.cL else if c = 8 then v.cR else if c = 9 then v.e else if c = 10 then v.mL
  else v.mR

theorem walkColD_base (cert : ℕ → ℕ → ℕ) (N kr q : ℕ) (ln cnt acc : K3) (xa pa hxa hpa : K6) (α γ : KC)
    (c : ℕ) (hc : 3 ≤ c ∧ c < 12)
    (hm : (wTrie cs reads j).label.node ∈ cs ∨ (wTrie cs reads j).label.node.isCell = false)
    (hmr : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    walkColDB cert H N kr q (dW χe H cs reads j) ln cnt acc xa pa hxa hpa c =
      baseColV (rowW χe cs reads j α γ) c := by
  have hidx := walkDB_idx χe H cs reads j hcs hm
  have hridx := walkDB_ridx χe H cs reads j hcs hmr
  obtain ⟨h1, h2⟩ := hc
  have hb : ∀ b b' : Bool, flag (b && b') = (if b then (1 : ZMod P) else 0) * (if b' then 1 else 0) := by
    intro b b'; cases b <;> cases b' <;> simp [flag]
  have hidx' := hidx
  have hridx' := hridx
  simp only [dW, walkDB, wrowOf] at hidx' hridx'
  interval_cases c <;>
    first
    | (simp [walkColDB, walkColD, baseColV, rowW, ComplJ8Enc.walkRow0E, hidx', hridx', dW, walkDB, wrowOf,
        flag, hb]; done)
    | (simp [walkColDB, walkColD, baseColV, rowW, ComplJ8Enc.walkRow0E, hidx', hridx', dW, walkDB, wrowOf,
        flag, hb]
       cases (wTrie cs reads j).label.cL <;> cases (wTrie cs reads j).label.cR <;> simp)

theorem walkColDB_handle (cert : ℕ → ℕ → ℕ) (N kr q : ℕ) (ln cnt acc : K3) (xa pa hxa hpa : K6)
    (hm : (wTrie cs reads j).label.node ∈ cs ∨ (wTrie cs reads j).label.node.isCell = false) :
    walkColDB cert H N kr q (dW χe H cs reads j) ln cnt acc xa pa hxa hpa 21 =
        (((H (VclL.hdN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P) ∧
    walkColDB cert H N kr q (dW χe H cs reads j) ln cnt acc xa pa hxa hpa 22 =
        (((H (VclL.hdN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P) ∧
    walkColDB cert H N kr q (dW χe H cs reads j) ln cnt acc xa pa hxa hpa 23 =
        (((H (VclL.tlN (wTrie cs reads j).label.node)).1 : ℕ) : ZMod P) ∧
    walkColDB cert H N kr q (dW χe H cs reads j) ln cnt acc xa pa hxa hpa 24 =
        (((H (VclL.tlN (wTrie cs reads j).label.node)).2 : ℕ) : ZMod P) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [walkColDB, walkColD, dW, walkDB, wrowOf, hdN'_eq, tlN'_eq]

omit hcs in
theorem walkColDB_cert (N kr q : ℕ) (H : Noun → ℕ × ℕ) (d : WalkD) (ln cnt acc : K3) (xa pa hxa hpa : K6)
    (c : ℕ) (hc : 14 ≤ c ∧ c < 21) :
    walkColDB HonestK8.certB8 H N kr q d ln cnt acc xa pa hxa hpa c =
      HonestK8.fixVal8 d.w.len c := by
  obtain ⟨h1, h2⟩ := hc
  by_cases h : c = 14
  · subst h; simp [walkColDB, HonestK8.fixVal8]
  · have h' : 15 ≤ c := by omega
    simp [walkColDB, HonestK8.fixVal8, h, h', h2]

theorem toK_curD_frame
    (hm : (wTrie cs reads j).label.root ∈ cs ∨ (wTrie cs reads j).label.root.isCell = false) :
    K3.toK (curD (chalsMJ8E χe 1) (dW χe H cs reads j)) =
      ComplJ8Enc.wNodeValE deltaF (ComplJ8Of.encR deltaF (toχ χe)) cs (VerJ8.chalsMJ8 deltaF (toχ χe) 1)
        (wTrie cs reads j) :=
  toK_curD χe H cs reads j hcs _ _ (toK_chals χe 1) hm

end

#print axioms hdN'_eq
#print axioms tlN'_eq
#print axioms idxD_eq'
#print axioms idxOf_mem
#print axioms idxN_eq
#print axioms foW_wrowOf
#print axioms toK_chals
#print axioms toQ_encE
#print axioms toQ_wpE
#print axioms toQ_wlE
#print axioms toQ_wrE
#print axioms toQ_rootE
#print axioms walkDB_idx
#print axioms walkDB_ridx
#print axioms toQ_xInv
#print axioms toQ_pInvL
#print axioms toQ_pInvR
#print axioms toQ_hXi
#print axioms toQ_hPLi
#print axioms toQ_hPRi
#print axioms toK_reim
#print axioms toK_natG
#print axioms toK_curD
#print axioms toK_curD_frame
#print axioms walkColD_base
#print axioms walkColDB_handle
#print axioms walkColDB_cert

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRow
