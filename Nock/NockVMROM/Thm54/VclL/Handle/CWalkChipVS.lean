/-
  Nock/NockVMROM/Thm54/VclL/Handle/CWalkChipVS.lean

* `selIdx` / `zEnv` / **`rowsC`** — the decoded compute rows, 1-indexed (walk row `i` = chip row
    `i − 1`), read off the round-0 columns with zero coins / publics (`rowsC_congr`: columns `< 43`);
    `rowsC_eq` (= `rowOf` at the real row environment, at its one-hot index), `rowsC_small`.
  * **`rowsC_root`** — the root row's `(s, f, e)` are the claim handles (the first-row `hpub` gates,
    `claimHandle`; atoms below `p` by `V.Checks.hclaim`).
  * **`cwalk_sat`** — at an accepted VS coin, the nine `ChipH.walkGates` give `WalkSat` at
    `α = χ₁₃`, `γ = χ₁₄`, `initial_count = α` (public `6..8`), `seed = RLC^γ(label of row 1)·α`
    (public `9..11` = `seedVS` and the `hpub` gates), over `N` rows with the `WalkLblVS` labels and
    child labels (`ChipH.children` = `kids`), `out = 0` (public `12..14`), the queue witness
    `count ≠ ln` below the last row and the terminal `count = ln`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
import Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open scoped Polynomial

noncomputable section

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF

theorem find_congr {α : Type} (p q : α → Bool) : ∀ l : List α, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..)]
    cases q a <;> simp [find_congr p q l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The one-hot index of a row (first selector equal to `1`, default `10`). -/
def selIdx (eF : Env F) : ℕ := ((List.range 11).find? fun j => decide (eF.trace j = 1)).getD 10

/-- Row `i`'s environment with zero coins and publics (the trace part only is read). -/
def zEnv (V : VerifierData F K hC (shapeVS hT hP)) (Qc : Fin (tableVS hC).width → F[X]) (i : ℕ) : Env F :=
  if hi : i < V.N then Reify.envOfTrace Qc V.orbitC.ω (V.computeNodes ⟨i, hi⟩) (fun _ => 0) (fun _ => 0)
  else Reify.envOfTrace Qc V.orbitC.ω (V.computeNodes ⟨0, V.hN⟩) (fun _ => 0) (fun _ => 0)

/-- **The decoded rows, 1-indexed**: walk row `i` is chip row `i − 1`. -/
def rowsC (V : VerifierData F K hC (shapeVS hT hP)) (Qc : Fin (tableVS hC).width → F[X]) (i : ℕ) : RowVS :=
  rowOf (zEnv hT hP hC V Qc (i - 1)) (selIdx (zEnv hT hP hC V Qc (i - 1)))

omit [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq (Quad (algebraMap F K δF))] in
theorem selIdx_of_rowSel {eF : Env F} {j0 : ℕ} (hs : RowSel eF j0) : selIdx eF = j0 := by
  have h := hs.sel
  have hj := hs.lt
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have key : ∀ j < 11, decide (eF.trace j = 1) = decide (j = j0) := by
    intro j hj'
    rw [h j hj']
    by_cases e : j = j0 <;> simp [e, h1]
  interval_cases j0 <;> simp [selIdx, List.range_succ, key]


omit [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq (Quad (algebraMap F K δF))] in
theorem selIdx_congr {e e' : Env F} (h : ∀ j < 11, e.trace j = e'.trace j) : selIdx e = selIdx e' := by
  unfold selIdx
  rw [find_congr (fun j => decide (e.trace j = 1)) (fun j => decide (e'.trace j = 1)) _
    (fun x hx => by rw [h x (List.mem_range.mp hx)])]

omit [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq (Quad (algebraMap F K δF))] in
theorem rowOf_congr {e e' : Env F} (h : ∀ j < 43, e.trace j = e'.trace j) (j0 : ℕ) :
    rowOf e j0 = rowOf e' j0 := by
  simp [rowOf, hdF, hdc, hS, ChipH.hF, hE, hSf1, hSf2, hFh, hFt, hFth, hFtt, hFtth, hFttt, hM, hd, h] <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq (Quad (algebraMap F K δF))] in
/-- The decode reads only columns `0 .. 42`. -/
theorem rowsC_congr (V : VerifierData F K hC (shapeVS hT hP)) {Qc Qc' : Fin (tableVS hC).width → F[X]}
    (h : ∀ j : Fin (tableVS hC).width, (j : ℕ) < 43 → Qc j = Qc' j) :
    rowsC hT hP hC V Qc = rowsC hT hP hC V Qc' := by
  funext i
  have ht : ∀ k, ∀ j < 43, (zEnv hT hP hC V Qc k).trace j = (zEnv hT hP hC V Qc' k).trace j := by
    intro k j hj
    have hw : j < (tableVS hC).width := lt_of_lt_of_le hj (show 43 ≤ ChipH.widthH by decide)
    unfold zEnv
    split_ifs <;> simp [Reify.envOfTrace, hw, h ⟨j, hw⟩ hj]
  unfold rowsC
  rw [rowOf_congr (ht _) _, selIdx_congr (fun j hj => ht _ j (by omega))]

theorem rowsC_eq (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (i : Fin V.N) {j0 : ℕ} (hs : RowSel (cEnvVS δF hT hP kr hC V msg χ i) j0) :
    rowsC hT hP hC V (msg.Qc χ) ((i : ℕ) + 1) = rowOf (cEnvVS δF hT hP kr hC V msg χ i) j0 := by
  have hz : zEnv hT hP hC V (msg.Qc χ) (i : ℕ) = Reify.envOfTrace (msg.Qc χ) V.orbitC.ω (V.computeNodes i)
      (fun _ => 0) (fun _ => 0) := by
    simp [zEnv, i.isLt]
  have ht : ∀ j, (zEnv hT hP hC V (msg.Qc χ) (i : ℕ)).trace j = (cEnvVS δF hT hP kr hC V msg χ i).trace j := by
    intro j; rw [hz]; rfl
  unfold rowsC
  rw [Nat.add_sub_cancel, rowOf_congr (fun j _ => ht j), selIdx_congr (fun j _ => ht j), selIdx_of_rowSel hs]

theorem rowsC_small (hFe : GeneratedField.PrimeFieldElems F) (V : VerifierData F K hC (shapeVS hT hP))
    (Qc : Fin (tableVS hC).width → F[X]) (i : ℕ) : SmallR (ringChar F) (rowsC hT hP hC V Qc i) := by
  simp only [SmallR, rowsC, rowOf, hdF, hdc]
  exact ⟨natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _,
    natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _, natOf_lt hFe _⟩

end VS

/-! ## Env-level bridges -/

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

def HdOK (h : Hd) : Prop := ∃ j, j < 12 ∧ h = hd j

theorem hokS : HdOK hS := ⟨0, by norm_num, rfl⟩
theorem hokF : HdOK ChipH.hF := ⟨1, by norm_num, rfl⟩
theorem hokE : HdOK hE := ⟨2, by norm_num, rfl⟩
theorem hokSf1 : HdOK hSf1 := ⟨3, by norm_num, rfl⟩
theorem hokSf2 : HdOK hSf2 := ⟨4, by norm_num, rfl⟩
theorem hokFh : HdOK hFh := ⟨5, by norm_num, rfl⟩
theorem hokFt : HdOK hFt := ⟨6, by norm_num, rfl⟩
theorem hokFth : HdOK hFth := ⟨7, by norm_num, rfl⟩
theorem hokFtt : HdOK hFtt := ⟨8, by norm_num, rfl⟩
theorem hokFtth : HdOK hFtth := ⟨9, by norm_num, rfl⟩
theorem hokFttt : HdOK hFttt := ⟨10, by norm_num, rfl⟩
theorem hokM : HdOK hM := ⟨11, by norm_num, rfl⟩

theorem lift_enc (hFe : GeneratedField.PrimeFieldElems F) {e : Env F}
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e = 0) {h : Hd} (hh : HdOK h) :
    algebraMap F K (e.trace h.k) = (encH (hdF e h) : K × K).1 ∧
      algebraMap F K (e.trace h.v) = (encH (hdF e h) : K × K).2 := by
  obtain ⟨j, hj, rfl⟩ := hh
  constructor
  · rcases kind_bool hbase j hj with h0 | h1
    · simp [encH, hdF, hdc, h0]
    · simp [encH, hdF, hdc, h1]
  · have h2 : algebraMap F K ((natOf (e.trace (hd j).v) : ℕ) : F) = algebraMap F K (e.trace (hd j).v) := by
      rw [natOf_cast hFe]
    rw [map_natCast] at h2
    simp [encH, hdF, hdc, h2]

/-- A label's `γ`-RLC over trace columns. -/
def lblV (γ : K) (e : Env F) (cols : List ℕ) : K :=
  ∑ c ∈ Finset.range cols.length, γ ^ c * algebraMap F K (e.trace (cols.getD c 0))

theorem evalMQ_rlcKey' (eK : Env K) (eF : Env F) (kind : VarKind) (e' : Env F)
    (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i) (γ : ℕ) :
    ∀ (r : List ℕ) (m : ℕ), evalMQ (rlcKey kind γ m r : MixedExpr ℚ) eK eF =
      ∑ c ∈ Finset.range r.length, eK.chal γ ^ (m + c) * algebraMap F K (e'.trace (r.getD c 0))
  | [], m => by simp [rlcKey, evalMQ]
  | i :: r, m => by
    rw [rlcKey, evalMQ, evalMQ_rlcKey' eK eF kind e' hk γ r (m + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [evalMQ, hk, List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

theorem rlcKey_lbl (eK : Env K) (eF : Env F) (kind : VarKind) (e' : Env F)
    (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i) (γ : ℕ) (r : List ℕ) :
    evalMQ (rlcKey kind γ 0 r : MixedExpr ℚ) eK eF = lblV (eK.chal γ) e' r := by
  rw [evalMQ_rlcKey' eK eF kind e' hk]; simp [lblV]

theorem lblV_hcols (hFe : GeneratedField.PrimeFieldElems F) (γ : K) {e : Env F}
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e = 0) {s f g : Hd} (hs : HdOK s) (hf : HdOK f)
    (hg : HdOK g) :
    lblV γ e (hcols s f g) = Walk.rlc γ (encT (K := K) (hdF e s, hdF e f, hdF e g)) := by
  obtain ⟨a1, a2⟩ := lift_enc (K := K) hFe hbase hs
  obtain ⟨b1, b2⟩ := lift_enc (K := K) hFe hbase hf
  obtain ⟨c1, c2⟩ := lift_enc (K := K) hFe hbase hg
  simp [lblV, hcols, Walk.rlc, encT, Fin.sum_univ_succ, Finset.sum_range_succ, a1, a2, b1, b2, c1, c2]
  ring

theorem evalMQ_sumM (eK : Env K) (eF : Env F) (l : List (MixedExpr ℚ)) :
    evalMQ (sumM l : MixedExpr ℚ) eK eF = (l.map fun u => evalMQ u eK eF).sum := by
  induction l with
  | nil => simp [sumM, evalMQ]
  | cons a l ih => simp only [sumM, List.foldr_cons] at ih ⊢; simp [evalMQ, ih]

theorem zipIdx_sum {α M : Type} [AddCommMonoid M] (d : α) (g : α → ℕ → M) :
    ∀ (l : List α) (k : ℕ), ((l.zipIdx k).map fun p => g p.1 p.2).sum =
      ∑ i ∈ Finset.range l.length, g (l.getD i d) (k + i)
  | [], k => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum d g l (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show k + 1 + c = k + (c + 1) by omega]

theorem curL_eval (hFe : GeneratedField.PrimeFieldElems F) (eK : Env K) (eF : Env F) (kind : VarKind)
    (e' : Env F) (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i)
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e' = 0) :
    evalMQ (curL kind : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal 9) (encT (K := K) (hdF e' hS, hdF e' ChipH.hF, hdF e' hE)) := by
  unfold curL
  rw [rlcKey_lbl eK eF kind e' hk]
  exact lblV_hcols hFe _ hbase hokS hokF hokE

theorem children_kids (hFe : GeneratedField.PrimeFieldElems F) (γ : K) {e : Env F}
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e = 0) (j0 : ℕ) (hj : j0 < 11) (i : ℕ)
    (hi : i < (children j0).length) :
    lblV γ e ((children j0).getD i []) =
      Walk.rlc γ (encT (K := K) ((kids (rowOf e j0)).getD i trip0)) := by
  have h3 : i < 3 := lt_of_lt_of_le hi (by interval_cases j0 <;> simp [children])
  interval_cases j0 <;> interval_cases i <;> first | (simp [children] at hi; done) | skip <;>
    simp [children, kids, rowOf, stOf, lblV_hcols hFe γ hbase, hokS, hokF, hokE, hokSf1, hokSf2, hokFh, hokFt,
      hokFth, hokFtt, hokFtth, hokFttt, hokM]

theorem children_len : ∀ st < 11, (children st).length = fanS (stOf st) := by decide

theorem sum_onehot (X : ℕ → K) (c : ℕ → F) (j0 : ℕ) (hj : j0 < 11)
    (hc : ∀ st < 11, c st = if st = j0 then 1 else 0) :
    ((List.range 11).map fun st => algebraMap F K (c st) * X st).sum = X j0 := by
  have : (List.range 11).map (fun st => algebraMap F K (c st) * X st) =
      (List.range 11).map (fun st => if st = j0 then X st else 0) :=
    List.map_congr_left fun st hst => by
      rw [hc st (List.mem_range.mp hst)]; split_ifs <;> simp
  rw [this]
  interval_cases j0 <;> simp [List.range_succ]

theorem ccL_eval (hFe : GeneratedField.PrimeFieldElems F) (eK : Env K) (eF : Env F) (kind : VarKind)
    (e' : Env F) (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i)
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e' = 0) {j0 : ℕ} (hs : RowSel e' j0) :
    evalMQ (ccL kind : MixedExpr ℚ) eK eF =
      ∑ i ∈ Finset.range (fanS (stOf j0)), eK.chal 6 ^ (i + 1) *
        Walk.rlc (eK.chal 9) (encT (K := K) ((kids (rowOf e' j0)).getD i trip0)) := by
  unfold ccL
  rw [evalMQ_sumM, List.map_map]
  have h1 : ∀ st, evalMQ (MixedExpr.Scale (kv kind st) (childSum kind st) : MixedExpr ℚ) eK eF =
      algebraMap F K (e'.trace st) * evalMQ (childSum kind st : MixedExpr ℚ) eK eF := by
    intro st; simp only [evalMQ, kv, hk]
  simp only [Function.comp_def, h1, ChipH.allStates]
  rw [sum_onehot (fun st => evalMQ (childSum kind st : MixedExpr ℚ) eK eF) e'.trace j0 hs.lt hs.sel]
  unfold childSum
  rw [evalMQ_sumM, List.map_map]
  have h2 : ∀ p : List ℕ × ℕ, evalMQ (MixedExpr.Mul (MixedExpr.Pow (MixedExpr.Var .challenge chalAlphaW) (p.2 + 1))
      (rlcKey kind chalGammaW 0 p.1) : MixedExpr ℚ) eK eF = eK.chal 6 ^ (p.2 + 1) * lblV (eK.chal 9) e' p.1 := by
    intro p; simp only [evalMQ, chalAlphaW, rlcKey_lbl eK eF kind e' hk, chalGammaW]
  simp only [Function.comp_def, h2]
  rw [zipIdx_sum [] (fun p1 p2 => eK.chal 6 ^ (p2 + 1) * lblV (eK.chal 9) e' p1) (children j0) 0,
    children_len j0 hs.lt]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [children_kids hFe _ hbase j0 hs.lt i (by rw [children_len j0 hs.lt]; exact Finset.mem_range.mp hi)]
  simp

theorem cmL_eval (eK : Env K) (eF : Env F) (kind : VarKind)
    (e' : Env F) (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i) {j0 : ℕ}
    (hs : RowSel e' j0) :
    evalMQ (cmL kind : MixedExpr ℚ) eK eF = eK.chal 6 ^ (fanS (stOf j0)) := by
  unfold cmL
  rw [evalMQ_sumM, List.map_map]
  have h1 : ∀ st, evalMQ (MixedExpr.Scale (kv kind st) (MixedExpr.Pow (MixedExpr.Var .challenge chalAlphaW)
      (children st).length) : MixedExpr ℚ) eK eF =
      algebraMap F K (e'.trace st) * eK.chal 6 ^ (children st).length := by
    intro st; simp only [evalMQ, kv, hk, chalAlphaW]
  simp only [Function.comp_def, h1, ChipH.allStates]
  rw [sum_onehot (fun st => eK.chal 6 ^ (children st).length) e'.trace j0 hs.lt hs.sel,
    children_len j0 hs.lt]

end Env

/-! ## The chip level -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])

/-- The hypotheses of the extraction. -/
structure WCtx (α γ seed : K) : Prop where
  hFe : GeneratedField.PrimeFieldElems F
  hc : 11 < ringChar F
  hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P
  hinj : Function.Injective nodes
  hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω
  hα6 : Compute.LogUp.limbVal b chalV 6 = α
  hγ9 : Compute.LogUp.limbVal b chalV 9 = γ
  hp6 : Compute.LogUp.limbVal b pubVal 6 = α
  hp9 : Compute.LogUp.limbVal b pubVal 9 = seed
  hp12 : Compute.LogUp.limbVal b pubVal 12 = 0

local notation "EN" => envsN hn nodes chalV pubVal orbit P

variable {hn nodes b chalV pubVal orbit P} {α γ seed : K}
  (C : WCtx hn nodes b chalV pubVal orbit P α γ seed)
include C

theorem hbaseE {r : ℕ} (hr : r < n) : ∀ t ∈ baseGatesH (F := ℚ), evalQ t (EN r) = 0 := by
  intro t ht
  rw [envsN_lt hn nodes b chalV pubVal orbit P r hr]
  exact base_of_sat hn nodes b chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _) t ht

theorem selE {r : ℕ} (hr : r < n) : RowSel (EN r) (selIdx (EN r)) := by
  obtain ⟨j0, hs⟩ := rowSel_of_base (hbaseE C hr) C.hc
  rwa [selIdx_of_rowSel hs]

theorem tnE {r : ℕ} (hr : r + 1 < n) : (EN r).traceNext = (EN (r + 1)).trace := by
  funext j
  rw [envsN_lt hn nodes b chalV pubVal orbit P r (by omega),
    envsN_lt hn nodes b chalV pubVal orbit P (r + 1) hr]
  exact traceNext_eq nodes orbit P _ _ C.hadj ⟨r, by omega⟩ hr j

theorem masksE {r : ℕ} (hr : r < n) :
    (EN r).trace 11 = (if r = 0 then 1 else 0) ∧ (EN r).trace 12 = (if r = n - 1 then 1 else 0) := by
  have hb := ((computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mp C.hsat).1
  have := masksC hn nodes b chalV pubVal orbit P hb C.hinj ⟨r, hr⟩
  rw [envsN_lt hn nodes b chalV pubVal orbit P r hr]
  simpa using this

theorem gateE {r : ℕ} (hr : r < n) (g : MixedExpr ℚ) (hg : g ∈ (walkGates : List (MixedExpr ℚ))) :
    evalMQ g (Compute.TowerD.gatherEnv b (EN r)) (EN r) = 0 := by
  rw [envsN_lt hn nodes b chalV pubVal orbit P r hr]
  exact k_of_sat hn nodes b chalV pubVal orbit P C.hsat _ (mem_rowNodeSet nodes _) g
    (List.mem_append_right _ hg)

theorem chalE (r : ℕ) : (EN r).chal = chalV := by
  unfold envsN; split_ifs <;> rfl

theorem pubE (r : ℕ) : (EN r).pub = pubVal := by
  unfold envsN; split_ifs <;> rfl

theorem g_ln_step {r : ℕ} (hr : r + 1 < n) :
    Compute.LogUp.limbVal b (EN (r + 1)).trace wLn = α * Compute.LogUp.limbVal b (EN r).trace wLn := by
  have h0 := gateE C (by omega : r < n) (walkGates[0]'(by simp [walkGates])) (List.getElem_mem _)
  have m12 : (EN r).trace 12 = 0 := by rw [(masksE C (by omega)).2]; simp; omega
  simp [walkGates, evalMQ, evalQ, notLast, notC, cc, Compute.TowerD.gatherEnv, ChipH.wv, chalAlphaW,
    lastCol, tnE C hr, chalE C r, m12, C.hα6, sub_eq_zero] at h0
  exact h0

theorem hkNext {r : ℕ} (hr : r + 1 < n) :
    ∀ i, evalQ (.var .traceNext i : CoeffExpr ℚ) (EN r) = (EN (r + 1)).trace i := fun i => by
  show (EN r).traceNext i = _
  rw [tnE C hr]

theorem g_cnt_step {r : ℕ} (hr : r + 1 < n) :
    Compute.LogUp.limbVal b (EN (r + 1)).trace wCnt =
      Compute.LogUp.limbVal b (EN r).trace wCnt * α ^ (fanS (stOf (selIdx (EN (r + 1))))) := by
  have h0 := gateE C (by omega : r < n) (walkGates[1]'(by simp [walkGates])) (List.getElem_mem _)
  have m12 : (EN r).trace 12 = 0 := by rw [(masksE C (by omega)).2]; simp; omega
  have hc := cmL_eval (Compute.TowerD.gatherEnv b (EN r)) (EN r) .traceNext (EN (r + 1)) (hkNext C hr)
    (selE C (by omega : r + 1 < n))
  simp [walkGates, evalMQ, evalQ, notLast, notC, cc, Compute.TowerD.gatherEnv, ChipH.wv, chalAlphaW,
    lastCol, tnE C hr, chalE C r, m12, C.hα6, sub_eq_zero] at h0 hc
  rw [hc] at h0
  exact h0

theorem g_acc_step {r : ℕ} (hr : r + 1 < n) :
    Compute.LogUp.limbVal b (EN (r + 1)).trace wLn *
        Walk.rlc γ (encT (K := K) (hdF (EN (r + 1)) hS, hdF (EN (r + 1)) ChipH.hF, hdF (EN (r + 1)) hE)) +
      Compute.LogUp.limbVal b (EN (r + 1)).trace wAcc - Compute.LogUp.limbVal b (EN r).trace wAcc =
    ∑ i ∈ Finset.range (fanS (stOf (selIdx (EN (r + 1))))), Compute.LogUp.limbVal b (EN r).trace wCnt *
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kids (rowOf (EN (r + 1)) (selIdx (EN (r + 1))))).getD i trip0))) := by
  have h0 := gateE C (by omega : r < n) (walkGates[2]'(by simp [walkGates])) (List.getElem_mem _)
  have m12 : (EN r).trace 12 = 0 := by rw [(masksE C (by omega)).2]; simp; omega
  have hc := ccL_eval C.hFe (Compute.TowerD.gatherEnv b (EN r)) (EN r) .traceNext (EN (r + 1)) (hkNext C hr)
    (hbaseE C (by omega : r + 1 < n)) (selE C (by omega : r + 1 < n))
  have hl := curL_eval (K := K) C.hFe (Compute.TowerD.gatherEnv b (EN r)) (EN r) .traceNext (EN (r + 1))
    (hkNext C hr) (hbaseE C (by omega : r + 1 < n))
  have e6 : (Compute.TowerD.gatherEnv b (EN r)).chal 6 = α := by
    simp [Compute.TowerD.gatherEnv, chalE C r, C.hα6]
  have e9 : (Compute.TowerD.gatherEnv b (EN r)).chal 9 = γ := by
    simp [Compute.TowerD.gatherEnv, chalE C r, C.hγ9]
  rw [e6, e9] at hc
  rw [e9] at hl
  simp only [walkGates, evalMQ, evalQ, notLast, notC, cc, ChipH.wv, hc, hl, List.getElem_cons_succ,
    List.getElem_cons_zero] at h0
  simp [Compute.TowerD.gatherEnv, tnE C hr, m12, lastCol] at h0
  simp only [List.getD_eq_getElem?_getD, ← Finset.mul_sum]
  exact sub_eq_zero.mp h0

theorem m11_zero : (EN 0).trace 11 = 1 := by
  have := (masksE C hn).1; simpa using this

theorem g_ln_zero : Compute.LogUp.limbVal b (EN 0).trace wLn = α := by
  have h0 := gateE C hn (walkGates[3]'(by simp [walkGates])) (List.getElem_mem _)
  simp [walkGates, evalMQ, evalQ, cc, Compute.TowerD.gatherEnv, ChipH.wv, chalAlphaW, firstCol,
    m11_zero C, chalE C 0, C.hα6, sub_eq_zero] at h0
  exact h0

theorem g_cnt_zero : Compute.LogUp.limbVal b (EN 0).trace wCnt =
    α * α ^ (fanS (stOf (selIdx (EN 0)))) := by
  have h0 := gateE C hn (walkGates[4]'(by simp [walkGates])) (List.getElem_mem _)
  have hc := cmL_eval (Compute.TowerD.gatherEnv b (EN 0)) (EN 0) .traceCur (EN 0) (fun _ => rfl)
    (selE C hn)
  have e6 : (Compute.TowerD.gatherEnv b (EN 0)).chal 6 = α := by
    simp [Compute.TowerD.gatherEnv, chalE C 0, C.hα6]
  rw [e6] at hc
  simp only [walkGates, evalMQ, evalQ, cc, ChipH.wv, hc, List.getElem_cons_succ,
    List.getElem_cons_zero] at h0
  simp [Compute.TowerD.gatherEnv, firstCol, m11_zero C, pubE C 0, C.hp6, sub_eq_zero, pubIC] at h0
  exact h0

theorem g_acc_zero :
    Compute.LogUp.limbVal b (EN 0).trace wLn *
        Walk.rlc γ (encT (K := K) (hdF (EN 0) hS, hdF (EN 0) ChipH.hF, hdF (EN 0) hE)) +
      Compute.LogUp.limbVal b (EN 0).trace wAcc =
    α * ∑ i ∈ Finset.range (fanS (stOf (selIdx (EN 0)))),
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kids (rowOf (EN 0) (selIdx (EN 0)))).getD i trip0))) + seed := by
  have h0 := gateE C hn (walkGates[5]'(by simp [walkGates])) (List.getElem_mem _)
  have hc := ccL_eval C.hFe (Compute.TowerD.gatherEnv b (EN 0)) (EN 0) .traceCur (EN 0) (fun _ => rfl)
    (hbaseE C hn) (selE C hn)
  have hl := curL_eval (K := K) C.hFe (Compute.TowerD.gatherEnv b (EN 0)) (EN 0) .traceCur (EN 0)
    (fun _ => rfl) (hbaseE C hn)
  have e6 : (Compute.TowerD.gatherEnv b (EN 0)).chal 6 = α := by
    simp [Compute.TowerD.gatherEnv, chalE C 0, C.hα6]
  have e9 : (Compute.TowerD.gatherEnv b (EN 0)).chal 9 = γ := by
    simp [Compute.TowerD.gatherEnv, chalE C 0, C.hγ9]
  rw [e6, e9] at hc
  rw [e9] at hl
  simp only [walkGates, evalMQ, evalQ, cc, ChipH.wv, hc, hl, List.getElem_cons_succ,
    List.getElem_cons_zero] at h0
  simp [Compute.TowerD.gatherEnv, firstCol, m11_zero C, pubE C 0, C.hp6, C.hp9, pubIC, pubSeed] at h0
  simp only [List.getD_eq_getElem?_getD, ← Finset.mul_sum]
  exact sub_eq_zero.mp h0

theorem g_wit {r : ℕ} (hr : r + 1 < n) :
    Compute.LogUp.limbVal b (EN r).trace wCnt ≠ Compute.LogUp.limbVal b (EN r).trace wLn := by
  have h0 := gateE C (by omega : r < n) (walkGates[6]'(by simp [walkGates])) (List.getElem_mem _)
  have m12 : (EN r).trace 12 = 0 := by rw [(masksE C (by omega)).2]; simp; omega
  simp [walkGates, evalMQ, evalQ, notLast, notC, cc, Compute.TowerD.gatherEnv, ChipH.wv, lastCol, m12,
    sub_eq_zero] at h0
  intro he
  rw [he, sub_self, mul_zero] at h0
  exact zero_ne_one h0

theorem g_last : Compute.LogUp.limbVal b (EN (n - 1)).trace wCnt = Compute.LogUp.limbVal b (EN (n - 1)).trace wLn ∧
    Compute.LogUp.limbVal b (EN (n - 1)).trace wAcc = 0 := by
  have hr : n - 1 < n := by omega
  have m12 : (EN (n - 1)).trace 12 = 1 := by rw [(masksE C hr).2]; simp
  have h7 := gateE C hr (walkGates[7]'(by simp [walkGates])) (List.getElem_mem _)
  have h8 := gateE C hr (walkGates[8]'(by simp [walkGates])) (List.getElem_mem _)
  simp [walkGates, evalMQ, evalQ, cc, Compute.TowerD.gatherEnv, ChipH.wv, lastCol, m12, sub_eq_zero,
    pubE C, pubOut, C.hp12] at h7 h8
  exact ⟨h7, h8⟩

omit C in
theorem sum_Icc_range {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ m : ℕ, ∑ l ∈ Finset.Icc 1 m, f l = ∑ i ∈ Finset.range m, f (i + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, sum_Icc_range f m]

/-- The decoded rows of the generic chip, 1-indexed. -/
def rowsG (r : ℕ) : RowVS := rowOf (EN (r - 1)) (selIdx (EN (r - 1)))

omit C in
theorem enc_lbl (i : ℕ) :
    enc (K := K) (lblOf (rowsG (hn := hn) (nodes := nodes) (b := b) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P)) i) =
      encT (hdF (EN (i - 1)) hS, hdF (EN (i - 1)) ChipH.hF, hdF (EN (i - 1)) hE) := rfl

omit C in
theorem enc_clab (i l : ℕ) :
    enc (K := K) (clabOf (rowsG (hn := hn) (nodes := nodes) (b := b) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P)) i l) =
      encT ((kids (rowOf (EN (i - 1)) (selIdx (EN (i - 1))))).getD (l - 1) trip0) := by
  simp [WalkLblVS.enc, clabOf, rowsG]

theorem cwalk_chip (hseed : seed = Walk.rlc γ (encT (K := K) (hdF (EN 0) hS, hdF (EN 0) ChipH.hF,
      hdF (EN 0) hE)) * α) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc γ (enc (lblOf (rowsG (hn := hn) (nodes := nodes) (b := b)
          (chalV := chalV) (pubVal := pubVal) (orbit := orbit) (P := P)) i)))
        (fun i l => Walk.rlc γ (enc (clabOf (rowsG (hn := hn) (nodes := nodes) (b := b)
          (chalV := chalV) (pubVal := pubVal) (orbit := orbit) (P := P)) i l)))
        (foOf (rowsG (hn := hn) (nodes := nodes) (b := b) (chalV := chalV) (pubVal := pubVal)
          (orbit := orbit) (P := P))) ln cnt acc α
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc γ (enc (lblOf (rowsG (hn := hn) (nodes := nodes) (b := b)
          (chalV := chalV) (pubVal := pubVal) (orbit := orbit) (P := P)) i)) * α ^ i)
        (α ^ 1) n ∧
      acc n = 0 ∧ (∀ i, 1 ≤ i → i < n → cnt i ≠ ln i) ∧ cnt n = ln n := by
  refine ⟨fun i => Compute.LogUp.limbVal b (EN (i - 1)).trace wLn,
    fun i => Compute.LogUp.limbVal b (EN (i - 1)).trace wCnt,
    fun i => Compute.LogUp.limbVal b (EN (i - 1)).trace wAcc, ?_, ?_, ?_, ?_⟩
  · refine
      { hpos := hn
        ln1 := g_ln_zero C
        lnInc := fun i hi hin => ?_
        count1 := ?_
        countInc := fun i hi hin => ?_
        accInit := ?_
        accStep := fun i hi hin => ?_ }
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      exact g_ln_step C (r := r) (by omega)
    · rw [pow_one]; exact g_cnt_zero C
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      exact g_cnt_step C (r := r) (by omega)
    · have h0 := g_acc_zero C
      simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [sum_Icc_range]
      simp only [pow_one, enc_lbl, enc_clab, Nat.reduceSub]
      rw [← hseed, h0, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Nat.add_sub_cancel]
      ring
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      have h0 := g_acc_step C (r := r) (by omega)
      rw [sum_Icc_range]
      simp only [enc_lbl, enc_clab, Nat.add_sub_cancel]
      rw [h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · exact (g_last C).2
  · intro i hi hin
    obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
    exact g_wit C (r := r) (by omega)
  · exact (g_last C).1

theorem row0_pub :
    (EN 0).trace hS.k = pubVal 0 ∧ (EN 0).trace hS.v = pubVal 1 ∧
    (EN 0).trace ChipH.hF.k = pubVal 2 ∧ (EN 0).trace ChipH.hF.v = pubVal 3 ∧
    (EN 0).trace hE.k = pubVal 4 ∧ (EN 0).trace hE.v = pubVal 5 := by
  have hb := hbaseE C hn
  have key : ∀ (g : EqG ℚ), g ∈ (eqGates : List (EqG ℚ)) → g.σ = cc firstCol →
      ∀ (x y : ℕ), g.x = x → g.y = Opnd.pub y → (EN 0).trace x = pubVal y := by
    intro g hg hσ x y hx hy
    have := eq_fact hb g hg
    simp only [EqG.gate, hσ, hx, hy, Opnd.expr, evalQ, cc, firstCol, m11_zero C, pubE C 0, one_mul,
      sub_eq_zero] at this
    exact this
  have mSk : (⟨cc firstCol, hS.k, .pub 0⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (by unfold ChipH.hpub; exact List.mem_cons_self)))
  have mSv : (⟨cc firstCol, hS.v, .pub 1⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (by unfold ChipH.hpub; exact List.mem_cons_of_mem _ List.mem_cons_self)))
  have mFk : (⟨cc firstCol, ChipH.hF.k, .pub 2⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_left _ (List.mem_append_right _
      (by unfold ChipH.hpub; exact List.mem_cons_self))
  have mFv : (⟨cc firstCol, ChipH.hF.v, .pub 3⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_left _ (List.mem_append_right _
      (by unfold ChipH.hpub; exact List.mem_cons_of_mem _ List.mem_cons_self))
  have mEk : (⟨cc firstCol, hE.k, .pub 4⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_right _ (by unfold ChipH.hpub; exact List.mem_cons_self)
  have mEv : (⟨cc firstCol, hE.v, .pub 5⟩ : EqG ℚ) ∈ (ChipH.eqGates : List (EqG ℚ)) := by
    unfold ChipH.eqGates
    exact List.mem_append_right _ (by unfold ChipH.hpub; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨key ⟨cc firstCol, hS.k, .pub 0⟩ mSk rfl _ _ rfl rfl,
    key ⟨cc firstCol, hS.v, .pub 1⟩ mSv rfl _ _ rfl rfl,
    key ⟨cc firstCol, ChipH.hF.k, .pub 2⟩ mFk rfl _ _ rfl rfl,
    key ⟨cc firstCol, ChipH.hF.v, .pub 3⟩ mFv rfl _ _ rfl rfl,
    key ⟨cc firstCol, hE.k, .pub 4⟩ mEk rfl _ _ rfl rfl,
    key ⟨cc firstCol, hE.v, .pub 5⟩ mEv rfl _ _ rfl rfl⟩

end Chip

/-! ## At VS -/

section VSMain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF

theorem limb_chal_alpha (b : Basis (Fin 3) F K) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (chalVH b χ) 6 = χ cAlphaW := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [chalVH, coinH]

theorem limb_chal_gam (b : Basis (Fin 3) F K) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (chalVH b χ) 9 = χ cGamW := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [chalVH, coinH]

theorem limb_pub_alpha (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (pubVH δF b c m ρ χ) 6 = χ cAlphaW := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubVH]

theorem limb_pub_seed (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (pubVH δF b c m ρ χ) 9 = seedVS (F := F) c m χ := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubVH]

theorem limb_pub_zero (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    Compute.LogUp.limbVal b (pubVH δF b c m ρ χ) 12 = 0 := by
  refine Compute.LogUp.limbVal_eq_of_coords b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubVH, coord]

theorem vsCtx (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    WCtx V.hN V.computeNodes V.basis (chalVH V.basis χ)
      (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC
      (fun j => msg.Qc χ (Fin.cast rfl j)) (χ cAlphaW) (χ cGamW) (seedVS (F := F) V.claim msg.msg0C χ) := by
  obtain ⟨hg, hsat⟩ := compute_facts δF hT hP kr hC V msg χ h
  exact
    { hFe := hV.hF
      hc := lt_trans (by norm_num) hg.2.2.1
      hsat := hsat
      hinj := hg.2.1
      hadj := fun i hi => by rw [hg.1 i hi, mul_comm]
      hα6 := limb_chal_alpha V.basis χ
      hγ9 := limb_chal_gam V.basis χ
      hp6 := limb_pub_alpha δF V.basis V.claim msg.msg0C (msg.requests χ) χ
      hp9 := limb_pub_seed δF V.basis V.claim msg.msg0C (msg.requests χ) χ
      hp12 := limb_pub_zero δF V.basis V.claim msg.msg0C (msg.requests χ) χ }

theorem rowsC_eq_rowsG (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    rowsC hT hP hC V (msg.Qc χ) =
      rowsG (hn := V.hN) (nodes := V.computeNodes) (b := V.basis) (chalV := chalVH V.basis χ)
        (pubVal := pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) (orbit := V.orbitC)
        (P := fun j => msg.Qc χ (Fin.cast rfl j)) := by
  funext i
  have ht : ∀ k j, (zEnv hT hP hC V (msg.Qc χ) k).trace j =
      (envsN V.hN V.computeNodes (chalVH V.basis χ)
        (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC
        (fun j => msg.Qc χ (Fin.cast rfl j)) k).trace j := by
    intro k j
    unfold zEnv envsN
    split_ifs <;> rfl
  unfold rowsC rowsG
  rw [rowOf_congr (fun j _ => ht _ j), selIdx_congr (fun j _ => ht _ j)]
  rfl

theorem pub_labels (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    pubVH δF b c m ρ χ 0 = (if (claimH c m 0).1 then 1 else 0) ∧
    pubVH δF b c m ρ χ 1 = (((claimH c m 0).2 : ℕ) : F) ∧
    pubVH δF b c m ρ χ 2 = (if (claimH c m 1).1 then 1 else 0) ∧
    pubVH δF b c m ρ χ 3 = (((claimH c m 1).2 : ℕ) : F) ∧
    pubVH δF b c m ρ χ 4 = (if (claimH c m 2).1 then 1 else 0) ∧
    pubVH δF b c m ρ χ 5 = (((claimH c m 2).2 : ℕ) : F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [pubVH, labelF, hvalF]

theorem handle_claim (hFe : GeneratedField.PrimeFieldElems F) (x : Noun)
    (hx : FieldEmbedding.BoundedBy (ringChar F) x) (idx : ℕ) :
    (decide ((if (claimHandle x idx).1 then (1 : F) else 0) = 1),
        natOf (((claimHandle x idx).2 : ℕ) : F)) = claimHandle x (natOf (idx : F)) := by
  cases x with
  | atom v => simp [claimHandle, natOf_natCast hFe hx]
  | cell l r => simp [claimHandle]

theorem rowsC_root (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    (rowsC hT hP hC V (msg.Qc χ) 1).s = claimHandle V.claim.subject (natOf ((msg.msg0C 0).1 : F)) ∧
    (rowsC hT hP hC V (msg.Qc χ) 1).f = claimHandle V.claim.formula (natOf ((msg.msg0C 1).1 : F)) ∧
    (rowsC hT hP hC V (msg.Qc χ) 1).e = claimHandle V.claim.result (natOf ((msg.msg0C 2).1 : F)) := by
  have C := vsCtx δF hT hP kr hC V hV msg χ h
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_pub C
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pub_labels δF V.basis V.claim msg.msg0C (msg.requests χ) χ
  rw [rowsC_eq_rowsG δF hT hP kr hC V msg χ]
  obtain ⟨c0, c1, c2⟩ := hV.hclaim
  refine ⟨?_, ?_, ?_⟩
  · simp only [rowsG, rowOf, hdF, hdc, Nat.reduceSub]
    rw [p0, p1, l0, l1]
    exact handle_claim hV.hF V.claim.subject c0 (msg.msg0C 0).1
  · simp only [rowsG, rowOf, hdF, hdc, Nat.reduceSub]
    rw [p2, p3, l2, l3]
    exact handle_claim hV.hF V.claim.formula c1 (msg.msg0C 1).1
  · simp only [rowsG, rowOf, hdF, hdc, Nat.reduceSub]
    rw [p4, p5, l4, l5]
    exact handle_claim hV.hF V.claim.result c2 (msg.msg0C 2).1

theorem seed_gen (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) (e : Env F)
    (hFe : GeneratedField.PrimeFieldElems F) (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t e = 0)
    (p0 : e.trace hS.k = pubVH δF b c m ρ χ 0) (p1 : e.trace hS.v = pubVH δF b c m ρ χ 1)
    (p2 : e.trace ChipH.hF.k = pubVH δF b c m ρ χ 2) (p3 : e.trace ChipH.hF.v = pubVH δF b c m ρ χ 3)
    (p4 : e.trace hE.k = pubVH δF b c m ρ χ 4) (p5 : e.trace hE.v = pubVH δF b c m ρ χ 5) :
    seedVS (F := F) c m χ =
      Walk.rlc (χ cGamW) (encT (K := K) (hdF e hS, hdF e ChipH.hF, hdF e hE)) * χ cAlphaW := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pub_labels δF b c m ρ χ
  rw [← lblV_hcols hFe (χ cGamW) hbase hokS hokF hokE]
  simp [seedVS, lblV, hcols, Finset.sum_range_succ, labelF, hvalF, List.zipIdx, p0, p1, p2, p3, p4, p5,
    l0, l1, l2, l3, l4, l5]
  ring

set_option maxHeartbeats 1600000 in
theorem cwalk_sat (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc (χ cGamW) (enc (lblOf (rowsC hT hP hC V (msg.Qc χ)) i)))
        (fun i l => Walk.rlc (χ cGamW) (enc (clabOf (rowsC hT hP hC V (msg.Qc χ)) i l)))
        (foOf (rowsC hT hP hC V (msg.Qc χ))) ln cnt acc (χ cAlphaW)
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc (χ cGamW) (enc (lblOf (rowsC hT hP hC V (msg.Qc χ)) i)) *
          χ cAlphaW ^ i)
        (χ cAlphaW ^ 1) V.N ∧
      acc V.N = 0 ∧ (∀ i, 1 ≤ i → i < V.N → cnt i ≠ ln i) ∧ cnt V.N = ln V.N := by
  have C := vsCtx δF hT hP kr hC V hV msg χ h
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_pub C
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := pub_labels δF V.basis V.claim msg.msg0C (msg.requests χ) χ
  obtain ⟨ln, cnt, acc, hw⟩ := cwalk_chip (K := K) C
    (seed_gen δF V.basis V.claim msg.msg0C (msg.requests χ) χ _ C.hFe (hbaseE C V.hN) p0 p1 p2 p3 p4 p5)
  refine ⟨ln, cnt, acc, ?_⟩
  rw [rowsC_eq_rowsG δF hT hP kr hC V msg χ]
  exact hw

end VSMain

end

end Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
