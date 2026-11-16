/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/BudLenJ9A.lean

  **J-9 A: the record-count budgets of the twin** (twins of `ReadIOJ8.capB … compReqsX_length_le` and
  `AcceptsJ9ZG.compLenZG9 … hcount_ofZG9`).

  1. `consQX9_length_le`, `compReqsX9_length_le`, `compReqsOf9_length_le`: at most `capB9 bl` records per row.
  2.
  3. The `RR49A` budgets (`reqsA_x_le` … `hcountA9`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RR49A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RapWalkX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WalkBridgeX9
import Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BudLenJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (cc notC prodL)
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (pairRecsB)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (CSt)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (csIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.Jet.FibreJ8 (effP)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)

noncomputable section

/-! ## 1. The compute record counts -/

/-- The per-row cap of each balance of the twin. -/
def capB9 : Bal → ℕ
  | .x => 3
  | .p => 2
  | .s => 2

theorem cnt_le9 (bl : Bal) :
    ∀ j ∈ statesX9, (((slotsX9 : List (SlotX ℚ)).map (ReadIOJ8.cntS j bl)).sum ≤ capB9 bl) := by
  cases bl <;> decide +kernel

theorem states_sub9 : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ x ∈ S.ents, ∀ i ∈ x.states, i ∈ statesX9 := by
  decide +kernel

section Row
variable {F : Type} [Field F] [DecidableEq F] {env : Env F} {j : ℕ}

theorem act_zero9 (hOH : OneHotAt9 env j) {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ)))
    {x : EntX ℚ} (hx : x ∈ S.ents) (hj : j ∉ x.states) : evalQX x.act env = 0 := by
  simp only [EntX.act, evalQX]
  rw [evalQX_selS_zero _ (fun i hi => hOH.zero (states_sub9 S hS x hx i hi) (fun h => hj (h ▸ hi))),
    zero_mul]

theorem pair_flag9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) {S : SlotX ℚ}
    (hS : S ∈ (slotsX9 : List (SlotX ℚ))) {fl : ℕ} {a c : List RE} {b' : Bal}
    (hp : S.pair = some (fl, a, c, b')) (hf : env.trace fl = 1) : j ∈ S.pairStates := by
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · simp [slot0X9, extSlot, slot0X] at hp
  · simp [slot1X9, extSlot, slot1X] at hp
  · simp only [slot2X9, extSlot, slot2X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    by_contra hj
    have h5 : j ≠ 5 := fun h => hj (by simp [slot2X9, extSlot, slot2X, h])
    have h12 : j ≠ 12 := fun h => hj (by simp [slot2X9, extSlot, slot2X, h])
    have h125 : j ≠ sS10S := fun h => hj (by simp [slot2X9, extSlot, slot2X, h])
    have a := arith_of_base9 hB (g := prGateX9) (by decide +kernel)
    have e5 : env.trace 5 = 0 := hOH.zero (by decide +kernel) (Ne.symm h5)
    have e12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (Ne.symm h12)
    have e125 : env.trace sS10S = 0 := hOH.zero (by decide +kernel) (Ne.symm h125)
    simp only [prGateX9, prGateX, prodL, List.foldr, cc, notC, evalQX, Rat.cast_one, e5, e12, e125] at a
    have : env.trace prX = 0 := by linear_combination a
    rw [this] at hf; exact zero_ne_one hf
  · simp only [slot3X9, extSlot, slot3X, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    by_contra hj
    have h5 : j ≠ 5 := fun h => hj (by simp [slot3X9, extSlot, slot3X, h])
    have a := arith_of_base9 hB (g := pr2GateX) (by decide +kernel)
    have e5 : env.trace 5 = 0 := hOH.zero (by decide +kernel) (Ne.symm h5)
    simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one, e5] at a
    have : env.trace pr2X = 0 := by linear_combination a
    rw [this] at hf; exact zero_ne_one hf

theorem slot_count_le9 (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) (bl : Bal) {S : SlotX ℚ}
    (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    (((S.ents.filter fun x => decide (x.bal = bl)).filter fun x => decide (evalQX x.act env = 1)).map
      (·.rcd) ++ pairRecsB env bl S).length ≤ ReadIOJ8.cntS j bl S := by
  rw [List.length_append, List.length_map, List.filter_filter]
  unfold ReadIOJ8.cntS
  refine Nat.add_le_add ?_ ?_
  · refine ReadIOJ8.filter_len_mono _ _ _ fun x hxS hx => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    refine ⟨hx.2, ?_⟩
    by_contra hj
    rw [act_zero9 hOH hS hxS hj] at hx
    exact zero_ne_one hx.1
  · unfold pairRecsB
    cases hp : S.pair with
    | none => simp
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      simp only
      split_ifs with h1 h2
      · simp
      · exact absurd ⟨h1.1, pair_flag9 hB hOH hS hp h1.2⟩ h2
      · simp
      · simp

/-- **A twin row in a chip state `j` consumes at most `capB9 bl` records into `bl`.** -/
theorem consQX9_length_le (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env j) (hj : j ∈ statesX9) (bl : Bal) :
    (CompReqsX9.consQX9 env bl).length ≤ capB9 bl := by
  unfold CompReqsX9.consQX9
  rw [List.length_flatMap]
  refine le_trans ?_ (cnt_le9 bl j hj)
  exact List.sum_le_sum fun S hS => slot_count_le9 hB hOH bl hS

end Row

section Comp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chalV pubVal : ℕ → ZMod p}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

/-- **On an accepted twin compute trace, balance `bl` has at most `capB9 bl · n` compute requests.** -/
theorem compReqsX9_length_le
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit) P)
    (hp : 20 < p) (bl : Bal) :
    (CompReqsX9.compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl).length ≤ capB9 bl * n := by
  unfold CompReqsX9.compReqsX9
  rw [List.length_flatMap]
  calc _ ≤ ((List.range n).map fun _ => capB9 bl).sum := by
        refine List.sum_le_sum fun i hi => ?_
        have hi' : i < n := List.mem_range.mp hi
        rw [List.length_map]
        have e : CompReqsX9.envsN9 hn nodes orbit chalV pubVal P i =
            Env.viaPerm permX9 (TeleC.rEF nodes chalV pubVal orbit P ⟨i, hi'⟩) := by
          simp [CompReqsX9.envsN9, TeleC.envsN, hi']
        have hB : BaseHoldsX9 (CompReqsX9.envsN9 hn nodes orbit chalV pubVal P i) := by
          rw [e]
          exact RowSemSatX9.baseX9_of_sat hn nodes b δ chalV pubVal orbit P hsat.1 _
            (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.mem_rowNodeSet _ _)
        have hc : 20 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hp
        exact consQX9_length_le hB (RapWalkX9.stX9_spec hB hc) (WalkBridgeX9.csIdx_mem _) bl
    _ = capB9 bl * n := by simp [mul_comm]

end Comp

section CompOf
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K)

/-- **The coin-free compute list of a `J-9 A` trace**: at most `capB9 bl · n` records. -/
theorem compReqsOf9_length_le (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb tr chalV pubVal))
    (hp : 20 < p) (bl : Bal) :
    (CompReqsX9.compReqsOf9 (K := K) Pb tr bl).length ≤ capB9 bl * Pb.n := by
  rw [← CompReqsX9.compReqsX9_eq_of9 Pb tr chalV pubVal bl]
  exact compReqsX9_length_le hsat hp bl

end CompOf

/-! ## 2. -/

section Lanes
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (b : Basis (Fin 3) (ZMod p) K)

theorem axLimbReqsOf_length (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) :
    (axLimbReqsOf b Pb tr : List (Fin 8 → K)).length = Pb.nX := by
  simp [axLimbReqsOf, AxisChipJ9.axLimbReqs]

theorem axPathReqsOf_length_le (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) :
    (axPathReqsOf b Pb tr : List (Fin 5 → K)).length ≤ Pb.nX := by
  unfold axPathReqsOf AxisChipJ9.axPathReqs
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange Pb.nX).map fun _ => 1).sum :=
        List.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = Pb.nX := by simp

theorem axTagProvsOf_length_le (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) :
    (axTagProvsOf b Pb tr : List ((Fin 8 → K) × K)).length ≤ Pb.nX := by
  unfold axTagProvsOf AxisChipJ9.axTagProvs
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange Pb.nX).map fun _ => 1).sum :=
        List.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = Pb.nX := by simp

theorem splitProvsOf_length_le (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) :
    (splitProvsOf b Pb tr : List ((Fin 8 → K) × K)).length ≤ 2 * Pb.nS := by
  unfold splitProvsOf SplitChipJ9.splitProvs
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange Pb.nS).map fun _ => 2).sum :=
        List.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = 2 * Pb.nS := by simp [mul_comm]

theorem atomIncProvs_length_le9 {F K' : Type} [Field F] [Field K'] [Algebra F K'] [DecidableEq F]
    (b' : Basis (Fin 3) F K') {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K') (Q : Fin w → F[X]) : (atomIncProvs b' nodes orbit chals pubs Q).length ≤ n := by
  unfold atomIncProvs
  exact (AcceptsJ8P.length_flatMap_ite_le _ _ _).trans (by simp)

end Lanes

/-! ## 3. The budgets at `RR49A`'s lists -/

section Budgets
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

variable {Pb : PubJ9A p} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g : ℕ}

theorem reqsA_length (gA : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (bl : Bal) :
    (RR49A.reqsA δ b gA Pb tr bl).length =
      (CompReqsX9.compReqsOf9 (K := K) Pb tr bl).length + (RR49A.extA b gA Pb tr bl).length := by
  unfold RR49A.reqsA
  rw [List.length_map, List.length_append]

/-- **`budX`** at `RR49A`. -/
theorem reqsA_x_le (hp : 20 < p) (hB : BudJ9A Pb r (g + r.N)) (gA : Bool) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb tr chalV pubVal)) :
    (RR49A.reqsA δ b gA Pb tr .x).length ≤
      3 * (RR49A.rowsB r).N + (RR49A.rowsB r).W + (RR49A.rowsB r).rd := by
  rw [reqsA_length]
  have h1 := compReqsOf9_length_le (K := K) δ b Pb tr chalV pubVal hsat hp .x
  have h2 : (RR49A.extA b gA Pb tr .x).length = Pb.nW + RealIOJ8.jCount Nock.Jet.ChipJ8.entsX Pb.lay := by
    simp only [RR49A.extA, byBal, RealIOJ8.extT]
    erw [List.length_append, RealIOJ8.walkXReqs_length, RealIOJ8.jRd_length]
  simp only [capB9] at h1
  have := hB.x1
  simp only [RR49A.rowsB]
  omega

theorem provsA_x_le (hB : BudJ9A Pb r (g + r.N)) (gA gS : Bool) :
    (liftP (δ := δ) (RR49A.provsA b gA gS Pb tr .x)).length ≤ (RR49A.rowsB r).D := by
  simp only [liftP, List.length_map]
  show (CellTwinKW.cellProvsW b Pb.nodesC Pb.orbitC _ _ _).length ≤ r.D
  simp only [CellTwinKW.cellProvsW, List.length_map, List.length_finRange]
  exact hB.x2

/-- **`budP`** at `RR49A`. -/
theorem reqsA_p_le (hp : 20 < p) (hB : BudJ9A Pb r (g + r.N)) (gA : Bool) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb tr chalV pubVal)) :
    (RR49A.reqsA δ b gA Pb tr .p).length ≤ 2 * (RR49A.rowsB r).N := by
  rw [reqsA_length]
  have h1 := compReqsOf9_length_le (K := K) δ b Pb tr chalV pubVal hsat hp .p
  have h2 : (RR49A.extA b gA Pb tr .p).length ≤ Pb.nX := by
    cases gA
    · simp [RR49A.extA, byBal]
    · simp only [RR49A.extA, byBal, ↓reduceIte]
      exact axPathReqsOf_length_le b Pb tr
  simp only [capB9] at h1
  have := hB.p1
  simp only [RR49A.rowsB]
  omega

theorem provsA_p_le (hB : BudJ9A Pb r (g + r.N)) (gA gS : Bool) :
    (liftP (δ := δ) (RR49A.provsA b gA gS Pb tr .p)).length ≤ 2 * (RR49A.rowsB r).W := by
  simp only [liftP, List.length_map]
  show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
  rw [RealIOJ8.walkPProvs_length]
  have := hB.p2
  omega

/-- **`budS`** at `RR49A`: requests (`g' = g + N + AX`). -/
theorem reqsA_s_le (hp : 20 < p) (hB : BudJ9A Pb r (g + r.N)) (gA : Bool) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb tr chalV pubVal)) :
    (RR49A.reqsA δ b gA Pb tr .s).length ≤
      (RR49A.rowsB r).N + 2 * (RR49A.rowsB r).J + (g + r.N + r.AX) := by
  rw [reqsA_length]
  have h1 := compReqsOf9_length_le (K := K) δ b Pb tr chalV pubVal hsat hp .s
  have h2 : (RR49A.extA b gA Pb tr .s).length ≤
      Pb.regs.length + Pb.nX + (RealIOJ8.jCount Nock.Jet.ChipJ8.ents0T Pb.lay +
        RealIOJ8.jCount Nock.Jet.ChipJ8.ents1T Pb.lay) := by
    simp only [RR49A.extA, byBal]
    erw [List.length_append, List.length_append, RealIOJ8.jCons_length]
    refine Nat.add_le_add (Nat.add_le_add (Nat.le_of_eq (by unfold pinCons; exact List.length_map _)) ?_) (Nat.le_refl _)
    cases gA
    · exact Nat.zero_le _
    · simp only [↓reduceIte]
      exact Nat.le_of_eq (axLimbReqsOf_length b Pb tr)
  simp only [capB9] at h1
  have := hB.s1
  simp only [RR49A.rowsB]
  omega

/-- **`budS`** at `RR49A`: providers. -/
theorem provsA_s_le (hB : BudJ9A Pb r (g + r.N)) (gA gS : Bool) :
    (effP (liftP (δ := δ) (RR49A.provsA b gA gS Pb tr .s))).length ≤
      (RR49A.rowsB r).calls + (RR49A.rowsB r).heads + (RR49A.rowsB r).blocks + (RR49A.rowsB r).J := by
  refine (List.length_filter_le _ _).trans ?_
  simp only [liftP, List.length_map]
  show (jProv b Pb.nodesJ Pb.orbitJ _ _ Pb.lay tr.J ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
        (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
          else []) ++
        (if gA then axTagProvsOf b Pb tr else []) ++ (if gS then splitProvsOf b Pb tr else []))).length ≤ _
  have h0 : (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
      else ([] : List ((Fin 8 → K) × K))).length ≤ 2 * Pb.nV := by
    split_ifs
    · simp [pad8, RealIOJ8.walkPProvs_length]
    · simp
  simp only [List.length_append, pad8, List.length_map, RealIOJ8.jProv_length, RealIOJ8.walkPProvs_length] at h0 ⊢
  have h1 := atomIncProvs_length_le9 b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A
  have h2 : (if gA then axTagProvsOf b Pb tr else ([] : List ((Fin 8 → K) × K))).length ≤ Pb.nX := by
    split_ifs
    · exact axTagProvsOf_length_le b Pb tr
    · simp
  have h3 : (if gS then splitProvsOf b Pb tr else ([] : List ((Fin 8 → K) × K))).length ≤ 2 * Pb.nS := by
    split_ifs
    · exact splitProvsOf_length_le b Pb tr
    · simp
  have := hB.s2
  simp only [RR49A.rowsB]
  omega

/-- **`hcount`** at `RR49A` from the budgets and the caps below `p`. -/
theorem hcountA9 (hp : 20 < p) (hB : BudJ9A Pb r (g + r.N)) (gA : Bool) (chalV pubVal : ℕ → ZMod p)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX9 δ b Pb tr chalV pubVal))
    (hcap : 3 * (RR49A.rowsB r).N + (RR49A.rowsB r).W + (RR49A.rowsB r).rd < p ∧
      2 * (RR49A.rowsB r).N < p ∧ (RR49A.rowsB r).N + 2 * (RR49A.rowsB r).J + (g + r.N + r.AX) < p) :
    ∀ bl, (RR49A.reqsA δ b gA Pb tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (reqsA_x_le δ b hp hB gA chalV pubVal hsat) hcap.1
  · exact lt_of_le_of_lt (reqsA_p_le δ b hp hB gA chalV pubVal hsat) hcap.2.1
  · exact lt_of_le_of_lt (reqsA_s_le δ b hp hB gA chalV pubVal hsat) hcap.2.2

end Budgets

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.BudLenJ9A
#print axioms cnt_le9
#print axioms consQX9_length_le
#print axioms compReqsX9_length_le
#print axioms compReqsOf9_length_le
#print axioms axLimbReqsOf_length
#print axioms axPathReqsOf_length_le
#print axioms axTagProvsOf_length_le
#print axioms splitProvsOf_length_le
#print axioms reqsA_x_le
#print axioms provsA_x_le
#print axioms reqsA_p_le
#print axioms provsA_p_le
#print axioms reqsA_s_le
#print axioms provsA_s_le
#print axioms hcountA9
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.BudLenJ9A
