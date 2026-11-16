/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonSideP1.lean

 **Completeness of the compute side templates `canonC` and `canonC2`.**

 * §1 `TC`: expressions that read only current-row trace columns; evaluation is then independent of the challenge
 and public vectors and of the next row (`eval_congr_TC`); the E8 / E9 gates are such expressions.
 * §2 the lift of the row-level facts `HonestSideCP1.canonCGates_honest` / `honest_canonC2'` to RAP satisfaction:
 a compute trace that interpolates the honest columns `trX` over the nodes satisfies `canonC` and `canonC2`
 (`canonC_of_polyX`, `canonC2_of_polyX`), given that every BFS row is in a P1 state with a P1 handle map.
 * §3 at the canonical layout (`canon_sides`): the two hypotheses `hCside`, `hC2side` of `canon_complete`.
 * §4 `canon_complete'`: `canon_complete` without them.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (trX polyX baseT flX llX trX_zero polyX_eval)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (rowAtWX)

noncomputable section

/-! ## 1. Expressions that read only the current row -/

section TC
variable {F : Type} [Field F]

/-- The expression reads only current-row trace columns (no challenge, public or next-row variable). -/
def TC : CoeffExpr F → Prop
  | .const _ => True
  | .var k _ => k = VarKind.traceCur
  | .add a b => TC a ∧ TC b
  | .sub a b => TC a ∧ TC b
  | .mul a b => TC a ∧ TC b
  | .neg a => TC a
  | .pow a _ => TC a

theorem eval_congr_TC : ∀ (e : CoeffExpr F), TC e → ∀ (env env' : Env F), env.trace = env'.trace →
    e.eval env = e.eval env'
  | .const _, _, _, _, _ => rfl
  | .var k i, h, env, env', ht => by
    have hk : k = VarKind.traceCur := h
    subst hk
    simp only [CoeffExpr.eval, ht]
  | .add a b, h, env, env', ht => by
    simp only [CoeffExpr.eval, eval_congr_TC a h.1 env env' ht, eval_congr_TC b h.2 env env' ht]
  | .sub a b, h, env, env', ht => by
    simp only [CoeffExpr.eval, eval_congr_TC a h.1 env env' ht, eval_congr_TC b h.2 env env' ht]
  | .mul a b, h, env, env', ht => by
    simp only [CoeffExpr.eval, eval_congr_TC a h.1 env env' ht, eval_congr_TC b h.2 env env' ht]
  | .neg a, h, env, env', ht => by
    simp only [CoeffExpr.eval, eval_congr_TC a h env env' ht]
  | .pow a n, h, env, env', ht => by
    simp only [CoeffExpr.eval, eval_congr_TC a h env env' ht]

theorem TC_cc (i : ℕ) : TC (cc (F := F) i) := rfl

theorem TC_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr F) (h : ∀ x ∈ l, TC (f x)) :
    TC (CoeffExpr.sumList l f) := by
  induction l with
  | nil => exact trivial
  | cons a l ih =>
    exact ⟨h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem TC_notC (i : ℕ) : TC (notC (F := F) i) := ⟨trivial, rfl⟩

theorem TC_ents : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)), ∀ x ∈ S.ents, TC (EntX.act x) := by
  intro S hS x hx
  have hsel : ∀ l : List ℕ, TC (selS (F := F) l) := fun l => TC_sumList l _ fun _ _ => rfl
  simp only [ChipHX.slotsX, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨hsel _, by simp [TC, notC, kcE, kbE, cc]⟩

theorem TC_actTot (S : SlotX F) (h : ∀ x ∈ S.ents, TC (EntX.act x)) : TC (actTotX S) := by
  unfold actTotX
  refine ⟨TC_sumList _ _ h, ?_⟩
  rcases hp : S.pair with _ | ⟨fl, a, b, bb⟩
  · simp only [TC]
  · simp only [TC, cc]

theorem TC_canonC2Gates : ∀ g ∈ canonC2Gates (F := F), TC g := by
  intro g hg
  unfold canonC2Gates at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨S, hS, hg⟩ := List.mem_flatMap.mp hg
    have h := TC_actTot S (TC_ents S hS)
    simp only [e8Slot, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;>
      exact ⟨⟨trivial, h⟩, rfl⟩
  · simp only [e9Gates, List.mem_map] at hg
    obtain ⟨k, -, rfl⟩ := hg
    exact ⟨rfl, rfl⟩

end TC

/-! ## 2. From the honest rows to RAP satisfaction -/

section Lift
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (b : Basis (Fin 3) (ZMod p) K) (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

theorem rowAtWX_eq (W : List (NTree SkelX)) (i : ℕ) (hi : i < W.length) :
    rowAtWX W (i + 1) = rowOfSkelX (W[i]'hi).label := by
  unfold rowAtWX
  simp [hi]

/-- The trace field of the honest polynomials' environment is `trX`, whatever the challenge and public vectors. -/
theorem envTrace_polyX (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p) (ln cnt acc : ℕ → K) {n : ℕ}
    (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (ω : ZMod p) (cv pv : ℕ → ZMod p) (i : Fin n) :
    (Reify.envOfTrace (polyX b δ H pd W chalV pubVal ln cnt acc nodes 123) ω (nodes i) cv pv).trace =
      trX b δ H pd W chalV pubVal ln cnt acc (i : ℕ) := by
  funext c
  by_cases hc : c < 123
  · rw [envOfTrace_trace _ _ _ _ _ hc]
    exact polyX_eval b δ H pd W chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ i
  · simp only [Reify.envOfTrace, hc, dite_false]
    exact (trX_zero b δ H pd W chalV pubVal ln cnt acc _ _ (by omega)).symm

variable (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p)
  (ln cnt acc : ℕ → K)

/-- **`canonC` at the honest columns**: if the compute trace interpolates `trX` over the canonical nodes, and every BFS
row is a P1 row with a P1 handle map, `canonC` is satisfied. -/
theorem canonC_of_polyX {n : ℕ} (hn : Pb.n = n) (hW : W.length = n)
    (hnodes : ∀ i : Fin Pb.n, Pb.nodes i = Pb.orbit.ω ^ (i : ℕ))
    (hinj : Function.Injective fun i : Fin n => Pb.orbit.ω ^ (i : ℕ))
    (htr : tr.C = polyX b δ H pd W chalV pubVal ln cnt acc (fun i : Fin n => Pb.orbit.ω ^ (i : ℕ)) 123)
    (hst : ∀ u ∈ W, P1State u.label.state) (hy : ∀ u ∈ W, P1Hyp H (rowOfSkelX u.label)) :
    (canonC b Pb).Satisfies (sideCQ tr) := by
  subst hn
  refine (expandChip_satisfies_iff_language canonCT b (fun _ => 0) (fun _ => 0) Pb.orbit
    (rowNodeSet Pb.nodes) (sideCQ tr)).mpr fun x hx => ?_
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff _ x).mp hx
  refine ⟨fun g hg => ?_, fun g hg => absurd hg List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
    fun g hg => absurd hg List.not_mem_nil⟩
  have hi : (i : ℕ) < W.length := by rw [hW]; exact i.isLt
  have hr := honestEnv_rowEnv H pd b δ W chalV pubVal ln cnt acc i
  rw [rowAtWX_eq W i hi] at hr
  have hmem : W[(i : ℕ)]'hi ∈ W := List.getElem_mem hi
  have key : RowEnv H pd (rowOfSkelX (W[(i : ℕ)]'hi).label) (flX (F := ZMod p) i) (llX W i)
      (Reify.envOfTrace (sideCQ tr) Pb.orbit.ω (Pb.nodes i) (fun _ => 0) (fun _ => 0)) := by
    intro c hc
    have hc' : c < (canonCT (F := ZMod p)).width 3 := by rw [canonCT_width]; exact hc
    rw [envOfTrace_trace _ _ _ _ _ hc']
    have e1 : ((sideCQ tr) ⟨c, hc'⟩).eval (Pb.nodes i) =
        (polyX b δ H pd W chalV pubVal ln cnt acc (fun i : Fin Pb.n => Pb.orbit.ω ^ (i : ℕ)) 123
          ⟨c, by omega⟩).eval ((fun i : Fin Pb.n => Pb.orbit.ω ^ (i : ℕ)) i) := by
      rw [hnodes i, ← htr]; rfl
    rw [e1, polyX_eval b δ H pd W chalV pubVal ln cnt acc _ hinj]
    exact hr c hc
  exact canonCGates_honest H pd (W[(i : ℕ)]'hi).label (hst _ hmem) (hy _ hmem) (flX (F := ZMod p) i)
    (llX W i) _ key g hg

/-- **`canonC2` at the honest columns**, along the BFS of a tree `t`. -/
theorem canonC2_of_polyX {n : ℕ} (t : NTree SkelX) (α : K) (hn : Pb.n = n) (hW : (bfsForest [t]).length = n)
    (hnodes : ∀ i : Fin Pb.n, Pb.nodes i = Pb.orbit.ω ^ (i : ℕ))
    (hinj : Function.Injective fun i : Fin n => Pb.orbit.ω ^ (i : ℕ))
    (htr : tr.C = polyX b δ H pd (bfsForest [t]) chalV pubVal (Nock.NockVMROM.Thm54.VclL.HonestTraceX.lnW α)
      (Nock.NockVMROM.Thm54.VclL.HonestTraceX.cntW (bfsForest [t]) α) acc
      (fun i : Fin n => Pb.orbit.ω ^ (i : ℕ)) 123)
    (hst : ∀ u ∈ bfsForest [t], P1State u.label.state) :
    (canonC2 b Pb).Satisfies (sideC2Q tr) := by
  subst hn
  refine (expandChip_satisfies_iff_language canonC2T b (fun _ => 0) (fun _ => 0) Pb.orbit
    (rowNodeSet Pb.nodes) (sideC2Q tr)).mpr fun x hx => ?_
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff _ x).mp hx
  refine ⟨fun g hg => ?_, fun g hg => absurd hg List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
    fun g hg => absurd hg List.not_mem_nil⟩
  have hi : (i : ℕ) < (bfsForest [t]).length := by rw [hW]; exact i.isLt
  have hmem : (bfsForest [t])[(i : ℕ)]'hi ∈ bfsForest [t] := List.getElem_mem hi
  have hs : P1State (rowAtWX (bfsForest [t]) ((i : ℕ) + 1)).st := by
    rw [rowAtWX_eq _ _ hi, rowOfSkelX_st]; exact hst _ hmem
  have e1 : Reify.envOfTrace (sideC2Q tr) Pb.orbit.ω (Pb.nodes i) (fun _ => 0) (fun _ => 0) =
      Reify.envOfTrace tr.C Pb.orbit.ω (Pb.nodes i) (fun _ => 0) (fun _ => 0) :=
    envOfTrace_cast (canonC2T_width (F := ZMod p)) tr.C _ _ _ _
  have e2 := envTrace_polyX b δ H pd (bfsForest [t]) chalV pubVal
    (Nock.NockVMROM.Thm54.VclL.HonestTraceX.lnW α)
    (Nock.NockVMROM.Thm54.VclL.HonestTraceX.cntW (bfsForest [t]) α) acc
    (fun i : Fin Pb.n => Pb.orbit.ω ^ (i : ℕ)) hinj Pb.orbit.ω (fun _ => 0) (fun _ => 0) i
  have h0 := honest_canonC2' H pd b δ t chalV pubVal α acc (i : ℕ) hs g hg
  have key : g.eval (Reify.envOfTrace (sideC2Q tr) Pb.orbit.ω (Pb.nodes i) (fun _ => 0) (fun _ => 0)) = 0 := by
    refine (eval_congr_TC g (TC_canonC2Gates g hg) _ _ ?_).trans h0
    rw [e1, hnodes i, htr]
    exact e2
  exact key

end Lift

/-! ## 3. At the canonical layout -/

section Canon
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

theorem bnd_kind_ne_two {H : Noun → ℕ × ℕ} (hH : HonestCompX.HdlOK p H) {x : Noun}
    (hx : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound.Bnd p x) : (H x).1 ≠ 2 := by
  cases x with
  | atom a =>
    have h : a < p := hx
    rw [hH.small a h]; simp
  | cell l r => rw [hH.cell l r]; simp

theorem p1State_of_stP1 {st : StateX} (h : st ∈ stP1) : P1State st := by
  simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold P1State
  rcases h with h | h | h | h | h | h <;> simp [h]

theorem p1Hyp_of_row {H : Noun → ℕ × ℕ} (hH : HonestCompX.HdlOK p H) (sk : SkelX)
    (hr : RowP1 p (rowOfSkelX sk)) : P1Hyp H (rowOfSkelX sk) := by
  have hst : sk.state ∈ stP1 := by rw [← rowOfSkelX_st]; exact hr.st
  have h0 : H (.atom 0) = (0, 0) := hH.small 0 (Fact.out : p.Prime).pos
  refine ⟨h0, fun j hj => ?_, ?_⟩
  · refine bnd_kind_ne_two hH (hr.bnd _ ?_)
    simp only [rowHandleNounsX]
    interval_cases j <;> simp [HonestCompX.hN]
  · have hm : ∃ a, (rowOfSkelX sk).m = .atom a := by
      simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with h | h | h | h | h | h <;> simp [rowOfSkelX, h]
    obtain ⟨a, ha⟩ := hm
    have hb := hr.bnd (rowOfSkelX sk).m (by simp [rowHandleNounsX])
    rw [ha] at hb ⊢
    have h : a < p := hb
    rw [hH.small a h]

/-- **The compute side templates hold at the canonical trace.** -/
theorem canon_sides (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) (sz : P8PublicClaim → SizesP1)
    (hsz : sz (cJ s f r) = szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1) (χ : Coins frameJ8 K) :
    (canonC b (canonPb hpG sz (cJ s f r))).Satisfies
      (sideCQ (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)) ∧
    (canonC2 b (canonPb hpG sz (cJ s f r))).Satisfies
      (sideC2Q (trCanon δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
        (j8DataCanon_ok p Rg Rt hgen).acs_pos (oP1 hpG hgen hR) χ)) := by
  have hn : (sz (cJ s f r)).n = (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length := by rw [hsz]; rfl
  have hnC : (sz (cJ s f r)).nC = (j8DataCanon p Rg Rt hgen).cells.length := by rw [hsz]; rfl
  have hnW : (sz (cJ s f r)).nW = (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length := by
    rw [hsz]; rfl
  have hA1 : (j8DataCanon p Rg Rt hgen).acs.length = 1 := by rw [canon_acs hpG hgen hc]; rfl
  have hht : htJ8 (j8DataCanon p Rg Rt hgen) = (sz (cJ s f r)).ht :=
    htJ8_p1 _ (canon_jrows hpG hgen hc) hA1 (canon_preads hpG hgen hc) _ hn hnC hnW
  have ho : HEq (oP1 hpG hgen hR) (canonPb hpG sz (cJ s f r)).orbit :=
    orbitG_heq hpG hht _ _ (SizesP1.one_le_ht _) (SizesP1.ht_le_32 _)
  have etr := trCanon_congr δ b (j8DataCanon p Rg Rt hgen) (j8DataCanon_ok p Rg Rt hgen).cells_pos
    (j8DataCanon_ok p Rg Rt hgen).acs_pos hht (oP1 hpG hgen hR) (canonPb hpG sz (cJ s f r)).orbit ho χ
  have hleN : (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length ≤ 2 ^ (sz (cJ s f r)).ht := by
    rw [← hn]; exact le_trans (le_max_left _ _) (sz (cJ s f r)).fit_ht
  have hinj := powN_inj (canonPb hpG sz (cJ s f r)).orbit hleN
  have hrows := rows_p1 hpG hgen hc
  have hrow : ∀ u ∈ bfsForest [(j8DataCanon p Rg Rt hgen).t], RowP1 p (rowOfSkelX u.label) := fun u hu =>
    hrows _ (by
      show rowOfSkelX u.label ∈ (ComplJ8Data.rowsOfT t).toList
      simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.mem_map]
      exact ⟨u, hu, rfl⟩)
  have hH : HonestCompX.HdlOK p (j8DataCanon p Rg Rt hgen).H :=
    ComplJ8Data.hdlOK_hdlP p (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).acs
  have hst : ∀ u ∈ bfsForest [(j8DataCanon p Rg Rt hgen).t], P1State u.label.state := fun u hu => by
    have := (hrow u hu).st
    rw [rowOfSkelX_st] at this
    exact p1State_of_stP1 this
  have hy : ∀ u ∈ bfsForest [(j8DataCanon p Rg Rt hgen).t], P1Hyp (j8DataCanon p Rg Rt hgen).H (rowOfSkelX u.label) :=
    fun u hu => p1Hyp_of_row hH u.label (hrow u hu)
  rw [etr]
  refine ⟨?_, ?_⟩
  · exact canonC_of_polyX b δ (j8DataCanon p Rg Rt hgen).H (j8DataCanon p Rg Rt hgen).pd _ _ _ _ _ _ _ _
      hn rfl (fun i => rfl) hinj rfl hst hy
  · exact canonC2_of_polyX b δ (j8DataCanon p Rg Rt hgen).H (j8DataCanon p Rg Rt hgen).pd _ _ _ _ _
      (j8DataCanon p Rg Rt hgen).t _ hn rfl (fun i => rfl) hinj rfl hst

/-! ## 4. `canon_complete'` -/

open Classical in
/-- **`canon_complete'`:** on a P1 claim whose run is `genX … = some (t, r)`, with `Rows31` and `RootsLeafOK` of the
canonical data: at every good coin the canonical transcript is accepted by `AcceptsCanon2`, and if the walk has
no path read then the extra pin (E10) holds at that transcript; also `Pr[¬ Good] ≤ ε_c`. The compute-side
templates `canonC` and `canonC2` are discharged internally. -/
theorem canon_complete' (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : Rows31 (j8DataCanon p Rg Rt hgen)) (hL : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots)
    (sz : P8PublicClaim → SizesP1)
    (hsz : sz (cJ s f r) = szCanon p Rg Rt hgen (canon_fit_of_rows31 hgen hR).1) :
    let D := j8DataCanon p Rg Rt hgen
    let hC := (j8DataCanon_ok p Rg Rt hgen).cells_pos
    let hA := (j8DataCanon_ok p Rg Rt hgen).acs_pos
    let Pb := canonPb hpG sz (cJ s f r)
    let B := BP1 δ b hpG hgen hR (K := K)
    (∀ χ, B.Good χ →
      AcceptsCanon2 δ b hpG sz Pb Rg.R (cJ s f r) χ (msgCanon δ b D hC hA (oP1 hpG hgen hR) χ)
        (trCanon δ b D hC hA (oP1 hpG hgen hR) χ) (axP1 δ b D hC Pb.orbit χ) B.rows B.g ∧
      (walkRoots D.reads = [] →
        ((trCanon δ b D hC hA (oP1 hpG hgen hR) χ).W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, Pb.hnW⟩) = 0)) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) :=
  canon_complete δ b hpG hgen hc hR hL sz hsz (fun χ => (canon_sides δ b hpG hgen hc hR sz hsz χ).1)
    (fun χ => (canon_sides δ b hpG hgen hc hR sz hsz χ).2)

end Canon

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canonC_of_polyX
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canonC2_of_polyX
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canon_sides
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1.canon_complete'
