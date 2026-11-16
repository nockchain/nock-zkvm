/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RoundsCompP1.lean

 **Trace uniqueness on the P1 fragment: the compute chip's round-1 columns.**

 Two traces of `computeChipVCLHX` at one coin vector (public vectors may differ), with equal round-0 columns
 (the first `69`), satisfying the side gates `canonC2` (E8, E9), have equal columns `69 .. 122`, given that the
 slot denominators that matter are nonzero.

 * §1 read sets: a Boolean predicate on gate expressions that read only round-0 columns and the coins, and the
 congruence of the evaluation under it.
 * §2 the slot inverses: `inv·N = M` with `N`, `M` read-set-round-0; inactive slots are `0` by E8.
 * §3 the six accumulator limb families, by induction from the first row (prefix sums).
 * §4 the compute walk: `ln`, `cnt`, `acc` by induction, `wInv` by `wInv·(cnt − ln) = 1`, and `0` at the last row
 by E9.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS chalGammaW chalAlphaW pubIC pubSeed pubOut mapC mapM sumM)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (sumQ qγH qρH)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX slotsX_cast slotX_of_sat)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (mem_rowNodeSet traceNext_eq envOfTrace_trace envOfTrace_traceNext)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

/-! ## 1. Read sets and congruence -/

section ReadSet

/-- A coefficient expression that reads only trace columns below `B` (the next row too iff `nx`) and the coins
(iff `ch`); never a public. -/
def rdC {G : Type} (nx ch : Bool) (B : ℕ) : CoeffExpr G → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < B)
  | .var .traceNext i => nx && decide (i < B)
  | .var .challenge _ => ch
  | .var .publicVal _ => false
  | .add a b => rdC nx ch B a && rdC nx ch B b
  | .sub a b => rdC nx ch B a && rdC nx ch B b
  | .mul a b => rdC nx ch B a && rdC nx ch B b
  | .neg a => rdC nx ch B a
  | .pow a _ => rdC nx ch B a

/-- A mixed expression whose `𝕂`-variables are coins (iff `ch`) and whose base parts satisfy `rdC`. -/
def rdM {G : Type} (nx ch : Bool) (B : ℕ) : MixedExpr G → Bool
  | .Var .challenge _ => ch
  | .Var _ _ => false
  | .Lift g => rdC nx ch B g
  | .Scale g u => rdC nx ch B g && rdM nx ch B u
  | .Const _ => true
  | .Add a b => rdM nx ch B a && rdM nx ch B b
  | .Sub a b => rdM nx ch B a && rdM nx ch B b
  | .Neg a => rdM nx ch B a
  | .Mul a b => rdM nx ch B a && rdM nx ch B b
  | .Pow a _ => rdM nx ch B a

theorem rdC_mapC {G F : Type} (φ : G → F) (nx ch : Bool) (B : ℕ) (g : CoeffExpr G) :
    rdC nx ch B (mapC φ g) = rdC nx ch B g := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [mapC, rdC, iha, ihb]
  | sub a b iha ihb => simp only [mapC, rdC, iha, ihb]
  | mul a b iha ihb => simp only [mapC, rdC, iha, ihb]
  | neg a ih => simp only [mapC, rdC, ih]
  | pow a n ih => simp only [mapC, rdC, ih]

theorem rdM_mapM {G F : Type} (φ : G → F) (nx ch : Bool) (B : ℕ) (g : MixedExpr G) :
    rdM nx ch B (mapM φ g) = rdM nx ch B g := by
  induction g with
  | Var k i => cases k <;> rfl
  | Lift g => simp only [mapM, rdM, rdC_mapC]
  | Scale g u ih => simp only [mapM, rdM, rdC_mapC, ih]
  | Const c => rfl
  | Add a b iha ihb => simp only [mapM, rdM, iha, ihb]
  | Sub a b iha ihb => simp only [mapM, rdM, iha, ihb]
  | Neg a ih => simp only [mapM, rdM, ih]
  | Mul a b iha ihb => simp only [mapM, rdM, iha, ihb]
  | Pow a n ih => simp only [mapM, rdM, ih]

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem eval_congr_C {nx ch : Bool} {B : ℕ} {eF eF' : Env F} (hc : ∀ j < B, eF.trace j = eF'.trace j)
    (hn : nx = true → ∀ j < B, eF.traceNext j = eF'.traceNext j) (hch : ch = true → eF.chal = eF'.chal) :
    ∀ g : CoeffExpr F, rdC nx ch B g = true → g.eval eF = g.eval eF' := by
  intro g
  induction g with
  | const c => intro _; rfl
  | var k i =>
    intro h
    cases k with
    | traceCur => simp only [rdC, decide_eq_true_eq] at h; exact hc i h
    | traceNext =>
      simp only [rdC, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hn h.1 i h.2
    | challenge => exact congrFun (hch h) i
    | publicVal => simp [rdC] at h
  | add a b iha ihb => intro h; simp only [rdC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | sub a b iha ihb => intro h; simp only [rdC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | mul a b iha ihb => intro h; simp only [rdC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | neg a ih => intro h; simp only [rdC] at h; simp only [CoeffExpr.eval, ih h]
  | pow a n ih => intro h; simp only [rdC] at h; simp only [CoeffExpr.eval, ih h]

theorem eval_congr_M {nx ch : Bool} {B : ℕ} {eK eK' : Env K} {eF eF' : Env F}
    (hc : ∀ j < B, eF.trace j = eF'.trace j)
    (hn : nx = true → ∀ j < B, eF.traceNext j = eF'.traceNext j) (hch : ch = true → eF.chal = eF'.chal)
    (hchK : ch = true → eK.chal = eK'.chal) :
    ∀ g : MixedExpr F, rdM nx ch B g = true → g.eval eK eF = g.eval eK' eF' := by
  intro g
  induction g with
  | Var k i =>
    intro h
    cases k with
    | challenge => exact congrFun (hchK h) i
    | traceCur => simp [rdM] at h
    | traceNext => simp [rdM] at h
    | publicVal => simp [rdM] at h
  | Lift g => intro h; simp only [rdM] at h; simp only [MixedExpr.eval, eval_congr_C hc hn hch g h]
  | Scale g u ih =>
    intro h; simp only [rdM, Bool.and_eq_true] at h
    simp only [MixedExpr.eval, eval_congr_C hc hn hch g h.1, ih h.2]
  | Const c => intro _; rfl
  | Add a b iha ihb => intro h; simp only [rdM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Sub a b iha ihb => intro h; simp only [rdM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Neg a ih => intro h; simp only [rdM] at h; simp only [MixedExpr.eval, ih h]
  | Mul a b iha ihb => intro h; simp only [rdM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Pow a n ih => intro h; simp only [rdM] at h; simp only [MixedExpr.eval, ih h]

/-- The `ℚ`-template evaluation `evalQX` under a read set. -/
theorem evalQX_congr {nx ch : Bool} {B : ℕ} {eF eF' : Env F} (hc : ∀ j < B, eF.trace j = eF'.trace j)
    (hn : nx = true → ∀ j < B, eF.traceNext j = eF'.traceNext j) (hch : ch = true → eF.chal = eF'.chal)
    (g : CoeffExpr ℚ) (hg : rdC nx ch B g = true) : evalQX g eF = evalQX g eF' := by
  rw [evalQX_eq, evalQX_eq, ← eval_mapC_cast g eF, ← eval_mapC_cast g eF']
  exact eval_congr_C hc hn hch _ (by rw [rdC_mapC]; exact hg)

/-- The `ℚ`-template mixed evaluation `evalMQ` under a read set. -/
theorem evalMQ_congr {nx ch : Bool} {B : ℕ} {eK eK' : Env K} {eF eF' : Env F}
    (hc : ∀ j < B, eF.trace j = eF'.trace j)
    (hn : nx = true → ∀ j < B, eF.traceNext j = eF'.traceNext j) (hch : ch = true → eF.chal = eF'.chal)
    (hchK : ch = true → eK.chal = eK'.chal) (g : MixedExpr ℚ) (hg : rdM nx ch B g = true) :
    evalMQ g eK eF = evalMQ g eK' eF' := by
  rw [← eval_mapM_cast g eK eF, ← eval_mapM_cast g eK' eF']
  exact eval_congr_M hc hn hch hchK _ (by rw [rdM_mapM]; exact hg)

end ReadSet

/-! ## 1b. The three recurrence shapes -/

section Recur

/-- Prefix sums: `a 0 = c`, `a (i+1) = a i + t i` with equal `t` agree. -/
theorem rec_unique {G : Type} [AddCommGroup G] (n : ℕ) (a a' t t' : ℕ → G) (c : G) (h0 : a 0 = c) (h0' : a' 0 = c)
    (ht : ∀ i, i + 1 < n → t i = t' i) (hs : ∀ i, i + 1 < n → a (i + 1) = a i + t i)
    (hs' : ∀ i, i + 1 < n → a' (i + 1) = a' i + t' i) : ∀ i, i < n → a i = a' i := by
  intro i
  induction i with
  | zero => intro _; rw [h0, h0']
  | succ k ih => intro hi; rw [hs k hi, hs' k hi, ih (by omega), ht k hi]

end Recur


/-! ## 2. The slot inverses -/

section Slots
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- The factor of the inverse in the slot gate: `Σ act·den (+ pair)`. -/
def slotNQ (S : SlotX F) : Q F :=
  qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd)))
    (match S.pair with
     | some (fl, a, bb, _) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQX F δ a) (denQX F δ bb))
     | none => qconst F 0)

/-- The right-hand side of the slot gate: `Σ act (+ pair)`. -/
def slotMQ (S : SlotX F) : Q F :=
  qadd F (qlift F (CoeffExpr.sumList S.ents EntX.act))
    (match S.pair with
     | some (fl, a, bb, _) => qmul F δ (qlift F (cc fl)) (qadd F (denQX F δ a) (denQX F δ bb))
     | none => qconst F 0)

theorem slotGate_eq (S : SlotX F) :
    slotGateQX F δ S = qsub F (qmul F δ (qvar F .traceCur S.inv (some S.invIm)) (slotNQ δ S)) (slotMQ δ S) := rfl

theorem slotNM_rd : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
    rdM false true 69 (slotNQ δ S).1 = true ∧ rdM false true 69 (slotNQ δ S).2 = true ∧
    rdM false true 69 (slotMQ δ S).1 = true ∧ rdM false true 69 (slotMQ δ S).2 = true := by
  intro S hS
  simp only [ChipHX.slotsX, slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem actTot_rd : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)), rdC false false 69 (actTotX S) = true := by
  intro S hS
  simp only [ChipHX.slotsX, slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> rfl

theorem qval_congr (q : Q F) (h1 : rdM false true 69 q.1 = true) (h2 : rdM false true 69 q.2 = true)
    {e e' : Env F} (hc : ∀ j < 69, e.trace j = e'.trace j) (hch : e.chal = e'.chal) :
    Q.val δ q (Compute.TowerD.gatherEnv b e) e = Q.val δ q (Compute.TowerD.gatherEnv b e') e' := by
  have hK : (Compute.TowerD.gatherEnv b e).chal = (Compute.TowerD.gatherEnv b e').chal := by simp only [Compute.TowerD.gatherEnv, hch]
  simp only [Q.val, eval_congr_M hc (fun h => by simp at h) (fun _ => hch) (fun _ => hK) _ h1,
    eval_congr_M hc (fun h => by simp at h) (fun _ => hch) (fun _ => hK) _ h2]

/-- **The slot inverse is determined.** Equal round-0 columns and coins give equal `N`, `M`; an active slot with
`N ≠ 0` has `inv = M·N⁻¹`; an inactive slot is `0` (the side gate E8). -/
theorem slot_inv_eq (S : SlotX F) (hS : S ∈ (ChipHX.slotsX : List (SlotX F))) (e e' : Env F)
    (hc : ∀ j < 69, e.trace j = e'.trace j) (hch : e.chal = e'.chal)
    (g : Q.val δ (slotGateQX F δ S) (Compute.TowerD.gatherEnv b e) e = 0) (g' : Q.val δ (slotGateQX F δ S) (Compute.TowerD.gatherEnv b e') e' = 0)
    (hN : (actTotX S).eval e ≠ 0 → Q.val δ (slotNQ δ S) (Compute.TowerD.gatherEnv b e) e ≠ 0)
    (hz : (actTotX S).eval e = 0 → ∀ k < 3, e.trace (S.inv + k) = 0 ∧ e.trace (S.invIm + k) = 0)
    (hz' : (actTotX S).eval e' = 0 → ∀ k < 3, e'.trace (S.inv + k) = 0 ∧ e'.trace (S.invIm + k) = 0) :
    ∀ k < 3, e.trace (S.inv + k) = e'.trace (S.inv + k) ∧ e.trace (S.invIm + k) = e'.trace (S.invIm + k) := by
  have hA : (actTotX S).eval e = (actTotX S).eval e' :=
    eval_congr_C hc (fun h => by simp at h) (fun h => by simp at h) _ (actTot_rd S hS)
  obtain ⟨n1, n2, m1, m2⟩ := slotNM_rd δ S hS
  by_cases h0 : (actTotX S).eval e = 0
  · intro k hk
    have h0' : (actTotX S).eval e' = 0 := by rw [← hA]; exact h0
    rw [(hz h0 k hk).1, (hz h0 k hk).2, (hz' h0' k hk).1, (hz' h0' k hk).2]; exact ⟨rfl, rfl⟩
  · have hNe := hN h0
    rw [slotGate_eq, qsub_val, qmul_val, qvar_val, sub_eq_zero] at g g'
    have eN := qval_congr δ b _ n1 n2 hc hch
    have eM := qval_congr δ b _ m1 m2 hc hch
    have hinv : Quad.mk (algebraMap F K δ) (kread (Compute.TowerD.gatherEnv b e) .traceCur S.inv)
        (imVal (kread (Compute.TowerD.gatherEnv b e) .traceCur) (some S.invIm)) =
        Quad.mk (algebraMap F K δ) (kread (Compute.TowerD.gatherEnv b e') .traceCur S.inv)
        (imVal (kread (Compute.TowerD.gatherEnv b e') .traceCur) (some S.invIm)) := by
      refine mul_right_cancel₀ hNe ?_
      rw [g, eN, g', eM]
    simp only [kread, imVal, Quad.mk_eq_mk_iff, Compute.TowerD.gatherEnv] at hinv
    intro k hk
    have a1 := congrArg (fun x => coord b x ⟨k, hk⟩) hinv.1
    have a2 := congrArg (fun x => coord b x ⟨k, hk⟩) hinv.2
    simp only [Compute.LogUp.coord_limbVal] at a1 a2
    exact ⟨a1, a2⟩

end Slots


/-! ## 3. The accumulators -/

section Accs

theorem termCoord_congr {F : Type} [Field F] (slots : List (Compute.LogUp.Slot ℚ))
    (hrd : ∀ s ∈ slots, rdC false false 69 s.act = true) {e e' : Env F} (hc : ∀ j < 69, e.trace j = e'.trace j)
    (hinv : ∀ s ∈ slots, ∀ k < 3, e.trace (s.invBase + k) = e'.trace (s.invBase + k)) (k : ℕ) (hk : k < 3) :
    evalQX (Compute.LogUp.termCoord slots k) e = evalQX (Compute.LogUp.termCoord slots k) e' := by
  unfold Compute.LogUp.termCoord
  rw [TeleCQX.evalQX_sumList, TeleCQX.evalQX_sumList]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  simp only [evalQX]
  rw [evalQX_congr hc (fun h => by simp at h) (fun h => by simp at h) _ (hrd s hs), hinv s hs k hk]

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal pubVal' : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
  (P' : Fin (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).rap.w → F[X])

/-- **One accumulator limb family** (`accBase + k`, `k < 3`): `acc 0 = 0` and `acc (i+1) = acc i + term i`, so equal
terms give equal accumulators. -/
theorem accum_eq (slots : List (Compute.LogUp.Slot ℚ)) (accBase pubBase : ℕ)
    (hsub : ∀ g ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)), g ∈ (baseGatesHX : List (CoeffExpr ℚ)))
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hsat' : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal' orbit) P')
    (hbind : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hbind' : (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).BindsPreprocessing P')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hterm : ∀ (i : Fin n) (k : ℕ), k < 3 →
      evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pubVal orbit P i) =
        evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pubVal' orbit P' i)) :
    ∀ (i : Fin n) (k : ℕ), k < 3 →
      (rEF nodes chalV pubVal orbit P i).trace (accBase + k) =
        (rEF nodes chalV pubVal' orbit P' i).trace (accBase + k) := by
  have rows : ∀ (pv : ℕ → F) (Q : Fin (computeChipVCLHX hn nodes b δ chalV pv orbit).rap.w → F[X])
      (hs : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pv orbit) Q)
      (hb : (computeChipVCLHX hn nodes b δ chalV pv orbit).BindsPreprocessing Q) (k : ℕ) (hk : k < 3),
      (rEF nodes chalV pv orbit Q ⟨0, hn⟩).trace (accBase + k) = 0 ∧
      ∀ (i : ℕ) (hi : i + 1 < n),
        (rEF nodes chalV pv orbit Q ⟨i + 1, hi⟩).trace (accBase + k) =
          (rEF nodes chalV pv orbit Q ⟨i, by omega⟩).trace (accBase + k) +
            evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pv orbit Q ⟨i, by omega⟩) := by
    intro pv Q hs hb k hk
    have mem1 : accInitX accBase k ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)) := by
      unfold accGatesX
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    have mem2 : accStepX slots accBase k ∈ (accGatesX slots accBase pubBase : List (CoeffExpr ℚ)) := by
      unfold accGatesX
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    refine ⟨?_, fun i hi => ?_⟩
    · have g := baseX_of_sat hn nodes b δ chalV pv orbit Q hs _ (mem_rowNodeSet nodes ⟨0, hn⟩) _ (hsub _ mem1)
      have hm := (masksCX hn nodes b δ chalV pv orbit Q hb hinj ⟨0, hn⟩).1
      simp only [accInitX, evalQX, cc, hm] at g
      simpa using g
    · have g := baseX_of_sat hn nodes b δ chalV pv orbit Q hs _ (mem_rowNodeSet nodes ⟨i, by omega⟩) _ (hsub _ mem2)
      have hm := (masksCX hn nodes b δ chalV pv orbit Q hb hinj ⟨i, by omega⟩).2
      rw [if_neg (by simp; omega)] at hm
      have hnx := traceNext_eq nodes orbit Q chalV pv hadj ⟨i, by omega⟩ hi (accBase + k)
      simp only [accStepX, notC, evalQX, cc, hm, Rat.cast_one] at g
      have g2 : (rEF nodes chalV pv orbit Q ⟨i, by omega⟩).traceNext (accBase + k) -
          (rEF nodes chalV pv orbit Q ⟨i, by omega⟩).trace (accBase + k) -
          evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pv orbit Q ⟨i, by omega⟩) = 0 := by
        simpa using g
      rw [hnx] at g2
      linear_combination g2
  intro i k hk
  obtain ⟨a0, as⟩ := rows pubVal P hsat hbind k hk
  obtain ⟨a0', as'⟩ := rows pubVal' P' hsat' hbind' k hk
  have key := rec_unique n
    (fun j => if h : j < n then (rEF nodes chalV pubVal orbit P ⟨j, h⟩).trace (accBase + k) else 0)
    (fun j => if h : j < n then (rEF nodes chalV pubVal' orbit P' ⟨j, h⟩).trace (accBase + k) else 0)
    (fun j => if h : j < n then evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pubVal orbit P ⟨j, h⟩) else 0)
    (fun j => if h : j < n then evalQX (Compute.LogUp.termCoord slots k) (rEF nodes chalV pubVal' orbit P' ⟨j, h⟩) else 0)
    0 (by simpa [dif_pos hn] using a0) (by simpa [dif_pos hn] using a0')
    (fun j hj => by simp only [dif_pos (show j < n by omega)]; exact hterm ⟨j, by omega⟩ k hk)
    (fun j hj => by simp only [dif_pos (show j < n by omega), dif_pos hj]; exact as j hj)
    (fun j hj => by simp only [dif_pos (show j < n by omega), dif_pos hj]; exact as' j hj)
  have := key i i.isLt
  simpa [dif_pos i.isLt] using this

end Accs


/-! ## 4. The compute walk -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal pubVal' : ℕ → F) (orbit : StrictOrbitDomain F 3 h)

/-- Equal coordinate windows give equal limbs. -/
theorem cols_of_limbVal (f f' : ℕ → F) (i : ℕ) (hh : Compute.LogUp.limbVal b f i = Compute.LogUp.limbVal b f' i) :
    ∀ k < 3, f (i + k) = f' (i + k) := by
  intro k hk
  have := congrArg (fun x => coord b x ⟨k, hk⟩) hh
  simpa only [Compute.LogUp.coord_limbVal] using this

theorem limbVal_congr (f f' : ℕ → F) (i : ℕ) (hh : ∀ k < 3, f (i + k) = f' (i + k)) :
    Compute.LogUp.limbVal b f i = Compute.LogUp.limbVal b f' i := by
  unfold Compute.LogUp.limbVal
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hh k k.isLt]

/-- **The nine walk gates at one row**, in the gathered `𝕂` environment. -/
theorem walk_row (e : Env F)
    (hg : ∀ t ∈ (walkGatesX : List (MixedExpr ℚ)), evalMQ t (Compute.TowerD.gatherEnv b e) e = 0) :
    algebraMap F K (1 - e.trace lastX) *
        ((Compute.TowerD.gatherEnv b e).traceNext wLnX -
          (Compute.TowerD.gatherEnv b e).chal chalAlphaW * (Compute.TowerD.gatherEnv b e).trace wLnX) = 0 ∧
      algebraMap F K (1 - e.trace lastX) *
        ((Compute.TowerD.gatherEnv b e).traceNext wCntX -
          (Compute.TowerD.gatherEnv b e).trace wCntX * evalMQ (cmLX .traceNext) (Compute.TowerD.gatherEnv b e) e) = 0 ∧
      algebraMap F K (1 - e.trace lastX) *
        (((Compute.TowerD.gatherEnv b e).traceNext wLnX * evalMQ (curLX .traceNext) (Compute.TowerD.gatherEnv b e) e +
            (Compute.TowerD.gatherEnv b e).traceNext wAccX) - (Compute.TowerD.gatherEnv b e).trace wAccX -
          (Compute.TowerD.gatherEnv b e).trace wCntX * evalMQ (ccLX .traceNext) (Compute.TowerD.gatherEnv b e) e) = 0 ∧
      algebraMap F K (e.trace firstX) *
        ((Compute.TowerD.gatherEnv b e).trace wLnX - (Compute.TowerD.gatherEnv b e).chal chalAlphaW) = 0 ∧
      algebraMap F K (e.trace firstX) *
        ((Compute.TowerD.gatherEnv b e).trace wCntX -
          (Compute.TowerD.gatherEnv b e).pub pubIC * evalMQ (cmLX .traceCur) (Compute.TowerD.gatherEnv b e) e) = 0 ∧
      algebraMap F K (e.trace firstX) *
        (((Compute.TowerD.gatherEnv b e).trace wLnX * evalMQ (curLX .traceCur) (Compute.TowerD.gatherEnv b e) e +
            (Compute.TowerD.gatherEnv b e).trace wAccX) -
          ((Compute.TowerD.gatherEnv b e).pub pubIC * evalMQ (ccLX .traceCur) (Compute.TowerD.gatherEnv b e) e +
            (Compute.TowerD.gatherEnv b e).pub pubSeed)) = 0 ∧
      algebraMap F K (1 - e.trace lastX) *
        ((Compute.TowerD.gatherEnv b e).trace wInvX *
            ((Compute.TowerD.gatherEnv b e).trace wCntX - (Compute.TowerD.gatherEnv b e).trace wLnX) - 1) = 0 := by
  have m : ∀ k (hk : k < (walkGatesX : List (MixedExpr ℚ)).length),
      evalMQ ((walkGatesX : List (MixedExpr ℚ))[k]) (Compute.TowerD.gatherEnv b e) e = 0 :=
    fun k hk => hg _ (List.getElem_mem hk)
  have g0 := m 0 (by simp [walkGatesX])
  have g1 := m 1 (by simp [walkGatesX])
  have g2 := m 2 (by simp [walkGatesX])
  have g3 := m 3 (by simp [walkGatesX])
  have g4 := m 4 (by simp [walkGatesX])
  have g5 := m 5 (by simp [walkGatesX])
  have g6 := m 6 (by simp [walkGatesX])
  simp only [walkGatesX, List.getElem_cons_zero, List.getElem_cons_succ, evalMQ, evalQ, ChipH.notC, ChipH.cc,
    ChipH.wv, Rat.cast_one, Int.cast_one] at g0 g1 g2 g3 g4 g5 g6
  exact ⟨g0, g1, g2, g3, g4, g5, g6⟩


theorem rd_cmN : rdM true true 69 (cmLX (F := ℚ) .traceNext) = true := by decide +kernel
theorem rd_ccN : rdM true true 69 (ccLX (F := ℚ) .traceNext) = true := by decide +kernel
theorem rd_curN : rdM true true 69 (curLX (F := ℚ) .traceNext) = true := by decide +kernel
theorem rd_cmC : rdM false true 69 (cmLX (F := ℚ) .traceCur) = true := by decide +kernel
theorem rd_ccC : rdM false true 69 (ccLX (F := ℚ) .traceCur) = true := by decide +kernel
theorem rd_curC : rdM false true 69 (curLX (F := ℚ) .traceCur) = true := by decide +kernel

theorem scale_one {x : F} (hx : x = 1) {X : K} (h : algebraMap F K x * X = 0) : X = 0 := by
  rw [hx, map_one, one_mul] at h; exact h

/-- The `𝕂` value of a column at row `j` (`0` past the last row). -/
def ksq {pv : ℕ → F} (Q : Fin (computeChipVCLHX hn nodes b δ chalV pv orbit).rap.w → F[X]) (col j : ℕ) : K :=
  if hj : j < n then (Compute.TowerD.gatherEnv b (rEF nodes chalV pv orbit Q ⟨j, hj⟩)).trace col else 0

variable (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
  (P' : Fin (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).rap.w → F[X])

/-- **The compute walk's columns are determined.** `ln` (`α^(i+1)`), `cnt` (the product recurrence), `acc` (the
prefix recurrence) and `wInv` (`1/(cnt − ln)` off the last row, `0` on it by E9), from equal round-0 columns and
equal `pubIC`, `pubSeed` limbs. -/
theorem walk_eq
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hsat' : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal' orbit) P')
    (hbind : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hbind' : (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).BindsPreprocessing P')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 69 →
      (rEF nodes chalV pubVal orbit P i).trace j = (rEF nodes chalV pubVal' orbit P' i).trace j)
    (hIC : ∀ k < 3, pubVal (pubIC + k) = pubVal' (pubIC + k))
    (hSd : ∀ k < 3, pubVal (pubSeed + k) = pubVal' (pubSeed + k))
    (z : ∀ i : Fin n, (rEF nodes chalV pubVal orbit P i).trace lastX = 1 →
      ∀ k < 3, (rEF nodes chalV pubVal orbit P i).trace (wInvX + k) = 0)
    (z' : ∀ i : Fin n, (rEF nodes chalV pubVal' orbit P' i).trace lastX = 1 →
      ∀ k < 3, (rEF nodes chalV pubVal' orbit P' i).trace (wInvX + k) = 0) :
    ∀ (i : Fin n) (k : ℕ), k < 3 →
      (rEF nodes chalV pubVal orbit P i).trace (wLnX + k) = (rEF nodes chalV pubVal' orbit P' i).trace (wLnX + k) ∧
      (rEF nodes chalV pubVal orbit P i).trace (wCntX + k) = (rEF nodes chalV pubVal' orbit P' i).trace (wCntX + k) ∧
      (rEF nodes chalV pubVal orbit P i).trace (wAccX + k) = (rEF nodes chalV pubVal' orbit P' i).trace (wAccX + k) ∧
      (rEF nodes chalV pubVal orbit P i).trace (wInvX + k) = (rEF nodes chalV pubVal' orbit P' i).trace (wInvX + k) := by
  -- row environments
  let eP : Fin n → Env F := fun i => rEF nodes chalV pubVal orbit P i
  let eP' : Fin n → Env F := fun i => rEF nodes chalV pubVal' orbit P' i
  let KP : Fin n → Env K := fun i => Compute.TowerD.gatherEnv b (eP i)
  let KP' : Fin n → Env K := fun i => Compute.TowerD.gatherEnv b (eP' i)
  have rowP : ∀ i : Fin n, _ := fun i => walk_row b (eP i) (fun t ht =>
    walkX_of_sat hn nodes b δ chalV pubVal orbit P hsat (nodes i) (mem_rowNodeSet nodes i) t ht)
  have rowP' : ∀ i : Fin n, _ := fun i => walk_row b (eP' i) (fun t ht =>
    walkX_of_sat hn nodes b δ chalV pubVal' orbit P' hsat' (nodes i) (mem_rowNodeSet nodes i) t ht)
  have mkP := fun i : Fin n => masksCX hn nodes b δ chalV pubVal orbit P hbind hinj i
  have mkP' := fun i : Fin n => masksCX hn nodes b δ chalV pubVal' orbit P' hbind' hinj i
  -- next row
  have nextP : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (KP i).traceNext = (KP ⟨(i : ℕ) + 1, hi⟩).trace := by
    intro i hi
    funext j
    have : (eP i).traceNext = (eP ⟨(i : ℕ) + 1, hi⟩).trace := funext (traceNext_eq nodes orbit P chalV pubVal hadj i hi)
    simp only [KP, Compute.TowerD.gatherEnv, this]
  have nextP' : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (KP' i).traceNext = (KP' ⟨(i : ℕ) + 1, hi⟩).trace := by
    intro i hi
    funext j
    have : (eP' i).traceNext = (eP' ⟨(i : ℕ) + 1, hi⟩).trace := funext (traceNext_eq nodes orbit P' chalV pubVal' hadj i hi)
    simp only [KP', Compute.TowerD.gatherEnv, this]
  -- congruences
  have chE : ∀ i : Fin n, (eP i).chal = (eP' i).chal := fun i => rfl
  have chK : ∀ i : Fin n, (KP i).chal = (KP' i).chal := fun i => rfl
  have hnx : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), ∀ j < 69, (eP i).traceNext j = (eP' i).traceNext j := by
    intro i hi j hj
    rw [traceNext_eq nodes orbit P chalV pubVal hadj i hi j, traceNext_eq nodes orbit P' chalV pubVal' hadj i hi j]
    exact h0 ⟨(i : ℕ) + 1, hi⟩ j hj
  have cmC : ∀ i : Fin n, evalMQ (cmLX .traceCur) (KP i) (eP i) = evalMQ (cmLX .traceCur) (KP' i) (eP' i) :=
    fun i => evalMQ_congr (h0 i) (fun h => by simp at h) (fun _ => chE i) (fun _ => chK i) _ rd_cmC
  have ccC : ∀ i : Fin n, evalMQ (ccLX .traceCur) (KP i) (eP i) = evalMQ (ccLX .traceCur) (KP' i) (eP' i) :=
    fun i => evalMQ_congr (h0 i) (fun h => by simp at h) (fun _ => chE i) (fun _ => chK i) _ rd_ccC
  have curC : ∀ i : Fin n, evalMQ (curLX .traceCur) (KP i) (eP i) = evalMQ (curLX .traceCur) (KP' i) (eP' i) :=
    fun i => evalMQ_congr (h0 i) (fun h => by simp at h) (fun _ => chE i) (fun _ => chK i) _ rd_curC
  have cmN : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      evalMQ (cmLX .traceNext) (KP i) (eP i) = evalMQ (cmLX .traceNext) (KP' i) (eP' i) :=
    fun i hi => evalMQ_congr (h0 i) (fun _ => hnx i hi) (fun _ => chE i) (fun _ => chK i) _ rd_cmN
  have ccN : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      evalMQ (ccLX .traceNext) (KP i) (eP i) = evalMQ (ccLX .traceNext) (KP' i) (eP' i) :=
    fun i hi => evalMQ_congr (h0 i) (fun _ => hnx i hi) (fun _ => chE i) (fun _ => chK i) _ rd_ccN
  have curN : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      evalMQ (curLX .traceNext) (KP i) (eP i) = evalMQ (curLX .traceNext) (KP' i) (eP' i) :=
    fun i hi => evalMQ_congr (h0 i) (fun _ => hnx i hi) (fun _ => chE i) (fun _ => chK i) _ rd_curN
  have pIC : ∀ i : Fin n, (KP i).pub pubIC = (KP' i).pub pubIC := fun i =>
    limbVal_congr b _ _ _ (fun k hk => hIC k hk)
  have pSd : ∀ i : Fin n, (KP i).pub pubSeed = (KP' i).pub pubSeed := fun i =>
    limbVal_congr b _ _ _ (fun k hk => hSd k hk)
  have z0 : (⟨0, hn⟩ : Fin n).val = 0 := rfl
  have first0 : (eP ⟨0, hn⟩).trace firstX = 1 := by rw [(mkP ⟨0, hn⟩).1]; simp
  have first0' : (eP' ⟨0, hn⟩).trace firstX = 1 := by rw [(mkP' ⟨0, hn⟩).1]; simp
  have notlast : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (eP i).trace lastX = 0 := by
    intro i hi; rw [(mkP i).2, if_neg (by omega)]
  have notlast' : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (eP' i).trace lastX = 0 := by
    intro i hi; rw [(mkP' i).2, if_neg (by omega)]
  have one_sub : ∀ (x : F), x = 0 → 1 - x = 1 := fun x hx => by rw [hx, sub_zero]
  -- ln
  have lnEq : ∀ i : Fin n, (KP i).trace wLnX = (KP' i).trace wLnX := by
    have α_eq : ∀ i : Fin n, (KP i).chal chalAlphaW = (KP' i).chal chalAlphaW := fun i => rfl
    have gl : ∀ (Q : Fin n → Env F) (KQ : Fin n → Env K), Prop := fun _ _ => True
    have run : ∀ (Ee : Fin n → Env F) (KE : Fin n → Env K) (hKE : ∀ i, KE i = Compute.TowerD.gatherEnv b (Ee i))
        (hf : (Ee ⟨0, hn⟩).trace firstX = 1)
        (hnl : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (Ee i).trace lastX = 0)
        (hnext : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (KE i).traceNext = (KE ⟨(i : ℕ) + 1, hi⟩).trace)
        (hch : ∀ i : Fin n, (Ee i).chal = (Ee ⟨0, hn⟩).chal)
        (hF1 : ∀ i : Fin n, algebraMap F K (1 - (Ee i).trace lastX) *
          ((KE i).traceNext wLnX - (KE i).chal chalAlphaW * (KE i).trace wLnX) = 0)
        (hF4 : algebraMap F K ((Ee ⟨0, hn⟩).trace firstX) *
          ((KE ⟨0, hn⟩).trace wLnX - (KE ⟨0, hn⟩).chal chalAlphaW) = 0),
        ∀ i : Fin n, (KE i).trace wLnX = ((KE ⟨0, hn⟩).chal chalAlphaW) ^ ((i : ℕ) + 1) := by
      intro Ee KE hKE hf hnl hnext hch hF1 hF4
      have key := geom_closed n ((KE ⟨0, hn⟩).chal chalAlphaW)
        (fun j => if h : j < n then (KE ⟨j, h⟩).trace wLnX else 0)
        (by simp only [dif_pos hn]; have := scale_one hf hF4; exact sub_eq_zero.mp this)
        (fun i hi => by
          simp only [dif_pos (show i < n by omega), dif_pos hi]
          have := scale_one (by rw [hnl ⟨i, by omega⟩ hi]; simp) (hF1 ⟨i, by omega⟩)
          rw [hnext ⟨i, by omega⟩ hi] at this
          have hc : (KE ⟨i, by omega⟩).chal chalAlphaW = (KE ⟨0, hn⟩).chal chalAlphaW := by
            rw [hKE, hKE]; simp only [Compute.TowerD.gatherEnv, hch ⟨i, by omega⟩]
          rw [hc] at this
          exact sub_eq_zero.mp this)
      intro i
      have := key i i.isLt
      simpa [dif_pos i.isLt] using this
    have r1 := run eP KP (fun _ => rfl) first0 notlast nextP (fun _ => rfl) (fun i => (rowP i).1) (by
      have := (rowP ⟨0, hn⟩).2.2.2.1; exact this)
    have r2 := run eP' KP' (fun _ => rfl) first0' notlast' nextP' (fun _ => rfl) (fun i => (rowP' i).1) (by
      have := (rowP' ⟨0, hn⟩).2.2.2.1; exact this)
    intro i
    rw [r1, r2]
    rfl
  -- cnt
  have cnEq : ∀ i : Fin n, (KP i).trace wCntX = (KP' i).trace wCntX := by
    have key := prod_rec_unique n
      (fun j => if h : j < n then (KP ⟨j, h⟩).trace wCntX else 0)
      (fun j => if h : j < n then (KP' ⟨j, h⟩).trace wCntX else 0)
      (fun j => if h : j < n then evalMQ (cmLX .traceNext) (KP ⟨j, h⟩) (eP ⟨j, h⟩) else 1)
      (by
        simp only [dif_pos hn]
        have a := sub_eq_zero.mp (scale_one first0 (rowP ⟨0, hn⟩).2.2.2.2.1)
        have a' := sub_eq_zero.mp (scale_one first0' (rowP' ⟨0, hn⟩).2.2.2.2.1)
        rw [a, a', pIC ⟨0, hn⟩, cmC ⟨0, hn⟩])
      (fun i hi => by
        simp only [dif_pos hi, dif_pos (show i < n by omega)]
        have g := scale_one (by rw [notlast ⟨i, by omega⟩ hi]; simp) (rowP ⟨i, by omega⟩).2.1
        rw [nextP ⟨i, by omega⟩ hi] at g
        exact sub_eq_zero.mp g)
      (fun i hi => by
        simp only [dif_pos hi, dif_pos (show i < n by omega)]
        have g := scale_one (by rw [notlast' ⟨i, by omega⟩ hi]; simp) (rowP' ⟨i, by omega⟩).2.1
        rw [nextP' ⟨i, by omega⟩ hi] at g
        rw [cmN ⟨i, by omega⟩ hi]
        exact sub_eq_zero.mp g)
    intro i
    have := key i i.isLt
    simpa [dif_pos i.isLt] using this
  -- acc
  have acEq : ∀ i : Fin n, (KP i).trace wAccX = (KP' i).trace wAccX := by
    have key := rec_unique n
      (fun j => if h : j < n then (KP ⟨j, h⟩).trace wAccX else 0)
      (fun j => if h : j < n then (KP' ⟨j, h⟩).trace wAccX else 0)
      (fun j => if h : j + 1 < n then
        (KP ⟨j, by omega⟩).trace wCntX * evalMQ (ccLX .traceNext) (KP ⟨j, by omega⟩) (eP ⟨j, by omega⟩) -
          (KP ⟨j + 1, h⟩).trace wLnX * evalMQ (curLX .traceNext) (KP ⟨j, by omega⟩) (eP ⟨j, by omega⟩) else 0)
      (fun j => if h : j + 1 < n then
        (KP' ⟨j, by omega⟩).trace wCntX * evalMQ (ccLX .traceNext) (KP' ⟨j, by omega⟩) (eP' ⟨j, by omega⟩) -
          (KP' ⟨j + 1, h⟩).trace wLnX * evalMQ (curLX .traceNext) (KP' ⟨j, by omega⟩) (eP' ⟨j, by omega⟩) else 0)
      (((KP ⟨0, hn⟩).pub pubIC * evalMQ (ccLX .traceCur) (KP ⟨0, hn⟩) (eP ⟨0, hn⟩) + (KP ⟨0, hn⟩).pub pubSeed) -
        (KP ⟨0, hn⟩).trace wLnX * evalMQ (curLX .traceCur) (KP ⟨0, hn⟩) (eP ⟨0, hn⟩))
      (by
        simp only [dif_pos hn]
        have a := sub_eq_zero.mp (scale_one first0 (rowP ⟨0, hn⟩).2.2.2.2.2.1)
        linear_combination a)
      (by
        simp only [dif_pos hn]
        have a' := sub_eq_zero.mp (scale_one first0' (rowP' ⟨0, hn⟩).2.2.2.2.2.1)
        rw [← lnEq ⟨0, hn⟩, ← curC ⟨0, hn⟩, ← pIC ⟨0, hn⟩, ← ccC ⟨0, hn⟩, ← pSd ⟨0, hn⟩] at a'
        linear_combination a')
      (fun i hi => by
        simp only [dif_pos hi]
        rw [cnEq ⟨i, by omega⟩, ccN ⟨i, by omega⟩ hi, lnEq ⟨i + 1, hi⟩, curN ⟨i, by omega⟩ hi])
      (fun i hi => by
        simp only [dif_pos hi, dif_pos (show i < n by omega)]
        have g := scale_one (by rw [notlast ⟨i, by omega⟩ hi]; simp) (rowP ⟨i, by omega⟩).2.2.1
        rw [nextP ⟨i, by omega⟩ hi] at g
        linear_combination g)
      (fun i hi => by
        simp only [dif_pos hi, dif_pos (show i < n by omega)]
        have g := scale_one (by rw [notlast' ⟨i, by omega⟩ hi]; simp) (rowP' ⟨i, by omega⟩).2.2.1
        rw [nextP' ⟨i, by omega⟩ hi] at g
        linear_combination g)
    intro i
    have := key i i.isLt
    simpa [dif_pos i.isLt] using this
  -- wInv
  have wiEq : ∀ i : Fin n, (KP i).trace wInvX = (KP' i).trace wInvX := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have g := sub_eq_zero.mp (scale_one (by rw [notlast i hi]; simp) (rowP i).2.2.2.2.2.2)
      have g' := sub_eq_zero.mp (scale_one (by rw [notlast' i hi]; simp) (rowP' i).2.2.2.2.2.2)
      have hd : (KP i).trace wCntX - (KP i).trace wLnX ≠ 0 := right_ne_zero_of_mul_eq_one g
      exact inv_col_unique hd g (by rw [cnEq i, lnEq i]; exact g')
    · have hl : (eP i).trace lastX = 1 := by rw [(mkP i).2, if_pos (by omega)]
      have hl' : (eP' i).trace lastX = 1 := by rw [(mkP' i).2, if_pos (by omega)]
      exact limbVal_congr b (eP i).trace (eP' i).trace wInvX
        (fun k hk => (z i hl k hk).trans (z' i hl' k hk).symm)
  intro i k hk
  exact ⟨cols_of_limbVal b (eP i).trace (eP' i).trace wLnX (lnEq i) k hk,
    cols_of_limbVal b (eP i).trace (eP' i).trace wCntX (cnEq i) k hk,
    cols_of_limbVal b (eP i).trace (eP' i).trace wAccX (acEq i) k hk,
    cols_of_limbVal b (eP i).trace (eP' i).trace wInvX (wiEq i) k hk⟩

end Walk

/-! ## 5. The side gates and the whole block -/

section Final
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal pubVal' : ℕ → F) (orbit : StrictOrbitDomain F 3 h)

theorem slot_inv_lt : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)), S.inv + 3 ≤ 93 ∧ S.invIm + 3 ≤ 93 := by
  intro S hS
  simp only [ChipHX.slotsX, slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> simp [inv0X, inv0Xi, inv1X, inv1Xi, inv2X, inv2Xi, inv3X, inv3Xi]

/-- **The side gates E8, E9 at a row.** -/
theorem side_row (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (Pside : Fin ((canonC2T (F := F)).width 3) → F[X])
    (hs : (expandChip canonC2T b (fun _ => 0) (fun _ => 0) orbit (rowNodeSet nodes)).Satisfies Pside)
    (hside : ∀ (j : ℕ) (hj : j < 123), Pside ⟨j, by rw [canonC2T_width]; exact hj⟩ = P ⟨j, by show j < 123; exact hj⟩)
    (i : Fin n) :
    (∀ S ∈ (ChipHX.slotsX : List (SlotX F)), (actTotX S).eval (rEF nodes chalV pubVal orbit P i) = 0 →
        ∀ k < 3, (rEF nodes chalV pubVal orbit P i).trace (S.inv + k) = 0 ∧
          (rEF nodes chalV pubVal orbit P i).trace (S.invIm + k) = 0) ∧
      ((rEF nodes chalV pubVal orbit P i).trace lastX = 1 →
        ∀ k < 3, (rEF nodes chalV pubVal orbit P i).trace (wInvX + k) = 0) := by
  have hl := (expandChip_satisfies_iff_language canonC2T b (fun _ => 0) (fun _ => 0) orbit (rowNodeSet nodes)
    Pside).mp hs (nodes i) (mem_rowNodeSet nodes i)
  have hl' : ∀ g ∈ (canonC2Gates : List (CoeffExpr F)),
      g.eval (Reify.envOfTrace Pside orbit.ω (nodes i) (fun _ => 0) (fun _ => 0)) = 0 := fun g hg => hl.1 g hg
  have hE : ∀ j (hj : j < 123), (Reify.envOfTrace Pside orbit.ω (nodes i) (fun _ => 0) (fun _ => 0)).trace j =
      (rEF nodes chalV pubVal orbit P i).trace j := by
    intro j hj
    rw [envOfTrace_trace Pside _ _ _ _ (by rw [canonC2T_width]; exact hj),
      envOfTrace_trace P _ _ _ _ (by show j < 123; exact hj), hside j hj]
  refine ⟨fun S hS hA k hk => ?_, fun hL k hk => ?_⟩
  · have hlt := slot_inv_lt S hS
    have m1 : (CoeffExpr.mul (.sub (.const 1) (actTotX S)) (cc (S.inv + k)) : CoeffExpr F) ∈ canonC2Gates (F := F) :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)⟩)
    have m2 : (CoeffExpr.mul (.sub (.const 1) (actTotX S)) (cc (S.invIm + k)) : CoeffExpr F) ∈ canonC2Gates (F := F) :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)⟩)
    have hAeq : (actTotX S).eval (Reify.envOfTrace Pside orbit.ω (nodes i) (fun _ => 0) (fun _ => 0)) =
        (actTotX S).eval (rEF nodes chalV pubVal orbit P i) :=
      eval_congr_C (fun j hj => hE j (by omega)) (fun h => by simp at h) (fun h => by simp at h) _ (actTot_rd S hS)
    have g1 := hl' _ m1
    have g2 := hl' _ m2
    simp only [CoeffExpr.eval, ChipH.cc] at g1 g2
    rw [hAeq, hA, hE _ (show S.inv + k < 123 by omega)] at g1
    rw [hAeq, hA, hE _ (show S.invIm + k < 123 by omega)] at g2
    exact ⟨by simpa using g1, by simpa using g2⟩
  · have m : (CoeffExpr.mul (cc lastX) (cc (wInvX + k)) : CoeffExpr F) ∈ canonC2Gates (F := F) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    have g := hl' _ m
    simp only [CoeffExpr.eval, ChipH.cc] at g
    rw [hE lastX (by decide), hE (wInvX + k) (by simp [wInvX]; omega), hL, one_mul] at g
    exact g


/-- The slot list of an accumulator family. -/
def slotsFor (bl : Bal) (im : Bool) : List (Compute.LogUp.Slot ℚ) :=
  (ChipHX.slotsX : List (SlotX ℚ)).map fun S => ⟨S.actB bl, if im then S.invIm else S.inv⟩

theorem act_rd_all : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ bl : Bal, rdC false false 69 (S.actB bl) = true := by
  have h : ((ChipHX.slotsX : List (SlotX ℚ)).all fun S => rdC false false 69 (S.actB .x) &&
      rdC false false 69 (S.actB .p) && rdC false false 69 (S.actB .s)) = true := by decide +kernel
  intro S hS bl
  have := List.all_eq_true.mp h S hS
  simp only [Bool.and_eq_true] at this
  cases bl
  · exact this.1.1
  · exact this.1.2
  · exact this.2

theorem acc_sub (bl : Bal) (im : Bool) (ab pb : ℕ)
    (hm : (bl, im, ab, pb) ∈ ([(Bal.x, false, accXX, ChipH.pubRhoX), (Bal.x, true, accXXi, ChipHQ.pubRhoXIm),
      (Bal.p, false, accPX, ChipH.pubRhoP), (Bal.p, true, accPXi, ChipHQ.pubRhoPIm),
      (Bal.s, false, accSX, pubRhoSX), (Bal.s, true, accSXi, pubRhoSXi)] : List (Bal × Bool × ℕ × ℕ))) :
    ∀ g ∈ (accGatesX (slotsFor bl im) ab pb : List (CoeffExpr ℚ)), g ∈ (baseGatesHX : List (CoeffExpr ℚ)) := by
  intro g hg
  have hg' : g ∈ (accOf bl im ab pb : List (CoeffExpr ℚ)) := hg
  clear hg
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  (simp only [baseGatesHX, accGatesHX, List.mem_append]; tauto)

variable (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
  (P' : Fin (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).rap.w → F[X])

/-- **The compute chip's round-1 block is determined.** Two traces of `computeChipVCLHX` at one coin vector with
equal round-0 columns (the first `69`), satisfying the side gates E8, E9, equal `pubIC` and `pubSeed` limbs and
nonzero active slot factors `N` (the denominators-nonzero facts), agree on every column `69 .. 122` at every row. -/
theorem comp_cols_eq
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hsat' : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal' orbit) P')
    (hbind : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hbind' : (computeChipVCLHX hn nodes b δ chalV pubVal' orbit).BindsPreprocessing P')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (Pside : Fin ((canonC2T (F := F)).width 3) → F[X])
    (hs : (expandChip canonC2T b (fun _ => 0) (fun _ => 0) orbit (rowNodeSet nodes)).Satisfies Pside)
    (hside : ∀ (j : ℕ) (hj : j < 123), Pside ⟨j, by rw [canonC2T_width]; exact hj⟩ = P ⟨j, by show j < 123; exact hj⟩)
    (Pside' : Fin ((canonC2T (F := F)).width 3) → F[X])
    (hs' : (expandChip canonC2T b (fun _ => 0) (fun _ => 0) orbit (rowNodeSet nodes)).Satisfies Pside')
    (hside' : ∀ (j : ℕ) (hj : j < 123), Pside' ⟨j, by rw [canonC2T_width]; exact hj⟩ = P' ⟨j, by show j < 123; exact hj⟩)
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 69 →
      (rEF nodes chalV pubVal orbit P i).trace j = (rEF nodes chalV pubVal' orbit P' i).trace j)
    (hIC : ∀ k < 3, pubVal (pubIC + k) = pubVal' (pubIC + k))
    (hSd : ∀ k < 3, pubVal (pubSeed + k) = pubVal' (pubSeed + k))
    (hN : ∀ (i : Fin n), ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      (actTotX S).eval (rEF nodes chalV pubVal orbit P i) ≠ 0 →
        Q.val δ (slotNQ δ S) (Compute.TowerD.gatherEnv b (rEF nodes chalV pubVal orbit P i))
          (rEF nodes chalV pubVal orbit P i) ≠ 0) :
    ∀ (i : Fin n) (j : ℕ), j < 123 →
      (rEF nodes chalV pubVal orbit P i).trace j = (rEF nodes chalV pubVal' orbit P' i).trace j := by
  have sd := fun i => side_row hn nodes b δ chalV pubVal orbit P Pside hs hside i
  have sd' := fun i => side_row hn nodes b δ chalV pubVal' orbit P' Pside' hs' hside' i
  have chEq : ∀ i : Fin n, (rEF nodes chalV pubVal orbit P i).chal = (rEF nodes chalV pubVal' orbit P' i).chal :=
    fun i => rfl
  have slotsEq : ∀ (i : Fin n) (S : SlotX F), S ∈ (ChipHX.slotsX : List (SlotX F)) → ∀ k < 3,
      (rEF nodes chalV pubVal orbit P i).trace (S.inv + k) = (rEF nodes chalV pubVal' orbit P' i).trace (S.inv + k) ∧
      (rEF nodes chalV pubVal orbit P i).trace (S.invIm + k) = (rEF nodes chalV pubVal' orbit P' i).trace (S.invIm + k) := by
    intro i S hS
    have hS' := hS
    rw [← slotsX_cast] at hS'
    obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hS'
    exact slot_inv_eq δ b _ hS (rEF nodes chalV pubVal orbit P i) (rEF nodes chalV pubVal' orbit P' i) (h0 i) (chEq i)
      (slotX_of_sat hn nodes b δ chalV pubVal orbit P hsat (nodes i) (mem_rowNodeSet nodes i) S0 hS0)
      (slotX_of_sat hn nodes b δ chalV pubVal' orbit P' hsat' (nodes i) (mem_rowNodeSet nodes i) S0 hS0)
      (hN i _ hS) ((sd i).1 _ hS) ((sd' i).1 _ hS)
  have fam : ∀ (bl : Bal) (im : Bool) (ab pb : ℕ),
      (∀ g ∈ (accGatesX (slotsFor bl im) ab pb : List (CoeffExpr ℚ)), g ∈ (baseGatesHX : List (CoeffExpr ℚ))) →
      ∀ (i : Fin n) (k : ℕ), k < 3 →
        (rEF nodes chalV pubVal orbit P i).trace (ab + k) = (rEF nodes chalV pubVal' orbit P' i).trace (ab + k) := by
    intro bl im ab pb hsub
    refine accum_eq hn nodes b δ chalV pubVal pubVal' orbit P P' (slotsFor bl im) ab pb hsub
      hsat hsat' hbind hbind' hinj hadj (fun i k hk => ?_)
    refine termCoord_congr _ ?_ (h0 i) ?_ k hk
    · intro s hs; unfold slotsFor at hs; obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hs; exact act_rd_all S0 hS0 bl
    · intro s hs k hk
      unfold slotsFor at hs
      obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hs
      have hmem : castSlotX S0 ∈ (ChipHX.slotsX : List (SlotX F)) := by
        rw [← slotsX_cast]; exact List.mem_map_of_mem hS0
      have := slotsEq i _ hmem k hk
      cases im
      · exact this.1
      · exact this.2
  have f1 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (93 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (93 + k) := fam .x false accXX ChipH.pubRhoX (acc_sub _ _ _ _ (by simp))
  have f2 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (96 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (96 + k) := fam .x true accXXi ChipHQ.pubRhoXIm (acc_sub _ _ _ _ (by simp))
  have f3 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (99 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (99 + k) := fam .p false accPX ChipH.pubRhoP (acc_sub _ _ _ _ (by simp))
  have f4 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (102 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (102 + k) := fam .p true accPXi ChipHQ.pubRhoPIm (acc_sub _ _ _ _ (by simp))
  have f5 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (105 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (105 + k) := fam .s false accSX pubRhoSX (acc_sub _ _ _ _ (by simp))
  have f6 : ∀ (i : Fin n) (k : ℕ), k < 3 → (rEF nodes chalV pubVal orbit P i).trace (108 + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (108 + k) := fam .s true accSXi pubRhoSXi (acc_sub _ _ _ _ (by simp))
  have wk := walk_eq hn nodes b δ chalV pubVal pubVal' orbit P P' hsat hsat' hbind hbind' hinj hadj h0 hIC hSd
    (fun i => (sd i).2) (fun i => (sd' i).2)
  intro i j hj
  have pick : ∀ (base : ℕ), (∀ k, k < 3 → (rEF nodes chalV pubVal orbit P i).trace (base + k) =
      (rEF nodes chalV pubVal' orbit P' i).trace (base + k)) → base ≤ j → j < base + 3 →
      (rEF nodes chalV pubVal orbit P i).trace j = (rEF nodes chalV pubVal' orbit P' i).trace j := by
    intro base f h1 h2
    have := f (j - base) (by omega)
    rwa [show base + (j - base) = j by omega] at this
  have pickS : ∀ (S : SlotX F), S ∈ (ChipHX.slotsX : List (SlotX F)) →
      (S.inv ≤ j ∧ j < S.inv + 3 ∨ S.invIm ≤ j ∧ j < S.invIm + 3) →
      (rEF nodes chalV pubVal orbit P i).trace j = (rEF nodes chalV pubVal' orbit P' i).trace j := by
    intro S hS hh
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact pick S.inv (fun k hk => (slotsEq i S hS k hk).1) h1 h2
    · exact pick S.invIm (fun k hk => (slotsEq i S hS k hk).2) h1 h2
  by_cases a1 : j < 69
  · exact h0 i j a1
  by_cases a2 : j < 93
  · have m0 : (slot0X : SlotX F) ∈ (ChipHX.slotsX : List (SlotX F)) := by simp [ChipHX.slotsX]
    have m1 : (slot1X : SlotX F) ∈ (ChipHX.slotsX : List (SlotX F)) := by simp [ChipHX.slotsX]
    have m2 : (slot2X : SlotX F) ∈ (ChipHX.slotsX : List (SlotX F)) := by simp [ChipHX.slotsX]
    have m3 : (slot3X : SlotX F) ∈ (ChipHX.slotsX : List (SlotX F)) := by simp [ChipHX.slotsX]
    rcases (by omega : j < 72 ∨ (72 ≤ j ∧ j < 75) ∨ (75 ≤ j ∧ j < 78) ∨ (78 ≤ j ∧ j < 81) ∨ (81 ≤ j ∧ j < 84) ∨
      (84 ≤ j ∧ j < 87) ∨ (87 ≤ j ∧ j < 90) ∨ 90 ≤ j) with h | h | h | h | h | h | h | h
    · exact pickS _ m0 (Or.inl ⟨by show 69 ≤ j; omega, by show j < 69 + 3; omega⟩)
    · exact pickS _ m0 (Or.inr ⟨by show 72 ≤ j; omega, by show j < 72 + 3; omega⟩)
    · exact pickS _ m1 (Or.inl ⟨by show 75 ≤ j; omega, by show j < 75 + 3; omega⟩)
    · exact pickS _ m1 (Or.inr ⟨by show 78 ≤ j; omega, by show j < 78 + 3; omega⟩)
    · exact pickS _ m2 (Or.inl ⟨by show 81 ≤ j; omega, by show j < 81 + 3; omega⟩)
    · exact pickS _ m2 (Or.inr ⟨by show 84 ≤ j; omega, by show j < 84 + 3; omega⟩)
    · exact pickS _ m3 (Or.inl ⟨by show 87 ≤ j; omega, by show j < 87 + 3; omega⟩)
    · exact pickS _ m3 (Or.inr ⟨by show 90 ≤ j; omega, by show j < 90 + 3; omega⟩)
  by_cases a3 : j < 111
  · rcases (by omega : j < 96 ∨ (96 ≤ j ∧ j < 99) ∨ (99 ≤ j ∧ j < 102) ∨ (102 ≤ j ∧ j < 105) ∨
      (105 ≤ j ∧ j < 108) ∨ 108 ≤ j) with h | h | h | h | h | h
    · exact pick 93 (f1 i) (by omega) (by omega)
    · exact pick 96 (f2 i) (by omega) (by omega)
    · exact pick 99 (f3 i) (by omega) (by omega)
    · exact pick 102 (f4 i) (by omega) (by omega)
    · exact pick 105 (f5 i) (by omega) (by omega)
    · exact pick 108 (f6 i) (by omega) (by omega)
  · rcases (by omega : j < 114 ∨ (114 ≤ j ∧ j < 117) ∨ (117 ≤ j ∧ j < 120) ∨ 120 ≤ j) with h | h | h | h
    · exact pick 111 (fun k hk => (wk i k hk).1) (by omega) (by omega)
    · exact pick 114 (fun k hk => (wk i k hk).2.1) (by omega) (by omega)
    · exact pick 117 (fun k hk => (wk i k hk).2.2.1) (by omega) (by omega)
    · exact pick 120 (fun k hk => (wk i k hk).2.2.2) (by omega) (by omega)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1.slot_inv_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1.accum_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1.walk_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1.side_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1.comp_cols_eq
