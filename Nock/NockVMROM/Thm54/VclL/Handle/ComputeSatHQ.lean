/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComputeSatHQ.lean

  **`computeChipVCLHQ` is satisfiable** — every trace accepted by the
  VS compute chip `computeChipVCLH` at challenge / public vectors whose `𝕂′` Im slots are zero
  (challenge limbs `12..17`, public limbs `21..26`), extended by zero Im columns `70..84`, is accepted
  by `computeChipVCLHQ` at the SAME vectors (`computeChipVCLHQ_of_H`).  At real handle coins the `𝕂′`
  slot pair of every slot is `(slot gate, 0)`, and the Im accumulator gates read only zero columns /
  publics.  Additive.

  The honest VS compute traces (`computeChipVCLH_honest_sat`) are read at `chalVH` / `pubVH`, which are
  `0` beyond limbs `12` / `21`, so the hypotheses hold there.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify

noncomputable section

/-! ## 1. The slot templates at `ℚ` and at `F` -/

section Cast
variable {F : Type} [Field F]

theorem mapC_foldr_var (l : List ℕ) :
    mapC (fun q : ℚ => (q : F)) (l.foldr (fun i acc => (CoeffExpr.var VarKind.traceCur i).add acc)
      (CoeffExpr.const 0)) =
      l.foldr (fun i acc => (CoeffExpr.var VarKind.traceCur i).add acc) (CoeffExpr.const 0) := by
  induction l with
  | nil => simp [mapC]
  | cons a t ih => simp [mapC, ih]

/-- The three slot gates of the `ℚ` template, cast to `F`, ARE the slot gates at `F`. -/
theorem slots_cast :
    (slots (F := ℚ)).map (fun S => mapM (fun q : ℚ => (q : F)) (slotGate S)) = (slots (F := F)).map slotGate := by
  simp [slots, slot0, slot1, slot2, slotGate, mapM, mapC, sumM, den, rlcKey, Ent.act, selS, notC, cc,
    CoeffExpr.sumList, cellRec, walkRec, mapC_foldr_var]

theorem slotGate_mem_kGatesF (S : SlotSpec F) (hS : S ∈ slots (F := F)) : slotGate S ∈ (kGatesF : List (MixedExpr F)) := by
  have h : slotGate S ∈ (slots (F := ℚ)).map (fun S => mapM (fun q : ℚ => (q : F)) (slotGate S)) := by
    rw [slots_cast]; exact List.mem_map_of_mem hS
  obtain ⟨S', hS', he⟩ := List.mem_map.mp h
  rw [← he]
  exact List.mem_map_of_mem (List.mem_append_left _ (List.mem_map_of_mem hS'))

theorem walkGatesF_sub (g : MixedExpr F) (hg : g ∈ (walkGatesF : List (MixedExpr F))) : g ∈ (kGatesF : List (MixedExpr F)) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  exact List.mem_map_of_mem (List.mem_append_right _ ht)

end Cast

/-! ## 2. The zero-reading instrument -/

section Zero
variable {F : Type} [Field F]

/-- A `ℚ`-template base expression that vanishes once the marked columns `Z` and publics `P` do. -/
def zeroB (Z P : ℕ → Bool) : CoeffExpr ℚ → Bool
  | .const c => decide (c = 0)
  | .var .traceCur i => Z i
  | .var .traceNext i => Z i
  | .var .publicVal i => P i
  | .var .challenge _ => false
  | .add a b => zeroB Z P a && zeroB Z P b
  | .sub a b => zeroB Z P a && zeroB Z P b
  | .mul a b => zeroB Z P a || zeroB Z P b
  | .neg a => zeroB Z P a
  | .pow a n => decide (0 < n) && zeroB Z P a

theorem zeroB_sound (Z P : ℕ → Bool) (e : Env F) (hZ : ∀ i, Z i = true → e.trace i = 0 ∧ e.traceNext i = 0)
    (hP : ∀ i, P i = true → e.pub i = 0) : ∀ g : CoeffExpr ℚ, zeroB Z P g = true → evalQ g e = 0
  | .const c, h => by simp [zeroB] at h; simp [evalQ, h]
  | .var .traceCur i, h => (hZ i h).1
  | .var .traceNext i, h => (hZ i h).2
  | .var .publicVal i, h => hP i h
  | .var .challenge _, h => by simp [zeroB] at h
  | .add a b, h => by
      simp only [zeroB, Bool.and_eq_true] at h
      simp [evalQ, zeroB_sound Z P e hZ hP a h.1, zeroB_sound Z P e hZ hP b h.2]
  | .sub a b, h => by
      simp only [zeroB, Bool.and_eq_true] at h
      simp [evalQ, zeroB_sound Z P e hZ hP a h.1, zeroB_sound Z P e hZ hP b h.2]
  | .mul a b, h => by
      simp only [zeroB, Bool.or_eq_true] at h
      rcases h with h | h <;> simp [evalQ, zeroB_sound Z P e hZ hP _ h]
  | .neg a, h => by simp only [zeroB] at h; simp [evalQ, zeroB_sound Z P e hZ hP a h]
  | .pow a n, h => by
      simp only [zeroB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [evalQ, zeroB_sound Z P e hZ hP a h.2, zero_pow (Nat.pos_iff_ne_zero.mp h.1)]

/-- The Im accumulator gates of the twin. -/
def imAccGates : List (CoeffExpr ℚ) :=
  accGates 3 ((slots (F := ℚ)).map fun S => ⟨S.actX, imOf S.inv⟩) accXIm pubRhoXIm ++
    accGates 3 ((slots (F := ℚ)).map fun S => ⟨S.actP, imOf S.inv⟩) accPIm pubRhoPIm

def zCols (i : ℕ) : Bool := decide (70 ≤ i ∧ i < 85)
def zPubs (i : ℕ) : Bool := decide (21 ≤ i ∧ i < 27)

/-- **The Im accumulator gates read only the Im columns `70..84` and Im publics `21..26`** (kernel). -/
theorem imAcc_zero : imAccGates.all (zeroB zCols zPubs) = true := by decide +kernel

theorem accGatesHQ_split (t : CoeffExpr ℚ) (ht : t ∈ (accGatesHQ (F := ℚ))) :
    t ∈ (accGatesH (F := ℚ)) ∨ t ∈ imAccGates := by
  simp only [accGatesHQ, List.mem_append] at ht
  rcases ht with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (List.mem_append_left _ h)
  · exact Or.inr (List.mem_append_right _ h)

end Zero

/-! ## 3. Real-coin values of the `𝕂′` slot pairs -/

section Val
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) (eK : Env K) (eF : Env F)

theorem aM (x : K) : (algebraMap K (Quad (algebraMap F K δ))) x = Quad.mk _ x 0 := (Quad.mk_base _ x).symm

theorem qlift_val' (g : CoeffExpr F) :
    Q.val δ (qlift F g) eK eF = algebraMap K _ (algebraMap F K (g.eval eF)) := by
  rw [qlift_val]; exact IsScalarTower.algebraMap_apply F K _ _

theorem rlcKeyQ_val (hγ : eK.chal chalGammaIm = 0) :
    ∀ (r : List ℕ) (n : ℕ), Q.val δ (rlcKeyQ F δ n r) eK eF =
      algebraMap K _ ((rlcKey (F := F) .traceCur chalGammaL n r).eval eK eF)
  | [], n => by simp [rlcKeyQ, rlcKey, qconst_val, MixedExpr.eval]
  | i :: r, n => by
      rw [rlcKeyQ, qadd_val, qmul_val, qpow_val, rlcKeyQ_val hγ r (n + 1), qlift_val']
      have hg : Q.val δ (qγH F) eK eF = algebraMap K _ (eK.chal chalGammaL) := by
        rw [qγH, qvar_val, aM]; simp [kread, imVal, hγ]
      rw [hg]
      simp [rlcKey, MixedExpr.eval, cc, CoeffExpr.eval, map_add, map_mul, map_pow]

theorem denQH_val (hγ : eK.chal chalGammaIm = 0) (hρ : eK.chal chalRhoIm = 0) (r : List ℕ) :
    Q.val δ (denQH F δ r) eK eF = algebraMap K _ ((den (F := F) r).eval eK eF) := by
  rw [denQH, qadd_val, rlcKeyQ_val δ eK eF hγ r 0]
  have hr : Q.val δ (qρH F) eK eF = algebraMap K _ (eK.chal chalRhoL) := by
    rw [qρH, qvar_val, aM]; simp [kread, imVal, hρ]
  rw [hr]
  simp [den, MixedExpr.eval, map_add]

theorem sumQ_val (l : List (Q F)) : Q.val δ (sumQ F l) eK eF = (l.map fun q => Q.val δ q eK eF).sum := by
  induction l with
  | nil => simp [sumQ, qconst_val]
  | cons a t ih => simp only [sumQ, List.foldr_cons] at ih ⊢; rw [qadd_val, ih]; simp

theorem sumM_eval (l : List (MixedExpr F)) : (sumM l).eval eK eF = (l.map fun g => g.eval eK eF).sum := by
  induction l with
  | nil => simp [sumM, MixedExpr.eval]
  | cons a t ih => simp only [sumM, List.foldr_cons] at ih ⊢; simp [MixedExpr.eval, ih]

/-- **At real handle coins and a zero Im inverse, the `𝕂′` slot pair is `(slot gate, 0)`.** -/
theorem slotGateQ_val (hγ : eK.chal chalGammaIm = 0) (hρ : eK.chal chalRhoIm = 0) (S : SlotSpec F)
    (him : eK.trace (imOf S.inv) = 0) :
    Q.val δ (slotGateQ F δ S) eK eF = algebraMap K _ ((slotGate S).eval eK eF) := by
  have hinv : Q.val δ (qvar F .traceCur S.inv (some (imOf S.inv))) eK eF = algebraMap K _ (eK.trace S.inv) := by
    rw [qvar_val, aM]; simp [kread, imVal, him]
  have hents : Q.val δ (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQH F δ x.rcd))) eK eF =
      algebraMap K _ ((sumM (S.ents.map fun x => MixedExpr.Scale x.act (den x.rcd))).eval eK eF) := by
    rw [sumQ_val, sumM_eval, map_list_sum]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, qmul_val, qlift_val', denQH_val δ eK eF hγ hρ, MixedExpr.eval, map_mul]
  have hlift : Q.val δ (qlift F (CoeffExpr.sumList S.ents Ent.act)) eK eF =
      algebraMap K _ ((MixedExpr.Lift (CoeffExpr.sumList S.ents Ent.act) : MixedExpr F).eval eK eF) := by
    rw [qlift_val']; rfl
  unfold slotGateQ slotGate
  rcases hp : S.pair with _ | ⟨fl, a, b⟩
  · simp only [qsub_val, qmul_val, qadd_val, hinv, hents, hlift, qconst_val, MixedExpr.eval, map_sub, map_mul,
      map_add]
    try simp
  · simp only [qsub_val, qmul_val, qadd_val, hinv, hents, hlift, qlift_val', denQH_val δ eK eF hγ hρ,
      MixedExpr.eval, map_sub, map_mul, map_add]
    try simp [cc, CoeffExpr.eval]

end Val

/-! ## 4. The embedding -/

section Embed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

set_option maxHeartbeats 4000000 in
/-- **`sat_iff` for the `𝕂′` compute twin** (copy of `computeChipVCLH_sat_iff`). -/
theorem computeChipVCLHQ_sat_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P ↔
      (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesHQ b δ,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.compose P i).eval x =
        ((gatesHQ b δ).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- The zero-extension of a `70`-column trace to `85` columns. -/
def extendQ (P : Fin 70 → F[X]) : Fin 85 → F[X] := fun j => if h : (j : ℕ) < 70 then P ⟨j, h⟩ else 0

theorem env_extendQ (P : Fin 70 → F[X]) (ω x : F) (cv pv : ℕ → F) :
    Reify.envOfTrace (extendQ P) ω x cv pv = Reify.envOfTrace P ω x cv pv := by
  simp only [Reify.envOfTrace, extendQ]
  congr 1 <;> funext i <;> by_cases h : i < 70 <;> by_cases h' : i < 85 <;> simp [h, h'] <;> omega

variable [Fintype K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)

/-- **`computeChipVCLHQ` accepts the zero-extension of every `computeChipVCLH`-accepted trace** at
challenge / public vectors with zero `𝕂′` Im slots. -/
theorem computeChipVCLHQ_of_H (P : Fin 70 → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P)
    (hchal : ∀ j, 12 ≤ j → j < 18 → chalV j = 0) (hpub : ∀ j, 21 ≤ j → j < 27 → pubVal j = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) (extendQ P) := by
  obtain ⟨hfix, hall⟩ := (TeleC.computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mp hsat
  refine (computeChipVCLHQ_sat_iff hn nodes b δ chalV pubVal orbit (extendQ P)).mpr ⟨?_, fun x hx g hg => ?_⟩
  · intro j
    have h := hfix j
    fin_cases j <;> exact h
  show g.eval (Reify.envOfTrace (extendQ P) orbit.ω x chalV pubVal) = 0
  rw [env_extendQ]
  set eF := Reify.envOfTrace P orbit.ω x chalV pubVal with heF
  have hgH := hall x hx
  set eK := Compute.TowerD.gatherEnv b eF with heK
  have hcoord := Compute.TowerD.isCoordEnv_gather b eF
  -- `𝕂` gates of `computeChipVCLH` hold at the gathered environment
  have hK : ∀ t ∈ (kGatesF : List (MixedExpr F)), t.eval eK eF = 0 := by
    intro t ht
    have h0 : ∀ k, (mixedCompile b Compute.TowerD.col0Id t k).eval eF = 0 := fun k =>
      hgH _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ht, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
    exact (mixedCompile_zero_iff b Compute.TowerD.col0Id hcoord _).mpr h0
  have hzt : ∀ i, 70 ≤ i → eF.trace i = 0 ∧ eF.traceNext i = 0 := by
    intro i hi; simp [heF, Reify.envOfTrace, show ¬ i < 70 by omega]
  have hKz : ∀ i, 70 ≤ i → eK.trace i = 0 := by
    intro i hi
    simp only [heK, Compute.TowerD.gatherEnv, limbVal]
    exact Finset.sum_eq_zero fun k _ => by rw [(hzt _ (by omega)).1, zero_smul]
  have hchalK : ∀ j, 12 ≤ j → j < 16 → eK.chal j = 0 := by
    intro j h1 h2
    simp only [heK, Compute.TowerD.gatherEnv, limbVal]
    exact Finset.sum_eq_zero fun k _ => by
      rw [show eF.chal (j + (k : ℕ)) = 0 from hchal _ (by omega) (by have := k.isLt; omega), zero_smul]
  simp only [gatesHQ, List.mem_append, List.mem_flatMap] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, hg⟩
  · -- base gates
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    rw [eval_mapC_cast]
    simp only [baseGatesHQ, List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · rw [← eval_mapC_cast]
      exact hgH _ (List.mem_append_left _ (List.mem_map_of_mem (by simp [baseGatesH, ht])))
    · rcases accGatesHQ_split t ht with ht' | ht'
      · rw [← eval_mapC_cast]
        exact hgH _ (List.mem_append_left _ (List.mem_map_of_mem (by simp [baseGatesH, ht'])))
      · refine zeroB_sound zCols zPubs eF ?_ ?_ t (List.all_eq_true.mp imAcc_zero t ht')
        · intro i hi; simp [zCols] at hi; exact hzt i hi.1
        · intro i hi; simp [zPubs] at hi; simp [heF, Reify.envOfTrace]; exact hpub i hi.1 hi.2
    · rw [← eval_mapC_cast]
      exact hgH _ (List.mem_append_left _ (List.mem_map_of_mem (by simp [baseGatesH, ht])))
  · -- slot pairs
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
    have hzero : Q.IsZero (slotGateQ F δ S) eK eF := by
      rw [Q.isZero_iff δ eK eF, slotGateQ_val δ eK eF (hchalK _ (by decide) (by decide))
        (hchalK _ (by decide) (by decide)) S ?_, hK _ (slotGate_mem_kGatesF S hS), map_zero]
      have hS' : S = slot0 ∨ S = slot1 ∨ S = slot2 := by simpa [slots] using hS
      rcases hS' with rfl | rfl | rfl <;>
        exact hKz _ (by simp [slot0, slot1, slot2, imOf, inv0, inv1, inv2, invIm0, invIm1, invIm2])
    exact (Compute.TowerD.qGates_iff b hcoord _).mpr hzero g hg
  · -- walk gates
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact hgH _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, walkGatesF_sub m hm, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))

/-- **At the VS coin and public vectors** (`chalVH`, `pubVH`: zero beyond limbs `12` / `21`) the
hypotheses hold, so every VS-accepted compute trace yields a `computeChipVCLHQ`-accepted one. -/
theorem computeChipVCLHQ_of_VS [Fintype F] [DecidableEq F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
    (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap F K δF))
    (χ : SVFrame.Coins FrameVS.frameVS K) (P : Fin 70 → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLH hn nodes b (FrameVS.chalVH b χ) (FrameVS.pubVH δF b c m ρ χ) orbit) P) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHQ hn nodes b δ (FrameVS.chalVH b χ) (FrameVS.pubVH δF b c m ρ χ) orbit) (extendQ P) :=
  computeChipVCLHQ_of_H hn nodes b δ _ _ orbit P hsat
    (fun j h1 _ => by simp [FrameVS.chalVH, show ¬ j < 12 by omega])
    (fun j h1 h2 => by simp [FrameVS.pubVH, show ¬ j < 21 by omega, show ¬ j < 6 by omega,
      show ¬ j < 9 by omega, show ¬ j < 12 by omega, show ¬ j < 15 by omega, show ¬ j < 18 by omega])

end Embed

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ
