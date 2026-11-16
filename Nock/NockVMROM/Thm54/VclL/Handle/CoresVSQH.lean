/-
  Nock/NockVMROM/Thm54/VclL/Handle/CoresVSQH.lean

  A NEW module; nothing existing is edited.

  `compCoreVSQ` / `memCoreVSQ` (FrameVSQ.lean) hard-code `Honest := Empty`, so the completeness half of
  `StandaloneG` at them is vacuous.  Here:
  * `liftC` / `liftU`: a `frameVCL` summand read at a FIXED staged trace (resp. a trace-free `frameVSQ`
    summand) as a `frameVSQ` summand over the VSQ traces; same weight, same coin count (`mem_liftC`,
    `mem_liftU`, `epsilonOf_map_liftC`, `epsilonOf_map_liftU`);
  * `HonestVSQD` = the VSQ honest datum (`HonestVCLW` over `demandH2`, the generator tree `t`, the claim
    message `x`), exactly the arguments of `msgVSQ` / `vsqCompleteness`;
  * `honestBadC` = `honestVSQ` lifted (the `𝕂′` handle pole, the walk coin order), `honestBadM` = the 39th's
    seed / key-pole events `H.bad` lifted along `toVCL ∘ toVS` at the honest `frameVCL` trace;
    **`epsilon_honestBad`**: `epsilonOf (honestBadC ++ honestBadM) = epsCVSQ`; **`good_of_outside`**: outside
    every honest summand, `HonestGoodVSQ` holds;
  * **`compCoreVSQH` / `memCoreVSQH`**: the VSQ cores verbatim (chips `85 / 238 / 166`, summands `sumCVSQ /
    sumMVSQ`) with `Honest := HonestVSQD`, `honestV := vsqOf H.V`, `honestQ` = `msgVSQ`'s traces (staged by
    `msgVSQ_staged`), `honestReq := rhoVSQ`;
  * **`standaloneVSQH`**: `StandaloneG compCoreVSQH memCoreVSQH jointVSQ` by `standaloneG_of_sound` and
    `hsoundVSQ` (no new hypothesis); **`standaloneVSQH_completeness_le`**: its completeness half at a datum
    `D` is `≤ epsCVSQ`, and `prob_not_good_le` shows it dominates `Pr[¬ HonestGoodVSQ]` (the field is the
    honest-acceptance premise, not vacuous);
  * the figures at the honest-carrying cores: `standaloneVSQH_156 / _155_at_32 / _166` (tight values, from
    `figVCLHQ''_156 / _155_at_32 / _166_kernel`) and `standaloneVSQH_soundness_le`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.NonVacVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Nock.NockVMROM.Thm54.VclL.Handle.EpsVS Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Lifting honest summands to `frameVSQ` -/

section Lift
variable {F K : Type} [Field F] [Fintype K] [DecidableEq K] (hT hP hC : ℕ)

/-- The eleven `frameVCL` coins inside the seventeen. -/
def embC : Fin frameVCL.n ↪ Fin frameVSQ.n :=
  ⟨fun i => ⟨i, by have := i.isLt; change (i : ℕ) < 11 at this; change (i : ℕ) < 17; omega⟩,
    fun _ _ h => Fin.ext (congrArg Fin.val h :)⟩

/-- The `frameVCL` coins of a `frameVSQ` coin vector. -/
abbrev projC (χ : Coins frameVSQ K) : Coins frameVCL K := toVCL (toVS χ)

theorem projC_apply (χ : Coins frameVSQ K) (i : Fin frameVCL.n) : projC χ i = χ (embC i) := rfl

/-- **A `frameVCL` summand read at a fixed staged trace `Q`, as a `frameVSQ` summand** (the VSQ trace argument
is ignored: the honest trace is baked in).  Same weight; coins and read set mapped by `embC`. -/
def liftC {Tr : Type} {St : (Coins frameVCL K → Tr) → Prop} (s : BadSummand frameVCL K Tr St)
    (Q : Coins frameVCL K → Tr) (hQ : St Q) :
    BadSummand frameVSQ K (TrVSQ F hT hP hC) (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)) where
  coins := s.coins.map embC
  dep := s.dep.map embC
  disj := (Finset.disjoint_map embC).mpr s.disj
  badSet _ χ := Finset.univ.filter fun v : (s.coins.map embC) → K =>
    (fun i : s.coins => v ⟨embC i, Finset.mem_map_of_mem _ i.2⟩) ∈ s.badSet (Q (projC χ)) (projC χ)
  weight := s.weight
  card_le _ χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v : (s.coins.map embC) → K => fun i : s.coins => v ⟨embC i, Finset.mem_map_of_mem _ i.2⟩) ?_ ?_)
      (s.card_le (Q (projC χ)) (projC χ))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp x.2
      have := congrFun h ⟨i, hi⟩
      have hx : x = ⟨embC i, Finset.mem_map_of_mem _ hi⟩ := Subtype.ext hix.symm
      rw [hx]; exact this
  readsOn _ _ χ χ' hχ := by
    have hr := s.readsOn Q hQ (projC χ) (projC χ')
      (fun j hj => hχ (embC j) (Finset.mem_map_of_mem _ hj))
    simp only at hr
    show Finset.univ.filter _ = Finset.univ.filter _
    rw [hr]

theorem mem_liftC {Tr : Type} {St : (Coins frameVCL K → Tr) → Prop} (s : BadSummand frameVCL K Tr St)
    (Q : Coins frameVCL K → Tr) (hQ : St Q) (tr : TrVSQ F hT hP hC) (χ : Coins frameVSQ K) :
    (liftC hT hP hC s Q hQ).mem tr χ ↔ s.mem (Q (projC χ)) (projC χ) := by
  unfold BadSummand.mem
  show _ ∈ Finset.univ.filter _ ↔ _
  erw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **A trace-free `frameVSQ` summand, over the VSQ traces.** -/
def liftU (s : BadSummand frameVSQ K Unit (fun _ => True)) :
    BadSummand frameVSQ K (TrVSQ F hT hP hC) (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)) where
  coins := s.coins
  dep := s.dep
  disj := s.disj
  badSet _ χ := s.badSet () χ
  weight := s.weight
  card_le _ χ := s.card_le () χ
  readsOn _ _ := s.readsOn (fun _ => ()) trivial

theorem mem_liftU (s : BadSummand frameVSQ K Unit (fun _ => True)) (tr : TrVSQ F hT hP hC)
    (χ : Coins frameVSQ K) : (liftU hT hP hC s).mem tr χ ↔ s.mem () χ := Iff.rfl

theorem epsilonOf_map_liftC {Tr : Type} {St : (Coins frameVCL K → Tr) → Prop}
    (l : List (BadSummand frameVCL K Tr St)) (Q : Coins frameVCL K → Tr) (hQ : St Q) :
    epsilonOf (l.map fun s => liftC (F := F) hT hP hC s Q hQ) = epsilonOf l := by
  unfold epsilonOf
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply, liftC, Finset.card_map]

theorem epsilonOf_map_liftU (l : List (BadSummand frameVSQ K Unit (fun _ => True))) :
    epsilonOf (l.map (liftU (F := F) hT hP hC)) = epsilonOf l := by
  unfold epsilonOf
  rw [List.map_map]
  rfl

end Lift

/-! ## 2. The honest datum and its bad-summand lists -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (hT hP hC kr : ℕ)

/-- **The VSQ honest datum**: the honest walk memory datum over `demandH2`, the generator tree, the claim
message — exactly the arguments of `msgVSQ` and `vsqCompleteness`. -/
structure HonestVSQD where
  H : HonestVCLW (K := K) δF hT hP hC kr
  t : NTree (GenComputeRow (Quad (algebraMap F K δF)))
  x : ClaimMsgVS

variable {δF hT hP hC kr}

/-- The honest `frameVCL` trace of the 39th's events (compute block zero, the two walk-era tables). -/
def Q39 (D : HonestVSQD (K := K) δF hT hP hC kr) : Coins frameVCL K → Traces F (tableVS hC) (shapeVW hT hP) :=
  fun χ => ((fun _ => 0), fun tt => D.H.trace χ tt)

theorem Q39_staged (D : HonestVSQD (K := K) δF hT hP hC kr) :
    TracesStaged frameVCL (tableVS hC) (shapeVW hT hP) (Q39 D) :=
  ⟨stagedCols_const _ _ _, fun tt => trace_stagedW D.H tt⟩

/-- **The compute-side honest summands**: the `𝕂′` handle pole and the walk coin order (`honestVSQ`). -/
def honestBadC (D : HonestVSQD (K := K) δF hT hP hC kr) : SummandsVSQ (F := F) (K := K) hT hP hC :=
  (honestVSQ D.H D.t D.x).map (liftU hT hP hC)

/-- **The memory-side honest summands**: the 39th's zero seed and three key poles (`H.bad`), at the honest
trace, along `toVCL ∘ toVS`. -/
def honestBadM (D : HonestVSQD (K := K) δF hT hP hC kr) : SummandsVSQ (F := F) (K := K) hT hP hC :=
  (D.H.bad (C := tableVS hC)).map fun s => liftC hT hP hC s (Q39 D) (Q39_staged D)

/-- **The honest bad mass is `epsCVSQ`.** -/
theorem epsilon_honestBad (D : HonestVSQD (K := K) δF hT hP hC kr) :
    epsilonOf (honestBadC D ++ honestBadM D) = epsCVSQ D.H D.t := by
  have e : ∀ (l l' : SummandsVSQ (F := F) (K := K) hT hP hC), epsilonOf (l ++ l') = epsilonOf l + epsilonOf l' := by
    intro l l'; unfold epsilonOf; rw [List.map_append, List.sum_append]
  rw [e, honestBadC, honestBadM, epsilonOf_map_liftU, epsilonOf_map_liftC, epsilon_honestVSQ, epsilon_badW]
  unfold epsCVSQ
  ring

/-- **Outside every honest summand, `HonestGoodVSQ` holds** (any trace argument). -/
theorem good_of_outside (D : HonestVSQD (K := K) δF hT hP hC kr)
    (hN : (vsqOf D.H.V).N = (bfsForest [airReorder D.t]).length) (tr : TrVSQ F hT hP hC) (χ : Coins frameVSQ K)
    (h : ∀ s ∈ honestBadC D ++ honestBadM D, ¬ s.mem tr χ) : HonestGoodVSQ D.H D.t D.x χ := by
  refine honestGoodQ_of_notBad D.H D.t D.x hN χ (fun s hs hm => ?_) (fun s hs hm => ?_)
  · refine h (liftC hT hP hC s (Q39 D) (Q39_staged D))
      (List.mem_append_right _ (List.mem_map_of_mem hs)) ?_
    exact (mem_liftC hT hP hC s _ _ tr χ).mpr hm
  · exact h (liftU hT hP hC s) (List.mem_append_left _ (List.mem_map_of_mem hs)) hm

end Honest

/-! ## 3. The honest-carrying cores -/

section Cores
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (hT hP kr hC : ℕ)

/-- The honest VSQ messages of a datum (summands `sumCVSQ / sumMVSQ`). -/
abbrev msgD (D : HonestVSQD (K := K) δF hT hP hC kr) :=
  msgVSQ (sumC := sumCVSQ (F := F) (K := K) hT hP hC) (sumM := sumMVSQ (F := F) (K := K) δF hT hP kr hC) D.H D.t D.x

/-- **`compCoreVSQH`**: `compCoreVSQ` at `sumCVSQ` (chip `computeChipVCLHQ`, width 85) with the honest datum. -/
def compCoreVSQH :
    CompCore F K (Quad (algebraMap F K δF)) frameVSQ hC (shapeVSQ hT hP) (tableVSQ hC) 5 where
  Msg0 := ClaimMsgVS
  chip := fun V x ρ χ => chipCVSQ δF V x ρ χ
  chip_width := fun V x ρ χ => chipCVSQ_width δF V x ρ χ
  reqBound := reqBoundVSQ hT hP hC
  summands := sumCVSQ hT hP hC
  Honest := HonestVSQD (K := K) δF hT hP hC kr
  honestV := fun D => vsqOf D.H.V
  honestQ := fun D => (msgD δF hT hP kr hC D).Qc
  honestReq := fun D => rhoVSQ D.H D.t
  honest_staged := fun D => (msgVSQ_staged (sumC := sumCVSQ (F := F) (K := K) hT hP hC)
    (sumM := sumMVSQ (F := F) (K := K) δF hT hP kr hC) D.H D.t D.x).1
  honestBad := fun D => honestBadC D

/-- **`memCoreVSQH`**: `memCoreVSQ` at `sumMVSQ` (`cellChipHQ` 238, `walkChipHQ` 166) with the honest datum. -/
def memCoreVSQH :
    MemCore F K (Quad (algebraMap F K δF)) frameVSQ hC (shapeVSQ hT hP) (tableVSQ hC) 5 where
  Msg0 := Unit
  Msg2 := Quad (algebraMap F K δF) × Quad (algebraMap F K δF)
  chip := fun V t _ ρ yy χ => chipMVSQ δF hT hP kr V t ρ yy χ
  chip_width := fun V t _ ρ yy χ => chipMVSQ_width δF hT hP kr V t ρ yy χ
  internalBound := internalBoundVSQ hT hP hC
  summands := sumMVSQ δF hT hP kr hC
  Honest := HonestVSQD (K := K) δF hT hP hC kr
  honestV := fun D => vsqOf D.H.V
  honestQ := fun D => (msgD δF hT hP kr hC D).Qm
  honestReq := fun D => rhoVSQ D.H D.t
  honest_staged := fun D t => (msgVSQ_staged (sumC := sumCVSQ (F := F) (K := K) hT hP hC)
    (sumM := sumMVSQ (F := F) (K := K) δF hT hP kr hC) D.H D.t D.x).2 t
  honestBad := fun D => honestBadM D

/-- A message at the honest-carrying cores, read at the `Honest := Empty` cores (same fields). -/
def toE (msg : MessagesG (compCoreVSQH (K := K) δF hT hP kr hC) (memCoreVSQH (K := K) δF hT hP kr hC)) :
    MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ (F := F) (K := K) hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ (F := F) (K := K) δF hT hP kr hC)) where
  Qc := msg.Qc
  Qm := msg.Qm
  msg0C := msg.msg0C
  msg0M := msg.msg0M
  requests := msg.requests
  msg2M := msg.msg2M

/-- **`hsoundVSQ` at the honest-carrying cores** (same hypotheses; the chips and summands are those of
`compCoreVSQ / memCoreVSQ`). -/
theorem hsoundVSQH (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => (compCoreVSQH δF hT hP kr hC).reqBound V a +
      (memCoreVSQH δF hT hP kr hC).internalBound V a) (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQH δF hT hP kr hC) (memCoreVSQH δF hT hP kr hC))
    (χ : Coins frameVSQ K) (h : AcceptsG V msg χ)
    (hout : ∀ s ∈ allSummandsG (CC := compCoreVSQH δF hT hP kr hC) (MC := memCoreVSQH δF hT hP kr hC)
        V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC), ¬ s.mem (msg.traces χ) χ) :
    HoldsF (ringChar K) V.claim :=
  hsoundVSQ δF hT hP kr hC V hV (toE δF hT hP kr hC msg) χ ⟨h.compute, h.memory⟩ hout

/-- **`StandaloneG` at the honest-carrying VSQ cores**: soundness by `hsoundVSQ`, completeness by the
generic union bound at every honest datum. -/
theorem standaloneVSQH :
    StandaloneG (compCoreVSQH δF hT hP kr hC) (memCoreVSQH δF hT hP kr hC) (jointVSQ (F := F) (K := K) δF hT hP hC) :=
  standaloneG_of_sound (CC := compCoreVSQH δF hT hP kr hC) (MC := memCoreVSQH δF hT hP kr hC)
    (jointVSQ (F := F) (K := K) δF hT hP hC)
    (fun V hV msg χ h hout => hsoundVSQH δF hT hP kr hC V hV msg χ h hout)

open Classical in
/-- **The completeness half at a datum, valued**: `≤ epsCVSQ`. -/
theorem standaloneVSQH_completeness_le (D : HonestVSQD (K := K) δF hT hP hC kr) :
    ((Finset.univ.filter fun χ : Coins frameVSQ K =>
        ∃ s ∈ honestBadC D ++ honestBadM D,
          s.mem ((msgD δF hT hP kr hC D).Qc χ, (msgD δF hT hP kr hC D).Qm χ) χ).card : ℚ) /
      Fintype.card (Coins frameVSQ K) ≤ epsCVSQ D.H D.t := by
  have h := (standaloneVSQH δF hT hP kr hC).completeness D D rfl rfl
  rw [← epsilon_honestBad D]
  convert h using 4 <;> rfl

open Classical in
/-- **The completeness half is the honest-acceptance premise**: `Pr[¬ HonestGoodVSQ] ≤ Pr[some honest summand
fires]`, so the field re-proves `vsqCompleteness`. -/
theorem prob_not_good_le (D : HonestVSQD (K := K) δF hT hP hC kr)
    (hN : (vsqOf D.H.V).N = (bfsForest [airReorder D.t]).length) :
    ((Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ D.H D.t D.x χ).card : ℚ) /
        Fintype.card (Coins frameVSQ K) ≤
      ((Finset.univ.filter fun χ : Coins frameVSQ K =>
        ∃ s ∈ honestBadC D ++ honestBadM D,
          s.mem ((msgD δF hT hP kr hC D).Qc χ, (msgD δF hT hP kr hC D).Qm χ) χ).card : ℚ) /
        Fintype.card (Coins frameVSQ K) := by
  have hpos : (0 : ℚ) ≤ Fintype.card (Coins frameVSQ K) := by positivity
  refine div_le_div_of_nonneg_right ?_ hpos
  refine Nat.cast_le.mpr (Finset.card_le_card fun χ hχ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
  by_contra hno
  push Not at hno
  exact hχ (good_of_outside D hN _ χ hno)

end Cores

/-! ## 4. Bound and figures at the honest-carrying cores -/

section Figures
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (hT hP kr hC : ℕ)

attribute [local instance] ClaimDenVS.quadCharF

/-- **`ε = boundVCLHQ''`** at the honest-carrying cores, for every pair of first messages. -/
theorem epsilonVSQH_eq (V : VerifierData F K hC (shapeVSQ hT hP)) (x : ClaimMsgVS) (y : Unit) :
    epsilonOf (allSummandsG (CC := compCoreVSQH δF hT hP kr hC) (MC := memCoreVSQH δF hT hP kr hC) V x y
        (jointVSQ δF hT hP hC)) =
      boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) :=
  epsilonVSQ_eq δF hT hP kr hC V ⟨fun _ _ => 0, fun _ _ _ => 0, x, y, fun _ _ => 0, fun _ => (0, 0)⟩

open Classical in
/-- **Soundness at the honest-carrying cores with its `ε`**: `≤ boundVCLHQ''`. -/
theorem standaloneVSQH_soundness_le (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => (compCoreVSQH δF hT hP kr hC).reqBound V a +
      (memCoreVSQH δF hT hP kr hC).internalBound V a) (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQH δF hT hP kr hC) (memCoreVSQH δF hT hP kr hC))
    (hst : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces) :
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) ≤
      boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) := by
  refine ((standaloneVSQH δF hT hP kr hC).soundness V hV msg hst).trans ?_
  exact (epsilonVSQH_eq δF hT hP kr hC V msg.msg0C msg.msg0M).le

open Classical in
/-- The three corners, one proof: a figure of `boundVCLHQ''` at `claimFuel = fuelChip` is a figure of the
false-acceptance fraction. -/
theorem fig_of_bound (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => (compCoreVSQH δF hT hP kr hC).reqBound V a +
      (memCoreVSQH δF hT hP kr hC).internalBound V a) (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQH δF hT hP kr hC) (memCoreVSQH δF hT hP kr hC))
    (hst : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces)
    (hcK : Fintype.card K = cK) (hΛ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110) {b : ℕ}
    (hb : boundVCLHQ'' cK (cK ^ 2) V.N (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) fuelChip < 1 / (2 : ℚ) ^ b) :
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ b := by
  refine lt_of_le_of_lt (standaloneVSQH_soundness_le δF hT hP kr hC V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact hb

end Figures

end

end Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH
