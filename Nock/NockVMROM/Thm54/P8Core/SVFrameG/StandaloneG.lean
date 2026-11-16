/-
  MessagesG, AcceptsG, allSummandsG,
  StandaloneG and the generic skeleton `standaloneG_of_sound` (one obligation per instance).
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.CompCore

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.SVFrameG

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)
open scoped Polynomial

attribute [local instance] Classical.propDecidable

variable {F K Kio : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ}

structure MessagesG (CC : CompCore F K Kio Φ hC S C nAcc) (MC : MemCore F K Kio Φ hC S C nAcc) where
  Qc : Coins Φ K → Fin C.width → F[X]
  Qm : Coins Φ K → ∀ t : Fin S.k, Fin (S.table t).width → F[X]
  msg0C : CC.Msg0
  msg0M : MC.Msg0
  requests : Coins Φ K → Fin nAcc → Kio
  msg2M : Coins Φ K → MC.Msg2

variable {CC : CompCore F K Kio Φ hC S C nAcc} {MC : MemCore F K Kio Φ hC S C nAcc}

def MessagesG.traces (msg : MessagesG CC MC) (χ : Coins Φ K) : Traces F C S := (msg.Qc χ, msg.Qm χ)

structure AcceptsG (V : VerifierData F K hC S) (msg : MessagesG CC MC) (χ : Coins Φ K) : Prop where
  compute : RAP.SatisfiesWithPreprocessing (CC.chip V msg.msg0C (msg.requests χ) χ)
    (fun j => msg.Qc χ (Fin.cast (CC.chip_width _ _ _ _) j))
  memory : ∀ t, RAP.SatisfiesWithPreprocessing
    (MC.chip V t msg.msg0M (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ t (Fin.cast (MC.chip_width _ _ _ _ _ _) j))

def allSummandsG (V : VerifierData F K hC S) (x : CC.Msg0) (y : MC.Msg0)
    (joint : VerifierData F K hC S → CC.Msg0 → MC.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))) :=
  CC.summands V x ++ MC.summands V y ++ joint V x y

structure StandaloneG (CC : CompCore F K Kio Φ hC S C nAcc) (MC : MemCore F K Kio Φ hC S C nAcc)
    (joint : VerifierData F K hC S → CC.Msg0 → MC.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))) : Prop where
  soundness : ∀ (V : VerifierData F K hC S),
    V.Checks (fun a => CC.reqBound V a + MC.internalBound V a) (ringChar Kio) →
    ∀ msg : MessagesG CC MC, TracesStaged Φ C S msg.traces →
    ((Finset.univ.filter fun χ : Coins Φ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card
        : ℚ) / Fintype.card (Coins Φ K) ≤
      epsilonOf (allSummandsG (CC := CC) (MC := MC) V msg.msg0C msg.msg0M joint)
  completeness : ∀ (HC : CC.Honest) (HM : MC.Honest), CC.honestV HC = MC.honestV HM →
    CC.honestReq HC = MC.honestReq HM →
    ((Finset.univ.filter fun χ : Coins Φ K =>
        ∃ s ∈ CC.honestBad HC ++ MC.honestBad HM, s.mem (CC.honestQ HC χ, MC.honestQ HM χ) χ).card
        : ℚ) / Fintype.card (Coins Φ K) ≤ epsilonOf (CC.honestBad HC ++ MC.honestBad HM)

/-- The generic skeleton: the only instance obligation is per-coin soundness. -/
theorem standaloneG_of_sound
    (joint : VerifierData F K hC S → CC.Msg0 → MC.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S)))
    (hsound : ∀ V, V.Checks (fun a => CC.reqBound V a + MC.internalBound V a) (ringChar Kio) →
      ∀ (msg : MessagesG CC MC) χ, AcceptsG V msg χ →
      (∀ s ∈ allSummandsG (CC := CC) (MC := MC) V msg.msg0C msg.msg0M joint,
        ¬ s.mem (msg.traces χ) χ) →
      HoldsF (ringChar K) V.claim) :
    StandaloneG CC MC joint where
  soundness V hV msg hst := by
    classical
    have hsub : (Finset.univ.filter fun χ : Coins Φ K =>
          AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim) ⊆
        unionEvent (allSummandsG (CC := CC) (MC := MC) V msg.msg0C msg.msg0M joint) msg.traces := by
      intro χ hχ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
      simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hno
      push Not at hno
      exact hχ.2 (hsound V hV msg χ hχ.1 hno)
    have hpos : (0 : ℚ) ≤ Fintype.card (Coins Φ K) := by positivity
    refine le_trans (div_le_div_of_nonneg_right ?_ hpos) (union_prob_le _ msg.traces hst)
    exact_mod_cast Finset.card_le_card hsub
  completeness HC HM _ _ := by
    classical
    have hQ : TracesStaged Φ C S (fun χ => (CC.honestQ HC χ, MC.honestQ HM χ)) :=
      ⟨CC.honest_staged HC, fun t => MC.honest_staged HM t⟩
    have h := union_prob_le (CC.honestBad HC ++ MC.honestBad HM)
      (fun χ => (CC.honestQ HC χ, MC.honestQ HM χ)) hQ
    refine le_of_eq_of_le ?_ h
    congr 2

end Nock.NockVMROM.Thm54.SVFrameG
