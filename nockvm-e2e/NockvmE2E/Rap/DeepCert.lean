/-
goal 3: the `Certificate` of the extended RAP (`Rap/Bridge.lean`), so that `rap_rbr_knowledge` and
`rap_singleSalt_knowledge_soundness` apply to `P.statement R0 Rest` unchanged.
-/
import NockvmE2E.Rap.Bridge
import NockvmE2E.Rap.DeepSound

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace NockvmE2E.Rap

section
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

theorem local_liftS {s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)} {b : ℕ} (h : Local s b) :
    Local (P.liftS s) b where
  coins_block := h.coins_block
  dep_le := h.dep_le
  congr tr tr' χ χ' ht hc := h.congr (P.restr tr) (P.restr tr') χ χ' (fun j hj => ht (Sum.inl j) hj) hc

theorem local_sAlpha : Local P.sAlpha P.R where
  coins_block i hi := by
    have : i = P.a := Finset.mem_singleton.mp hi
    subst this; exact P.ha
  dep_le i hi := by
    have : Φ.sampledAfter i < P.R := by simpa [DeepParams.sAlpha] using hi
    omega
  congr tr tr' χ χ' ht hc := by
    have : P.restr tr = P.restr tr' := funext fun j => ht (Sum.inl j) (P.hcol j)
    show P.badAlpha χ (P.restr tr) = P.badAlpha χ' (P.restr tr')
    rw [this]
    exact P.badAlpha_congr χ χ' (fun i hi => hc i (by simpa [DeepParams.sAlpha] using hi)) _

theorem local_sZeta : Local P.sZeta (P.R + 1) where
  coins_block i hi := by
    have : i = P.z := Finset.mem_singleton.mp hi
    subst this; exact P.hz
  dep_le i hi := by
    have : Φ.sampledAfter i ≤ P.R := by simpa [DeepParams.sZeta] using hi
    omega
  congr tr tr' χ χ' ht hc := by
    have h1 : tr = tr' := funext fun j => ht j (by
      rcases j with j | j
      · exact (P.hcol j).trans (Nat.le_succ _)
      · exact le_rfl)
    have h2 : χ P.a = χ' P.a := hc P.a (by simp [DeepParams.sZeta, P.ha])
    show P.badZeta χ tr (χ P.a) = P.badZeta χ' tr' (χ' P.a)
    have hg : ∀ tr α, P.Gpoly χ tr α = P.Gpoly χ' tr α := fun tr α =>
      P.Gpoly_congr χ χ' (fun i hi => hc i (by simpa [DeepParams.sZeta] using hi.le)) tr α
    rw [h1, h2]
    unfold DeepParams.badZeta
    simp only [hg]

/-- **Goal 3: the certificate of the extended RAP.** `blk'` is any block assignment extending the old one
(`blk (liftS s) = blk0 s`) with `s_α ↦ R`, `s_ζ ↦ R+1`; `R+1 < nb`. Then `rap_rbr_knowledge` and
`rap_singleSalt_knowledge_soundness` apply to `P.statement R0 Rest`. -/
theorem certificate_deep (R0 : RapStatement Φ K ι β colRound) (Rest)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (blk0 : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound) → ℕ) (nb : ℕ)
    (hold : Certificate R0 blk0 nb) (hnb : P.R + 1 < nb)
    (blk' : BadSummand Φ K (DeepTr P) (DeepStaged P) → ℕ)
    (hl : ∀ m0, ∀ s ∈ R0.summands m0, blk' (P.liftS s) = blk0 s)
    (hα : blk' P.sAlpha = P.R) (hζ : blk' P.sZeta = P.R + 1) :
    Certificate (P.statement R0 Rest) blk' nb where
  sound := soundG_deep P R0 Rest hold.sound hlink
  local_ m0 s hs := by
    simp only [DeepParams.statement, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with ⟨s0, hs0, rfl⟩ | rfl | rfl
    · rw [hl m0 s0 hs0]; exact local_liftS P (hold.local_ m0 s0 hs0)
    · rw [hα]; exact local_sAlpha P
    · rw [hζ]; exact local_sZeta P
  blk_lt m0 s hs := by
    simp only [DeepParams.statement, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with ⟨s0, hs0, rfl⟩ | rfl | rfl
    · rw [hl m0 s0 hs0]; exact hold.blk_lt m0 s0 hs0
    · rw [hα]; omega
    · rw [hζ]; exact hnb

end

end NockvmE2E.Rap
