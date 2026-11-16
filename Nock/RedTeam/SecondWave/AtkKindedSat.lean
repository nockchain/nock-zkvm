/-
  This file supplies the missing artifact and records what the
  plan's `KindedSat` as literally written does and does not give.
-/
import Nock.AIR

namespace AtkKS

open Nock Nock.Reified Nock.Reified.Trans

variable {K : Type*} [Field K]

/-- The plan's `KindedSat`, transcribed verbatim from the D1a code block. -/
def KindedSat (air : AIR) (rowEnv : ℕ → Env K) (n : ℕ) : Prop :=
  (∀ c ∈ air.constraints, c.kind = .boundary → c.expr.eval (rowEnv 0) = 0) ∧
  (∀ c ∈ air.constraints, c.kind = .transition →
      ∀ i, i < n → c.expr.eval (twoRow (rowEnv i) (rowEnv (i + 1))) = 0) ∧
  (∀ c ∈ air.constraints, c.kind = .terminal → c.expr.eval (rowEnv n) = 0) ∧
  (∀ c ∈ air.constraints, c.kind = .row → ∀ i, i ≤ n → c.expr.eval (rowEnv i) = 0)

variable {L : Type*} [Field L]

/-- **D1a CONFIRMED.**  The claimed biconditional does hold, and is kernel-clean. -/
theorem progIOSat_iff_kindedSat (a : ℕ → L) (accP : ℕ → RatFunc L) (requests : RatFunc L)
    (k₁ : ℕ) :
    IO.ProgIOSat a accP requests k₁
      ↔ KindedSat ioProgAIR (ioProgRowEnv a accP requests) k₁ := by
  rw [reified_io_prog_sound]
  constructor
  · rintro ⟨hi, hs, ht⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c hc hk <;>
      · simp only [ioProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp_all
  · rintro ⟨hb, htr, hte, -⟩
    refine ⟨hb ⟨.boundary, ioProgInit⟩ (by simp [ioProgAIR]) rfl, ?_,
            hte ⟨.terminal, ioProgTerm⟩ (by simp [ioProgAIR]) rfl⟩
    exact htr ⟨.transition, ioProgStep⟩ (by simp [ioProgAIR]) rfl

/-! `computeAIRchained` has **zero** `.boundary` and **zero** `.terminal` constraints and 526 of its
  527 constraints are `.row` (see `atk_degree.lean`).  So for the compute chip, `KindedSat`
  reduces to "all 526 row constraints on rows `0..n`, plus `lnChainExpr` on `i < n`" — the
  boundary/terminal machinery D1b spends four pages on is *memory-only*. -/

/-- For any AIR with no boundary and no terminal constraints, the first and third conjuncts of
    `KindedSat` are vacuous. -/
theorem kindedSat_degenerates_without_boundary_or_terminal
    (air : AIR) (rowEnv : ℕ → Env K) (n : ℕ)
    (hb : ∀ c ∈ air.constraints, c.kind ≠ .boundary)
    (ht : ∀ c ∈ air.constraints, c.kind ≠ .terminal) :
    KindedSat air rowEnv n ↔
      ((∀ c ∈ air.constraints, c.kind = .transition →
          ∀ i, i < n → c.expr.eval (twoRow (rowEnv i) (rowEnv (i + 1))) = 0) ∧
       (∀ c ∈ air.constraints, c.kind = .row → ∀ i, i ≤ n → c.expr.eval (rowEnv i) = 0)) := by
  constructor
  · rintro ⟨-, h2, -, h4⟩; exact ⟨h2, h4⟩
  · rintro ⟨h2, h4⟩
    exact ⟨fun c hc hk => absurd hk (hb c hc), h2, fun c hc hk => absurd hk (ht c hc), h4⟩

end AtkKS

section Audit
#print axioms AtkKS.progIOSat_iff_kindedSat
#print axioms AtkKS.kindedSat_degenerates_without_boundary_or_terminal
end Audit
