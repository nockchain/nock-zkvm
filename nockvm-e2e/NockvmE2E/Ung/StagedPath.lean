/-
how the traces and coins written by a path (`finalOf`) depend on its first `n` rounds, and how
equality of the written round-`n` commitments gives equality of the round-`n` message (`MAt`).
-/
import NockvmE2E.Ung.Consist
import NockvmE2E.Rap.Bridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Ung

open NockvmE2E.Rap Interaction.Oracle Interaction.Oracle.Security.StateRestoration

section Path

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}
  [SampleableType K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  (R : RapStatement Φ K ι β colRound)
  [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (Ifin : OracleInterface R.Mfin)

/-- Rounds outside the window `[r, r+k)` leave the accumulators untouched. -/
theorem finalOf_out : ∀ (k r : ℕ) (tr : Tr ι β) (χ : Coins Φ K)
    (path : (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).tree.ExecutionPath),
    (∀ j, ¬ (r ≤ colRound j ∧ colRound j < r + k) → (finalOf R I Ifin r k tr χ path).1 j = tr j) ∧
    (∀ i, ¬ (r ≤ Φ.sampledAfter i ∧ Φ.sampledAfter i < r + k) →
      (finalOf R I Ifin r k tr χ path).2.1 i = χ i)
  | 0, _, _, _, _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | k + 1, r, tr, χ, path => by
      have ih := finalOf_out k (r + 1) (setCols r path.1 tr) (setBlock r path.2.1 χ) path.2.2
      refine ⟨fun j hj => ?_, fun i hi => ?_⟩
      · have hne : colRound j ≠ r := by omega
        have e : setCols r (path.1 : Cols colRound β r) tr j = tr j := setCols_of_ne _ _ hne
        rw [finalOf, ih.1 j (by omega)]
        exact e
      · have hne : Φ.sampledAfter i ≠ r := by omega
        have e : setBlock r (path.2.1 : Block Φ K r) χ i = χ i := setBlock_of_ne _ _ hne
        rw [finalOf, ih.2 i (by omega)]
        exact e

/-- If two paths agree on their first `n ≤ k` rounds (messages and challenges), their written traces and coins
agree outside the window `[r+n, r+k)`, provided the accumulators agree outside `[r, r+k)`. -/
theorem finalOf_agree : ∀ (k r n : ℕ), n ≤ k → ∀ (tr tr' : Tr ι β) (χ χ' : Coins Φ K)
    (P P' : (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).tree.ExecutionPath),
    PEq _ n P P' →
    (∀ j, ¬ (r ≤ colRound j ∧ colRound j < r + k) → tr j = tr' j) →
    (∀ i, ¬ (r ≤ Φ.sampledAfter i ∧ Φ.sampledAfter i < r + k) → χ i = χ' i) →
    (∀ j, ¬ (r + n ≤ colRound j ∧ colRound j < r + k) →
      (finalOf R I Ifin r k tr χ P).1 j = (finalOf R I Ifin r k tr' χ' P').1 j) ∧
    (∀ i, ¬ (r + n ≤ Φ.sampledAfter i ∧ Φ.sampledAfter i < r + k) →
      (finalOf R I Ifin r k tr χ P).2.1 i = (finalOf R I Ifin r k tr' χ' P').2.1 i)
  | 0, r, n, hn, tr, tr', χ, χ', P, P', _, h1, h2 => by
      refine ⟨fun j hj => ?_, fun i hi => ?_⟩
      · exact h1 j (by omega)
      · exact h2 i (by omega)
  | k + 1, r, 0, _, tr, tr', χ, χ', P, P', _, h1, h2 => by
      refine ⟨fun j hj => ?_, fun i hi => ?_⟩
      · rw [(finalOf_out R I Ifin (k + 1) r tr χ P).1 j (by omega),
          (finalOf_out R I Ifin (k + 1) r tr' χ' P').1 j (by omega)]
        exact h1 j (by omega)
      · rw [(finalOf_out R I Ifin (k + 1) r tr χ P).2 i (by omega),
          (finalOf_out R I Ifin (k + 1) r tr' χ' P').2 i (by omega)]
        exact h2 i (by omega)
  | k + 1, r, n + 1, hn, tr, tr', χ, χ', P, P', hP, h1, h2 => by
      obtain ⟨hm, hc, hP⟩ := hP
      have ih := finalOf_agree k (r + 1) n (by omega) (setCols r P.1 tr) (setCols r P'.1 tr')
        (setBlock r P.2.1 χ) (setBlock r P'.2.1 χ') P.2.2 P'.2.2 hP
        (fun j hj => by
          by_cases hr : colRound j = r
          · simp only [setCols, hr, dite_true]
            rw [hm]
          · have e1 : setCols r (P.1 : Cols colRound β r) tr j = tr j := setCols_of_ne _ _ hr
            have e2 : setCols r (P'.1 : Cols colRound β r) tr' j = tr' j := setCols_of_ne _ _ hr
            rw [e1, e2]
            exact h1 j (by omega))
        (fun i hi => by
          by_cases hr : Φ.sampledAfter i = r
          · simp only [setBlock, hr, dite_true]
            rw [hc]
          · have e1 : setBlock r (P.2.1 : Block Φ K r) χ i = χ i := setBlock_of_ne _ _ hr
            have e2 : setBlock r (P'.2.1 : Block Φ K r) χ' i = χ' i := setBlock_of_ne _ _ hr
            rw [e1, e2]
            exact h2 i (by omega))
      refine ⟨fun j hj => ?_, fun i hi => ?_⟩
      · rw [finalOf, finalOf]
        exact ih.1 j (by omega)
      · rw [finalOf, finalOf]
        exact ih.2 i (by omega)

/-- Equality of the written round-`r+n` columns gives equality of the round-`n` message. -/
theorem finalOf_msg : ∀ (k r n : ℕ), n < k → ∀ (tr tr' : Tr ι β) (χ χ' : Coins Φ K)
    (P P' : (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).tree.ExecutionPath),
    (∀ j, colRound j = r + n → (finalOf R I Ifin r k tr χ P).1 j = (finalOf R I Ifin r k tr' χ' P').1 j) →
    MAt _ n P P'
  | 0, r, n, hn, _, _, _, _, _, _, _ => absurd hn (by omega)
  | k + 1, r, 0, _, tr, tr', χ, χ', P, P', h => by
      show P.1 = P'.1
      funext ⟨j, hj⟩
      have hj' : colRound j = r + 0 := hj
      have e := h j hj'
      rw [finalOf, finalOf, (finalOf_out R I Ifin k (r + 1) _ _ P.2.2).1 j (by omega),
        (finalOf_out R I Ifin k (r + 1) _ _ P'.2.2).1 j (by omega)] at e
      simpa [setCols, hj] using e
  | k + 1, r, n + 1, hn, tr, tr', χ, χ', P, P', h => by
      exact finalOf_msg k (r + 1) n (by omega) _ _ _ _ P.2.2 P'.2.2 (fun j hj => by
        have := h j (by omega)
        rwa [finalOf, finalOf] at this)

end Path

end NockvmE2E.Ung
