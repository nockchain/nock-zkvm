/-
SUCC-0, nockvm review  point (a)/(b)-(ii): column-locality is NOT an extra input. Our `Rap.Local`
(bad set reads only early columns, for ALL traces) follows from the nockvm library's `BadSummand.readsOn` (STAGED traces
only) plus the two facts nockvm named as explicit hypotheses:
  (ii)  all priced coins of a summand lie in ONE sampling round (not type-enforced on the nockvm library), and they are
        nonempty;
  (dep) every read coin (`dep`) is sampled no later than the priced ones;
and `|K| ≥ 2`. The trick: a fixed trace prefix is the CONSTANT (hence staged) coin function, and two traces
that agree on the columns committed by block `b` are glued into ONE staged function by branching on a
priced coin `c` (sampled after block `b`, so later columns may read it; `c ∉ dep`, so `readsOn` ignores it).
The block of a summand is read off its own coins (`blkOf`), so no external block map is needed.
-/
import NockvmE2E.Rap.Frame

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Succ

open NockvmE2E.Rap

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}

/--  (b)-(ii) + the dep half: the summand prices a nonempty set of coins, all sampled in ONE
round, and reads only coins sampled no later than that round. -/
structure OneRound (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) : Prop where
  ne : s.coins.Nonempty
  same : ∀ i ∈ s.coins, ∀ i' ∈ s.coins, Φ.sampledAfter i = Φ.sampledAfter i'
  dep_le : ∀ i ∈ s.dep, ∀ i' ∈ s.coins, Φ.sampledAfter i ≤ Φ.sampledAfter i'

open Classical in
/-- The sampling round of a summand, read off its priced coins (`0` if it prices none). -/
noncomputable def blkOf (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) : ℕ :=
  if h : s.coins.Nonempty then Φ.sampledAfter h.choose else 0

theorem sampledAfter_eq_blkOf {s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)}
    (h : OneRound s) {i : Fin Φ.n} (hi : i ∈ s.coins) : Φ.sampledAfter i = blkOf s := by
  unfold blkOf
  simp only [h.ne, dite_true]
  exact h.same i hi _ h.ne.choose_spec

/-- **: `readsOn` (staged traces) ⇒ `Local` (all traces)**, given `OneRound` and `|K| ≥ 2`. -/
theorem local_of_readsOn (hK : 1 < Fintype.card K)
    (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) (h : OneRound s) :
    Local s (blkOf s) := by
  obtain ⟨k0, k1, hk⟩ := Fintype.exists_pair_of_one_lt_card hK
  obtain ⟨c, hc⟩ := h.ne
  have hcb : Φ.sampledAfter c = blkOf s := sampledAfter_eq_blkOf h hc
  have hcd : c ∉ s.dep := fun hd => Finset.disjoint_left.mp s.disj hc hd
  -- coin part: at a fixed trace (constant, hence staged) the bad set reads only `dep`
  have hcoin : ∀ (tr : Tr ι β) (χ χ' : Coins Φ K), (∀ i ∈ s.dep, χ i = χ' i) →
      s.badSet tr χ = s.badSet tr χ' := fun tr χ χ' hd =>
    s.readsOn (fun _ => tr) (fun _ _ _ _ => rfl) χ χ' hd
  refine ⟨fun i hi => sampledAfter_eq_blkOf h hi, fun i hi => (h.dep_le i hi c hc).trans hcb.le, ?_⟩
  intro tr tr' χ χ' ht hd
  -- glue `tr`, `tr'` into one staged coin function by branching on the priced coin `c`
  let Q : Coins Φ K → Tr ι β := fun ψ => if ψ c = k0 then tr else tr'
  have hQ : TracesStaged Φ colRound Q := by
    intro j ψ ψ' hψ
    by_cases hj : colRound j ≤ blkOf s
    · simp only [Q]; split_ifs <;> simp [ht j hj]
    · have : ψ c = ψ' c := hψ c (by omega)
      simp only [Q, this]
  let χ0 := Function.update χ c k0
  let χ1 := Function.update χ' c k1
  have hupd : ∀ i ∈ s.dep, χ0 i = χ1 i := by
    intro i hi
    have hne : i ≠ c := fun e => hcd (e ▸ hi)
    simp [χ0, χ1, Function.update_of_ne hne, hd i hi]
  have key : s.badSet (Q χ0) χ0 = s.badSet (Q χ1) χ1 := s.readsOn Q hQ χ0 χ1 hupd
  have hQ0 : Q χ0 = tr := by simp [Q, χ0]
  have hQ1 : Q χ1 = tr' := by simp [Q, χ1, Ne.symm hk]
  rw [hQ0, hQ1] at key
  have e0 : s.badSet tr χ = s.badSet tr χ0 := hcoin tr χ χ0 (fun i hi => by
    have hne : i ≠ c := fun e => hcd (e ▸ hi)
    simp [χ0, Function.update_of_ne hne])
  have e1 : s.badSet tr' χ' = s.badSet tr' χ1 := hcoin tr' χ' χ1 (fun i hi => by
    have hne : i ≠ c := fun e => hcd (e ▸ hi)
    simp [χ1, Function.update_of_ne hne])
  rw [e0, e1, key]

end NockvmE2E.Succ
