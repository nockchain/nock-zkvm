/-
  NockvmE2E/Exec/E2E.lean   (proof-only)

  The probabilistic wrapper of `exec_e2e`: lazy = eager random oracle, the fixed-table marginal, and the
  reduction of the flat verifier's bad event to the audited verifier's bad event, pointwise in the table.
-/
import NockvmE2E.Exec.Embed
import NockvmE2E.Merkle.E2E

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec MeasureTheory
open MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2E

open NockvmE2E.Exec.Emb

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort
  NockvmE2E.FriPort.Batched NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
open NockvmE2E.Merkle NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good
  SoundnessWorld SoundnessCoupling BadBound

section Table

variable {D : Type} {R : ∀ _ : D, Type} [DecidableEq D]

/-- The random oracle's answers fixed to the total table `g`; private `unifSpec` draws pass through. -/
noncomputable def withTable (g : ∀ d, R d) : QueryImpl (unifSpec + OracleSpec.ofFn R) ProbComp :=
  unifSpec.passthrough + (QueryImpl.ofFn g).liftTarget ProbComp

theorem fixedTable_query_inr (t : D) (g : ∀ d, R d) (cache : (OracleSpec.ofFn R).QueryCache)
    (hc : cache.AgreesWithFn (QueryImpl.ofFn g)) :
    ∃ cache' : (OracleSpec.ofFn R).QueryCache, cache'.AgreesWithFn (QueryImpl.ofFn g) ∧
      fixedTableLoggedRun (liftM ((unifSpec + OracleSpec.ofFn R).query (.inr t)) :
          OracleComp (unifSpec + OracleSpec.ofFn R) (R t)) g cache =
        pure ((g t, [⟨t, g t⟩]), cache') := by
  rw [fixedTableLoggedRun_hashQuery]
  cases hct : cache t with
  | some u =>
    have hu : u = g t := (hc hct).symm
    subst hu
    refine ⟨cache, hc, ?_⟩
    rw [QueryImpl.withCaching_run_some _ hct]
    simp
  | none =>
    refine ⟨cache.cacheQuery t (g t), ?_, ?_⟩
    · intro t' r h
      by_cases ht : t' = t
      · subst ht
        rw [QueryCache.cacheQuery_self] at h
        cases h; rfl
      · rw [QueryCache.cacheQuery_of_ne _ _ ht] at h
        exact hc h
    · rw [QueryImpl.withCaching_run_none _ hct]
      simp [QueryImpl.liftTarget]
      have : (liftM (m := Id) (g t) : ProbComp (R t)) = pure (g t) := rfl
      rw [this]; simp

theorem fixedTable_marginal_aux {α : Type} (oa : OracleComp (unifSpec + OracleSpec.ofFn R) α)
    (g : ∀ d, R d) (cache : (OracleSpec.ofFn R).QueryCache)
    (hc : cache.AgreesWithFn (QueryImpl.ofFn g)) :
    (fun p => p.1.1) <$> fixedTableLoggedRun oa g cache = simulateQ (withTable g) oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp [fixedTableLoggedRun]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [fixedTableLoggedRun_bind, fixedTableLoggedRun_uniformQuery]
      simp only [simulateQ_bind, simulateQ_liftM_query, map_bind, bind_map_left, Functor.map_map]
      exact bind_congr fun u => ih u cache hc
    | inr t =>
      obtain ⟨cache', hc', hrun⟩ := fixedTable_query_inr t g cache hc
      rw [fixedTableLoggedRun_bind, hrun]
      simp only [simulateQ_bind, simulateQ_liftM_query, pure_bind, Functor.map_map]
      show _ = (pure (g t) : ProbComp _) >>= _
      rw [pure_bind]
      exact ih _ cache' hc'

/-- Caching a total table is transparent: dropping the log and the cache of the fixed-table run leaves the
plain simulation against `g`. -/
theorem fixedTable_marginal {α : Type} (oa : OracleComp (unifSpec + OracleSpec.ofFn R) α)
    (g : ∀ d, R d) :
    (Prod.fst ∘ Prod.fst) <$> fixedTableLoggedRun oa g ∅ = simulateQ (withTable g) oa :=
  fixedTable_marginal_aux oa g ∅ (by intro t r h; simp at h)

/-- If a computation evaluates to `x` against the table `g` (no private draws, every FS/hash answer from `g`),
then simulating it against the table is the point mass at `x`. -/
theorem simulate_of_tabEval_gen (g : ∀ d, R d)
    (f : (t : (unifSpec + OracleSpec.ofFn R).Domain) → Option ((unifSpec + OracleSpec.ofFn R).Range t))
    (hf : ∀ n, f (.inl n) = none) (hg : ∀ d, f (.inr d) = some (g d)) {α : Type}
    (oa : OracleComp (unifSpec + OracleSpec.ofFn R) α) (x : α) (h : tabEval f oa = some x) :
    simulateQ (withTable g) oa = pure x := by
  induction oa using OracleComp.inductionOn generalizing x with
  | pure a =>
    rw [tabEval_pure] at h
    cases h
    simp
  | query_bind t k ih =>
    rw [tabEval_query_bind] at h
    cases t with
    | inl n =>
      rw [hf n] at h
      cases h
    | inr d =>
      rw [hg d] at h
      simp only [simulateQ_bind, simulateQ_liftM_query]
      show (pure (g d) : ProbComp _) >>= _ = _
      rw [pure_bind]
      exact ih _ x h

/-- One table, pointwise: if `E g o` forces the continuation to be the point mass at a bad value, then the
event `E` of the flat run is at most the event `B` of the continued run. -/
theorem pr_table_le {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ) (E : β → Prop) (B : γ → Prop)
    (h : ∀ o, E o → ∃ c, f o = pure c ∧ B c) :
    Pr{let o ← mx}[E o] ≤ Pr{let y ← mx >>= f}[B y] := by
  classical
  let : MeasurableSpace β := ⊤
  have : DiscreteMeasurableSpace β := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [prEvent_bind_eq_lintegral_of_discrete]
  have h1 : Pr{let o ← mx}[E o] = Pr{let y ← mx >>= pure}[E y] := by rw [bind_pure]
  rw [h1, prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_mono fun o => ?_
  rw [prEvent_pure]
  by_cases hE : E o
  · obtain ⟨c, hc, hB⟩ := h o hE
    rw [hc, prEvent_pure]; simp [hE, hB]
  · simp [hE]

/-- **Lazy = eager, pointwise reduction.** Sampling a total table `g` and running `oa` against it (with the
event allowed to read `g`) is at most the bad event of the lazy cached random-oracle run of `oa >>= cont`,
whenever `E g o` makes the continuation deterministic and bad. -/
theorem pr_flat_le_audited [Finite D] [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]
    {β γ : Type} (oa : OracleComp (unifSpec + OracleSpec.ofFn R) β)
    (cont : β → OracleComp (unifSpec + OracleSpec.ofFn R) γ)
    (E : (∀ d, R d) → β → Prop) (B : γ → Prop)
    (h : ∀ g o, E g o → ∃ c, simulateQ (withTable g) (cont o) = pure c ∧ B c) :
    Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (withTable g) oa}[E g o] ≤
      Pr{let j ← randomOracleLoggedRun (oa >>= cont) ∅}[B j.1.1] := by
  classical
  let : MeasurableSpace (∀ d, R d) := ⊤
  have : DiscreteMeasurableSpace (∀ d, R d) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let : MeasurableSpace ((γ × QueryLog (OracleSpec.ofFn R)) × (OracleSpec.ofFn R).QueryCache) := ⊤
  have : DiscreteMeasurableSpace ((γ × QueryLog (OracleSpec.ofFn R)) × (OracleSpec.ofFn R).QueryCache) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_eq_evalDist_of_discrete (randomOracleLoggedRun (oa >>= cont) ∅) (fun j => B j.1.1),
    evalDist_randomOracleLoggedRun_eq_fixedTable_finite, ← prEvent_eq_evalDist_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_mono fun g => ?_
  rw [completeTable_empty]
  refine le_of_le_of_eq ?_ (prEvent_map (fixedTableLoggedRun (oa >>= cont) g ∅) (Prod.fst ∘ Prod.fst) B)
  rw [fixedTable_marginal, simulateQ_bind]
  exact pr_table_le _ _ _ _ (h g)

end Table

/-- the table-evaluation of the compiled experiment's verifier, as a simulation (instance of the generic lemma) -/
theorem simulate_of_tabEval {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]
    {Query : Type} [DecidableEq Query] {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt]
    {ms : MRounds Dg}
    (g : ∀ d, succinctRange Dg Op Query Statement Salt ms d) {α : Type}
    (oc : OracleComp (SuccinctSpecK Dg Op Query Statement Salt ms) α) (x : α)
    (h : tabEval (tabK g) oc = some x) :
    simulateQ (withTable g) oc = pure x :=
  simulate_of_tabEval_gen g (tabK g) (fun _ => rfl) (fun _ => rfl) oc x h

section Final

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg] (enc : F ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]

local notation "MS" => msC P A R0 Rest RestV e I0 I Ifin nb s d 170 Dg enc md L (S := F)

/-- The audited adversary obtained from a flat one: same queries, outputs re-packaged by `emb`
(flat proof to audited public messages). -/
def embedAdv {Pf : Type} {ms : MRounds Dg} {Op : Type} [Finite Op] [DecidableEq Op]
    (emb : Pf → PublicMessages (compiledRoundsK Dg Op ms))
    (Aflat : OracleComp (SuccinctSpecK Dg Op Query Statement Salt ms) (Option (Statement × Salt × Pf × W))) :
    SuccinctAdversaryK Dg Op Query Statement Salt W ms :=
  (Option.map fun x : Statement × Salt × Pf × W => (x.1, (x.2.1, emb x.2.2.1), x.2.2.2)) <$> Aflat

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers in
/-- **`exec_e2e` modulo the pointwise embedding**.  A flat adversary `Aflat` runs against ONE lazy
random oracle on `Query ⊕ Key` (the very oracle of `rap_fri_merkle_sound_deep_numbers`), here presented
eagerly as a uniformly sampled total table `g` (lazy = eager, `evalDist_randomOracleLoggedRun_eq_fixedTable_finite`).
`Acc g z π` abstracts "the flat verifier, reading `g` through its flat hash/FS views, accepts `(z, π)`"
(at `exec_e2e`: `verifyFlat XI (Hof g) (FSdec g) (encZ z) π = true`).  The pointwise hypothesis `hpt` says that
acceptance forces the audited verifier, run against the table, to return a path on the embedded messages
`emb π`; it is the only link left to the table soundness lemma (`verifyFlat_sound_tab`).  Conclusion: the event
"flat verifier accepts, and the claim fails" has probability `≤ 2^-82`. -/
theorem exec_e2e_of_pointwise [Finite Query] [Finite Statement] [Finite Salt]
    [SampleableType (∀ d, succinctRange Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt (MS) d)]
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (MS))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS)))
    (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, Polynomial.eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (hs : ∀ i, s i = 1) (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (htoPoly : P.toPoly = udDecodeB ω (31 / 64) (friBound s d))
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg)
    {Pf : Type}
    (emb : Pf → PublicMessages (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS)))
    (Acc : (∀ d, succinctRange Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt (MS) d) →
      Statement × Salt → Pf → Prop)
    (hpt : ∀ g z π, Acc g z π → ∃ p, tabEval (tabK g)
      (succinctVerifyK guards (merkleCheck (merkleSkels (MS)) model id)
        (cLocal P A R0 Rest RestV e I0 I Ifin nb s d 170 (univariatePowersGenerator F m) Dg enc md L
          (by have : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val) := by omega
              exact this.trans hrate)
          (OpenAll Dg (merkleSkels (MS))) id) z (emb π)) = some (some p))
    (Aflat : OracleComp (SuccinctSpecK Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt (MS))
      (Option (Statement × Salt × Pf × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))).QueryCache)
      Q_FS (verifiedFS guards (embedAdv Dg emb Aflat)))
    (hHq : IsQueryBoundP (embedAdv Dg emb Aflat)
      (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (MS)).length) (op : OpenAll Dg (merkleSkels (MS)))
      (logs : Fin (merkleSkels (MS)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (MS)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MS))).nodeBudget tag ≤ Pn) :
    Pr{let g ← $ᵗ (∀ d, succinctRange Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt (MS) d);
       let o ← simulateQ (withTable g) Aflat}[
      match o with | none => False | some (z, salt, π, _) => Acc g (z, salt) π ∧ ¬ R0.Holds] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hbound := rap_fri_merkle_sound_deep_numbers P A R0 Rest RestV e I0 I Ifin nb s d Dg enc md L model guards
    hR0 hlink hnb hRest errOld herr0 hs hrate hn hF hm htoPoly hns hD hH hnq herrOld hnb30 hDg
    (embedAdv Dg emb Aflat) Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  refine le_trans ?_ hbound
  generalize merkleCheck (merkleSkels (MS)) model id = mc at hpt hbound ⊢
  generalize cLocal P A R0 Rest RestV e I0 I Ifin nb s d 170 (univariatePowersGenerator F m) Dg enc md L
    (by have : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val) := by omega
        exact this.trans hrate)
    (OpenAll Dg (merkleSkels (MS))) id = la at hpt hbound ⊢
  have hshape : succinctAcceptedExecutionK guards mc la (embedAdv Dg emb Aflat) =
      Aflat >>= (fun o => match o with
        | none => pure none
        | some (z, salt, π, w) => do
            let path ← succinctVerifyK guards mc la (z, salt) (emb π)
            pure (path.map fun p => ((z, salt), p, w))) := by
    simp only [succinctAcceptedExecutionK, embedAdv, map_eq_bind_pure_comp, bind_assoc, bind_pure_comp]
    refine bind_congr fun o => ?_
    cases o <;> rfl
  rw [hshape]
  refine pr_flat_le_audited Aflat _ _ (fun y : Option ((Statement × Salt) × (protocol (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS))).tree.ExecutionPath × W) => match y with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}) ?_
  rintro g (_ | ⟨z, salt, π, w⟩) hE
  · exact hE.elim
  · obtain ⟨hacc, hnot⟩ := hE
    obtain ⟨p, hp⟩ := hpt g _ π hacc
    refine ⟨some ((z, salt), p, w), ?_, hnot⟩
    simp only [simulateQ_bind, simulate_of_tabEval g _ _ hp, pure_bind, simulateQ_pure]
    rfl

end Final

/-! ## Non-vacuity -/

section NonVac

variable {D : Type} {R : ∀ _ : D, Type} [DecidableEq D]

/-- The empty adversary (`Aflat := pure none`) has probability zero, for every event shape. -/
theorem pr_pure_none [Finite D] [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)] {β : Type}
    (E : (∀ d, R d) → Option β → Prop) (hE : ∀ g, ¬ E g none) :
    Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (withTable g) (pure none : OracleComp (unifSpec + OracleSpec.ofFn R) (Option β))}[E g o] = 0 := by
  classical
  let : MeasurableSpace (∀ d, R d) := ⊤
  have : DiscreteMeasurableSpace (∀ d, R d) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete]
  simp only [simulateQ_pure, prEvent_pure]
  simp [hE]

/-- The trivial verifier (accepts nothing) satisfies the pointwise hypothesis, for any evaluation. -/
theorem hpt_trivial {Gt Zt Pt Ph : Type} (V : Gt → Zt → Pt → Option (Option Ph)) :
    ∀ g z π, (fun (_ : Gt) (_ : Zt) (_ : Pt) => False) g z π → ∃ p, V g z π = some (some p) :=
  fun _ _ _ h => h.elim

/-- The pointwise hypothesis is also satisfiable with `Acc` inhabited: a verifier that always returns a path. -/
example : ∀ (g : Unit) (z : Unit) (π : Unit), (fun (_ : Unit) (_ : Unit) (_ : Unit) => True) g z π →
    ∃ p : Unit, (fun (_ : Unit) (_ : Unit) (_ : Unit) => some (some ())) g z π = some (some p) :=
  fun _ _ _ _ => ⟨(), rfl⟩

/-- A concrete evaluation: one hash query against a table over `Fin 2` is the point mass at the table's answer
(the hypotheses of `simulate_of_tabEval_gen` are inhabited, so it is not vacuous). -/
example (g : Fin 2 → Bool) :
    simulateQ (withTable (R := fun _ : Fin 2 => Bool) g)
      (liftM ((unifSpec + OracleSpec.ofFn (fun _ : Fin 2 => Bool)).query (.inr 0)) :
        OracleComp (unifSpec + OracleSpec.ofFn (fun _ : Fin 2 => Bool)) Bool) = pure (g 0) := by
  refine simulate_of_tabEval_gen (R := fun _ : Fin 2 => Bool) g
    (fun t => match t with | .inl _ => none | .inr d => some (g d)) (fun _ => rfl) (fun _ => rfl) _ (g 0) ?_
  rw [tabEval_liftM_query]

/-- A concrete fixed-table marginal: the log and cache of the fixed-table run are dropped. -/
example (g : Fin 2 → Bool) :
    (Prod.fst ∘ Prod.fst) <$> fixedTableLoggedRun
      (liftM ((unifSpec + OracleSpec.ofFn (fun _ : Fin 2 => Bool)).query (.inr 1)) :
        OracleComp (unifSpec + OracleSpec.ofFn (fun _ : Fin 2 => Bool)) Bool) g ∅ =
      pure (g 1) := by
  rw [fixedTable_marginal]
  refine simulate_of_tabEval_gen (R := fun _ : Fin 2 => Bool) g
    (fun t => match t with | .inl _ => none | .inr d => some (g d)) (fun _ => rfl) (fun _ => rfl) _ (g 1) ?_
  rw [tabEval_liftM_query]

end NonVac

#print axioms withTable
#print axioms fixedTable_marginal
#print axioms simulate_of_tabEval
#print axioms pr_flat_le_audited
#print axioms exec_e2e_of_pointwise
#print axioms pr_pure_none
#print axioms hpt_trivial

end NockvmE2E.Exec.E2E
