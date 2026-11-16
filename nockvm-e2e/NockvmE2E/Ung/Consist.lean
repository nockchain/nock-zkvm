/-
RANDOM-ORACLE CONSISTENCY of two FS-verified paths.

With a fixed salt, two FS-verified paths of one experiment that share a prefix of prover messages (and the
statement) have the same challenges on that prefix: the challenge at round `i` is the oracle answer at the key
"statement, messages `0..i`, and the earlier challenges", and the lazy oracle returns the cached answer on a repeated
key. This file proves it for the verification program `publicStoppedVerify` of Quang Dao's FS files, WITHOUT changing
any of its statements: `PathCached c …` says the path's challenges are the cache entries at the path's keys, it holds
for every path returned by a verification run on the cache the run leaves behind (`mapped_cached`), the cache only
grows (`ro_le`), and so two paths cached in one cache agree on the challenges wherever their messages agree
(`chal_of_msgs`).
-/
import NockvmE2E.Ung.Positive

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

namespace NockvmE2E.Ung

/-! ## 1. The cache only grows; a hash query leaves its answer in the cache -/

section Cache

variable {D : Type} {R' : D → Type} [DecidableEq D] [∀ d, SampleableType (R' d)]

theorem ro_hash_support (t : D) (cache : (OracleSpec.ofFn R').QueryCache)
    (p) (hp : p ∈ support (randomOracleLoggedRun
      (liftM ((unifSpec + OracleSpec.ofFn R').query (.inr t)) :
        OracleComp (unifSpec + OracleSpec.ofFn R') (R' t)) cache)) :
    p.2 t = some p.1.1 ∧ cache ≤ p.2 := by
  rw [randomOracleLoggedRun_hashQuery, support_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [randomOracle.run_eq] at hq
  cases hc : cache t with
  | some u =>
    rw [hc] at hq
    simp only [support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨hc, le_rfl⟩
  | none =>
    rw [hc] at hq
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hq
    obtain ⟨u, _, rfl⟩ := hq
    exact ⟨QueryCache.cacheQuery_self cache t u, QueryCache.le_cacheQuery cache hc⟩

theorem ro_le {α : Type} (oa : OracleComp (unifSpec + OracleSpec.ofFn R') α) :
    ∀ (cache : (OracleSpec.ofFn R').QueryCache), ∀ x ∈ support (randomOracleLoggedRun oa cache), cache ≤ x.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro cache x hx
      rw [ro_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact le_rfl
  | query_bind t k ih =>
      intro cache x hx
      rw [randomOracleLoggedRun_bind, support_bind] at hx
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      have h1 : cache ≤ p.2 := by
        rcases t with n | d
        · rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
          obtain ⟨u, _, rfl⟩ := hp
          exact le_rfl
        · exact (ro_hash_support d cache p hp).2
      exact h1.trans (ih p.1.1 p.2 q hq)

end Cache

/-! ## 2. Paths whose challenges are cache entries -/

section Cached

variable {Input : Type} {allRounds : List Round}

/-- The path's challenge at every round is the cache entry at the path's key at that round
(key = statement, the messages and challenges before, this round's message). -/
def PathCached (c : (oracleSpec Input PUnit allRounds).QueryCache) :
    (rounds : List Round) → Input →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (∀ key, (embed key).Challenge = key.Challenge) →
    (protocol rounds).tree.ExecutionPath → Prop
  | [], _, _, _, _ => True
  | _ :: rounds, z, embed, preserve, path =>
      c (embed (Key.here z path.1 PUnit.unit)) =
        some (cast (preserve (Key.here z path.1 PUnit.unit)).symm path.2.1) ∧
      PathCached c rounds z (fun key => embed (Key.later path.1 PUnit.unit key))
        (fun key => preserve (Key.later path.1 PUnit.unit key)) path.2.2

theorem PathCached.mono {c c' : (oracleSpec Input PUnit allRounds).QueryCache} (h : c ≤ c') :
    ∀ (rounds : List Round) (z : Input) (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge)
      (path : (protocol rounds).tree.ExecutionPath),
      PathCached c rounds z embed preserve path → PathCached c' rounds z embed preserve path
  | [], _, _, _, _, _ => trivial
  | _ :: rounds, z, embed, preserve, path, hp =>
      ⟨h hp.1, PathCached.mono h rounds z _ _ path.2.2 hp.2⟩

/-- **Every path returned by a verification run is cached in the cache the run leaves behind.** -/
theorem mapped_cached [DecidableEq Input] :
    ∀ (rounds : List Round) (guards : GuardSchedule Input PUnit rounds) (z : Input)
      (msgs : PublicMessages rounds)
      (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge)
      (cache : (oracleSpec Input PUnit allRounds).QueryCache),
      ∀ x ∈ support (randomOracleLoggedRun (simulateQ (restorationQueries Input PUnit allRounds)
        (mappedStoppedComplete rounds guards z msgs embed preserve)) cache),
        ∀ path, x.1.1 = some path → PathCached x.2 rounds z embed preserve path
  | [], _, _, _, _, _, cache => by
      intro x hx path hp
      simp only [mappedStoppedComplete, simulateQ_pure] at hx
      rw [ro_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      trivial
  | round :: rounds, (guard, next), z, (message, messages), embed, preserve, cache => by
      intro x hx path hp
      rw [mappedStoppedComplete] at hx
      by_cases hg : guard z message PUnit.unit = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false] at hx
        simp only [simulateQ_bind, simulateQ_liftM_query, simulateQ_pure] at hx
        change x ∈ support (randomOracleLoggedRun
          (liftM ((unifSpec + oracleSpec Input PUnit allRounds).query
              (.inr (embed (Key.here z message PUnit.unit)))) >>= fun u =>
            simulateQ (restorationQueries Input PUnit allRounds)
              (mappedStoppedComplete rounds
                (next message PUnit.unit (cast (preserve (Key.here z message PUnit.unit)) u)) z messages
                (fun key => embed (Key.later message PUnit.unit key))
                (fun key => preserve (Key.later message PUnit.unit key))) >>= fun x_1 =>
              pure (Option.map (fun tail => (⟨message, ⟨cast (preserve (Key.here z message PUnit.unit)) u, tail⟩⟩ :
                (protocol (round :: rounds)).tree.ExecutionPath)) x_1)) cache) at hx
        rw [randomOracleLoggedRun_bind, support_bind] at hx
        obtain ⟨p1, hx1⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hp1, hx2⟩ := Set.mem_iUnion.mp hx1
        rw [support_map] at hx2
        obtain ⟨q, hq, rfl⟩ := hx2
        have h1 := ro_hash_support _ cache p1 hp1
        rw [randomOracleLoggedRun_bind, support_bind] at hq
        obtain ⟨p2, hq1⟩ := Set.mem_iUnion.mp hq
        obtain ⟨hp2, hq2⟩ := Set.mem_iUnion.mp hq1
        rw [support_map] at hq2
        obtain ⟨q2, hq2, rfl⟩ := hq2
        rw [ro_pure, support_pure, Set.mem_singleton_iff] at hq2
        subst hq2
        have ih := mapped_cached rounds (next message PUnit.unit (cast (preserve (Key.here z message PUnit.unit)) p1.1.1))
          z messages (fun key => embed (Key.later message PUnit.unit key))
          (fun key => preserve (Key.later message PUnit.unit key)) p1.2 p2 hp2
        have hle := ro_le _ _ p2 hp2
        simp only at hp
        rcases hv : p2.1.1 with _ | tail
        · simp [hv] at hp
        · simp only [hv, Option.map_some] at hp
          have hpath := Option.some.inj hp
          subst hpath
          refine ⟨?_, ih tail hv⟩
          have e := hle h1.1
          simp only [cast_cast]
          rw [e]
          simp
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.not_false, ite_true, simulateQ_pure] at hx
        rw [ro_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx
        simp at hp

/-! ## 3. Agreement of two cached paths -/

/-- The first `n` rounds (messages AND challenges) of two paths agree. -/
def PEq : (rounds : List Round) → ℕ → (protocol rounds).tree.ExecutionPath →
    (protocol rounds).tree.ExecutionPath → Prop
  | [], _, _, _ => True
  | _ :: _, 0, _, _ => True
  | _ :: rs, n + 1, p, q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ PEq rs n p.2.2 q.2.2

/-- The message of round `n` agrees. -/
def MAt : (rounds : List Round) → ℕ → (protocol rounds).tree.ExecutionPath →
    (protocol rounds).tree.ExecutionPath → Prop
  | [], _, _, _ => True
  | _ :: _, 0, p, q => p.1 = q.1
  | _ :: rs, n + 1, p, q => MAt rs n p.2.2 q.2.2

/-- The challenge of round `n` agrees. -/
def CAt : (rounds : List Round) → ℕ → (protocol rounds).tree.ExecutionPath →
    (protocol rounds).tree.ExecutionPath → Prop
  | [], _, _, _ => True
  | _ :: _, 0, p, q => p.2.1 = q.2.1
  | _ :: rs, n + 1, p, q => CAt rs n p.2.2 q.2.2

theorem pEq_zero : ∀ (rounds : List Round) (p q : (protocol rounds).tree.ExecutionPath), PEq rounds 0 p q
  | [], _, _ => trivial
  | _ :: _, _, _ => trivial

theorem pEq_succ : ∀ (rounds : List Round) (n : ℕ) (p q : (protocol rounds).tree.ExecutionPath),
    PEq rounds (n + 1) p q ↔ PEq rounds n p q ∧ MAt rounds n p q ∧ CAt rounds n p q
  | [], _, _, _ => by simp [PEq, MAt, CAt]
  | _ :: rs, 0, p, q => by
      simp only [PEq, MAt, CAt]
      cases rs <;> simp [PEq]
  | _ :: rs, n + 1, p, q => by
      simp only [PEq, MAt, CAt]
      rw [pEq_succ rs n p.2.2 q.2.2]
      tauto

theorem pc_tail (c : (oracleSpec Input PUnit allRounds).QueryCache) {round : Round} {rs : List Round}
    (z : Input) (embed : Key Input PUnit (round :: rs) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) (m m' : round.Message) (h : m = m')
    (t : (protocol rs).tree.ExecutionPath)
    (H : PathCached c rs z (fun key => embed (Key.later m PUnit.unit key))
      (fun key => preserve (Key.later m PUnit.unit key)) t) :
    PathCached c rs z (fun key => embed (Key.later m' PUnit.unit key))
      (fun key => preserve (Key.later m' PUnit.unit key)) t := by
  subst h; exact H

theorem pc_head (c : (oracleSpec Input PUnit allRounds).QueryCache) {round : Round} {rs : List Round}
    (z : Input) (embed : Key Input PUnit (round :: rs) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) (m m' : round.Message) (h : m = m')
    (a a' : round.Challenge)
    (H : c (embed (Key.here z m PUnit.unit)) = some (cast (preserve (Key.here z m PUnit.unit)).symm a))
    (H' : c (embed (Key.here z m' PUnit.unit)) = some (cast (preserve (Key.here z m' PUnit.unit)).symm a')) :
    a = a' := by
  subst h
  have := H.symm.trans H'
  simp only [Option.some.injEq] at this
  exact (cast_inj _).mp this

theorem chal_at [DecidableEq Input] (c : (oracleSpec Input PUnit allRounds).QueryCache) :
    ∀ (rounds : List Round) (z : Input) (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge) (n : ℕ)
      (p q : (protocol rounds).tree.ExecutionPath),
      PathCached c rounds z embed preserve p → PathCached c rounds z embed preserve q →
      PEq rounds n p q → MAt rounds n p q → CAt rounds n p q
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: rs, z, embed, preserve, 0, p, q, hp, hq, _, hm =>
      pc_head c z embed preserve p.1 q.1 hm p.2.1 q.2.1 hp.1 hq.1
  | _ :: rs, z, embed, preserve, n + 1, p, q, hp, hq, he, hm => by
      simp only [PEq] at he
      obtain ⟨h1, h2, he⟩ := he
      exact chal_at c rs z _ _ n p.2.2 q.2.2 hp.2 (pc_tail c z embed preserve q.1 p.1 h1.symm _ hq.2) he hm

end Cached

/-! ## 4. The single-salt experiment and the two-acceptance experiment -/

section Exp

variable {rounds : List Round} {Statement GlobalSalt Witness : Type}
  [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- The path selected by `singleSaltExecution` is cached in the cache the run leaves behind. -/
theorem single_cached (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (cache : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) :
    ∀ y ∈ support (randomOracleLoggedRun (singleSaltExecution rounds guards adversary) cache),
      ∀ z p w, y.1.1.1 = some (z, p, w) → PathCached y.2 rounds z id (fun _ => rfl) p := by
  intro y hy z p w hyp
  unfold singleSaltExecution at hy
  rw [randomOracleLoggedRun_bind, support_bind] at hy
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
  obtain ⟨_, ha2⟩ := Set.mem_iUnion.mp ha
  rw [support_map] at ha2
  obtain ⟨q, hq, rfl⟩ := ha2
  obtain ⟨⟨⟨sel, log⟩, log2⟩, c2⟩ := a
  simp only at hq
  rcases sel with _ | ⟨statement, ⟨salt, msgs⟩, wit⟩
  · simp only [ro_pure, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    simp at hyp
  · simp only at hq
    rw [randomOracleLoggedRun_bind, support_bind] at hq
    obtain ⟨p1, hq1⟩ := Set.mem_iUnion.mp hq
    obtain ⟨hp1, hq2⟩ := Set.mem_iUnion.mp hq1
    rw [support_map] at hq2
    obtain ⟨q2, hq2, rfl⟩ := hq2
    rw [ro_pure, support_pure, Set.mem_singleton_iff] at hq2
    subst hq2
    rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped] at hp1
    simp only at hyp
    rcases hv : p1.1.1 with _ | p0
    · simp [hv] at hyp
    · simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hyp
      obtain ⟨rfl, rfl, rfl⟩ := hyp
      exact mapped_cached rounds guards _ msgs id (fun _ => rfl) c2 p1 hp1 p0 hv

end Exp

section TwoExp

open NockvmE2E.Rap NockvmE2E.Succ

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
  {Statement GlobalSalt : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- **RO consistency of the two paths** of `twoAcceptExecution`: both accepted-run paths are cached in ONE cache
(the final cache of the joint run). -/
theorem two_cached
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) :
    ∀ x ∈ support (randomOracleLoggedRun (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅),
      ∀ z p z' p', x.1.1 = some ((z, p), (z', p')) →
        PathCached x.2 (sRounds R CS plan I0 I Ifin nb) z id (fun _ => rfl) p ∧
        PathCached x.2 (sRounds R CS plan I0 I Ifin nb) z' id (fun _ => rfl) p' := by
  intro x hx z p z' p' hxp
  rw [two_eq_bind, randomOracleLoggedRun_bind, support_bind] at hx
  obtain ⟨y, hx1⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hy, hx2⟩ := Set.mem_iUnion.mp hx1
  rw [support_map] at hx2
  obtain ⟨q, hq, rfl⟩ := hx2
  obtain ⟨⟨⟨sel, log⟩, log2⟩, c2⟩ := y
  simp only [stage2] at hq
  rcases sel with _ | ⟨z0, p0, salt', msgs'⟩
  · simp only [ro_pure, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    simp at hxp
  · simp only at hq
    rw [randomOracleLoggedRun_bind, support_bind] at hq
    obtain ⟨p1, hq1⟩ := Set.mem_iUnion.mp hq
    obtain ⟨hp1, hq2⟩ := Set.mem_iUnion.mp hq1
    rw [support_map] at hq2
    obtain ⟨q2, hq2, rfl⟩ := hq2
    rw [ro_pure, support_pure, Set.mem_singleton_iff] at hq2
    subst hq2
    have hsingle := single_cached guards adversary ∅ _ hy z0 p0 (salt', msgs') rfl
    rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped] at hp1
    simp only at hxp
    rcases hv : p1.1.1 with _ | p0'
    · simp [hv] at hxp
    · simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hxp
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hxp
      exact ⟨PathCached.mono (ro_le _ _ p1 hp1) _ _ _ _ _ hsingle,
        mapped_cached _ guards _ msgs' id (fun _ => rfl) c2 p1 hp1 p0' hv⟩

end TwoExp

end NockvmE2E.Ung
