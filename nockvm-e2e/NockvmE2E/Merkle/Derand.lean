/-
Merkle (B) file 6: S0-S3 derandomisation.
Generic over a hash domain `Q` (range `Y`), FS keys `K` (ranges `Rc k`), round index `J` (ranges `C j`).
-/
import NockvmE2E.Merkle.Compiled
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.SimSemantics.StateT.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.RandomOracle.Eager

open OracleComp OracleSpec

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Derand

section Setup

variable (Q Y : Type) {K J : Type} (Rc : K → Type) (C : J → Type)

/-- answer family of the single lazy RO on `Q ⊕ K` -/
abbrev Rfam : Q ⊕ K → Type := Sum.elim (fun _ => Y) Rc
abbrev realSpec := unifSpec + ofFn (Rfam Q Y Rc)
abbrev hashSpec := (Q →ₒ Y)
abbrev roundSpec : OracleSpec J := ofFn C
abbrev coinSpec := unifSpec + roundSpec C
abbrev progSpec := coinSpec C + hashSpec Q Y

variable [∀ j, SampleableType (C j)] [SampleableType Y]

/-- the uniform sampler of every query of the program spec -/
def sampler : QueryImpl (progSpec Q Y C) ProbComp := fun t =>
  match t with
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr j) => $ᵗ (C j)
  | .inr q => $ᵗ Y

variable [∀ j, Finite (C j)] [∀ j, Nonempty (C j)] [Finite Y] [Nonempty Y]

noncomputable instance : UniformAnswerMeasure (roundSpec C) :=
  UniformAnswerMeasure.ofFiniteNonempty _
noncomputable instance : UniformAnswerMeasure (hashSpec Q Y) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- sampling every query uniformly is the uniform measure semantics -/
theorem evalDist_sampler {α : Type} [MeasurableSpace α] (X : OracleComp (progSpec Q Y C) α) :
    𝒟[simulateQ (sampler Q Y C) X] = 𝒟[X] := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    let : MeasurableSpace ((progSpec Q Y C).Range t) := ⊤
    have : DiscreteMeasurableSpace ((progSpec Q Y C).Range t) := ⟨fun _ => trivial⟩
    refine evalDist_bind_eq_query_bind_of_uniform t _ ?_ _ _ ih
    rcases t with (n | j) | q
    · exact evalDist_liftM_query_uniform n
    · exact SampleableType.evalDist_uniformSample
    · exact SampleableType.evalDist_uniformSample

end Setup

section Fold

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]

/-- S1 fold: FS cache in the program state, fresh keys answered by the round oracle (via `e`),
hash queries and coins forwarded raw. -/
def foldImpl (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) :
    QueryImpl (realSpec Q Y Rc)
      (StateT (ofFn Rc).QueryCache (OracleComp (progSpec Q Y C))) :=
  fun t => match t with
  | .inl n => StateT.lift (liftM ((progSpec Q Y C).query (.inl (.inl n))))
  | .inr (.inl q) => StateT.lift (liftM ((progSpec Q Y C).query (.inr q)))
  | .inr (.inr k) => do
      match (← get) k with
      | some v => pure v
      | none =>
        let c : C (rd k) ← StateT.lift (liftM ((progSpec Q Y C).query (.inl (.inr (rd k)))))
        modifyGet fun cache => (e k c, cache.cacheQuery k (e k c))

/-- hash-only caching layer over the program spec; coins and rounds are never cached. -/
def hcImpl :
    QueryImpl (progSpec Q Y C)
      (StateT (hashSpec Q Y).QueryCache (OracleComp (progSpec Q Y C))) :=
  fun t => match t with
  | .inl c => StateT.lift (liftM ((progSpec Q Y C).query (.inl c)))
  | .inr q => do
      match (← get) q with
      | some v => pure v
      | none =>
        let v : Y ← StateT.lift (liftM ((progSpec Q Y C).query (.inr q)))
        modifyGet fun cache => (v, cache.cacheQuery q v)

/-- split/join of the single RO cache on `Q ⊕ K` into hash and FS caches. -/
def joinCache (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    (ofFn (Rfam Q Y Rc)).QueryCache :=
  QueryCache.ofFn fun d => match d with | .inl q => hc q | .inr k => fc k

def splitCache (c : (ofFn (Rfam Q Y Rc)).QueryCache) :
    (hashSpec Q Y).QueryCache × (ofFn Rc).QueryCache :=
  (QueryCache.ofFn fun q => c (.inl q), QueryCache.ofFn fun k => c (.inr k))


theorem joinCache_splitCache (c : (ofFn (Rfam Q Y Rc)).QueryCache) :
    joinCache (splitCache c).1 (splitCache c).2 = c := by
  refine QueryCache.ext fun d => ?_
  cases d <;> rfl

theorem splitCache_joinCache (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    splitCache (joinCache hc fc) = (hc, fc) := by
  refine Prod.ext (QueryCache.ext fun q => rfl) (QueryCache.ext fun k => rfl)

theorem joinCache_cacheQuery_hash (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache)
    (q : Q) (v : Y) :
    joinCache (hc.cacheQuery q v) fc =
      (joinCache hc fc).cacheQuery (Sum.inl q : Q ⊕ K) (v : Rfam Q Y Rc (.inl q)) := by
  refine QueryCache.ext fun d => ?_
  rcases d with q' | k
  · by_cases h : q' = q
    · subst h
      exact (QueryCache.cacheQuery_self hc q' v).trans
        (QueryCache.cacheQuery_self (joinCache hc fc) (Sum.inl q') v).symm
    · exact (QueryCache.cacheQuery_of_ne hc v h).trans
        (QueryCache.cacheQuery_of_ne (joinCache hc fc) (t := Sum.inl q) (t' := Sum.inl q') v
          (by simpa using h)).symm
  · exact (QueryCache.cacheQuery_of_ne (joinCache hc fc) (t := Sum.inl q) (t' := Sum.inr k) v
      (by simp)).symm

theorem joinCache_cacheQuery_fs (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache)
    (k : K) (v : Rc k) :
    joinCache hc (fc.cacheQuery k v) =
      (joinCache hc fc).cacheQuery (Sum.inr k : Q ⊕ K) (v : Rfam Q Y Rc (.inr k)) := by
  refine QueryCache.ext fun d => ?_
  rcases d with q | k'
  · exact (QueryCache.cacheQuery_of_ne (joinCache hc fc) (t := Sum.inr k) (t' := Sum.inl q) v
      (by simp)).symm
  · by_cases h : k' = k
    · subst h
      exact (QueryCache.cacheQuery_self fc k' v).trans
        (QueryCache.cacheQuery_self (joinCache hc fc) (Sum.inr k') v).symm
    · exact (QueryCache.cacheQuery_of_ne fc v h).trans
        (QueryCache.cacheQuery_of_ne (joinCache hc fc) (t := Sum.inr k) (t' := Sum.inr k') v
          (by simpa using h)).symm

section Step

variable [∀ j, SampleableType (C j)] [∀ k, SampleableType (Rc k)] [SampleableType Y]
  [∀ j, Finite (C j)] [∀ j, Nonempty (C j)] [Finite Y] [Nonempty Y]

instance instSampRfam : ∀ d, SampleableType (Rfam Q Y Rc d) := fun d => match d with
  | .inl _ => inferInstanceAs (SampleableType Y)
  | .inr k => inferInstanceAs (SampleableType (Rc k))

@[simp] theorem joinCache_inl (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache)
    (q : Q) : (joinCache hc fc).toFn (.inl q) = hc.toFn q := rfl

@[simp] theorem joinCache_inr (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache)
    (k : K) : (joinCache hc fc).toFn (.inr k) = fc.toFn k := rfl

theorem step_hash (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) (q : Q)
    (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    ((ofFn (Rfam Q Y Rc)).romImpl (.inr (.inl q))).run (joinCache hc fc) =ᵈ
      (fun p => (p.1.1, joinCache p.2 p.1.2)) <$>
        simulateQ (sampler Q Y C)
          ((simulateQ hcImpl ((foldImpl rd e (.inr (.inl q))).run fc)).run hc) := by
  rcases hq : hc.toFn q with _ | v
  · simp [foldImpl, hcImpl, hq, sampler, joinCache_cacheQuery_hash]
    exact EvalDistEq.rfl
  · simp [foldImpl, hcImpl, hq]


theorem step_coin (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) (n : ℕ)
    (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    ((ofFn (Rfam Q Y Rc)).romImpl (.inl n)).run (joinCache hc fc) =ᵈ
      (fun p => (p.1.1, joinCache p.2 p.1.2)) <$>
        simulateQ (sampler Q Y C)
          ((simulateQ hcImpl ((foldImpl rd e (.inl n)).run fc)).run hc) := by
  simp [foldImpl, hcImpl, sampler]
  exact EvalDistEq.rfl

theorem step_fs (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) (k : K)
    (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    ((ofFn (Rfam Q Y Rc)).romImpl (.inr (.inr k))).run (joinCache hc fc) =ᵈ
      (fun p => (p.1.1, joinCache p.2 p.1.2)) <$>
        simulateQ (sampler Q Y C)
          ((simulateQ hcImpl ((foldImpl rd e (.inr (.inr k))).run fc)).run hc) := by
  rcases hq : fc.toFn k with _ | v
  · simp [foldImpl, hcImpl, hq, sampler, joinCache_cacheQuery_fs]
    have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective (α := C (rd k)) (β := Rc k)
      (e k).bijective).map
      (fun a => (a, (joinCache hc fc).cacheQuery (Sum.inr k) a))
    simp only [Functor.map_map, Function.comp_def] at h
    exact h.symm
  · simp [foldImpl, hcImpl, hq]


theorem step_all (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) (t : (realSpec Q Y Rc).Domain)
    (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache) :
    ((ofFn (Rfam Q Y Rc)).romImpl t).run (joinCache hc fc) =ᵈ
      (fun p => (p.1.1, joinCache p.2 p.1.2)) <$>
        simulateQ (sampler Q Y C)
          ((simulateQ hcImpl ((foldImpl rd e t).run fc)).run hc) := by
  rcases t with n | q | k
  · exact step_coin rd e n hc fc
  · exact step_hash rd e q hc fc
  · exact step_fs rd e k hc fc

/-- S1: the lazy real world equals, in distribution, the fold program (FS cache in program
state, raw hash and round queries) under hash-only caching and uniform sampling. -/
theorem s1_real_eq (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) :
    ∀ (hc : (hashSpec Q Y).QueryCache) (fc : (ofFn Rc).QueryCache),
    (simulateQ (ofFn (Rfam Q Y Rc)).romImpl oa).run (joinCache hc fc) =ᵈ
      (fun p => (p.1.1, joinCache p.2 p.1.2)) <$>
        simulateQ (sampler Q Y C)
          ((simulateQ hcImpl ((simulateQ (foldImpl rd e) oa).run fc)).run hc) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro hc fc; simp
  | query_bind t k ih =>
    intro hc fc
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind, bind_map_left]
    refine ((step_all rd e t hc fc).bind_left _).trans ?_
    simp only [bind_map_left]
    exact EvalDistEq.bind_right _ fun x => ih x.1.1 x.2 x.1.2

end Step

end Fold

section Seeded

variable {Q Y : Type} {J : Type} {C : J → Type}
variable [DecidableEq Q] [DecidableEq J]
  [∀ j, SampleableType (C j)] [SampleableType Y]
  [∀ j, Finite (C j)] [∀ j, Nonempty (C j)] [Finite Y] [Nonempty Y]

instance instSampProg : ∀ t : (progSpec Q Y C).Domain, SampleableType ((progSpec Q Y C).Range t) :=
  fun t => match t with
  | .inl (.inl _) => inferInstanceAs (SampleableType (Fin _))
  | .inl (.inr j) => inferInstanceAs (SampleableType (C j))
  | .inr _ => inferInstanceAs (SampleableType Y)

/-- a default answer for every coin query -/
noncomputable def dflt (t : (coinSpec C).Domain) : (coinSpec C).Range t :=
  match t with
  | .inl n => (0 : Fin (n + 1))
  | .inr j => Classical.choice inferInstance

/-- S3 handler: coins are answered from the seed (default when exhausted), hash queries stay raw. -/
noncomputable def sodImpl :
    QueryImpl (progSpec Q Y C) (StateT (QuerySeed (progSpec Q Y C)) (OracleComp (hashSpec Q Y))) :=
  fun t => match t with
  | .inl c => StateT.mk fun seed =>
      match seed (.inl c) with
      | u :: us => pure (u, seed.update (.inl c) us)
      | [] => pure (dflt c, seed)
  | .inr q => StateT.lift (liftM ((hashSpec Q Y).query q))

theorem seeded_eq {β : Type} (P : OracleComp (progSpec Q Y C) β) :
    ∀ (qb : (progSpec Q Y C).Domain → ℕ), IsPerIndexQueryBound P qb →
    ∀ (σ : QuerySeed (progSpec Q Y C)),
    (∀ c : (coinSpec C).Domain, qb (.inl c) ≤ (σ (.inl c)).length) →
    (∀ q : Q, σ (.inr q) = []) →
    ∀ hc : (hashSpec Q Y).QueryCache,
    (simulateQ (eagerRandomOracle (spec := progSpec Q Y C))
        ((simulateQ hcImpl P).run hc)).run σ =
      (fun p => ((p.1.1, p.2), p.1.2)) <$>
        (simulateQ (hashSpec Q Y).randomOracle ((simulateQ sodImpl P).run σ)).run hc := by
  induction P using OracleComp.inductionOn with
  | pure a => intro qb _ σ _ _ hc; simp
  | query_bind t k ih =>
    intro qb hqb σ hcov hhash hc
    rw [isPerIndexQueryBound_query_bind_iff] at hqb
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with c | q
    · have hpos := hqb.1
      obtain ⟨u, us, hσ⟩ : ∃ u us, σ (.inl c) = u :: us := by
        rcases h : σ (.inl c) with _ | ⟨u, us⟩
        · have := hcov c
          rw [h] at this
          simp at this
          have := hqb.1
          omega
        · exact ⟨u, us, rfl⟩
      have hcov' : ∀ c' : (coinSpec C).Domain,
          Function.update qb (.inl c) (qb (.inl c) - 1) (.inl c') ≤
            ((σ.update (.inl c) us) (.inl c')).length := by
        intro c'
        by_cases h : c' = c
        · subst h; simp [QuerySeed.update_self]
          have := hcov c'; rw [hσ] at this; simp at this; omega
        · have hne : (Sum.inl c' : (progSpec Q Y C).Domain) ≠ .inl c := by simpa using h
          rw [Function.update_of_ne hne, QuerySeed.update_of_ne _ _ _ _ hne]
          exact hcov c'
      have hhash' : ∀ q : Q, (σ.update (.inl c) us) (.inr q) = [] := by
        intro q
        rw [QuerySeed.update_of_ne _ _ _ _ (by simp)]
        exact hhash q
      simp only [hcImpl, sodImpl]
      simp [hσ, eagerRandomOracle.run_cons hσ]
      exact ih u _ (hqb.2 u) _ hcov' hhash' hc
    · have hq0 := hhash q
      have hcov' : ∀ c' : (coinSpec C).Domain,
          Function.update qb (.inr q) (qb (.inr q) - 1) (.inl c') ≤ (σ (.inl c')).length := by
        intro c'
        rw [Function.update_of_ne (by simp)]
        exact hcov c'
      rcases hh : hc.toFn q with _ | v
      · simp only [hcImpl, sodImpl]
        simp [hh, eagerRandomOracle.run_nil hq0]
        exact bind_congr fun a => ih a _ (hqb.2 a) σ hcov' hhash _
      · simp only [hcImpl, sodImpl]
        simp [hh]
        exact ih v _ (hqb.2 v) σ hcov' hhash hc

end Seeded

section Cover

/-- (S3 coverage) finite ranges ⇒ some finitely-supported per-index query bound exists
(König on a finite-branching free monad; per-index refinement of `Probe.exists_isTotalQueryBound`). -/
theorem exists_perIndexBound {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t, Finite (spec.Range t)] {α : Type} (oa : OracleComp spec α) :
    ∃ (S : Finset ι) (qb : ι → ℕ), IsPerIndexQueryBound oa qb ∧ ∀ i ∉ S, qb i = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨∅, 0, trivial, by simp⟩
  | query_bind t k ih =>
    classical
    choose S qb hqb hS using ih
    letI : Fintype (spec.Range t) := Fintype.ofFinite _
    refine ⟨insert t ((Finset.univ : Finset (spec.Range t)).biUnion S),
      fun i => ((Finset.univ : Finset (spec.Range t)).sup fun u => qb u i) + (if i = t then 1 else 0), ?_, ?_⟩
    · rw [isPerIndexQueryBound_query_bind_iff]
      refine ⟨by rw [if_pos rfl]; exact Nat.succ_pos _, fun u => (hqb u).mono ?_⟩
      intro i
      have hle : qb u i ≤ (Finset.univ : Finset (spec.Range t)).sup fun u => qb u i :=
        Finset.le_sup (f := fun u => qb u i) (Finset.mem_univ u)
      by_cases h : i = t
      · subst h; simpa using hle
      · simpa [Function.update_of_ne h, h] using hle
    · intro i hi
      have hit : i ≠ t := fun h => hi (by rw [h]; exact Finset.mem_insert_self _ _)
      have h0 : ∀ u, qb u i = 0 := fun u => hS u i fun hm =>
        hi (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, hm⟩))
      show (Finset.univ : Finset (spec.Range t)).sup (fun u => qb u i) + (if i = t then 1 else 0) = 0
      rw [if_neg hit, Nat.add_zero]
      exact Nat.eq_zero_of_le_zero (Finset.sup_le fun u _ => (h0 u).le)

end Cover

section Assembly

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]
  [∀ j, SampleableType (C j)] [∀ k, SampleableType (Rc k)] [SampleableType Y]
  [∀ j, Finite (C j)] [∀ j, Nonempty (C j)] [Finite Y] [Nonempty Y]

theorem joinCache_empty :
    joinCache (∅ : (hashSpec Q Y).QueryCache) (∅ : (ofFn Rc).QueryCache) = ∅ :=
  QueryCache.ext fun d => by cases d <;> rfl

/-- S1 program: the real-world program `oa` with the FS cache moved into the program state;
fresh FS keys become round-oracle queries, hash queries stay raw. -/
def foldProg (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) :
    OracleComp (progSpec Q Y C) (α × (ofFn Rc).QueryCache) :=
  (simulateQ (foldImpl rd e) oa).run ∅

/-- S3 program: `foldProg` with coins and rounds answered from the seed `σ`; only hash queries
remain. -/
noncomputable def seededProg (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) :
    OracleComp (hashSpec Q Y) (α × (ofFn Rc).QueryCache) :=
  (simulateQ sodImpl (foldProg rd e oa)).run' σ

/-- the observable of the real world kept by the derandomisation: output and final FS cache -/
def realObs {α : Type} (z : (α × QueryLog (ofFn (Rfam Q Y Rc))) × (ofFn (Rfam Q Y Rc)).QueryCache) :
    α × (ofFn Rc).QueryCache := (z.1.1, (splitCache z.2).2)

/-- S0+S1: the QD logged real world, projected to output and FS cache, is the fold program under
hash-only caching and uniform answers. -/
theorem realObs_evalDistEq (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) :
    realObs <$> randomOracleLoggedRun oa ∅ =ᵈ
      simulateQ (sampler Q Y C) ((simulateQ hcImpl (foldProg rd e oa)).run' ∅) := by
  have h1 := randomOracleLoggedRun_project oa ∅
  have h2 := s1_real_eq (C := C) rd e oa ∅ ∅
  rw [joinCache_empty] at h2
  have h3 := h2.map (fun p => (p.1, (splitCache p.2).2))
  have h4 : realObs <$> randomOracleLoggedRun oa ∅ =
      (fun p => (p.1, (splitCache p.2).2)) <$> (simulateQ (ofFn (Rfam Q Y Rc)).romImpl oa).run ∅ := by
    rw [← h1, Functor.map_map]; rfl
  rw [h4]
  refine h3.trans ?_
  simp only [Functor.map_map, splitCache_joinCache, foldProg, StateT.run'_eq, simulateQ_map]
  exact EvalDistEq.rfl

instance instFiniteProg : ∀ t : (progSpec Q Y C).Domain, Finite ((progSpec Q Y C).Range t) :=
  fun t => match t with
  | .inl (.inl n) => inferInstanceAs (Finite (Fin (n + 1)))
  | .inl (.inr j) => inferInstanceAs (Finite (C j))
  | .inr _ => inferInstanceAs (Finite Y)

/-- pointwise S3: on a covering, hash-clean seed the eager run of the hash-cached fold program is
the lazy-RO run of the hash-only seeded program. -/
theorem eager_run'_eq (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) (qb : (progSpec Q Y C).Domain → ℕ)
    (hqb : IsPerIndexQueryBound (foldProg rd e oa) qb) (σ : QuerySeed (progSpec Q Y C))
    (hcov : ∀ c : (coinSpec C).Domain, qb (.inl c) ≤ (σ (.inl c)).length)
    (hhash : ∀ q : Q, σ (.inr q) = []) :
    (simulateQ (eagerRandomOracle (spec := progSpec Q Y C))
        ((simulateQ hcImpl (foldProg rd e oa)).run' ∅)).run' σ =
      (simulateQ (hashSpec Q Y).randomOracle (seededProg rd e oa σ)).run' ∅ := by
  have h := seeded_eq (foldProg rd e oa) qb hqb σ hcov hhash ∅
  simp only [seededProg, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [← Functor.map_map, ← Functor.map_map, h]
  simp [Functor.map_map]

/-- **S0-S3 derandomisation.** The QD real world (one lazy RO on `Q ⊕ K`, logged), projected to its
output and final FS cache, is distributed as: sample a seed for the coin and round oracles, run the
hash-only program `seededProg` under the lazy hash RO. No coin bound on `oa` is assumed; the
covering `qc, js` are produced by König (`exists_perIndexBound`). -/
theorem derand (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) :
    ∃ (qc : (progSpec Q Y C).Domain → ℕ) (js : List (progSpec Q Y C).Domain),
      letI : MeasurableSpace (α × (ofFn Rc).QueryCache) := ⊤
      𝒟[realObs <$> randomOracleLoggedRun oa ∅] =
        𝒟[do
          let σ ← generateSeed (progSpec Q Y C) qc js
          (simulateQ (hashSpec Q Y).randomOracle (seededProg rd e oa σ)).run' ∅] := by
  obtain ⟨S, qb, hqb, hS⟩ := exists_perIndexBound (foldProg rd e oa)
  let qc : (progSpec Q Y C).Domain → ℕ := fun t => match t with
    | .inl c => qb (.inl c)
    | .inr _ => 0
  refine ⟨qc, S.toList, ?_⟩
  letI : MeasurableSpace (α × (ofFn Rc).QueryCache) := ⊤
  have hcover : ∀ j, 0 < qc j → j ∈ S.toList := by
    intro j hj
    rcases j with c | q
    · rw [Finset.mem_toList]
      by_contra hn
      have := hS _ hn
      simp only [qc] at hj
      omega
    · simp [qc] at hj
  calc 𝒟[realObs <$> randomOracleLoggedRun oa ∅]
      = 𝒟[simulateQ (sampler Q Y C) ((simulateQ hcImpl (foldProg rd e oa)).run' ∅)] :=
        (realObs_evalDistEq rd e oa).evalDist_eq
    _ = 𝒟[(simulateQ hcImpl (foldProg rd e oa)).run' ∅] := evalDist_sampler Q Y C _
    _ = 𝒟[do
          let σ ← generateSeed (progSpec Q Y C) qc S.toList
          (simulateQ (eagerRandomOracle (spec := progSpec Q Y C))
            ((simulateQ hcImpl (foldProg rd e oa)).run' ∅)).run' σ] :=
        (eagerRandomOracle_evalDist_generateSeed_bind _ qc S.toList).symm
    _ = _ := by
        refine evalDist_bind_congr_of_support _ _ _ fun σ hσ => ?_
        rw [eager_run'_eq rd e oa qb hqb σ ?_ ?_]
        · intro c
          exact le_length_of_mem_support_generateSeed_of_covers _ qc _ σ (.inl c) hσ hcover
        · intro q
          exact eq_nil_of_mem_support_generateSeed _ qc _ σ (.inr q) hσ (by simp [qc])

end Assembly

section Overlay

variable {Q Y : Type} [DecidableEq Q] [SampleableType Y] [Finite Y] [Nonempty Y]

/-- the lazy hash RO (`ProbComp`) and VCVio's `cachingOracle` (`OracleComp (Q →ₒ Y)`, uniform
answer measure) have the same joint output/cache measure. -/
theorem evalDist_randomOracle_run_eq_cachingOracle_run {β : Type}
    (Z : OracleComp (hashSpec Q Y) β) :
    letI : MeasurableSpace (β × (hashSpec Q Y).QueryCache) := ⊤
    ∀ c : (hashSpec Q Y).QueryCache,
      𝒟[(simulateQ (hashSpec Q Y).randomOracle Z).run c] =
        𝒟[(simulateQ (hashSpec Q Y).cachingOracle Z).run c] := by
  letI : MeasurableSpace (β × (hashSpec Q Y).QueryCache) := ⊤
  induction Z using OracleComp.inductionOn with
  | pure a => intro c; simp
  | query_bind t k ih =>
    intro c
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind]
    rcases hc : c.toFn t with _ | v
    · rw [randomOracle.run_eq, cachingOracle.run_none (by simpa using hc)]
      simp only [hc, bind_assoc, pure_bind, map_eq_bind_pure_comp]
      let : MeasurableSpace ((hashSpec Q Y).Range t) := ⊤
      have : DiscreteMeasurableSpace ((hashSpec Q Y).Range t) := ⟨fun _ => trivial⟩
      exact evalDist_bind_eq_query_bind_of_uniform t _ SampleableType.evalDist_uniformSample _ _
        (fun u => by simpa using ih u (c.cacheQuery t u))
    · rw [randomOracle.run_eq, cachingOracle.run_some (by simpa using hc)]
      simp only [hc, pure_bind]
      exact ih v c

/-- Output-only form: the lazy-RO run of a hash-only program has VCVio's `withCacheOverlay ∅`
measure, which is the shape of `MultiExtractability.extractabilityExperiment`. -/
theorem evalDist_randomOracle_run'_eq_withCacheOverlay {β : Type} [MeasurableSpace β]
    (Z : OracleComp (hashSpec Q Y) β) :
    𝒟[(simulateQ (hashSpec Q Y).randomOracle Z).run' ∅] =
      𝒟[(hashSpec Q Y).withCacheOverlay ∅ Z] := by
  letI : MeasurableSpace (β × (hashSpec Q Y).QueryCache) := ⊤
  have hfst : Measurable (Prod.fst : β × (hashSpec Q Y).QueryCache → β) := measurable_from_top
  rw [OracleSpec.withCacheOverlay, StateT.run'_eq, StateT.run'_eq, evalDist_map _ hfst,
    evalDist_map _ hfst, evalDist_randomOracle_run_eq_cachingOracle_run Z ∅]

end Overlay

section Observer

/-- **S0.** An observer handler (extra deterministic state, queries forwarded unchanged) can be
dropped: the instrumented program `(simulateQ obs oa).run' s` *is* `oa`. Instrumentation (hash log,
FS fresh-key events, memo) is therefore free to be added before `derand` and projected away. -/
theorem observer_run' {ι : Type} {spec : OracleSpec ι} {S α : Type}
    (obs : QueryImpl spec (StateT S (OracleComp spec)))
    (h : ∀ t s, Prod.fst <$> (obs t).run s = (liftM (spec.query t) : OracleComp spec _))
    (oa : OracleComp spec α) : ∀ s, (simulateQ obs oa).run' s = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp
  | query_bind t k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    have hk : ∀ p : spec.Range t × S, Prod.fst <$> (simulateQ obs (k p.1)).run p.2 = k p.1 := by
      intro p; simpa [StateT.run'_eq] using ih p.1 p.2
    simp_rw [hk]
    rw [← h t s]
    simp [map_eq_bind_pure_comp, bind_assoc]

end Observer

section Final

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]
  [∀ j, SampleableType (C j)] [∀ k, SampleableType (Rc k)] [SampleableType Y]
  [∀ j, Finite (C j)] [∀ j, Nonempty (C j)] [Finite Y] [Nonempty Y]

/-- **Derandomised bound transfer (the form Phases/Soundness consume).** If for every seed the
hash-only program `seededProg … σ`, run under VCVio's `withCacheOverlay ∅` (the shape of
`MultiExtractability.extractabilityExperiment`), makes `p` happen with probability at most `ε`,
then the QD logged real world does too. -/
theorem derand_prEvent_le (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k) {α : Type}
    (oa : OracleComp (realSpec Q Y Rc) α) (p : α × (ofFn Rc).QueryCache → Prop) {ε : ENNReal}
    (h : ∀ σ : QuerySeed (progSpec Q Y C),
      Pr{let z ← (hashSpec Q Y).withCacheOverlay ∅ (seededProg rd e oa σ)}[p z] ≤ ε) :
    Pr{let z ← realObs <$> randomOracleLoggedRun oa ∅}[p z] ≤ ε := by
  obtain ⟨qc, js, hd⟩ := derand rd e oa
  letI : MeasurableSpace (α × (ofFn Rc).QueryCache) := ⊤
  have : DiscreteMeasurableSpace (α × (ofFn Rc).QueryCache) := ⟨fun _ => trivial⟩
  rw [prEvent_eq_evalDist_of_discrete, hd, ← prEvent_eq_evalDist_of_discrete]
  refine prEvent_bind_le_of_forall_le _ _ _ fun σ => ?_
  rw [prEvent_eq_evalDist_of_discrete, evalDist_randomOracle_run'_eq_withCacheOverlay,
    ← prEvent_eq_evalDist_of_discrete]
  exact h σ

end Final

end NockvmE2E.Merkle.Derand
