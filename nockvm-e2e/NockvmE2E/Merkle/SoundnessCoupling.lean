/-
Merkle (B) file 10b: the reduction B₂ (`reductionB₂`: `verifiedFS A` under `Rename.bImpl`,
renaming at the memo after each key's own entries), its cache invariant (`InvB`, `runB`, `segB`),
evaluation against a cache (`cacheEval`), QD's paired verification replaying the compiled one
(`qd_accepts`), and the probability chain (`pr_instrA_eq_B`, `pr_B_le_qd`, `reductionB₂_queryBound`).
-/
import NockvmE2E.Merkle.SoundnessWorld

open OracleComp OracleSpec MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.SoundnessCoupling

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good
  NockvmE2E.Merkle.SoundnessWorld

/-! ## Evaluation of an oracle program against a cache -/

section CacheEval

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- the result of `oa` when every query it makes is answered by the cache `c` (`none` on a miss) -/
def cacheEval (c : spec.QueryCache) {α : Type} : OracleComp spec α → Option α
  | .pure a => some a
  | .queryBind t k => match c t with
    | some v => cacheEval c (k v)
    | none => none
theorem cacheEval_query_bind (c : spec.QueryCache) {α : Type} (t : ι)
    (k : spec.Range t → OracleComp spec α) :
    cacheEval c (liftM (spec.query t) >>= k) = match c t with
      | some v => cacheEval c (k v)
      | none => none := by
  rw [show (liftM (spec.query t) >>= k : OracleComp spec α) = OracleComp.queryBind t k from rfl,
    cacheEval]
  rfl
theorem cacheEval_bind (c : spec.QueryCache) {α β : Type} (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    cacheEval c (oa >>= f) = (cacheEval c oa).bind fun x => cacheEval c (f x) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [bind_assoc, cacheEval_query_bind, cacheEval_query_bind]
    rcases c t with _ | v
    · rfl
    · exact ih v
theorem cacheEval_mem_support (c : spec.QueryCache) {α : Type} (oa : OracleComp spec α) (x : α)
    (h : cacheEval c oa = some x) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => cases h; simp
  | query_bind t k ih =>
    rw [cacheEval_query_bind] at h
    rcases hc : c t with _ | v
    · rw [hc] at h; cases h
    · rw [hc] at h
      exact (mem_support_bind_iff _ _ _).mpr ⟨v, mem_support_query t v, ih v h⟩

end CacheEval

/-! ## A lazy random oracle step keeps the cache and caches the answer -/

theorem ro_step {D : Type} {R : D → Type} [DecidableEq D] [∀ d, SampleableType (R d)]
    (t : D) (c : (ofFn R).QueryCache) (p : R t × (ofFn R).QueryCache)
    (hp : p ∈ support (((ofFn R).randomOracle t).run c)) : p.2 t = some p.1 ∧ c ≤ p.2 := by
  rw [randomOracle.run_eq] at hp
  rcases h : c.toFn t with _ | u
  · rw [h] at hp
    simp at hp
    obtain ⟨a, rfl⟩ := hp
    refine ⟨QueryCache.cacheQuery_self _ _ _, QueryCache.le_def.mpr fun t' u' h' => ?_⟩
    have hne : t' ≠ t := fun e => by subst e; rw [h] at h'; cases h'
    exact (QueryCache.cacheQuery_of_ne _ _ hne).trans h'
  · rw [h] at hp
    simp at hp
    subst hp
    exact ⟨h, le_rfl⟩
theorem query_map_logged' {D : Type} {R : D → Type} [DecidableEq D] [∀ d, SampleableType (R d)]
    {α : Type} (t : D) (f : R t → α) (c : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache) (hz : z ∈ support (randomOracleLoggedRun
      (f <$> (liftM ((unifSpec + ofFn R).query (.inr t)) : OracleComp (unifSpec + ofFn R) (R t))) c)) :
    ∃ p ∈ support (((ofFn R).randomOracle t).run c), z = ((f p.1, [⟨t, p.1⟩]), p.2) := by
  rw [FreshKeys.loggedRun_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [randomOracleLoggedRun_hashQuery, support_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  exact ⟨p, hp, rfl⟩
/-- a logged run that is answered entirely from the cache returns the cached evaluation -/
theorem loggedRun_cacheEval {Input : Type} [DecidableEq Input] {rounds : List Round} {α : Type}
    (V : OracleComp (oracleSpec Input PUnit rounds) α) (c : (oracleSpec Input PUnit rounds).QueryCache)
    (x : α) (h : cacheEval c V = some x) :
    ∀ y ∈ support (randomOracleLoggedRun (simulateQ (restorationQueries Input PUnit rounds) V) c),
      y.1.1 = x := by
  induction V using OracleComp.inductionOn generalizing c with
  | pure a =>
    intro y hy
    cases h
    simp [randomOracleLoggedRun] at hy
    rw [hy]
  | query_bind t k ih =>
    intro y hy
    rw [cacheEval_query_bind] at h
    rcases hct : c t with _ | v
    · rw [hct] at h; cases h
    rw [hct] at h
    rw [simulateQ_bind, simulateQ_spec_query, randomOracleLoggedRun_bind, mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [support_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    unfold restorationQueries at hp
    rw [randomOracleLoggedRun_hashQuery, support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [randomOracle.run_eq] at hq
    rw [show c.toFn t = some v from hct] at hq
    simp at hq
    subst hq
    exact ih v c h w hw


/-! ## The reduction B₂ and its cache invariant -/

section BSide

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
  (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
/-- compiled and paired FS keys -/
abbrev KeyC (Y Op Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) := Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)
abbrev KeyP (Y Statement Salt : Type) [Finite Y] [DecidableEq Y] (ms : MRounds Y) :=
  Key (Statement × Salt) PUnit (pairedRoundsK Y ms)
/-- the memo update of an FS answer (it does not read the answer) -/
def fsStep (s : Reduction.Obs Query Statement Salt Y) (d : KeyC Y Op Statement Salt ms) :
    Reduction.Obs Query Statement Salt Y :=
  { s with nck := s.nck + 1, memo := addEntries d.input (keyEntries ms [] d) (s.nck, s.log) s.memo }
/-- B₂'s renaming of a compiled FS key, read at the memo **after** the key's own entries are
recorded. (The `bImplK` reads the memo before the update; a fresh root is then translated
with an empty log, so the paired key it queries need not be the key the paired verifier asks.) -/
def eB (s : Reduction.Obs Query Statement Salt Y) (d : KeyC Y Op Statement Salt ms) :
    Option (KeyP Y Statement Salt ms) :=
  translateK Y Op ms (memoWords ext (fsStep s d)) [] d
/-- B₂'s simulation of A's oracle (`Rename.bImpl` at `eB`) -/
noncomputable def bImplE :=
  Rename.bImpl (RH := fun _ : Query => Y) (R := Key.Challenge)
    (R' := (Key.Challenge : KeyP Y Statement Salt ms → Type))
    (obsStep Y Op ms (Query := Query) (Statement := Statement) (Salt := Salt))
    (eB (Op := Op) ext) (untranslateK Y Op ms)
    (fun s d d' h => untranslate_translateK Y Op ms _ [] d d' h)
    (fun d' => (untranslate_challengeK Y Op ms d').symm)
/-- B₂'s cache invariant: every compiled FS key B answered has its memo entries, and its renaming
at the current memo is cached in B's oracle with the same answer -/
def InvB (s : Reduction.Obs Query Statement Salt Y)
    (cF : (ofFn (KC Y Op Statement Salt ms)).QueryCache)
    (cR : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache) : Prop :=
  ∀ d a, cF d = some a → (∀ e ∈ keyEntries ms [] d, s.memo (d.input, e) ≠ none) ∧
    ∀ d', translateK Y Op ms (memoWords ext s) [] d = some d' → ∃ a', cR d' = some a' ∧ HEq a' a
theorem invB_extend {s s' : Reduction.Obs Query Statement Salt Y}
    {cF : (ofFn (KC Y Op Statement Salt ms)).QueryCache}
    {cR cR' : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache}
    (h : InvB ext s cF cR) (hs : Extends s.memo s'.memo) (hc : cR ≤ cR') : InvB ext s' cF cR' := by
  intro d a hd
  obtain ⟨h1, h2⟩ := h d a hd
  refine ⟨fun e he h0 => h1 e he (by
    cases hm : s.memo (d.input, e) with
    | none => rfl
    | some u => rw [hs _ _ hm] at h0; cases h0), fun d' hd' => ?_⟩
  rw [translateK_stable ext s s' hs ms [] d h1] at hd'
  obtain ⟨a', ha', hh⟩ := h2 d' hd'
  exact ⟨a', QueryCache.le_def.mp hc ha', hh⟩
theorem invB_init : InvB (Op := Op) (ms := ms) ext (Reduction.Obs.init : Reduction.Obs Query Statement Salt Y) ∅ ∅ := by
  intro d a h; simp at h
/-- one FS step of B₂ -/
theorem stepB_fs (d : KeyC Y Op Statement Salt ms) (s : Reduction.Obs Query Statement Salt Y)
    (cH : (ofFn (fun _ : Query => Y)).QueryCache)
    (cF : (ofFn (KC Y Op Statement Salt ms)).QueryCache)
    (c : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache)
    (hI : InvB ext s cF c) (z)
    (hz : z ∈ support (randomOracleLoggedRun ((bImplE (Op := Op) ext (.inr (.inr d))).run (s, cH, cF)) c)) :
    InvB ext z.1.1.2.1 z.1.1.2.2.2 z.2 ∧ Extends s.memo z.1.1.2.1.memo ∧ cF ≤ z.1.1.2.2.2 ∧ c ≤ z.2 ∧
      z.1.1.2.2.2 d = some z.1.1.1 := by
  have hext : ∀ a, Extends s.memo (obsStep Y Op ms s (.inr d) a).memo :=
    fun a => obsStep_extends (Op := Op) (ms := ms) s (.inr d) a
  rcases hcF : cF d with _ | a
  · have hle : ∀ a, cF ≤ cF.cacheQuery d a := fun a => QueryCache.le_def.mpr fun t u ht => by
      have hne : t ≠ d := fun e => by subst e; rw [show cF.toFn t = cF t from rfl, hcF] at ht; cases ht
      exact (QueryCache.cacheQuery_of_ne _ _ hne).trans ht
    rcases he : eB (Op := Op) ext s d with _ | d'
    · rw [bImplE, Rename.bImpl_fs_none _ _ _ _ _ s cH cF d hcF he] at hz
      obtain ⟨-, hc, a, ha⟩ := FreshKeys.liftComp_map_logged _ _ c z hz
      rw [ha, hc]
      refine ⟨fun d₀ a₀ h₀ => ?_, hext a, hle a, le_rfl, QueryCache.cacheQuery_self _ _ _⟩
      by_cases hd : d₀ = d
      · subst hd
        refine ⟨obsStep_defined (Op := Op) (ms := ms) s d₀ a, fun d' hd' => ?_⟩
        exact absurd (he.symm.trans hd') (by simp)
      · dsimp only at h₀ ⊢
        exact invB_extend ext hI (hext a) le_rfl d₀ a₀
          ((QueryCache.cacheQuery_of_ne cF (t := d) a hd).symm.trans h₀)
    · rw [bImplE, Rename.bImpl_fs_some _ _ _ _ _ s cH cF d d' hcF he] at hz
      obtain ⟨p, hp, rfl⟩ := query_map_logged' _ _ c z hz
      obtain ⟨hp1, hp2⟩ := ro_step _ _ p hp
      dsimp only
      refine ⟨fun d₀ a₀ h₀ => ?_, hext _, hle _, hp2, QueryCache.cacheQuery_self _ _ _⟩
      by_cases hd : d₀ = d
      · subst hd
        rw [QueryCache.cacheQuery_self] at h₀
        obtain rfl := Option.some.inj h₀
        refine ⟨obsStep_defined (Op := Op) (ms := ms) s d₀ _, fun d'' hd'' => ?_⟩
        have : d'' = d' := Option.some.inj (hd''.symm.trans he)
        subst this
        exact ⟨p.1, hp1, (cast_heq _ _).symm⟩
      · exact invB_extend ext hI (hext _) hp2 d₀ a₀
          ((QueryCache.cacheQuery_of_ne cF (t := d) _ hd).symm.trans h₀)
  · simp only [bImplE, Rename.bImpl, StateT.run_mk, hcF] at hz
    simp [randomOracleLoggedRun] at hz
    subst hz
    exact ⟨invB_extend ext hI (hext a) le_rfl, hext a, le_rfl, le_rfl, hcF⟩


/-- one step of B₂ -/
theorem stepB (t : (Rename.ClientSpec (fun _ : Query => Y) (KC Y Op Statement Salt ms)).Domain)
    (s : Reduction.Obs Query Statement Salt Y) (cH : (ofFn (fun _ : Query => Y)).QueryCache)
    (cF : (ofFn (KC Y Op Statement Salt ms)).QueryCache)
    (c : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache)
    (hI : InvB ext s cF c) (z)
    (hz : z ∈ support (randomOracleLoggedRun ((bImplE (Op := Op) ext t).run (s, cH, cF)) c)) :
    InvB ext z.1.1.2.1 z.1.1.2.2.2 z.2 ∧ Extends s.memo z.1.1.2.1.memo ∧ cF ≤ z.1.1.2.2.2 ∧ c ≤ z.2 := by
  rcases t with n | q | d
  · have e1 : (bImplE (Op := Op) ext (.inl n)).run (s, cH, cF) =
        (fun a => (a, (s, cH, cF))) <$>
          (liftM ((unifSpec + OracleSpec.ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).query
            (.inl n)) : OracleComp _ (Fin (n+1))) := by
      simp [bImplE, Rename.bImpl]
    rw [e1, FreshKeys.loggedRun_map, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [randomOracleLoggedRun_uniformQuery, support_map] at hw
    obtain ⟨a, _, rfl⟩ := hw
    exact ⟨hI, Extends.refl _, le_rfl, le_rfl⟩
  · have hext : ∀ a, Extends s.memo (obsStep Y Op ms s (.inl q) a).memo := fun a => Extends.refl _
    rcases h : cH q with _ | a
    · simp only [bImplE, Rename.bImpl, StateT.run_mk, h] at hz
      have hz' : z ∈ support (randomOracleLoggedRun
          ((fun a : Y => ((a : (Rename.ClientSpec (fun _ : Query => Y)
              (KC Y Op Statement Salt ms)).Range (Sum.inr (Sum.inl q))),
            obsStep Y Op ms s (Sum.inl q) a, cH.cacheQuery q a, cF)) <$>
            OracleComp.liftComp ($ᵗ Y) (unifSpec + OracleSpec.ofFn
              (Key.Challenge : KeyP Y Statement Salt ms → Type))) c) := by
        rw [map_eq_bind_pure_comp]; exact hz
      obtain ⟨-, hc, a, ha⟩ := FreshKeys.liftComp_map_logged _ _ c z hz'
      rw [ha, hc]
      exact ⟨invB_extend ext hI (hext a) le_rfl, hext a, le_rfl, le_rfl⟩
    · simp only [bImplE, Rename.bImpl, StateT.run_mk, h] at hz
      simp [randomOracleLoggedRun] at hz
      subst hz
      exact ⟨invB_extend ext hI (hext a) le_rfl, hext a, le_rfl, le_rfl⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := stepB_fs ext d s cH cF c hI z hz
    exact ⟨h1, h2, h3, h4⟩
/-- B₂'s whole run keeps the invariant and only extends memo and caches -/
theorem runB {α : Type} (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) :
    ∀ (st : Reduction.Obs Query Statement Salt Y × (ofFn (fun _ : Query => Y)).QueryCache ×
        (ofFn (KC Y Op Statement Salt ms)).QueryCache)
      (c : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache),
      InvB ext st.1 st.2.2 c →
      ∀ z ∈ support (randomOracleLoggedRun ((simulateQ (bImplE (Op := Op) ext) oa).run st) c),
        InvB ext z.1.1.2.1 z.1.1.2.2.2 z.2 ∧ Extends st.1.memo z.1.1.2.1.memo ∧
          st.2.2 ≤ z.1.1.2.2.2 ∧ c ≤ z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st c hI z hz
    simp [randomOracleLoggedRun] at hz
    subst hz
    exact ⟨hI, Extends.refl _, le_rfl, le_rfl⟩
  | query_bind t k ih =>
    intro st c hI z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨st1, st2, st3⟩ := st
    obtain ⟨a1, a2, a3, a4⟩ := stepB ext t st1 st2 st3 c hI p hp
    obtain ⟨b1, b2, b3, b4⟩ := ih p.1.1.1 p.1.1.2 p.2 a1 w hw
    exact ⟨b1, a2.trans b2, a3.trans b3, a4.trans b4⟩
/-- B₂'s run of an FS-only segment returns its evaluation against B's final local FS cache -/
theorem segB {α : Type} (V : OracleComp (oracleSpec (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) α) :
    ∀ (st : Reduction.Obs Query Statement Salt Y × (ofFn (fun _ : Query => Y)).QueryCache ×
        (ofFn (KC Y Op Statement Salt ms)).QueryCache)
      (c : (ofFn (Key.Challenge : KeyP Y Statement Salt ms → Type)).QueryCache),
      InvB ext st.1 st.2.2 c →
      ∀ z ∈ support (randomOracleLoggedRun ((simulateQ (bImplE (Op := Op) ext)
          (simulateQ (fsQueriesK (Query := Query) (ms := ms)) V)).run st) c),
        cacheEval z.1.1.2.2.2 V = some z.1.1.1 := by
  induction V using OracleComp.inductionOn with
  | pure a =>
    intro st c hI z hz
    simp [randomOracleLoggedRun] at hz
    subst hz
    rfl
  | query_bind d k ih =>
    intro st c hI z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    unfold fsQueriesK at hz
    erw [simulateQ_spec_query] at hz
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨st1, st2, st3⟩ := st
    obtain ⟨a1, -, -, -, a5⟩ := stepB_fs ext d st1 st2 st3 c hI p hp
    obtain ⟨-, -, b3, -⟩ := runB ext _ p.1.1.2 p.2 a1 w hw
    have := ih p.1.1.1 p.1.1.2 p.2 a1 w hw
    rw [cacheEval_query_bind, show w.1.1.2.2.2 d = some p.1.1.1 from QueryCache.le_def.mp b3 a5]
    exact this

end BSide


/-! ## The paired verification replays the compiled one from the caches -/

section Replay

variable {Input : Type}

/-- `k` is a key the stopped verifier builds along the messages `m` -/
def AlongR : (rounds : List Round) → PublicMessages rounds → Key Input PUnit rounds → Prop
  | [], _, _ => True
  | _ :: _, (m, _), .inl (_, m', _) => m' = m
  | _ :: rs, (m, rest), .inr (m', _, k) => m' = m ∧ AlongR rs rest k
/-- the messages of an execution path -/
def MsgsOf : (rounds : List Round) → (protocol rounds).tree.ExecutionPath → PublicMessages rounds
  | [], _ => PUnit.unit
  | _ :: rs, p => (p.1, MsgsOf rs p.2.2)
theorem cacheEval_mapped {allA allB : List Round} :
    ∀ (rounds : List Round) (g : GuardSchedule Input PUnit rounds) (z : Input)
      (m : PublicMessages rounds)
      (eA : Key Input PUnit rounds → Key Input PUnit allA) (pA : ∀ k, (eA k).Challenge = k.Challenge)
      (eB : Key Input PUnit rounds → Key Input PUnit allB) (pB : ∀ k, (eB k).Challenge = k.Challenge)
      (cA : (oracleSpec Input PUnit allA).QueryCache) (cB : (oracleSpec Input PUnit allB).QueryCache)
      (x : Option (protocol rounds).tree.ExecutionPath),
      (∀ k, AlongR rounds m k → k.input = z → ∀ a, cA (eA k) = some a →
        ∃ b, cB (eB k) = some b ∧ cast (pB k) b = cast (pA k) a) →
      cacheEval cA (mappedStoppedComplete rounds g z m eA pA) = some x →
      cacheEval cB (mappedStoppedComplete rounds g z m eB pB) = some x
  | [], _, _, _, _, _, _, _, _, _, _, _, h => h
  | r :: rs, (guard, next), z, (msg, rest), eA, pA, eB, pB, cA, cB, x, hc, h => by
    by_cases hg : guard z msg PUnit.unit = true
    · simp only [mappedStoppedComplete] at h ⊢
      simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
      rw [cacheEval_query_bind] at h ⊢
      rcases ha : cA (eA (Key.here z msg PUnit.unit)) with _ | a
      · rw [ha] at h; cases h
      rw [ha] at h
      obtain ⟨b, hb, hab⟩ := hc (Key.here z msg PUnit.unit) rfl rfl a ha
      rw [hb]
      dsimp only at h ⊢
      rw [hab]
      rw [cacheEval_bind] at h ⊢
      rcases hs : cacheEval cA (mappedStoppedComplete rs (next msg PUnit.unit (cast (pA _) a)) z rest
        (fun k => eA (Key.later msg PUnit.unit k)) (fun k => pA (Key.later msg PUnit.unit k))) with _ | sx
      · rw [hs] at h; cases h
      rw [hs] at h
      rw [cacheEval_mapped rs _ z rest _ _ _ _ cA cB sx (fun k hk hz a' ha' =>
        hc (Key.later msg PUnit.unit k) ⟨rfl, hk⟩ hz a' ha') hs]
      exact h
    · have hg' : guard z msg PUnit.unit = false := by simpa using hg
      simp only [mappedStoppedComplete] at h ⊢
      simp only [hg', Bool.not_false, ite_true] at h ⊢
      exact h
theorem mapped_msgs {allR : List Round} :
    ∀ (rounds : List Round) (g : GuardSchedule Input PUnit rounds) (z : Input)
      (m : PublicMessages rounds) (e : Key Input PUnit rounds → Key Input PUnit allR)
      (pc : ∀ k, (e k).Challenge = k.Challenge) (pp : (protocol rounds).tree.ExecutionPath),
      some pp ∈ support (mappedStoppedComplete rounds g z m e pc) → MsgsOf rounds pp = m
  | [], _, _, _, _, _, _, _ => rfl
  | r :: rs, (guard, next), z, (msg, rest), e, pc, pp, h => by
    by_cases hg : guard z msg PUnit.unit = true
    · simp only [mappedStoppedComplete] at h
      simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨resp, -, suffix, hsuf, hpp⟩ := h
      rcases suffix with _ | tail
      · cases hpp
      · obtain rfl := Option.some.inj hpp
        show (msg, MsgsOf rs tail) = (msg, rest)
        rw [mapped_msgs rs _ z rest _ _ tail hsuf]
    · have hg' : guard z msg PUnit.unit = false := by simpa using hg
      simp only [mappedStoppedComplete] at h
      simp [hg'] at h

end Replay


section ReplayK

open NockvmE2E.Merkle.VerifyTransport NockvmE2E.Merkle.FreshKeys

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
  {Input : Type} {All : List Round}
theorem keyAlong_of_alongR : ∀ (ms : MRounds Y) (pm : PublicMessages (pairedRoundsK Y ms))
    (k : Key Input PUnit (pairedRoundsK Y ms)), AlongR (pairedRoundsK Y ms) pm k → KeyAlong ms pm k
  | [], _, _, _ => trivial
  | ⟨_, .clear⟩ :: _, (_, _), .inl _, h => h
  | ⟨_, .clear⟩ :: ms, (_, rest), .inr (_, _, k), h => ⟨h.1, keyAlong_of_alongR ms rest k h.2⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, (_, _), .inl _, h => h
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (_, rest), .inr (_, _, k), h => ⟨h.1, keyAlong_of_alongR ms rest k h.2⟩
/-- `finishK` rebuilds the compiled path from the paired one: the paired path is the compiled path
with the words `words` next to its roots. -/
theorem finish_pairPath (z : Input)
    (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    ∀ (ms : MRounds Y) (pre : List Y) (g : GuardSchedule Input PUnit (compiledRoundsK Y Op ms))
      (cm : PublicMessages (compiledRoundsK Y Op ms))
      (E : Key Input PUnit (compiledRoundsK Y Op ms) → Key Input PUnit All)
      (pc : ∀ k, (E k).Challenge = k.Challenge)
      (pp : (protocol (pairedRoundsK Y ms)).tree.ExecutionPath)
      (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath),
      some p ∈ support (finishK z ms g cm E pc pp) →
      MsgsOf (pairedRoundsK Y ms) pp = pairMsgs z words ms pre cm →
      pairPath (fun r hr => words r hr z) ms pre p = pp
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | ⟨_, .clear⟩ :: ms, pre, (_, next), (m, rest), E, pc, pp, p, hp, hm => by
    simp only [finishK, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨suffix, hs, hpe⟩ := hp
    rcases suffix with _ | tail
    · cases hpe
    obtain rfl := Option.some.inj hpe
    obtain ⟨h1, h2⟩ := Prod.mk.inj hm
    have ih := finish_pairPath z words ms pre _ rest _ _ pp.2.2 tail hs h2
    obtain ⟨a, b, c⟩ := pp
    simp only at h1 ih
    subst h1 ih
    rfl
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, pre, (_, next), (root, rest), E, pc, pp, p, hp, hm => by
    simp only [finishK, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨suffix, hs, hpe⟩ := hp
    rcases suffix with _ | tail
    · cases hpe
    obtain rfl := Option.some.inj hpe
    obtain ⟨h1, h2⟩ := Prod.mk.inj hm
    have ih := finish_pairPath z words ms _ _ rest _ _ pp.2.2 tail hs h2
    obtain ⟨a, b, c⟩ := pp
    simp only at h1 ih
    subst h1 ih
    rfl

end ReplayK


/-! ## B₂ and QD's acceptance on the support -/

section B2

open NockvmE2E.Merkle.VerifyTransport NockvmE2E.Merkle.FreshKeys

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
  (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
  (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
  (A : SuccinctAdversaryK Y Op Query Statement Salt W ms)
  (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
  (L : Set Statement)
/-- B₂'s witness: A's witness, the end-of-run memo, and A's verified compiled path -/
abbrev WB (Y Op Query Statement Salt W : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) := W × Reduction.Obs Query Statement Salt Y × PathC Y Op ms
/-- B₂'s output: the paired proof of A's verified run (words from the end-of-run memo) -/
def postB (r : Out1 Y Op Statement Salt W ms × (Reduction.Obs Query Statement Salt Y ×
      (ofFn (fun _ : Query => Y)).QueryCache ×
      (ofFn (KC Y Op Statement Salt ms)).QueryCache)) :
    Option (Statement × SaltedProof Salt (pairedRoundsK Y ms) × WB Y Op Query Statement Salt W ms) :=
  match r.1 with
  | some (o, some p) =>
      some (o.1, (o.2.1.1, pairMsgs (zOf o) (memoWords ext (finObsR r.2.1 (zOf o) p)) ms [] o.2.1.2),
        (o.2.2, finObsR r.2.1 (zOf o) p, p))
  | _ => none
/-- **The reduction B₂**: run `verifiedFS A` under `bImplE`, output the paired proof. -/
noncomputable def reductionB₂ :
    SingleSaltAdversary Statement Salt (WB Y Op Query Statement Salt W ms) (pairedRoundsK Y ms) :=
  postB ext <$> (simulateQ (bImplE (Op := Op) ext) (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)
/-- **QD's paired verification accepts B₂'s proof** on every run of B₂ that is good. -/
theorem qd_accepts (z) (hz : z ∈ support (randomOracleLoggedRun ((simulateQ (bImplE (Op := Op) ext)
      (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)) ∅))
    (hg : goodB L accepts ext (z.1.1.1, z.1.1.2.1)) :
    ∃ stmt salt pm wit, postB ext z.1.1 = some (stmt, (salt, pm), wit) ∧ stmt ∉ L ∧
      ∀ y ∈ support (randomOracleLoggedRun (simulateQ (restorationQueries (Statement × Salt) PUnit
          (pairedRoundsK Y ms)) (publicStoppedVerify (pairedRoundsK Y ms) (pairGuards Y Op ms guards)
            (stmt, salt) pm)) z.2),
        ∃ pp, y.1.1 = some pp ∧ pairAccepts Y ms accepts (stmt, salt) pp = true := by
  -- split the run into A and the FS verification
  unfold verifiedFS at hz
  simp only [simulateQ_bind, StateT.run_bind] at hz
  rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  obtain ⟨hIw, -, -, -⟩ := runB ext A _ ∅ (invB_init ext) w hw
  rcases hwo : w.1.1.1 with _ | o
  · rw [hwo] at hz'
    simp [randomOracleLoggedRun] at hz'
    rw [hz'] at hg
    exact hg.elim
  rw [hwo] at hz'
  simp only [simulateQ_map, StateT.run_map, FreshKeys.loggedRun_map, support_map] at hz'
  obtain ⟨z'', hz'', rfl⟩ := hz'
  have hseg := segB ext _ w.1.1.2 w.2 hIw z'' hz''
  obtain ⟨hI, -, -, -⟩ := runB ext _ w.1.1.2 w.2 hIw z'' hz''
  rcases hp : z''.1.1.1 with _ | p
  · simp only [hp] at hg; exact hg.elim
  simp only [hp] at hg hseg
  obtain ⟨hL, hacc⟩ := hg
  set s := z''.1.1.2.1
  set sf := finObsR s (zOf o) p
  have hIf : InvB ext sf z''.1.1.2.2.2 z''.2 :=
    invB_extend ext hI (Reduction.addEntries_extends _ _ _ _) le_rfl
  refine ⟨o.1, o.2.1.1, pairMsgs (zOf o) (memoWords ext sf) ms [] o.2.1.2, (o.2.2, sf, p),
    by simp [postB, hp, sf, s], hL, fun y hy => ?_⟩
  -- the compiled verification, evaluated against B's FS cache, is the paired one then `finishK`
  change cacheEval z''.1.1.2.2.2 (publicStoppedVerify (compiledRoundsK Y Op ms) guards (zOf o)
    o.2.1.2) = some (some p) at hseg
  rw [publicStoppedVerify_compiled_eq (zOf o) (memoWords ext sf), publicStoppedVerifyWith_eq_mapped,
    cacheEval_bind] at hseg
  rcases hpp : cacheEval z''.1.1.2.2.2 (mappedStoppedComplete (pairedRoundsK Y ms)
      (pairGuards Y Op ms guards) (zOf o) (pairMsgs (zOf o) (memoWords ext sf) ms [] o.2.1.2)
      (untranslateK Y Op ms) (untranslate_challengeK Y Op ms)) with _ | pp?
  · rw [hpp] at hseg; cases hseg
  rw [hpp] at hseg
  rcases pp? with _ | pp
  · cases hseg
  have hR := cacheEval_mapped _ _ _ _ _ _ id (fun _ => rfl) _ z''.2 _ (fun k hk hzk a ha => by
      obtain ⟨-, h2⟩ := hIf _ a ha
      obtain ⟨a', ha', hh⟩ := h2 k (translateK_untranslateK_pairMsgs (zOf o) (memoWords ext sf) ms []
        o.2.1.2 k hzk (keyAlong_of_alongR ms _ k hk))
      exact ⟨a', ha', eq_of_heq ((cast_heq _ _).trans (hh.trans (cast_heq _ _).symm))⟩) hpp
  rw [← publicStoppedVerifyWith_eq_mapped, ← publicStoppedVerify_eq_with] at hR
  refine ⟨pp, loggedRun_cacheEval _ _ _ hR y hy, ?_⟩
  have hmsgs := mapped_msgs _ _ _ _ _ _ pp (cacheEval_mem_support _ _ _ hpp)
  have hfin := finish_pairPath (zOf o) (memoWords ext sf) ms [] guards o.2.1.2 id (fun _ => rfl) pp p
    (cacheEval_mem_support _ _ _ hseg) hmsgs
  rw [← hfin]
  exact hacc

/-! ## The probability chain: W' good ⇒ real world ⇒ B₂ (renaming) ⇒ QD accepts -/

theorem romImpl_obsR {α : Type} (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) :
    ∀ (s : Reduction.Obs Query Statement Salt Y)
      (c : (ofFn (Sum.elim (fun _ : Query => Y) (KC Y Op Statement Salt ms))).QueryCache),
      (simulateQ (@OracleSpec.romImpl _ (ofFn (Sum.elim (fun _ : Query => Y)
          (KC Y Op Statement Salt ms))) _ (fun t => Rename.sumElimSampleable t))
        ((simulateQ obsR oa).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (Rename.realImpl (obsStep Y Op ms)) oa).run (s, c) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s c; simp
  | query_bind t k ih =>
    intro s c
    rw [obsR_run_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with n | t
    · have h : (unifFwdImpl (OracleSpec.ofFn (Sum.elim (fun _ : Query => Y)
          (KC Y Op Statement Salt ms))) n).run c =
          (fun u => (u, c)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n+1))) := rfl
      simp only [OracleSpec.romImpl, QueryImpl.add_apply_inl, h, bind_map_left]
      simp [Rename.realImpl, stepR, ih]
    · rw [Rename.realImpl_run]
      simp only [OracleSpec.romImpl, QueryImpl.add_apply_inr, bind_map_left]
      simp [stepR, ih]
theorem loggedRun_inst {D α : Type} {R : D → Type} [DecidableEq D] {i₁ i₂ : ∀ d, SampleableType (R d)}
    {oa : OracleComp (unifSpec + ofFn R) α} {c : (ofFn R).QueryCache} (h : i₁ = i₂) :
    @randomOracleLoggedRun D α R _ i₁ oa c = @randomOracleLoggedRun D α R _ i₂ oa c := by
  subst h; rfl
/-- **Real world ↔ B₂ (renaming).** Any event of (A's verified output, reduction memo) has the same
probability in the instrumented real world and inside B₂'s simulation. -/
theorem pr_instrA_eq_B (P : Out1 Y Op Statement Salt W ms ×
      Reduction.Obs Query Statement Salt Y → Prop) :
    Pr{let y ← randomOracleLoggedRun (instrA guards A) ∅}[P y.1.1] =
    Pr{let z ← randomOracleLoggedRun ((simulateQ (bImplE (Op := Op) ext)
      (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)) ∅}[P (z.1.1.1, z.1.1.2.1)] := by
  let : MeasurableSpace (OutO Y Op Query Statement Salt W ms) := ⊤
  have : DiscreteMeasurableSpace (OutO Y Op Query Statement Salt W ms) :=
    ⟨fun _ => trivial⟩
  have hR := Rename.evalDist_adaptiveRename (RH := fun _ : Query => Y) (R := Key.Challenge)
    (R' := (Key.Challenge : KeyP Y Statement Salt ms → Type))
    (obsStep Y Op ms (Query := Query) (Statement := Statement) (Salt := Salt))
    (eB (Op := Op) ext) (untranslateK Y Op ms)
    (fun s d d' h => untranslate_translateK Y Op ms _ [] d d' h)
    (fun d' => (untranslate_challengeK Y Op ms d').symm) (FreshKeys.hS_K (Op := Op))
    (verifiedFS guards A) Reduction.Obs.init
  calc Pr{let y ← randomOracleLoggedRun (instrA guards A) ∅}[P y.1.1]
      = Pr{let y ← (fun z => (z.1.1, z.2)) <$> randomOracleLoggedRun (instrA guards A) ∅}[P y.1] :=
        (prEvent_map (randomOracleLoggedRun (instrA guards A) ∅) (fun z => (z.1.1, z.2))
          (fun y => P y.1)).symm
    _ = Pr{let y ← (fun z : Out1 Y Op Statement Salt W ms × Reduction.Obs Query Statement Salt Y ×
            (ofFn (Sum.elim (fun _ : Query => Y)
              (KC Y Op Statement Salt ms))).QueryCache => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ (Rename.realImpl (obsStep Y Op ms
          (Query := Query) (Statement := Statement) (Salt := Salt))) (verifiedFS guards A)).run
            (Reduction.Obs.init, ∅)}[P y.1] := by
        have h1 := congrArg (fun L => Pr{let y ← (fun z : ((Out1 Y Op Statement Salt W ms ×
            Reduction.Obs Query Statement Salt Y) × _) × _ => (z.1.1, z.2)) <$> L}[P y.1])
          (loggedRun_inst (oa := instrA guards A) (c := ∅) FreshKeys.inst_eq)
        refine h1.trans ?_
        rw [@randomOracleLoggedRun_project _ _ _ _ (fun d => Rename.sumElimSampleable d), instrA,
          romImpl_obsR]
    _ = Pr{let z ← (fun z => (z.1, z.2.1)) <$> (simulateQ (Rename.realImpl (obsStep Y Op ms
          (Query := Query) (Statement := Statement) (Salt := Salt))) (verifiedFS guards A)).run
            (Reduction.Obs.init, ∅)}[P z] := by
        rw [prEvent_map, prEvent_map]
    _ = Pr{let z ← (fun z => (z.1.1.1, z.1.1.2.1)) <$> randomOracleLoggedRun ((simulateQ
          (bImplE (Op := Op) ext) (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)) ∅}[P z] := by
        rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
        exact congrArg (fun μ => μ {x | P x}) hR.symm
    _ = _ := prEvent_map _ _ _
/-- **B₂ good ⇒ QD accepts**: the good event inside B₂ is at most QD's accepted-and-outside-`L`
event for B₂. -/
theorem pr_B_le_qd :
    Pr{let z ← randomOracleLoggedRun ((simulateQ (bImplE (Op := Op) ext)
      (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)) ∅}[goodB L accepts ext (z.1.1.1, z.1.1.2.1)] ≤
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution (pairedRoundsK Y ms)
        (pairGuards Y Op ms guards) (pairAccepts Y ms accepts) (reductionB₂ ext guards A)) ∅}[
      match j.1.1.1 with | none => False | some (z, _, _) => z.1 ∉ L] := by
  set X := (simulateQ (bImplE (Op := Op) ext) (verifiedFS guards A)).run (Reduction.Obs.init, ∅, ∅)
  rw [singleSaltAcceptedExecution_loggedRun, prEvent_map]
  have hB : (reductionB₂ ext guards A).withQueryLog = (fun r => (postB ext r.1, r.2)) <$> X.withQueryLog := by
    unfold reductionB₂
    simp [map_eq_bind_pure_comp, withQueryLog_bind, withQueryLog_pure]
    rfl
  unfold singleSaltExecution
  rw [hB, bind_map_left, randomOracleLoggedRun_bind]
  rw [← FreshKeys.loggedRun_withQueryLog X ∅, prEvent_map]
  refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun q hq hg => ?_
  have hzq : ((q.1.1.1, q.1.2), q.2) ∈ support (randomOracleLoggedRun X ∅) := by
    rw [← FreshKeys.loggedRun_withQueryLog X ∅, support_map]; exact ⟨q, hq, rfl⟩
  obtain ⟨stmt, salt, pm, wit, hpost, hL, hver⟩ := qd_accepts ext guards A accepts L _ hzq hg
  refine prEvent_eq_one_of_forall_mem_support _ _ fun y hy => ?_
  rw [support_map] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  simp only at hpost
  simp only [hpost] at hw
  rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hw
  obtain ⟨v, hv, hw⟩ := hw
  simp [randomOracleLoggedRun] at hw
  subst hw
  obtain ⟨pp, hpp, hacc⟩ := hver v hv
  simp [hpp, acceptSingleSaltResult, Option.filter, hacc, hL]
/-- **B₂ meets QD's support-wise `queryBound`** when A₁ = `verifiedFS A` does (H1′). -/
theorem reductionB₂_queryBound (Qfs : ℕ)
    (hA : ∀ w ∈ support (randomOracleLoggedRun (verifiedFS guards A).withQueryLog ∅),
      (fsKeysOfLogK (Op := Op) w.1.2).card ≤ Qfs) :
    ∀ phase ∈ support (randomOracleLoggedRun (reductionB₂ ext guards A).withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Qfs := by
  intro phase hphase
  have h1 : ((phase.1.1.1, phase.1.2), phase.2) ∈ support (randomOracleLoggedRun (reductionB₂ ext guards A) ∅) := by
    rw [← FreshKeys.loggedRun_withQueryLog, support_map]; exact ⟨phase, hphase, rfl⟩
  unfold reductionB₂ at h1
  rw [FreshKeys.loggedRun_map, support_map] at h1
  obtain ⟨p, hp, hpe⟩ := h1
  have hlog : phase.1.2 = p.1.2 := (congrArg (fun x => x.1.2) hpe).symm
  rw [hlog]
  exact bImpl_queryBound (RH := fun _ : Query => Y) (R := Key.Challenge)
    (R' := (Key.Challenge : KeyP Y Statement Salt ms → Type))
    (obsStep Y Op ms (Query := Query) (Statement := Statement) (Salt := Salt))
    (eB (Op := Op) ext) (untranslateK Y Op ms)
    (fun s d d' h => untranslate_translateK Y Op ms _ [] d d' h)
    (fun d' => (untranslate_challengeK Y Op ms d').symm) (hS_K (Op := Op))
    (verifiedFS guards A) Reduction.Obs.init Qfs (by
      have e := inst_eq (Y := Y) (Op := Op) (Query := Query) (Statement := Statement) (Salt := Salt) (ms := ms)
      convert hA using 5
      exact e.symm) p hp

end B2

end NockvmE2E.Merkle.SoundnessCoupling
