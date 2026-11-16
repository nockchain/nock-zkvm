/-
Merkle (B): `FsBound ∅ Q oa` bounds the distinct fresh FS keys of every logged lazy-RO run of `oa`.
-/
import NockvmE2E.Merkle.BadBound
import NockvmE2E.Merkle.FreshKeys

open OracleComp OracleSpec
open NockvmE2E.Merkle.Derand NockvmE2E.Merkle.Phases NockvmE2E.Merkle.BadBound

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.FsBoundSupport

variable {Q Y K : Type} {Rc : K → Type} [DecidableEq Q] [DecidableEq K]
  [∀ d, SampleableType (Rfam Q Y Rc d)] [SampleableType Y] [∀ k, SampleableType (Rc k)]

theorem queryBind_eq {α : Type} (t : (realSpec Q Y Rc).Domain)
    (k : (realSpec Q Y Rc).Range t → OracleComp (realSpec Q Y Rc) α) :
    OracleComp.queryBind t k = (liftM ((realSpec Q Y Rc).query t) >>= k) := rfl

theorem cq_ne {ι : Type} {S : OracleSpec ι} [DecidableEq ι] (c : S.QueryCache) {k' key : ι} (u : S.Range key)
    (h : k' ≠ key) : (c.cacheQuery key u) k' = c k' := QueryCache.cacheQuery_of_ne c u h

theorem mem_fsKeys {log : QueryLog (ofFn (Rfam Q Y Rc))} {d : K} :
    d ∈ FreshKeys.fsKeysOfLog (RH := fun _ : Q => Y) (R := Rc) log ↔ ∃ e ∈ log, e.1 = Sum.inr d := by
  rw [FreshKeys.mem_fsKeysOfLog, mem_freshKeysOfLog]

open Classical in
/-- **Support-wise FS-key bound from `FsBound`.** If the lazy RO cache `c` agrees with `seen` on FS keys,
every logged run of `oa` queries at most `n` distinct FS keys not already in `seen`. -/
theorem supportFS_aux {α : Type} {seen : (ofFn Rc).QueryCache} {n : ℕ} {oa : OracleComp (realSpec Q Y Rc) α}
    (h : FsBound seen n oa) :
    ∀ (c : (ofFn (Rfam Q Y Rc)).QueryCache), (∀ key, c (Sum.inr key) = seen key) →
      ∀ w ∈ support (randomOracleLoggedRun oa c),
        ((FreshKeys.fsKeysOfLog (RH := fun _ : Q => Y) (R := Rc) w.1.2).filter
          (fun k => seen k = none)).card ≤ n := by
  induction h with
  | pure a seen n =>
    intro c hc w hw
    simp [randomOracleLoggedRun] at hw
    subst hw; simp [FreshKeys.fsKeysOfLog]
  | coin cc k seen n _ ih =>
    intro c hc w hw
    rw [queryBind_eq, randomOracleLoggedRun_bind, mem_support_bind_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    rw [support_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    simpa using ih _ c hc w' hw'
  | hash q k seen n _ ih =>
    intro c hc w hw
    rw [queryBind_eq, randomOracleLoggedRun_bind, mem_support_bind_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    rw [support_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [randomOracleLoggedRun_hashQuery, support_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    have hs := FreshKeys.randomOracle_step _ c p' hp'
    have := ih _ p'.2 (by
      intro key
      rcases hs with ⟨_, h4⟩ | ⟨_, h4⟩
      · rw [h4]; exact hc key
      · rw [h4, cq_ne _ _ (by simp)]; exact hc key) w' hw'
    refine le_trans (Finset.card_le_card ?_) this
    intro d hd
    rw [Finset.mem_filter, mem_fsKeys] at hd ⊢
    obtain ⟨⟨e, he, he2⟩, hd2⟩ := hd
    refine ⟨⟨e, ?_, he2⟩, hd2⟩
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with rfl | he
    · simp at he2
    · exact he
  | fs key k seen n hseen hn hfresh ih1 ih2 =>
    intro c hc w hw
    rw [queryBind_eq, randomOracleLoggedRun_bind, mem_support_bind_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    rw [support_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [randomOracleLoggedRun_hashQuery, support_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    have hs := FreshKeys.randomOracle_step _ c p' hp'
    simp only at hw'
    rcases hsk : seen key with _ | v
    · have hn' := hn hsk
      have hck : c (Sum.inr key) = none := (hc key).trans hsk
      rcases hs with ⟨h3, _⟩ | ⟨_, h4⟩
      · simp [hck] at h3
      · have := ih2 p'.1 hsk (p'.2) (by
          intro k'
          rw [h4]
          by_cases hk' : k' = key
          · subst hk'; simp
          · have e1 : (c.cacheQuery (Sum.inr key) p'.1) (Sum.inr k') = c (Sum.inr k') :=
              cq_ne (S := ofFn (Rfam Q Y Rc)) _ _ (by simpa using hk')
            have e2 : (seen.cacheQuery key p'.1) k' = seen k' := cq_ne (S := ofFn Rc) _ _ hk'
            exact e1.trans ((hc k').trans e2.symm)) w' hw'
        refine le_trans (Finset.card_le_card ?_) (((Finset.card_insert_le key _).trans (Nat.succ_le_succ this)).trans (by omega))
        intro d hd
        rw [Finset.mem_filter, mem_fsKeys] at hd
        obtain ⟨⟨e, he, he2⟩, hd2⟩ := hd
        by_cases hdk : d = key
        · subst hdk; exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨mem_fsKeys.mpr ⟨e, ?_, he2⟩, ?_⟩)
          · simp only [List.mem_append, List.mem_singleton] at he
            rcases he with rfl | he
            · exact absurd (Sum.inr_injective he2).symm hdk
            · exact he
          · exact (cq_ne (S := ofFn Rc) seen p'.1 hdk).trans hd2
    · have hck : c (Sum.inr key) = some v := (hc key).trans hsk
      rcases hs with ⟨_, h4⟩ | ⟨h3, _⟩
      · have hv : p'.1 = v := by
          rw [randomOracle.run_eq, show c (Sum.inr key) = some v from hck] at hp'
          simp at hp'; subst hp'; rfl
        have := ih1 p'.1 (hv ▸ hsk) p'.2 (by rw [h4]; exact hc) w' hw'
        refine le_trans (Finset.card_le_card ?_) this
        intro d hd
        rw [Finset.mem_filter, mem_fsKeys] at hd ⊢
        obtain ⟨⟨e, he, he2⟩, hd2⟩ := hd
        refine ⟨⟨e, ?_, he2⟩, hd2⟩
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with rfl | he
        · have := Sum.inr_injective he2
          subst this; rw [hsk] at hd2; cases hd2
        · exact he
      · simp [hck] at h3

open Classical in
/-- **`FsBound ∅ n oa` ⇒ every logged lazy-RO run of `oa` (source-logged) has at most `n` distinct FS keys.** -/
theorem supportFS_of_FsBound {α : Type} {n : ℕ} {oa : OracleComp (realSpec Q Y Rc) α}
    (h : FsBound (∅ : (ofFn Rc).QueryCache) n oa) :
    ∀ w ∈ support (randomOracleLoggedRun oa.withQueryLog ∅),
      (FreshKeys.fsKeysOfLog (RH := fun _ : Q => Y) (R := Rc) w.1.2).card ≤ n := by
  intro w hw
  have h1 : ((w.1.1.1, w.1.2), w.2) ∈ support (randomOracleLoggedRun oa ∅) := by
    rw [← FreshKeys.loggedRun_withQueryLog, support_map]; exact ⟨w, hw, rfl⟩
  have := supportFS_aux h ∅ (fun _ => rfl) _ h1
  have e : ∀ s : Finset K, s.filter (fun k => (∅ : (ofFn Rc).QueryCache) k = none) = s :=
    fun s => Finset.filter_true_of_mem fun k _ => rfl
  rw [e] at this
  exact this

end NockvmE2E.Merkle.FsBoundSupport
