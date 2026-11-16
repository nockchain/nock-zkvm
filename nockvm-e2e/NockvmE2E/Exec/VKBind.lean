/-
  NockvmE2E/Exec/VKBind.lean   (pcs,  1.2 term (c), 1.3 row "VK-tree binding"; KERNEL-checked)

  Binding of the VK tree.  `goRoot` (Verify.lean) recomputes a Merkle root from an opened set of leaves and frontier digests.  If it accepts
  against the spec root `specRoot X Hf` (= `(vkSpec X Hf).root`, VKSpecExe.lean) while an opened leaf differs from the honest leaf, two
  DISTINCT hash inputs have equal `Hf` among {the verifier's recomputation, the honest nodes}: `VKcoll`.
-/
import NockvmE2E.Exec.VKSpecExe
import NockvmE2E.Exec.Verify
import VCVio.OracleComp.QueryTracking.Birthday

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open OracleComp OracleSpec ENNReal
open scoped OracleSpec.PrimitiveQuery

namespace NockvmE2E.Exec.VKBind
open NockvmE2E.Exec.V

/-! ### 1. `lb` (binary search) characterisation -/

/-- `a` is sorted (weakly) -/
def Sorted (a : Array ℕ) : Prop := ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!

/-- `m` is the lower-bound position of `x` in `a` -/
def IsLB (a : Array ℕ) (x m : ℕ) : Prop :=
  m ≤ a.size ∧ (∀ i, i < m → a[i]! < x) ∧ (∀ i, m ≤ i → i < a.size → x ≤ a[i]!)

theorem lbGo_spec (a : Array ℕ) (x : ℕ) (ha : Sorted a) : ∀ (f lo hi : ℕ), lo ≤ hi → hi ≤ a.size → hi - lo ≤ f →
    (∀ i, i < lo → a[i]! < x) → (∀ i, hi ≤ i → i < a.size → x ≤ a[i]!) → IsLB a x (lbGo a x f lo hi) := by
  intro f
  induction f with
  | zero =>
    intro lo hi h1 h2 h3 h4 h5
    have : lo = hi := by omega
    subst this
    simp only [lbGo]
    exact ⟨h2, h4, h5⟩
  | succ f ih =>
    intro lo hi h1 h2 h3 h4 h5
    simp only [lbGo]
    by_cases hlt : lo < hi
    · have hmid : (lo + hi) / 2 < a.size := by omega
      simp only [hlt, ite_true]
      by_cases hx : a[(lo + hi) / 2]! < x
      · simp only [hx, ite_true]
        refine ih _ _ (by omega) h2 (by omega) ?_ h5
        intro i hi'
        by_cases hc : i = (lo + hi) / 2
        · subst hc; exact hx
        · exact lt_of_le_of_lt (ha i _ (by omega) hmid) hx
      · simp only [hx, ite_false]
        refine ih _ _ (by omega) (by omega) (by omega) h4 ?_
        intro i hi' hi''
        exact le_trans (not_lt.mp hx) (ha _ i hi' hi'')
    · simp only [hlt, ite_false]
      have : lo = hi := by omega
      subst this
      exact ⟨h2, h4, h5⟩

theorem lb_spec (a : Array ℕ) (ha : Sorted a) (x : ℕ) : IsLB a x (lb a x) :=
  lbGo_spec a x ha _ 0 a.size (Nat.zero_le _) le_rfl (by omega) (fun i hi => absurd hi (by omega)) (fun i hi hi' => absurd hi' (by omega))

theorem lb_mono (a : Array ℕ) (ha : Sorted a) {x y : ℕ} (h : x ≤ y) : lb a x ≤ lb a y := by
  obtain ⟨hs, h1, h2⟩ := lb_spec a ha x
  obtain ⟨hs', h1', h2'⟩ := lb_spec a ha y
  by_contra hc
  push Not at hc
  have := h1 _ hc
  have := h2' _ le_rfl (by omega)
  omega

theorem lt_lb (a : Array ℕ) (ha : Sorted a) {x i : ℕ} (hi : i < a.size) (h : a[i]! < x) : i < lb a x := by
  obtain ⟨hs, h1, h2⟩ := lb_spec a ha x
  by_contra hc
  push Not at hc
  have := h2 _ hc hi
  omega



/-! ### 2. the lazy hash oracle and its caching run -/

abbrev HS (Y : Type) := (List ℕ →ₒ Y)

section Lazy
variable {Y : Type} (dg : Y → Dg5)

/-- a hash evaluation: one query of the lazy random oracle, read out as a digest -/
def hq (x : List ℕ) : OracleComp (HS Y) Dg5 :=
  (fun v => dg v) <$> (liftM ((HS Y).query x) : OracleComp (HS Y) ((HS Y).Range x))

/-- the flat hash function read off a cache (unqueried inputs read as the zero digest) -/
def Hc (c : QueryCache (HS Y)) (x : List ℕ) : Dg5 := match c x with | some v => dg v | none => [0, 0, 0, 0, 0]

/-- `(a, c')` is a possible outcome of running `x` under the caching oracle from cache `c` -/
def Runs {α : Type} (x : OracleComp (HS Y) α) (c : QueryCache (HS Y)) (a : α) (c' : QueryCache (HS Y)) : Prop :=
  (a, c') ∈ support ((simulateQ cachingOracle x).run c)

theorem Runs.le {α : Type} {x : OracleComp (HS Y) α} {c c' : QueryCache (HS Y)} {a : α} (h : Runs x c a c') : c ≤ c' :=
  simulateQ_cachingOracle_cache_le x c _ h

theorem Runs_pure {α : Type} (a a' : α) (c c' : QueryCache (HS Y)) (h : Runs (pure a : OracleComp (HS Y) α) c a' c') :
    a' = a ∧ c' = c := by
  unfold Runs at h
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
  exact h

theorem Runs_pure_intro {α : Type} (a : α) (c : QueryCache (HS Y)) : Runs (pure a : OracleComp (HS Y) α) c a c := by
  unfold Runs
  simp

theorem Runs_bind {α β : Type} {x : OracleComp (HS Y) α} {g : α → OracleComp (HS Y) β} {c : QueryCache (HS Y)} {b : β}
    {c'' : QueryCache (HS Y)} (h : Runs (x >>= g) c b c'') :
    ∃ a c', Runs x c a c' ∧ Runs (g a) c' b c'' := by
  unfold Runs at h ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨a, c'⟩, h1, h2⟩ := h
  exact ⟨a, c', h1, h2⟩

theorem Runs_bind_intro {α β : Type} {x : OracleComp (HS Y) α} {g : α → OracleComp (HS Y) β} {c : QueryCache (HS Y)} {b : β}
    {c'' c' : QueryCache (HS Y)} {a : α} (h1 : Runs x c a c') (h2 : Runs (g a) c' b c'') : Runs (x >>= g) c b c'' := by
  unfold Runs at h1 h2 ⊢
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨(a, c'), h1, h2⟩

theorem Runs_hq {x : List ℕ} {c c' : QueryCache (HS Y)} {d : Dg5} (h : Runs (hq dg x) c d c') :
    ∃ v, c' x = some v ∧ d = dg v := by
  unfold Runs hq at h
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨v, c1⟩, hv, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [cachingOracle.simulateQ_query] at hv
  exact ⟨v, cachingOracle_query_caches x c v c1 hv, rfl⟩

end Lazy

/-! ### 3. the monadic verifier recomputation and the monadic honest tree -/

section Mon
variable {Y : Type} (dg : Y → Dg5)

/-- `goRootF` (Verify.lean) with the hash replaced by queries to the lazy oracle (same case analysis, same order of evaluation) -/
def goRootG (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5) :
    ℕ → ℕ → ℕ → ℕ → ℕ → OracleComp (HS Y) (Option (Dg5 × ℕ))
  | 0, _, _, _, _ => pure none
  | f + 1, idx, lo, cnt, s =>
    if cnt == 1 then
      pure (if sel[lb sel lo]? == some lo then some (leaf (lb sel lo), s) else none)
    else if sp.split cnt == 0 || decide (sp.split cnt ≥ cnt) then pure none
    else
      if lb sel (lo + sp.split cnt) > lb sel lo && lb sel (lo + cnt) > lb sel (lo + sp.split cnt) then do
        let r1 ← goRootG sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s
        match r1 with
        | none => pure none
        | some (l, s1) => do
          let r2 ← goRootG sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1
          match r2 with
          | none => pure none
          | some (r, s2) => do
            let d ← hq dg ([tagNode, j, idx] ++ l ++ r)
            pure (some (d, s2))
      else if lb sel (lo + sp.split cnt) > lb sel lo then
        match sibs[s]? with
        | none => pure none
        | some sib => do
          let r1 ← goRootG sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)
          match r1 with
          | none => pure none
          | some (l, s1) => do
            let d ← hq dg ([tagNode, j, idx] ++ l ++ sib)
            pure (some (d, s1))
      else if lb sel (lo + cnt) > lb sel (lo + sp.split cnt) then
        match sibs[s]? with
        | none => pure none
        | some sib => do
          let r1 ← goRootG sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)
          match r1 with
          | none => pure none
          | some (r, s1) => do
            let d ← hq dg ([tagNode, j, idx] ++ sib ++ r)
            pure (some (d, s1))
      else pure none

/-- the honest digest of the node `idx` over the leaves `lo ..< lo+cnt` (same recursion shape as the verifier; `hl` = honest leaf digests),
with its hash evaluations issued as queries -/
def honG (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) : ℕ → ℕ → ℕ → ℕ → OracleComp (HS Y) Dg5
  | 0, _, _, _ => pure [0, 0, 0, 0, 0]
  | f + 1, idx, lo, cnt =>
    if cnt == 1 then pure (hl lo) else do
      let l ← honG sp j hl f (2 * idx) lo (sp.split cnt)
      let r ← honG sp j hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt)
      hq dg ([tagNode, j, idx] ++ l ++ r)

/-- the same, as a pure function of a flat hash `H` -/
def honP (H : HFn) (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) : ℕ → ℕ → ℕ → ℕ → Dg5
  | 0, _, _, _ => [0, 0, 0, 0, 0]
  | f + 1, idx, lo, cnt =>
    if cnt == 1 then hl lo else
      H ([tagNode, j, idx] ++ honP H sp j hl f (2 * idx) lo (sp.split cnt) ++
        honP H sp j hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt))

end Mon

section Bridge
variable {Y : Type} (dg : Y → Dg5)

theorem Runs_hq' {x : List ℕ} {c c' : QueryCache (HS Y)} {d : Dg5} (h : Runs (hq dg x) c d c') :
    c ≤ c' ∧ ∃ v, c' x = some v ∧ d = dg v := by
  refine ⟨?_, Runs_hq dg h⟩
  unfold Runs hq at h
  exact simulateQ_cachingOracle_cache_le _ _ _ h

theorem Hc_of_le {c c'' : QueryCache (HS Y)} (h : c ≤ c'') {x : List ℕ} {v : Y} (hx : c x = some v) : Hc dg c'' x = dg v := by
  have := h hx
  simp [Hc, this]

theorem honG_run (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) (hl5 : ∀ lo, (hl lo).length = 5) (hdg5 : ∀ v, (dg v).length = 5) :
    ∀ (f idx lo cnt : ℕ) (c c' : QueryCache (HS Y)) (d : Dg5), Runs (honG dg sp j hl f idx lo cnt) c d c' →
      c ≤ c' ∧ d.length = 5 ∧ ∀ c'', c' ≤ c'' → honP (Hc dg c'') sp j hl f idx lo cnt = d := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt c c' d h
    simp only [honG] at h
    obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
    exact ⟨le_rfl, rfl, fun _ _ => rfl⟩
  | succ f ih =>
    intro idx lo cnt c c' d h
    simp only [honG] at h
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true] at h
      obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
      exact ⟨le_rfl, hl5 _, fun _ _ => by simp [honP, h1]⟩
    · simp only [h1, Bool.false_eq_true, if_false] at h
      obtain ⟨l, c1, hl1, h2⟩ := Runs_bind h
      obtain ⟨r, c2, hr1, h3⟩ := Runs_bind h2
      obtain ⟨hle1, hlen1, hv1⟩ := ih _ _ _ _ _ _ hl1
      obtain ⟨hle2, hlen2, hv2⟩ := ih _ _ _ _ _ _ hr1
      obtain ⟨hle3, v, hv, hd⟩ := Runs_hq' dg h3
      refine ⟨hle1.trans (hle2.trans hle3), by rw [hd]; exact hdg5 v, fun c'' hc'' => ?_⟩
      simp only [honP, h1, Bool.false_eq_true, if_false]
      rw [hv1 c'' ((hle2.trans hle3).trans hc''), hv2 c'' (hle3.trans hc''), hd]
      exact Hc_of_le dg hc'' hv

theorem goRootG_run (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5)
    (hleaf5 : ∀ r, (leaf r).length = 5) (hsib5 : ∀ (s : ℕ) (sib : Dg5), sibs[s]? = some sib → sib.length = 5)
    (hdg5 : ∀ v, (dg v).length = 5) :
    ∀ (f idx lo cnt s : ℕ) (c c' : QueryCache (HS Y)) (res : Option (Dg5 × ℕ)),
      Runs (goRootG dg sp j sel leaf sibs f idx lo cnt s) c res c' →
      c ≤ c' ∧ (∀ d s', res = some (d, s') → d.length = 5) ∧
        ∀ c'', c' ≤ c'' → goRootF (Hc dg c'') sp j sel leaf sibs f idx lo cnt s = res := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt s c c' res h
    simp only [goRootG] at h
    obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
    exact ⟨le_rfl, by simp, fun _ _ => by simp [goRootF]⟩
  | succ f ih =>
    intro idx lo cnt s c c' res h
    simp only [goRootG] at h
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true] at h
      obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
      refine ⟨le_rfl, ?_, fun _ _ => by simp [goRootF, h1]⟩
      intro d s' hd
      split at hd
      · simp only [Option.some.injEq, Prod.mk.injEq] at hd; rw [← hd.1]; exact hleaf5 _
      · simp at hd
    · simp only [h1, Bool.false_eq_true, ite_false] at h
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true] at h
        obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
        exact ⟨le_rfl, by simp, fun _ _ => by simp [goRootF, h1, hg]⟩
      · simp only [hg, Bool.false_eq_true, ite_false] at h
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA] at h
          obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind h
          obtain ⟨hle1, hlen1, hv1⟩ := ih _ _ _ _ _ _ _ hr1
          rcases r1 with _ | ⟨l, s1⟩
          · simp only at h2
            obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h2
            refine ⟨hle1, by simp, fun c'' hc'' => ?_⟩
            simp [goRootF, h1, hg, hB, hC, hv1 c'' hc'']
          · simp only at h2
            obtain ⟨r2, c2, hr2, h3⟩ := Runs_bind h2
            obtain ⟨hle2, hlen2, hv2⟩ := ih _ _ _ _ _ _ _ hr2
            rcases r2 with _ | ⟨r, s2⟩
            · simp only at h3
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h3
              refine ⟨hle1.trans hle2, by simp, fun c'' hc'' => ?_⟩
              simp [goRootF, h1, hg, hB, hC, hv1 c'' (hle2.trans hc''), hv2 c'' hc'']
            · simp only at h3
              obtain ⟨d, c3, hr3, h4⟩ := Runs_bind h3
              obtain ⟨hle3, v, hv, hd⟩ := Runs_hq' dg hr3
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h4
              refine ⟨hle1.trans (hle2.trans hle3), ?_, fun c'' hc'' => ?_⟩
              · intro d' s' hd'
                simp only [Option.some.injEq, Prod.mk.injEq] at hd'
                rw [← hd'.1, hd]; exact hdg5 v
              · have hh := Hc_of_le dg hc'' hv
                simp only [List.cons_append, List.nil_append] at hh
                simp [goRootF, h1, hg, hB, hC, hv1 c'' ((hle2.trans hle3).trans hc''), hv2 c'' (hle3.trans hc''), hd, hh]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_pos hB] at h
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs] at h
            obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
            exact ⟨le_rfl, by simp, fun c'' hc'' => by simp [goRootF, h1, hg, hB, hC, hs]⟩
          · simp only [hs] at h
            obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind h
            obtain ⟨hle1, hlen1, hv1⟩ := ih _ _ _ _ _ _ _ hr1
            rcases r1 with _ | ⟨l, s1⟩
            · simp only at h2
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h2
              exact ⟨hle1, by simp, fun c'' hc'' => by simp [goRootF, h1, hg, hB, hC, hs, hv1 c'' hc'']⟩
            · simp only at h2
              obtain ⟨d, c3, hr3, h4⟩ := Runs_bind h2
              obtain ⟨hle3, v, hv, hd⟩ := Runs_hq' dg hr3
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h4
              refine ⟨hle1.trans hle3, ?_, fun c'' hc'' => ?_⟩
              · intro d' s' hd'
                simp only [Option.some.injEq, Prod.mk.injEq] at hd'
                rw [← hd'.1, hd]; exact hdg5 v
              · have hh := Hc_of_le dg hc'' hv
                simp only [List.cons_append, List.nil_append] at hh
                simp [goRootF, h1, hg, hB, hC, hs, hv1 c'' (hle3.trans hc''), hd, hh]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_pos hC] at h
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs] at h
            obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
            exact ⟨le_rfl, by simp, fun c'' hc'' => by simp [goRootF, h1, hg, hB, hC, hs]⟩
          · simp only [hs] at h
            obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind h
            obtain ⟨hle1, hlen1, hv1⟩ := ih _ _ _ _ _ _ _ hr1
            rcases r1 with _ | ⟨r, s1⟩
            · simp only at h2
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h2
              exact ⟨hle1, by simp, fun c'' hc'' => by simp [goRootF, h1, hg, hB, hC, hs, hv1 c'' hc'']⟩
            · simp only at h2
              obtain ⟨d, c3, hr3, h4⟩ := Runs_bind h2
              obtain ⟨hle3, v, hv, hd⟩ := Runs_hq' dg hr3
              obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h4
              refine ⟨hle1.trans hle3, ?_, fun c'' hc'' => ?_⟩
              · intro d' s' hd'
                simp only [Option.some.injEq, Prod.mk.injEq] at hd'
                rw [← hd'.1, hd]; exact hdg5 v
              · have hh := Hc_of_le dg hc'' hv
                simp only [List.cons_append, List.nil_append] at hh
                simp [goRootF, h1, hg, hB, hC, hs, hv1 c'' (hle3.trans hc''), hd, hh]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC] at h
          obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ h
          exact ⟨le_rfl, by simp, fun c'' hc'' => by simp [goRootF, h1, hg, hB, hC]⟩

/-! ### 4. binding: an accepted opening that differs from the honest tree forces a collision -/

theorem CacheHasCollision.mono_le {c c' : QueryCache (HS Y)} (h : c ≤ c') (hc : CacheHasCollision c) : CacheHasCollision c' := by
  obtain ⟨t1, t2, u1, u2, hne, h1, h2, he⟩ := hc
  exact ⟨t1, t2, u1, u2, hne, h h1, h h2, he⟩

/-- two hash evaluations with the same output on different inputs are a collision in the final cache -/
theorem hash_eq_or_coll (hdginj : ∀ v w : Y, dg v = dg w → v = w) {xh xv : List ℕ} {c0 ch cV c2 : QueryCache (HS Y)} {dh d : Dg5}
    (hH : Runs (hq dg xh) c0 dh ch) (hV : Runs (hq dg xv) cV d c2) (hle : ch ≤ cV) (heq : d = dh) :
    xv = xh ∨ CacheHasCollision c2 := by
  by_cases hx : xv = xh
  · exact Or.inl hx
  · right
    obtain ⟨_, vh, hvh, hdh⟩ := Runs_hq' dg hH
    obtain ⟨_, vv, hvv, hdv⟩ := Runs_hq' dg hV
    have hle2 : ch ≤ c2 := hle.trans hV.le
    have h1 : c2 xh = some vh := hle2 hvh
    have : vv = vh := hdginj _ _ (by rw [← hdv, ← hdh, heq])
    exact ⟨xv, xh, vv, vh, hx, hvv, h1, heq_of_eq this⟩

theorem node_inj {a b c : ℕ} {l r l' r' : Dg5} (hlen : l.length = l'.length)
    (h : [a, b, c] ++ l ++ r = [a, b, c] ++ l' ++ r') : l = l' ∧ r = r' := by
  simp only [List.append_assoc] at h
  have h2 := List.append_cancel_left h
  exact List.append_inj h2 hlen

theorem sel_of_getElem? {a : Array ℕ} {i x : ℕ} (h : a[i]? = some x) : i < a.size ∧ a[i]! = x := by
  have hi : i < a.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at h
    simp at h
  rw [Array.getElem?_eq_getElem hi] at h
  refine ⟨hi, ?_⟩
  rw [getElem!_pos a i hi]
  exact Option.some.inj h

theorem vk_bind (hdginj : ∀ v w : Y, dg v = dg w → v = w) (hdg5 : ∀ v, (dg v).length = 5)
    (sp : TSpec) (j : ℕ) (sel : Array ℕ) (hl leaf : ℕ → Dg5) (sibs : Array Dg5) (hsel : Sorted sel)
    (hl5 : ∀ lo, (hl lo).length = 5) (hleaf5 : ∀ r, (leaf r).length = 5)
    (hsib5 : ∀ (s : ℕ) (sib : Dg5), sibs[s]? = some sib → sib.length = 5) :
    ∀ (f idx lo cnt s : ℕ) (c0 ch cV c2 : QueryCache (HS Y)) (dh d : Dg5) (s' : ℕ),
      Runs (honG dg sp j hl f idx lo cnt) c0 dh ch → ch ≤ cV →
      Runs (goRootG dg sp j sel leaf sibs f idx lo cnt s) cV (some (d, s')) c2 → d = dh →
      (∃ lo0, lo ≤ lo0 ∧ lo0 < lo + cnt ∧ sel[lb sel lo0]? = some lo0 ∧ leaf (lb sel lo0) ≠ hl lo0) →
      CacheHasCollision c2 := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt s c0 ch cV c2 dh d s' hH hle hV heq hdiff
    simp only [goRootG] at hV
    have := (Runs_pure _ _ _ _ hV).1
    simp at this
  | succ f ih =>
    intro idx lo cnt s c0 ch cV c2 dh d s' hH hle hV heq hdiff
    simp only [goRootG] at hV
    simp only [honG] at hH
    by_cases h1 : cnt == 1
    · exfalso
      simp only [h1, ite_true] at hV hH
      obtain ⟨rfl, rfl⟩ := Runs_pure _ _ _ _ hH
      obtain ⟨hv, rfl⟩ := Runs_pure _ _ _ _ hV
      obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
      have : lo0 = lo := by simp at h1; omega
      subst this
      split at hv
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv
        exact hne (hv.1.symm.trans heq)
      · simp at hv
    · simp only [h1, Bool.false_eq_true, ite_false] at hV hH
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true] at hV
        have := (Runs_pure _ _ _ _ hV).1
        simp at this
      · simp only [hg, Bool.false_eq_true, ite_false] at hV
        obtain ⟨lh, c0a, hhl, hH2⟩ := Runs_bind hH
        obtain ⟨rh, c0b, hhr, hH3⟩ := Runs_bind hH2
        obtain ⟨hle1h, hlenlh, -⟩ := honG_run dg sp j hl hl5 hdg5 _ _ _ _ _ _ _ hhl
        obtain ⟨hle2h, hlenrh, -⟩ := honG_run dg sp j hl hl5 hdg5 _ _ _ _ _ _ _ hhr
        have hchain : c0 ≤ c0a ∧ c0a ≤ c0b ∧ c0b ≤ ch := ⟨hle1h, hle2h, hH3.le⟩
        have hLc : sp.split cnt < cnt := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hg; exact hg.2
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA] at hV
          obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind hV
          rcases r1 with _ | ⟨l, s1⟩
          · have := (Runs_pure _ _ _ _ h2).1; simp at this
          simp only at h2
          obtain ⟨r2, c2v, hr2, h3⟩ := Runs_bind h2
          rcases r2 with _ | ⟨r, s2⟩
          · have := (Runs_pure _ _ _ _ h3).1; simp at this
          simp only at h3
          obtain ⟨dd, c3, hr3, h4⟩ := Runs_bind h3
          obtain ⟨he, rfl⟩ := Runs_pure _ _ _ _ h4
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hle1v, hlenl, -⟩ := goRootG_run dg sp j sel leaf sibs hleaf5 hsib5 hdg5 _ _ _ _ _ _ _ _ hr1
          obtain ⟨hle2v, hlenr, -⟩ := goRootG_run dg sp j sel leaf sibs hleaf5 hsib5 hdg5 _ _ _ _ _ _ _ _ hr2
          have hch : ch ≤ c2v := hle.trans (hle1v.trans hle2v)
          have hmono : c2v ≤ c2 := hr3.le
          rcases hash_eq_or_coll dg hdginj hH3 hr3 hch heq with hx | hcol
          · obtain ⟨hl', hr'⟩ := node_inj ((hlenl l s1 rfl).trans (hlenlh).symm) hx
            subst hl' hr'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            by_cases hlt : lo0 < lo + sp.split cnt
            · exact CacheHasCollision.mono_le (hle2v.trans hmono)
                (ih _ _ _ _ _ _ _ _ _ _ _ hhl (hchain.2.1.trans (hchain.2.2.trans hle)) hr1 rfl ⟨lo0, hlo0, hlt, hs0, hne⟩)
            · exact CacheHasCollision.mono_le hmono
                (ih _ _ _ _ _ _ _ _ _ _ _ hhr (hchain.2.2.trans (hle.trans hle1v)) hr2 rfl ⟨lo0, by omega, by omega, hs0, hne⟩)
          · exact hcol
        · -- left subtree selected, right frontier digest
          have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_pos hB] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs] at hV
            have := (Runs_pure _ _ _ _ hV).1; simp at this
          simp only [hs] at hV
          obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind hV
          rcases r1 with _ | ⟨l, s1⟩
          · have := (Runs_pure _ _ _ _ h2).1; simp at this
          simp only at h2
          obtain ⟨dd, c3, hr3, h4⟩ := Runs_bind h2
          obtain ⟨he, rfl⟩ := Runs_pure _ _ _ _ h4
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hle1v, hlenl, -⟩ := goRootG_run dg sp j sel leaf sibs hleaf5 hsib5 hdg5 _ _ _ _ _ _ _ _ hr1
          have hch : ch ≤ c1 := hle.trans hle1v
          rcases hash_eq_or_coll dg hdginj hH3 hr3 hch heq with hx | hcol
          · obtain ⟨hl', hr'⟩ := node_inj ((hlenl l _ rfl).trans (hlenlh).symm) hx
            subst hl'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            have hlt : lo0 < lo + sp.split cnt := by
              by_contra hge
              push Not at hge
              obtain ⟨hi, he'⟩ := sel_of_getElem? hs0
              have h1' := lb_mono sel hsel hge
              have h2' := lt_lb sel hsel (x := lo + cnt) hi (by rw [he']; omega)
              omega
            exact CacheHasCollision.mono_le hr3.le
              (ih _ _ _ _ _ _ _ _ _ _ _ hhl (hchain.2.1.trans (hchain.2.2.trans hle)) hr1 rfl ⟨lo0, hlo0, hlt, hs0, hne⟩)
          · exact hcol
        · -- right subtree selected, left frontier digest
          have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_pos hC] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs] at hV
            have := (Runs_pure _ _ _ _ hV).1; simp at this
          simp only [hs] at hV
          obtain ⟨r1, c1, hr1, h2⟩ := Runs_bind hV
          rcases r1 with _ | ⟨r, s1⟩
          · have := (Runs_pure _ _ _ _ h2).1; simp at this
          simp only at h2
          obtain ⟨dd, c3, hr3, h4⟩ := Runs_bind h2
          obtain ⟨he, rfl⟩ := Runs_pure _ _ _ _ h4
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hle1v, hlenr, -⟩ := goRootG_run dg sp j sel leaf sibs hleaf5 hsib5 hdg5 _ _ _ _ _ _ _ _ hr1
          have hch : ch ≤ c1 := hle.trans hle1v
          rcases hash_eq_or_coll dg hdginj hH3 hr3 hch heq with hx | hcol
          · obtain ⟨hl', hr'⟩ := node_inj ((hsib5 s sib hs).trans (hlenlh).symm) hx
            subst hr'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            have hge : lo + sp.split cnt ≤ lo0 := by
              by_contra hlt
              push Not at hlt
              obtain ⟨hi, he'⟩ := sel_of_getElem? hs0
              have h1' := lb_mono sel hsel hlo0
              have h2' := lt_lb sel hsel (x := lo + sp.split cnt) hi (by rw [he']; omega)
              omega
            exact CacheHasCollision.mono_le hr3.le
              (ih _ _ _ _ _ _ _ _ _ _ _ hhr (hchain.2.2.trans hle) hr1 rfl ⟨lo0, hge, by omega, hs0, hne⟩)
          · exact hcol
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC] at hV
          have := (Runs_pure _ _ _ _ hV).1; simp at this
end Bridge

/-! ### 5. the spec root is the honest tree of the rag skeleton -/

section SpecRoot

/-- the honest leaf digest at global leaf position `p` (row-major `g * 2F + s * F + r`): the spec word of column rank `r` at FRI index
`g + s * half`, exactly `honestLeaf` of HFixFri's `VKcoll` -/
def hlSpec (X : ExecInst) (F half p : ℕ) : Dg5 :=
  [(specWord X (fixCols X)[(p % (2 * F)) % F]! (p / (2 * F) + ((p % (2 * F)) / F) * half)).toNat, 0, 0, 0, 0]

theorem pos_arith (F g s r : ℕ) (hF : 0 < F) (hs : s < 2) (hr : r < F) :
    (g * (2 * F) + s * F + r) % (2 * F) = s * F + r ∧ ((g * (2 * F) + s * F + r) % (2 * F)) % F = r ∧
    (g * (2 * F) + s * F + r) / (2 * F) = g ∧ ((g * (2 * F) + s * F + r) % (2 * F)) / F = s := by
  have h1 : s * F + r < 2 * F := by nlinarith
  have e : g * (2 * F) + s * F + r = (s * F + r) + (2 * F) * g := by ring
  have h2 : (g * (2 * F) + s * F + r) % (2 * F) = s * F + r := by
    rw [e, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h1
  have h3 : (s * F + r) % F = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hr
  have h4 : (s * F + r) / F = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hF, Nat.div_eq_of_lt hr]; simp
  refine ⟨h2, by rw [h2, h3], ?_, by rw [h2, h4]⟩
  rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * F), Nat.div_eq_of_lt h1]; simp

/-- a column subtree: `specSub` is the honest recursion of the rag skeleton on the leaves of group `g`, side `s` -/
theorem specSub_eq (X : ExecInst) (Hf : HFn) (F half g s : ℕ) (hF : 0 < F) (hs : s < 2) (hFc : (fixCols X).size = F) :
    ∀ (f1 f2 idx cnt lo : ℕ), 1 ≤ cnt → cnt + lo ≤ F → cnt ≤ f1 → cnt ≤ f2 →
      specSub Hf (fun r => specWord X (fixCols X)[r]! (g + s * half)) f1 idx cnt lo =
        honP Hf (ragSpec F half) 0 (hlSpec X F half) f2 idx (g * (2 * F) + s * F + lo) cnt := by
  intro f1
  induction f1 with
  | zero => intro f2 idx cnt lo h1 h2 h3; omega
  | succ f1 ih =>
    intro f2 idx cnt lo h1 h2 h3 h4
    obtain ⟨f2, rfl⟩ : ∃ f, f2 = f + 1 := ⟨f2 - 1, by omega⟩
    simp only [specSub, honP]
    by_cases hc : cnt == 1
    · simp only [hc, ite_true]
      have hc1 : cnt = 1 := by simpa using hc
      subst hc1
      simp only [hlSpec]
      obtain ⟨-, a1, a2, a3⟩ := pos_arith F g s lo hF hs (by omega)
      rw [a1, a2, a3]
    · simp only [hc, Bool.false_eq_true, ite_false]
      have hc2 : 2 ≤ cnt := by simp at hc; omega
      have hsp : (ragSpec F half).split cnt = (cnt + 1) / 2 := by
        simp only [ragSpec]
        rw [if_neg (by omega), if_neg (by simp only [beq_iff_eq]; omega)]
      rw [hsp]
      rw [ih f2 (2 * idx) ((cnt + 1) / 2) lo (by omega) (by omega) (by omega) (by omega),
        ih f2 (2 * idx + 1) (cnt - (cnt + 1) / 2) (lo + (cnt + 1) / 2) (by omega) (by omega) (by omega) (by omega)]
      have : g * (2 * F) + s * F + (lo + (cnt + 1) / 2) = g * (2 * F) + s * F + lo + (cnt + 1) / 2 := by ring
      rw [this]

theorem specGroup_eq (X : ExecInst) (Hf : HFn) (F half g : ℕ) (hF : 0 < F) (hFc : (fixCols X).size = F) (f : ℕ) (hf : 2 * F ≤ f) :
    specGroup X Hf (fixCols X) half g = honP Hf (ragSpec F half) 0 (hlSpec X F half) f (half + g) (g * (2 * F)) (2 * F) := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hc : ¬ (2 * F == 1) = true := by simp only [beq_iff_eq]; omega
  have hsp : (ragSpec F half).split (2 * F) = F := by
    simp only [ragSpec]
    rw [if_neg (by omega), if_pos (by simp)]
  have e0 := specSub_eq X Hf F half g 0 hF (by omega) hFc F f (2 * (half + g)) F 0 (by omega) (by omega) (by omega) (by omega)
  have e1 := specSub_eq X Hf F half g 1 hF (by omega) hFc F f (2 * (half + g) + 1) F 0 (by omega) (by omega) (by omega) (by omega)
  have h2F : 2 * F - F = F := by omega
  simp only [honP, hc, Bool.false_eq_true, ite_false, hsp, h2F]
  unfold specGroup
  simp only [zero_mul, add_zero, one_mul, hFc] at e0 e1 ⊢
  rw [e0, e1]

/-- the top tree: heap node `2^a + k` at `e` levels above the group level covers `U e = 2F * 2^e` leaves from `k * U e` -/
theorem specTop_eq (X : ExecInst) (Hf : HFn) (F m : ℕ) (hF : 0 < F) (hFc : (fixCols X).size = F) :
    ∀ (e a k f : ℕ), a + e = m → 2 * F * 2 ^ e ≤ f →
      specTop Hf (specGroup X Hf (fixCols X) (2 ^ m)) m e (2 ^ a + k) =
        honP Hf (ragSpec F (2 ^ m)) 0 (hlSpec X F (2 ^ m)) f (2 ^ a + k) (k * (2 * F * 2 ^ e)) (2 * F * 2 ^ e) := by
  intro e
  induction e with
  | zero =>
    intro a k f ha hf
    have : a = m := by omega
    subst this
    simp only [specTop, Nat.add_sub_cancel_left, pow_zero, mul_one]
    exact specGroup_eq X Hf F (2 ^ a) k hF hFc f (by omega)
  | succ e ih =>
    intro a k f ha hf
    have hpos' : 0 < 2 * F * 2 ^ (e + 1) := by positivity
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hU : 2 * F * 2 ^ (e + 1) = 2 * (2 * F * 2 ^ e) := by ring
    have hpos : 0 < 2 * F * 2 ^ e := by positivity
    have hc : ¬ (2 * (2 * F * 2 ^ e) == 1) = true := by simp only [beq_iff_eq]; omega
    have hge : 2 * F ≤ 2 * F * 2 ^ e := Nat.le_mul_of_pos_right _ (by positivity)
    have hsp : (ragSpec F (2 ^ m)).split (2 * (2 * F * 2 ^ e)) = 2 * F * 2 ^ e := by
      simp only [ragSpec]
      rw [if_pos (by omega)]; omega
    rw [hU] at hf ⊢
    simp only [specTop, honP, hc, Bool.false_eq_true, ite_false, hsp]
    have i1 := ih (a + 1) (2 * k) f (by omega) (by omega)
    have i2 := ih (a + 1) (2 * k + 1) f (by omega) (by omega)
    have p1 : 2 ^ (a + 1) + 2 * k = 2 * (2 ^ a + k) := by ring
    have p2 : 2 ^ (a + 1) + (2 * k + 1) = 2 * (2 ^ a + k) + 1 := by ring
    rw [p1] at i1
    rw [p2] at i2
    rw [i1, i2]
    have q1 : 2 * k * (2 * F * 2 ^ e) = k * (2 * (2 * F * 2 ^ e)) := by ring
    have q2 : k * (2 * (2 * F * 2 ^ e)) + 2 * F * 2 ^ e = (2 * k + 1) * (2 * F * 2 ^ e) := by ring
    have q3 : 2 * (2 * F * 2 ^ e) - 2 * F * 2 ^ e = 2 * F * 2 ^ e := by omega
    rw [q3, q1, q2]

/-- **the spec root is the honest tree of the rag skeleton**: `specRoot X Hf = honP` over `ragSpec F 2^(nD-1)` with the spec leaves -/
theorem specRoot_eq (X : ExecInst) (Hf : HFn) (hF : 0 < (fixCols X).size) (f : ℕ)
    (hf : 2 * (fixCols X).size * 2 ^ (X.nD - 1) ≤ f) :
    specRoot X Hf = honP Hf (ragSpec (fixCols X).size (2 ^ (X.nD - 1))) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) f 1 0
      (2 * (fixCols X).size * 2 ^ (X.nD - 1)) := by
  have := specTop_eq X Hf (fixCols X).size (X.nD - 1) hF rfl (X.nD - 1) 0 0 f (by omega) hf
  simpa [specRoot] using this

end SpecRoot

/-! ### 6. query counts -/

section Count
variable {Y : Type} (dg : Y → Dg5)

theorem hq_bound (x : List ℕ) : IsTotalQueryBound (hq dg x) 1 := by
  unfold hq
  rw [map_eq_bind_pure_comp, isTotalQueryBound_query_bind_iff]
  exact ⟨by norm_num, fun u => trivial⟩

theorem honG_bound (sp : TSpec) (hsp : ∀ c, 2 ≤ c → 0 < sp.split c ∧ sp.split c < c) (j : ℕ) (hl : ℕ → Dg5) :
    ∀ (f idx lo cnt : ℕ), 1 ≤ cnt → cnt ≤ f → IsTotalQueryBound (honG dg sp j hl f idx lo cnt) (cnt - 1) := by
  intro f
  induction f with
  | zero => intro idx lo cnt h1 h2; omega
  | succ f ih =>
    intro idx lo cnt h1 h2
    simp only [honG]
    by_cases hc : cnt == 1
    · simp only [hc, ite_true]
      exact (show IsTotalQueryBound (pure (hl lo) : OracleComp (HS Y) Dg5) 0 from trivial).mono (Nat.zero_le _)
    · simp only [hc, Bool.false_eq_true, ite_false]
      have hc2 : 2 ≤ cnt := by simp at hc; omega
      obtain ⟨hs1, hs2⟩ := hsp cnt hc2
      exact (isTotalQueryBound_bind (ih _ lo _ (by omega) (by omega))
        (fun l => isTotalQueryBound_bind (ih _ (lo + sp.split cnt) (cnt - sp.split cnt) (by omega) (by omega))
          (fun r => hq_bound dg _))).mono (by omega)

theorem goRootG_bound (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : ℕ), 1 ≤ cnt → cnt ≤ f → IsTotalQueryBound (goRootG dg sp j sel leaf sibs f idx lo cnt s) (cnt - 1) := by
  intro f
  induction f with
  | zero => intro idx lo cnt s h1 h2; omega
  | succ f ih =>
    intro idx lo cnt s h1 h2
    have hz : ∀ {β : Type} (b : β), IsTotalQueryBound (pure b : OracleComp (HS Y) β) (cnt - 1) :=
      fun b => (show IsTotalQueryBound (pure b : OracleComp (HS Y) _) 0 from trivial).mono (Nat.zero_le _)
    simp only [goRootG]
    by_cases hc : cnt == 1
    · simp only [hc, ite_true]; exact hz _
    · simp only [hc, Bool.false_eq_true, ite_false]
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true]; exact hz _
      · simp only [hg, Bool.false_eq_true, ite_false]
        have hc2 : 2 ≤ cnt := by simp at hc; omega
        have hs1 : 0 < sp.split cnt := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hg; omega
        have hs2 : sp.split cnt < cnt := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hg; omega
        have hL := ih (2 * idx) lo (sp.split cnt) s (by omega) (by omega)
        have hL' := ih (2 * idx) lo (sp.split cnt) (s + 1) (by omega) (by omega)
        have hR' := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) (by omega) (by omega)
        have hp0 : ∀ {β : Type} (b : β), IsTotalQueryBound (pure b : OracleComp (HS Y) β) 0 := fun b => trivial
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA]
          refine (isTotalQueryBound_bind (n₂ := cnt - sp.split cnt) hL (fun r1 => ?_)).mono (by omega)
          rcases r1 with _ | ⟨l, s1⟩
          · exact (hp0 _).mono (Nat.zero_le _)
          · simp only
            refine (isTotalQueryBound_bind (n₁ := cnt - sp.split cnt - 1) (n₂ := 1) (ih _ _ _ _ (by omega) (by omega))
              (fun r2 => ?_)).mono (by omega)
            rcases r2 with _ | ⟨r, s2⟩
            · exact (hp0 _).mono (Nat.zero_le _)
            · simp only
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hq_bound dg _) (fun d => hp0 _)).mono (by omega)
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_pos hB]
          rcases hs : sibs[s]? with _ | sib
          · exact hz _
          · simp only
            refine (isTotalQueryBound_bind (n₂ := 1) hL' (fun r1 => ?_)).mono (by omega)
            rcases r1 with _ | ⟨l, s1⟩
            · exact (hp0 _).mono (Nat.zero_le _)
            · simp only
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hq_bound dg _) (fun d => hp0 _)).mono (by omega)
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_pos hC]
          rcases hs : sibs[s]? with _ | sib
          · exact hz _
          · simp only
            refine (isTotalQueryBound_bind (n₂ := 1) hR' (fun r1 => ?_)).mono (by omega)
            rcases r1 with _ | ⟨r, s1⟩
            · exact (hp0 _).mono (Nat.zero_le _)
            · simp only
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hq_bound dg _) (fun d => hp0 _)).mono (by omega)
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC]
          exact hz _

end Count

theorem ragSpec_split_valid (W half : ℕ) (hW : 0 < W) : ∀ c, 2 ≤ c → 0 < (ragSpec W half).split c ∧ (ragSpec W half).split c < c := by
  intro c hc
  simp only [ragSpec]
  by_cases h1 : c > 2 * W
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : (c == 2 * W) = true
    · rw [if_pos h2]; simp only [beq_iff_eq] at h2; omega
    · rw [if_neg h2]; omega

theorem fixCols_size_pos (X : ExecInst) : 0 < (fixCols X).size := by
  simp [fixCols]

/-! ### 7. the experiment and the probability bound -/

section Final
variable {Y : Type} (dg : Y → Dg5) {P : Type}

/-- the lazy experiment: the honest tree is evaluated first (setup, `T` queries), then the adversary `A` runs (`QA` queries) and produces an
opening `ver p = (sel, leaf, sibs)`, then the verifier recomputes the root (`Vf` queries) -/
noncomputable def vkExp (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) (A : OracleComp (HS Y) P)
    (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5) (f idx lo cnt : ℕ) : OracleComp (HS Y) (Dg5 × P × Option (Dg5 × ℕ)) := do
  let dh ← honG dg sp j hl f idx lo cnt
  let p ← A
  let r ← goRootG dg sp j (ver p).1 (ver p).2.1 (ver p).2.2 f idx lo cnt 0
  pure (dh, p, r)

/-- the structure the verifier's own checks give an opening: sorted selection, 5-limb leaf digests, 5-limb frontier digests -/
def WfOpen (o : Array ℕ × (ℕ → Dg5) × Array Dg5) : Prop :=
  Sorted o.1 ∧ (∀ r, (o.2.1 r).length = 5) ∧ ∀ (s : ℕ) (sib : Dg5), o.2.2[s]? = some sib → sib.length = 5

/-- some opened leaf in `[lo, lo+cnt)` differs from the honest leaf `hl` -/
def WrongLeaf (hl : ℕ → Dg5) (o : Array ℕ × (ℕ → Dg5) × Array Dg5) (lo cnt : ℕ) : Prop :=
  ∃ lo0, lo ≤ lo0 ∧ lo0 < lo + cnt ∧ o.1[lb o.1 lo0]? = some lo0 ∧ o.2.1 (lb o.1 lo0) ≠ hl lo0

theorem vkExp_collision (hdginj : ∀ v w : Y, dg v = dg w → v = w) (hdg5 : ∀ v, (dg v).length = 5)
    (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) (hl5 : ∀ lo, (hl lo).length = 5) (A : OracleComp (HS Y) P)
    (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5) (f idx lo cnt : ℕ)
    (z : (Dg5 × P × Option (Dg5 × ℕ)) × QueryCache (HS Y))
    (hz : z ∈ support ((simulateQ cachingOracle (vkExp dg sp j hl A ver f idx lo cnt)).run ∅))
    (hwf : WfOpen (ver z.1.2.1)) (hacc : ∃ d s', z.1.2.2 = some (d, s') ∧ d = z.1.1)
    (hwrong : WrongLeaf hl (ver z.1.2.1) lo cnt) : CacheHasCollision z.2 := by
  obtain ⟨⟨dh, p, r⟩, c2⟩ := z
  have h : Runs (vkExp dg sp j hl A ver f idx lo cnt) ∅ (dh, p, r) c2 := hz
  unfold vkExp at h
  obtain ⟨dh', ch, hH, h1⟩ := Runs_bind h
  obtain ⟨p', cA, hA, h2⟩ := Runs_bind h1
  obtain ⟨r', cV, hV, h3⟩ := Runs_bind h2
  obtain ⟨he, rfl⟩ := Runs_pure _ _ _ _ h3
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨hs, hl5', hsib⟩ := hwf
  obtain ⟨d, s', hr, hd⟩ := hacc
  simp only at hr hd hs hl5' hsib hwrong
  subst hr
  exact vk_bind dg hdginj hdg5 sp j (ver p).1 hl (ver p).2.1 (ver p).2.2 hs hl5 hl5' hsib f idx lo cnt 0 ∅ ch cA _ dh d s'
    hH hA.le hV hd hwrong

/-- **the birthday bound** (lazy random oracle, `Hf` read off the cache): the probability that the verifier accepts the honest root digest
with an opened leaf different from the honest leaf is at most `(T + QA + Vf)² / (2 |Y|)`, with `T` the honest tree's queries (setup),
`QA` the adversary's, `Vf` the verifier's recomputation -/
theorem vkExp_prob [Fintype Y] [UniformAnswerMeasure (HS Y)] (hdginj : ∀ v w : Y, dg v = dg w → v = w) (hdg5 : ∀ v, (dg v).length = 5)
    (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) (hl5 : ∀ lo, (hl lo).length = 5) (A : OracleComp (HS Y) P)
    (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5) (f idx lo cnt : ℕ) (T QA Vf : ℕ)
    (hT : IsTotalQueryBound (honG dg sp j hl f idx lo cnt) T) (hA : IsTotalQueryBound A QA)
    (hV : ∀ p, IsTotalQueryBound (goRootG dg sp j (ver p).1 (ver p).2.1 (ver p).2.2 f idx lo cnt 0) Vf) :
    Pr{let z ← (simulateQ cachingOracle (vkExp dg sp j hl A ver f idx lo cnt)).run ∅}[
        WfOpen (ver z.1.2.1) ∧ (∃ d s', z.1.2.2 = some (d, s') ∧ d = z.1.1) ∧ WrongLeaf hl (ver z.1.2.1) lo cnt] ≤
      ((T + QA + Vf) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Y : ℝ≥0∞)) := by
  haveI : ∀ t, Fintype ((HS Y).Range t) := fun _ => inferInstanceAs (Fintype Y)
  have hbound : IsTotalQueryBound (vkExp dg sp j hl A ver f idx lo cnt) (T + QA + Vf) := by
    unfold vkExp
    have := isTotalQueryBound_bind hT (fun dh => isTotalQueryBound_bind hA (fun p =>
      isTotalQueryBound_bind (hV p) (fun r => (show IsTotalQueryBound (pure (dh, p, r) : OracleComp (HS Y) _) 0 from trivial))))
    simpa [add_assoc] using this
  have hrange : ∀ t, Fintype.card ((HS Y).Range default) ≤ Fintype.card ((HS Y).Range t) := fun t => le_of_eq (Fintype.card_congr (Equiv.refl Y))
  refine le_trans (prEvent_mono_of_support _ _ (fun z => CacheHasCollision z.2) ?_) ?_
  · intro z hz hev
    exact vkExp_collision dg hdginj hdg5 sp j hl hl5 A ver f idx lo cnt z hz hev.1 hev.2.1 hev.2.2
  · refine (prEvent_cacheCollision_le_birthday_total _ _ hbound hrange).trans (le_of_eq ?_)
    have hc : Fintype.card ((HS Y).Range default) = Fintype.card Y := Fintype.card_congr (Equiv.refl Y)
    rw [hc, Nat.card_eq_fintype_card]
    push_cast
    rfl

end Final

/-! ### 8. against `specRoot`: the pure statement -/

section SpecFinal
variable {Y : Type} (dg : Y → Dg5) {P : Type}

/-- the rag skeleton of the VK tree of `X` -/
abbrev vkSp (X : ExecInst) : TSpec := ragSpec (fixCols X).size (2 ^ (X.nD - 1))

theorem vkSp_total (X : ExecInst) : (vkSp X).total = 2 * (fixCols X).size * 2 ^ (X.nD - 1) := by
  simp only [vkSp, ragSpec]; ring

/-- **`VKcollLazy`**: with `Hf` the hash read off the cache `c`, the pure `goRoot` ACCEPTS the opening `o` against `specRoot X Hf`
(= `(vkSpec X Hf).root`) while an opened leaf differs from the honest leaf `hlSpec` (the spec word of `VKcoll`'s `honestLeaf`) -/
def VKcollLazy (X : ExecInst) (c : QueryCache (HS Y)) (o : Array ℕ × (ℕ → Dg5) × Array Dg5) : Prop :=
  WfOpen o ∧
  (∃ s', goRoot (Hc dg c) (vkSp X) 0 o.1 o.2.1 o.2.2 1 0 (vkSp X).total 0 = some (specRoot X (Hc dg c), s')) ∧
  WrongLeaf (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) o 0 (vkSp X).total

theorem VKcollLazy_bad (hdg5 : ∀ v, (dg v).length = 5) (X : ExecInst) (A : OracleComp (HS Y) P)
    (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5)
    (z : (Dg5 × P × Option (Dg5 × ℕ)) × QueryCache (HS Y))
    (hz : z ∈ support ((simulateQ cachingOracle (vkExp dg (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) A ver
      (vkSp X).total 1 0 (vkSp X).total)).run ∅))
    (hev : VKcollLazy dg X z.2 (ver z.1.2.1)) :
    WfOpen (ver z.1.2.1) ∧ (∃ d s', z.1.2.2 = some (d, s') ∧ d = z.1.1) ∧
      WrongLeaf (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) (ver z.1.2.1) 0 (vkSp X).total := by
  obtain ⟨⟨dh, p, r⟩, c2⟩ := z
  have h : Runs (vkExp dg (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) A ver (vkSp X).total 1 0 (vkSp X).total) ∅ (dh, p, r) c2 := hz
  unfold vkExp at h
  obtain ⟨dh', ch, hH, h1⟩ := Runs_bind h
  obtain ⟨p', cA, hA, h2⟩ := Runs_bind h1
  obtain ⟨r', cV, hV, h3⟩ := Runs_bind h2
  obtain ⟨he, rfl⟩ := Runs_pure _ _ _ _ h3
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨hwf, ⟨s', hacc⟩, hwrong⟩ := hev
  refine ⟨hwf, ?_, hwrong⟩
  obtain ⟨hs, hl5', hsib⟩ := hwf
  have hl5 : ∀ lo, (hlSpec X (fixCols X).size (2 ^ (X.nD - 1)) lo).length = 5 := fun lo => by simp [hlSpec]
  obtain ⟨-, -, hHv⟩ := honG_run dg (vkSp X) 0 _ hl5 hdg5 _ _ _ _ _ _ _ hH
  obtain ⟨-, -, hVv⟩ := goRootG_run dg (vkSp X) 0 _ _ _ hl5' hsib hdg5 _ _ _ _ _ _ _ _ hV
  have hVe := hVv _ le_rfl
  have hHe := hHv _ (hA.le.trans hV.le)
  have hsr := specRoot_eq X (Hc dg c2) (fixCols_size_pos X) (vkSp X).total (by rw [vkSp_total])
  rw [← vkSp_total X] at hsr
  unfold goRoot at hacc
  refine ⟨specRoot X (Hc dg c2), s', hVe.symm.trans hacc, ?_⟩
  rw [hsr, hHe]

set_option maxHeartbeats 4000000 in
/-- **`hcoll`, lazy model**: `Pr[VKcollLazy] ≤ (T + QA + Vf)² / (2 |Y|)`, with `T` the honest-tree (setup) queries, `QA` the adversary's, `Vf`
the verifier's recomputation. -/
theorem vkcoll_prob [Fintype Y] [UniformAnswerMeasure (HS Y)] (hdginj : ∀ v w : Y, dg v = dg w → v = w) (hdg5 : ∀ v, (dg v).length = 5)
    (X : ExecInst) (A : OracleComp (HS Y) P) (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5) (T QA Vf : ℕ)
    (hT : IsTotalQueryBound (honG dg (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) (vkSp X).total 1 0 (vkSp X).total) T)
    (hA : IsTotalQueryBound A QA)
    (hV : ∀ p, IsTotalQueryBound (goRootG dg (vkSp X) 0 (ver p).1 (ver p).2.1 (ver p).2.2 (vkSp X).total 1 0 (vkSp X).total 0) Vf) :
    Pr{let z ← (simulateQ cachingOracle (vkExp dg (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) A ver
        (vkSp X).total 1 0 (vkSp X).total)).run ∅}[VKcollLazy dg X z.2 (ver z.1.2.1)] ≤
      ((T + QA + Vf) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Y : ℝ≥0∞)) := by
  have hl5 : ∀ lo, (hlSpec X (fixCols X).size (2 ^ (X.nD - 1)) lo).length = 5 := fun lo => by simp [hlSpec]
  have key := vkExp_prob dg hdginj hdg5 (vkSp X) 0 _ hl5 A ver (vkSp X).total 1 0 (vkSp X).total T QA Vf hT hA hV
  exact le_trans (prEvent_mono_of_support _ _ _ (fun z hz hev => VKcollLazy_bad dg hdg5 X A ver z hz hev)) key

/-- with `T = Vf = total - 1` (every tree node hashed at most once per pass): no query-count hypothesis but the adversary's `QA` -/
theorem vkcoll_prob_tot [Fintype Y] [UniformAnswerMeasure (HS Y)] (hdginj : ∀ v w : Y, dg v = dg w → v = w)
    (hdg5 : ∀ v, (dg v).length = 5)
    (X : ExecInst) (A : OracleComp (HS Y) P) (ver : P → Array ℕ × (ℕ → Dg5) × Array Dg5) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← (simulateQ cachingOracle (vkExp dg (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1))) A ver
        (vkSp X).total 1 0 (vkSp X).total)).run ∅}[VKcollLazy dg X z.2 (ver z.1.2.1)] ≤
      (((((vkSp X).total - 1 : ℕ) : ℝ≥0∞) + QA + (((vkSp X).total - 1 : ℕ) : ℝ≥0∞)) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Y : ℝ≥0∞)) := by
  have hF := fixCols_size_pos X
  have h2 : 2 ≤ (vkSp X).total := by
    rw [vkSp_total]
    have : 1 ≤ 2 ^ (X.nD - 1) := Nat.one_le_two_pow
    nlinarith
  refine vkcoll_prob dg hdginj hdg5 X A ver ((vkSp X).total - 1) QA ((vkSp X).total - 1) ?_ hA (fun p => ?_)
  · exact honG_bound dg (vkSp X) (ragSpec_split_valid _ _ hF) 0 _ _ 1 0 _ (by omega) le_rfl
  · exact goRootG_bound dg _ 0 _ _ _ _ 1 0 _ 0 (by omega) le_rfl

end SpecFinal

/-! ### 9. instantiating examples -/

section Examples

/-- the digest model of the audited stack (5 limbs of `ZMod N`; `N = p` at J-8): `dg` reads the canonical limbs out -/
def dgN (N : ℕ) : (Fin 5 → ZMod N) → Dg5 := fun v => List.ofFn fun i => (v i).val

theorem dgN_len (N : ℕ) (v : Fin 5 → ZMod N) : (dgN N v).length = 5 := by simp [dgN]

theorem dgN_inj (N : ℕ) [NeZero N] (v w : Fin 5 → ZMod N) (h : dgN N v = dgN N w) : v = w := by
  funext i
  have := congrArg (fun l => l[i.1]?) h
  simp only [dgN, List.getElem?_ofFn] at this
  simp only [Fin.is_lt, getElem?_pos, List.getElem_ofFn] at this
  exact ZMod.val_injective N (by simpa using this)

/-- a wrong leaf is satisfiable and well-formed: single leaf, claimed `[1,0,0,0,0]`, honest `[0,0,0,0,0]` -/
example : WfOpen ((#[0] : Array ℕ), (fun _ => [1, 0, 0, 0, 0]), (#[] : Array Dg5)) ∧
    WrongLeaf (fun _ => [0, 0, 0, 0, 0]) ((#[0] : Array ℕ), (fun _ => [1, 0, 0, 0, 0]), (#[] : Array Dg5)) 0 1 := by
  refine ⟨⟨?_, fun _ => rfl, fun s sib h => by simp at h⟩, 0, le_rfl, by omega, ?_, ?_⟩
  · intro i j hij hj; simp at hj; have : i = 0 := by omega
    subst this; have : j = 0 := by omega
    subst this; exact le_rfl
  · simp [lb, lbGo]
  · simp [lb, lbGo]

set_option maxHeartbeats 4000000 in
/-- the whole statement at the audited digest model, for an adversary that makes no queries and an empty opening:
every hypothesis (`hdginj`, `hdg5`, the instances) is instantiated -/
theorem vkcoll_prob_example (N : ℕ) [NeZero N] (X : ExecInst) :
    haveI : UniformAnswerMeasure (HS (Fin 5 → ZMod N)) := UniformAnswerMeasure.ofFiniteNonempty _
    Pr{let z ← (simulateQ cachingOracle (vkExp (dgN N) (vkSp X) 0 (hlSpec X (fixCols X).size (2 ^ (X.nD - 1)))
        (pure () : OracleComp (HS (Fin 5 → ZMod N)) Unit) (fun _ => ((#[] : Array ℕ), (fun _ => [0, 0, 0, 0, 0]), (#[] : Array Dg5)))
        (vkSp X).total 1 0 (vkSp X).total)).run ∅}[VKcollLazy (dgN N) X z.2 (#[], (fun _ => [0, 0, 0, 0, 0]), #[])] ≤
      (((((vkSp X).total - 1 : ℕ) : ℝ≥0∞) + (0 : ℕ) + (((vkSp X).total - 1 : ℕ) : ℝ≥0∞)) ^ 2 : ℝ≥0∞) / (2 * (Nat.card (Fin 5 → ZMod N) : ℝ≥0∞)) := by
  letI : UniformAnswerMeasure (HS (Fin 5 → ZMod N)) := UniformAnswerMeasure.ofFiniteNonempty _
  exact vkcoll_prob_tot (dgN N) (dgN_inj N) (dgN_len N) X (pure ())
    (fun _ => ((#[] : Array ℕ), (fun _ => [0, 0, 0, 0, 0]), (#[] : Array Dg5))) 0 trivial

end Examples

end NockvmE2E.Exec.VKBind

#print axioms NockvmE2E.Exec.VKBind.lb_spec
#print axioms NockvmE2E.Exec.VKBind.honG_run
#print axioms NockvmE2E.Exec.VKBind.goRootG_run
#print axioms NockvmE2E.Exec.VKBind.vk_bind
#print axioms NockvmE2E.Exec.VKBind.specRoot_eq
#print axioms NockvmE2E.Exec.VKBind.vkExp_collision
#print axioms NockvmE2E.Exec.VKBind.vkExp_prob
#print axioms NockvmE2E.Exec.VKBind.VKcollLazy_bad
#print axioms NockvmE2E.Exec.VKBind.vkcoll_prob
#print axioms NockvmE2E.Exec.VKBind.vkcoll_prob_tot
#print axioms NockvmE2E.Exec.VKBind.vkcoll_prob_example
