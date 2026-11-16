import NockvmE2E.Exec.LazyColl
import NockvmE2E.Exec.VKBindBridge

/-!  the deterministic part of `hcoll`.  The VK-tree honest recomputation and the verifier recomputation as hash-only programs
over the node oracle `NQuery skels →ₒ DgJ8` (port of `VKBind.honG` / `goRootG` with `hq dg` replaced by `hqN skels`), their recorded runs
`tabRun`, and the binding argument `vk_bind_tab` (port of `VKBind.vk_bind`) producing a `TraceColl`. -/

open OracleComp OracleSpec ENNReal BinaryTree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.VKTrace
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Exec.VKBind NockvmE2E.Exec.VKBindBridge NockvmE2E.Exec.LazyColl

/-- the node-query oracle of the side trees -/
abbrev HN (skels : List Skeleton) := (NQuery skels →ₒ DgJ8)

def skelVK (XX : ExecInst) : Skeleton := skelOf (vkSp XX) (vkSp XX).total (vkSp XX).total

/-- one hash evaluation: decode the flat input to a node query (zero digest off the image, as `Hof`) -/
def hqN (skels : List Skeleton) (x : List ℕ) : OracleComp (HN skels) Dg5 :=
  match decQ skels x with
  | some q => (liftM ((HN skels).query q) : OracleComp (HN skels) DgJ8) >>= fun v => pure (dgFlat v)
  | none => pure dgZero

def honN (skels : List Skeleton) (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) : ℕ → ℕ → ℕ → ℕ → OracleComp (HN skels) Dg5
  | 0, _, _, _ => pure [0, 0, 0, 0, 0]
  | f + 1, idx, lo, cnt =>
    if cnt == 1 then pure (hl lo) else do
      let l ← honN skels sp j hl f (2 * idx) lo (sp.split cnt)
      let r ← honN skels sp j hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt)
      hqN skels ([tagNode, j, idx] ++ l ++ r)

def goRootN (skels : List Skeleton) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5) :
    ℕ → ℕ → ℕ → ℕ → ℕ → OracleComp (HN skels) (Option (Dg5 × ℕ))
  | 0, _, _, _, _ => pure none
  | f + 1, idx, lo, cnt, s =>
    if cnt == 1 then
      pure (if sel[lb sel lo]? == some lo then some (leaf (lb sel lo), s) else none)
    else if sp.split cnt == 0 || decide (sp.split cnt ≥ cnt) then pure none
    else
      if lb sel (lo + sp.split cnt) > lb sel lo && lb sel (lo + cnt) > lb sel (lo + sp.split cnt) then do
        let r1 ← goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s
        match r1 with
        | none => pure none
        | some (l, s1) => do
          let r2 ← goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1
          match r2 with
          | none => pure none
          | some (r, s2) => do
            let d ← hqN skels ([tagNode, j, idx] ++ l ++ r)
            pure (some (d, s2))
      else if lb sel (lo + sp.split cnt) > lb sel lo then
        match sibs[s]? with
        | none => pure none
        | some sib => do
          let r1 ← goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)
          match r1 with
          | none => pure none
          | some (l, s1) => do
            let d ← hqN skels ([tagNode, j, idx] ++ l ++ sib)
            pure (some (d, s1))
      else if lb sel (lo + cnt) > lb sel (lo + sp.split cnt) then
        match sibs[s]? with
        | none => pure none
        | some sib => do
          let r1 ← goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)
          match r1 with
          | none => pure none
          | some (r, s1) => do
            let d ← hqN skels ([tagNode, j, idx] ++ sib ++ r)
            pure (some (d, s1))
      else pure none

def vkProg (XX : ExecInst) (skels : List Skeleton) (πF : FixProof) : OracleComp (HN skels) (Dg5 × Option (Dg5 × ℕ)) := do
  let dh ← honN skels (vkSp XX) 0 (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1))) (vkSp XX).total 1 0 (vkSp XX).total
  let r ← goRootN skels (vkSp XX) 0 (openV XX πF).1 (openV XX πF).2.1 (openV XX πF).2.2 (vkSp XX).total 1 0 (vkSp XX).total 0
  pure (dh, r)

/-! ### recorded runs of the pieces -/

section Tab
variable {QQ YY : Type} {β : Type}

theorem tabRun_pure (h : QQ → YY) (a : β) (L : List (QQ × YY)) : tabRun h (pure a : OracleComp (QQ →ₒ YY) β) L = (a, L) := by
  simp [tabRun]; rfl

theorem tabRun_bind {α : Type} (h : QQ → YY) (x : OracleComp (QQ →ₒ YY) α) (f : α → OracleComp (QQ →ₒ YY) β) (L : List (QQ × YY)) :
    tabRun h (x >>= f) L = tabRun h (f (tabRun h x L).1) (tabRun h x L).2 := by
  simp [tabRun, simulateQ_bind, StateT.run_bind]; rfl

theorem tabRun_query_bind (h : QQ → YY) (q : QQ) (k : YY → OracleComp (QQ →ₒ YY) β) (L : List (QQ × YY)) :
    tabRun h (liftM ((QQ →ₒ YY).query q) >>= k) L = tabRun h (k (h q)) (L ++ [(q, h q)]) := by
  simp [tabRun, tabImpl, StateT.run_bind, simulateQ_bind]

end Tab

theorem tabRun_hqN_some (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ) (q : NQuery skels)
    (hq : decQ skels x = some q) (L : List (NQuery skels × DgJ8)) :
    tabRun h (hqN skels x) L = (dgFlat (h q), L ++ [(q, h q)]) := by
  simp only [hqN, hq]
  rw [tabRun_query_bind, tabRun_pure]

theorem tabRun_hqN_none (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ)
    (hq : decQ skels x = none) (L : List (NQuery skels × DgJ8)) :
    tabRun h (hqN skels x) L = (dgZero, L) := by
  simp only [hqN, hq]
  rw [tabRun_pure]

theorem dgOk_dgZero : dgOk dgZero = true := by decide +kernel

theorem hqN_run (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ) (L : List (NQuery skels × DgJ8)) :
    dgOk (tabRun h (hqN skels x) L).1 = true ∧ ∃ L', (tabRun h (hqN skels x) L).2 = L ++ L' := by
  rcases hd : decQ skels x with _ | q
  · rw [tabRun_hqN_none _ _ _ hd]; exact ⟨dgOk_dgZero, [], by simp⟩
  · rw [tabRun_hqN_some _ _ _ _ hd]; exact ⟨dgOk_dgFlat _, [(q, h q)], rfl⟩

theorem hqN_bound (skels : List Skeleton) (x : List ℕ) : IsTotalQueryBound (hqN skels x) 1 := by
  unfold hqN
  split
  · rw [isTotalQueryBound_query_bind_iff]; exact ⟨by norm_num, fun u => trivial⟩
  · exact (show IsTotalQueryBound (pure dgZero : OracleComp (HN skels) Dg5) 0 from trivial).mono (Nat.zero_le _)

theorem honN_run (skels : List Skeleton) (h : NQuery skels → DgJ8) (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5)
    (hl5 : ∀ lo, dgOk (hl lo) = true) :
    ∀ (f idx lo cnt : ℕ) (L : List (NQuery skels × DgJ8)),
      dgOk (tabRun h (honN skels sp j hl f idx lo cnt) L).1 = true ∧ ∃ L', (tabRun h (honN skels sp j hl f idx lo cnt) L).2 = L ++ L' := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt L
    simp only [honN, tabRun_pure]
    exact ⟨dgOk_dgZero, [], by simp⟩
  | succ f ih =>
    intro idx lo cnt L
    simp only [honN]
    by_cases hc : cnt == 1
    · simp only [hc, ite_true, tabRun_pure]; exact ⟨hl5 lo, [], by simp⟩
    · simp only [hc, Bool.false_eq_true, ite_false, tabRun_bind]
      obtain ⟨-, L1, e1⟩ := ih (2 * idx) lo (sp.split cnt) L
      obtain ⟨-, L2, e2⟩ := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt)
        (tabRun h (honN skels sp j hl f (2 * idx) lo (sp.split cnt)) L).2
      obtain ⟨hok, L3, e3⟩ := hqN_run skels h ([tagNode, j, idx] ++
        (tabRun h (honN skels sp j hl f (2 * idx) lo (sp.split cnt)) L).1 ++
        (tabRun h (honN skels sp j hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt)) (tabRun h (honN skels sp j hl f (2 * idx) lo (sp.split cnt)) L).2).1)
        (tabRun h (honN skels sp j hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt))
          (tabRun h (honN skels sp j hl f (2 * idx) lo (sp.split cnt)) L).2).2
      refine ⟨hok, L1 ++ L2 ++ L3, ?_⟩
      rw [e3, e2, e1]; simp [List.append_assoc]

theorem goRootN_run (skels : List Skeleton) (h : NQuery skels → DgJ8) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5)
    (hleaf5 : ∀ r, dgOk (leaf r) = true) (hsib5 : ∀ (s : ℕ) (sib : Dg5), sibs[s]? = some sib → dgOk sib = true) :
    ∀ (f idx lo cnt s : ℕ) (L L2 : List (NQuery skels × DgJ8)) (d : Dg5) (s' : ℕ),
      tabRun h (goRootN skels sp j sel leaf sibs f idx lo cnt s) L = (some (d, s'), L2) →
      dgOk d = true ∧ ∃ L', L2 = L ++ L' := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt s L L2 d s' hV
    simp only [goRootN, tabRun_pure] at hV
    simp at hV
  | succ f ih =>
    intro idx lo cnt s L L2 d s' hV
    simp only [goRootN] at hV
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true, tabRun_pure] at hV
      split at hV
      · simp only [Option.some.injEq, Prod.mk.injEq] at hV
        obtain ⟨⟨rfl, -⟩, rfl⟩ := hV
        exact ⟨hleaf5 _, [], by simp⟩
      · simp at hV
    · simp only [h1, Bool.false_eq_true, ite_false] at hV
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true, tabRun_pure] at hV; simp at hV
      · simp only [hg, Bool.false_eq_true, ite_false] at hV
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA] at hV
          simp only [tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s) L with ⟨r1, L1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨l, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind] at hV
          rcases hr2 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1) L1 with ⟨r2, L2'⟩
          rw [hr2] at hV
          rcases r2 with _ | ⟨r, s2⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨-, a1, e1⟩ := ih _ _ _ _ _ _ _ _ hr1
          obtain ⟨-, a2, e2⟩ := ih _ _ _ _ _ _ _ _ hr2
          obtain ⟨hok, a3, e3⟩ := hqN_run skels h ([tagNode, j, idx] ++ l ++ r) L2'
          simp only [Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨rfl, -⟩, rfl⟩ := hV
          exact ⟨hok, a1 ++ a2 ++ a3, by rw [e3, e2, e1]; simp [List.append_assoc]⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_pos hB] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs, tabRun_pure] at hV; simp at hV
          simp only [hs, tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨l, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨-, a1, e1⟩ := ih _ _ _ _ _ _ _ _ hr1
          obtain ⟨hok, a3, e3⟩ := hqN_run skels h ([tagNode, j, idx] ++ l ++ sib) L1
          simp only [Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨rfl, -⟩, rfl⟩ := hV
          exact ⟨hok, a1 ++ a3, by rw [e3, e1]; simp [List.append_assoc]⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_pos hC] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs, tabRun_pure] at hV; simp at hV
          simp only [hs, tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨r, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨-, a1, e1⟩ := ih _ _ _ _ _ _ _ _ hr1
          obtain ⟨hok, a3, e3⟩ := hqN_run skels h ([tagNode, j, idx] ++ sib ++ r) L1
          simp only [Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨rfl, -⟩, rfl⟩ := hV
          exact ⟨hok, a1 ++ a3, by rw [e3, e1]; simp [List.append_assoc]⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC] at hV
          simp only [tabRun_pure] at hV; simp at hV

/-! ### decoding of VK-tree node inputs -/

/-- heap numbers of the internal nodes of a skeleton rooted at heap number `idx` -/
def heapSet : Skeleton → ℕ → List ℕ
  | .leaf, _ => []
  | .internal l r, idx => idx :: (heapSet l (2 * idx) ++ heapSet r (2 * idx + 1))

theorem exists_of_mem_heapSet : ∀ (s : Skeleton) (idx i : ℕ), i ∈ heapSet s idx → ∃ a : SkeletonInternalIndex s, heapIdx a idx = i
  | .leaf, _, _, h => by simp [heapSet] at h
  | .internal l r, idx, i, h => by
    simp only [heapSet, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact ⟨.ofInternal, rfl⟩
    · obtain ⟨a, ha⟩ := exists_of_mem_heapSet l _ _ h
      exact ⟨.ofLeft a, ha⟩
    · obtain ⟨a, ha⟩ := exists_of_mem_heapSet r _ _ h
      exact ⟨.ofRight a, ha⟩

theorem heapSet_succ (sp : TSpec) (f idx cnt : ℕ) (h1 : ¬ (cnt == 1) = true) :
    heapSet (skelOf sp (f + 1) cnt) idx =
      idx :: (heapSet (skelOf sp f (sp.split cnt)) (2 * idx) ++ heapSet (skelOf sp f (cnt - sp.split cnt)) (2 * idx + 1)) := by
  simp [skelOf, h1, heapSet]

theorem decQ_node (skels : List Skeleton) (h0 : 0 < skels.length) (a : SkeletonInternalIndex (skels.get ⟨0, h0⟩))
    (l r : List ℕ) (hl : l.length = 5) :
    decQ skels ([tagNode, 0, heapIdx a 1] ++ l ++ r) = some (⟨⟨0, h0⟩, a⟩, (dgOf l, dgOf r)) := by
  have hf : (allIdx (skels.get ⟨0, h0⟩)).find? (fun b => heapIdx b 1 == heapIdx a 1) = some a :=
    find_uniq _ a (by simp) (fun b hb => heapIdx_inj b a (by simpa using hb)) _ (mem_allIdx a)
  have h1 : (l ++ r).take 5 = l := List.take_left' hl
  have h2 : (l ++ r).drop 5 = r := List.drop_left' hl
  simp only [decQ, List.cons_append, List.nil_append, List.append_assoc, h1, h2, hf, h0]
  rfl

theorem dgFlat_dgOf (l : List ℕ) (h : dgOk l = true) : dgFlat (dgOf l) = l := by
  simp only [dgOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, VF.based, decide_eq_true_eq] at h
  obtain ⟨hlen, hc⟩ := h
  apply List.ext_getElem (by simp [dgFlat, hlen])
  intro i h1 h2
  simp only [dgFlat, List.getElem_ofFn, dgOf]
  have hi : i < l.length := h2
  rw [List.getD_eq_getElem _ _ hi, ZMod.val_natCast]
  have := hc _ (List.getElem_mem hi)
  have hPN := PN_eq
  exact Nat.mod_eq_of_lt (by omega)

theorem dgOk_len {l : List ℕ} (h : dgOk l = true) : l.length = 5 := by
  simp only [dgOk, Bool.and_eq_true, beq_iff_eq] at h; exact h.1

theorem node_step (skels : List Skeleton) (h0 : 0 < skels.length) (idx : ℕ)
    (hi : idx ∈ heapSet (skels.get ⟨0, h0⟩) 1) (lh rh l r : List ℕ)
    (hlh : dgOk lh = true) (hrh : dgOk rh = true) (hl : dgOk l = true) (hr : dgOk r = true) :
    ∃ qh qv : NQuery skels, decQ skels ([tagNode, 0, idx] ++ lh ++ rh) = some qh ∧
      decQ skels ([tagNode, 0, idx] ++ l ++ r) = some qv ∧ (qv = qh → l = lh ∧ r = rh) := by
  obtain ⟨a, ha⟩ := exists_of_mem_heapSet _ _ _ hi
  subst ha
  refine ⟨_, _, decQ_node skels h0 a lh rh (dgOk_len hlh), decQ_node skels h0 a l r (dgOk_len hl), fun hq => ?_⟩
  have hq2 : (dgOf l, dgOf r) = (dgOf lh, dgOf rh) := congrArg Prod.snd hq
  simp only [Prod.mk.injEq] at hq2
  obtain ⟨hl', hr'⟩ := hq2
  refine ⟨?_, ?_⟩
  · calc l = dgFlat (dgOf l) := (dgFlat_dgOf l hl).symm
      _ = dgFlat (dgOf lh) := by rw [hl']
      _ = lh := dgFlat_dgOf lh hlh
  · calc r = dgFlat (dgOf r) := (dgFlat_dgOf r hr).symm
      _ = dgFlat (dgOf rh) := by rw [hr']
      _ = rh := dgFlat_dgOf rh hrh

theorem TraceColl_mono {QQ YY : Type} {L L' : List (QQ × YY)} (hsub : ∀ p ∈ L, p ∈ L') :
    TraceColl L → TraceColl L' := fun ⟨p1, h1, p2, h2, hne, he⟩ => ⟨p1, hsub _ h1, p2, hsub _ h2, hne, he⟩

/-! ### binding: an accepted opening that differs from the honest tree forces a trace collision -/

theorem vk_bind_tab (skels : List Skeleton) (h0 : 0 < skels.length) (h : NQuery skels → DgJ8) (sp : TSpec)
    (sel : Array ℕ) (hl leaf : ℕ → Dg5) (sibs : Array Dg5) (hsel : Sorted sel)
    (hl5 : ∀ lo, dgOk (hl lo) = true) (hleaf5 : ∀ r, dgOk (leaf r) = true)
    (hsib5 : ∀ (s : ℕ) (sib : Dg5), sibs[s]? = some sib → dgOk sib = true) :
    ∀ (f idx lo cnt s : ℕ) (L0 Lv L2 : List (NQuery skels × DgJ8)) (d : Dg5) (s' : ℕ),
      (∀ i ∈ heapSet (skelOf sp f cnt) idx, i ∈ heapSet (skels.get ⟨0, h0⟩) 1) →
      (∀ p ∈ (tabRun h (honN skels sp 0 hl f idx lo cnt) L0).2, p ∈ Lv) →
      tabRun h (goRootN skels sp 0 sel leaf sibs f idx lo cnt s) Lv = (some (d, s'), L2) →
      d = (tabRun h (honN skels sp 0 hl f idx lo cnt) L0).1 →
      (∃ lo0, lo ≤ lo0 ∧ lo0 < lo + cnt ∧ sel[lb sel lo0]? = some lo0 ∧ leaf (lb sel lo0) ≠ hl lo0) →
      TraceColl L2 := by
  intro f
  induction f with
  | zero =>
    intro idx lo cnt s L0 Lv L2 d s' _ _ hV _ _
    simp only [goRootN, tabRun_pure] at hV
    simp at hV
  | succ f ih =>
    intro idx lo cnt s L0 Lv L2 d s' hemb hle hV heq hdiff
    simp only [goRootN] at hV
    simp only [honN] at hle
    simp only [honN] at heq
    by_cases h1 : cnt == 1
    · exfalso
      simp only [h1, ite_true, tabRun_pure] at hV
      simp only [h1, ite_true, tabRun_pure] at heq
      obtain ⟨hv1, -⟩ := Prod.mk.inj hV
      obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
      have : lo0 = lo := by simp at h1; omega
      subst this
      split at hv1
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv1
        first | exact hne (hv1.1.trans heq) | exact hne (hv1.1.symm.trans heq)
      · simp at hv1
    · simp only [h1, Bool.false_eq_true, ite_false] at hV
      simp only [h1, Bool.false_eq_true, ite_false] at hle
      simp only [h1, Bool.false_eq_true, ite_false] at heq
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true, tabRun_pure] at hV; simp at hV
      · simp only [hg, Bool.false_eq_true, ite_false] at hV
        have hLc : sp.split cnt < cnt := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_le] at hg; exact hg.2
        have hsucc := heapSet_succ sp f idx cnt h1
        rw [hsucc] at hemb
        have hidx : idx ∈ heapSet (skels.get ⟨0, h0⟩) 1 := hemb idx (List.mem_cons_self ..)
        have hembL : ∀ i ∈ heapSet (skelOf sp f (sp.split cnt)) (2 * idx), i ∈ heapSet (skels.get ⟨0, h0⟩) 1 :=
          fun i hi => hemb i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
        have hembR : ∀ i ∈ heapSet (skelOf sp f (cnt - sp.split cnt)) (2 * idx + 1), i ∈ heapSet (skels.get ⟨0, h0⟩) 1 :=
          fun i hi => hemb i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))
        simp only [tabRun_bind] at hle heq
        rcases hHL : tabRun h (honN skels sp 0 hl f (2 * idx) lo (sp.split cnt)) L0 with ⟨lh, Lh1⟩
        rcases hHR : tabRun h (honN skels sp 0 hl f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt)) Lh1 with ⟨rh, Lh2⟩
        simp only [hHL, hHR] at hle heq
        have hrl := honN_run skels h sp 0 hl hl5 f (2 * idx) lo (sp.split cnt) L0
        simp only [hHL] at hrl
        obtain ⟨hlhok, a1, e1⟩ := hrl
        have hrr := honN_run skels h sp 0 hl hl5 f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) Lh1
        simp only [hHR] at hrr
        obtain ⟨hrhok, a2, e2⟩ := hrr
        subst e1 e2
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA] at hV
          simp only [tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp 0 sel leaf sibs f (2 * idx) lo (sp.split cnt) s) Lv with ⟨r1, Lv1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨l, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind] at hV
          rcases hr2 : tabRun h (goRootN skels sp 0 sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1) Lv1 with ⟨r2, Lv2⟩
          rw [hr2] at hV
          rcases r2 with _ | ⟨r, s2⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨hlok, b1, f1⟩ := goRootN_run skels h sp 0 sel leaf sibs hleaf5 hsib5 _ _ _ _ _ _ _ _ _ hr1
          obtain ⟨hrok, b2, f2⟩ := goRootN_run skels h sp 0 sel leaf sibs hleaf5 hsib5 _ _ _ _ _ _ _ _ _ hr2
          subst f1 f2
          obtain ⟨qh, qv, hdh, hdv, hinj⟩ := node_step skels h0 idx hidx lh rh l r hlhok hrhok hlok hrok
          simp only [tabRun_hqN_some skels h _ qh hdh] at hle heq
          simp only [tabRun_hqN_some skels h _ qv hdv, Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨hd, hs⟩, hL2⟩ := hV
          subst hL2
          have hsubL : ∀ p ∈ L0 ++ a1, p ∈ Lv := fun p hp =>
            hle p (by simp only [List.mem_append, List.mem_singleton] at hp ⊢; tauto)
          have hsubR : ∀ p ∈ L0 ++ a1 ++ a2, p ∈ Lv := fun p hp =>
            hle p (by simp only [List.mem_append, List.mem_singleton] at hp ⊢; tauto)
          have hqhm : (qh, h qh) ∈ Lv := hle _ (by simp)
          by_cases hqq : qv = qh
          · obtain ⟨hl', hr'⟩ := hinj hqq
            subst hl' hr'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            by_cases hlt : lo0 < lo + sp.split cnt
            · exact TraceColl_mono (fun p hp => by simp only [List.mem_append] at hp ⊢; tauto)
                (ih (2 * idx) lo (sp.split cnt) s L0 Lv _ _ _ hembL (by rw [hHL]; exact hsubL) hr1 (by rw [hHL])
                  ⟨lo0, hlo0, hlt, hs0, hne⟩)
            · exact TraceColl_mono (fun p hp => by simp only [List.mem_append] at hp ⊢; tauto)
                (ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 (L0 ++ a1) _ _ _ _ hembR
                  (by rw [hHR]; exact fun p hp => List.mem_append_left _ (hsubR p hp)) hr2 (by rw [hHR])
                  ⟨lo0, by omega, by omega, hs0, hne⟩)
          · have hdd : dgFlat (h qv) = dgFlat (h qh) := by
              first | exact hd.trans heq | exact hd.symm.trans heq
            have hvh : h qv = h qh := by
              have := congrArg dgOf hdd
              simpa [dgOf_dgFlat] using this
            exact ⟨(qv, h qv), by simp, (qh, h qh), by simp only [List.mem_append]; tauto, hqq, hvh⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_pos hB] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs, tabRun_pure] at hV; simp at hV
          simp only [hs, tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp 0 sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)) Lv with ⟨r1, Lv1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨l, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨hlok, b1, f1⟩ := goRootN_run skels h sp 0 sel leaf sibs hleaf5 hsib5 _ _ _ _ _ _ _ _ _ hr1
          subst f1
          obtain ⟨qh, qv, hdh, hdv, hinj⟩ := node_step skels h0 idx hidx lh rh l sib hlhok hrhok hlok (hsib5 s sib hs)
          simp only [tabRun_hqN_some skels h _ qh hdh] at hle heq
          simp only [tabRun_hqN_some skels h _ qv hdv, Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨hd, hs2⟩, hL2⟩ := hV
          subst hL2
          have hsubL : ∀ p ∈ L0 ++ a1, p ∈ Lv := fun p hp =>
            hle p (by simp only [List.mem_append, List.mem_singleton] at hp ⊢; tauto)
          have hqhm : (qh, h qh) ∈ Lv := hle _ (by simp)
          by_cases hqq : qv = qh
          · obtain ⟨hl', hr'⟩ := hinj hqq
            subst hl'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            have hlt : lo0 < lo + sp.split cnt := by
              by_contra hge
              push Not at hge
              obtain ⟨hi, he'⟩ := sel_of_getElem? hs0
              have h1' := lb_mono sel hsel hge
              have h2' := lt_lb sel hsel (x := lo + cnt) hi (by rw [he']; omega)
              omega
            exact TraceColl_mono (fun p hp => by simp only [List.mem_append] at hp ⊢; tauto)
              (ih (2 * idx) lo (sp.split cnt) (s + 1) L0 Lv _ _ _ hembL (by rw [hHL]; exact hsubL) hr1 (by rw [hHL])
                ⟨lo0, hlo0, hlt, hs0, hne⟩)
          · have hdd : dgFlat (h qv) = dgFlat (h qh) := by
              first | exact hd.trans heq | exact hd.symm.trans heq
            have hvh : h qv = h qh := by
              have := congrArg dgOf hdd
              simpa [dgOf_dgFlat] using this
            exact ⟨(qv, h qv), by simp, (qh, h qh), by simp only [List.mem_append]; tauto, hqq, hvh⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_pos hC] at hV
          rcases hs : sibs[s]? with _ | sib
          · simp only [hs, tabRun_pure] at hV; simp at hV
          simp only [hs, tabRun_bind] at hV
          rcases hr1 : tabRun h (goRootN skels sp 0 sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)) Lv with ⟨r1, Lv1⟩
          rw [hr1] at hV
          rcases r1 with _ | ⟨r, s1⟩
          · simp [tabRun_pure] at hV
          simp only [tabRun_bind, tabRun_pure] at hV
          obtain ⟨hrok, b1, f1⟩ := goRootN_run skels h sp 0 sel leaf sibs hleaf5 hsib5 _ _ _ _ _ _ _ _ _ hr1
          subst f1
          obtain ⟨qh, qv, hdh, hdv, hinj⟩ := node_step skels h0 idx hidx lh rh sib r hlhok hrhok (hsib5 s sib hs) hrok
          simp only [tabRun_hqN_some skels h _ qh hdh] at hle heq
          simp only [tabRun_hqN_some skels h _ qv hdv, Option.some.injEq, Prod.mk.injEq] at hV
          obtain ⟨⟨hd, hs2⟩, hL2⟩ := hV
          subst hL2
          have hsubR : ∀ p ∈ L0 ++ a1 ++ a2, p ∈ Lv := fun p hp =>
            hle p (by simp only [List.mem_append, List.mem_singleton] at hp ⊢; tauto)
          have hqhm : (qh, h qh) ∈ Lv := hle _ (by simp)
          by_cases hqq : qv = qh
          · obtain ⟨hl', hr'⟩ := hinj hqq
            subst hr'
            obtain ⟨lo0, hlo0, hlo1, hs0, hne⟩ := hdiff
            have hge : lo + sp.split cnt ≤ lo0 := by
              by_contra hlt
              push Not at hlt
              obtain ⟨hi, he'⟩ := sel_of_getElem? hs0
              have h1' := lb_mono sel hsel hlo0
              have h2' := lt_lb sel hsel (x := lo + sp.split cnt) hi (by rw [he']; omega)
              omega
            exact TraceColl_mono (fun p hp => by simp only [List.mem_append] at hp ⊢; tauto)
              (ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) (L0 ++ a1) Lv _ _ _ hembR
                (by rw [hHR]; exact hsubR) hr1 (by rw [hHR]) ⟨lo0, hge, by omega, hs0, hne⟩)
          · have hdd : dgFlat (h qv) = dgFlat (h qh) := by
              first | exact hd.trans heq | exact hd.symm.trans heq
            have hvh : h qv = h qh := by
              have := congrArg dgOf hdd
              simpa [dgOf_dgFlat] using this
            exact ⟨(qv, h qv), by simp, (qh, h qh), by simp only [List.mem_append]; tauto, hqq, hvh⟩
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC] at hV
          simp only [tabRun_pure] at hV; simp at hV

/-! ### the recorded runs compute the flat functions -/

theorem tabRun_hqN_fst (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ) (L : List (NQuery skels × DgJ8)) :
    (tabRun h (hqN skels x) L).1 = Hof skels h x := by
  rcases hd : decQ skels x with _ | q
  · rw [tabRun_hqN_none _ _ _ hd]; simp [Hof, hd]
  · rw [tabRun_hqN_some _ _ _ _ hd]; simp [Hof, hd]

theorem tabRun_honN (skels : List Skeleton) (h : NQuery skels → DgJ8) (sp : TSpec) (j : ℕ) (hl : ℕ → Dg5) :
    ∀ (f idx lo cnt : ℕ) (L : List (NQuery skels × DgJ8)),
      (tabRun h (honN skels sp j hl f idx lo cnt) L).1 = honP (Hof skels h) sp j hl f idx lo cnt := by
  intro f
  induction f with
  | zero => intro idx lo cnt L; simp [honN, honP, tabRun_pure]
  | succ f ih =>
    intro idx lo cnt L
    simp only [honN, honP]
    by_cases hc : cnt == 1
    · simp [hc, tabRun_pure]
    · simp only [hc, Bool.false_eq_true, ite_false, tabRun_bind, tabRun_hqN_fst]
      rw [ih, ih]

/- OLD (superseded by tabRun_goRootN below)
theorem tabRun_goRootN_old (skels : List Skeleton) (h : NQuery skels → DgJ8) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5)
    (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : ℕ) (L : List (NQuery skels × DgJ8)),
      (tabRun h (goRootN skels sp j sel leaf sibs f idx lo cnt s) L).1 =
        goRootF (Hof skels h) sp j sel leaf sibs f idx lo cnt s := by
  intro f
  induction f with
  | zero => intro idx lo cnt s L; simp [goRootN, goRootF, tabRun_pure]
  | succ f ih =>
    intro idx lo cnt s L
    simp only [goRootN, goRootF]
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true, tabRun_pure]
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true, tabRun_pure]
      · simp only [hg, Bool.false_eq_true, ite_false]
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          simp only [hA, ite_true, tabRun_bind]
          rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s) L with ⟨r1, L1⟩
          have e1 := ih (2 * idx) lo (sp.split cnt) s L
          rw [hr1] at e1
          simp only at e1 ⊢
          rw [← e1]
          rcases r1 with _ | ⟨l, s1⟩
          · simp [tabRun_pure]
          · simp only [Option.bind_some, tabRun_bind]
            rcases hr2 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1) L1 with ⟨r2, L2⟩
            have e2 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 L1
            rw [hr2] at e2
            simp only at e2 ⊢
            rw [← e2]
            rcases r2 with _ | ⟨r, s2⟩
            · simp [tabRun_pure]
            · simp [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          simp only [hA, hB, ite_true, ite_false, Bool.false_eq_true]
          rcases hs : sibs[s]? with _ | sib
          · simp [tabRun_pure]
          · simp only [tabRun_bind, Option.bind_some]
            rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
            have e1 := ih (2 * idx) lo (sp.split cnt) (s + 1) L
            rw [hr1] at e1
            simp only at e1 ⊢
            rw [← e1]
            rcases r1 with _ | ⟨l, s1⟩
            · simp [tabRun_pure]
            · simp [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          simp only [hA, hB, hC, ite_true, ite_false, Bool.false_eq_true]
          rcases hs : sibs[s]? with _ | sib
          · simp [tabRun_pure]
          · simp only [tabRun_bind, Option.bind_some]
            rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
            have e1 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) L
            rw [hr1] at e1
            simp only at e1 ⊢
            rw [← e1]
            rcases r1 with _ | ⟨r, s1⟩
            · simp [tabRun_pure]
            · simp [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          simp only [hA, hB, hC, ite_true, ite_false, Bool.false_eq_true, tabRun_pure]

-/

theorem tabRun_goRootN (skels : List Skeleton) (h : NQuery skels → DgJ8) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5)
    (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : ℕ) (L : List (NQuery skels × DgJ8)),
      (tabRun h (goRootN skels sp j sel leaf sibs f idx lo cnt s) L).1 =
        goRootF (Hof skels h) sp j sel leaf sibs f idx lo cnt s := by
  intro f
  induction f with
  | zero => intro idx lo cnt s L; simp [goRootN, goRootF, tabRun_pure]
  | succ f ih =>
    intro idx lo cnt s L
    simp only [goRootN, goRootF]
    by_cases h1 : cnt == 1
    · simp only [h1, ite_true, tabRun_pure]
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases hg : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp only [hg, ite_true, tabRun_pure]
      · simp only [hg, Bool.false_eq_true, ite_false]
        by_cases hB : lb sel (lo + sp.split cnt) > lb sel lo <;> by_cases hC : lb sel (lo + cnt) > lb sel (lo + sp.split cnt)
        · have hA : (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_pos hA, if_pos hA]
          simp only [tabRun_bind]
          rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) s) L with ⟨r1, L1⟩
          have e1 := ih (2 * idx) lo (sp.split cnt) s L
          rw [hr1] at e1
          try simp only at e1
          try simp only [hr1]
          rcases r1 with _ | ⟨l, s1⟩
          · simp [← e1, tabRun_pure]
          · simp only [tabRun_bind]
            rcases hr2 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1) L1 with ⟨r2, L2⟩
            have e2 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) s1 L1
            rw [hr2] at e2
            try simp only at e2
            try simp only [hr2]
            rcases r2 with _ | ⟨r, s2⟩
            · simp [← e1, ← e2, tabRun_pure]
            · simp only [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
              simp [← e1, ← e2]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hA, if_pos hB, if_pos hB]
          rcases hs : sibs[s]? with _ | sib
          · simp [tabRun_pure]
          · simp only [tabRun_bind]
            rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx) lo (sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
            have e1 := ih (2 * idx) lo (sp.split cnt) (s + 1) L
            rw [hr1] at e1
            try simp only at e1
            try simp only [hr1]
            rcases r1 with _ | ⟨l, s1⟩
            · simp [← e1, tabRun_pure]
            · simp only [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
              simp [← e1]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hA, if_neg hB, if_neg hB, if_pos hC, if_pos hC]
          rcases hs : sibs[s]? with _ | sib
          · simp [tabRun_pure]
          · simp only [tabRun_bind]
            rcases hr1 : tabRun h (goRootN skels sp j sel leaf sibs f (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1)) L with ⟨r1, L1⟩
            have e1 := ih (2 * idx + 1) (lo + sp.split cnt) (cnt - sp.split cnt) (s + 1) L
            rw [hr1] at e1
            try simp only at e1
            try simp only [hr1]
            rcases r1 with _ | ⟨r, s1⟩
            · simp [← e1, tabRun_pure]
            · simp only [tabRun_bind, tabRun_pure, tabRun_hqN_fst]
              simp [← e1]
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hA, if_neg hB, if_neg hB, if_neg hC, if_neg hC]
          simp only [tabRun_pure]

/-! ### canonicity of the spec leaves -/

theorem specWord_canon {XI : ExecInst} (hg : setupGates XI = true) (col : FixCol) (i : ℕ) : (specWord XI col i).toNat < p := by
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  have hx : NockvmE2E.Exec.VL.canon (domPt XI i) := NockvmE2E.Exec.VL.mul_lt _ _
  unfold specWord
  cases col with
  | pre c => exact hornerB_canon _ _ (hpre c)
  | zh => exact (prodLinG_spec XI.hGen _ XI.hShift hx hS XI.hN).1
  | zout t => exact (prodLinG_spec XI.hGen _ _ hx (NockvmE2E.Exec.VL.mul_lt _ _) (XI.hN - tabHN XI t)).1

theorem dgOk_hlSpec {XI : ExecInst} (hg : setupGates XI = true) (F half p' : ℕ) : dgOk (hlSpec XI F half p') = true := by
  simp only [hlSpec, dgOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, VF.based, decide_eq_true_eq]
  refine ⟨rfl, ?_⟩
  intro x hx
  have hP := PN_eq
  have hp0 := (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [hP]; exact specWord_canon hg _ _
  all_goals omega

/-- **the deterministic half of `hcoll`**: `VKcollC` forces a collision in the recorded trace of the honest tree plus the verifier recomputation -/
theorem vkcollC_trace (XX : ExecInst) (hg : setupGates XX = true) {skels : List Skeleton}
    (hsk : skels[0]? = some (skelVK XX)) (h : NQuery skels → DgJ8) (πF : FixProof)
    (hc : VKcollC XX (vkSpec XX (Hof skels h)) (Hof skels h) πF) :
    TraceColl (tabRun h (vkProg XX skels πF) []).2 := by
  have h0 : 0 < skels.length := by
    cases skels with
    | nil => simp at hsk
    | cons a t => simp
  have hT : skels.get ⟨0, h0⟩ = skelVK XX := by
    rw [List.getElem?_eq_getElem h0] at hsk
    exact Option.some.inj hsk
  obtain ⟨⟨hwf1, hwf2, hwf3⟩, ⟨s', hgo⟩, hwrong⟩ := VKcollC_flat XX (Hof skels h) πF hc
  obtain ⟨-, hbased, hdg⟩ := hc
  have hleaf5 : ∀ r, dgOk ((openV XX πF).2.1 r) = true := by
    intro r
    have hP := PN_eq
    have hp0 := (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    simp only [openV, dgOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, VF.based, decide_eq_true_eq]
    refine ⟨rfl, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · by_cases hr : r < (πF.vals[0]!).size
      · rw [getElem!_pos _ r hr]
        have := (Array.all_eq_true_iff_forall_mem.1 hbased) _ (Array.getElem_mem hr)
        simpa [VF.based] using this
      · rw [getElem!_neg _ r hr]; simp; omega
    all_goals omega
  have hsib5 : ∀ (s : ℕ) (sib : Dg5), (openV XX πF).2.2[s]? = some sib → dgOk sib = true := by
    intro s sib hs
    exact (Array.all_eq_true_iff_forall_mem.1 hdg) sib (Array.mem_of_getElem? hs)
  have hF := fixCols_size_pos XX
  have hroot : specRoot XX (Hof skels h) = (tabRun h (honN skels (vkSp XX) 0 (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1)))
      (vkSp XX).total 1 0 (vkSp XX).total) []).1 := by
    rw [tabRun_honN]
    have e := specRoot_eq XX (Hof skels h) hF (vkSp XX).total (by rw [vkSp_total])
    rw [← vkSp_total XX] at e
    exact e
  have hrun : tabRun h (goRootN skels (vkSp XX) 0 (openV XX πF).1 (openV XX πF).2.1 (openV XX πF).2.2 (vkSp XX).total 1 0 (vkSp XX).total 0)
      (tabRun h (honN skels (vkSp XX) 0 (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1))) (vkSp XX).total 1 0 (vkSp XX).total) []).2 =
      (some (specRoot XX (Hof skels h), s'),
        (tabRun h (goRootN skels (vkSp XX) 0 (openV XX πF).1 (openV XX πF).2.1 (openV XX πF).2.2 (vkSp XX).total 1 0 (vkSp XX).total 0)
          (tabRun h (honN skels (vkSp XX) 0 (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1))) (vkSp XX).total 1 0 (vkSp XX).total) []).2).2) := by
    refine Prod.ext ?_ rfl
    rw [tabRun_goRootN]
    exact hgo
  simp only [vkProg, tabRun_bind, tabRun_pure]
  exact vk_bind_tab skels h0 h (vkSp XX) (openV XX πF).1 (hlSpec XX (fixCols XX).size (2 ^ (XX.nD - 1))) (openV XX πF).2.1
    (openV XX πF).2.2 hwf1 (dgOk_hlSpec hg _ _) hleaf5 hsib5 (vkSp XX).total 1 0 (vkSp XX).total 0 [] _ _ _ _
    (fun i hi => by rw [hT]; exact hi) (fun p hp => hp) hrun hroot hwrong

/-! ### query counts -/

theorem honN_bound (skels : List Skeleton) (sp : TSpec) (hsp : ∀ c, 2 ≤ c → 0 < sp.split c ∧ sp.split c < c) (j : ℕ) (hl : ℕ → Dg5) :
    ∀ (f idx lo cnt : ℕ), 1 ≤ cnt → cnt ≤ f → IsTotalQueryBound (honN skels sp j hl f idx lo cnt) (cnt - 1) := by
  intro f
  induction f with
  | zero => intro idx lo cnt h1 h2; omega
  | succ f ih =>
    intro idx lo cnt h1 h2
    simp only [honN]
    by_cases hc : cnt == 1
    · simp only [hc, ite_true]
      exact (show IsTotalQueryBound (pure (hl lo) : OracleComp (HN skels) Dg5) 0 from trivial).mono (Nat.zero_le _)
    · simp only [hc, Bool.false_eq_true, ite_false]
      have hc2 : 2 ≤ cnt := by simp at hc; omega
      obtain ⟨hs1, hs2⟩ := hsp cnt hc2
      exact (isTotalQueryBound_bind (ih _ lo _ (by omega) (by omega))
        (fun l => isTotalQueryBound_bind (ih _ (lo + sp.split cnt) (cnt - sp.split cnt) (by omega) (by omega))
          (fun r => hqN_bound skels _))).mono (by omega)

theorem goRootN_bound (skels : List Skeleton) (sp : TSpec) (j : ℕ) (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : Array Dg5) :
    ∀ (f idx lo cnt s : ℕ), 1 ≤ cnt → cnt ≤ f → IsTotalQueryBound (goRootN skels sp j sel leaf sibs f idx lo cnt s) (cnt - 1) := by
  intro f
  induction f with
  | zero => intro idx lo cnt s h1 h2; omega
  | succ f ih =>
    intro idx lo cnt s h1 h2
    have hz : ∀ {β : Type} (b : β), IsTotalQueryBound (pure b : OracleComp (HN skels) β) (cnt - 1) :=
      fun b => (show IsTotalQueryBound (pure b : OracleComp (HN skels) _) 0 from trivial).mono (Nat.zero_le _)
    simp only [goRootN]
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
        have hp0 : ∀ {β : Type} (b : β), IsTotalQueryBound (pure b : OracleComp (HN skels) β) 0 := fun b => trivial
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
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hqN_bound skels _) (fun d => hp0 _)).mono (by omega)
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
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hqN_bound skels _) (fun d => hp0 _)).mono (by omega)
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
              exact (isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) (hqN_bound skels _) (fun d => hp0 _)).mono (by omega)
        · have hA : ¬ (decide (lb sel (lo + sp.split cnt) > lb sel lo) && decide (lb sel (lo + cnt) > lb sel (lo + sp.split cnt))) = true := by
            simp [hB, hC]
          rw [if_neg hA, if_neg hB, if_neg hC]
          exact hz _

/-- the honest tree plus the verifier recomputation make at most `2 (total - 1)` node queries -/
theorem vkProg_bound (XX : ExecInst) (skels : List Skeleton) (πF : FixProof) :
    IsTotalQueryBound (vkProg XX skels πF) (2 * ((vkSp XX).total - 1)) := by
  have hF := fixCols_size_pos XX
  have hsp := ragSpec_split_valid (fixCols XX).size (2 ^ (XX.nD - 1)) hF
  have ht : 1 ≤ (vkSp XX).total := by
    rw [vkSp_total]
    have := Nat.two_pow_pos (XX.nD - 1)
    have : 1 ≤ (fixCols XX).size * 2 ^ (XX.nD - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hF this))
    nlinarith
  unfold vkProg
  refine (isTotalQueryBound_bind (n₁ := (vkSp XX).total - 1) (n₂ := (vkSp XX).total - 1)
    (honN_bound skels (vkSp XX) hsp 0 _ _ 1 0 _ ht le_rfl) (fun dh => ?_)).mono (by omega)
  refine (isTotalQueryBound_bind (n₁ := (vkSp XX).total - 1) (n₂ := 0)
    (goRootN_bound skels (vkSp XX) 0 _ _ _ _ 1 0 _ 0 ht le_rfl) (fun r => ?_)).mono (by omega)
  exact (show IsTotalQueryBound (pure (dh, r) : OracleComp (HN skels) _) 0 from trivial)

#print axioms vk_bind_tab
#print axioms vkcollC_trace
#print axioms vkProg_bound
#print axioms specWord_canon
#print axioms dgOk_hlSpec

end NockvmE2E.Exec.VKTrace
