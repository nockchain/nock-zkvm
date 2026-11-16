/-
  Nock/AxisDescent.lean

  THE HONEST NON-BATCHED BASELINE for axis-lookup verification — the **descended-axis register**
  the way the tex's walk semantics describe it and the way the DEPLOYED
  implementation actually does it (`nockchain/hoon/common/v0-v1/table/verifier/memory.hoon:288–289`:
  `l-axis = 2·axis`, `r-axis = 2·axis + axis-flag`).

  This is a tex-cited CORRECTNESS DELTA beyond the batched App B.2 arithmetization of
  `Nock/AxisBatching.lean` (`axis_indicator`/`axis_counts`), whose axis-lookup soundness the paper
  DEFERS at the paper.
  The batched development proves `mem.axis = Relaxis` only under THREE crutches: a carried `Nested`
  well-nesting hypothesis, the `∑ z^{i_j}` positivity, and the terminal `axis_counts = 0` boundary
  (`AxisBatching.axis_batching_sound`).  The batched recognizer even ADMITS a within-real-subject
  sibling crossing (`scratchpad/RealSubjectCrossing.lean`'s `WALL`).

  The DIRECT model here needs NONE of those.  It threads a per-record **descended-axis** scalar
  down the reconstructed walk and checks the committed axis LOCALLY at each `verify_child`:

    * `read_root` (`mem.root = pt.noun`): SEEDS the region axis to `1`.
    * `decompose` (`pt.noun = cons(lc.noun, rc.noun)`): `lc.a = 2·pt.a`, `rc.a = 2·pt.a + 1` (the
      binary-address doubling, memory.hoon:288–289).
    * `verify_child` (`mem.child = pt.noun`): GATE `mem.axis = pt.a` (committed record axis = the
      node's descended axis).
    * `halt`: leaf.

  The register is a per-record `Option ℕ` (`none` = "the walk has not entered THIS record's read
  region"; the impl's `axis-flag = 0`, memory.hoon:165–181).  It is a **threaded scalar recurrence
  over parent/child labels** — §0-legal (memoryless, positionless; NO pointer, NO range-check, NO
  positional lookup), exactly like `childLinkMem` threading `indicator`/`counts`.

  ─────────────────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN (all UNCONDITIONAL — no `Nested`, no `∑z^{i_j}` positivity, no `axis_counts=0`):

    1. `nested_of_descent` — in a descent-gated walk, a record's `verify_child` is NECESSARILY a
       descendant of its `read_root`.  `Nested` is DERIVED, not assumed: the seed `a=1` occurs only
       at `read_root`, propagates only downward by the doubling, so a node passing the verify gate
       has a `read_root` ancestor (the register is `some`, not `none`).

    2. `axis_correct_desc` / `axis_correct` — the committed `mem.axis` equals the descended address,
       which equals `AxisBatching.Relaxis` (the TRUE topological `axis_root(child)`).  UNCONDITIONAL.

    3. Bridge onto the real reconstructed memory trace (`AxisBridge.MemWalk` / `Walk.ForestReconGoal`,
       reusing `toMTree`): axis validity exposed for the reconstructed forest.

    4. End-to-end capstone `NockVM.V_NockVMROM_forest_direct` (in `Nock/NockVM.lean`): the paper's
       witness-linked verifier with an axis-validity conjunct threaded through conjunct (2)'s OWN
       `ForestReconGoal` forest, carrying NONE of Nested/positivity/counts=0.

  We REUSE (do not re-derive) the offline-memory LogUp / `InterChain` (read/write consistency) —
  that is NOT the batching trick.  We REPLACE only the `axis_counts`/`axis_indicator` axis check.
  The batched development (`AxisBatching.lean`, the batched parts of `AxisBridge`/`MemoryTable`) is
  left UNTOUCHED for later comparison.

  Generic over an arbitrary field `K`; `goldilocks_prime` is NOT used.
  ─────────────────────────────────────────────────────────────────────────────────────────
-/
import Nock.AxisBatching

namespace Nock
namespace AxisDescent

open AxisBatching AxisBatching.MTree

variable {K : Type*} [Field K]

/-! ## The descended-axis register and the descent gate

  We work over the SAME reconstructed-walk value model `AxisBatching.MTree K` the batched
  development uses (so `readCount`/`verifyCount`/`vaddr`/`vdep`/`vaxis`/`Relaxis` are all reused
  verbatim — the topological truth is the same object).  What we REPLACE is the axis CHECK: no
  `indP`/`countsP`, but a threaded descended-axis register.

  The register is analysed PER RECORD `e`.  It is
  the memory-side analogue of `AxisBatching`'s per-`e` treatment (`readCount e`, `verifyCount e`):
  each record's lookup is verified relative to its OWN `read_root`.  The deployed impl batches all
  records into a single `axis` column (memory.hoon), the exact analogue of how the batched model
  batches into `axis_counts`; here — as in `AxisBatching` — we reason one record at a time. -/

/-- **The descended-axis register threaded for record `e`.**  `none` = not (yet) inside record
    `e`'s read region; `some a` = inside, at descended axis `a`.  RESET to `some 1` at record
    `e`'s own `read_root`; DOUBLED at `decompose`; carried through unrelated `read`/`verify`.
    (`descA` returns the register value AT record `e`'s `verify_child`; `none` if that verify is
    NOT reached inside `e`'s region — i.e. not nested under `e`'s `read_root`.) -/
def descA (e : ℕ) : Option ℕ → MTree K → Option ℕ
  | _,      .halt          => none
  | some k, .decompose l r =>
      if verifyCount e l = 1 then descA e (some (2 * k)) l
      else if verifyCount e r = 1 then descA e (some (2 * k + 1)) r else none
  | none,   .decompose l r =>
      if verifyCount e l = 1 then descA e none l
      else if verifyCount e r = 1 then descA e none r else none
  | a,      .read e' c     => descA e (if e' = e then some 1 else a) c
  | a,      .verify e' _ c => if e' = e then a else descA e a c

/-- **The descent GATE for record `e`.**  Threading the register from seed `ma`, every
    `verify_child` for `e` must commit exactly its descended axis, and a `verify_child` for `e`
    reached with NO active region (`none`) is REJECTED (there is no `read_root` ancestor to seed
    it — this is the sibling-crossing rejection).  A threaded scalar recurrence over parent/child
    labels (§0-legal). -/
def DescOK (e : ℕ) : Option ℕ → MTree K → Prop
  | _,      .halt            => True
  | some k, .decompose l r   => DescOK e (some (2 * k)) l ∧ DescOK e (some (2 * k + 1)) r
  | none,   .decompose l r   => DescOK e none l ∧ DescOK e none r
  | a,      .read e' c       => DescOK e (if e' = e then some 1 else a) c
  | some k, .verify e' comm c => (e' = e → comm = ((k : ℕ) : K)) ∧ DescOK e (some k) c
  | none,   .verify e' _ c    => (e' = e → False) ∧ DescOK e none c

/-- **The full direct axis-descent model.**  Every record `e` in the walk `t` passes the descent
    gate, seeded `none` at the walk root (no region active before the first `read_root`). -/
def DescModel (t : MTree K) : Prop := ∀ e : ℕ, DescOK e none t

/-! ## Item 2 (part a): `axis_correct_desc` — committed axis = descended address (UNCONDITIONAL)

  The verify gate forces `mem.axis = pt.a`, and `descA` computes `pt.a` (the descended address).
  No `Nested`, no positivity, no `axis_counts = 0`; the only hypothesis is `verifyCount e t = 1`
  (identifying the single `verify_child` whose committed axis `vaxis e t` we read out — NOT the
  batched "distinctness" crutch, which needs read-AND-verify counts to block compensating errors). -/

/-- Under the descent gate, `vaxis e t` (the committed `mem.axis` at the `verify_child` for `e`)
    equals — as a field element — the descended register `descA e ma t`, which is necessarily
    `some` (there IS a read region seeding it: `nested_of_descent`). -/
theorem descOK_vaxis (e : ℕ) :
    ∀ (ma : Option ℕ) (t : MTree K), DescOK e ma t → verifyCount e t = 1 →
      ∃ n : ℕ, descA e ma t = some n ∧ vaxis e t = ((n : ℕ) : K) := by
  intro ma t
  induction t generalizing ma with
  | halt => intro _ hv; simp [verifyCount] at hv
  | decompose l r ihl ihr =>
      intro hok hv
      simp only [verifyCount] at hv
      cases ma with
      | some k =>
          obtain ⟨hl, hr⟩ := hok
          by_cases hvl : verifyCount e l = 1
          · have hvr : verifyCount e r = 0 := by omega
            simp only [descA, vaxis, if_pos hvl]
            exact ihl (some (2 * k)) hl hvl
          · have hvr : verifyCount e r = 1 := by omega
            simp only [descA, vaxis, if_neg hvl, if_pos hvr]
            exact ihr (some (2 * k + 1)) hr hvr
      | none =>
          obtain ⟨hl, hr⟩ := hok
          by_cases hvl : verifyCount e l = 1
          · have hvr : verifyCount e r = 0 := by omega
            simp only [descA, vaxis, if_pos hvl]
            exact ihl none hl hvl
          · have hvr : verifyCount e r = 1 := by omega
            simp only [descA, vaxis, if_neg hvl, if_pos hvr]
            exact ihr none hr hvr
  | read e' c ih =>
      intro hok hv
      simp only [verifyCount] at hv
      simp only [descA, DescOK] at *
      exact ih _ hok hv
  | verify e' comm c ih =>
      intro hok hv
      simp only [verifyCount] at hv
      cases ma with
      | some k =>
          obtain ⟨hgate, hc⟩ := hok
          by_cases he : e' = e
          · refine ⟨k, ?_, ?_⟩
            · rw [descA, if_pos he]
            · rw [vaxis, if_pos he]; exact hgate he
          · have hvc : verifyCount e c = 1 := by simp [he] at hv ⊢; omega
            simp only [descA, vaxis, if_neg he]
            exact ih (some k) hc hvc
      | none =>
          obtain ⟨hgate, hc⟩ := hok
          by_cases he : e' = e
          · exact absurd rfl (he ▸ hgate)
          · have hvc : verifyCount e c = 1 := by simp [he] at hv ⊢; omega
            simp only [descA, vaxis, if_neg he]
            exact ih none hc hvc

/-! ## Item 1: `nested_of_descent` — `Nested` is DERIVED from the descent gate

  A `verify_child` for `e` that passes the gate necessarily descends from `e`'s `read_root`: the
  register at the verify is `some` (`descOK_vaxis`), and the ONLY thing that turns `none` into
  `some` is a `read_root` for `e` (`descA_none_readCount`).  Hence `readCount e t ≥ 1` — the read
  is present AND (by the threading) an ancestor of the verify. -/

/-- If record `e` is never read (`readCount e t = 0`), the register threaded from `none` stays
    `none` everywhere — in particular no `verify_child` for `e` can be seeded. -/
theorem descA_none_of_noRead (e : ℕ) :
    ∀ t : MTree K, readCount e t = 0 → descA e none t = none := by
  intro t
  induction t with
  | halt => intro _; rfl
  | decompose l r ihl ihr =>
      intro hr
      simp only [readCount] at hr
      have hrl : readCount e l = 0 := by omega
      have hrr : readCount e r = 0 := by omega
      simp only [descA]
      by_cases hvl : verifyCount e l = 1
      · rw [if_pos hvl]; exact ihl hrl
      · rw [if_neg hvl]; by_cases hvr : verifyCount e r = 1
        · rw [if_pos hvr]; exact ihr hrr
        · rw [if_neg hvr]
  | read e' c ih =>
      intro hr
      simp only [readCount] at hr
      have he : e' ≠ e := by rintro rfl; simp at hr
      have hrc : readCount e c = 0 := by simpa [he] using hr
      simp only [descA, if_neg he]
      exact ih hrc
  | verify e' comm c ih =>
      intro hr
      simp only [readCount] at hr
      by_cases he : e' = e
      · subst he; simp [descA]
      · simp only [descA, if_neg he]; exact ih hr

/-- **`nested_of_descent` (item 1).**  In a descent-gated walk, a record `e` whose `verify_child`
    is present (`verifyCount e t = 1`) is NECESSARILY read: `readCount e t ≥ 1` — its `read_root`
    exists and (by the register threading, which only carries `some` downward from a `read_root`)
    is an ancestor of the `verify_child`.  `Nested` is DERIVED, not assumed. -/
theorem nested_of_descent (e : ℕ) (t : MTree K)
    (hok : DescOK e none t) (hv : verifyCount e t = 1) :
    1 ≤ readCount e t := by
  obtain ⟨n, hn, _⟩ := descOK_vaxis e none t hok hv
  by_contra hlt
  have h0 : readCount e t = 0 := by omega
  rw [descA_none_of_noRead e t h0] at hn
  simp at hn

/-! ## Item 2 (part b): the descended address EQUALS `AxisBatching.Relaxis`

  `descA` (threaded ℕ doubling, cast to `K`) equals `Relaxis` (the batched model's `K`-valued
  topological address, the SAME doubling).  Together with `descOK_vaxis` this gives
  `mem.axis = Relaxis` for the direct model. -/

/-- **No read below ⟹ the register threads to `k·2^{vdep} + vaddr`.**  Where record `e` has no
    `read_root` in `t` (`readCount e t = 0`) but its `verify_child` is here (`verifyCount e t = 1`),
    the register seeded `some k` descends by pure doubling to the verify, giving (cast to `K`) the
    batched address `k·2^{vdep} + vaddr`.  (The `read_root` reset cannot fire — there is none.) -/
theorem descA_somek_eval (e : ℕ) :
    ∀ (t : MTree K) (k : ℕ), readCount e t = 0 → verifyCount e t = 1 →
      ∃ m : ℕ, descA e (some k) t = some m
        ∧ ((m : ℕ) : K) = (k : K) * (2 : K) ^ (vdep e t) + vaddr e t := by
  intro t
  induction t with
  | halt => intro k _ hv; simp [verifyCount] at hv
  | decompose l r ihl ihr =>
      intro k hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have hrl : readCount e l = 0 := by omega
      have hrr : readCount e r = 0 := by omega
      by_cases hvl : verifyCount e l = 1
      · have hvr : verifyCount e r = 0 := by omega
        obtain ⟨m, hm, hme⟩ := ihl (2 * k) hrl hvl
        refine ⟨m, ?_, ?_⟩
        · simp only [descA, if_pos hvl]; exact hm
        · simp only [vdep, vaddr, if_pos hvl]
          rw [hme, pow_succ]; push_cast; ring
      · have hvr : verifyCount e r = 1 := by omega
        obtain ⟨m, hm, hme⟩ := ihr (2 * k + 1) hrr hvr
        refine ⟨m, ?_, ?_⟩
        · simp only [descA, if_neg hvl, if_pos hvr]; exact hm
        · simp only [vdep, vaddr, if_neg hvl]
          rw [hme, pow_succ]; push_cast; ring
  | read e' c ih =>
      intro k hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hr
      have hrc : readCount e c = 0 := by simpa [he] using hr
      obtain ⟨m, hm, hme⟩ := ih k hrc hv
      refine ⟨m, ?_, ?_⟩
      · simp only [descA, if_neg he]; exact hm
      · simp only [vdep, vaddr]; exact hme
  | verify e' comm c ih =>
      intro k hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · subst he
        refine ⟨k, ?_, ?_⟩
        · simp [descA]
        · simp only [vdep, vaddr]; push_cast; ring
      · have hvc : verifyCount e c = 1 := by simpa [he] using hv
        obtain ⟨m, hm, hme⟩ := ih k hr hvc
        refine ⟨m, ?_, ?_⟩
        · simp only [descA, if_neg he]; exact hm
        · simp only [vdep, vaddr, if_neg he]; exact hme

/-- **The descended address equals `Relaxis`.**  For a USED record (`readCount e t = 1`, unique —
    inherent to naming `Relaxis`, which is defined by the read-relative doubling; NOT a soundness
    crutch) whose register threaded from `none` HAS reached a value (`descA e none t = some m` — i.e.
    the verify IS nested under the read, the crossing case having `descA = none` is vacuously
    excluded), that value cast to `K` equals `Relaxis e t`.  UNCONDITIONAL in `Nested`/positivity/
    `counts=0`. -/
theorem descA_eq_Relaxis (e : ℕ) :
    ∀ (t : MTree K) (m : ℕ), readCount e t = 1 → verifyCount e t = 1 →
      descA e none t = some m → ((m : ℕ) : K) = Relaxis e t := by
  intro t
  induction t with
  | halt => intro m hr _ _; simp [readCount] at hr
  | decompose l r ihl ihr =>
      intro m hr hv hda
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases hrl : readCount e l = 1
      · have hrr : readCount e r = 0 := by omega
        by_cases hvl : verifyCount e l = 1
        · rw [Relaxis, if_pos hrl]
          exact ihl m hrl hvl (by rwa [descA, if_pos hvl] at hda)
        · -- crossing: verify on the right, read on the left ⇒ descA e none r = none, vacuous
          have hvr : verifyCount e r = 1 := by omega
          rw [descA, if_neg hvl, if_pos hvr, descA_none_of_noRead e r hrr] at hda
          exact absurd hda (by simp)
      · have hrr : readCount e r = 1 := by omega
        by_cases hvr : verifyCount e r = 1
        · have hvl : verifyCount e l = 0 := by omega
          rw [Relaxis, if_neg hrl]
          exact ihr m hrr hvr
            (by rwa [descA, if_neg (by omega : ¬ verifyCount e l = 1), if_pos hvr] at hda)
        · have hvl : verifyCount e l = 1 := by omega
          rw [descA, if_pos hvl, descA_none_of_noRead e l (by omega)] at hda
          exact absurd hda (by simp)
  | read e' c ih =>
      intro m hr hv hda
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · have hrc : readCount e c = 0 := by rw [if_pos he] at hr; omega
        obtain ⟨m', hm', hme⟩ := descA_somek_eval e c 1 hrc hv
        rw [descA, if_pos he, hm'] at hda
        have hmm : m' = m := by injection hda
        rw [Relaxis, if_pos he, ← hmm, hme]; push_cast; ring
      · have hrc : readCount e c = 1 := by simpa [he] using hr
        rw [Relaxis, if_neg he]
        exact ih m hrc hv (by rwa [descA, if_neg he] at hda)
  | verify e' comm c ih =>
      intro m hr hv hda
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · rw [descA, if_pos he] at hda; exact absurd hda (by simp)
      · have hvc : verifyCount e c = 1 := by simpa [he] using hv
        show ((m : ℕ) : K) = Relaxis e c
        exact ih m hr hvc (by rwa [descA, if_neg he] at hda)

/-! ## Item 2 (headline): `axis_correct` — `mem.axis = Relaxis`, UNCONDITIONAL -/

/-- **`axis_correct` (item 2).**  In a descent-gated walk (`DescOK e none t`) with record `e` used
    (`readCount e t = 1`, `verifyCount e t = 1`), the committed axis `vaxis e t` (`= mem.axis`)
    equals the TRUE topological address `Relaxis e t` (`= axis_root(child)`).

    HYPOTHESIS LIST — note what is ABSENT: NO `Nested` (derived, `nested_of_descent`), NO `∑z^{i_j}`
    positivity, NO `axis_counts = 0` terminal boundary.  Only the descent gate + "the record is
    used once" (`readCount = verifyCount = 1`, inherent to naming the single record's `Relaxis`). -/
theorem axis_correct (e : ℕ) (t : MTree K)
    (hok : DescOK e none t) (hr : readCount e t = 1) (hv : verifyCount e t = 1) :
    vaxis e t = Relaxis e t := by
  obtain ⟨n, hn, hvax⟩ := descOK_vaxis e none t hok hv
  rw [hvax, descA_eq_Relaxis e t n hr hv hn]

end AxisDescent
end Nock
