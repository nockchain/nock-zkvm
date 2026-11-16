import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.TemplateAxisCounting

/-!
# Same-execution served-memory trace

This is the semantic CORE connective between Nock requests and the supplied memory forest.  It is an *operational* object: a recursive, noun-indexed walk
over the actual supplied root, in which

* every node carries the realized noun of the walked subject;
* a `read_root` node binds that noun and the emitted record to one compute-side service — the
  paper's "check that its root node is equal to the parent label";
* the matching `verify_child` node binds its realized noun to the record's child and its committed
  `address` column to the record's axis — the paper's "check that it is equal to the parent node of
  the label … remove `address · z^i`";
* the descent between the two is the paper's own axis recursion `axis(left) = 2·axis`,
  `axis(right) = 2·axis + 1`, i.e. the route is the *binary expansion of the
  record's axis*, not a free path asserted equal to it.

From those bindings the axis facts are DERIVED, not accepted: `VerifyRoute.served` recovers
`Noun.slot (pathAxis bs) n = some child` from the noun index, `ServiceWalk.nounShape` recovers
`NounShape`, `ServiceWalk.readVerifyNested` recovers the ancestry primitive, and
`ServiceWalk.axisValidity` derives `vaxis = Relaxis` from the record binding plus the axis descent
together with read/verify timestamp uniqueness.  No `pathAxis = axis` equation, `ReadVerifyNested`,
`NounShape`, `ExactAxisStructuralRefinement`, `ExactMemoryAxisValidity`, polynomial equation,
acceptance predicate, or production assignment is a field.

`RootTrace` gives the exact semantic service partition of one supplied root.  Its record partition
is literal (it is the emission list of that root's `read_root` rows), while the two exponent
partitions are `List.Perm`: the paper's `intermediate` matching is a positionless LogUp multiset,
not a traversal-order equality.  Empty service
partitions are allowed, since a supplied noun root may require only decompose/halt validation.

The two aggregate side conditions live on `ExactServedMemoryTrace`, not on every root: global
`z^i` timestamp uniqueness and the `L_mIO` index range `[K]` of the one `intermediate` accumulator, which the paper stores "externally
to the node labels … a variable `global' to the traversal" with only global initial-zero and
terminal-zero checks.  A record-free root is therefore fully legal, both locally and in the
aggregate: the paper seeds every mutated `OP2`/`OP7`/`OP8`/`OP9` subject into the same forest,
so a seeded atom subject is necessarily a record-free `halt` leaf.
-/

namespace Nock.NockVMROM.Thm54.ServedMemoryTrace

open scoped Classical
open Nock
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open TemplateAxisCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. Nock axes of root-relative left/right paths -/

/-- Low binary bits contributed by a root-to-node left/right path. -/
def pathAddress : List Bool → ℕ
  | [] => 0
  | b :: bs => pathAddress bs + if b then 2 ^ bs.length else 0

/-- The ordinary Nock axis of a root-to-node path: the leading-`1` binary address. -/
def pathAxis (bs : List Bool) : ℕ :=
  pathAddress bs + 2 ^ bs.length

theorem pathAxis_pos (bs : List Bool) : 1 ≤ pathAxis bs := by
  have h : 1 ≤ 2 ^ bs.length := Nat.one_le_two_pow
  simp only [pathAxis]
  omega

theorem pathAddress_concat (bs : List Bool) (b : Bool) :
    pathAddress (bs ++ [b]) = 2 * pathAddress bs + (if b then 1 else 0) := by
  induction bs with
  | nil => cases b <;> simp [pathAddress]
  | cons x xs ih =>
      have hx : (2 : ℕ) ^ (xs ++ [b]).length = 2 * 2 ^ xs.length := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring
      have hcons : pathAddress ((x :: xs) ++ [b])
          = pathAddress (xs ++ [b]) + (if x then 2 ^ (xs ++ [b]).length else 0) := rfl
      have hcons2 : pathAddress (x :: xs)
          = pathAddress xs + (if x then 2 ^ xs.length else 0) := rfl
      rw [hcons, hcons2, ih, hx]
      cases x <;> (simp; try omega)

/-- Appending one descent step is the paper's axis recursion `2·axis (+1 on the right)`. -/
theorem pathAxis_concat (bs : List Bool) (b : Bool) :
    pathAxis (bs ++ [b]) = 2 * pathAxis bs + (if b then 1 else 0) := by
  have hlen : (bs ++ [b]).length = bs.length + 1 := by simp
  simp only [pathAxis, pathAddress_concat, hlen, pow_succ]
  omega

/-- The root-relative left/right descent path of a Nock axis: its binary digits below the leading
one, most significant (topmost) first. -/
def axisPath (a : ℕ) : List Bool :=
  if a < 2 then [] else axisPath (a / 2) ++ [decide (a % 2 = 1)]
termination_by a
decreasing_by omega

theorem axisPath_of_lt_two {a : ℕ} (h : a < 2) : axisPath a = [] := by
  rw [axisPath, if_pos h]

theorem axisPath_of_two_le {a : ℕ} (h : 2 ≤ a) :
    axisPath a = axisPath (a / 2) ++ [decide (a % 2 = 1)] := by
  rw [axisPath, if_neg (by omega)]

/-- The descent path of an axis recomputes that axis.  This is the derivation that turns a
record's axis into a memory-tree route; nothing asserts `pathAxis bs = axis`. -/
theorem pathAxis_axisPath : ∀ a : ℕ, 1 ≤ a → pathAxis (axisPath a) = a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro ha
      rw [axisPath]
      by_cases h : a < 2
      · have ha1 : a = 1 := by omega
        subst ha1
        simp [pathAxis, pathAddress]
      · rw [if_neg h, pathAxis_concat, ih (a / 2) (by omega) (by omega)]
        have hbit : (if (decide (a % 2 = 1)) then 1 else 0) = a % 2 := by
          rcases Nat.mod_two_eq_zero_or_one a with hm | hm <;> simp [hm]
        rw [hbit]
        omega

/-! ## B. The walked noun at a route position -/

/-- One left/right step in the walked noun. -/
def nounChild : Bool → Noun → Option Noun
  | _, .atom _ => none
  | b, .cell l r => some (if b then r else l)

/-- The noun reached by a root-relative left/right path. -/
def nounAt : List Bool → Noun → Option Noun
  | [], n => some n
  | b :: bs, n => (nounChild b n).bind (nounAt bs)

theorem nounAt_concat (bs : List Bool) (b : Bool) (n : Noun) :
    nounAt (bs ++ [b]) n = (nounAt bs n).bind (nounChild b) := by
  induction bs generalizing n with
  | nil => cases n <;> simp [nounAt, nounChild]
  | cons x xs ih =>
      cases n with
      | atom k => simp [nounAt, nounChild]
      | cell l r => simp [nounAt, nounChild, ih]

private theorem slot_step (k : ℕ) (hk : 1 ≤ k) (b : Bool) (n : Noun) :
    Noun.slot (2 * k + if b then 1 else 0) n = (Noun.slot k n).bind (nounChild b) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * k + (if b then 1 else 0) = m + 2 := by
    refine ⟨2 * k + (if b then 1 else 0) - 2, ?_⟩
    cases b <;> simp <;> omega
  have hdiv : (2 * k + (if b then 1 else 0)) / 2 = k := by
    cases b <;> (simp; try omega)
  have hmod : (2 * k + (if b then 1 else 0)) % 2 = (if b then 1 else 0) := by
    cases b <;> simp
  rw [hm, Noun.slot, ← hm, hdiv, hmod]
  cases hs : Noun.slot k n with
  | none => simp
  | some v =>
      cases v with
      | atom j => simp [nounChild]
      | cell l r => cases b <;> simp [nounChild]

/-- The Nock `slot` operator IS the root-relative descent of the path's axis. -/
theorem slot_pathAxis (bs : List Bool) (n : Noun) :
    Noun.slot (pathAxis bs) n = nounAt bs n := by
  induction bs using List.reverseRecOn with
  | nil => simp [pathAxis, pathAddress, Noun.slot, nounAt]
  | append_singleton bs b ih =>
      rw [pathAxis_concat, nounAt_concat, ← ih]
      exact slot_step (pathAxis bs) (pathAxis_pos bs) b n

/-! ## C. Compute-side services -/

/-- One Nock-level service record from the compute trace. -/
structure Service
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) where
  exponent : ℕ
  record : ComputeTable.MemRec K
  root : Noun
  child : Noun
  axis : ℕ
  request_mem : record ∈ exec.rawRequests
  timestamp : record.ts = cfg.challenges.α ^ exponent
  realization : OpcodeSemantics.RealizesMemRec cfg.challenges.z record root child axis
  served : Noun.slot axis root = some child

/-- Nock axes are leading-`1` binary addresses, so a genuinely served record has `axis ≥ 1`. -/
theorem Service.axis_pos {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : Service cfg exec) : 1 ≤ s.axis := by
  by_contra h
  have h0 : s.axis = 0 := by omega
  have hs := s.served
  rw [h0] at hs
  simp [Noun.slot] at hs

/-- Records emitted by `read_root` rows in one authoritative supplied memory root. -/
def rootResponseRecords
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (i : Fin cfg.kMem) : List (ComputeTable.MemRec K) :=
  (Nock.Walk.bfsForest [exec.memoryTreeAt i]).flatMap
    (fun node : Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K) =>
      MemoryTable.responseRecords node.label.2.2)

/-! ## D. The noun-indexed operational route and walk -/

/-- The recursively generated route from one `read_root` node down to the matching `verify_child`.

It is indexed by the realized noun at the current node, so each `decompose` step consumes one
binary digit of the axis in the paper's own recursion.  Its terminal constructor binds the
verify node's realized noun to the record's child and its committed `address` column to the
record's axis.  Absence side conditions keep the chosen timestamp unique inside
the route. -/
inductive VerifyRoute (e : ℕ) (child : Noun) (recAxis : K) :
    List Bool → Noun → MTree K → Prop
  | here {n : Noun} {a : K} {c : MTree K}
      (hchild : n = child) (hcommitted : a = recAxis)
      (hr : readCount e c = 0) (hv : verifyCount e c = 0) :
      VerifyRoute e child recAxis [] n (.verify e a c)
  | left {bs : List Bool} {nl nr : Noun} {l r : MTree K}
      (route : VerifyRoute e child recAxis bs nl l)
      (hr : readCount e r = 0) (hv : verifyCount e r = 0) :
      VerifyRoute e child recAxis (false :: bs) (.cell nl nr) (.decompose l r)
  | right {bs : List Bool} {nl nr : Noun} {l r : MTree K}
      (hr : readCount e l = 0) (hv : verifyCount e l = 0)
      (route : VerifyRoute e child recAxis bs nr r) :
      VerifyRoute e child recAxis (true :: bs) (.cell nl nr) (.decompose l r)
  | read_other {bs : List Bool} {n : Noun} {e' : ℕ} {c : MTree K}
      (hne : e' ≠ e) (route : VerifyRoute e child recAxis bs n c) :
      VerifyRoute e child recAxis bs n (.read e' c)
  | verify_other {bs : List Bool} {n : Noun} {e' : ℕ} {a : K} {c : MTree K}
      (hne : e' ≠ e) (route : VerifyRoute e child recAxis bs n c) :
      VerifyRoute e child recAxis bs n (.verify e' a c)

omit [Field F] [Algebra F K] in
private theorem nested_of_event_counts_zero (e : ℕ) :
    ∀ t : MTree K, readCount e t = 0 → verifyCount e t = 0 → Nested e t := by
  intro t
  induction t with
  | halt => simp [Nested]
  | decompose l r ihl ihr =>
      simp only [readCount, verifyCount]
      intro hr hv
      have hrl : readCount e l = 0 := by omega
      have hrr : readCount e r = 0 := by omega
      have hvl : verifyCount e l = 0 := by omega
      have hvr : verifyCount e r = 0 := by omega
      exact ⟨by omega, by omega, ihl hrl hvl, ihr hrr hvr⟩
  | read e' c ih =>
      simp only [readCount, verifyCount]
      by_cases h : e' = e
      · subst e'
        simp
      · intro hr hv
        have hr' : readCount e c = 0 := by simpa [h] using hr
        simpa [Nested, h] using ih hr' hv
  | verify e' a c ih =>
      simp only [readCount, verifyCount]
      by_cases h : e' = e
      · subst e'
        simp
      · intro hr hv
        have hv' : verifyCount e c = 0 := by simpa [h] using hv
        simpa [Nested, h] using ih hr hv'

/-- A generated route has exactly one matching verify, no matching read, computes the ordinary
Nock address from its local left/right choices, exposes the bound committed axis, and locates the
bound child noun through the walked noun. -/
theorem VerifyRoute.spec {e : ℕ} {child : Noun} {recAxis : K} {bs : List Bool} {n : Noun}
    {t : MTree K} (h : VerifyRoute e child recAxis bs n t) :
    readCount e t = 0 ∧
      verifyCount e t = 1 ∧
      Nested e t ∧
      vaxis e t = recAxis ∧
      vdep e t = bs.length ∧
      vaddr e t = (pathAddress bs : K) ∧
      nounAt bs n = some child := by
  induction h with
  | here hchild hcommitted hr hv =>
      subst hchild
      subst hcommitted
      refine ⟨by simp [readCount, hr], by simp [verifyCount, hv], ?_,
        by simp [vaxis], by simp [vdep], by simp [vaddr, pathAddress], by simp [nounAt]⟩
      simp only [Nested]
      exact ⟨by simpa using hr, nested_of_event_counts_zero e _ hr hv⟩
  | @left bs nl nr l r route hr hv ih =>
      obtain ⟨hrr, hvr, hn, ha, hd, hvaddr, hnoun⟩ := ih
      refine ⟨by simp [readCount, hrr, hr], by simp [verifyCount, hvr, hv], ?_,
        by simp [vaxis, hvr, ha], by simp [vdep, hvr, hd], ?_, ?_⟩
      · simp only [Nested]
        exact ⟨by omega, by omega, hn, nested_of_event_counts_zero e _ hr hv⟩
      · simp [vaddr, hvr, hvaddr, pathAddress]
      · simpa [nounAt, nounChild] using hnoun
  | @right bs nl nr l r hr hv route ih =>
      obtain ⟨hrr, hvr, hn, ha, hd, hvaddr, hnoun⟩ := ih
      have hvne : verifyCount e l ≠ 1 := by omega
      refine ⟨by simp [readCount, hrr, hr], by simp [verifyCount, hvr, hv], ?_,
        by simp [vaxis, hvne, ha], by simp [vdep, hvne, hd], ?_, ?_⟩
      · simp only [Nested]
        exact ⟨by omega, by omega, nested_of_event_counts_zero e _ hr hv, hn⟩
      · simp [vaddr, hvne, hvaddr, hd, pathAddress]
      · simpa [nounAt, nounChild] using hnoun
  | read_other hne route ih =>
      simpa [readCount, verifyCount, Nested, vaxis, vdep, vaddr, hne] using ih
  | verify_other hne route ih =>
      simpa [readCount, verifyCount, Nested, vaxis, vdep, vaddr, hne] using ih

/-- **The route DERIVES its Nock slot fact.**  The bound root noun, the bound child noun and the
axis recursion together give `\(pathAxis bs, n\) ↦ child`; no slot or axis equation is a field of
the route. -/
theorem VerifyRoute.served {e : ℕ} {child : Noun} {recAxis : K} {bs : List Bool} {n : Noun}
    {t : MTree K} (h : VerifyRoute e child recAxis bs n t) :
    Noun.slot (pathAxis bs) n = some child := by
  rw [slot_pathAxis]
  exact h.spec.2.2.2.2.2.2

/-- Recursive noun-indexed service walk over one supplied memory root.

Every node is indexed by the realized noun of the walked subject.  At a `read_root` node the
realized noun and the emitted record are bound to one compute-side service, and the matching
`verify_child` is located by the *binary expansion of that record's axis*. -/
inductive ServiceWalk
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) : Noun → MTree K → Prop
  | halt {a : ℕ} : ServiceWalk services (.atom a) .halt
  | decompose {nl nr : Noun} {l r : MTree K} :
      ServiceWalk services nl l → ServiceWalk services nr r →
        ServiceWalk services (.cell nl nr) (.decompose l r)
  | read {n : Noun} {e : ℕ} {c : MTree K} (s : Service cfg exec)
      (hs : s ∈ services) (he : s.exponent = e) (hroot : s.root = n)
      (route : VerifyRoute e s.child s.record.axis (axisPath s.axis) n c)
      (below : ServiceWalk services n c) :
      ServiceWalk services n (.read e c)
  | verify {n : Noun} {e : ℕ} {a : K} {c : MTree K} :
      ServiceWalk services n c → ServiceWalk services n (.verify e a c)

namespace ServiceWalk

variable {cfg : ExactConfig F K} {exec : ExactExecution cfg}
  {services : List (Service cfg exec)}

/-- The walk DERIVES the noun-shape reconstruction; `NounShape` is not a field. -/
theorem nounShape {n : Noun} {t : MTree K} (h : ServiceWalk services n t) :
    NounShape n t := by
  induction h with
  | halt => exact NounShape.halt
  | decompose _ _ ihl ihr => exact NounShape.decompose ihl ihr
  | read s hs he hroot route below ih => exact NounShape.read ih
  | verify _ ih => exact NounShape.verify ih

/-- The walk DERIVES the ancestry primitive; `ReadVerifyNested` is not a field. -/
theorem readVerifyNested {n : Noun} {t : MTree K} (h : ServiceWalk services n t) :
    ReadVerifyNested t := by
  induction h with
  | halt => trivial
  | decompose _ _ ihl ihr => exact ⟨ihl, ihr⟩
  | read s hs he hroot route child ih =>
      exact ⟨by
        have hv := route.spec.2.1
        omega, ih⟩
  | verify _ ih => exact ih

/-- Read multiplicity is dominated by verify multiplicity below a walked node. -/
private theorem readCount_le_verifyCount {n : Noun} {t : MTree K}
    (h : ServiceWalk services n t) (hone : ∀ q, readCount q t ≤ 1) (e : ℕ) :
    readCount e t ≤ verifyCount e t :=
  rc_le_vc_of_rvn t h.readVerifyNested hone e

/-- **The walk DERIVES the axis conclusion.**  At each `read_root` the committed `address` column
is the record's axis (route binding) while the topological address is the binary expansion of that
same axis (route descent); the two therefore agree.  Timestamp uniqueness localizes the argument
at each `decompose`. -/
theorem axisValidity {n : Noun} {t : MTree K} (h : ServiceWalk services n t) :
    (readExps t).Nodup → (verifyExps t).Nodup →
      ∀ e ∈ readExps t, vaxis e t = Relaxis e t := by
  induction h with
  | halt =>
      intro _ _ e he
      simp [readExps] at he
  | @decompose nl nr l r hl hr ihl ihr =>
      intro hrnd hvnd e he
      rw [readExps] at hrnd he
      rw [verifyExps] at hvnd
      have hrl : (readExps l).Nodup := hrnd.of_append_left
      have hrr : (readExps r).Nodup := hrnd.of_append_right
      have hvl : (verifyExps l).Nodup := hvnd.of_append_left
      have hvr : (verifyExps r).Nodup := hvnd.of_append_right
      have hrdis : (readExps l).Disjoint (readExps r) :=
        List.disjoint_of_nodup_append hrnd
      have hvdis : (verifyExps l).Disjoint (verifyExps r) :=
        List.disjoint_of_nodup_append hvnd
      rcases List.mem_append.mp he with hel | her
      · have hrl1 : readCount e l = 1 := readCount_eq_one_of_mem e l hrl hel
        have hrr0 : readCount e r = 0 := by
          rw [readCount_eq_count, List.count_eq_zero_of_not_mem (hrdis hel)]
        have hvl1 : verifyCount e l = 1 := by
          have hle := hl.readCount_le_verifyCount
            (fun q => readCount_le_one q l hrl) e
          have hub := verifyCount_le_one e l hvl
          omega
        simp only [vaxis, Relaxis, if_pos hvl1, if_pos hrl1]
        exact ihl hrl hvl e hel
      · have hrl0 : readCount e l = 0 := by
          rw [readCount_eq_count,
            List.count_eq_zero_of_not_mem (fun hc => hrdis hc her)]
        have hvr1 : 1 ≤ verifyCount e r := by
          have hrr1 : readCount e r = 1 := readCount_eq_one_of_mem e r hrr her
          have hle := hr.readCount_le_verifyCount
            (fun q => readCount_le_one q r hrr) e
          omega
        have hvl0 : verifyCount e l = 0 := by
          by_contra hne
          have hmem_r : e ∈ verifyExps r := by
            rw [verifyCount_eq_count] at hvr1
            exact List.count_pos_iff.mp hvr1
          have hmem_l : e ∈ verifyExps l := by
            have : 0 < verifyCount e l := by omega
            rw [verifyCount_eq_count] at this
            exact List.count_pos_iff.mp this
          exact hvdis hmem_l hmem_r
        have hrl1 : readCount e l ≠ 1 := by omega
        have hvl1 : verifyCount e l ≠ 1 := by omega
        simp only [vaxis, Relaxis, if_neg hvl1, if_neg hrl1]
        exact ihr hrr hvr e her
  | @read n e' c s hs he hroot route below ih =>
      intro hrnd hvnd e hmem
      rw [readExps] at hrnd hmem
      rw [verifyExps] at hvnd
      rcases List.mem_cons.mp hmem with rfl | hec
      · obtain ⟨-, -, -, hax, hdep, hvaddr, -⟩ := route.spec
        have hpath : pathAxis (axisPath s.axis) = s.axis :=
          pathAxis_axisPath s.axis s.axis_pos
        have hrec : s.record.axis = (s.axis : K) := s.realization.axis_realizes
        simp only [vaxis, Relaxis, hax, hvaddr, hdep, if_pos]
        calc s.record.axis = ((s.axis : ℕ) : K) := hrec
          _ = ((pathAxis (axisPath s.axis) : ℕ) : K) := by rw [hpath]
          _ = (pathAddress (axisPath s.axis) : K) + (2 : K) ^ (axisPath s.axis).length := by
              simp [pathAxis, Nat.cast_add, Nat.cast_pow]
      · have hne : e' ≠ e := by
          intro hEq
          exact (List.nodup_cons.mp hrnd).1 (hEq ▸ hec)
        simp only [vaxis, Relaxis, if_neg hne]
        exact ih (List.nodup_cons.mp hrnd).2 hvnd e hec
  | @verify n e' a c below ih =>
      intro hrnd hvnd e hmem
      rw [readExps] at hrnd hmem
      rw [verifyExps] at hvnd
      have hne : e' ≠ e := by
        intro hEq
        subst hEq
        have hle := below.readCount_le_verifyCount
          (fun q => readCount_le_one q c hrnd) e'
        have hrc : 1 ≤ readCount e' c := by
          rw [readCount_eq_count]
          exact List.count_pos_iff.mpr hmem
        have hub : verifyCount e' (MTree.verify e' a c) ≤ 1 :=
          verifyCount_le_one e' _ (by rw [verifyExps]; exact hvnd)
        have hub' : 1 + verifyCount e' c ≤ 1 := by
          simpa [verifyCount] using hub
        omega
      simp only [vaxis, Relaxis, if_neg hne]
      exact ih hrnd (List.nodup_cons.mp hvnd).2 e hmem

end ServiceWalk

/-! ## E. The per-root exact service partition -/

/-- The exact semantic service partition of one actual root.

`recordPartition` is the literal emission list of this root's `read_root` rows; the two exponent
partitions are positionless permutations, matching the paper's LogUp `intermediate` multiset
rather than a traversal order.  An empty partition is legal: a supplied noun root may require only
decompose/halt validation.  No `[K]` index bound appears here
either: the `L_mIO` range is a property of the one global `intermediate` multiset and is carried by `ExactServedMemoryTrace`. -/
structure RootTrace
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) (i : Fin cfg.kMem) where
  subject : Noun
  services : List (Service cfg exec)
  /-- The service records are exactly the records emitted by `read_root` rows of this root. -/
  recordPartition :
    rootResponseRecords exec i = services.map Service.record
  readPartition :
    (readExps (exactAxisTree cfg exec i)).Perm (services.map Service.exponent)
  verifyPartition :
    (verifyExps (exactAxisTree cfg exec i)).Perm (services.map Service.exponent)
  traversal :
    ServiceWalk services subject (exactAxisTree cfg exec i)

/-! `RootTrace` also contains traversal services which need not be OP0/OP9 semantic lookups.
The coverage direction below is deliberately one-way: every row-level served lookup must occur in
the exact forest partition, while ordinary recursive traversal records may also occur there. -/

namespace RootTrace

variable {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}

/-- The exponent multiset carried by this root's services. -/
abbrev exponents (R : RootTrace cfg exec i) : List ℕ :=
  R.services.map Service.exponent

/-- The `z^i` timestamp multiset carried by this root's services. -/
abbrev timestampPowers (R : RootTrace cfg exec i) : List K :=
  R.exponents.map (fun e => cfg.challenges.α ^ e)

theorem support (R : RootTrace cfg exec i) (e : ℕ) :
    e ∈ readExps (exactAxisTree cfg exec i) ↔
      e ∈ verifyExps (exactAxisTree cfg exec i) := by
  rw [R.readPartition.mem_iff, R.verifyPartition.mem_iff]

/-- The walk supplies the noun reconstruction; it is not a field. -/
theorem nounShape (R : RootTrace cfg exec i) :
    NounShape R.subject (exactAxisTree cfg exec i) :=
  R.traversal.nounShape

/-- The walk supplies the ancestry primitive; it is not a field. -/
theorem readVerifyNested (R : RootTrace cfg exec i) :
    ReadVerifyNested (exactAxisTree cfg exec i) :=
  R.traversal.readVerifyNested

theorem readTimestamps_nodup (R : RootTrace cfg exec i)
    (hts : R.timestampPowers.Nodup) :
    ((readExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup :=
  ((R.readPartition.map _).nodup_iff).mpr hts

theorem verifyTimestamps_nodup (R : RootTrace cfg exec i)
    (hts : R.timestampPowers.Nodup) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup :=
  ((R.verifyPartition.map _).nodup_iff).mpr hts

theorem readExps_nodup (R : RootTrace cfg exec i)
    (hts : R.timestampPowers.Nodup) :
    (readExps (exactAxisTree cfg exec i)).Nodup :=
  Nock.AxisBridge.readExps_nodup_of_ts cfg.challenges.α _ (R.readTimestamps_nodup hts)

theorem verifyExps_nodup (R : RootTrace cfg exec i)
    (hts : R.timestampPowers.Nodup) :
    (verifyExps (exactAxisTree cfg exec i)).Nodup :=
  List.Nodup.of_map _ (R.verifyTimestamps_nodup hts)

/-- This root's read timestamp multiset is a permutation of its service timestamps. -/
theorem readTimestamps_perm (R : RootTrace cfg exec i) :
    ((readExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Perm R.timestampPowers :=
  R.readPartition.map _

/-- This root's verify timestamp multiset is a permutation of the same service timestamps. -/
theorem verifyTimestamps_perm (R : RootTrace cfg exec i) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Perm R.timestampPowers :=
  R.verifyPartition.map _

/-- Every used exponent's committed axis equals its topological axis.  This is derived from the
operational walk, not stored. -/
theorem axisValidity (R : RootTrace cfg exec i)
    (hts : R.timestampPowers.Nodup) (e : ℕ)
    (he : e ∈ readExps (exactAxisTree cfg exec i)) :
    vaxis e (exactAxisTree cfg exec i) =
      Relaxis e (exactAxisTree cfg exec i) :=
  R.traversal.axisValidity (R.readExps_nodup hts) (R.verifyExps_nodup hts) e he

end RootTrace

/-! ## F. The same-execution semantic memory CORE -/

/-- Same-execution semantic memory CORE.  It partitions every actual root into a recursively
walked, noun-indexed Nock service traversal and connects every OP0/OP9 `ServedNounLookup` from the
authoritative compute rows to one service in that partition.  The witness names no committed row
position in the memory multiset: `i` chooses a supplied forest root, and `ServiceWalk` recursively
follows the root noun/tree.

The two aggregate side conditions are carried here, explicitly, rather than in every `RootTrace`:

* `timestampPowersNodup` is the paper's global `z^i` uniqueness across the whole forest.  `exec.derivedRequestIO.Nodup` does not imply it, since distinct full
  records may share a timestamp, so it is a named premise rather than a silent assumption.
* `forestIndexRange` is the `[K]` index range of `L_mIO` applied once, to the
  one `intermediate`/IO multiset that the paper stores globally to the traversal.  It bounds
  the aggregate number of lookups over the whole forest; it says nothing about any individual root,
  so a record-free seeded root is legal both
  in `RootTrace` and here. -/
-- `D` stays on the executed `exec`.
structure ExactServedMemoryTrace
    (q Λ : ℕ) (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec)
    (execA : ExactExecution cfg) : Type where
  roots : ∀ i : Fin cfg.kMem, RootTrace cfg execA i
  timestampPowersNodup :
    ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).Nodup
  forestIndexRange :
    IO.InRange cfg.Ksz
      ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).length
  semanticCoverage :
    ∀ row : Fin cfg.compRows,
      ∀ lookup ∈ (D.rows row).needs.served,
        ∃ (i : Fin cfg.kMem) (s : Service cfg execA),
          s ∈ (roots i).services ∧
            s.record = lookup.record ∧
            s.root = lookup.root ∧
            s.child = lookup.child ∧
            s.axis = lookup.axis

namespace ExactServedMemoryTrace

variable {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
  {D : SemanticTrace.ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}

/-- Global uniqueness localizes to each root. -/
theorem rootTimestampPowersNodup (T : ExactServedMemoryTrace q Λ cfg exec D execA)
    (i : Fin cfg.kMem) : (T.roots i).timestampPowers.Nodup :=
  (sublist_flatMap_of_mem (l := List.finRange cfg.kMem)
    (f := fun j => (T.roots j).timestampPowers) (List.mem_finRange i)).nodup
    T.timestampPowersNodup

private theorem perm_flatMap_of_pointwise {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons b t ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (h b (by simp)).append (ih fun a ha => h a (by simp [ha]))

/-- The whole forest's `intermediate` request multiset is a permutation of the aggregate service
timestamp multiset. -/
theorem forestReadTimestamps_perm (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    (forestReadTimestamps cfg execA).Perm
      ((List.finRange cfg.kMem).flatMap (fun i => (T.roots i).timestampPowers)) :=
  perm_flatMap_of_pointwise fun i _ => (T.roots i).readTimestamps_perm

/-- The whole forest's `intermediate` response multiset is a permutation of the same aggregate
service timestamp multiset. -/
theorem forestVerifyTimestamps_perm (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    (forestVerifyTimestamps cfg execA).Perm
      ((List.finRange cfg.kMem).flatMap (fun i => (T.roots i).timestampPowers)) :=
  perm_flatMap_of_pointwise fun i _ => (T.roots i).verifyTimestamps_perm

/-- The paper's one global `intermediate` condition, discharged once on the aggregate multiset of
the whole forest.  the paper adds a `z^i` at every `read_root` row and the paper removes
it at the matching `verify_child` row; both sides are permutations of the same aggregate service
timestamp list, so the accumulator closes and its terminal value is zero.
The `[K]` index range is `forestIndexRange`, taken once on that aggregate list.  No root is required to carry a record. -/
theorem intermediateMatching
    [DecidableEq K] (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    IO.LmIO cfg.Ksz (forestReadTimestamps cfg execA) (forestVerifyTimestamps cfg execA) := by
  have hread := T.forestReadTimestamps_perm
  have hverify := T.forestVerifyTimestamps_perm
  rw [IO.LmIO_iff]
  refine ⟨?_, ?_, hverify.nodup_iff.2 T.timestampPowersNodup, ?_⟩
  · rw [hread.length_eq]; exact T.forestIndexRange
  · rw [hread.length_eq, hverify.length_eq]
  · rw [List.toFinset_eq_of_perm _ _ hread, List.toFinset_eq_of_perm _ _ hverify]

def axisStructural
    [Fintype K] [DecidableEq K]
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ExactAxisStructuralRefinement cfg execA where
  ancestry := fun i => (T.roots i).readVerifyNested
  read_timestamps_nodup := fun i =>
    (T.roots i).readTimestamps_nodup (T.rootTimestampPowersNodup i)
  intermediate_matching := T.intermediateMatching

def axisValidity
    [Fintype K] [DecidableEq K]
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ExactMemoryAxisValidity cfg execA :=
  fun i e hread _hverify =>
    (T.roots i).axisValidity (T.rootTimestampPowersNodup i) e hread

theorem support
    [Fintype K] [DecidableEq K]
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ∀ i e, e ∈ readExps (exactAxisTree cfg execA i) ↔
      e ∈ verifyExps (exactAxisTree cfg execA i) :=
  fun i => (T.roots i).support

def honestReconstruction
    [Fintype K] [DecidableEq K]
    (T : ExactServedMemoryTrace q Λ cfg exec D execA) :
    ExactMemoryHonestReconstruction cfg execA (fun i => (T.roots i).subject) :=
  fun i => ⟨(T.roots i).nounShape, (T.roots i).readVerifyNested⟩

end ExactServedMemoryTrace

end

end Nock.NockVMROM.Thm54.ServedMemoryTrace

#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.pathAxis_axisPath
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.slot_pathAxis
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.Service.axis_pos
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.spec
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.served
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.nounShape
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.readVerifyNested
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.intermediateMatching
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisStructural
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.axisValidity
#print axioms Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace.support
