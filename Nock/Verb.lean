/-
  Nock/Verb.lean

  The paper's *strengthened* executable data object — the **verb** — together with the
  strict traversal order (`map`/`getIndex`, DFS), the *computable opcode domain* `D`, and
  the single-step Nock transition function..

  ────────────────────────────────────────────────────────────────────────────────────
  ENCODING CHOICES (faithfulness notes — flagged for the author):

  1. `Verb` as an *annotated tree*.  The paper defines a verb as a
     pair `(actions, noun)` where `noun` has `λ` leaves and `actions` is a `(λ-1)`-array
     over `X ∪ {*, ⊥}` indexed by the *internal* nodes of the tree via `map` (DFS).  A
     `(λ-1)`-array indexed by the internal nodes is *isomorphic* to labelling every cell
     of the noun with one action; we take that isomorphic inductive presentation as
     primary (`Verb.leaf`/`Verb.node`).  `Verb.noun` forgets the labels.

  2. FULL alphabet `X ∪ {*, ⊥}` with `X = ⟨?,=,/,#,-⟩`.  The opcodes whose
     rewrite leaves an operator pending on a sub-computation
       OP₀ → `/`(slot),  OP₃ → `-[3,·]`(=`?`),  OP₄ → `-[4,·]`(=`+`),
       OP₅ → `=`,        OP₁₀ → `#`(edit)
     produce a node labelled with the corresponding operator; a *later* transition step
     applies that operator once its argument sub-noun is terminal.

     The paper never lets `?`/`+` label a node directly: OP₃/OP₄ route them
         through the *binary* ordering operator `-`, i.e.
         `-[3,x] = ?(x)`, `-[4,x] = +(x)`.  We follow this verbatim.  Hence `Action.wut`
         (`?`) is in the alphabet for fidelity to `X` but is NEVER produced by the
         transition function; `+` is not an `Action` at all (it is only reached inside
         `-[4,·]`).  `reduce` maps a stray `?`-node to ⊥ (documented, unreachable).
     (b) App A's Transition-Function algorithm is written ONLY for the
         opcode form `*[n₁,[i,n₂]]`; it has no branch for a pending *operator* node.  The
         paper's `getIndex`, however, selects the deepest-rightmost
         *non-null* action — which includes operators.  We resolve this by making an
         operator-application a genuine transition step (as the task directs): when the
         selected node carries an operator and its argument subtree is terminal, apply the
         operator (App A Algorithms 2/3) and splice the resulting noun back.  This is the
         faithful completion of the elided operator steps.
     (c) Consequently the computable domain `D` is
         preserved verbatim as `inOpcodeDomain`; the guard actually used by the transition
         function `next` is `inDomain := inOpcodeDomain ∨ opReady`, the full domain of
         `next` (opcode redexes ∪ ready-operator nodes).  `Lem:domain`'s Lean form
         (`Trace.domain`) therefore concludes membership in this transition domain.

  3. `map = DFS`.  Internal nodes are indexed by DFS pre-order (root 0,
     then the whole left subtree, then the whole right subtree).  `getIndex` = argmax of the
     pre-order *index* among pending (non-⊥) internal nodes.

     What is (and is NOT) claimed.  The paper allows "*any* total ordering" for `getIndex` and notes the specific choice does not affect the formal properties.  The ONLY property the determinism theorem needs is that the order is
     *strict* (a strict total order), so that the argmax is unique.  The DFS pre-order gives
     *distinct* indices to distinct internal nodes (`enum_index_range` / `map_of_mem_nodes`),
     and `Nat.lt` is a strict total order on them, so `map = DFS` "enforces a strict
     ordering" — see `strictSelect_dfs`, and `next_eq_some_iff` for how this
     makes `deterministic_Trace` an instance of the paper's conditional theorem.

     We do NOT claim the pre-order argmax coincides with the paper's *illustrative*
     "largest depth, deepest-rightmost" ordering — in general it does not (a shallow node in
     the right subtree can receive a larger pre-order index than a deep node in the left
     subtree).  That illustrative ordering is not load-bearing anywhere; only strictness is.
  ────────────────────────────────────────────────────────────────────────────────────
-/

import Nock.Tree
import Nock.Reference

namespace Nock

/-- A pending action labelling an internal node.
    `null` = `⊥` (nothing pending), `star` = `*` (a pending Nock opcode transition), and
    the operator alphabet `X = ⟨?,=,/,#,-⟩`: `wut`=`?`, `equal`=`=`, `slot`=`/`, `edit`=`#`,
    `minus`=`-`.  (`+`/`lus` is not in `X`: it is reached only inside
    `-[4,·]`, see note 2a.  `wut` is in `X` for fidelity but is not produced by the
    transition function, see note 2a.) -/
inductive Action where
  | null    -- ⊥
  | star    -- *
  | wut     -- ?
  | equal   -- =
  | slot    -- /
  | edit    -- #
  | minus   -- -
deriving Repr, DecidableEq, Inhabited

/-- Is an action the null element `⊥`? -/
def Action.isNull : Action → Bool
  | .null => true
  | _     => false

/-- Is an action one of the operators in `X` (as opposed to `⊥` or `*`)? -/
def Action.isOperator : Action → Bool
  | .null => false
  | .star => false
  | _     => true

-- the paper`, presented as an action-annotated tree)
/-- A **verb**: an action-annotated proper binary tree.  A `leaf` carries an atom (`Nat`);
    a `node` carries an `Action` (the entry of the `actions` array for that internal node)
    together with its two child verbs. -/
inductive Verb where
  | leaf : Nat → Verb
  | node : Action → Verb → Verb → Verb
deriving Repr, DecidableEq, Inhabited

namespace Verb

/-- The underlying noun (`snd` of the verb pair): forget the action labels. -/
def noun : Verb → Noun
  | .leaf n     => .atom n
  | .node _ l r => .cell l.noun r.noun

/-- Number of leaves `λ` of the verb's noun. -/
def leaves : Verb → Nat
  | .leaf _     => 1
  | .node _ l r => l.leaves + r.leaves

/-- `type`: is the underlying noun a cell? -/
def isCell : Verb → Bool
  | .node _ _ _ => true
  | .leaf _     => false

/-- Root action, if the verb is a cell (`none` at a leaf — leaves carry no action). -/
def rootAction : Verb → Option Action
  | .node a _ _ => some a
  | .leaf _     => none

/-- Is the root action a pending `*`? -/
def isStar : Verb → Bool
  | .node .star _ _ => true
  | _               => false

/-- Does the root node carry a *pending* (non-`⊥`) action?  `*` or any operator counts;
    a leaf or a `⊥`-node does not. -/
def isPending : Verb → Bool
  | .node a _ _ => !a.isNull
  | .leaf _     => false

/-- **Terminal / fully-executed**: no pending action (`*` or operator) anywhere. -/
def isTerminal : Verb → Bool
  | .leaf _     => true
  | .node a l r => a.isNull && isTerminal l && isTerminal r

/-! ### `map` and `getIndex` — the DFS traversal order -/

/-- `enum v c` performs a DFS pre-order walk of `v` starting the index counter at `c`,
    returning the final counter and the list of `(index, subverb)` pairs for every
    *internal* node (cells only; leaves are excluded, as in the paper). -/
def enum : Verb → Nat → Nat × List (Nat × Verb)
  | .leaf _,     c => (c, [])
  | .node a l r, c =>
      let e1 := enum l (c + 1)
      let e2 := enum r e1.1
      (e2.1, (c, .node a l r) :: (e1.2 ++ e2.2))

/-- All `(index, subverb)` pairs of internal nodes, in DFS pre-order. -/
def nodes (v : Verb) : List (Nat × Verb) := (enum v 0).2

def findAt : Nat → List (Nat × Verb) → Option Verb
  | _, []          => none
  | i, (j, v) :: t => if i = j then some v else findAt i t

-- the paper` : the subverb at internal-node index `i`)
/-- The paper's `map` (a.k.a. `DFS`): the subverb at DFS internal-node index `i`. -/
def map (i : Nat) (v : Verb) : Option Verb := findAt i (nodes v)

private def maxPendingIdx : List (Nat × Verb) → Option Nat
  | []          => none
  | (i, v) :: t =>
      let rest := maxPendingIdx t
      if v.isPending then
        some (match rest with | none => i | some j => Nat.max i j)
      else rest

-- the paper = argmax_{map(i,F) pending} i`)
/-- `getIndex F`: the largest DFS pre-order index of an internal node with a *pending* (non-⊥)
    action (a `*` opcode or an operator awaiting its arguments).  This is the argmax under
    the DFS index order, which is a strict total order (`strictSelect_dfs`); it is NOT in
    general the "deepest/rightmost" node (see note 3).  `none` iff `F` is terminal. -/
def getIndex (v : Verb) : Option Nat := maxPendingIdx (nodes v)

/-- Rebuild `v`, replacing the internal node at DFS index `i` by `new`. -/
def replaceAux (i : Nat) (new : Verb) : Verb → Nat → Nat × Verb
  | .leaf n,     c => (c, .leaf n)
  | .node a l r, c =>
      let e1 := replaceAux i new l (c + 1)
      let e2 := replaceAux i new r e1.1
      (e2.1, if c = i then new else .node a e1.2 e2.2)

/-- Splice: replace the subverb at DFS index `i` with `new`. -/
def replaceAt (i : Nat) (v new : Verb) : Verb := (replaceAux i new v 0).2

/-! ### The computable opcode domain `D` -/

/-- `type(i) = atom ∧ i ∈ [11]`, or `type(i) = cell` (⇒ the `cons` opcode). -/
def opHeadOk : Verb → Bool
  | .leaf k     => k < 11
  | .node _ _ _ => true

/-- The paper's **computable opcode domain** `D(V)`: verbs
    `v = *[n₁, [i, n₂]]` with `n₁,[i,n₂]` in terminal state and `i` either an atom in
    `[11]` or a cell.  These are exactly the redexes on which an *opcode* fires without
    any recursive call to `*`.  Operator-application steps are *not* in
    `D` (they are covered by `opReady`); see note 2c. -/
def inOpcodeDomain : Verb → Bool
  | .node .star n1 (.node ra i n2) =>
      isTerminal n1
        && ra.isNull
        && isTerminal i && isTerminal n2 && opHeadOk i
  | _ => false

/-- A node ready for an **operator-application step**: it carries an operator from `X`
    and both of its argument subtrees are already in terminal state (note 2b).  These are
    the operator redexes that the paper's App A transition algorithm elides. -/
def opReady : Verb → Bool
  | .node a l r => a.isOperator && isTerminal l && isTerminal r
  | .leaf _     => false

/-- The full domain of the transition function `next`: opcode redexes (`inOpcodeDomain`,
    = the paper's `D`) together with ready operator nodes (`opReady`).  See note 2c;
    `Trace.domain` (`Lem:domain`) concludes membership here. -/
def inDomain (v : Verb) : Bool := inOpcodeDomain v || opReady v

/-! ### The opcode local rewrite

    `redex` is the local, non-recursive opcode rewrite applied to a `*`-redex in `D`.  It
    is a *deterministic partial function*.  All of OP₀..OP₁₀ + `cons` are
    implemented, matching the transition function exactly; opcodes
    that spawn an operator produce the corresponding operator-labelled node, whose
    argument is a (possibly still-`*`-pending) sub-computation. -/
def redex : Verb → Option Verb
  | .node .star n1 (.node _ i n2) =>
      match i with
      | .node _ _ _ =>                                  -- the paper cons (type(i)=cell)
          some (.node .null (.node .star n1 i) (.node .star n1 n2))
      | .leaf op =>
          match op with
          | 0 =>                                        -- the paperOP₀ : → /(n₂,n₁)
              some (.node .slot n2 n1)
          | 1 => some n2                                -- the paperOP₁ : → n₂
          | 2 => match n2 with                          -- the paperOP₂ : → *[*[n₁,h],*[n₁,t]]
                 | .node _ b c =>
                     some (.node .star (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 3 =>                                        -- the paperOP₃ : → -[3, *[n₁,n₂]] = ?(*[n₁,n₂])
              some (.node .minus (.leaf 3) (.node .star n1 n2))
          | 4 =>                                        -- the paperOP₄ : → -[4, *[n₁,n₂]] = +(*[n₁,n₂])
              some (.node .minus (.leaf 4) (.node .star n1 n2))
          | 5 => match n2 with                          -- the paperOP₅ : → =(*[n₁,h],*[n₁,t])
                 | .node _ b c =>
                     some (.node .equal (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 6 => match n2 with                          -- the paperOP₆ (if-then-else macro)
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂);
                     -- → *[n₁, *[c, [0, *[[2,3], [0, *[n₁,[4,[4,b]]]]]]]]
                     let inner := Verb.node .star n1
                                    (.node .null (.leaf 4) (.node .null (.leaf 4) b))
                     let d0    := Verb.node .null (.leaf 0) inner
                     let c0    := Verb.node .star (.node .null (.leaf 2) (.leaf 3)) d0
                     let b0    := Verb.node .null (.leaf 0) c0
                     let a0    := Verb.node .star c b0
                     some (.node .star n1 a0)
                 | _ => none
          | 7 => match n2 with                          -- the paperOP₇ : → *[*[n₁,h],t]
                 | .node _ b c => some (.node .star (.node .star n1 b) c)
                 | _ => none
          | 8 => match n2 with                          -- the paperOP₈ : → *[[*[n₁,h],n₁],t]
                 | .node _ b c =>
                     some (.node .star (.node .null (.node .star n1 b) n1) c)
                 | _ => none
          | 9 => match n2 with                          -- the paperOP₉ : → *[*[n₁,t], 2, [[0,1],0,h]]
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂)
                     let core := Verb.node .star n1 c
                     let f01  := Verb.node .null (.leaf 0) (.leaf 1)
                     let f0h  := Verb.node .null (.leaf 0) b
                     let form := Verb.node .null (.leaf 2) (.node .null f01 f0h)
                     some (.node .star core form)
                 | _ => none
          | 10 => match n2 with                         -- the paperOP₁₀ : → #[hh(n₂), *[n₁,th(n₂)], *[n₁,t(n₂)]]
                  | .node _ hd d =>
                      match hd with
                      | .node _ ax c =>
                          some (.node .edit ax
                                  (.node .null (.node .star n1 c) (.node .star n1 d)))
                      | _ => none
                  | _ => none
          | _ => none                                   -- i ∉ [11] ⇒ crash
  | _ => none

/-! ### Operator-application steps

    When the selected node carries an operator from `X` and its argument subtrees are
    terminal, the transition applies the operator to the underlying noun(s) (`Nock.Noun`
    operators, `Reference.lean`, which mirror App A Algorithms 2/3) and yields a terminal
    noun-verb.  ⊥ (crash) is `none`. -/

/-- Convert a plain noun into a *terminal* verb (all actions `⊥`). -/
def ofNoun : Noun → Verb
  | .atom k   => .leaf k
  | .cell l r => .node .null (ofNoun l) (ofNoun r)

/-! ### The Nock transition function `*` -/

/-- The local rewrite of the redex selected by `getIndex`: an opcode step on a `*`-node
    (`redex`), or an operator-application step on an operator node (App A).  A `⊥`-node or
    leaf is never selected (not pending) so maps to `none`. -/
def reduce : Verb → Option Verb
  | .node .star n1 t     => redex (.node .star n1 t)                    -- opcode step
  | .node .equal l r     => some (ofNoun (Noun.tis l.noun r.noun))      -- the paper=
  | .node .slot l r      =>                                             -- the paper/
      match l.noun with
      | .atom ax => (Noun.slot ax r.noun).map ofNoun
      | _        => none
  | .node .edit l r      =>                                             -- the paper#
      match l.noun, r with
      | .atom ax, .node _ nw od => (Noun.edit ax nw.noun od.noun).map ofNoun
      | _,        _             => none
  | .node .minus l r     =>
      match l.noun with
      | .atom 3 => some (ofNoun (Noun.wut r.noun))                      -- -[3,·] = ?(·)
      | .atom 4 => (Noun.lus r.noun).map ofNoun                         -- -[4,·] = +(·)
      | _       => none
  | .node .wut _ _       => none                                        -- unreachable, see note 2a
  | .node .null _ _      => none
  | .leaf _              => none

/-- One Nock step.  Locate the pending redex of largest DFS index via `getIndex`/`map`; if it
    lies in the transition domain `D` (opcode redex or ready operator), apply the local
    rewrite (`reduce`) and splice the result back; otherwise crash (`none`).
    `next v = none` also when `v` is terminal (no pending action).  Being a Lean function,
    `next` is deterministic — the concrete realization of the paper's "`*` is a
    deterministic mapping between program states". -/
def next (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduce sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none


/-- The initial program verb `F = *[subject, formula]`: a `*` action on the root over the
    terminal noun `[subject, formula]`. -/
def program (subject formula : Noun) : Verb :=
  .node .star (ofNoun subject) (ofNoun formula)

/-- Extract the observable output of a stuck verb: its underlying noun if it is in terminal
    state, else `none`. -/
def result (v : Verb) : Option Noun :=
  if v.isTerminal then some v.noun else none

/-- Fuel-indexed iteration of `next` from `v` to a terminal/⊥ state, returning the result
    noun (`none` on crash or fuel exhaustion).  Nock is Turing-complete, so fuel is
    required for totality; `none` conflates a genuine crash with fuel exhaustion, exactly
    as `evalN` does. -/
def run : Nat → Verb → Option Noun
  | 0,        _ => none
  | fuel + 1, v =>
      match next v with
      | some v' => run fuel v'
      | none    => result v

/-- Run a Nock program `*[subject, formula]` through the paper's small-step interpreter. -/
def runProgram (fuel : Nat) (subject formula : Noun) : Option Noun :=
  run fuel (program subject formula)

/-! ### Strictness of the DFS order -/

/-- The DFS counter never decreases: `(enum v c).1 ≥ c`. -/
theorem enum_ge_start (v : Verb) (c : Nat) : c ≤ (enum v c).1 := by
  induction v generalizing c with
  | leaf n => simp [enum]
  | node a l r ihl ihr =>
      simp only [enum]
      have h1 : c + 1 ≤ (enum l (c + 1)).1 := ihl (c + 1)
      have h2 : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := ihr _
      omega

/-- Every internal-node index produced by `enum v c` lies in the half-open counter range
    `[c, (enum v c).1)`.  Distinct nodes therefore receive distinct indices: the DFS
    `map` enforces a *strict* ordering on subtrees. -/
theorem enum_index_range (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, c ≤ p.1 ∧ p.1 < (enum v c).1 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      have hrge : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := enum_ge_start r _
      rcases hp with hroot | hleft | hright
      · subst hroot; simp only [enum]; omega
      · have := ihl (c + 1) p hleft
        simp only [enum]; omega
      · have := ihr (enum l (c + 1)).1 p hright
        simp only [enum]; omega

/-! ### DFS indices are *distinct* — the concrete strictness of `map`

    `enum_index_range` (disjoint index ranges for disjoint subtrees) is exactly what makes
    the DFS pre-order assign a *distinct* index to every internal node.  The lemma
    `map_of_mem_nodes` below turns that distinctness into the statement that
    `map i` retrieves the *unique* subverb carrying index `i`.  This is where
    `enum_index_range` becomes load-bearing (see `getIndex_eq_some_iff`): distinct indices
    ⇒ the argmax over indices names a *unique* node ⇒ `map`/`replaceAt` target that node. -/

/-- `findAt` over an append: the left list wins if it has a match. -/
theorem findAt_append (i : Nat) :
    ∀ (L1 L2 : List (Nat × Verb)),
      findAt i (L1 ++ L2) = match findAt i L1 with
                            | some v => some v
                            | none   => findAt i L2
  | [],            L2 => by simp [findAt]
  | (j, w) :: t, L2 => by
      simp only [List.cons_append, findAt]
      by_cases h : i = j
      · simp [h]
      · simp only [if_neg h]; exact findAt_append i t L2

/-- If no pair in `L` carries index `i`, then `findAt i L = none`. -/
theorem findAt_eq_none {i : Nat} :
    ∀ {L : List (Nat × Verb)}, (∀ p ∈ L, p.1 ≠ i) → findAt i L = none
  | [],            _ => rfl
  | (j, w) :: t, h => by
      have hj : ¬ (i = j) := fun heq => (h (j, w) (by simp)) heq.symm
      simp only [findAt, if_neg hj]
      exact findAt_eq_none (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- `findAt i L = some v` witnesses membership `(i, v) ∈ L`. -/
theorem findAt_some_mem {i : Nat} {v : Verb} :
    ∀ {L : List (Nat × Verb)}, findAt i L = some v → (i, v) ∈ L
  | [],            h => by simp [findAt] at h
  | (j, w) :: t, h => by
      simp only [findAt] at h
      split at h
      · rename_i hij
        subst hij
        obtain rfl := Option.some.inj h
        simp
      · exact List.mem_cons_of_mem _ (findAt_some_mem h)

/-- **DFS distinctness (core).**  Every pair produced by `enum` is recovered by `findAt` on
    its own index: the index ranges of the two subtrees (`enum_index_range`) are disjoint
    from each other and from the root counter, so no two pairs share an index. -/
private theorem enum_findAt (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, findAt p.1 (enum v c).2 = some p.2 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      simp only [enum, findAt]
      rcases hp with hroot | hleft | hright
      · subst hroot; simp
      · have hb := enum_index_range l (c + 1) p hleft
        have hpc : p.1 ≠ c := by omega
        rw [if_neg hpc, findAt_append]
        rw [ihl (c + 1) p hleft]
      · have hb := enum_index_range r (enum l (c + 1)).1 p hright
        have hpc : p.1 ≠ c := by omega
        rw [if_neg hpc, findAt_append]
        have hnone : findAt p.1 (enum l (c + 1)).2 = none := by
          apply findAt_eq_none
          intro q hq
          have := enum_index_range l (c + 1) q hq
          omega
        rw [hnone]
        exact ihr (enum l (c + 1)).1 p hright

/-- **`map` retrieves the unique node at an index.**  If `(i, v)` is one of the DFS
    internal-node pairs of `a`, then `map i a = some v`.  (Uses DFS distinctness,
    `enum_findAt`.) -/
theorem map_of_mem_nodes {a : Verb} {i : Nat} {v : Verb}
    (h : (i, v) ∈ nodes a) : map i a = some v :=
  enum_findAt a 0 (i, v) h

/-- Membership of the retrieved node: `map i a = some v ⇒ (i, v) ∈ nodes a`. -/
theorem mem_nodes_of_map {a : Verb} {i : Nat} {v : Verb}
    (h : map i a = some v) : (i, v) ∈ nodes a :=
  findAt_some_mem h

/-! ### `getIndex` = numeric argmax of pending indices (spec of `maxPendingIdx`) -/

/-- `maxPendingIdx L = none` iff no pair in `L` has a pending action. -/
private theorem maxPendingIdx_eq_none :
    ∀ {L : List (Nat × Verb)},
      maxPendingIdx L = none ↔ ∀ p ∈ L, p.2.isPending = false
  | [] => by simp [maxPendingIdx]
  | (i, w) :: t => by
      simp only [maxPendingIdx]
      by_cases hw : w.isPending = true
      · rw [if_pos hw]
        constructor
        · intro h; cases maxPendingIdx t <;> simp at h
        · intro h; exact absurd (h (i, w) (by simp)) (by simp [hw])
      · rw [if_neg hw]
        rw [maxPendingIdx_eq_none]
        constructor
        · intro h p hp
          rcases List.mem_cons.1 hp with heq | hmem
          · subst heq; simpa using hw
          · exact h p hmem
        · intro h p hp; exact h p (List.mem_cons_of_mem _ hp)

/-- The numeric argmax is achieved: `maxPendingIdx L = some i` names a pending pair at `i`. -/
private theorem maxPendingIdx_mem :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maxPendingIdx L = some i → ∃ v, (i, v) ∈ L ∧ v.isPending = true
  | [], i, h => by simp [maxPendingIdx] at h
  | (j, w) :: t, i, h => by
      simp only [maxPendingIdx] at h
      by_cases hw : w.isPending = true
      · rw [if_pos hw] at h
        cases hr : maxPendingIdx t with
        | none => rw [hr] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨w, by simp, hw⟩
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max j k = i
            rcases Nat.le_total j k with hjk | hkj
            · have hmx : Nat.max j k = k := Nat.max_eq_right hjk
              have hik : i = k := hmx ▸ h.symm
              subst hik
              obtain ⟨v, hv, hvp⟩ := maxPendingIdx_mem hr
              exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩
            · have hmx : Nat.max j k = j := Nat.max_eq_left hkj
              have hij : i = j := hmx ▸ h.symm
              subst hij
              exact ⟨w, by simp, hw⟩
      · rw [if_neg hw] at h
        obtain ⟨v, hv, hvp⟩ := maxPendingIdx_mem h
        exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩

/-- Every pending index is `≤` the numeric argmax. -/
private theorem maxPendingIdx_ge :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maxPendingIdx L = some i → ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i
  | [], i, h => by simp [maxPendingIdx] at h
  | (p, w) :: t, i, h => by
      intro j v hmem hvp
      simp only [maxPendingIdx] at h
      by_cases hw : w.isPending = true
      · rw [if_pos hw] at h
        cases hr : maxPendingIdx t with
        | none =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : p = i
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq; have hjp := heq.1; omega
            · have hnone := (maxPendingIdx_eq_none).1 hr
              exact absurd (hnone (j, v) hmem') (by simp [hvp])
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max p k = i  (kept as an opaque atom for omega)
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq
              have hjp : j = p := heq.1
              have hle : p ≤ Nat.max p k := Nat.le_max_left p k; omega
            · have hjk := maxPendingIdx_ge hr j v hmem' hvp
              have hle : k ≤ Nat.max p k := Nat.le_max_right p k; omega
      · rw [if_neg hw] at h
        rcases List.mem_cons.1 hmem with heq | hmem'
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨_, rfl⟩ := heq; simp [hvp] at hw
        · exact maxPendingIdx_ge h j v hmem' hvp

/-- Characterization of the numeric argmax: if `(i, v)` is pending and no pending index
    exceeds `i`, then `maxPendingIdx L = some i`. -/
private theorem maxPendingIdx_of {L : List (Nat × Verb)} {i : Nat}
    (hmem : ∃ v, (i, v) ∈ L ∧ v.isPending = true)
    (hmax : ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i) :
    maxPendingIdx L = some i := by
  obtain ⟨v, hv, hvp⟩ := hmem
  cases hm : maxPendingIdx L with
  | none =>
      have hnone := (maxPendingIdx_eq_none).1 hm
      exact absurd (hnone (i, v) hv) (by simp [hvp])
  | some m =>
      obtain ⟨w, hw, hwp⟩ := maxPendingIdx_mem hm
      have h1 : m ≤ i := hmax m w hw hwp
      have h2 : i ≤ m := maxPendingIdx_ge hm i v hv hvp
      have : m = i := by omega
      rw [this]

/-! ### The paper's real content: a *strict* redex-selection order

    The paper defines a redex order `>_F` on the subtrees of a verb, induced by `map`.  `getIndex` is the `argmax` under this order,
    and `Thm:deterministic_Trace` is *conditional*: **if** `map` enforces a
    *strict* ordering, then a finite verb has at most one consistent trace of each size.

    We mechanize this faithfully by abstracting over the order.  A redex-selection step
    (`SelStep`) rewrites *a* maximal pending redex; when the order is a strict total order
    (`StrictSelect`), the maximal redex is **unique**, so the step is
    deterministic.  Strictness is load-bearing: `SelStep.det` uses `total` essentially, and
    without it `SelStep` is genuinely multi-valued. -/

/-- A **strict selection order** on internal-node indices: a strict total order.  Irreflexive + transitive ⇒ asymmetric; `total`
    (connectedness) is what forbids ties, hence forces a *unique* maximum. -/
structure StrictSelect (lt : Nat → Nat → Prop) : Prop where
  irrefl : ∀ i, ¬ lt i i
  trans  : ∀ {i j k}, lt i j → lt j k → lt i k
  total  : ∀ {i j}, i ≠ j → lt i j ∨ lt j i

/-- `i` is a *pending* internal-node index of `a`: `map i a` is a node with a pending
    (non-⊥) action. -/
def IsPendingIdx (a : Verb) (i : Nat) : Prop :=
  ∃ v, map i a = some v ∧ v.isPending = true

/-- `i` is a **maximal** pending index of `a` under the order `lt`: a pending index that no
    other pending index exceeds.  This is the paper's `argmax` characterization of
    `getIndex`. -/
def IsMaxPending (lt : Nat → Nat → Prop) (a : Verb) (i : Nat) : Prop :=
  IsPendingIdx a i ∧ ∀ j, IsPendingIdx a j → ¬ lt i j

/-- An **abstract redex-selection step**: pick a maximal pending index `i` under `lt`, and
    if the selected subverb is in the transition domain, apply the local rewrite and splice
    it back.  With no strictness assumption this relation can be multi-valued (several
    maximal redexes); `SelStep.det` shows a *strict* order collapses it to a function. -/
def SelStep (lt : Nat → Nat → Prop) (a b : Verb) : Prop :=
  ∃ i sub r, IsMaxPending lt a i ∧ map i a = some sub ∧ inDomain sub = true
             ∧ reduce sub = some r ∧ b = replaceAt i a r

/-- **Determinism from strictness.**  If `lt` is a strict total order, a redex-selection
    step is deterministic.  The strictness hypothesis is *load-bearing*: `hs.total` is what
    forces the two selected indices to coincide; the rest is functionality of
    `map`/`reduce`/`replaceAt`. -/
theorem SelStep.det {lt : Nat → Nat → Prop} (hs : StrictSelect lt) {a b b' : Verb}
    (h : SelStep lt a b) (h' : SelStep lt a b') : b = b' := by
  obtain ⟨i, sub, r, ⟨hip, hmax⟩, hmap, _, hred, hb⟩ := h
  obtain ⟨i', sub', r', ⟨hip', hmax'⟩, hmap', _, hred', hb'⟩ := h'
  have hii : i = i' := by
    rcases Classical.em (i = i') with heq | hne
    · exact heq
    · rcases hs.total hne with hlt | hlt
      · exact absurd hlt (hmax i' hip')
      · exact absurd hlt (hmax' i hip)
  subst hii
  have hsub : sub = sub' := Option.some.inj (hmap.symm.trans hmap')
  subst hsub
  have hr : r = r' := Option.some.inj (hred.symm.trans hred')
  subst hr
  exact hb.trans hb'.symm

/-! ### DFS instantiation: the concrete order is strict, and `next` realizes `SelStep` -/

/-- The concrete DFS order on pre-order indices is the usual strict order on `Nat`. -/
abbrev dfsLt : Nat → Nat → Prop := (· < ·)

/-- The DFS index order is a strict total order.  This is *why* `map = DFS` "enforces a
    strict ordering on subtrees": distinct internal nodes get distinct `Nat`
    indices (`enum_index_range`/`map_of_mem_nodes`), and `Nat.lt` is a strict total order. -/
theorem strictSelect_dfs : StrictSelect dfsLt where
  irrefl i := Nat.lt_irrefl i
  trans h h' := Nat.lt_trans h h'
  total hne := Nat.lt_or_gt_of_ne hne

/-- Pending-index membership, in list form.  The `←` direction is where DFS distinctness
    (`map_of_mem_nodes`) is load-bearing: a pending node in the `nodes` list is retrieved by
    `map` on its (unique) index. -/
theorem isPendingIdx_iff_mem {a : Verb} {i : Nat} :
    IsPendingIdx a i ↔ ∃ v, (i, v) ∈ nodes a ∧ v.isPending = true := by
  constructor
  · rintro ⟨v, hmap, hp⟩; exact ⟨v, mem_nodes_of_map hmap, hp⟩
  · rintro ⟨v, hmem, hp⟩; exact ⟨v, map_of_mem_nodes hmem, hp⟩

/-- `getIndex` is exactly the DFS argmax: `getIndex a = some i ↔ i` is the maximal pending
    index under `dfsLt`.  (Combines the `maxPendingIdx` spec with DFS distinctness.) -/
theorem getIndex_eq_some_iff {a : Verb} {i : Nat} :
    getIndex a = some i ↔ IsMaxPending dfsLt a i := by
  unfold getIndex IsMaxPending dfsLt
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv, hvp⟩ := maxPendingIdx_mem h
      exact isPendingIdx_iff_mem.2 ⟨v, hv, hvp⟩
    · intro j hj
      rw [Nat.not_lt]
      obtain ⟨w, hw, hwp⟩ := isPendingIdx_iff_mem.1 hj
      exact maxPendingIdx_ge h j w hw hwp
  · rintro ⟨hip, hmax⟩
    obtain ⟨v, hv, hvp⟩ := isPendingIdx_iff_mem.1 hip
    apply maxPendingIdx_of ⟨v, hv, hvp⟩
    intro j w hjw hwp
    have hj : IsPendingIdx a j := isPendingIdx_iff_mem.2 ⟨w, hjw, hwp⟩
    have := hmax j hj
    omega

/-- **`next` faithfully realizes the strict DFS selection step.**  This is the bridge that
    makes `deterministic_Trace` an instance of the paper's conditional theorem: the concrete
    interpreter's step is `SelStep` for the (strict) DFS order. -/
theorem next_eq_some_iff {a b : Verb} : next a = some b ↔ SelStep dfsLt a b := by
  constructor
  · intro h
    unfold next at h
    split at h
    · simp at h
    · rename_i i hgi
      split at h
      · simp at h
      · rename_i sub hmap
        split at h
        · rename_i hdom
          split at h
          · rename_i r hred
            exact ⟨i, sub, r, getIndex_eq_some_iff.1 hgi, hmap, hdom, hred, (Option.some.inj h).symm⟩
          · simp at h
        · simp at h
  · rintro ⟨i, sub, r, hmax, hmap, hdom, hred, hb⟩
    have hgi : getIndex a = some i := getIndex_eq_some_iff.2 hmax
    unfold next
    simp only [hgi, hmap, hdom, hred, if_true]
    rw [hb]

/-! ### Strictness is load-bearing: without it, `SelStep` is genuinely multi-valued

    The following witnesses that the strictness hypothesis of `SelStep.det` is *essential*, not decorative: for a
    non-strict order (here the empty relation, which fails `total`), the very same
    `SelStep` relation sends one verb to two *distinct* successors — because a verb can have
    two independent maximal pending redexes.  Strictness is exactly what rules this out. -/

/-- The empty order — *not* total, hence not a `StrictSelect`.  Every index is vacuously
    maximal under it. -/
def emptyLt : Nat → Nat → Prop := fun _ _ => False

/-- A verb with two independent, equally-maximal redexes: two copies of `*[0, [1, 5]]`
    (each an `OP₁` redex reducing to `5`), spliced under a `⊥` root. -/
def twoRedex : Verb :=
  .node .null
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))

/-- **Non-vacuity of strictness.**  Under a non-strict order, `SelStep` is not a function:
    it relates `twoRedex` to two distinct successors.  Contrast `SelStep.det`, which uses
    `StrictSelect.total` to collapse exactly this ambiguity. -/
theorem selStep_multivalued_without_strictness :
    ∃ (a b b' : Verb), b ≠ b' ∧ SelStep emptyLt a b ∧ SelStep emptyLt a b' := by
  refine ⟨twoRedex, replaceAt 1 twoRedex (.leaf 5), replaceAt 3 twoRedex (.leaf 5), by decide,
    ⟨1, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩,
    ⟨3, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩⟩

/-! ### Terminal verbs cannot step (`getIndex`/`next` bottom out on terminal state)

    A verb in *terminal* state has no pending
    internal node, so `getIndex` yields `none` and both transition functions (`next` and the
    ROM restriction `nextROM` below) return `none`.  This is the "`tₙ` in terminal state" halting
    condition of the paper's completeness clause. -/

/-- Every internal node produced by `enum` of a *terminal* verb is non-pending. -/
theorem enum_nonpending_of_terminal : ∀ (v : Verb), isTerminal v = true →
    ∀ (c : Nat), ∀ p ∈ (enum v c).2, p.2.isPending = false := by
  intro v
  induction v with
  | leaf n => intro _ c p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro h c p hp
      simp only [isTerminal, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; simp [isPending, ha]
      · exact ihl hl (c + 1) p hleft
      · exact ihr hr _ p hright

/-- `getIndex` of a terminal verb is `none`: no internal node carries a pending action. -/
theorem getIndex_none_of_terminal {v : Verb} (h : isTerminal v = true) : getIndex v = none := by
  unfold getIndex nodes
  rw [maxPendingIdx_eq_none]
  exact enum_nonpending_of_terminal v h 0

/-- A terminal verb cannot take a Nock step. -/
theorem next_none_of_terminal {v : Verb} (h : isTerminal v = true) : next v = none := by
  unfold next; rw [getIndex_none_of_terminal h]

/-! ### Converses: no pending redex ⇒ terminal

    The halting condition of the paper's completeness clause is `getIndex F = ⊥`.  The forward
    direction (`terminal ⇒ getIndex none`) is `getIndex_none_of_terminal`; the completeness
    argument needs the *converse* (a stuck-but-non-terminal verb is impossible) together with
    the geometric fact that the **selected** (argmax) redex has no pending descendants, so its
    children are already terminal — exactly the shape `inDomain`/`reduce` require. -/

/-- **Converse of `enum_nonpending_of_terminal`.**  If every internal node enumerated from `v`
    is non-pending, then `v` is terminal. -/
theorem terminal_of_enum_nonpending :
    ∀ (v : Verb) (c : Nat),
      (∀ p ∈ (enum v c).2, p.2.isPending = false) → isTerminal v = true := by
  intro v
  induction v with
  | leaf k => intro c _; rfl
  | node a l r ihl ihr =>
      intro c h
      have hroot : ((c, Verb.node a l r) : Nat × Verb) ∈ (enum (Verb.node a l r) c).2 := by
        simp [enum]
      have hpc := h _ hroot
      have ha : a.isNull = true := by
        simp only [isPending] at hpc
        cases hh : a.isNull with
        | true => rfl
        | false => rw [hh] at hpc; simp at hpc
      have hl : isTerminal l = true := by
        apply ihl (c + 1)
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hp)
      have hr : isTerminal r = true := by
        apply ihr (enum l (c + 1)).1
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hp)
      simp only [isTerminal, ha, hl, hr, Bool.and_self]

/-- **`getIndex` is `none` iff terminal.** -/
theorem getIndex_none_iff_terminal {v : Verb} : getIndex v = none ↔ isTerminal v = true := by
  constructor
  · intro h
    apply terminal_of_enum_nonpending v 0
    unfold getIndex nodes at h
    exact maxPendingIdx_eq_none.1 h
  · exact getIndex_none_of_terminal

/-- **Subtree enumeration embeds.**  If `sub` is enumerated at index `i` within `v` (counter
    `c`), then every internal node of `sub`'s own enumeration (counter `i`) also appears in
    `v`'s enumeration.  This is what lets a pending node *inside* the selected redex be seen as
    a pending index of the whole verb. -/
theorem enum_subtree_mem :
    ∀ (v : Verb) (c i : Nat) (sub : Verb),
      (i, sub) ∈ (enum v c).2 → ∀ p ∈ (enum sub i).2, p ∈ (enum v c).2 := by
  intro v
  induction v with
  | leaf k => intro c i sub hmem; simp [enum] at hmem
  | node a l r ihl ihr =>
      intro c i sub hmem p hp
      simp only [enum, List.mem_cons, List.mem_append] at hmem
      rcases hmem with hroot | hleft | hright
      · simp only [Prod.mk.injEq] at hroot
        obtain ⟨rfl, rfl⟩ := hroot
        simpa only [enum] using hp
      · have := ihl (c + 1) i sub hleft p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl this)
      · have := ihr (enum l (c + 1)).1 i sub hright p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr this)

/-- **The selected redex has terminal children.**  If `getIndex v = some i` picks the argmax
    pending node `map i v = node a l r`, then `l` and `r` are terminal: any pending node below
    them would have a strictly larger DFS index (`enum_index_range` + `enum_subtree_mem`),
    contradicting maximality (`getIndex_eq_some_iff`).  This is the shape `inDomain`/`reduce`
    need at the redex. -/
theorem children_terminal_of_getIndex {v : Verb} {i : Nat} {a : Action} {l r : Verb}
    (hidx : getIndex v = some i) (hmap : map i v = some (Verb.node a l r)) :
    isTerminal l = true ∧ isTerminal r = true := by
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hidx
  have hmem : (i, Verb.node a l r) ∈ nodes v := mem_nodes_of_map hmap
  have hsub : ∀ p ∈ (enum (Verb.node a l r) i).2, p ∈ nodes v := by
    intro p hp; exact enum_subtree_mem v 0 i (Verb.node a l r) hmem p hp
  have hnopend : ∀ p ∈ (enum (Verb.node a l r) i).2, i < p.1 → p.2.isPending = false := by
    intro p hp hlt
    obtain ⟨j, w⟩ := p
    simp only at hlt ⊢
    cases hw : w.isPending with
    | false => rfl
    | true =>
        have hpid : IsPendingIdx v j := isPendingIdx_iff_mem.2 ⟨w, hsub (j, w) hp, hw⟩
        exact absurd hlt (hmax.2 j hpid)
  refine ⟨?_, ?_⟩
  · apply terminal_of_enum_nonpending l (i + 1)
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hp)
    · have := enum_index_range l (i + 1) p hp; omega
  · apply terminal_of_enum_nonpending r (enum l (i + 1)).1
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hp)
    · have hge : i + 1 ≤ (enum l (i + 1)).1 := enum_ge_start l (i + 1)
      have := enum_index_range r (enum l (i + 1)).1 p hp; omega

/-! ### `NockVMROM` at the verb level — the transition function without OP₁₀

    `NockVMROM^Λ` is "Definition~\ref{Def:Nock} but without `OP₁₀`": the Nock
    opcodes *without the ability to write to memory*.  At the verb/transition level this is the
    transition function with the `OP₁₀` (edit, `#`) opcode removed from its computable domain — a
    selected `OP₁₀` redex now *crashes* (`⊥`) instead of rewriting.  We realize this by
    `redexROM` (= `redex` but rejecting `OP₁₀`) and `nextROM` (= `next` driven by `redexROM`).
    (This is the verb-level object; the §5 *compiled* `NockVM.V_NockVMROM` verifier is separate.) -/

/-- The ROM local rewrite: identical to `reduce` except every part of `OP₁₀` is *rejected* (`none` = crash), removing the ability to write to memory.
    Two things are excluded, exactly the two halves of `OP₁₀` in our two-step encoding
    (note 2b): (i) the `OP₁₀` opcode redex `*[n₁,[10,n₂]]` (`i = 10`), and (ii) the `edit`
    operator node it produces (`#`, the actual memory write).  No other opcode produces `edit`,
    so this removes `OP₁₀` and nothing else. -/
def reduceROM : Verb → Option Verb
  | .node .star _ (.node _ (.leaf 10) _) => none   -- (i) OP₁₀ opcode excluded
  | .node .edit _ _                      => none   -- (ii) the `#`/edit write step excluded
  | v => reduce v

/-- One `NockVMROM` step: exactly `next`, but using `reduceROM` for the local rewrite, so a
    selected `OP₁₀` redex (or a stray `edit` node) crashes.  Every non-crashing ROM step is a
    genuine Nock step (`next_of_nextROM`). -/
def nextROM (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduceROM sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none

/-- A terminal verb cannot take a ROM step either. -/
theorem nextROM_none_of_terminal {v : Verb} (h : isTerminal v = true) : nextROM v = none := by
  unfold nextROM; rw [getIndex_none_of_terminal h]

/-- `reduceROM` refines `reduce`: whenever the ROM rewrite succeeds, the full Nock rewrite agrees
    (they differ only on `OP₁₀`, where `reduceROM` returns `none`). -/
theorem reduce_of_reduceROM {v r : Verb} (h : reduceROM v = some r) : reduce v = some r := by
  unfold reduceROM at h
  split at h <;> first | exact h | simp at h

/-- **Every ROM transition is a Nock transition.**  `nextROM` is a *restriction* of `next`
    (`OP₁₀` removed): if `nextROM v = some w` then `next v = some w`.  This is the verb-level
    sense in which `NockVMROM` is `NockVM` without `OP₁₀`. -/
theorem next_of_nextROM {v w : Verb} (h : nextROM v = some w) : next v = some w := by
  unfold nextROM at h
  unfold next
  cases hg : getIndex v with
  | none => simp only [hg] at h ⊢; exact h
  | some i =>
      simp only [hg] at h ⊢
      cases hm : map i v with
      | none => simp only [hm] at h ⊢; exact h
      | some sub =>
          simp only [hm] at h ⊢
          by_cases hd : inDomain sub = true
          · simp only [if_pos hd] at h ⊢
            cases hr : reduceROM sub with
            | none => simp only [hr] at h; simp at h
            | some r =>
                simp only [hr] at h
                simp only [reduce_of_reduceROM hr]
                exact h
          · simp only [if_neg hd] at h ⊢; exact h

/-! ### The two-verb transition *checker* `Nock` (App A, `Algorithm:Transition_Function`)

    App A specifies the transition function `Nock` NOT as the forward map `next`, but as a
    **0/1 verifier** `Nock(Tᵢ, Tᵢ₊₁) → {0,1}` that CONSUMES *both* verbs and
    returns `0` (accept) iff `Tᵢ₊₁` is a consistent successor of `Tᵢ` (`Nock(tᵢ,tᵢ₊₁)=0`,
    the paper).  We model *accept* as `true`.

    ⊥ (the crash successor).  The checker's universe is `𝒱 × (𝒱 ∪ {⊥})`: `Tᵢ₊₁` may be the
    crash noun `⊥`.  The verb
    alphabet already carries `⊥`.  Exactly as EVERYWHERE else in this
    development — `next`, `reduce`, `redex` all land in `Option Verb` with `none = ⊥` — we
    represent the crash successor as `none : Option Verb`.  This is the file's canonical `⊥`,
    NOT a fresh ad-hoc marker; `NockCheck a none` is the paper's "`Tᵢ₊₁ = ⊥`" test.

    How each line of Algorithm 4 is modelled:
      • `index ← getIndex(Tᵢ)`, `Fᵢ ← map(Tᵢ, index)`: the selected
        redex.  If `Tᵢ` is terminal there is no
        `index` and hence NO transition to accept — the checker rejects everything.
      • `Check Tᵢ \ Fᵢ = Tᵢ₊₁ \ Fᵢ₊₁, returning 1 if false`: the
        frame-invariance gate — `Tᵢ₊₁` must equal `Tᵢ` with ONLY the selected index changed.
        `next` enforces it by construction via `replaceAt`; the checker VERIFIES it against
        the *given* `Tᵢ₊₁` by demanding `Tᵢ₊₁ = replaceAt index Tᵢ Fᵢ₊₁`.  This single
        equation is simultaneously the frame gate AND the successor
        comparison `Fᵢ₊₁ = OPₖ:Fᵢ` / `= cons:Fᵢ`; see `FrameAgree`.
      • The opcode / crash branches: "`type(tail Fᵢ) ≠ cell`" and
        "`head(tail Fᵢ) ∉ [11]`" are exactly `¬ inOpcodeDomain Fᵢ`; the
        accepted rewrite `OPₖ:Fᵢ` / `cons:Fᵢ` is exactly `redex Fᵢ`.
        Both are captured by `inDomain`/`reduce`, which additionally cover the pending-operator
        steps App A elides (notes 2b/2c) *identically to* `next` — so `NockCheck` is precisely
        the two-verb checker form of the SAME transition function `next` realizes. -/

-- the paper → {0,1}`, the two-verb transition checker)
/-- The paper's **`Nock` two-verb checker**.
    Given `Ti` and a candidate successor `Tnext ∈ 𝒱 ∪ {⊥}` (`none = ⊥`), returns `true` iff `Tnext` is a consistent successor of
    `Ti`: either a *genuine step* — `Tnext` is `Ti` with the selected redex `Fᵢ` replaced by
    its local rewrite —
    or a *crash* — `Tnext = ⊥` when `Fᵢ` is out of the transition domain.
    Unlike `next` (which only MAPS `Ti`), this CONSUMES `Tnext` and compares it. -/
def NockCheck (Ti : Verb) (Tnext : Option Verb) : Bool :=
  match getIndex Ti with
  | none   => false                                        -- terminal `Ti`: no transition
  | some i =>
      match map i Ti with
      | none    => false                                   -- (unreachable: `getIndex ⇒ node`)
      | some Fi =>
          match inDomain Fi, reduce Fi with
          -- the paper genuine step: frame-preserving splice of the rewrite
          | true,  some Fnext => decide (Tnext = some (replaceAt i Ti Fnext))
          -- the paper crash: selected redex reduces to ⊥
          | true,  none       => decide (Tnext = none)
          -- the paper crash: selected `Fᵢ` is a non-redex / out of domain
          | false, _          => decide (Tnext = none)

/-- **`Ti` crashes.**  `Ti` selects a pending redex but that redex is out of the transition domain / does not reduce,
    so its only consistent successor is `⊥`.  Equivalently `next Ti = none`
    together with a pending redex. -/
def Crashes (Ti : Verb) : Prop := getIndex Ti ≠ none ∧ next Ti = none

/-- `getIndex a = some i` names an actual internal node: `map i a` succeeds.  (The argmax is
    achieved at a pending node, which `map` retrieves by DFS distinctness.) -/
theorem map_some_of_getIndex {a : Verb} {i : Nat} (h : getIndex a = some i) :
    ∃ sub, map i a = some sub := by
  obtain ⟨⟨v, hmap, _⟩, _⟩ := getIndex_eq_some_iff.1 h
  exact ⟨v, hmap⟩

/-- **`NockCheck` ⟺ forward semantics + crash.**  The two-verb checker accepts `(a, b)`
    (returns `true` = the paper's `0`) iff `b` is a genuine one-step successor of `a`
    (`next a = some v`, i.e. `Step a v`) OR `a` crashes and `b = ⊥` (`b = none`).  This is a
    genuine biconditional: `NockCheck` is 1-1 with `next` (on non-⊥ successors) together with
    the crash branch — the checker `Nock(Tᵢ,Tᵢ₊₁)=0` and the forward map coincide exactly. -/
theorem nockCheck_eq_true_iff {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔
      (∃ v, b = some v ∧ next a = some v) ∨ (b = none ∧ Crashes a) := by
  unfold NockCheck Crashes
  cases hgi : getIndex a with
  | none =>
      have hn : next a = none := by unfold next; rw [hgi]
      rw [hn]; simp
  | some i =>
      obtain ⟨Fi, hmap⟩ := map_some_of_getIndex hgi
      simp only [hmap]
      by_cases hd : inDomain Fi = true
      · cases hr : reduce Fi with
        | some Fnext =>
            have hnext : next a = some (replaceAt i a Fnext) := by
              unfold next; simp only [hgi, hmap, if_pos hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = some (replaceAt i a Fnext) := by simpa using h
              exact Or.inl ⟨_, hb, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨_, _, hcr⟩)
              · rw [hnext] at hv
                have : v = replaceAt i a Fnext := (Option.some.inj hv).symm
                subst this; simp [hb]
              · rw [hnext] at hcr; simp at hcr
        | none =>
            have hnext : next a = none := by
              unfold next; simp only [hgi, hmap, if_pos hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = none := by simpa using h
              exact Or.inr ⟨hb, by simp, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
              · rw [hnext] at hv; simp at hv
              · simp [hb]
      · have hd' : inDomain Fi = false := by simpa using hd
        have hnext : next a = none := by
          unfold next; simp only [hgi, hmap, if_neg hd]
        simp only [hd']
        constructor
        · intro h
          have hb : b = none := by simpa using h
          exact Or.inr ⟨hb, by simp, hnext⟩
        · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
          · rw [hnext] at hv; simp at hv
          · simp [hb]

/-! ### The frame-invariance gate as an explicit predicate

    `Tᵢ \ Fᵢ = Tᵢ₊₁ \ Fᵢ₊₁` says `Tᵢ` and `Tᵢ₊₁` agree everywhere OUTSIDE the
    selected index — i.e. `Tᵢ₊₁` is `Tᵢ` with only the index-`i` subverb changed.  We model
    the "map-complement at the selected index" by the frame-preserving splice `replaceAt`
    (`next` realizes the gate by construction; here it is exposed as a predicate the checker
    verifies). -/

/-- **Frame agreement at index `i`**: `Tj` is `Ti` with the subverb at DFS index `i` replaced
    by some `Fj` — so `Ti` and `Tj` share the same frame (context) outside `i`.  This is the
    map-complement equality `Ti \ Fᵢ = Tj \ Fⱼ`. -/
def FrameAgree (i : Nat) (Ti Tj : Verb) : Prop := ∃ Fj, Tj = replaceAt i Ti Fj

/-- **Accepted steps pass the frame gate.**  If `NockCheck` accepts a non-⊥
    successor `b` of `a`, then `b` agrees with `a` outside the selected index: `FrameAgree`.
    (The genuine-step branch of `NockCheck` is exactly the frame-preserving splice.) -/
theorem nockCheck_frameAgree {a b : Verb} (h : NockCheck a (some b) = true) :
    ∃ i, getIndex a = some i ∧ FrameAgree i a b := by
  rcases nockCheck_eq_true_iff.1 h with ⟨v, hbv, hnext⟩ | ⟨hb, _⟩
  · have hvb : v = b := (Option.some.inj hbv).symm
    subst hvb
    obtain ⟨i, sub, r, hmax, _, _, _, hb⟩ := next_eq_some_iff.1 hnext
    exact ⟨i, getIndex_eq_some_iff.2 hmax, r, hb⟩
  · exact absurd hb (by simp)

end Verb
end Nock
