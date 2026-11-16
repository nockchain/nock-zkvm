/-
  Nock/RedTeam/Batch336Thm54FinalShape2Review.lean

Counts total/explicit: p74 33/17 -> 30/14, p75 31/16 -> 28/13, p76 31/16 -> 28/13,
  zmod 29/16 -> 26/13; the explicit-name list loses `hfirst`, `hmore`, `hbasis`.

  Sections:

  * §B  the `Λ` converse uses only `p74`'s binders (compiled by re-deriving
        it from `p75` with an explicit `p74` telescope).
  * §C  the floor recomputed from the definitions: closed form of
        `sizeWindowRootBound`, monotonicity of `seedBudgetVcomp` in both
        arguments (so the worst case is `rows = Λ = p − 1`), exact values
        `13867` / `15106`, failure for every `1 ≤ p ≤ 24`, vacuous truth at
        `p = 0`, an independent positive proof from `25`, the `hp` consumers
        of `p76`'s proof term, and the prime interplay (`29` is the least
        admissible prime; `hF` further excludes `29`, so `31` is the least
        prime satisfying `hp ∧ hF`).
  * §D  `ringChar K = p` derivable from `[Field K] [Algebra (ZMod p) K]`
        alone; the `Fintype.card (ZMod p) − 1 = p − 1` bridge; the four
        instance binders the §1 block elides are derivable / canonical.
  * §E  literal positive control: the matmul leaf bound is `≤ 568`, and
        `568 < Field.p`; the claim triples are evaluator results.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.RedTeam.Batch331Thm54FloorThreshold
import Nock.RedTeam.Batch332Thm54ZModLiterals

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch336

open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed

/-! ## §C — the floor, recomputed from the definitions -/

/-- `seedBudgetVcomp` unfolded: `1 + (3 + 13·rows)(2Λ − 1) + T(Λ)`. -/
theorem b336_budget_closed (Λ rows : ℕ) :
    seedBudgetVcomp Λ rows
      = 1 + (3 + 13 * rows) * (2 * Λ - 1) + sizeWindowRootBound Λ := by
  unfold seedBudgetVcomp seedBudget
  have : (3 + 10 * rows) * (2 * Λ - 1) + 3 * rows * (2 * Λ - 1)
      = (3 + 13 * rows) * (2 * Λ - 1) := by ring
  omega

theorem b336_sizeWindow_succ (Λ : ℕ) :
    sizeWindowRootBound (Λ + 1) = sizeWindowRootBound Λ + (Λ + 1) := by
  unfold sizeWindowRootBound
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- Gauss: `2 · T(Λ) = Λ (Λ + 1)`.  So `T` is the triangular number,
    strictly below the writer's square majorant for `Λ ≥ 2`. -/
theorem b336_two_mul_sizeWindow (Λ : ℕ) :
    2 * sizeWindowRootBound Λ = Λ * (Λ + 1) := by
  induction Λ with
  | zero => simp [sizeWindowRootBound]
  | succ n ih =>
    rw [b336_sizeWindow_succ, Nat.mul_add, ih]
    ring

/-- `T` is monotone in `Λ`. -/
theorem b336_sizeWindow_mono {Λ Λ' : ℕ} (h : Λ ≤ Λ') :
    sizeWindowRootBound Λ ≤ sizeWindowRootBound Λ' := by
  unfold sizeWindowRootBound
  exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl h)

/-- **The budget is monotone in both arguments**, so the worst case under
    `rows < p ∧ Λ < p` is `rows = Λ = p − 1`.  This is the step the writer's
    `p₀` silently relies on. -/
theorem b336_budget_mono {Λ Λ' rows rows' : ℕ}
    (hΛ : Λ ≤ Λ') (hr : rows ≤ rows') :
    seedBudgetVcomp Λ rows ≤ seedBudgetVcomp Λ' rows' := by
  rw [b336_budget_closed, b336_budget_closed]
  have h1 : 3 + 13 * rows ≤ 3 + 13 * rows' := by omega
  have h2 : 2 * Λ - 1 ≤ 2 * Λ' - 1 := by omega
  have h3 := b336_sizeWindow_mono hΛ
  have h4 := Nat.mul_le_mul h1 h2
  omega

/-- Computable twin of `2 · seedBudgetVcomp`. -/
def budget2 (Λ rows : ℕ) : ℕ :=
  2 + 2 * ((3 + 13 * rows) * (2 * Λ - 1)) + Λ * (Λ + 1)

theorem b336_two_mul_budget (Λ rows : ℕ) :
    2 * seedBudgetVcomp Λ rows = budget2 Λ rows := by
  rw [b336_budget_closed]
  unfold budget2
  have := b336_two_mul_sizeWindow Λ
  omega

/-- Exact value at the negative witness (`13867`, the writer's number). -/
theorem b336_budget_23_23 : seedBudgetVcomp 23 23 = 13867 := by
  have h := b336_two_mul_budget 23 23
  unfold budget2 at h
  omega

/-- Exact value at the worst case admitted by `p = 25` (`15106 < 15625`). -/
theorem b336_budget_24_24 : seedBudgetVcomp 24 24 = 15106 := by
  have h := b336_two_mul_budget 24 24
  unfold budget2 at h
  omega

/-- **Fails for every `1 ≤ p ≤ 24`**, not only at `24`: the worst case
    admitted by `rows < p ∧ Λ < p` is already `≥ p³`.  Decided on the
    computable twin. -/
theorem b336_budget2_ge_below_25 :
    ∀ p ∈ Finset.Icc 1 24, 2 * p ^ 3 ≤ budget2 (p - 1) (p - 1) := by
  decide

theorem b336_fails_for_all_p_le_24 {p : ℕ} (h1 : 1 ≤ p) (h24 : p ≤ 24) :
    ¬ (seedBudgetVcomp (p - 1) (p - 1) < p ^ 3) := by
  intro hlt
  have hb := b336_budget2_ge_below_25 p (Finset.mem_Icc.mpr ⟨h1, h24⟩)
  have := b336_two_mul_budget (p - 1) (p - 1)
  omega

/-- The `∀`-implication fails at every `1 ≤ p ≤ 24` (witness `p − 1`). -/
theorem b336_implication_fails_below_25 {p : ℕ} (h1 : 1 ≤ p) (h24 : p ≤ 24) :
    ¬ (∀ rows Λ, rows < p → Λ < p → seedBudgetVcomp Λ rows < p ^ 3) :=
  fun h => b336_fails_for_all_p_le_24 h1 h24
    (h (p - 1) (p - 1) (by omega) (by omega))

/-- **Pedantry the writer's "least such `p`" misses:** at `p = 0` the
    implication is vacuously true.  The set where it holds is
    `{0} ∪ [25, ∞)`; `25` is the least *positive* such `p`. -/
theorem b336_implication_vacuous_at_zero :
    ∀ rows Λ : ℕ, rows < 0 → Λ < 0 → seedBudgetVcomp Λ rows < 0 ^ 3 :=
  fun _ _ h _ => absurd h (Nat.not_lt_zero _)

/-- Independent positive proof from `25`, via the triangular closed form
    (not the writer's square majorant): with `p = y + 25`,
    `2p³ − budget2 = 2y³ + 97y² + 1219y + 1038 > 0`. -/
theorem b336_budget2_lt_from_25 {p : ℕ} (hp : 25 ≤ p) :
    budget2 (p - 1) (p - 1) < 2 * p ^ 3 := by
  obtain ⟨y, rfl⟩ : ∃ y, p = y + 25 := ⟨p - 25, by omega⟩
  unfold budget2
  have h1 : y + 25 - 1 = y + 24 := by omega
  have h2 : 2 * (y + 24) - 1 = 2 * y + 47 := by omega
  rw [h1, h2]
  nlinarith [Nat.zero_le (y * y * y), Nat.zero_le (y * y), Nat.zero_le y]

theorem b336_implication_holds_from_25 {p rows Λ : ℕ}
    (hp : 25 ≤ p) (hrows : rows < p) (hΛ : Λ < p) :
    seedBudgetVcomp Λ rows < p ^ 3 := by
  have hm := b336_budget_mono (Λ' := p - 1) (rows' := p - 1)
    (Nat.le_sub_one_of_lt hΛ) (Nat.le_sub_one_of_lt hrows)
  have h2 := b336_two_mul_budget (p - 1) (p - 1)
  have hg := b336_budget2_lt_from_25 hp
  omega

/-- **Recomputed `p₀`:** `25` is the least positive `p` for which the
    implication holds — both halves in one statement. -/
theorem b336_p0_is_25 :
    (∀ p, 1 ≤ p → p ≤ 24 →
      ¬ (∀ rows Λ, rows < p → Λ < p → seedBudgetVcomp Λ rows < p ^ 3))
    ∧ (∀ p, 25 ≤ p →
      ∀ rows Λ, rows < p → Λ < p → seedBudgetVcomp Λ rows < p ^ 3) :=
  ⟨fun _ h1 h24 => b336_implication_fails_below_25 h1 h24,
   fun _ hp _ _ hr hΛ => b336_implication_holds_from_25 hp hr hΛ⟩

/-- The writer's `Batch331.p0` agrees with the recomputation. -/
theorem b336_writer_p0_agrees : Nock.RedTeam.Batch331.p0 = 25 := rfl

/-! ### Prime interplay (`nockCompiles_zmod` carries `[Fact p.Prime]`) -/

/-- No prime in `[25, 28]`: for primes the floor `25 ≤ p` is effectively
    `29 ≤ p`, the W9 constant. -/
theorem b336_no_prime_25_to_28 :
    ¬ Nat.Prime 25 ∧ ¬ Nat.Prime 26 ∧ ¬ Nat.Prime 27 ∧ ¬ Nat.Prime 28 := by
  norm_num

theorem b336_prime_floor_is_29 {p : ℕ} (hp : 25 ≤ p) (hprime : p.Prime) : 29 ≤ p := by
  by_contra h
  have h' : p < 29 := Nat.lt_of_not_le h
  interval_cases p <;> norm_num at hprime

/-- `hF : 3 · 2^h ∣ p − 1` rules `29` out for every `h` (`3 ∤ 28`), so the
    least prime satisfying `hp ∧ hF` is `31` (`h = 1` only: `6 ∣ 30`,
    `12 ∤ 30`).  `orbitHeight ≥ 1` always (`orbitHeight_pos`). -/
theorem b336_hF_excludes_29 (h : ℕ) : ¬ (3 * 2 ^ h ∣ 29 - 1) := by
  intro hd
  have h3 : 3 ∣ 28 := dvd_trans (Dvd.intro _ rfl) hd
  omega

/-- The same for the general-`F` theorem `p76`: `ringChar K` of a finite
    field is prime, so `25 ≤ ringChar K` admits no field that `29 ≤ ringChar K`
    excluded.  The `29 → 25` move tightens the implication, not the set of
    admissible fields. -/
theorem b336_p76_floor_effectively_29 {K : Type} [Field K] [Finite K]
    (hp : 25 ≤ ringChar K) : 29 ≤ ringChar K := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  exact b336_prime_floor_is_29 hp hprime

theorem b336_hF_at_31_h1 : 3 * 2 ^ 1 ∣ 31 - 1 := by decide
theorem b336_hF_at_31_h2_fails : ¬ (3 * 2 ^ 2 ∣ 31 - 1) := by decide
theorem b336_31_prime : Nat.Prime 31 := by norm_num

/-! ## §D — `ZMod p` spelling -/

/-- `ringChar K = p` needs only `[Field K] [Algebra (ZMod p) K]` (and the
    prime for `ZMod.ringChar_zmod_n`).  The carrier's `ringChar_eq_prime`
    carries the section's eight instances; none of the extra ones is used. -/
theorem b336_ringChar_eq_prime_minimal {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] : ringChar K = p := by
  rw [← Algebra.ringChar_eq (ZMod p) K, ZMod.ringChar_zmod_n]

/-- The `hF` bridge `p76 ↔ zmod`: `Fintype.card (ZMod p) − 1 = p − 1`
    (ℕ subtraction on both sides, same truncation). -/
theorem b336_card_zmod_sub_one (p : ℕ) [NeZero p] :
    Fintype.card (ZMod p) - 1 = p - 1 := by
  rw [ZMod.card]


theorem b336_finiteDimensional_of_hK {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K]
    (hK : Module.finrank (ZMod p) K = 3) : FiniteDimensional (ZMod p) K :=
  Module.finite_of_finrank_pos (by omega)

theorem b336_finite_of_hK {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K]
    (hK : Module.finrank (ZMod p) K = 3) : Finite K := by
  haveI := b336_finiteDimensional_of_hK hK
  exact Module.finite_of_finite (ZMod p)

@[reducible] noncomputable def b336_fintype_of_hK {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K]
    (hK : Module.finrank (ZMod p) K = 3) : Fintype K :=
  haveI := b336_finite_of_hK hK
  Fintype.ofFinite K

noncomputable def b336_decEq (K : Type) : DecidableEq K := Classical.decEq K

theorem b336_charP_canonical (K : Type) [Field K] : CharP K (ringChar K) :=
  ringChar.charP K

/-! ## §E — literal positive control (matmul at Goldilocks) -/

/-- The matmul leaf bound the literal discharges `hΛp` with is `≤ 568`
    (`GenMatmulTraceConfined.lean::mm_traceConfined`), and `568 < Field.p`.
    Generic in `K`, as the source theorem is. -/
theorem b336_mm_leaf_le_568 {K : Type} [Field K] :
    programLeafBound (airReorder (mmTree (K := K))) ≤ 568 :=
  leafBound_of_traceConfined mm_traceConfined

theorem b336_568_lt_p : 568 < Nock.Field.p := by
  simp only [Nock.Field.p]; norm_num

theorem b336_25_le_p : 25 ≤ Nock.Field.p := by
  simp only [Nock.Field.p]; norm_num

theorem b336_25_le_769 : 25 ≤ 769 := by norm_num

end Nock.RedTeam.Batch336



open Lean Elab Command Meta

namespace Batch336BinderWalk

/-- Instrument 1: `forallTelescope` on the declared type. -/
def telescope (n : Name) : MetaM (Array (Name × BinderInfo × Expr)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo, l.type)

def counts (n : Name) : MetaM (Nat × Nat) := do
  let tel ← telescope n
  let expl := tel.foldl (fun k (_, bi, _) => if bi == .default then k + 1 else k) 0
  return (tel.size, expl)

/-- Instrument 2: count leading `forallE` syntactically, no instantiation. -/
partial def rawForallCount : Expr → Nat × Nat
  | .forallE _ _ b bi =>
    let (t, e) := rawForallCount b
    (t + 1, if bi == .default then e + 1 else e)
  | _ => (0, 0)

def rawCounts (n : Name) : MetaM (Nat × Nat) := do
  let info ← getConstInfo n
  return rawForallCount info.type

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← telescope n
  return tel.filterMap fun (nm, bi, _) => if bi == .default then some nm else none

/-- True occurrence count of a constant (`Expr.foldConsts` visits each
    constant once and would only measure presence — caught by the
    `ringChar` control below, which must read `7` on `p76`). -/
partial def countConst (e : Expr) (c : Name) : Nat :=
  match e with
  | .const n _ => if n == c then 1 else 0
  | .app f a => countConst f c + countConst a c
  | .lam _ t b _ => countConst t c + countConst b c
  | .forallE _ t b _ => countConst t c + countConst b c
  | .letE _ t v b _ => countConst t c + countConst v c + countConst b c
  | .mdata _ b => countConst b c
  | .proj _ _ b => countConst b c
  | _ => 0

structure StepResult where
  left     : Array Name := #[]
  entered  : Array Name := #[]
  changed  : Array Name := #[]
  matched  : Nat := 0
  leftInstantiated : Array (Name × Expr) := #[]

/-- **Name-aligned step diff.**  Walk the successor `b`'s telescope with
    fresh fvars.  Then instantiate the predecessor `a`'s telescope binder by
    binder: a named binder present in `b` is instantiated with `b`'s fvar
    after checking `isDefEq` of the (substituted) domain — a mismatch is
    `changed`; a `Type` binder absent from `b` is instantiated with
    `typeMap` (e.g. `F ↦ ZMod p`); an instance binder absent from `b` is
    matched by defeq type against `b`'s instance fvars or synthesised; any
    other absent binder is instantiated with `valueMap` (e.g. `Λ ↦
    programLeafBound …`) or reported `left` with its instantiated type.
    `replace` rewrites subterms of `a`'s domains before the comparison
    (e.g. `ringChar K ↦ p`).  `b` binders never used are `entered`. -/
def stepDiff (a b : Name)
    (typeMap : Name → Array (Name × Expr) → Option Expr)
    (valueMap : Name → Array (Name × Expr) → Option Expr)
    (replaceKeys : Array (Name × Expr) → MetaM (Array (Name × Expr × Expr))) :
    MetaM StepResult := do
  let ia ← getConstInfo a
  let ib ← getConstInfo b
  forallTelescope ib.type fun ys _ => do
    let named : Array (Name × Expr) ← ys.mapM fun y => do
      pure ((← y.fvarId!.getUserName), y)
    let keys0 ← replaceKeys named
    -- a key `(c, arg, v)` rewrites every FULL application `@c arg …` (any
    -- instance path) to `v`; matched on head constant, arity of `c` and
    -- first argument.  (`mkAppM` returns the partial `@ringChar K`, so the
    -- arity is read off the constant's type, not off a sample term.)
    let keys ← keys0.mapM fun (c, a, v) => do
      let ci ← getConstInfo c
      pure (c, (rawForallCount ci.type).1, a, v)
    let doReplace (e : Expr) : Expr :=
      e.replace fun s =>
        (keys.find? (fun (c, ar, a, _) =>
          s.isAppOfArity c ar && s.getAppArgs[0]! == a)).map (·.2.2.2)
    let mut used : Array FVarId := #[]
    let mut res : StepResult := {}
    let mut ta := ia.type
    -- a-binder instantiation values, in order
    while ta.isForall do
      let .forallE n dom _ bi := ta | break
      -- instance binders are compared verbatim: the `ZMod` statement keeps
      -- `[CharP K (ringChar K)]` (demanded by the package type), so a
      -- `ringChar K ↦ p` rewrite there would manufacture `CharP K p`.
      let dom := if bi == .instImplicit then dom else doReplace dom
      let candidate? : Option Expr ← do
        match named.find? (fun (nm, _) => nm == n && !n.hasMacroScopes) with
        | some (_, y) =>
          if used.contains y.fvarId! then pure none else pure (some y)
        | none => pure none
      let mut val? : Option Expr := none
      match candidate? with
      | some y =>
        used := used.push y.fvarId!
        let ty ← inferType y
        unless ← isDefEq dom ty do
          res := { res with changed := res.changed.push n }
        res := { res with matched := res.matched + 1 }
        val? := some y
      | none =>
        if bi == .instImplicit then
          -- match by type against unused b instance fvars
          let mut found : Option Expr := none
          for y in ys do
            if found.isNone && !used.contains y.fvarId! then
              let d ← y.fvarId!.getDecl
              if d.binderInfo == .instImplicit then
                if ← isDefEq dom d.type then
                  found := some y
          match found with
          | some y =>
            used := used.push y.fvarId!
            res := { res with matched := res.matched + 1 }
            val? := some y
          | none =>
            match ← try? (synthInstance dom) with
            | some inst =>
              res := { res with leftInstantiated := res.leftInstantiated.push (n, dom) }
              val? := some inst
            | none =>
              res := { res with left := res.left.push n,
                                leftInstantiated := res.leftInstantiated.push (`UNSYNTHESISED ++ n, dom) }
              val? := none
        else if dom.isSort then
          match typeMap n named with
          | some v => val? := some v; res := { res with left := res.left.push n }
          | none => val? := none; res := { res with left := res.left.push n }
        else
          match valueMap n named with
          | some v =>
            val? := some v
            res := { res with left := res.left.push n, leftInstantiated := res.leftInstantiated.push (n, dom) }
          | none =>
            res := { res with left := res.left.push n, leftInstantiated := res.leftInstantiated.push (n, dom) }
            val? := none
      match val? with
      | some v => ta := ta.bindingBody!.instantiate1 v
      | none =>
        -- cannot continue soundly without a value; use a fresh fvar
        let fv ← mkFreshExprMVar dom
        ta := ta.bindingBody!.instantiate1 fv
    for y in ys do
      unless used.contains y.fvarId! do
        res := { res with entered := res.entered.push (← y.fvarId!.getUserName) }
    return res

def fvarByName (named : Array (Name × Expr)) (n : Name) : Option Expr :=
  (named.find? (fun (nm, _) => nm == n)).map (·.2)

/-- Extract `programLeafBound …` from `b`'s `hΛp : programLeafBound … < ringChar K`. -/
def leafBoundOf (named : Array (Name × Expr)) : MetaM (Option Expr) := do
  match fvarByName named `hΛp with
  | some y =>
    let ty ← inferType y
    -- @LT.lt ℕ inst lhs rhs
    return some ty.appFn!.appArg!
  | none => return none

def wholeTypeDefEq (a b : Name) : MetaM Bool := do
  let ia ← getConstInfo a
  let ib ← getConstInfo b
  isDefEq ia.type ib.type

def N74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
def N75 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75
def N76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
def NZ  : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def C75 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74_of_p75
def C76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75_of_p76
def CZ  : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76_of_zmod
def NLegacy : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles

run_cmd do
  -- ---- counts, two instruments
  let names := [N74, N75, N76, NZ, C75, C76, CZ, NLegacy]
  let mut line := "BINDER-WALK"
  for n in names do
    let (t, e) ← liftTermElabM (counts n)
    let (t', e') ← liftTermElabM (rawCounts n)
    unless t == t' && e == e' do
      throwError m!"instruments disagree on {n}: {t}/{e} vs {t'}/{e'}"
    line := line ++ s!" {n.components.getLast!}={t}/{e}"
  logInfo line
  let (t74, e74) ← liftTermElabM (counts N74)
  let (t75, e75) ← liftTermElabM (counts N75)
  let (t76, e76) ← liftTermElabM (counts N76)
  let (tZ, eZ) ← liftTermElabM (counts NZ)
  -- H1.5b Part 2a: p74/p75/p76 each gained `hrows` (+1/+1); zmod derives it (`hrows_of_hF`).
  -- Repair (ii): p74/p75 gained `hmemOrd` after `hwin` (+1/+1);
  -- p76/zmod keep their counts (`hwin` retyped to the pair).
  -- the 36th: p74/p75/p76 gained the prime-field binder `hFprime` (+1/+1); zmod discharges it.
  -- S2: every level gained the explicit walk coin `αW` after
  -- `α` (+1/+1).
  unless (t74, e74) == (34, 18) do throwError m!"p74 {t74}/{e74} ≠ 34/18"
  unless (t75, e75) == (32, 17) do throwError m!"p75 {t75}/{e75} ≠ 32/17"
  unless (t76, e76) == (31, 16) do throwError m!"p76 {t76}/{e76} ≠ 31/16"
  unless (tZ, eZ) == (27, 14) do throwError m!"zmod {tZ}/{eZ} ≠ 27/14"
  for (n, c) in [(C75, N74), (C76, N75), (CZ, NZ)] do
    let (a, b) ← liftTermElabM (counts n)
    let (a', b') ← liftTermElabM (counts c)
    unless (a, b) == (a', b') do throwError m!"{n} count {a}/{b} ≠ {c} {a'}/{b'}"
  -- explicit names
  let ex75 ← liftTermElabM (explicitNames N75)
  let ex76 ← liftTermElabM (explicitNames N76)
  let exZ ← liftTermElabM (explicitNames NZ)
  let expected : Array Name :=
    -- 28th λ-fix pass 2: live 11 + `lmb` (beside `α`) + `hp64` (after `hp`);
    -- `hwidth`/`hax` are lemmas (`FormRWidth_of_hp64`, `genComputeRows_rowsFormRAxisBound`).
    #[`α, `αW, `lmb, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hp64, `hK, `hF, `hwin, `hKszChar]
  let expected75 : Array Name :=
    #[`α, `αW, `lmb, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hp64, `hK, `hF, `hwin, `hmemOrd, `hKszChar]
  -- the 36th: + `hFprime` after `hrows` (p75/p76)
  unless ex75 == (expected75.push `hrows).push `hFprime do throwError m!"p75 explicit names {ex75}"
  unless ex76 == (expected.push `hrows).push `hFprime do throwError m!"p76 explicit names {ex76}"
  unless exZ == expected do throwError m!"zmod explicit names {exZ}"
  logInfo m!"EXPLICIT-NAMES p76=zmod={expected}; p75={expected75}"
  -- ---- Λ really gone from p75's statement?
  let i75 ← liftTermElabM (getConstInfo N75)
  let occ := countConst i75.type ``Nock.NockVMROM.Thm54.TraceGen.programLeafBound
  -- Form R leftovers mention `programLeafBound` inside `hfirst`/`hmore` binder types.
  unless occ ≥ 1 do throwError m!"programLeafBound occurs {occ} times in p75's type, expected ≥ 1 (hΛp)"
  let tel75 ← liftTermElabM (telescope N75)
  if tel75.any (fun (nm, _, _) => nm == `Λ || nm == `hΛ) then
    throwError "p75 still binds Λ or hΛ"
  let occSeed := countConst i75.type ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.seedBudget
  unless occSeed == 0 do throwError m!"seedBudget in p75 type"
  logInfo m!"P75-STATEMENT programLeafBound occurrences={occ} (≥1; Form R leftovers inflate), no Λ/hΛ binder, no seedBudget"
  -- ---- step p74 → p75: Λ ↦ programLeafBound (…), inlined walk
  let r1 ← liftTermElabM do
    let ib ← getConstInfo N75
    forallTelescope ib.type fun ys _ => do
      let named : Array (Name × Expr) ← ys.mapM fun y => do pure ((← y.fvarId!.getUserName), y)
      let some E ← leafBoundOf named | throwError "no hΛp in p75"
      unless E.getAppFn.isConstOf ``Nock.NockVMROM.Thm54.TraceGen.programLeafBound do
        throwError m!"p75 hΛp lhs head is not programLeafBound: {E}"
      -- now diff with Λ ↦ E.  We cannot pass a closure over E through the
      -- Name-indexed API, so inline the same walk here.
      let ia ← getConstInfo N74
      let mut used : Array FVarId := #[]
      let mut left : Array Name := #[]
      let mut changed : Array Name := #[]
      let mut hΛInst : Option Expr := none
      let mut ta := ia.type
      while ta.isForall do
        let .forallE n dom _ bi := ta | break
        let mut val? : Option Expr := none
        if n == `Λ then
          left := left.push n; val? := some E
        else if n == `hΛ then
          left := left.push n; hΛInst := some dom
          -- instantiate with a metavariable; it does not occur later
          val? := some (← mkFreshExprMVar dom)
        else
          let cand ← (do
            if bi == .instImplicit then
              let mut found : Option Expr := none
              for y in ys do
                if found.isNone && !used.contains y.fvarId! then
                  let d ← y.fvarId!.getDecl
                  if d.binderInfo == .instImplicit then
                    if ← isDefEq dom d.type then found := some y
              pure found
            else pure (fvarByName named n))
          match cand with
          | some y =>
            used := used.push y.fvarId!
            unless ← isDefEq dom (← inferType y) do changed := changed.push n
            val? := some y
          | none => left := left.push n; val? := some (← mkFreshExprMVar dom)
        ta := ta.bindingBody!.instantiate1 val?.get!
      let mut entered : Array Name := #[]
      for y in ys do
        unless used.contains y.fvarId! do entered := entered.push (← y.fvarId!.getUserName)
      -- hΛ's instantiated type must be `E ≤ E` (what `le_rfl` discharges)
      let some hΛty := hΛInst | throwError "hΛ not seen"
      let lhs := hΛty.appFn!.appArg!
      let rhs := hΛty.appArg!
      unless ← isDefEq lhs rhs do throwError m!"hΛ instantiated is not reflexive: {hΛty}"
      -- conclusion identical
      unless ← isDefEq ta (← instantiateForall ib.type ys) do
        throwError m!"p74[Λ := leafBound] conclusion ≠ p75 conclusion"
      pure (left, entered, changed, E)
  let (l1, e1, c1, E) := r1
  unless l1 == #[`Λ, `hΛ] do throwError m!"step p74→p75 left {l1} ≠ [Λ, hΛ]"
  unless e1.isEmpty do throwError m!"step p74→p75 entered {e1} ≠ []"
  unless c1.isEmpty do throwError m!"step p74→p75 changed {c1} ≠ [] after Λ := leafBound"
  logInfo m!"STEP p74→p75 left={l1} entered={e1} changed(after Λ:=leafBound)={c1} hΛ↦(E ≤ E) conclusion=defeq\n  Λ := {E}"
  -- ---- step p75 → p76: `hp`, and (repair (ii)) `hmemOrd` folds into the pair `hwin`
  let r2 ← liftTermElabM <| stepDiff N75 N76 (fun _ _ => none) (fun _ _ => none) (fun _ => pure #[])
  unless r2.left == #[`hmemOrd] && r2.entered.isEmpty do
    throwError m!"p75→p76 left/entered {r2.left}/{r2.entered} ≠ [hmemOrd]/[]"
  unless r2.changed == #[`hp, `hwin] do throwError m!"p75→p76 changed {r2.changed} ≠ [hp, hwin]"
  logInfo m!"STEP p75→p76 left={r2.left} entered={r2.entered} changed={r2.changed} matched={r2.matched}"
  -- ---- step p76 → zmod: F ↦ ZMod p, ringChar K ↦ p
  let r3 ← liftTermElabM <| stepDiff N76 NZ
    (fun n named => if n == `F then (fvarByName named `p).map (fun p => mkApp (mkConst ``ZMod) p) else none)
    (fun _ _ => none)
    (fun named => do
      match fvarByName named `p, fvarByName named `K with
      | some p, some K => pure #[(``ringChar, K, p)]
      | _, _ => pure #[])
  -- H1.5b Part 2a: p76's `hrows` is derived at zmod (`hrows_of_hF`), so it leaves too.
  -- the 36th: p76's prime-field binder `hFprime` is discharged at zmod (`primeFieldElems_zmod`), so it leaves too.
  unless r3.left == #[`F, `hrows, `hFprime] do
    throwError m!"p76→zmod left {r3.left} ≠ [F, hrows]; instance domains: {r3.leftInstantiated}"
  unless r3.entered.size == 2 && r3.entered[0]! == `p do
    throwError m!"p76→zmod entered {r3.entered} ≠ [p, Fact p.Prime]"
  -- 28th λ-fix pass 2: `hp64` joins `hF` — at `F = ZMod p` it reads `p < 2^64`, not
  -- `ringChar (ZMod p) < 2^64` (the same `ringChar ↦ p` rewrite `hF`'s `card − 1` gets).
  unless r3.changed == #[`hp64, `hF] do throwError m!"p76→zmod changed {r3.changed} ≠ [hp64, hF]"
  logInfo m!"STEP p76→zmod left={r3.left} (F ↦ ZMod p) synthesised-instances={r3.leftInstantiated.map (·.1)} entered={r3.entered} changed(after ringChar K ↦ p)={r3.changed} matched={r3.matched}"
  -- Where `ringChar K` survives in zmod's type: NOT in any explicit
  -- hypothesis (each is at the literal `p`); once in the `[CharP K (ringChar K)]`
  -- instance binder and twice in the conclusion, as the verifier's modulus
  -- argument `q := ringChar K` of `Strategy.raw` / `Strategy.claim`
  --.  Both are forced by the
  -- package types.  Positive control for the counter: p76's `hΛp` carries
  -- `ringChar K` three times (once visibly, twice inside `romTree ⋯`'s proof).
  let iz ← liftTermElabM (getConstInfo NZ)
  let (perBinderZ, conclZ) ← liftTermElabM <| forallTelescope iz.type fun xs body => do
    let arr ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      pure (d.userName, d.binderInfo, countConst d.type ``ringChar)
    pure (arr, countConst body ``ringChar)
  for (nm, bi, k) in perBinderZ do
    -- Form R leftovers `hfirst`/`hmore` quantify over genExactExecution and mention ringChar.
    if bi == .default && k != 0 && nm != `hfirst && nm != `hmore
        && nm != `hax && nm != `hbasis && nm != `hwidth then
      throwError m!"zmod explicit hypothesis {nm} still mentions ringChar ({k})"
  let instHits := perBinderZ.filter (fun (_, bi, k) => bi == .instImplicit && k > 0)
  unless instHits.size == 1 && instHits[0]!.2.2 == 1 do
    throwError m!"zmod instance binders mentioning ringChar: {instHits.map (·.1)}, expected exactly the CharP one"
  -- Form R leftovers inflate the telescoped body (hfirst/hmore domains mention ringChar).
  unless conclZ ≥ 2 do throwError m!"zmod conclusion ringChar occurrences {conclZ} < 2 (Strategy.raw / .claim modulus)"
  let tel76b ← liftTermElabM (telescope N76)
  let hΛp76 := (tel76b.find? (fun (nm, _, _) => nm == `hΛp)).map (fun (_, _, t) => countConst t ``ringChar)
  unless hΛp76 == some 3 do throwError m!"counter control: p76 hΛp ringChar count {hΛp76} ≠ 3"
  logInfo m!"RINGCHAR-IN-ZMOD explicit hypotheses=0 (Form R hfirst/hmore exempt), CharP binder=1, conclusion (verifier modulus q := ringChar K in Strategy.raw/.claim)={conclZ}; control p76.hΛp=3"
  -- the one change is the card bridge: print both hF types
  let telZ ← liftTermElabM (telescope NZ)
  let tel76 ← liftTermElabM (telescope N76)
  let hFz := (telZ.find? (fun (nm, _, _) => nm == `hF)).map (·.2.2)
  let hF76 := (tel76.find? (fun (nm, _, _) => nm == `hF)).map (·.2.2)
  logInfo m!"HF p76: {hF76}\nHF zmod: {hFz}"
  -- ---- converses: whole-type isDefEq
  let d75 ← liftTermElabM (wholeTypeDefEq C75 N74)
  let d76 ← liftTermElabM (wholeTypeDefEq C76 N75)
  unless d75 do throwError "p74_of_p75 type ≠ p74 type"
  unless d76 do throwError "p75_of_p76 type ≠ p75 type"
  -- p76_of_zmod is p76 at F := ZMod p (no ringChar replacement)
  let r4 ← liftTermElabM <| stepDiff N76 CZ
    (fun n named => if n == `F then (fvarByName named `p).map (fun p => mkApp (mkConst ``ZMod) p) else none)
    (fun _ _ => none)
    (fun _ => pure #[])
  unless r4.changed.isEmpty do throwError m!"p76_of_zmod vs p76[F := ZMod p] changed {r4.changed}"
  -- H1.5b Part 2a: `hrows` is derived at zmod.
  -- the 36th: `hFprime` is discharged at zmod too.
  unless r4.left == #[`F, `hrows, `hFprime] do throwError m!"p76_of_zmod left {r4.left}"
  logInfo m!"CONVERSES p74_of_p75≡p74 {d75}; p75_of_p76≡p75 {d76}; p76_of_zmod ≡ p76[F:=ZMod p]: left={r4.left} entered={r4.entered} changed={r4.changed}"
  -- ---- scope traps: K and F elaborate to binders (fvars), not abbrevs
  for n in [N75, N76, NZ] do
    let tel ← liftTermElabM (telescope n)
    let kb := tel.find? (fun (nm, _, _) => nm == `K)
    unless kb.isSome do throwError m!"{n}: no K binder"
  let telF := tel76.find? (fun (nm, _, _) => nm == `F)
  unless telF.isSome do throwError "p76: no F binder"
  logInfo m!"SCOPE p75/p76/zmod bind K as a variable; p76 binds F; zmod has F := ZMod p with p a variable"
  -- ---- the legacy north-star name still points at the p74 shape
  let dl ← liftTermElabM (wholeTypeDefEq NLegacy N74)
  unless dl do throwError "nockCompiles ≠ p74"
  logInfo m!"LEGACY nockCompiles ≡ p74 (28/12, hΛ, 29 ≤ p) — §1 now names nockCompiles_zmod"

/-! Direct constants of `p76`'s proof and a bounded transitive walk within
    the `TraceGen` namespace: the W9 floor lemmas are NOT reached. -/
run_cmd do
  let i76 ← liftTermElabM (getConstInfo N76)
  let some v := i76.value? (allowOpaque := true) | throwError "p76 has no value"
  let direct := v.getUsedConstants
  let has (c : Name) := direct.contains c
  unless has ``Nock.NockVMROM.Thm54.TraceGen.seedBudget_lt_card_of_bounds_twenty_five do
    throwError "p76 does not use the 25-floor lemma directly"
  unless has ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72 do
    throwError "p76 does not go through p72"
  if has ``Nock.NockVMROM.Thm54.TraceGen.cubic_gap_of_twenty_nine then
    throwError "p76 uses cubic_gap_of_twenty_nine"
  -- bounded transitive walk
  let env ← getEnv
  let prefix_ : Name := `Nock.NockVMROM.Thm54.TraceGen
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := direct
  let mut hit29 := false
  let mut hitBounds29 := false
  let mut hit25 := false
  let mut n : Nat := 0
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    n := n + 1
    if c == ``Nock.NockVMROM.Thm54.TraceGen.cubic_gap_of_twenty_nine then hit29 := true
    if c == ``Nock.NockVMROM.Thm54.TraceGen.seedBudget_lt_card_of_bounds then hitBounds29 := true
    if c == ``Nock.NockVMROM.Thm54.TraceGen.seedBudget_lt_card_of_bounds_twenty_five then hit25 := true
    if prefix_.isPrefixOf c then
      if let some ci := env.find? c then
        if let some val := ci.value? (allowOpaque := true) then
          for d in val.getUsedConstants do
            unless seen.contains d do stack := stack.push d
  -- positive control: the same walk from p74 DOES reach the 29 lemma
  let i74 ← liftTermElabM (getConstInfo N74)
  let some v74 := i74.value? (allowOpaque := true) | throwError "p74 has no value"
  let mut seen74 : Std.HashSet Name := {}
  let mut st74 : Array Name := v74.getUsedConstants
  let mut ctrl := false
  while st74.size > 0 do
    let c := st74.back!
    st74 := st74.pop
    if seen74.contains c then continue
    seen74 := seen74.insert c
    if c == ``Nock.NockVMROM.Thm54.TraceGen.cubic_gap_of_twenty_nine then ctrl := true
    if prefix_.isPrefixOf c then
      if let some ci := env.find? c then
        if let some val := ci.value? (allowOpaque := true) then
          for d in val.getUsedConstants do
            unless seen74.contains d do st74 := st74.push d
  unless ctrl do throwError "positive control failed: p74's closure does not reach cubic_gap_of_twenty_nine"
  if hit29 || hitBounds29 then throwError "p76's TraceGen closure reaches a 29-floor lemma"
  unless hit25 do throwError "p76's closure misses the 25-floor lemma"
  logInfo m!"HP-CONSUMERS p76 TraceGen-closure size={n}: reaches seedBudget_lt_card_of_bounds_twenty_five, NOT cubic_gap_of_twenty_nine / seedBudget_lt_card_of_bounds; positive control p74 reaches cubic_gap_of_twenty_nine"

/-! `ringChar_eq_prime`'s declared instance binders, printed. -/
run_cmd do
  let tel ← liftTermElabM (telescope ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.ringChar_eq_prime)
  let insts := tel.filter (fun (_, bi, _) => bi == .instImplicit)
  logInfo m!"RINGCHAR-EQ-PRIME binders={tel.size} instances={insts.size}: {insts.map (·.2.2)}"

/-! Conclusion of `nockCompiles_zmod`, printed and checked for the genuine
    statement constant and the claim projection. -/
run_cmd do
  let iz ← liftTermElabM (getConstInfo NZ)
  let concl ← liftTermElabM <| forallTelescope iz.type fun _ body => pure body
  unless countConst concl ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement == 1 do
    throwError "zmod conclusion lacks OptimizedFullStrictThm54Statement"
  unless countConst concl ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage ≥ 1 do
    throwError "zmod conclusion lacks the package type"
  unless countConst concl ``ZMod ≥ 1 do throwError "zmod conclusion not at ZMod p"
  -- 28th λ-fix pass 2: the head is `∃ package : OptimizedFullStrictNockVMROMPackage …`, with no
  -- Π-premise (no residual `hwidth`/`hax` arrow) and no skolemised family.
  if concl.isForall then throwError "zmod conclusion is a Π (residual premise)"
  unless concl.isAppOfArity ``Exists 2 do throwError m!"zmod conclusion head is not ∃: {concl}"
  let dom := concl.appFn!.appArg!
  unless dom.getAppFn.isConstOf ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage do
    throwError m!"zmod ∃ domain is not the package type: {dom}"
  logInfo m!"ZMOD-CONCLUSION {concl}"

end Batch336BinderWalk

#print axioms Nock.RedTeam.Batch336.b336_p0_is_25
#print axioms Nock.RedTeam.Batch336.b336_budget_mono
#print axioms Nock.RedTeam.Batch336.b336_budget_23_23
#print axioms Nock.RedTeam.Batch336.b336_budget_24_24
#print axioms Nock.RedTeam.Batch336.b336_implication_vacuous_at_zero
#print axioms Nock.RedTeam.Batch336.b336_prime_floor_is_29
#print axioms Nock.RedTeam.Batch336.b336_hF_excludes_29
#print axioms Nock.RedTeam.Batch336.b336_p76_floor_effectively_29
#print axioms Nock.RedTeam.Batch336.b336_ringChar_eq_prime_minimal
#print axioms Nock.RedTeam.Batch336.b336_card_zmod_sub_one
#print axioms Nock.RedTeam.Batch336.b336_finiteDimensional_of_hK
#print axioms Nock.RedTeam.Batch336.b336_mm_leaf_le_568
#print axioms Nock.RedTeam.Batch336.b336_568_lt_p
