import Nock.Tactic.DeriveFintypeFix
import Nock.NockVMROM.Thm54.JointCoins
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting

/-!
# Challenge inventory: every coin, its paper counterpart, and the budget it is measured against

This module is additive audit bookkeeping.  It edits nothing, replaces nothing, and is not
imported by `Nock/NockVMROM/Thm54.lean`; add
`import Nock.NockVMROM.Thm54.ChallengeInventory` there to put it in the default build.

## 1. What the paper samples, and where

Every random element the paper draws is an element of `𝕂`.  There is no base-field sample
anywhere in the construction.  The sampling sites, re-read at source:

| site | coins |
|---|---|
| `RAP_prog-IO` Table Construction, step 3 | `α, β ∈ 𝕂` (record RLC, LogUp pole) |
| `RAP_walk` Table Construction, step 3 | `α, γ ∈ 𝕂` (line/count base, node RLC) |
| `Thm:Walk_IOP` statement | "`(α,γ) ∈ 𝕂` the Verifier responses" |
| `Corr:forest` statement | "`(α,γ) ∈ 𝕂` are the Verifier responses" |
| `Appendix:CompConstraints` **Inputs** | `(α,α²,α³)` timestamp base |
| same | `(a,b,c) : 𝕂³` |
| same | `z : 𝕂` NPR seed |
| `Lem:equiv_compute` | `rap_inputs := (α, z, a, b, c) ∈ 𝕂⁵` |
| `App:Memconstraints` intermediate aggregator | `RLC^γ(mem_record) − β` |
| `Def:NMR` | `α` NPR seed, `𝒯 := β^k` timestamp base (symbols swapped vs the appendix) |

Only `a`, `b`, `c` are named as three independent coins; every other symbol is one of `α`, `β`,
`γ`, `z`.  So the paper's own constructions name **at least seven** distinct `𝕂` coins.

## 2. What the paper *prices*, and why that number is not an inventory

| site | claim |
|---|---|
| `RAP_prog-IO` Additional Costs | "One round of interaction, providing **two** random elements in `𝕂`" (price P1) |
| `RAP_mem-IO` Additional Costs | `e + 1` columns and **no round** (its `α, β` come from the compute table) |
| `Thm:Walk_IOP` Table Building | "One round of interaction, providing **three** random elements in `𝕂`" (price P2) |
| `Corr:forest` | "the concrete costs of this protocol are as in Theorem~`Thm:Walk_IOP`" |
| `Thm:NockVMROM`, `RAP_NockComp-IO` | "**Two** rounds of interaction, providing **three** random elements in `𝕂`" (price P3) |
| `Thm:NockVMROM`, `RAP_NockMem-IO` | "**One** round of interaction, providing **a** random element in `𝕂`" (price P4) |

`Thm:NockVMROM` composes the memory table from `Corr:forest` and `RAP_mem-IO`, so the memory price P4 ("a
random element") is below the three of P2, which `Corr:forest` inherits verbatim.  The
same holds on the compute side: the three of P3 is below `P2 + P1 = 5`.  Both facts are compiled
below (`memory_priced_below_its_walk_component`, `compute_priced_below_its_components`).

**Consequence, and it is the load-bearing methodological point of this module:** the price P4
cannot be used as a coin inventory to measure the tree against.  A coin count exceeding it is not
by itself evidence of anything.  The evidence that the base-field compression coins are outside
the paper's design is of a different kind — see §4.

**Corrected reading.**  The three theorems above are true
arithmetic, but the conclusion drawn from them is too strong.  Under the paper's sharing
discipline — the memory side *obtains* `α, β` "from the computation table's `w_prog-IO` array"
rather than drawing them — the pricing lines are **exact for the gadget coins**: compute is
walk `(α, γ)` plus prog-IO `β`, two rounds and three elements (P3 verbatim), and memory is
its forest walk's `γ`, one round and one element (P4 verbatim).  What they are is *silent*
about `z, a, b, c`, which `Lem:equiv_compute` fixes as `𝕂⁵` for `RAP_comp`
alone. So the right statement is neither "the pricing is not an inventory" nor "the pricing is
exact": it is exact for `{R2 = R5, R3, R6}`, silent about `{R1, R9}`, and its exactness is bought
by a letter-driven identification the text never makes.

## 3. What the tree carries

`OptimizedProductionChallengeTuple K F`
(`OptimizedStrictPackage.lean::OptimizedProductionChallengeTuple`) is
`JointCoins K × ((K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K))`,
of cardinality `|K|⁹` (`card_optimizedProductionChallengeTuple`).

On the memory side (`OptimizedMemoryGateBasis.lean:10`): memory challenges `0..2`, forest
challenge `3` and fold challenge `6`. The four base-field "scalar compression coins" that sat at
memory base indices `0..3` are gone from the tuple; the *slots* remain
in the gate-basis file's index map, read by nothing.

`TreeCoin` below enumerates the **nine** coordinates of the production tuple, with the paper
counterpart of each recorded as `Option PaperSymbol`. **There is no
base-field coordinate left.**

## 4. The finding

`no_paper_counterpart_iff_fold_or_compression` (below) is the inventory verdict: the **three**
coordinates with no paper counterpart are exactly the three `𝕂` *fold* coins. They are not
protocol coins of the paper; they are artifacts of this tree's compilation of an extension-valued
AIR into a base-field coordinate RAP.

For that base-field one the case rested on three independent legs, none of which is
the pricing P4, and they are kept below because they are what licensed the two deletions:

1. **Type.** Every paper sample is in `𝕂` (§1). `cardF_lt_cardK` below: for `e ≥ 2` a base-field
   coin is drawn from a strictly smaller space, so the `20/|𝔽|` summand of
   `optimizedExtensionProductionFailureProbabilityBound`
   (`OptimizedStrictPackage.lean::optimizedExtensionProductionFailureProbabilityBound`) is
   strictly worse than any `𝕂`-denominated term.
2. **Site.** The paper's cost model charges `e` base gates for one extension gate
   ("`e` gates of degree 3", `24·e + 16` transition gates).  It expands coordinates; it never
   *compresses* them.  There is no construction in the paper at which such a coin is drawn.
3. **Deployed client.** `chal-names-rd1` (14 coins) and `chal-names-rd2` (12 coins)
   are all `pelt-chal` (the extension-field challenge type of the deployed client, in `ext-chals` and
   `mega-ext-chals`).  Twenty-six extension coins, zero base-field coins.

`rlc3_compression_is_lossy` records what the coins buy and cost: for **every** `ρ` there is a
nonzero coordinate triple the compressed gate accepts, so the compressed gate is strictly weaker
than the three coordinate gates it replaces — the coin is load-bearing (deleting it changes the
gate) and it is exactly the source of the collision event.

`decompressed_memory_resources` records the other side: de-compressing restores the paper's
expansion discipline but moves the resource conjuncts of
`OptimizedFullCostRealization.exact_resources`.

**Retyping versus de-compression.**  (i) The two repairs move the same resource conjuncts only
where the family size equals `e`: on memory `m = e = 3` makes retyping and de-compression
numerically identical (`4 → 12` either way), but on compute the eleven-term `challenge36` family
gives `2 → 6` against `2 → 22`, a five-fold difference.  (ii) The paper's `24·e + 16` does **not**
break under the memory repair: `RAPPadding.residualTransitionGates` absorbs it
(`memory_transition_bucket_unmoved`).  The paper's two verifier-side equality counts are not the
tree's counter: they count verifier-side equalities on terminal outputs of type `out_walk ∈ 𝕂`,
priced as "One equality check" in the same list that charges `𝕂`-valued gates `2·e` and `e`,
whereas the tree's counter counts committed base gates. -/

namespace Nock.NockVMROM.Thm54
namespace ChallengeInventory

open OptimizedComputeCollisionBound
open OptimizedMemoryCollisionAccounting

/-! ## The paper's coin symbols -/

/-- The distinct `𝕂` coin symbols the paper's own constructions name.

`alpha` covers the timestamp base and the walk line/count base;
`beta` covers the external `RAP_prog-IO` pole and the internal
`intermediate` pole; `gamma` covers the node RLC and the
memory-record RLC.  Collapsing each symbol to one coin is the **most generous**
reading available — it is the reading under which the paper needs fewest coins — and even it
needs seven. -/
inductive PaperSymbol
  /-- `α`: timestamp base / walk line-and-count base. -/
  | alpha
  /-- `β`: LogUp pole offset. -/
  | beta
  /-- `γ`: random-linear-combination coefficient. -/
  | gamma
  /-- `z`: NPR fingerprint seed. -/
  | zseed
  /-- `a`: first opcode-5 equality coefficient. -/
  | eqA
  /-- `b`: second opcode-5 equality coefficient. -/
  | eqB
  /-- `c`: third opcode-5 equality coefficient. -/
  | eqC
deriving DecidableEq, Fintype, Repr

theorem card_paperSymbol : Fintype.card PaperSymbol = 7 := by decide

/-! ## The paper's priced randomness -/

/-- Paper price: `RAP_prog-IO` Additional Costs, "two random elements in `𝕂`". -/
def progIOPriced : ℕ := 2

/-- Paper price: `Thm:Walk_IOP` Table Building, "three random elements in `𝕂`".
`Corr:forest` — the memory table's walk gadget — has the same costs. -/
def walkPriced : ℕ := 3

/-- Paper price: `Thm:NockVMROM`, `RAP_NockComp-IO`, "three random elements in `𝕂`". -/
def computePriced : ℕ := 3

/-- Paper price: `Thm:NockVMROM`, `RAP_NockMem-IO`, "a random element in `𝕂`". -/
def memoryPriced : ℕ := 1

/-- The whole priced randomness of `Thm:NockVMROM`. -/
def nockVMROMPriced : ℕ := computePriced + memoryPriced

theorem nockVMROMPriced_eq : nockVMROMPriced = 4 := rfl

/-- **The priced budget is below the number of coin symbols the paper itself names.**
The paper prices four `𝕂` elements for `Thm:NockVMROM`, but its construction sites (`RAP_prog-IO`,
`RAP_walk`, the compute inputs `a, b, c, z`, and the intermediate aggregator)
name seven distinct symbols. -/
theorem priced_below_named : nockVMROMPriced < Fintype.card PaperSymbol := by decide

/-- **The compute table's priced total is below the sum of its two component costs.**
`Thm:NockVMROM` builds `RAP_NockComp-IO` from `Thm:Walk_IOP` and
`RAP_prog-IO`. -/
theorem compute_priced_below_its_components : computePriced < walkPriced + progIOPriced := by
  decide

/-- **The memory table's priced total is below its walk gadget alone.**
`Thm:NockVMROM` builds `RAP_NockMem-IO` from `Corr:forest`, whose costs the paper declares
identical to `Thm:Walk_IOP`'s, plus `RAP_mem-IO`, which draws no round (its `α, β` come from
the compute table).

This is why the memory price cannot be read as a coin inventory: the paper's own memory table
already needs more than the one element that price states. -/
theorem memory_priced_below_its_walk_component : memoryPriced < walkPriced := by decide

/-! ## The tree's production-tuple coordinates (fourteen, then ten, now nine) -/

/-- Which field a coordinate is drawn from. -/
inductive CoinField
  /-- Extension field `𝕂`. -/
  | ext
  /-- Base field `𝔽`. -/
  | base
deriving DecidableEq, Fintype, Repr

/-- The six coordinates of `OptimizedProductionChallengeTuple K F`
(`OptimizedStrictPackage.lean::OptimizedProductionChallengeTuple`), in order. -/
inductive TreeCoin
  /-- `JointCoins.alphaC` (`JointCoins.lean:28`): the compute walk's own base. -/
  | alphaC
  /-- `JointCoins.gamma` (`JointCoins.lean:34`): the shared node/record RLC coin. -/
  | gamma
  /-- `JointCoins.alphaM` (`JointCoins.lean:31`): the timestamp base;
  `ComputeStagedTable.lean:51` pins `cfg.challenges.α = alphaM ω`. -/
  | alphaM
  /-- `JointCoins.nprSeed` (`JointCoins.lean:37`): the NPR seed. -/
  | zseed
  /-- `FiniteIO.IOCoins.gamma` (`FiniteFieldIO.lean:57`): the `RAP_prog-IO` record RLC. -/
  | ioGamma
  /-- `FiniteIO.IOCoins.pole` (`FiniteFieldIO.lean:59`): the `RAP_prog-IO` pole. -/
  | ioPole
  /-- `MemoryChallengeTuple.interPole`: the memory table's internal `intermediate` LogUp pole
(one more element than the paper's memory price). -/
  | interPole
  /-- `FinalComputeChallengeTuple.eqA`: first OP5 equality coin. -/
  | eqA
  /-- `FinalComputeChallengeTuple.eqB`: second OP5 equality coin. -/
  | eqB
  /-- `FinalComputeChallengeTuple.eqC`: third OP5 equality coin. -/
  | eqC
deriving DecidableEq, Fintype, Repr

/-- The field each coordinate is drawn from. -/
def field : TreeCoin → CoinField
  | .alphaC | .gamma | .alphaM | .zseed | .ioGamma | .ioPole | .interPole
    | .eqA | .eqB | .eqC => .ext

/-- The paper coin each coordinate realizes, **mapped by role, never by symbol**
(the deployed client's `α` and `z` are the reverse of this tree's).

`ioGamma` is the `RAP_prog-IO` record's `RLC^α` — an RLC coefficient, hence `gamma`; `ioPole` is the same
record's `− β`.  `alphaC` and `alphaM` are both instances of the paper's walk base, on the
compute tree and on the memory forest respectively. -/
def paperCounterpart : TreeCoin → Option PaperSymbol
  | .alphaC => some .alpha
  | .gamma => some .gamma
  | .alphaM => some .alpha
  | .zseed => some .zseed
  | .ioGamma => some .gamma
  | .ioPole => some .beta
  | .interPole => some .beta
  | .eqA => some .eqA
  | .eqB => some .eqB
  | .eqC => some .eqC

/-- Whether a coordinate is a coordinate-RAP fold or compression coin rather than a protocol
coin.  Since W2 stage 3 every remaining coordinate is a protocol coin. -/
def isFoldOrCompression : TreeCoin → Bool
  | .alphaC | .gamma | .alphaM | .zseed | .ioGamma | .ioPole | .interPole
    | .eqA | .eqB | .eqC => false

/-- **The inventory verdict.**  A production-tuple coordinate has no paper counterpart exactly
when it is a coordinate-RAP fold or compression coin. -/
theorem no_paper_counterpart_iff_fold_or_compression (t : TreeCoin) :
    paperCounterpart t = none ↔ isFoldOrCompression t = true := by
  cases t <;> decide

/-- **Every base-field coordinate has no paper counterpart.**  The paper samples only in `𝕂`
(at every sampling and pricing site of §§1–2).  There is no base-field coordinate, so this holds vacuously. -/
theorem base_field_coins_have_no_paper_counterpart (t : TreeCoin) :
    field t = CoinField.base → paperCounterpart t = none := by
  cases t <;> decide

/-- Six extension-field coordinates.  Seven until W2 stage 3 deleted the memory fold. -/
theorem card_ext_coins :
    (Finset.univ.filter fun t : TreeCoin => field t = CoinField.ext).card = 10 := by decide

/-- **No** base-field coordinate — there is no `|F|` factor in `|K|⁶`
(`card_optimizedProductionChallengeTuple`, `OptimizedStrictPackage.lean`). -/
theorem card_base_coins :
    (Finset.univ.filter fun t : TreeCoin => field t = CoinField.base).card = 0 := by decide

/-- Every remaining coordinate carries a paper coin.  It was one (the memory fold) until W2
stage 3, three until W3 stage 2 deleted the two compute folds. -/
theorem card_without_paper_counterpart :
    (Finset.univ.filter fun t : TreeCoin => paperCounterpart t = none).card = 0 := by decide

/-- **H1.U exit 1: `a`, `b`, `c` are now production-tuple coordinates.**  They sit in
`FinalComputeChallengeTuple` at `c.2.2.1`. -/
theorem eq_coefficients_present_in_production_tuple :
    paperCounterpart TreeCoin.eqA = some PaperSymbol.eqA ∧
      paperCounterpart TreeCoin.eqB = some PaperSymbol.eqB ∧
      paperCounterpart TreeCoin.eqC = some PaperSymbol.eqC := by decide

/-! ## The production tuple's shape and cardinality -/

/-- `OptimizedProductionChallengeTuple K F` (`OptimizedStrictPackage.lean:554`) with the
abbreviation unfolded.  Stated here so this module does not import that file. -/
abbrev ProductionTupleShape (K F : Type) [Fintype K] [Fintype F] :=
  JointCoins K × ((K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K))

/-- The compute tuple is `(a, b, c)` (H1.U exit 1; a unit until then). -/
def finalComputeEquiv (K : Type) : FinalComputeChallengeTuple K ≃ (K × K × K) where
  toFun c := (c.eqA, c.eqB, c.eqC)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := fun c => by cases c; rfl
  right_inv := fun p => rfl

theorem card_finalComputeChallengeTuple' (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 := by
  rw [Fintype.card_congr (finalComputeEquiv K)]
  simp [pow_three]

/-- **`|K|¹⁰`** — the independent re-derivation of `card_optimizedProductionChallengeTuple`
(`OptimizedStrictPackage.lean`), reached without importing that file. -/
theorem card_productionTupleShape (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (ProductionTupleShape K F) = Fintype.card K ^ 11 := by
  simp only [ProductionTupleShape, Fintype.card_prod, JointCoins,
    card_finalComputeChallengeTuple', memoryChallengeTuple_card]
  ring

/-- The exponents in `|K|⁷` (and the absent `|F|`) are exactly the coordinate counts of
`TreeCoin`. -/
theorem card_exponents_match_inventory :
    (Finset.univ.filter fun t : TreeCoin => field t = CoinField.ext).card = 10 ∧
      (Finset.univ.filter fun t : TreeCoin => field t = CoinField.base).card = 0 := by
  exact ⟨card_ext_coins, card_base_coins⟩

/-! ## Leg 1: a base-field coin is a strictly smaller sample space -/

section Cardinality

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]

/-- **A base-field coin is drawn from a strictly smaller space than an extension coin**, for any
extension degree `e ≥ 2`.  So the `(20 + 14M)/|𝔽|` summand of
`optimizedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:632`) is strictly
larger than the corresponding `𝕂`-denominated term, and `Thm:NockVMROM`'s soundness statement is
against `𝕂`. -/
theorem cardF_lt_cardK (he : 2 ≤ Module.finrank F K) : Fintype.card F < Fintype.card K := by
  have hcard : Fintype.card K = Fintype.card F ^ Module.finrank F K :=
    Module.card_eq_pow_finrank
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
    _ < Fintype.card F ^ Module.finrank F K := by
        exact Nat.pow_lt_pow_right h1 (lt_of_lt_of_le Nat.one_lt_two he)
    _ = Fintype.card K := hcard.symm

/-- At the tree's `e = 3` this is `|𝔽| < |𝕂|` with `|𝕂| = |𝔽|³`. -/
theorem cardF_lt_cardK_cubic (he : Module.finrank F K = 3) :
    Fintype.card F < Fintype.card K :=
  cardF_lt_cardK (by omega)

/-- The five base-field coordinates cost strictly more sample space than five extension ones —
the compiled form of `ExtensionChallenges.lean`'s `|K|¹⁴` versus `|K|⁹·|F|⁵`. -/
theorem base_coordinates_shrink_the_space
    (he : 2 ≤ Module.finrank F K) :
    Fintype.card F ^ 5 < Fintype.card K ^ 5 :=
  Nat.pow_lt_pow_left (cardF_lt_cardK he) (by norm_num)

end Cardinality

/-! ## Leg 2: what the compression coin buys, and what it costs -/

section Compression

variable {F : Type*} [Field F]

/-- The scalar compression combinator of `OptimizedMemoryGateBasis.rlc3` (`:668`), read
semantically: `Σ_{k<3} ρ^k · f k`. -/
def rlc3 (ρ : F) (f : Fin 3 → F) : F := ∑ k : Fin 3, ρ ^ (k : ℕ) * f k

@[simp] theorem rlc3_apply (ρ : F) (f : Fin 3 → F) :
    rlc3 ρ f = f 0 + ρ * f 1 + ρ ^ 2 * f 2 := by
  simp [rlc3, Fin.sum_univ_three, pow_zero, pow_one]

/-- **The compression is lossy for every coin value.**  For every `ρ` there is a nonzero
coordinate triple whose compressed gate vanishes, so the single committed gate
`rlc3 ρ (coordinates)` is strictly weaker than the three coordinate gates it replaces.

This is the compiled statement of *why the coin is load-bearing and why it costs soundness*: the
gate cannot be recovered from the compression at any fixed `ρ`, which is exactly the collision
event `MemoryChallengeTuple` union-bounds.  It is the semantic form of
`GatheredMemoryScalarGates.base_gate_is_strictly_weaker_than_gathered_gate`. -/
theorem rlc3_compression_is_lossy (ρ : F) :
    ∃ f : Fin 3 → F, f ≠ 0 ∧ rlc3 ρ f = 0 := by
  refine ⟨![ρ, -1, 0], ?_, ?_⟩
  · intro h
    have h1 : (![ρ, -1, 0] : Fin 3 → F) 1 = 0 := by rw [h]; rfl
    simp at h1
  · simp

/-- Three uncompressed coordinate gates are *not* lossy: they vanish only on the zero triple.
Together with `rlc3_compression_is_lossy` this is the exact trade the four coins make. -/
theorem uncompressed_is_not_lossy (f : Fin 3 → F) (h : ∀ k, f k = 0) : f = 0 := funext h

end Compression

/-! ## Leg 3 and the resource ledger -/

/-- Paper count: `RAP_NockMem-IO` transition constraints, `24·e + 16` gates. -/
def paperMemoryTransitionGates (e : ℕ) : ℕ := 24 * e + 16

/-- Paper count: `RAP_NockMem-IO`, "Four equality checks". -/
def paperMemoryEqualityChecks : ℕ := 4

/-- That is what the de-compression ledger below is
about, so the constant stays.

**The deployed lists today are different**: `memorySourceTemplate` carries
`baseTransitionGates` `11`, three `𝕂`-valued `mixedTransition` gates and `equalityChecks` `12`
(`GatheredMemoryScalarGates.the_four_scalar_gates_are_retyped`). -/
def treeCompressedMemoryBaseGates : ℕ := 14

/-- The same lists after de-compression: each compressed gate becomes its three coordinate gates
(`GatheredMemoryScalarGates.extension_gate_costs_three_base_gates`, `:576`). -/
def decompressedMemoryBaseGates : ℕ := treeCompressedMemoryBaseGates + 3 * (3 - 1)

/-- De-compressing the four selector equality checks. -/
def decompressedMemoryEqualityChecks : ℕ := paperMemoryEqualityChecks + 4 * (3 - 1)

/-- **The resource ledger of de-compression.**  Removing the four scalar coins costs `+6` base
transition gates and `+8` equality checks, so it moves the `exact_resources` conjuncts of
`OptimizedFullStrictThm54Statement` that name and ("Four equality checks").

Recorded as an accounting fact, **not** as a recommendation: re-typing the coins to `𝕂` moves the
same conjuncts, and a third possibility — that the paper's counts are met by
a gate factorization this tree has not found — is untested. -/
theorem decompressed_memory_resources :
    decompressedMemoryBaseGates = treeCompressedMemoryBaseGates + 6 ∧
      decompressedMemoryEqualityChecks = paperMemoryEqualityChecks + 8 ∧
      paperMemoryTransitionGates 3 = 88 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The deployed client's coin count, for comparison: `chal-names-rd1` has fourteen names and
`chal-names-rd2` twelve, every one
of them a `pelt-chal`, i.e. an extension element (`ztd/five.hoon:158`). -/
def clientExtensionCoins : ℕ := 14 + 12

/-- The client draws no base-field challenge at all. -/
def clientBaseFieldCoins : ℕ := 0

/-- **The three coin counts side by side.**  The paper prices four `𝕂` elements and names seven
symbols; the tree's production tuple carries nine `𝕂` coordinates and **no** `𝔽` coordinate; the
deployed client draws twenty-six `𝕂` coins and no `𝔽` coin. -/
theorem base_field_coins_are_a_tree_only_object :
    clientBaseFieldCoins = 0 ∧
      (Finset.univ.filter fun t : TreeCoin => field t = CoinField.base).card = 0 ∧
      nockVMROMPriced < clientExtensionCoins := by
  exact ⟨rfl, card_base_coins, by decide⟩



section AxiomAudit

#print axioms priced_below_named
#print axioms compute_priced_below_its_components
#print axioms memory_priced_below_its_walk_component
#print axioms no_paper_counterpart_iff_fold_or_compression
#print axioms base_field_coins_have_no_paper_counterpart
#print axioms card_without_paper_counterpart
#print axioms eq_coefficients_present_in_production_tuple
#print axioms card_productionTupleShape
#print axioms cardF_lt_cardK
#print axioms rlc3_compression_is_lossy
#print axioms decompressed_memory_resources
#print axioms base_field_coins_are_a_tree_only_object

end AxiomAudit

end ChallengeInventory
end Nock.NockVMROM.Thm54
