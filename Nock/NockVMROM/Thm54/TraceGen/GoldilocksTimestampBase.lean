/-
  Nock/NockVMROM/Thm54/TraceGen/GoldilocksTimestampBase.lean

  **The timestamp base `α`, provisioned at the Goldilocks carrier.**

  `Def:NMR` parameterises the memory encoding by two extension-field elements.
  It is *not*
  `Def:RAP` item 6's evaluation-domain generator `ω ∈ 𝔽` of order `e · 2^h` (`:142`), which is
  provisioned separately and at the **base** field by `GoldilocksOrbit.lean`.  Read both lines at
  source before editing either module.

  The paper puts no order condition on the timestamp base: `β` is any element of `𝕂` and `𝒯` is
  the set of its powers.  The order condition is ours, and it is a *distinctness* condition — the
  generated trace hands consecutive record exponents `0, 1, 2, …` to `timestampExp α ·`, so two
  records collide unless the exponent range stays inside `α`'s orbit.  That is exactly the two
  premise shapes `GenServedRoots.lean` §D.1 catalogues:

  * `(B : ℕ) (hB : B ≤ orderOf α)` with `hwin : accAt … + 3 < B`, taken by `genSemanticData`
    (`GenSemanticData.lean:129-130`) and `genLanguage`;
  * `horbα : accAt … < orderOf α`, taken by `genRoots` and the two `nodup` theorems.

  `horb_of_window` (§D.1) shows the first implies the second, and `exists_alpha_assembly_orbit`
  shows one primitive element of a finite carrier supplies all of it.  This module *names* that
  element at `Nock.Field.K = GaloisField p 3` and threads it through `genSemanticData`.

  ## The choice, and why

  `goldilocksTimestampBase` is a **primitive element** of `Field.K`, of order `p^3 - 1`
  (`goldilocksTimestampBase_order_value`: `6277101731002175853884774869567645561244584131361410908160`,
  which is `2^192` to within one part in `2^64`).  Two reasons, and the second is the load-bearing
  one:

  1. The paper constrains the timestamp base only to lie in `𝕂`, so nothing forces a smaller
     subgroup — unlike `ω`, which `Def:RAP` item 6 pins to order `e · 2^h`.
  2. It is **optimal**: `orderOf_le_card_sub_one` says no element of any finite field has order
     above `card K - 1`, so `goldilocksTimestampBase_maximal` establishes that no other choice of
     timestamp base admits a longer trace.  The admissible-trace bound below is therefore a
     property of the *field*, not of our choice within it.

  ## Scope — what this does and does not establish

  It says: the orbit-side side conditions of the generic
  assembly are *simultaneously satisfiable by an explicit named witness* at the field a real
  deployment uses.  It does **not**:

  * produce a STARK, a proof system, or anything executable.  Nothing here is a commitment
    scheme, an FRI instance, or a prover.
  * inhabit `ExactServedMemoryTrace` at the generated carrier.  Two of its four fields
    (`timestampPowersNodup`, `semanticCoverage`) remain open, so **no
    end-to-end capstone follows from this module** and none is claimed.
  * discharge the seed family.  `hseed`/`hbad`/`hout` are counting arguments over the NPR seed `z`; they are independent of the orbit family and are passed straight
    through below.

  Everything naming `Field.K` or `Field.p` depends on `Field.goldilocks_prime` and is therefore
  named `goldilocks…`, per `scripts/gen-axiom-audit.py`.  The two field-generic lemmas at the top
  are not, and are marked as such.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.TraceGen.GenServedRoots
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.Framework.Thm54

/-! ## A. Field-generic: the orbit bound `exists_orderOf_eq_card_sub_one` attains is the best one

Neither declaration in this section mentions Goldilocks; both are `∀ K`.  They are here rather than
in `GenServedRoots.lean` §D.1 only to keep this change to one new file — they would sit equally well
beside `exists_orderOf_eq_card_sub_one`, whose optimality they establish. -/

section Generic

variable {K : Type} [Field K]

/-- **No element of a finite field has multiplicative order above `card K - 1`.**  Field-generic;
no Goldilocks content.  Together with `exists_orderOf_eq_card_sub_one` this pins the largest
attainable timestamp orbit exactly, so `exists_alpha_assembly_orbit`'s premise
`n + 3 < card K - 1` cannot be relaxed by choosing a different `α`. -/
theorem orderOf_le_card_sub_one [Fintype K] [DecidableEq K] {α : K} (hα : α ≠ 0) :
    orderOf α ≤ Fintype.card K - 1 := by
  have hdvd : orderOf (Units.mk0 α hα) ∣ Fintype.card Kˣ := orderOf_dvd_card
  rw [Fintype.card_units] at hdvd
  have hpos : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hle := Nat.le_of_dvd hpos hdvd
  rw [← orderOf_units (y := Units.mk0 α hα), Units.val_mk0] at hle
  exact hle

/-- **The orbit window in the shape a caller has it: a bound on the trace's record count.**

`n` is `accAt (airReorder t) (bfsRows (airReorder t)).length`, the number of memory records the
generated trace emits.  This is `exists_alpha_assembly_orbit` with the existential replaced by a
supplied `α`, so a *named* witness can discharge the assembly's four orbit obligations at once.
Field-generic; no Goldilocks content. -/
theorem orbit_window_of_lt_orderOf {α : K} {n : ℕ} (hα : α ≠ 0)
    (hn : n + 3 < orderOf α) :
    α ≠ 0 ∧ orderOf α ≤ orderOf α ∧ n + 3 < orderOf α ∧ n < orderOf α :=
  ⟨hα, le_rfl, hn, horb_of_window (α := α) le_rfl hn⟩

end Generic

/-! ## B. The Goldilocks carrier

`Field.K = GaloisField p 3` with `p = 2^64 - 2^32 + 1`. -/

noncomputable section Goldilocks

/-- Goldilocks base field, as the semantic base `F` of the generated configuration. -/
abbrev GF : Type := Nock.Field.Fp

/-- Goldilocks cubic extension, as the table/RAP field `K`. -/
abbrev GK : Type := Nock.Field.K

/-- **`ringChar K = p` at the Goldilocks carrier.**  `K` is a `ZMod p`-algebra, so its
characteristic is that of `ZMod p`.  This is what lets `genSemanticData`'s `hchar : q = ringChar K`
be discharged at `q := Field.p` rather than carried. -/
theorem goldilocks_ringChar_K : ringChar GK = Nock.Field.p := by
  rw [← Algebra.ringChar_eq Nock.Field.Fp Nock.Field.K, ZMod.ringChar_zmod_n]

/-- **`2 ≠ 0` in the Goldilocks extension.**  `p` is odd, so `p ∤ 2`.  Discharges
`genSemanticData`'s `htwo`. -/
theorem goldilocks_two_ne_zero : (2 : GK) ≠ 0 := by
  intro hz
  have h2 : ((2 : ℕ) : GK) = 0 := by exact_mod_cast hz
  have hd := (ringChar.spec GK 2).mp h2
  rw [goldilocks_ringChar_K] at hd
  have := Nat.le_of_dvd (by norm_num) hd
  norm_num [Nock.Field.p] at this

/-! ### B.1 The witness -/

/-- **The Goldilocks timestamp base**: a primitive element of `Field.K`, i.e. a generator of `Kˣ`.

Chosen exactly as `GoldilocksOrbit.lean` chooses `ω` — `Classical.choose` on an existence lemma,
order by `choose_spec` — but from `exists_orderOf_eq_card_sub_one` rather than from a divisor of
`p - 1`, because `Def:NMR` item 3 puts no order condition on the timestamp base
and a primitive element is the optimal choice (`goldilocksTimestampBase_maximal`). -/
def goldilocksTimestampBase : GK :=
  Classical.choose (exists_orderOf_eq_card_sub_one (K := GK))

theorem goldilocksTimestampBase_spec :
    goldilocksTimestampBase ≠ 0 ∧
      orderOf goldilocksTimestampBase = Fintype.card GK - 1 :=
  Classical.choose_spec (exists_orderOf_eq_card_sub_one (K := GK))

/-- The timestamp base is nonzero — `genSemanticData`'s `hα`, and `genRoots`' too. -/
theorem goldilocksTimestampBase_ne_zero : goldilocksTimestampBase ≠ 0 :=
  goldilocksTimestampBase_spec.1

/-- **`orderOf α = p^3 - 1`.**  The full unit-group order of the cubic extension. -/
theorem goldilocksTimestampBase_order :
    orderOf goldilocksTimestampBase = Nock.Field.p ^ 3 - 1 := by
  rw [goldilocksTimestampBase_spec.2, Nock.Field.card_K]

/-- The order as a decimal, for the record: `≈ 2^192`. -/
theorem goldilocksTimestampBase_order_value :
    orderOf goldilocksTimestampBase
      = 6277101731002175853884774869567645561244584131361410908160 := by
  rw [goldilocksTimestampBase_order, Nock.Field.p_eq]; norm_num

/-- **The choice is optimal.**  No timestamp base in `Field.K` has a larger orbit, so the
admissible-trace bound below is a property of the Goldilocks cubic extension and not an artefact of
which element we picked. -/
theorem goldilocksTimestampBase_maximal {α : GK} (hα : α ≠ 0) :
    orderOf α ≤ orderOf goldilocksTimestampBase := by
  rw [goldilocksTimestampBase_spec.2]
  exact orderOf_le_card_sub_one hα

/-! ### B.2 Every orbit condition of the assembly, discharged -/

/-- **The four orbit obligations of the generic assembly, met at Goldilocks by a named witness.**

Read `n` as `accAt (airReorder t) (bfsRows (airReorder t)).length`, the generated trace's memory
record count.  The conclusion is, in order: `genSemanticData`'s `hα`, its `hB` at
`B := orderOf goldilocksTimestampBase`, its `hwin`, and `genRoots`' `horbα`.

It is not a claim that the assembly is complete: the seed family and the
two open `ExactServedMemoryTrace` fields are untouched (see the module header). -/
theorem goldilocksTimestampBase_assembly_orbit (n : ℕ)
    (hn : n + 3 < Nock.Field.p ^ 3 - 1) :
    goldilocksTimestampBase ≠ 0 ∧
      orderOf goldilocksTimestampBase ≤ orderOf goldilocksTimestampBase ∧
      n + 3 < orderOf goldilocksTimestampBase ∧
      n < orderOf goldilocksTimestampBase :=
  orbit_window_of_lt_orderOf goldilocksTimestampBase_ne_zero
    (by rw [goldilocksTimestampBase_order]; exact hn)

/-- The same, stated on a generated trace rather than on an abstract `n`, so the premise shapes are
literally `genSemanticData`'s and `genRoots`'.  `t` is any tree `genComputeSkeleton` produced. -/
theorem goldilocksTimestampBase_trace_orbit {t : NTree (GenComputeRow GK)}
    (hn : accAt (airReorder t) (bfsRows (airReorder t)).length + 3
      < Nock.Field.p ^ 3 - 1) :
    goldilocksTimestampBase ≠ 0 ∧
      orderOf goldilocksTimestampBase ≤ orderOf goldilocksTimestampBase ∧
      accAt (airReorder t) (bfsRows (airReorder t)).length + 3
        < orderOf goldilocksTimestampBase ∧
      accAt (airReorder t) (bfsRows (airReorder t)).length
        < orderOf goldilocksTimestampBase :=
  goldilocksTimestampBase_assembly_orbit _ hn

/-! ## C. `genSemanticData`, applied at the Goldilocks carrier

`genSemanticData` (`GenSemanticData.lean:119`) takes twenty-six arguments.  Six of them are
discharged here and not carried:

| argument | discharged by |
|---|---|
| `α` | `goldilocksTimestampBase` |
| `htwo : (2 : K) ≠ 0` | `goldilocks_two_ne_zero` |
| `B` | `orderOf goldilocksTimestampBase` |
| `hB : B ≤ orderOf α` | `le_rfl` |
| `hwin : accAt … + 3 < B` | `goldilocksTimestampBase_trace_orbit`, from `hfit` |
| `hq : 11 < q` | `q := Field.p`, `norm_num` |
| `hchar : q = ringChar K` | `goldilocks_ringChar_K` |

and `horbα`, which `genSemanticData` does not take but `genRoots` does, comes with them.

The rest pass through unchanged, and the reason each does is different.  `hz`, `hinp`, `hmi`,
`hKsz`, `horb`, `hmempos`, `hcomp`, `hmem` are the caller's configuration choices; `h` is the
program; `hΛ`/`hconf` are the leaf window; and `hseed`, `hbad`, `hout`, `hb`,
`haxis`, `hcoins` are the seed-counting and skeleton-bound families, which are a different
provisioning problem and are deliberately untouched here.

`hfit` replaces `B`/`hB`/`hwin` and is the *only* new obligation: the trace's record count must fit
inside `α`'s orbit.  `Batch206` measures what it admits. -/

/-- **`sd : ExactExecutionSemanticData` at `Field.K`, with every orbit condition supplied.**

Same object as `genSemanticData`, at `F := Field.Fp`, `K := Field.K`, `q := Field.p` and
`α := goldilocksTimestampBase`, with the orbit family, `htwo`, `hq` and `hchar` discharged rather
than assumed.  See the section header for the full argument ledger and the module header for what
this does *not* establish — in particular it is not an end-to-end capstone, because two
`ExactServedMemoryTrace` fields are still open at the generated carrier. -/
def goldilocksSemanticData {Λ : ℕ} (z : GK) (hz : z ≠ 0) (a b c : GK)
    (chal : ChallengeVector GK)
    (hinp : chal.computeInputs = ⟨goldilocksTimestampBase, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain GK) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow GK)} {result : Noun}
    (h : genComputeSkeleton (K := GK) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z goldilocksTimestampBase a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z goldilocksTimestampBase chal.lam
      (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z goldilocksTimestampBase t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t)).length
      ≤ 2 ^ orbit.h)
    (hfit : accAt (airReorder t) (bfsRows (airReorder t)).length + 3
      < Nock.Field.p ^ 3 - 1)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t)).BoundedBy Nock.Field.p)
    (haxis : SkeletonAxisRange Nock.Field.p (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t)))
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar GK)
    (hbad : z ∉ (genSkeletonP8Census (K := GK) hΛ h hconf
      (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := GK)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t))) :
    SemanticTrace.ExactExecutionSemanticData Nock.Field.p Λ
      (genExactConfig (F := GF) chal Ksz orbit horb
        (genComputeRows z goldilocksTimestampBase t)
        (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := GF) chal Ksz orbit horb a b c
        (genComputeRows z goldilocksTimestampBase t)
        (genMemoryForest z goldilocksTimestampBase chal.lam (memInputs z) t) hmempos hcomp hmem) :=
  genSemanticData (F := GF) z goldilocksTimestampBase hz goldilocks_two_ne_zero a b c
    chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
    (orderOf goldilocksTimestampBase) le_rfl
    (goldilocksTimestampBase_trace_orbit (t := t) hfit).2.2.1
    hKsz hb (by norm_num [Nock.Field.p]) goldilocks_ringChar_K.symm haxis hbad hout hfirst

end Goldilocks

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.orderOf_le_card_sub_one
#print axioms Nock.NockVMROM.Thm54.TraceGen.orbit_window_of_lt_orderOf
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_ringChar_K
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_two_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_order_value
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_maximal
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_assembly_orbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksTimestampBase_trace_orbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocksSemanticData
