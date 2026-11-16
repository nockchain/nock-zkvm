import Nock.NockVMROM.Thm54.Config
import Nock.NockVMROM.CanonicalRAP

/-!
This module repairs the shape identified by `rev3.HasCanonicalRAP2`.

There are no stored fixed RAP decorations.  A program or memory RAP is derived from the
corresponding problem's parameters and constraint kind, and is therefore definitionally an
`airToRAP (kindSeg air kind)...`.  The two acceptance biconditionals mention
`RAP.Satisfies` of those same derived objects directly.

The supplied Nock prototype is deliberately row-local: it uses the already-proved
`computeTable_reified_iff` and `memoryTable_reified_iff` for `computeAIR` and `memoryAIR`.
Those AIRs contain the row-local gates.
-/

namespace Nock.NockVMROM.Thm54

open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified Nock.ComputeTable
open scoped Polynomial
open Classical

/-- The complete parameter tuple from which one problem's per-kind ordinary RAPs are derived.

`βcoset` is the nonzero RAP evaluation-orbit shift.  It is not the memory LogUp challenge
`ChallengeVector.β`.
-/
structure SegmentedRAPParams (K : Type*) [Field K] where
  /-- AIR challenge valuation for this problem. -/
  chalVal : ℕ → K
  /-- AIR public-value valuation for this problem. -/
  pubVal : ℕ → K
  /-- RAP extension-degree metadata. -/
  eDeg : ℕ
  /-- RAP orbit-height exponent. -/
  hExp : ℕ
  /-- Adjacent-row orbit generator. -/
  ω : K
  /-- Nonzero shifted-orbit base used as `RAP.β`. -/
  βcoset : K
  /-- Active evaluation domain assigned to each constraint kind. -/
  domain : Reified.ConstraintKind → Finset K
  /-- The shifted-orbit base is nonzero. -/
  βcoset_ne_zero : βcoset ≠ 0
  /-- The shipped RAP index set `{0,1}` fits in the orbit exponent. -/
  hExp_pos : 1 ≤ hExp

namespace SegmentedRAPParams

variable {K : Type*} [Field K]

/-- The ordinary RAP for one problem and one constraint kind. -/
@[reducible]
noncomputable def rap (q : SegmentedRAPParams K) (air : Reified.AIR)
    (kind : Reified.ConstraintKind) : RAP K :=
  airToRAP (kindSeg air kind) q.chalVal q.pubVal q.eDeg q.hExp q.ω q.βcoset
    (q.domain kind) q.βcoset_ne_zero q.hExp_pos

/-- Exact compute parameters derived from one shared configuration.
-/
noncomputable def ofComputeConfig {F K : Type*} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (pubVal : ℕ → K) : SegmentedRAPParams K where
  chalVal := cfg.challenges.computeValuation
  pubVal := pubVal
  eDeg := cfg.eDeg
  hExp := cfg.orbit.h
  ω := cfg.orbit.ω
  βcoset := cfg.orbit.βcoset
  domain := cfg.computeDomain
  βcoset_ne_zero := cfg.orbit.βcoset_ne_zero
  hExp_pos := cfg.orbit_h_pos

/-- Exact memory parameters derived from one shared configuration.
-/
noncomputable def ofMemoryConfig {F K : Type*} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (lmb : K) (pubVal : ℕ → K) : SegmentedRAPParams K where
  chalVal := cfg.challenges.memoryChalVal lmb
  pubVal := pubVal
  eDeg := cfg.eDeg
  hExp := cfg.orbit.h
  ω := cfg.orbit.ω
  βcoset := cfg.orbit.βcoset
  domain := cfg.memoryDomain
  βcoset_ne_zero := cfg.orbit.βcoset_ne_zero
  hExp_pos := cfg.orbit_h_pos

end SegmentedRAPParams

/-- Every identity-bearing datum is a type parameter: the problem types, acceptance predicates, AIRs,
auxiliary types, problem-indexed RAP parameters, and trace encoders.  Consequently replacing
`progAir`, `memAir`, or either parameter family changes the proposition being instantiated.
-/
class HasCanonicalRAP2
    (K : Type*) [Field K]
    (ProgProblem MemProblem : Type*)
    (progAccepts : ProgProblem → Prop)
    (memAccepts : MemProblem → Prop)
    (progAir memAir : Reified.AIR)
    (ProgAux : ProgProblem → Type*)
    (MemAux : MemProblem → Type*)
    (progParams : ProgProblem → SegmentedRAPParams K)
    (memParams : MemProblem → SegmentedRAPParams K)
    (encodeProg :
      (p : ProgProblem) → ProgAux p → Fin progAir.numTraceCols → K[X])
    (encodeMem :
      (p : MemProblem) → MemAux p → Fin memAir.numTraceCols → K[X]) : Prop where
  compute_iff : ∀ p,
    progAccepts p ↔
      ∃ a : ProgAux p, ∀ kind,
        ((progParams p).rap progAir kind).Satisfies (encodeProg p a)
  memory_iff : ∀ p,
    memAccepts p ↔
      ∃ a : MemAux p, ∀ kind,
        ((memParams p).rap memAir kind).Satisfies (encodeMem p a)

namespace HasCanonicalRAP2

variable {K : Type*} [Field K]
variable {ProgProblem MemProblem : Type*}

/-- The program RAP family.  This is derived data, not a replaceable class field. -/
@[reducible]
noncomputable def Rprog
    (progAir : Reified.AIR)
    (progParams : ProgProblem → SegmentedRAPParams K)
    (p : ProgProblem) (kind : Reified.ConstraintKind) : RAP K :=
  (progParams p).rap progAir kind

/-- The memory RAP family.  This is derived data, not a replaceable class field. -/
@[reducible]
noncomputable def Rmem
    (memAir : Reified.AIR)
    (memParams : MemProblem → SegmentedRAPParams K)
    (p : MemProblem) (kind : Reified.ConstraintKind) : RAP K :=
  (memParams p).rap memAir kind

@[simp]
theorem Rprog_pinned
    (progAir : Reified.AIR)
    (progParams : ProgProblem → SegmentedRAPParams K)
    (p : ProgProblem) (kind : Reified.ConstraintKind) :
    Rprog progAir progParams p kind =
      airToRAP (kindSeg progAir kind)
        (progParams p).chalVal (progParams p).pubVal
        (progParams p).eDeg (progParams p).hExp
        (progParams p).ω (progParams p).βcoset
        ((progParams p).domain kind)
        (progParams p).βcoset_ne_zero (progParams p).hExp_pos :=
  rfl

@[simp]
theorem Rmem_pinned
    (memAir : Reified.AIR)
    (memParams : MemProblem → SegmentedRAPParams K)
    (p : MemProblem) (kind : Reified.ConstraintKind) :
    Rmem memAir memParams p kind =
      airToRAP (kindSeg memAir kind)
        (memParams p).chalVal (memParams p).pubVal
        (memParams p).eDeg (memParams p).hExp
        (memParams p).ω (memParams p).βcoset
        ((memParams p).domain kind)
        (memParams p).βcoset_ne_zero (memParams p).hExp_pos :=
  rfl

end HasCanonicalRAP2

variable {K : Type*} [Field K]

/-- When every kind uses the same active domain, satisfying all filtered ordinary RAPs is
equivalent to satisfying the unfiltered AIR RAP.  This is the assembly seam used by the
row-local prototype below. -/
theorem segmentedRAP_satisfies_sameDomain_iff
    (air : Reified.AIR) (chalVal pubVal : ℕ → K)
    (eDeg hExp : ℕ) (ω βcoset : K) (H : Finset K)
    (hβ : βcoset ≠ 0) (hh1 : 1 ≤ hExp)
    (P : Fin air.numTraceCols → K[X]) :
    (∀ kind : Reified.ConstraintKind,
        (airToRAP (kindSeg air kind) chalVal pubVal eDeg hExp ω βcoset H hβ hh1).Satisfies P)
      ↔ (airToRAP air chalVal pubVal eDeg hExp ω βcoset H hβ hh1).Satisfies P := by
  rw [segmented_is_kinded, airToRAP_satisfies_iff]
  constructor
  · intro h x hx c hc
    exact h c hc x hx
  · intro h c hc x hx
    exact h x hx c hc

/-- Official row-local compute acceptance predicate, fixed outside the S2 class. -/
def nockRowLocalProgAccepts (p : ComputeProblem K) : Prop :=
  ∀ k, ComputeTable.Vcomp (p.inp k) (p.pub k) (p.dec k)

/-- Official row-local memory acceptance predicate, fixed outside the S2 class. -/
def nockRowLocalMemAccepts (p : MemProblem K) : Prop :=
  ∀ k, MemoryTable.Vmem (p.minp k) (p.mrow k)

/-- Official row-local compute AIR, fixed as a class index. -/
def nockRowLocalProgAir : Reified.AIR := computeAIR

/-- Official row-local memory AIR, fixed as a class index. -/
noncomputable def nockRowLocalMemAir (K : Type*) [Field K] : Reified.AIR :=
  memoryAIR (K := K)

/-- Official compute prover-witness family, fixed outside the S2 class. -/
abbrev NockRowLocalProgAux (p : ComputeProblem K) :=
  Fin p.n → ComputeTable.Extra K

/-- Official memory prover-witness family, fixed outside the S2 class. -/
abbrev NockRowLocalMemAux (p : MemProblem K) :=
  Fin p.n → K

/-- Official problem-indexed row-local compute RAP parameters. -/
noncomputable def nockRowLocalProgParams (p : ComputeProblem K) :
    SegmentedRAPParams K where
  chalVal := p.chalVal
  pubVal := fun _ => 0
  eDeg := p.eDeg
  hExp := p.hExp
  ω := p.ω
  βcoset := p.β
  domain := fun _ => Finset.image p.nodes Finset.univ
  βcoset_ne_zero := p.hβ
  hExp_pos := p.hh1

/-- Official problem-indexed row-local memory RAP parameters. -/
noncomputable def nockRowLocalMemParams (p : MemProblem K) :
    SegmentedRAPParams K where
  chalVal := p.chalVal
  pubVal := fun _ => 0
  eDeg := p.eDeg
  hExp := p.hExp
  ω := p.ω
  βcoset := p.β
  domain := fun _ => Finset.image p.nodes Finset.univ
  βcoset_ne_zero := p.hβ
  hExp_pos := p.hh1

/-- Official row-local compute trace encoder, fixed outside the S2 class. -/
noncomputable def nockRowLocalEncodeProg
    (p : ComputeProblem K) (ex : NockRowLocalProgAux p) :
    Fin nockRowLocalProgAir.numTraceCols → K[X] :=
  encodeComputeTrace
    (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state)
      (p.pub k) (p.dec k) (ex k))
    p.nodes

/-- Official row-local memory trace encoder, fixed outside the S2 class. -/
noncomputable def nockRowLocalEncodeMem
    (p : MemProblem K) (g : NockRowLocalMemAux p) :
    Fin (nockRowLocalMemAir K).numTraceCols → K[X] :=
  encodeMemoryTrace
    (fun k => memoryEnvFull (p.minp k) (MemoryTable.opSel (p.mrow k).st)
      (p.mrow k) (g k))
    p.nodes

/-- The fully indexed proposition implemented by the official row-local Nock S2 instance. -/
abbrev NockRowLocalHasCanonicalRAP2 (K : Type*) [Field K] : Prop :=
  HasCanonicalRAP2 K (ComputeProblem K) (MemProblem K)
    (nockRowLocalProgAccepts (K := K))
    (nockRowLocalMemAccepts (K := K))
    nockRowLocalProgAir (nockRowLocalMemAir K)
    (NockRowLocalProgAux (K := K)) (NockRowLocalMemAux (K := K))
    (nockRowLocalProgParams (K := K)) (nockRowLocalMemParams (K := K))
    (nockRowLocalEncodeProg (K := K)) (nockRowLocalEncodeMem (K := K))

/-- Type-level discrimination receipt: `computeAIR` and `memoryAIR` occur as explicit indices of
the official row-local S2 proposition.  Replacing either with an empty AIR produces a different
application of `HasCanonicalRAP2`, not another value of this proposition. -/
theorem nockRowLocalS2_type_exposes_AIRs (K : Type*) [Field K] :
    NockRowLocalHasCanonicalRAP2 K =
      HasCanonicalRAP2 K (ComputeProblem K) (MemProblem K)
        (nockRowLocalProgAccepts (K := K))
        (nockRowLocalMemAccepts (K := K))
        computeAIR (memoryAIR (K := K))
        (NockRowLocalProgAux (K := K)) (NockRowLocalMemAux (K := K))
        (nockRowLocalProgParams (K := K)) (nockRowLocalMemParams (K := K))
        (nockRowLocalEncodeProg (K := K)) (nockRowLocalEncodeMem (K := K)) :=
  rfl

/-- Row-local Nock prototype for the hardened interface.

All four
kinds use the current problem's active node set because `computeAIR` and `memoryAIR` are the
row-local AIRs.
-/
noncomputable instance nockRowLocalHasCanonicalRAP2 (K : Type*) [Field K] :
    NockRowLocalHasCanonicalRAP2 K where
  compute_iff p := by
    constructor
    · intro h
      obtain ⟨ex, hex⟩ :=
        (computeTable_reified_iff p.inp p.pub p.dec p.nodes p.hnodes p.chalVal
          p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz).mp h
      refine ⟨ex, ?_⟩
      simpa [nockRowLocalProgAir, nockRowLocalProgParams, nockRowLocalEncodeProg,
        SegmentedRAPParams.rap] using
        (segmentedRAP_satisfies_sameDomain_iff computeAIR p.chalVal (fun _ => 0)
          p.eDeg p.hExp p.ω p.β (Finset.image p.nodes Finset.univ)
          p.hβ p.hh1
          (encodeComputeTrace
            (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state)
              (p.pub k) (p.dec k) (ex k))
            p.nodes)).mpr hex
    · rintro ⟨ex, hex⟩
      apply
        (computeTable_reified_iff p.inp p.pub p.dec p.nodes p.hnodes p.chalVal
          p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz).mpr
      refine ⟨ex, ?_⟩
      apply
        (segmentedRAP_satisfies_sameDomain_iff computeAIR p.chalVal (fun _ => 0)
          p.eDeg p.hExp p.ω p.β (Finset.image p.nodes Finset.univ)
          p.hβ p.hh1
          (encodeComputeTrace
            (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state)
              (p.pub k) (p.dec k) (ex k))
            p.nodes)).mp
      simpa [nockRowLocalProgAir, nockRowLocalProgParams, nockRowLocalEncodeProg,
        SegmentedRAPParams.rap] using hex
  memory_iff p := by
    constructor
    · intro h
      obtain ⟨g, hg⟩ :=
        (memoryTable_reified_iff p.minp p.mrow p.nodes p.hnodes p.chalVal
          p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz).mp h
      refine ⟨g, ?_⟩
      simpa [nockRowLocalMemAir, nockRowLocalMemParams, nockRowLocalEncodeMem,
        SegmentedRAPParams.rap] using
        (segmentedRAP_satisfies_sameDomain_iff (memoryAIR (K := K)) p.chalVal (fun _ => 0)
          p.eDeg p.hExp p.ω p.β (Finset.image p.nodes Finset.univ)
          p.hβ p.hh1
          (encodeMemoryTrace
            (fun k => memoryEnvFull (p.minp k) (MemoryTable.opSel (p.mrow k).st)
              (p.mrow k) (g k))
            p.nodes)).mpr hg
    · rintro ⟨g, hg⟩
      apply
        (memoryTable_reified_iff p.minp p.mrow p.nodes p.hnodes p.chalVal
          p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz).mpr
      refine ⟨g, ?_⟩
      apply
        (segmentedRAP_satisfies_sameDomain_iff (memoryAIR (K := K)) p.chalVal (fun _ => 0)
          p.eDeg p.hExp p.ω p.β (Finset.image p.nodes Finset.univ)
          p.hβ p.hh1
          (encodeMemoryTrace
            (fun k => memoryEnvFull (p.minp k) (MemoryTable.opSel (p.mrow k).st)
              (p.mrow k) (g k))
            p.nodes)).mp
      simpa [nockRowLocalMemAir, nockRowLocalMemParams, nockRowLocalEncodeMem,
        SegmentedRAPParams.rap] using hg

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.HasCanonicalRAP2.Rprog_pinned
#print axioms Nock.NockVMROM.Thm54.HasCanonicalRAP2.Rmem_pinned
#print axioms Nock.NockVMROM.Thm54.segmentedRAP_satisfies_sameDomain_iff
#print axioms Nock.NockVMROM.Thm54.nockRowLocalS2_type_exposes_AIRs
#print axioms Nock.NockVMROM.Thm54.nockRowLocalHasCanonicalRAP2
