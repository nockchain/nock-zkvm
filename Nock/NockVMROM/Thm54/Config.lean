import Nock.Framework.Thm54
import Nock.ComputeTable
import Nock.MemoryTable

/-!
# Exact Theorem 5.4 configuration

This module owns the choices shared by the additive exact Theorem 5.4 surface.  It does not
assert any S1--S8 acceptance theorem.

There are three distinct values that older interfaces sometimes called `β`:

* `ChallengeVector.α` is the compute timestamp/line challenge;
* `ChallengeVector.β` is the memory-table LogUp pole challenge;
* `OrbitDomain.βcoset` is the nonzero RAP evaluation-orbit shift.

Likewise, the NPR seed `z` occurs only in `ChallengeVector`; it is not duplicated as a free
configuration field.
-/

namespace Nock.NockVMROM.Thm54

open Nock.Framework.Thm54

/-- All field challenges shared by one exact NockVMROM execution.

Each field has one role:

* `a`, `b`, and `c` are the three compute equality-RLC coefficients;
* `α` is the compute memory-timestamp and line-recurrence challenge;
* `z` is the noun-polynomial-representation fingerprint seed;
* `β` is the memory LogUp pole offset in `RLC^γ(record) - β`;
* `γ` is the memory-record RLC challenge.

The RAP orbit shift is deliberately absent: it is `ExactConfig.orbit.βcoset`.
-/
structure ChallengeVector (K : Type*) where
  /-- First compute equality-RLC coefficient. -/
  a : K
  /-- Second compute equality-RLC coefficient. -/
  b : K
  /-- Third compute equality-RLC coefficient. -/
  c : K
  /-- Compute timestamp/line-recurrence challenge. -/
  α : K
  /-- NPR fingerprint seed used by both tables. -/
  z : K
  /-- Memory-table LogUp pole offset. -/
  β : K
  /-- Memory-record random-linear-combination challenge. -/
  γ : K
  /-- Read by the
  memory chip's slot 8 and the compute chip's 𝕂 slot 9, by every honest row's `Pub.lambda`
  (`MemoryRowTemplate.encodeRow`) and by the IO encode `encRecFormR`.  `MemoryTable.formRDefault` is only a
  fixture's sample of this field. -/
  lam : K

namespace ChallengeVector

/-- The compute-table inputs selected by a shared challenge vector. -/
def computeInputs (v : ChallengeVector K) : ComputeTable.Inputs K :=
  { α := v.α, z := v.z, a := v.a, b := v.b, c := v.c }

/-- The memory-table inputs selected by a shared challenge vector. -/
def memoryInputs (v : ChallengeVector K) : MemoryTable.Inputs K :=
  { z := v.z, β := v.β, γ := v.γ }

/-- Challenge valuation in the full compute AIR's documented order
`(α, z, a, b, c)`. -/
def computeValuation [Zero K] (v : ChallengeVector K) : ℕ → K
  | 0 => v.α
  | 1 => v.z
  | 2 => v.a
  | 3 => v.b
  | 4 => v.c
  | _ => 0

/-- Challenge valuation in the full memory AIR's documented order `(z, β, γ)`.
    Slot 8 is the form R accounting base `λ`; the three-field `Inputs` carrier cannot
    hold it (`Gen.lean` constructs `⟨z, β, γ⟩`), so the RAP valuation takes `λ` as an
    extra argument (the row-copied `Pub.lambda`, constant across the table). -/
def memoryValuation [Zero K] (v : ChallengeVector K) : ℕ → K
  | 0 => v.z
  | 1 => v.β
  | 2 => v.γ
  | _ => 0

/-- Form R RAP valuation: `(z, β, γ)` plus `λ` at slot 8. -/
def memoryChalVal [Zero K] (v : ChallengeVector K) (lmb : K) : ℕ → K
  | 0 => v.z
  | 1 => v.β
  | 2 => v.γ
  | 8 => lmb
  | _ => 0

end ChallengeVector

/-- Shared, non-acceptance-bearing configuration for the exact Theorem 5.4 surface.

The active domains are positive prefixes of one certified orbit, not padded full cosets.
`eDeg = 1` records the honest limitation of the shipped single-`ω` reifier: the same `ω`
drives adjacent-row reads and has order `2^h`.  The node maps are not free injective maps;
their defining equations identify them with the corresponding active orbit prefixes.
-/
structure ExactConfig (F K : Type*) [Field F] [Field K] [Algebra F K] where
  /-- Every compute and memory field challenge for this configuration. -/
  challenges : ChallengeVector K
  /-- Bound used by the multiset-IO language. -/
  Ksz : ℕ
  /-- Number of roots in the authoritative memory forest. -/
  kMem : ℕ
  /-- Shared single-generator evaluation orbit. -/
  orbit : OrbitDomain K
  /-- The orbit exponent is positive, as required by the shipped adjacent-row RAP index set. -/
  orbit_h_pos : 1 ≤ orbit.h
  /-- Number of active compute rows. -/
  compRows : ℕ
  /-- Number of active memory rows. -/
  memRows : ℕ
  /-- The active compute prefix is nonempty. -/
  compRows_pos : 0 < compRows
  /-- The active memory prefix is nonempty. -/
  memRows_pos : 0 < memRows
  /-- The active compute prefix fits in the certified orbit. -/
  compRows_le : compRows ≤ 2 ^ orbit.h
  /-- The active memory prefix fits in the certified orbit. -/
  memRows_le : memRows ≤ 2 ^ orbit.h
  /-- RAP extension-degree metadata used by the shipped reifier. -/
  eDeg : ℕ
  /-- The exact single-generator construction honestly has extension-degree metadata one. -/
  eDeg_eq_one : eDeg = 1
  /-- Compute evaluation nodes, indexed only by active rows. -/
  compNodes : Fin compRows → K
  /-- Compute nodes are the active shifted-orbit prefix, not a free node map. -/
  compNodes_spec :
    ∀ i, compNodes i = orbit.βcoset * orbit.ω ^ (i : ℕ)
  /-- Memory evaluation nodes, indexed only by active rows. -/
  memNodes : Fin memRows → K
  /-- Memory nodes are the active shifted-orbit prefix, not a free node map. -/
  memNodes_spec :
    ∀ i, memNodes i = orbit.βcoset * orbit.ω ^ (i : ℕ)

namespace ExactConfig

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The domain assigned to each compute constraint kind. -/
noncomputable def computeDomain (cfg : ExactConfig F K) :
    Reified.ConstraintKind → Finset K
  | .row => cfg.orbit.rowDomain cfg.compRows
  | .transition => cfg.orbit.transitionDomain cfg.compRows cfg.compRows_pos
  | .boundary => cfg.orbit.boundaryDomain
  | .terminal => cfg.orbit.terminalDomain cfg.compRows cfg.compRows_pos

/-- The domain assigned to each memory constraint kind. -/
noncomputable def memoryDomain (cfg : ExactConfig F K) :
    Reified.ConstraintKind → Finset K
  | .row => cfg.orbit.rowDomain cfg.memRows
  | .transition => cfg.orbit.transitionDomain cfg.memRows cfg.memRows_pos
  | .boundary => cfg.orbit.boundaryDomain
  | .terminal => cfg.orbit.terminalDomain cfg.memRows cfg.memRows_pos

/-- Public form of the load-bearing compute-node orbit equation. -/
@[simp]
theorem compNodes_eq_orbitPoint (cfg : ExactConfig F K) (i : Fin cfg.compRows) :
    cfg.compNodes i = cfg.orbit.orbitPoint i := by
  simpa [OrbitDomain.orbitPoint] using cfg.compNodes_spec i

/-- Public form of the load-bearing memory-node orbit equation. -/
@[simp]
theorem memNodes_eq_orbitPoint (cfg : ExactConfig F K) (i : Fin cfg.memRows) :
    cfg.memNodes i = cfg.orbit.orbitPoint i := by
  simpa [OrbitDomain.orbitPoint] using cfg.memNodes_spec i

/-- The compute node map is injective because its orbit-prefix equation is load-bearing. -/
theorem compNodes_injective (cfg : ExactConfig F K) :
    Function.Injective cfg.compNodes := by
  intro i j hij
  apply cfg.orbit.orbitPoint_injective cfg.compRows_le
  simpa using hij

/-- The memory node map is injective because its orbit-prefix equation is load-bearing. -/
theorem memNodes_injective (cfg : ExactConfig F K) :
    Function.Injective cfg.memNodes := by
  intro i j hij
  apply cfg.orbit.orbitPoint_injective cfg.memRows_le
  simpa using hij

/-- No second compute node map satisfying the same orbit equations is an independent choice. -/
theorem compNodes_determined (cfg : ExactConfig F K) (nodes : Fin cfg.compRows → K)
    (h : ∀ i, nodes i = cfg.orbit.orbitPoint i) :
    nodes = cfg.compNodes := by
  funext i
  rw [h i, cfg.compNodes_eq_orbitPoint]

/-- No second memory node map satisfying the same orbit equations is an independent choice. -/
theorem memNodes_determined (cfg : ExactConfig F K) (nodes : Fin cfg.memRows → K)
    (h : ∀ i, nodes i = cfg.orbit.orbitPoint i) :
    nodes = cfg.memNodes := by
  funext i
  rw [h i, cfg.memNodes_eq_orbitPoint]

end ExactConfig

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExactConfig.compNodes_eq_orbitPoint
#print axioms Nock.NockVMROM.Thm54.ExactConfig.memNodes_eq_orbitPoint
#print axioms Nock.NockVMROM.Thm54.ExactConfig.compNodes_injective
#print axioms Nock.NockVMROM.Thm54.ExactConfig.memNodes_injective
#print axioms Nock.NockVMROM.Thm54.ExactConfig.compNodes_determined
#print axioms Nock.NockVMROM.Thm54.ExactConfig.memNodes_determined
