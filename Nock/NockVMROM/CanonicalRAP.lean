import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language
import Nock.NockVMROM.TraceEncoding

/-!
# S2 `HasCanonicalRAP` — the NockVMROM canonical-RAP instance

Wraps the two already-proven whole-trace bridge theorems
`Nock.Reified.computeTable_reified_iff` / `Nock.Reified.memoryTable_reified_iff`
(TraceEncoding.lean) into the `Nock.Framework.HasCanonicalRAP` interface on the NockVMROM tag.

The disclosed well-formedness (injective evaluation nodes, shared challenge vector, per-row `WF`,
`z ≠ 0`) is bundled into the two problem structures `ComputeProblem` / `MemProblem`, so the
`compute_iff` / `memory_iff` correspondences are *unconditional* over those structures — they are
literally the two bridge theorems applied field-by-field.  The `Rprog`/`Rmem` witnesses are the
reified `computeAIR`/`memoryAIR` RAPs at trivial parameters; the *load-bearing* content is the
per-problem satisfiability predicate (which reifies at each problem's own parameters), not these.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework Nock.Reified Nock.ComputeTable
open Classical

/-- **Compute-side problem (bundled WF).**  A finite family of `n` compute rows together with all
    hypotheses of `computeTable_reified_iff`: injective evaluation `nodes`, shared challenge vector
    `chalVal`, RAP parameters `(eDeg, hExp, ω, β)` with `β ≠ 0` and `1 ≤ hExp`, per-row
    well-formedness `WF` and non-degeneracy `z ≠ 0`. -/
structure ComputeProblem (K : Type*) [Field K] where
  n : ℕ
  inp : Fin n → ComputeTable.Inputs K
  pub : Fin n → ComputeTable.Pub K
  dec : Fin n → ComputeTable.Dec K
  nodes : Fin n → K
  chalVal : ℕ → K
  eDeg : ℕ
  hExp : ℕ
  ω : K
  β : K
  hnodes : Function.Injective nodes
  hβ : β ≠ 0
  hh1 : 1 ≤ hExp
  hchal : ∀ k, (computeEnvFull (inp k) (opSel (pub k).state) (pub k) (dec k) ⟨0, 0⟩).chal = chalVal
  hwf : ∀ k, ComputeTable.WF (inp k) (pub k)
  hz : ∀ k, (inp k).z ≠ 0

/-- **Memory-side problem (bundled WF).**  The memory analogue of `ComputeProblem`: a finite family
    of `n` memory rows with the hypotheses of `memoryTable_reified_iff`. -/
structure MemProblem (K : Type*) [Field K] where
  n : ℕ
  minp : Fin n → MemoryTable.Inputs K
  mrow : Fin n → MemoryTable.Pub K
  nodes : Fin n → K
  chalVal : ℕ → K
  eDeg : ℕ
  hExp : ℕ
  ω : K
  β : K
  hnodes : Function.Injective nodes
  hβ : β ≠ 0
  hh1 : 1 ≤ hExp
  hchal : ∀ k, (memoryEnvFull (minp k) (MemoryTable.opSel (mrow k).st) (mrow k) 0).chal = chalVal
  hwf : ∀ k, MemoryTable.WF (minp k) (mrow k)
  hz : ∀ k, (minp k).z ≠ 0

/-- **The NockVMROM canonical-RAP instance.**  Realises `HasCanonicalRAP` on the
    NockVMROM tag over the field `K` the compute/memory tables live over.  `progAccepts` is the
    per-row algorithmic `Vcomp` fold and `progSatisfiable` the reified-`computeAIR` satisfaction of
    the Lagrange trace encoding (memory analogously); the two `iff`s are exactly the whole-trace
    bridge theorems `computeTable_reified_iff` / `memoryTable_reified_iff`. -/
noncomputable instance nock_hasCanonicalRAP (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasCanonicalRAP (Tag F K α β Ksz) (nmrMEF F K) K where
  Rprog := Nock.Framework.Reify.airToRAP computeAIR (fun _ => 0) (fun _ => 0) 1 1 1 1 ∅ one_ne_zero (le_refl 1)
  Rmem  := Nock.Framework.Reify.airToRAP (memoryAIR (K := K))  (fun _ => 0) (fun _ => 0) 1 1 1 1 ∅ one_ne_zero (le_refl 1)
  ProgProblem := ComputeProblem K
  MemProblem := MemProblem K
  progAccepts p := ∀ k, ComputeTable.Vcomp (p.inp k) (p.pub k) (p.dec k)
  progSatisfiable p := ∃ ex : Fin p.n → ComputeTable.Extra K,
    (Nock.Framework.Reify.airToRAP computeAIR p.chalVal (fun _ => 0) p.eDeg p.hExp p.ω p.β
        (Finset.image p.nodes Finset.univ) p.hβ p.hh1).Satisfies
      (encodeComputeTrace (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state) (p.pub k) (p.dec k) (ex k)) p.nodes)
  memAccepts p := ∀ k, MemoryTable.Vmem (p.minp k) (p.mrow k)
  memSatisfiable p := ∃ g : Fin p.n → K,
    (Nock.Framework.Reify.airToRAP (memoryAIR (K := K)) p.chalVal (fun _ => 0) p.eDeg p.hExp p.ω p.β
        (Finset.image p.nodes Finset.univ) p.hβ p.hh1).Satisfies
      (encodeMemoryTrace (fun k => memoryEnvFull (p.minp k) (MemoryTable.opSel (p.mrow k).st) (p.mrow k) (g k)) p.nodes)
  compute_iff p := computeTable_reified_iff p.inp p.pub p.dec p.nodes p.hnodes p.chalVal p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz
  memory_iff p := memoryTable_reified_iff p.minp p.mrow p.nodes p.hnodes p.chalVal p.eDeg p.hExp p.ω p.β p.hβ p.hh1 p.hchal p.hwf p.hz

#print axioms nock_hasCanonicalRAP

end Nock.NockVMROM
