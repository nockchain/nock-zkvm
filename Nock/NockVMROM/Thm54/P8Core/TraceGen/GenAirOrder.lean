/-
  Nock/NockVMROM/Thm54/P8Core/TraceGen/GenAirOrder.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.TraceGen.GenAirOrder`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenAirOrder.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable
variable {K : Type} [Field K]
set_option linter.unusedSimpArgs false

/-- Swap a two-element child list; identity on every other length. -/
def swapPair {α : Type*} : List α → List α
  | [a, b] => [b, a]
  | cs => cs

/-- Opcodes whose DFS child order is the reverse of AIR `sf` slots. -/
def airNeedsSwap : State → Bool
  | .s6 | .s7 | .s8 => true
  | _ => false

/-- Recursively put generated children into AIR `sf` order. -/
def airReorder : NTree (GenComputeRow K) → NTree (GenComputeRow K)
  | .node g cs =>
    let cs' := cs.map airReorder
    if airNeedsSwap g.skel.state then
      .node g (swapPair cs')
    else
      .node g cs'

theorem airReorder_label (t : NTree (GenComputeRow K)) :
    (airReorder t).label = t.label := by
  cases t with
  | node g cs =>
    simp [airReorder]
    split_ifs <;> rfl

end Nock.NockVMROM.Thm54.TraceGen
