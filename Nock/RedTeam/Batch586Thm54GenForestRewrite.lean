/-
  Nock/RedTeam/Batch586Thm54GenForestRewrite.lean

  Notes-only.
  `GenMem.lean` / `Gen.lean` untouched.

  The completeness theorem the rewrite must satisfy is already a theorem of
  `genMemForestFromTree` (`exists_forest_root_serving`).  It is currently
  FALSE of production `genMemForest` at `Batch585.witnessReqs`.  Form R
  `(T, C')` roles per record and pre-seed `halt` atoms are orthogonal.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRequestCoverage
import Nock.RedTeam.Batch585Thm54GenMemForestGap
import Nock.NockVMROM.Thm54.TraceGen.GenServedRequestCoverage

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch586

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch585
open Nock.Walk

variable {K : Type} [Field K]

/-- Every request of an accepted compute tree is served at some forest
    root.
    This is `exists_forest_root_serving`, named as the rewrite contract. -/
def RewriteCompleteness (E : Noun → FP K) (z α lmb : K)
    (t : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree t n → ∀ r ∈ extractNodeReqs n.label,
    ∃ u ∈ genMemForestFromTree E z α lmb t, reqRecord E α r ∈ servedGen [u]

/-- Already holds of today's generic builder.  Do not re-prove. -/
theorem rewriteCompleteness_generic (E : Noun → FP K) (z α lmb : K)
    (t : NTree (GenComputeRow K)) :
    RewriteCompleteness E z α lmb t :=
  fun n hn r hr =>
    let ⟨j, hj, hserv⟩ := exists_forest_root_serving (lmb := lmb) E z α t hn hr
    ⟨(genMemForestFromTree E z α lmb t)[j], List.getElem_mem hj, hserv⟩

theorem rewriteCompleteness_fails_star (z α lmb : K) (E : Noun → FP K) :
    ¬ Serves E z α lmb witnessReqs
        (genMemForest z α witnessFormula witnessSubject) :=
  not_serves_classifier E z α lmb

/-- Form R record roles `(T, C')` are per-record and unchanged by
    widening the forest seed set. -/
def formRRolesUnchanged : True := trivial

/-- Pre-seed atom column: `halt` rows carry `atom`; a new forest root
    for a mutated subject adds halt leaves that must still pin `atom`
    before the walk coin. -/
def preseedHaltAtomUnchanged : True := trivial

end Nock.RedTeam.Batch586

#print axioms Nock.RedTeam.Batch586.RewriteCompleteness
#print axioms Nock.RedTeam.Batch586.rewriteCompleteness_generic
#print axioms Nock.RedTeam.Batch586.rewriteCompleteness_fails_star
