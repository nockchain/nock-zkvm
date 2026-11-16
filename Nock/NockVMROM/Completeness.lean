import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language
import Nock.NockVMROM.CanonicalRAP

/-!
# S6 — perfect (algebraic) completeness

Perfect completeness is exactly the forward (`.mp`) direction of the proven S2 compute bridge: an
accepted compute execution (`∀ k, V_comp`) has a satisfying reified-RAP assignment.  This is
**algebraic/RAP completeness only** — NOT a cryptographic IOP acceptance-probability claim (that
remains the explicit Tier-3 boundary).  Reuses `ComputeProblem` (the disclosed-WF trace family) and
`computeTable_reified_iff`.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework Nock.Reified Nock.ComputeTable
open Classical

/-- The NockVMROM completeness model: a compute problem is *accepted* iff every row passes `V_comp`,
    and *has a satisfying assignment* iff the reified compute RAP is satisfied by some Lagrange
    encoding of the rows. -/
noncomputable def nockCompletenessModel (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    CompletenessModel (Tag F K α β Ksz) (nmrMEF F K) K where
  Problem := ComputeProblem K
  accepted p := ∀ k, ComputeTable.Vcomp (p.inp k) (p.pub k) (p.dec k)
  hasSatisfyingAssignment p := ∃ ex : Fin p.n → ComputeTable.Extra K,
    (Nock.Framework.Reify.airToRAP computeAIR p.chalVal (fun _ => 0) p.eDeg p.hExp p.ω p.β
        (Finset.image p.nodes Finset.univ) p.hβ p.hh1).Satisfies
      (encodeComputeTrace
        (fun k => computeEnvFull (p.inp k) (opSel (p.pub k).state) (p.pub k) (p.dec k) (ex k)) p.nodes)

/-- **S6: NockVMROM has perfect (algebraic) completeness** — accepted executions have satisfying
    reified-RAP assignments, via the forward direction of the S2 compute bridge. -/
instance nock_hasPerfectCompleteness (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasPerfectCompleteness (Tag F K α β Ksz) (nmrMEF F K) K (nockCompletenessModel F K α β Ksz) where
  complete p hp :=
    (computeTable_reified_iff p.inp p.pub p.dec p.nodes p.hnodes p.chalVal p.eDeg p.hExp p.ω p.β
      p.hβ p.hh1 p.hchal p.hwf p.hz).mp hp

end Nock.NockVMROM

#print axioms Nock.NockVMROM.nock_hasPerfectCompleteness
