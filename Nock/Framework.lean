import Nock.Framework.Core
import Nock.Framework.FixedPreprocessingRAP
import Nock.Framework.EndpointMasks
import Nock.Framework.Separation
import Nock.Framework.Traversal
import Nock.Framework.Verification
import Nock.Framework.NockInstances

/-!
# Generic compilation framework (§2–§3) — the reusable abstractions

This module formalises the paper's **generic** framework abstractions as faithful Lean
structures, and proves that the concrete Nock construction is an **instance** of the
generic framework.

Definitions (all `📐` — carry no proof obligation, faithful & cited):

* `MEF`               — memory encoding family `(A, VD, T)`
* `IOP`               — interactive oracle proof interface
* `RAP` / `RAP.Satisfies` — randomized AIR with preprocessing + satisfaction
* `MES`               — uniquely memory-execution separable language
* `CanonicalRAP`      — two sub-RAPs sharing IO                            (Def:Canonical_RAP)
* `OpcodeMemOneHot`   — opcode/memory one-hot of size `N_OP`, arity `M_OP`
* `Traversable`       — `(F,F*)`-traversable
* `Fib.*`             — Fibonacci `L_Fib ≡ L_RVT^{G,2}` sanity instance   (Example:fibonacci)

Instance theorems (Nock ⊂ the framework):

* `nock_traversable`      — the Nock compute/memory languages are `(Fcomp, Fmem)`-traversable
* `nock_opcode_oneHot`    — the compute-table opcode selector is one-hot (Def:one-hot, cond. 1)
* `nock_MES` / `nock_canonicalRAP` — Nock as a MES / canonical-RAP instance (see docstrings for
  what is proven vs. carried as an explicit cross-module hypothesis, and why).

## Axiom / crypto boundary (Tier-3, flagged, NOT proved)
`IOP` is a structural **interface**: its completeness/soundness fields constrain an abstract
probability model (`ℝ`-valued), but the cryptographic state-restoration soundness itself is the
Tier-3 crypto boundary and is *not* proved here.  No `axiom` is
declared in this module; the only axiom reachable is `Field.goldilocks_prime`.

`Def:unique_request` / `cor_uni_req_uni_resp` live in `Nock.IO`; they are reused here.
-/

#print axioms Nock.Framework.Reify.airToRAP_satisfies_iff
#print axioms Nock.Framework.Reify.eval_exprToMv
#print axioms Nock.Framework.Reify.compose_eval
#print axioms Nock.Framework.Reify.exprToMv_vars
#print axioms Nock.Framework.nock_canonicalRAP_ofReified
#print axioms Nock.Framework.Fib.RVT_FG_unique
