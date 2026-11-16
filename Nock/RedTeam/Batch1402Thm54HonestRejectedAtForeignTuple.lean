import Nock.RedTeam.Batch1257Thm54HonestSeedWidenedChain
import Nock.RedTeam.Batch366Thm54ForeignCoinRejection
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1402Thm54HonestRejectedAtForeignTuple.lean

  * `honest_rejected_at_foreign_ioPole_zmod`: `nockCompiles_zmod`'s binders verbatim; the package is the
    chain's `genPkg` (through `Batch1257.nvX_zmod` at `X = ∅`).  Conclusion: `Stmt ∧ claim ∧ lam`, the
    honest pair `(QcH, QmH)` is accepted at `honestTuple` (`Batch1061.gen_honest_accepted`), and at
    the tuple `c' := withIoPole honestTuple (pole + 1)` -- which differs from `honestTuple` in exactly
    the IO-pole coordinate `c.2.1.2` -- NO compute trace pairs with the honest memory trace
    (`Batch366.foreign_ioPole_rejects_succ`).
  * The coordinate that breaks it: the IO pole `c.2.1.2`, read by the memory gate
    `OptimizedMemoryGateBasis.denominatorPinMixed` (`role 37 − (pole + RLC^γ(record))`,
    the paper), linear in the pole, so every foreign pole is rejected.
  * The concrete zero-binder instance is in `Batch1401` (F73 program of `Batch1259`).

  `nockCompiles_zmod` now takes
  the memory walk coin `αW` explicitly (27/14); this receipt keeps the pre-S2 binders and builds its
  package through `Batch1257`'s chain at `mwa = α`, i.e. it is `nockCompiles_zmod` at `αW := α`
  (honest acceptance is `mwa`-free, `Batch1420.gen_honest_accepted12`).

  Scope: one trace pair, one tuple, fixed.  No interactive (`:966`) statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1402

open scoped Polynomial
open Polynomial
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.RedTeam.Batch906 (QcH QmH)
open Nock.RedTeam.Batch366 (withIoPole castMemTrace)

noncomputable section

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional (ZMod p) K]

/-- The foreign tuple: `honestTuple` with only the IO pole moved by one. -/
abbrev foreignTuple {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage (ZMod p) K hOrb) :
    OptimizedProductionChallengeTuple K (ZMod p) :=
  withIoPole P.honestTuple (P.honestTuple.2.1.2 + 1)

/-- The receipt predicate at a package: honest pair accepted at `honestTuple`, the foreign tuple
differs from it, and at the foreign tuple the honest memory trace admits no compute trace. -/
def HonestRejectedAtForeign {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage (ZMod p) K hOrb) :
    Prop :=
  DeployedAcceptanceAt P P.honestTuple (QcH P) (QmH P) ∧
    foreignTuple P ≠ P.honestTuple ∧
    ∀ Qc : Fin (P.computeChipAt (foreignTuple P)).rap.w → (ZMod p)[X],
      ¬ DeployedAcceptanceAt P (foreignTuple P) Qc
        (castMemTrace P P.honestTuple (foreignTuple P) (QmH P))

theorem foreignTuple_ne {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage (ZMod p) K hOrb) :
    foreignTuple P ≠ P.honestTuple := by
  intro h
  have h2 := congrArg (fun c : OptimizedProductionChallengeTuple K (ZMod p) => c.2.1.2) h
  simp only [foreignTuple, withIoPole] at h2
  exact one_ne_zero (add_left_cancel (h2.trans (add_zero _).symm))

/-- From honest acceptance alone, the foreign-tuple rejection (any package). -/
theorem honestRejectedAtForeign_of_acc {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage (ZMod p) K hOrb)
    (hacc : DeployedAcceptanceAt P P.honestTuple (QcH P) (QmH P)) :
    HonestRejectedAtForeign P :=
  ⟨hacc, foreignTuple_ne P, fun _ h =>
    Nock.RedTeam.Batch366.foreign_ioPole_rejects_succ P P.honestTuple (QmH P)
      hacc.memory_satisfies h.memory_satisfies⟩

/-- **Item (ii) at every generated program** (`nockCompiles_zmod`'s binders verbatim). -/
theorem honest_rejected_at_foreign_ioPole_zmod
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ HonestRejectedAtForeign package := by
  obtain ⟨P, h1, h2, h3, h4, -⟩ :=
    Nock.RedTeam.Batch1257.nvX_zmod α lmb hrun hbound hs hf hΛp hp hp64 hK hF hwin hKszChar
    ∅ (by simp) (fun P => HonestRejectedAtForeign P)
    (fun stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM
        hrows hFp hsB hfB hG hp64 _ =>
      honestRejectedAtForeign_of_acc _
        (Nock.RedTeam.Batch1061.gen_honest_accepted (F := ZMod p) (K := K) stc hK pOrbit hcap n
          hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hFp hsB hfB hG
          hp64))
  exact ⟨P, h1, h2, h3, h4⟩

end

end Nock.RedTeam.Batch1402

#print axioms Nock.RedTeam.Batch1402.foreignTuple_ne
#print axioms Nock.RedTeam.Batch1402.honestRejectedAtForeign_of_acc
#print axioms Nock.RedTeam.Batch1402.honest_rejected_at_foreign_ioPole_zmod
