/-
  Nock/RedTeam/Batch263Thm54BoundedPremisesAtTierA.lean

  **`GenNockCompilesBounded` instantiated: Tier A's program satisfies the program-level premises
  that replaced `hb` and `haxis`, and the ROM transport `Batch251` left undone is done here.**

  Three things, and the third is what makes the first two more than a rename.

  1. `b263_nockCompiles_bounded` — `nockCompiles_of_accepted_bounded` at Tier A.  It is
     `Batch251.b251_nockCompiles` with `Batch180.dot_hb` and `Batch180.dot_haxis` **deleted** and
     the three program measurements `b263_subject_bounded` / `b263_formula_bounded` /
     `b263_evalG` supplied in their place.  So the premise list of the derived form is inhabited
     at a live configuration, and the two facts it no longer needs are visibly unused.

  2. `b263_nockCompiles_grom` — `nockCompiles_of_grom` at Tier A.  `Batch251`'s own "Not claimed"
     recorded that `nockCompiles_of_rom`'s premise list had only an *equation-mediated* witness,
     because its premises are stated at `romTree hrom` while every Tier A fact is recorded at
     `dotTree`.  `nockCompiles_of_grom_atTree` runs that transport generically, and this theorem
     applies it, so the witness is a compiled term.  **That sentence of `Batch251` is corrected at
     source.**

  3. `b263_overflow_*` — the guard is not free.  `evalGRom q` is **strictly** stronger than
     `evalRom`: on `*[0 [4 [1 4]]]` at `q = 5` the ROM evaluator returns `.atom 5` and the guarded
     ROM evaluator returns `none`, because `5 < 5` is false.

  **Scope.**  One program, one configuration — Tier A over `GaloisField 769 3`, exactly
  `Batch251`'s.  Tier A has no `OP_4` at all, so its guarded run is the unguarded one at any
  `1 < q`; (3) is what keeps that from being mistaken for generality.

  **Not claimed.**  `GoodSeed.nockCompiles_of_grom_atRomSeed` is *not* instantiated here: its
  trace-level premises are stated at `romSeed`, the compiler's `Classical.choose`, and Tier A's
  facts are recorded at the literal seed `φ(8)`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch251Thm54NockCompiles
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch263

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




/-! ## 1. The three program measurements

`hs`, `hf` and `hG` are the inputs `genComputeSkeleton_skeletonBounded` and
`genComputeSkeleton_axisRange` spend.  All three are decidable on Tier A's source text; none
mentions the compiled skeleton. -/

/-- Every atom of the subject is `< 769`. -/
theorem b263_subject_bounded : FieldEmbedding.BoundedBy 769 dotSubject := by
  simp [dotSubject]

/-- Every atom of the formula is `< 769`. -/
theorem b263_formula_bounded : FieldEmbedding.BoundedBy 769 dotFormula := by
  simp [dotFormula, dotParentTail, dotBranchPair, dotCondFormula, dotThenFormula,
    dotElseFormula, dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail,
    dotCoreFormula, dotCore, dotElem0, dotElem1, FieldEmbedding.BoundedBy]

/-- The guarded run, at the fuel `genComputeSkeleton_dot 0` uses.  Tier A has no `OP_4`, so the
guard never fires. -/
theorem b263_evalG : FieldEmbedding.evalGBy 769 4 dotSubject dotFormula = some dotResult := by
  simp [FieldEmbedding.evalGBy, dotSubject, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
    dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
    dotCore, dotElem0, dotElem1, dotResult, Noun.slot]

/-- And the guarded **ROM** run, the single antecedent `nockCompiles_of_grom` takes. -/
theorem b263_grom : evalGRom 769 4 dotSubject dotFormula = some dotResult := by
  simp [evalGRom, dotSubject, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
    dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
    dotCore, dotElem0, dotElem1, dotResult, Noun.slot]

/-! ## 2. `nockCompiles_of_accepted_bounded` at Tier A

`Batch251.b251_nockCompiles` with `Batch180.dot_hb` and `Batch180.dot_haxis` gone. -/

/-- **`∃ package, OptimizedFullStrictThm54Statement package ∧ the package commits Tier A's own
triple`**, from the form whose skeleton-level premises are derived. -/
noncomputable def b263_nockCompiles_bounded :=
  nockCompiles_of_accepted_bounded (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    Batch216.b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    b263_subject_bounded b263_formula_bounded b263_evalG
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch191.b191_hKsz2
    (by norm_num) DotConfig769.ringChar_K.symm
    Batch180.dot_hlt
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    Batch221.b221_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
    DotConfig769.stateTagChar DotConfig769.basis DotConfig769.strictOrbit Batch251.b251_hcap
    255 Batch251.b251_hreqn Batch251.b251_hrespn Batch246.b246_hcard
    2 2 5 (fun j => (j : DF) + 1) 2
    (fun hge => by
      change (bfsForest [genComputeRows seedZ alphaA (dotTree (K := DK))]).length ≤
        orderOf (2 : DK)
      rw [Batch180.dot_compRowsLen]
      exact Batch246.b246_two_order_ge 8 (by norm_num))
    (fun _ => by
      change (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
          (dotTree (K := DK)))).length ≤ orderOf (2 : DK)
      rw [Batch180.dot_memRowsLen]
      have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
        (map_natCast (algebraMap DF DK) 2).symm
      rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
        (RingHom.injective (algebraMap DF DK)) (2 : DF)]
      have : orderOf (2 : DF) = 384 :=
        Nock.NockVMROM.Thm54.TraceGen.DotConfig769.goldilocks769_two_order
      omega)
    Batch246.b246_hrows DotConfig769.dot_primeField Batch221.b221_laterSeedZeros

/-! ## 3. The ROM transport `Batch251` left undone

`romTree` is `Classical.choose`, so a fact recorded at `dotTree` does not typecheck against a
premise stated at `romTree hrom` until the two are identified.  `nockCompiles_of_grom_atTree`
does that identification generically — by `.ok`-injectivity against `romTree_spec`, then `subst`
— so every fact below is Tier A's own, at `dotTree`, with no transport written here. -/

/-- **`nockCompiles_of_grom` at Tier A**, through the transport form.  Every trace-level premise
is Tier A's own fact at `dotTree`; `nockCompiles_of_grom_atTree` identifies that tree with
`romTree` and applies `nockCompiles_of_grom`.  So that theorem's premise list is inhabited by a
compiled term, not by an equation. -/
noncomputable def b263_nockCompiles_grom :=
  nockCompiles_of_grom_atTree (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    Batch216.b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    b263_subject_bounded b263_formula_bounded b263_grom
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch191.b191_hKsz2
    (by norm_num) DotConfig769.ringChar_K.symm
    Batch180.dot_hlt
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    Batch221.b221_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
    DotConfig769.stateTagChar DotConfig769.basis DotConfig769.strictOrbit Batch251.b251_hcap
    255 Batch251.b251_hreqn Batch251.b251_hrespn Batch246.b246_hcard
    2 2 5 (fun j => (j : DF) + 1) 2
    (fun hge => by
      change (bfsForest [genComputeRows seedZ alphaA (dotTree (K := DK))]).length ≤
        orderOf (2 : DK)
      rw [Batch180.dot_compRowsLen]
      exact Batch246.b246_two_order_ge 8 (by norm_num))
    (fun _ => by
      change (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
          (dotTree (K := DK)))).length ≤ orderOf (2 : DK)
      rw [Batch180.dot_memRowsLen]
      have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
        (map_natCast (algebraMap DF DK) 2).symm
      rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
        (RingHom.injective (algebraMap DF DK)) (2 : DF)]
      have : orderOf (2 : DF) = 384 :=
        Nock.NockVMROM.Thm54.TraceGen.DotConfig769.goldilocks769_two_order
      omega)
    Batch246.b246_hrows DotConfig769.dot_primeField Batch221.b221_laterSeedZeros

/-! ## 4. The guard is a real restriction

Without this, `hgrom` could be read as `hrom` under another name. -/

/-- Subject `0`, formula `[4 [1 4]]` — increment the constant `4`. -/
def ovSubject : Noun := .atom 0
/-- `*[0 4 [1 4]] = 5`. -/
def ovFormula : Noun := .cell (.atom 4) (.cell (.atom 1) (.atom 4))

/-- The ROM evaluator succeeds: `5` is a perfectly good Nock atom. -/
theorem b263_overflow_evalRom : evalRom 2 ovSubject ovFormula = some (.atom 5) := by
  decide

/-- The guarded ROM evaluator does not, at `q = 5`: `5 < 5` is false. -/
theorem b263_overflow_evalGRom : evalGRom 5 2 ovSubject ovFormula = none := by
  decide

/-- **So `evalGRom q` is strictly stronger than `evalRom`**, and `hgrom` is a side condition and
not a restatement.  `nockCompiles_of_grom` therefore does not cover every ROM program — it covers
the ones whose run fits the characteristic. -/
theorem b263_guard_is_strict :
    ∃ fuel s f r, evalRom fuel s f = some r ∧ evalGRom 5 fuel s f = none :=
  ⟨2, ovSubject, ovFormula, .atom 5, b263_overflow_evalRom, b263_overflow_evalGRom⟩

end

end Nock.RedTeam.Batch263

#print axioms Nock.RedTeam.Batch263.b263_subject_bounded
#print axioms Nock.RedTeam.Batch263.b263_formula_bounded
#print axioms Nock.RedTeam.Batch263.b263_evalG
#print axioms Nock.RedTeam.Batch263.b263_grom
#print axioms Nock.RedTeam.Batch263.b263_nockCompiles_bounded
#print axioms Nock.RedTeam.Batch263.b263_nockCompiles_grom
#print axioms Nock.RedTeam.Batch263.b263_overflow_evalRom
#print axioms Nock.RedTeam.Batch263.b263_overflow_evalGRom
#print axioms Nock.RedTeam.Batch263.b263_guard_is_strict
