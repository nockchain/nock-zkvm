/-
  Nock/RedTeam/Batch251Thm54NockCompiles.lean

  Nothing here re-proves the statement: `nockCompiles_of_accepted` is
  applied.

  §2 is the ROM side.  `Batch165.gen_op10_notROM` recorded that the generator declines `OP_10` as a
  single-case fact; what was missing was the *semantic* half — that `Nock.evalN` succeeds on such
  programs, so the restriction in `nockCompiles_of_rom` is not decorative.  `b251_op10_*` is a
  concrete `OP_10` program on which `evalN` returns a value, `evalRom` returns `none`, and the
  generator answers `.error.notROM`.  And `b251_rom_dot` is the other side: Tier A's program *is*
  a terminating ROM program by the semantic condition, so `evalRom` is not the empty predicate.

  **Scope.**  One program, one configuration — Tier A over `GaloisField 769 3`, seed `φ(8)`,
  `α = φ(4)`, coins `(0,0,0)`, `Ksz = 64`, `Λ = 22`, table orbit `h = 8`, package orbit
  `StrictOrbitDomain F 3 8`.  The capstone type `optimizedFullStrictNockVMROM_of_package` and the
  `11+1+2` accounting are untouched, and `Gen.lean` is unedited.

  This
  batch does not instantiate `nockCompiles_of_rom`, the form whose antecedent is
  `evalRom … = some result` rather than generator acceptance.  Its trace-level premises are stated
  at `romTree hrom`, and `b251_romTree_dot` is the equation that would transport Tier A's facts
  (all recorded at `dotTree`) onto it; the transport was described here as running "through the
  dependent `hconf`/`hbad` chain" and not done, leaving an *equation-mediated* witness.  **It is
  done now**, at the guarded ROM antecedent: `TraceGen.nockCompiles_of_grom_atTree` performs the
  transport once and generically, where the tree is still a variable and `subst` applies, and
  `Batch263Thm54BoundedPremisesAtTierA.b263_nockCompiles_grom` is the compiled term at this very
  configuration.  The diagnosis above was right about *where* the difficulty sits: at a call site
  `▸` fails on exactly `hKsz2` and `hbad`, the two arguments whose types mention earlier premises.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompiles
import Nock.RedTeam.Batch165Thm54DoublingWitness
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch251

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




/-! ## 1. The §1 existential, at Tier A -/

/-- The table orbit is no taller than the package orbit. -/
theorem b251_hcap : 2 ^ DotConfig769.executionOrbit.h ≤ 2 ^ 8 := by
  norm_num [DotConfig769.executionOrbit]

/-- The request column is the thirteen records `Batch211` measures. -/
theorem b251_hreqn :
    accAt (airReorder (dotTree (K := DK)))
      (bfsRows (airReorder (dotTree (K := DK)))).length ≤ 255 := by
  rw [Batch211.b211_accAt_eq_13]; norm_num

/-- The memory table is the `184` rows `Batch180` measures. -/
theorem b251_hrespn :
    (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length
      ≤ 255 := by
  rw [Batch180.dot_memRowsLen]; norm_num

/-- The premise list of `nockCompiles_of_accepted` is therefore inhabited. -/
theorem b251_nockCompiles
    (hax : FormRAxisBound
      Batch246.b246Package.optimized.sampled
      Batch246.b246Package.optimized.basis)
    (hbasis : FormRBasis DotConfig769.basis)
    (hwidth : FormRWidth DF) :
    ∃ package : OptimizedFullStrictNockVMROMPackage DF DK 8,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨dotSubject, dotFormula, dotResult⟩ := by
  obtain ⟨package, hstmt, hclaim, -⟩ := nockCompiles_of_accepted (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    Batch216.b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch191.b191_hKsz2
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    Batch221.b221_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
    Batch180.dot_hlt Batch221.b221_laterSeedZeros
    DotConfig769.stateTagChar DotConfig769.basis DotConfig769.strictOrbit b251_hcap
    255 b251_hreqn b251_hrespn Batch246.b246_hcard
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
    Batch246.b246_hrows DotConfig769.dot_evalG769 DotConfig769.dot_primeField hax hbasis hwidth
  exact ⟨package, hstmt, hclaim⟩

/-! ## 2. The claim conjunct is not trivially true

These two
theorems say the conjunct actually pins the result: it determines it, and it fails at a wrong
one. -/

/-- The conjunct determines the result. -/
theorem b251_claim_pins_result {r : Noun}
    (h : Batch246.b246Package.optimized.verifier.raw.claim = ⟨dotSubject, dotFormula, r⟩) :
    r = dotResult := by
  rw [Batch246.b246_claim_triple] at h
  exact (congrArg P8PublicClaim.result h).symm

/-- And it is false at a wrong result, so it is a real constraint on the emitted package. -/
theorem b251_claim_not_vacuous :
    Batch246.b246Package.optimized.verifier.raw.claim ≠
      ⟨dotSubject, dotFormula, .atom 0⟩ := by
  intro h
  have := b251_claim_pins_result h
  rw [dotResult] at this
  exact absurd this (by decide)

/-! ## 3. The ROM restriction, both directions

`Batch165.gen_op10_notROM` says the generator declines `OP_10`.  What makes the restriction in
`nockCompiles_of_rom` necessary rather than cosmetic is that `Nock.evalN` *succeeds* on such a
program — so `hrun : evalN … = some result` alone cannot imply acceptance.  the paper has
`𝒪𝒫 = {OP_0, …, OP_10}` and the paper removes `OP_10`; the program below is exactly the
removed opcode. -/

/-- Subject `[1 2]`. -/
def op10Subject : Noun := .cell (.atom 1) (.atom 2)

/-- `*[a 10 [2 [1 5]] [0 1]]` — write `5` at axis `2` of `a`.  the paper (the `OP_10` clause). -/
def op10Formula : Noun :=
  .cell (.atom 10)
    (.cell (.cell (.atom 2) (.cell (.atom 1) (.atom 5))) (.cell (.atom 0) (.atom 1)))

/-- `#[2 5 [1 2]] = [5 2]`. -/
def op10Result : Noun := .cell (.atom 5) (.atom 2)

/-- **The reference interpreter succeeds** on the `OP_10` program. -/
theorem b251_op10_evalN : Nock.evalN 3 op10Subject op10Formula = some op10Result := by
  simp [Nock.evalN, op10Subject, op10Formula, op10Result, Noun.edit, Noun.slot]

/-- **The ROM semantics does not** — `evalRom` has no `OP_10` arm. -/
theorem b251_op10_evalRom : evalRom 3 op10Subject op10Formula = none := by
  decide

/-- **And the generator declines it as non-ROM.**  So `evalN` success does not imply acceptance,
and `nockCompiles_of_rom`'s antecedent cannot be weakened to `evalN`. -/
theorem b251_op10_notROM :
    genComputeSkeleton (K := DK) 3 op10Subject op10Formula = .error .notROM :=
  Batch165.gen_op10_notROM (K := DK) 2 op10Subject _

/-- **Tier A's program is a terminating ROM program by the semantic condition**, so `evalRom` is
not the empty predicate.  Read off the generator's acceptance through `evalRom_of_gen_ok`, which
is the converse half of completeness. -/
theorem b251_rom_dot : evalRom 4 dotSubject dotFormula = some dotResult :=
  evalRom_of_gen_ok (K := DK) (genComputeSkeleton_dot 0)

/-- **`romTree` is the real tree, not a junk choice.**  `Classical.choose` lands on `dotTree`
because `genComputeSkeleton` is a function: both equations describe the same `.ok`.  This is the
equation that would transport Tier A's trace-level facts onto `nockCompiles_of_rom`'s premises. -/
theorem b251_romTree_dot : romTree (K := DK) b251_rom_dot = dotTree (K := DK) := by
  have h1 := romTree_spec (K := DK) b251_rom_dot
  have h2 := genComputeSkeleton_dot (K := DK) 0
  rw [h2] at h1
  exact (congrArg Prod.fst (Except.ok.inj h1)).symm

theorem b251_rom_evalN : Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  evalRom_evalN b251_rom_dot

end

end Nock.RedTeam.Batch251

#print axioms Nock.RedTeam.Batch251.b251_hcap
#print axioms Nock.RedTeam.Batch251.b251_hreqn
#print axioms Nock.RedTeam.Batch251.b251_hrespn
#print axioms Nock.RedTeam.Batch251.b251_nockCompiles
#print axioms Nock.RedTeam.Batch251.b251_claim_pins_result
#print axioms Nock.RedTeam.Batch251.b251_claim_not_vacuous
#print axioms Nock.RedTeam.Batch251.b251_op10_evalN
#print axioms Nock.RedTeam.Batch251.b251_op10_evalRom
#print axioms Nock.RedTeam.Batch251.b251_op10_notROM
#print axioms Nock.RedTeam.Batch251.b251_rom_dot
#print axioms Nock.RedTeam.Batch251.b251_romTree_dot
#print axioms Nock.RedTeam.Batch251.b251_rom_evalN
