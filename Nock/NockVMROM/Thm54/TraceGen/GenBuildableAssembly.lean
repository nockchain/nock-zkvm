/-
  Nock/NockVMROM/Thm54/TraceGen/GenBuildableAssembly.lean

  **`BuildableNockExecution` at the generated carrier — `genBuildable`'s argument list, filled.**

  `genBuildable` (`GenExactExecution.lean:171`) has fourteen arguments beyond the carrier itself.
  This module supplies every one of them for any program `genComputeSkeleton` accepts:

  | argument | supplied by | landed |
  |---|---|---|
  | `hnodup` | `genExactExecution_requestNodup` | `GenRequestNodup.lean` |
  | `hbal` | `genBuildable_hbal` | `FF` |
  | `hqrc : q ≤ ringChar K` | `le_of_eq hchar` — `genSemanticData` already carries `hchar` | — |
  | `h2 : (2 : K) ≠ 0` | `htwo` — already `genSemanticData`'s | — |
  | `hq : 1 < q` | `hq : 11 < q` — already `genSemanticData`'s | — |
  | `hprog` | `genExactExecution_derivedRequestIO_length` + `hprogCap` | here |
  | `hresp` | `derivedResponseIO_length_le` + `hmemCap` | here |

  None of them
  is a property of the program that has to be proved, and none of them is a weakening of the
  conclusion:

  * `hKszChar : Ksz < ringChar K`.  This is `genBuildable`'s `hKsz` and is a **different** condition
    from `genSemanticData`'s `hKsz : accAt … ≤ Ksz` — one bounds `Ksz` above, the other below.
    `Batch221` exhibits one.
  * `hprogCap : accAt … + 1 ≤ 2 ^ orbit.h` — the request IO column, which
    `genExactExecution_derivedRequestIO_length` measures as exactly `accAt …`, must fit the orbit
    with one slot to spare.  `hcomp` bounds the *row* count, which does not bound the record count,
    so this is not implied.
  * `hmemCap : memRows + 1 ≤ 2 ^ orbit.h` — the same for the response column, and a strengthening
    by one of `genExactConfig`'s own `memRows_le`.  `derivedResponseIO_length_le` is what lets the
    condition be stated on the row count rather than on the record list.

  **Not claimed.**  M2 /
  Plonky3 remains out of scope; nothing here is executable.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenRequestNodup
import Nock.NockVMROM.Thm54.TraceGen.GenServedMemoryTrace
import Nock.NockVMROM.Thm54.TraceGen.GenBalance

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## The two IO capacity conditions, in program-measurable form -/

/-- **`genBuildable`'s `hprog` from the record count.**  The request IO column has exactly
`accAt (airReorder t) …` entries (`genExactExecution_derivedRequestIO_length`), so the capacity
condition is stated on a number the generator computes. -/
theorem genBuildable_hprog (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).derivedRequestIO.length + 1 ≤ 2 ^ orbit.h := by
  rw [genExactExecution_derivedRequestIO_length (F := F) z α chal Ksz orbit horb a b c t mf
    hmempos hcomp hmem]
  exact hprogCap

/-- **`genBuildable`'s `hresp` from the memory row count.**  `responseRecords` emits at most one
record per memory row (`derivedResponseIO_length_le`), so a one-slot strengthening of `memRows_le`
suffices. -/
theorem genBuildable_hresp
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest mf).length + 1 ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).derivedResponseIO.length + 1 ≤ 2 ^ orbit.h := by
  have hle := ExactExecution.derivedResponseIO_length_le
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem)
  have hrows : (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
      hmempos hcomp hmem).memoryRows.length = (bfsForest mf).length := by
    rw [ExactExecution.memoryRows_length]
    simp [genExactConfig]
  calc
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
        hmempos hcomp hmem).derivedResponseIO.length + 1
        ≤ (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf
            hmempos hcomp hmem).memoryRows.length + 1 := Nat.succ_le_succ hle
    _ = (bfsForest mf).length + 1 := by rw [hrows]
    _ ≤ 2 ^ orbit.h := hmemCap

/-! ## The assembly -/

section Assembly

variable [Fintype K] [DecidableEq K]

/-- **`BuildableNockExecution` for any program `genComputeSkeleton` accepts.**

The hypothesis list is `genServedMemoryTrace`'s plus the three capacity conditions the module
docstring names; every other `genBuildable` argument is discharged here. -/
noncomputable def genBuildableOfProgram {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    BuildableNockExecution F K :=
  genBuildable (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem q (by omega) Λ
    (genSemanticData (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hb hq hchar
      haxis hbad hout hfirst)
    (genServedMemoryTrace (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hfirst)
    (genExactExecution_requestNodup (F := F) z α chal Ksz orbit horb a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem (horb_of_window hB hwin))
    (genBuildable_hbal (F := F) chal Ksz orbit horb z α a b c (memInputs z)
      (genComputeRows z α t) t hmempos hcomp hmem)
    (le_of_eq hchar) htwo hKszChar
    (genBuildable_hprog (F := F) z α chal Ksz orbit horb a b c t
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem hprogCap)
    (genBuildable_hresp (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem hmemCap)


/-- **Later-seed zeros of the generated carrier**, from the
honest Form R read cancellation at every root (`genExactExecution_laterSeedZeros`).  This is the
retired `hmore` premise, now a theorem.  All arguments implicit: it is used against the expected
type. -/
theorem genBuildableOfProgram_laterSeedZeros {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K} :
    BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst) :=
  fun i _ hi => genExactExecution_laterSeedZeros (F := F) chal Ksz orbit horb z α a b c h hfirst
    hmempos hcomp hmem i hi

end Assembly

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildable_hprog
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildable_hresp
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram
