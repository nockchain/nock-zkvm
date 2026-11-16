/-
  Nock/NockVMROM/Thm54/MemoryHaltAtomDecode.lean

  The memory chip commits a round-0 `𝔽` column `atom`
  (`OptimizedMemoryGateBasis.atomCol = 180`) and the `halt`-row gate
  `sel_halt · (pt.noun.leaf − algebraMap atom) = 0` (`haltAtomMixed`).  On every trace accepted at
  `memoryChipAt c`, every decoded `halt` row's leaf is the lifted atom
  (`decodeMemPub_halt_leaf_eq_atom`), so the decoded `halt` noun is the atom the column holds
  (`decodeNoun_halt_eq_atom`; at `𝔽 = ZMod p` it is `Noun.atom atom.val`,
  `decodeNoun_halt_eq_atom_zmod`).  The decoder reads the column through `memoryAtomAt`;
  `decodeNoun`'s `halt` case never goes through `nounByFP`.
-/
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.P8Core.MemoryHaltAtomDecode
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.MemoryHaltAtomDecode

open scoped Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.MemoryWalkDeployed

noncomputable section

/-! ## The three compiled coordinate gates (shape lemmas) -/

section Shape

open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem haltAtomGateCoord_eq (b : Module.Basis (Fin 3) F K) (k : Fin 3) :
    haltAtomGateCoord b k =
      .mul (bcur 1) (.sub (.var .traceCur (12 + (k : ℕ)))
        (.mul (.const (coord b (1 : K) k)) (bcur 180))) := by
  simp only [haltAtomGateCoord, haltAtomMixed, haltSel, atomCol,
    MixedCoordinateCompiler.mixedCompile, memoryCol0]

/-- At a basis with `coord b 1 = (1, 0, 0)` (`OptimizedComputeFinalTrace.FormRBasis`, given for
the compiler basis by `compilerBasis_formR`) the three coordinate gates are exactly
`sel_halt·(leaf₀ − atom)`, `sel_halt·leaf₁`, `sel_halt·leaf₂` (up to the literal `0·atom`). -/
theorem haltAtomGateCoord_formR (b : Module.Basis (Fin 3) F K)
    (h0 : coord b (1 : K) 0 = 1) (h1 : coord b (1 : K) 1 = 0) (h2 : coord b (1 : K) 2 = 0)
    (env : Env F) :
    (haltAtomGateCoord b 0).eval env = env.trace 1 * (env.trace 12 - env.trace 180) ∧
      (haltAtomGateCoord b 1).eval env = env.trace 1 * env.trace 13 ∧
      (haltAtomGateCoord b 2).eval env = env.trace 1 * env.trace 14 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [haltAtomGateCoord_eq, CoeffExpr.eval, bcur, h0, h1, h2]

end Shape

/-! ## The decoded `halt` noun of a leaf that is a lifted atom -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `decodeNoun` on a `halt` node whose committed leaf is `algebraMap a` reads `a` (through
`leafAtomOf`), never `nounByFP`. -/
theorem decodeNoun_halt_of_leaf (q : ℕ) (data : DTmem K) (a : F)
    (hleaf : data.2.pt.noun.leaf = algebraMap F K a) :
    HostileSkeletonDecoding.decodeNoun q (.node (.halt, data) []) =
      Noun.atom (HostileSkeletonDecoding.leafAtomOf q (algebraMap F K a)) := by
  rw [HostileSkeletonDecoding.decodeNoun, hleaf]

end Generic

/-- At `𝔽 = ZMod p`, the `ℕ` preimage below `p` of `algebraMap a` is `a.val`. -/
theorem leafAtomOf_algebraMap_zmod {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Algebra (ZMod p) K] (a : ZMod p) :
    HostileSkeletonDecoding.leafAtomOf p (algebraMap (ZMod p) K a) = a.val := by
  classical
  have hcast : ∀ n : ℕ, (n : K) = algebraMap (ZMod p) K (n : ZMod p) := fun n => by
    simp
  have hex : ∃ k : ℕ, k < p ∧ (k : K) = algebraMap (ZMod p) K a :=
    ⟨a.val, ZMod.val_lt a, by rw [hcast, ZMod.natCast_zmod_val]⟩
  have hlt := HostileSkeletonDecoding.leafAtomOf_lt hex
  have hcst := HostileSkeletonDecoding.leafAtomOf_cast hex
  rw [hcast] at hcst
  have hinj := (algebraMap (ZMod p) K).injective hcst
  have hval := congrArg ZMod.val hinj
  rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval

theorem decodeNoun_halt_eq_atom_zmod {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Algebra (ZMod p) K] (data : DTmem K) (a : ZMod p)
    (hleaf : data.2.pt.noun.leaf = algebraMap (ZMod p) K a) :
    HostileSkeletonDecoding.decodeNoun p (.node (.halt, data) []) = Noun.atom a.val := by
  rw [decodeNoun_halt_of_leaf p data a hleaf, leafAtomOf_algebraMap_zmod]

/-! ## Accepted traces: the decoded `halt` leaf is the committed atom -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

variable (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

include hsat in
/-- **`decodeNoun_halt_eq_atom`** (generic `𝔽`): the decoded noun of an accepted `halt` row is
the atom its committed `atom` column holds, read through `leafAtomOf`. -/
theorem decodeNoun_halt_eq_atom (q : ℕ)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .halt) :
    HostileSkeletonDecoding.decodeNoun q (.node (lblMAt P (honestQm P c Qm) c i) []) =
      Noun.atom (HostileSkeletonDecoding.leafAtomOf q
        (algebraMap F K (memoryAtomAt P c (honestQm P c Qm) i))) := by
  have hleaf := decodeMemPub_halt_leaf_eq_atom P c Qm hsat i hst
  have hst' : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .halt := by
    simpa [decodeMemPub] using hst
  unfold lblMAt
  simp only [hst']
  exact decodeNoun_halt_of_leaf q _ _ hleaf

end

end Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
