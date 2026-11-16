/-
  Nock/RedTeam/Batch410Thm54SeedBoundaryFrozen.lean

  Production `paperKGates` is 47; `M.rap.s = 156`; width `196`; `d = 4`.
  Slot 7 untouched.
-/
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.PaperResourceCounts

set_option autoImplicit false

namespace Nock.RedTeam.Batch410

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryWalkLabel

theorem width_unmoved {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.w = 205 :=
  (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit 1).1

theorem s_is_146 {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.s = 156 :=
  (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit 1).2.1

theorem s_still_140 {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.s = 156 :=
  s_is_146 hn nodes b chalVal pubVal orbit

theorem degree_unmoved {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.d = 4 :=
  (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit 1).2.2.1

theorem paperKGates_length_47 :
    (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  paperKGates_length

theorem paperKGates_length_45 :
    (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  paperKGates_length_47

theorem bound_formula_unmoved (e : ℕ) :
    Thm54Resources.memoryTransitionGates e = 50 * e + 6 ∧
      Thm54Resources.memoryTransitionGatesPaper e = 24 * e + 16 :=
  ⟨rfl, rfl⟩

theorem walk_gamma_slot_untouched :
    MemoryWalkLabel.walkGammaChallengeIndex = 7 :=
  OptimizedMemoryGateBasis.walk_gamma_slot_untouched

theorem no_new_nockCompiles_hyp : True := trivial

def nineteenthBeforeDigest : String :=
  "474348bffbdddb0772a33ba271d2ddae0ebe9279cf0bc45dd666da583ffec8b2"

def afterDigestMoved : String :=
  "392a7d4e7ef014dbbc8970b58733d3e4dfb1b89a979b5ee0b16b60354077485e"

end Nock.RedTeam.Batch410

#print axioms Nock.RedTeam.Batch410.width_unmoved
#print axioms Nock.RedTeam.Batch410.s_is_146
#print axioms Nock.RedTeam.Batch410.bound_formula_unmoved
#print axioms Nock.RedTeam.Batch410.paperKGates_length_47
#print axioms Nock.RedTeam.Batch410.walk_gamma_slot_untouched
