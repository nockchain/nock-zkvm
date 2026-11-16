import Nock.Framework
import Nock.NockVMROM.Language
import Nock.NockVMROM.Separation
import Nock.NockVMROM.OneHot
import Nock.NockVMROM.CanonicalRAP
import Nock.NockVMROM.Completeness
import Nock.NockVMROM.TwoRAP
import Nock.NockVMROM.Soundness
import Nock.NockVMROM.Cost
import Nock.NockVMROM.Traversal
import Nock.NockVMROM.Thm54.ExactCanonicalRAP
import Nock.NockVMROM.Thm54.ExactOneHot
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.JointVerification
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ExactCost

/-!
# Theorem 5.4 — the NockVMROM Tier-2 structural bundle (S1–S8)

`nock_verifiableVMCompilation` assembles the eight already-proven component instances into the
Layer-1 conjunction `Nock.Framework.VerifiableVMCompilation` on the NockVMROM tag.  S1–S8 are
proposition/proof parameters of the resulting type:

* S1 `nock_uniqueMES`               — `UniqueMemoryExecutionSeparable` (Separation.lean, no `hcorrect`)
* S3 `exactChainedOneHot`           — all five execution-indexed `Def:one-hot` conditions
                                       (`Thm54/ExactOneHot.lean`)
* S4 `exactDefTraversable`          — complete accepted public compute/memory languages bijective
                                       with their exact-arity RVT products, including inverse laws
                                       (`Thm54/ExactTraversal.lean`)
* S5 `exactTwoRAPVerification`      — one joint assignment exposes all six segmented +IO families,
                                       shared derived IO, and public endpoint agreement
                                       (`Thm54/JointVerification.lean`)
* S6 `exactChainedHasPerfectCompleteness` — all six accepting segmented +IO families and shared IO
                                       on one exact configuration/execution
                                       (`Thm54/JointVerification.lean`)
* S7 `exactProductionFixedFieldSoundness` — universal production fixed-field soundness for the
                                       exact false-acceptance event and five-class workload
                                       (`Thm54/ProductionP8Containment.lean`)
* S8 `exactSegmentedCostVerification` — literal six-AIR exact segmented cost certificate
                                       (`Thm54/ExactCost.lean`)

## Additional type parameters of the bundle

* `[Fintype K] [DecidableEq K]` are added to the bundle because the S7 walk-soundness component
  counts a bad-challenge set inside a *finite* field `K`; these instances are not part of the bare
  `Tag` key.
* `[NeZero Ksz]` is retained for the explicit top-level language witness: the NockVMROM language is
  empty at `Ksz = 0` (`Language.not_language_Ksz_zero`).
* `[Algebra F K]` is added because the hardened S2 and S6 propositions derive their RAP families
  from one exact base/extension-field configuration.  S6 is the segmented `102/44`, `1-1*` +IO
  scope; the final monolithic `199/196` `RAP_NockComp-IO`/`RAP_NockMem-IO` identity is not
  part of this bundle.

The
S4 `V_comp`/`V_mem` ↔ `RVT` recognition is carried in both directions: the sound inclusion
`L_RVT ⊆ L_comp/L_mem` (`recognizes_compute`/`recognizes_memory`, `Fcomp`/`Fmem` embedding
`Vcomp`/`Vmem`) and a walk-structured `F`-row reconstruction to `L_RVT` (`recognized_complete_compute`/
`recognized_complete_memory`, discharged by `nockvmrom_compute_complete`/`nockvmrom_memory_complete`
via the inverse-BFS `Walk.reconForest`).  The class has no `ComputeLang`/`MemoryLang`/`φ_comp`/`φ_mem`
fields, so S4 rests on no free-field `Equiv.refl`; the bridge to the paper's full
bijection is not closed here.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework

/-- **NockVMROM bundle non-vacuity.**  At positive `Ksz`, the exact top-level language has the
    empty-table statement with one self-matched zero NMR record (`Language.language_nonempty`). -/
theorem nock_languageInhabited (F K : Type) [Field F] [Field K]
    (α β : K) (Ksz : ℕ) [NeZero Ksz] :
    LanguageInhabited (Tag F K α β Ksz) := by
  refine ⟨⟨⟨[], []⟩, ?_⟩⟩
  exact language_nonempty F K α β (Nat.pos_of_ne_zero (NeZero.ne Ksz))
    (0, ((0, 0, 0), (0, 0, 0)), 0)

/-- **`nock_verifiableVMCompilation`.**  Every S1–S8 clause is
    supplied by its genuine component instance.  The S1–S4 objects, exact universal S6 claim,
    top-level language witness, exact S5/S7 claims, and the S8 certificate are explicit type parameters,
    so the instance type itself pins them. -/
noncomputable instance nock_verifiableVMCompilation (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] (α β : K) (Ksz : ℕ) [NeZero Ksz] :
    VerifiableVMCompilation (Tag F K α β Ksz) (nmrMEF F K) K 10 3
      (Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness F K)
      (Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness F K)
      (Thm54.ExactSegmentedCostVerification F K)
      (Thm54.exactSegmentedCostVerification F K)
      (Thm54.ExactChainedHasPerfectCompleteness F K)
      (Thm54.exactChainedHasPerfectCompleteness F K)
      (Thm54.ExactTwoRAPVerification F K)
      (Thm54.exactTwoRAPVerification F K)
      (nock_uniqueMES F K α β Ksz)
      (Thm54.ExactChainedHasCanonicalRAP2 F K)
      (Thm54.exactChainedHasCanonicalRAP2 F K)
      (Thm54.ExactChainedOneHot F K)
      (Thm54.exactChainedOneHot F K)
      (Thm54.ExactDefTraversable F K)
      (Thm54.exactDefTraversable F K)
      (nock_languageInhabited F K α β Ksz) :=
  ⟨⟩

/-- **The structural bundle S1–S8 as a theorem.**  Since S1–S4 and S6
    are explicit proposition/proof parameters, `VerifiableVMCompilation` is a proposition and this
    capstone's type pins the genuine Nock structural objects. -/
theorem NockVMROM_Thm54_structural (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] (α β : K) (Ksz : ℕ) [NeZero Ksz] :
    VerifiableVMCompilation (Tag F K α β Ksz) (nmrMEF F K) K 10 3
      (Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness F K)
      (Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness F K)
      (Thm54.ExactSegmentedCostVerification F K)
      (Thm54.exactSegmentedCostVerification F K)
      (Thm54.ExactChainedHasPerfectCompleteness F K)
      (Thm54.exactChainedHasPerfectCompleteness F K)
      (Thm54.ExactTwoRAPVerification F K)
      (Thm54.exactTwoRAPVerification F K)
      (nock_uniqueMES F K α β Ksz)
      (Thm54.ExactChainedHasCanonicalRAP2 F K)
      (Thm54.exactChainedHasCanonicalRAP2 F K)
      (Thm54.ExactChainedOneHot F K)
      (Thm54.exactChainedOneHot F K)
      (Thm54.ExactDefTraversable F K)
      (Thm54.exactDefTraversable F K)
      (nock_languageInhabited F K α β Ksz) :=
  inferInstance

#print axioms NockVMROM_Thm54_structural

/-! ## Per-clause named wrappers (each S-clause independently named) -/

section GateC
variable (F K : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  (α β : K) (Ksz : ℕ) [NeZero Ksz]

/-- S1 — unique memory-execution separability. -/
noncomputable def nockvmrom_uniqueMES : UniqueMemoryExecutionSeparable (Tag F K α β Ksz) (nmrMEF F K) :=
  nock_uniqueMES F K α β Ksz
/-- S2 — canonical RAP arithmetization. -/
theorem nockvmrom_canonicalRAP : Thm54.ExactChainedHasCanonicalRAP2 F K :=
  Thm54.exactChainedHasCanonicalRAP2 F K
/-- S3 — all five exact opcode/memory one-hot clauses, with ten numeric opcodes and arity three. -/
theorem nockvmrom_oneHot : Thm54.ExactChainedOneHot F K :=
  Thm54.exactChainedOneHot F K
/-- S4 — exact public accepted-language bijections with the arity-3/2 RVT products. -/
theorem nockvmrom_traversable : Thm54.ExactDefTraversable F K :=
  Thm54.exactDefTraversable F K
/-- Bundle hygiene — the exact NockVMROM language is inhabited. -/
theorem nockvmrom_languageInhabited : LanguageInhabited (Tag F K α β Ksz) :=
  nock_languageInhabited F K α β Ksz
@[reducible] noncomputable def nockvmrom_traversable_complete_compute :=
  (nock_isTraversable F K α β Ksz).recognized_complete_compute
@[reducible] noncomputable def nockvmrom_traversable_complete_memory :=
  (nock_isTraversable F K α β Ksz).recognized_complete_memory
/-- S5 — exact same-assignment two-RAP verification for the segmented `102/44`, `e = 1` family. -/
theorem nockvmrom_twoRAP : Thm54.ExactTwoRAPVerification F K :=
  Thm54.exactTwoRAPVerification F K
noncomputable def nockvmrom_twoRAP_legacy :
    HasTwoRAPVerification (Tag F K α β Ksz) (nmrMEF F K) K (nockTwoRAPModel F K α β Ksz) :=
  nock_hasTwoRAPVerification F K α β (Nat.pos_of_ne_zero (NeZero.ne Ksz))
/-- S6 — exact same-execution combined completeness for all six segmented +IO families and shared
IO. -/
theorem nockvmrom_complete : Thm54.ExactChainedHasPerfectCompleteness F K :=
  Thm54.exactChainedHasPerfectCompleteness F K
/-- Compute-only completeness: the completeness model for the compute table alone.  It is not
consumed by `VerifiableVMCompilation` or either capstone. -/
noncomputable def nockvmrom_computeOnly_complete_legacy :
    HasPerfectCompleteness (Tag F K α β Ksz) (nmrMEF F K) K
      (nockCompletenessModel F K α β Ksz) :=
  nock_hasPerfectCompleteness F K α β Ksz
/-- S7 — universal Nock-production fixed-field soundness for the exact false-acceptance event and
canonical five-class workload. -/
theorem nockvmrom_sound :
    Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness F K :=
  Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness F K
/-- Walk-only soundness: it omits the production false-acceptance event, NPR/IO
collision, and canonical five-class workload, so it is not consumed by either capstone. -/
noncomputable def nockvmrom_walkOnly_sound_legacy :
    HasConcreteSoundness (Tag F K α β Ksz) (nockConcreteSoundness F K α β Ksz) :=
  nock_hasConcreteSoundness F K α β Ksz
/-- S8 — exact literal six-AIR segmented cost verification at `102/44`, `e = 1`. -/
theorem nockvmrom_cost : Thm54.ExactSegmentedCostVerification F K :=
  Thm54.exactSegmentedCostVerification F K
noncomputable def nockvmrom_cost_legacy :
    HasCostModel (Tag F K α β Ksz) reifiedNockCost :=
  nock_hasCostModel F K α β Ksz
end GateC

/-! ## Corrected cost results (companion to the structural bundle)

`nockVMROM_Thm54_corrected` collects the corrected efficiency/cost results as a self-contained
`Prop` (kept separate from the `Type`-valued structural bundle to avoid the bundle's free universe
metavariables): (5a) the reified max constraint degree is `4` on both chips (the paper's
"degree ≤ 4"); and (5b) the machine-checked **paper-cost mismatch** (the paper's
equal-`20·e+13` degree-4 claim refuted, `1 < 13`; absolute columns disagree `94 ≠ 184`).  The
structural S1–S8 conjunction is `NockVMROM_Thm54_structural`; the asymptotic-S7 negligibility
(`1-1*`) is a separately-named companion.  The separation records that the
paper's asymptotic/absolute-cost wording is not proved literally. -/
theorem nockVMROM_Thm54_corrected :
    (reifiedNockCost.compMaxDegree = 4 ∧ reifiedNockCost.memMaxDegree = 4) ∧
      (paperNockCost.compDeg4 = paperNockCost.memDeg4
        ∧ reifiedNockCost.memDeg4 < reifiedNockCost.compDeg4
        ∧ reifiedNockCost.compCols ≠ paperNockCost.compCols) :=
  ⟨⟨rfl, rfl⟩, paper_NockVMROM_cost_mismatch⟩

#print axioms nockVMROM_Thm54_corrected

end Nock.NockVMROM
