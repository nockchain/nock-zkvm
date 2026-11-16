/-
  Nock/RedTeam/Batch844Thm54HpowHW.lean

  **`hpow` — DISCHARGED** (`hpow_of_family_acceptance`, `hpow_of_family_acceptance_two`).  `read_root` rows: `ver = 1` and
  `FamilyIOChain.ts_eq_alpha_pow_natLift_at`; `verify_child` rows: the `intermediate` partner's
  record (slot `7` is `ts`).

  `specializeA` keeps the row's `mem.axis`; `encodeRow` then
  re-encodes it.  That map is not
  idempotent on encoded values: `formRT_nockAxisOf_not_idempotent` (`𝔽₅`, `λ = 3`, `a = 8`:
  `T = 3³ = 2`, re-encoded `3¹ = 3 ≠ 2`).  The failing goal is `hW_forces_axis_fixed`'s
  conclusion at an active row; acceptance does not touch it (it is a property of the decode /
  re-encode pair, not of the gates).  No compiled accepted trace is exhibited: the identity's
  failure on a concrete accepted family trace is UNCONFIRMED here.  The a-bearing half
  (`Batch509.wrap_idA_lblM_of_topology`, `specializeA` only) holds; the repair is the parked H1
  `wrapJoin` or consuming the `specializeA` view.
-/
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.NockVMROM.Thm54.P8Core.Batch844Thm54HpowHW
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch844

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Reified

noncomputable section

/-! ## A. `hpow` -/

section Hpow

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)

include hacc hgood hio hrb hb1

/-- Every active family memory row's timestamp is `alphaM c.1 ^ n` for some `n`. -/
theorem active_ts_pow_at (r : Fin (memRows P))
    (hact : memoryMemRecKind (memoryStateOf (memEnvF P c Qm r)) = .active) :
    ∃ n : ℕ, (memEnvK P c Qm r).trace 26 = alphaM c.1 ^ n := by
  have hsat := hacc.memory_satisfies
  have hts : ∀ a : Fin (memRows P), (memEnvF P c Qm a).trace 2 = 1 →
      ∃ n : ℕ, (memEnvK P c Qm a).trace 26 = alphaM c.1 ^ n := by
    intro a ha
    exact ⟨_, ts_eq_alpha_pow_natLift_at P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) a
      (readSel_ver_at P c Qm hsat hb1 a ha)⟩
  rw [memoryStateOf_eq_memRowStateOf] at hact
  rcases hst : WalkTilingEvents.memRowStateOf (memEnvF P c Qm r) with _ | _ | _ | _ <;>
    rw [hst] at hact <;> simp [memoryMemRecKind] at hact
  · exact hts r (sel2_of_read hst)
  · have h3 := verify_sel_at P c Qm hsat r hst
    obtain ⟨a, ha2, hra⟩ := verify_partner_at P c Qc Qm hacc hgood hrb r h3
    obtain ⟨n, hn⟩ := hts a ha2
    refine ⟨n, ?_⟩
    have h7 := congrFun hra 7
    simp [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h7
    rw [h7, hn]

/-- **`hpow` from family acceptance**, at the trace `lblM` reads (`honestQm P c Qm`), under an
explicit `alphaM c.1 ≠ 0`. -/
theorem hpow_of_family_acceptance (hα0 : alphaM c.1 ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P (honestQm P c Qm) c i).1 = .active →
        MemPower (alphaM c.1) (lblM P (honestQm P c Qm) c i).2.2.mem.ts := by
  intro i h1 hi hact
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < P.optimized.family.problem.cfg.memRows := by omega
  have hl := lblM_succ P (honestQm P c Qm) c ⟨k, hk⟩
  simp only at hl
  rw [hl] at hact ⊢
  obtain ⟨n, hn⟩ := active_ts_pow_at P c Qc Qm hacc hgood hio hrb hb1 ⟨k, hk⟩ hact
  have hts : (lblMAt P (honestQm P c Qm) c ⟨k, hk⟩).2.2.mem.ts =
      (memEnvK P c Qm ⟨k, hk⟩).trace 26 := rfl
  rw [hts, hn]
  exact memPower_of_pow hα0 n

theorem hpow_of_family_acceptance_two (hD : 2 ≤ (hostileRequestsAt P c Qc).length) :
    ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P (honestQm P c Qm) c i).1 = .active →
        MemPower (alphaM c.1) (lblM P (honestQm P c Qm) c i).2.2.mem.ts :=
  hpow_of_family_acceptance P c Qc Qm hacc hgood hio hrb hb1
    (alpha_ne_zero_of_not_collision (timestamp_good_at P c Qc Qm hgood) hD)

end Hpow

/-! ## B. `hW`: the compiled obstruction -/

section HW

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- On an active row, the encoded `axis` of `(wrapMemoryLabel α row).specialize α λ` is
`formRT λ (nockAxisOf row.mem.axis)`: `specializeA` keeps the axis, `encodeRow` re-encodes it. -/
theorem specialize_wrap_axis (α lmb : K) (row : MState × DTmem K)
    (hact : memoryMemRecKind row.1 = .active) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem.axis =
      formRT lmb (nockAxisOf row.2.2.mem.axis) := by
  simp [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow, MemoryRowTemplate.specializeA,
    wrapMemoryLabel, specializeMemRec, hact, NockVM.formRRow]

/-- **The obstruction.**  `WrapMemoryIdentity` forces every active `lblM` row's decoded `axis`
slot to be a fixed point of `formRT λ ∘ nockAxisOf`. -/
theorem hW_forces_axis_fixed (hW : Batch509.WrapMemoryIdentity P c Qm₀) (i : ℕ)
    (hact : memoryMemRecKind (lblM P Qm₀ c i).1 = .active) :
    (lblM P Qm₀ c i).2.2.mem.axis =
      formRT c.2.2.2.lambda (nockAxisOf (lblM P Qm₀ c i).2.2.mem.axis) := by
  have h := congrArg (fun r : MState × DTmem K => r.2.2.mem.axis) (hW i)
  rw [specialize_wrap_axis _ _ _ hact] at h
  exact h.symm

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **`formRT λ ∘ nockAxisOf` is not idempotent on encoded values** (`𝔽₅`, `λ = 3`, `a = 8 = 2³`):
`T = formRT 3 8 = 3³ = 2`, and `formRT 3 (nockAxisOf 2) = 3¹ = 3 ≠ 2`. -/
theorem formRT_nockAxisOf_not_idempotent :
    formRT (3 : ZMod 5) (nockAxisOf (formRT (3 : ZMod 5) 8)) ≠ formRT (3 : ZMod 5) 8 := by
  have hs8 : formRCertShift 8 = 3 := by
    unfold formRCertShift
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.size_pow]
  have hs2 : formRCertShift 2 = 1 := by
    unfold formRCertShift
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, Nat.size_pow]
  have hT : formRT (3 : ZMod 5) 8 = ((2 : ℕ) : ZMod 5) := by
    rw [formRT, hs8]; decide
  have hchar : ringChar (ZMod 5) = 5 := ZMod.ringChar_zmod_n 5
  have hax : nockAxisOf (((2 : ℕ) : ZMod 5)) = 2 := nockAxisOf_natCast (by rw [hchar]; norm_num)
  rw [hT, hax, formRT, hs2]
  decide

end HW

end

end Nock.RedTeam.Batch844

#print axioms Nock.RedTeam.Batch844.hpow_of_family_acceptance
#print axioms Nock.RedTeam.Batch844.hpow_of_family_acceptance_two
#print axioms Nock.RedTeam.Batch844.hW_forces_axis_fixed
#print axioms Nock.RedTeam.Batch844.formRT_nockAxisOf_not_idempotent
