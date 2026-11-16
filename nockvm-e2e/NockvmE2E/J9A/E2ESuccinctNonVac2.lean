/-
the conclusion-binder witnesses and the bad-event witness.

* `Jm_T_pos`: `0 < IG.Jm.T` for every `InstG` over an instance with a table (`Jm.T = R.T' = XI.tabs.size`); `toy9R_Jm_T_pos` at `XI170 toy9R`.
* `nonempty_M0`, `nonempty_Mfin`: `Nonempty` of the DEEP statement's `M0` and of the DEEP plan's `Mfin` (`friPlan` is `deepPlan`), from `Nonempty` of the base
  `R0`; `R0J` has `M0 = Mfin = Unit` (`J8/Statement.lean:58`), so both hold at every interface and in particular at toy9R.
* `bad_event_toy`: the false-claim twin carried from `toy9_witness_false` to the datum of `nock_e2e_J9A_succinct`: there is a datum `d` with `d.c = cToyF` and
  `¬HoldsN d.c`, and the link gate accepts `cToyF` at `toy9RF` (so the bad event `verifyOnline' ∧ ¬HoldsN c` ranges over a non-empty claim).
  Modulo `hsh : shapeOkF famJ9A (XI170 toy9RF) = true` (the executed gate, as in `toy9_witness_false`).
-/
import NockvmE2E.J9A.E2ESuccinctNonVac
import NockvmE2E.J9A.RunGate9
import NockvmE2E.J9A.E2EJ9AToyR

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9A.E2ESuccinctNonVac2
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.E2EGen NockvmE2E.J8
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Toy9R
open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep
open NockvmE2E.Exec.J9AChips NockvmE2E.Exec.SideInst NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.E2EJ9AToyR

/-- `0 < Jm.T` for every instance bundle over an instance with a table -/
theorem Jm_T_pos {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)
    (h : 0 < XI.tabs.size) : 0 < IG.Jm.T := by
  have h1 : IG.Jm.T = XI.tabs.size := IG.hT
  omega

theorem toy9R_tabs_pos : 0 < (XI170 toy9R).tabs.size := by
  have := NockvmE2E.J9A.E2ESuccinctNonVac.toy9R_dims.2.2
  omega

/-- `0 < Jm.T` at the loaded instance `XI170 toy9R`, for any bundle (in particular `InstG.ofJ9A (XI170 toy9R) ..`) -/
theorem toy9R_Jm_T_pos {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} (IG : InstG F J (XI170 toy9R)) :
    0 < IG.Jm.T := Jm_T_pos IG toy9R_tabs_pos

section Nonempty
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ} [Fintype ι]
  (P : DeepParams Φ K ι β colRound) {r : ℕ} (A : AirShape P r) (R0 : RapStatement Φ K ι β colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ K → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ K → Prop)

/-- `Nonempty M0` of the DEEP statement -/
theorem nonempty_M0 [h : Nonempty R0.M0] : Nonempty (P.statement R0 Rest).M0 := h

/-- `Nonempty Mfin` of the DEEP plan (`friPlan` is `deepPlan` with a strengthened `RestV`) -/
theorem nonempty_Mfin [h : Nonempty R0.Mfin] : Nonempty (deepPlan P A R0 Rest RestV).Mfin :=
  ⟨(Classical.choice h, fun _ => 0, fun _ => 0)⟩

end Nonempty

open Toy9R Abs9R in
/-- the bad event of the headline is inhabited at the datum level (modulo the executed `hsh`) -/
theorem bad_event_toy (hsh : shapeOkF famJ9A (XI170 toy9RF) = true) :
    ∃ (d : Datum9A) (_ : DatumOK9A d), d.c = cToyF ∧ ¬ Nock.Jet.HoldsN d.c := by
  obtain ⟨⟨d, hdk, L, -, -, -, -, -, -, -, -, -, -, hc, -⟩, -, -, hn⟩ := NockvmE2E.J9A.E2EJ9AToyR.toy9_witness_false hsh
  exact ⟨d, hdk, hc, by rw [hc]; exact hn⟩

open Toy9R in
/-- and the link gate accepts the false claim at its own instance (so it is a claim the runtime gate lets through to `verifyOnline'`) -/
theorem bad_event_gate_toyF : NockvmE2E.J9A.RunGate9.linkGate9 (XI170 toy9RF) cToyF = true :=
  NockvmE2E.J9A.RunGate9.gate_toyF

open NockvmE2E.J9A.E2ESuccinctNonVac NockvmE2E.J9A.E2ESuccinctNum NockvmE2E.Merkle.SideMerkle NockvmE2E.Exec.J9AChips in
set_option maxHeartbeats 2000000 in
/-- **`nock_e2e_J9A_toy_numbers`**: the numbers theorem at the loaded instance `toy9R`, with `m = mSX` (`mSX + 1 <= 2^12`, `mSX_toy`) and the side-VK budget
`T = 2 * (total - 1)` (the value forced by `hTb` of `nock_e2e_J9A_succinct`, so `hTb` holds by `le_rfl`), whose `T <= 2^40` is discharged (`vk_total_toy`).
`hsh` is the executed `shapeOkF` gate (decide not run: OOM).  Composes with `nock_e2e_J9A_succinct` at `XI0 = toy9R` through `sideNums_toy`. -/
theorem nock_e2e_J9A_toy_numbers [SampleableType KC] (hsh : shapeOkF famJ9A (XI170 toy9R) = true) (P : ℝ≥0∞)
    (Q_FSf Q_Hf Vf Pf : ℕ) (hQFS : Q_FSf ≤ 2 ^ 64) (hQH : Q_Hf ≤ 2 ^ 64) (hV : Vf ≤ 2 ^ 32)
    (h : P ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ +
      (bfriErr (ω := smoothDomain (XI170 toy9R).nD (hn32_of_shapeF hsh)) (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) 1 (XI170 toy9R).l
          (31 / 64 : ℝ) (31 / 64 : ℝ≥0)
          ((mSX (XI170 toy9R) * ((2 ^ (XI170 toy9R).nD : ℝ≥0) / Fintype.card KC) : ℝ≥0)) Q_FSf +
        (MerkleTreeMultiExtractability.multiCheckpointROMErrorNumerator (((XI170 toy9R).k * (Q_FSf + 1)) * Pf) ((XI170 toy9R).k * (Q_FSf + 1)) Vf Q_Hf :
            ℝ≥0∞) * (Nat.card E2E.DgJ8 : ℝ≥0∞)⁻¹ +
        (((Q_Hf : ℝ≥0∞) + Vf + ((2 * ((NockvmE2E.Exec.VKBind.vkSp (XI170 toy9R)).total - 1) : ℕ) : ℝ≥0∞)) ^ 2 : ℝ≥0∞) / (2 * (Nat.card E2E.DgJ8 : ℝ≥0∞)))) :
    P ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ + ((2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 120 : ℝ≥0∞)⁻¹) :=
  nock_e2e_J9A_numbers (XI170 toy9R) hsh P (mSX (XI170 toy9R)) mSX_toy Q_FSf Q_Hf Vf Pf _ hQFS hQH hV vk_total_toy h

end NockvmE2E.J9A.E2ESuccinctNonVac2

#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.nock_e2e_J9A_toy_numbers
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.Jm_T_pos
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.toy9R_Jm_T_pos
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.nonempty_M0
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.nonempty_Mfin
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.bad_event_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac2.bad_event_gate_toyF
