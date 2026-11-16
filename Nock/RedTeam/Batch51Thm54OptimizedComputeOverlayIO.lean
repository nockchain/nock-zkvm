import Nock.RedTeam.Batch26Thm54FiniteFieldIO
import Nock.RedTeam.Batch50Thm54OptimizedComputeCodec
import Nock.NockVMROM.Thm54.OptimizedComputeIOObstruction

/-!
* `Nock/NockVMROM/Thm54/OptimizedComputeOverlay.lean`;
* `Nock/NockVMROM/Thm54/OptimizedComputeIOObstruction.lean`.

Paper frame:

* RAP field and degree-three carrier: the paper;
* symbolic IO accumulators and costs: the paper, proof the paper;
* walk values and costs: the paper;
* compute/memory CORE: the paper;
* consumed compute capstone: the paper.

The obstruction theorems are correct for a lossless encoding of the entire nested rational-function
field.  This artifact also pins their exact boundary: they do not prohibit encoding a finite set of
honest accumulator values, and they do not contradict the existing sampled `FiniteFieldIO` path.
That path is `K`-valued and is sound only outside its explicitly counted events.
-/

namespace Nock.RedTeam.Batch51

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeIOObstruction
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

/-! ## 1. Six-value overlay census and state-dependent sharing -/

variable {F K : Type*} [Field F] [Field K]

/-- The overlay is exactly a six-coordinate carrier. -/
def overlayEquivFinSix : OverlayValues K ≃ (Fin 6 → K) where
  toFun v
    | 0 => v.walkCount
    | 1 => v.walkAcc
    | 2 => v.sf1_st
    | 3 => v.sf2_st
    | 4 => v.sf3_st
    | 5 => v.ioAcc
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩
  left_inv v := by cases v; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

noncomputable instance overlayFintype [Fintype K] : Fintype (OverlayValues K) :=
  Fintype.ofEquiv (Fin 6 → K) overlayEquivFinSix.symm

theorem overlay_cardinality [Fintype K] :
    Fintype.card (OverlayValues K) = Fintype.card K ^ 6 := by
  rw [Fintype.card_congr overlayEquivFinSix, Fintype.card_fun, Fintype.card_fin]

/-- Every state uses two different physical fingerprint roles. -/
theorem every_state_has_exactly_two_distinct_roles :
    ∀ st : State, overlayRoleA st ≠ overlayRoleB st :=
  overlayRoles_ne

/-- The complete state-dependent role matrix, independently unfolded. -/
theorem overlay_role_matrix :
    (overlayRoleA .s0, overlayRoleB .s0) = (3, 4) ∧
    (overlayRoleA .s1, overlayRoleB .s1) = (2, 3) ∧
    (overlayRoleA .s2, overlayRoleB .s2) = (3, 4) ∧
    (overlayRoleA .s3, overlayRoleB .s3) = (6, 7) ∧
    (overlayRoleA .s4, overlayRoleB .s4) = (6, 7) ∧
    (overlayRoleA .s5, overlayRoleB .s5) = (9, 10) ∧
    (overlayRoleA .s6, overlayRoleB .s6) = (9, 10) ∧
    (overlayRoleA .s7, overlayRoleB .s7) = (9, 10) ∧
    (overlayRoleA .s8, overlayRoleB .s8) = (9, 10) ∧
    (overlayRoleA .s9, overlayRoleB .s9) = (9, 10) ∧
    (overlayRoleA .cons, overlayRoleB .cons) = (9, 10) := by
  decide

theorem non_overlay_fingerprint_unchanged
    (pub : Pub K) (dec : Dec K) (ex : Extra K) (v : OverlayValues K)
    (r : Fin 12) (c : Fin 3)
    (hA : r ≠ overlayRoleA pub.state) (hB : r ≠ overlayRoleB pub.state) :
    OptimizedComputeOverlay.encodeExtension pub dec ex v (.inl (r, c)) =
      OptimizedComputeCodec.encodeExtension pub dec ex (.inl (r, c)) := by
  simp [OptimizedComputeOverlay.encodeExtension, hA, hB]

/-- Reading the two overlaid fingerprints returns all six coordinates exactly. -/
theorem six_coordinates_roundtrip
    (pub : Pub K) (dec : Dec K) (ex : Extra K) (v : OverlayValues K) :
    decodeOverlay (F := F) (OptimizedComputeCodec.encodeBase pub.state)
      (OptimizedComputeOverlay.encodeExtension pub dec ex v) = v :=
  decodeOverlay_encode pub dec ex v

/-! ## 2. Exact accepted-row roundtrip and threading -/

noncomputable def overlay123456 : OverlayValues K73cubic :=
  ⟨1, 2, 3, 4, 5, 6⟩

noncomputable def overlayZero : OverlayValues K73cubic :=
  ⟨0, 0, 0, 0, 0, 0⟩

theorem op1_overlay_roundtrip :
    OptimizedComputeOverlay.decode (computeInputs honestSeed honestAlpha)
        (OptimizedComputeOverlay.encode (F := F73)
          (computePub honestSeed honestAlpha) (computeDec honestSeed)
          OptimizedComputeCodecConcrete.honestExtra overlay123456) =
      (OptimizedComputeOverlay.withOverlayTags
        { computePub honestSeed honestAlpha with
            sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } overlay123456,
        computeDec honestSeed,
        OptimizedComputeCodecConcrete.honestExtra, overlay123456) :=
  OptimizedComputeOverlay.decode_encode_of_vcomp compute_accepts

theorem op6_overlay_roundtrip :
    OptimizedComputeOverlay.decode (computeInputs honestSeed honestAlpha)
        (OptimizedComputeOverlay.encode (F := F73)
          Batch50.s6Pub Batch50.s6Dec Batch50.s6Extra overlay123456) =
      (OptimizedComputeOverlay.withOverlayTags
        { Batch50.s6Pub with sf1_st := none, sf2_st := none, sf3_st := none, certC? := none }
          overlay123456,
        Batch50.s6Dec, Batch50.s6Extra, overlay123456) :=
  OptimizedComputeOverlay.decode_encode_of_vcomp Batch50.s6_vcomp

/-- Equality of physical rows forces equality of all six live values while keeping the same
`Inputs`/`Pub`/`Dec`/`Extra` witness. -/
theorem same_witness_overlay_injective
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {ex : Extra K}
    (h : Vcomp inp pub dec) :
    Function.Injective
      (fun v : OverlayValues K => OptimizedComputeOverlay.encode (F := F) pub dec ex v) := by
  intro v₁ v₂ heq
  have hd := congrArg (OptimizedComputeOverlay.decode inp) heq
  rw [OptimizedComputeOverlay.decode_encode_of_vcomp h,
    OptimizedComputeOverlay.decode_encode_of_vcomp h] at hd
  exact congrArg (fun t => t.2.2.2) hd

theorem distinct_overlay_payloads_give_distinct_rows :
    OptimizedComputeOverlay.encode (F := F73)
        (computePub honestSeed honestAlpha) (computeDec honestSeed)
        OptimizedComputeCodecConcrete.honestExtra overlayZero ≠
      OptimizedComputeOverlay.encode (F := F73)
        (computePub honestSeed honestAlpha) (computeDec honestSeed)
        OptimizedComputeCodecConcrete.honestExtra overlay123456 := by
  apply (same_witness_overlay_injective (F := F73) compute_accepts).ne
  intro h
  have hc := congrArg OverlayValues.walkCount h
  norm_num [overlayZero, overlay123456] at hc

/-! ## 3. Malformed/conflicting boundary

At this layer there is intentionally no walk or finite-IO gate predicate.  Any six-value payload
round-trips when the underlying table row satisfies `Vcomp`.  Thus malformed walk recurrences or
IO accumulators are not rejected by this codec module; their rejection belongs to the future
folded gate basis. -/

theorem arbitrary_overlay_payload_roundtrips
    (v : OverlayValues K73cubic) :
    OptimizedComputeOverlay.decode (computeInputs honestSeed honestAlpha)
        (OptimizedComputeOverlay.encode (F := F73)
          (computePub honestSeed honestAlpha) (computeDec honestSeed)
          OptimizedComputeCodecConcrete.honestExtra v) =
      (OptimizedComputeOverlay.withOverlayTags
        { computePub honestSeed honestAlpha with
            sf1_st := none, sf2_st := none, sf3_st := none, certC? := none } v,
        computeDec honestSeed,
        OptimizedComputeCodecConcrete.honestExtra, v) :=
  OptimizedComputeOverlay.decode_encode_of_vcomp compute_accepts

/-- A physically overwritten role may differ from the restored table fingerprint and still
round-trip: restoration uses the active `Vcomp` equation, not an equality gate against the overlay
payload.  This is the exact current rejection boundary. -/
theorem zero_payload_overwrites_nonzero_op1_role :
    OptimizedComputeOverlay.encodeExtension
        (computePub honestSeed honestAlpha) (computeDec honestSeed)
        OptimizedComputeCodecConcrete.honestExtra overlayZero
        (.inl (overlayRoleA .s1, 0)) = 0 ∧
      OptimizedComputeCodec.encodeExtension
        (computePub honestSeed honestAlpha) (computeDec honestSeed)
        OptimizedComputeCodecConcrete.honestExtra
        (.inl (overlayRoleA .s1, 0)) = 1 := by
  constructor
  · rfl
  · norm_num [overlayRoleA, OptimizedComputeCodec.encodeExtension,
      OptimizedComputeCodec.pubFingerprint, computePub, computeDec, fp, resultNoun,
      honestSeed, GlobalCarryRecognizer.enc_atom, FP.atomFP, fpCoordinate]

/-! ## 4. Whole-field obstruction and finite honest-set counter-scope -/

/-- Over finite `K`, the stronger base-field formulation also holds: the entire nested
rational-function field cannot have a three-coordinate `K`-basis. -/
theorem no_degree_three_basis_IOField_over_finite_base
    (K : Type*) [Field K] [Finite K] :
    ¬ Nonempty (Module.Basis (Fin 3) K (IOField K)) := by
  rintro ⟨b⟩
  letI : Fintype K := Fintype.ofFinite K
  letI : Infinite (IOField K) :=
    Algebra.Transcendental.infinite (RatFunc K) (IOField K)
  letI : Finite (IOField K) := Finite.of_injective b.repr b.repr.injective
  exact not_finite (IOField K)

/-- The no-global-codec theorem does not prohibit a roundtrip on a singleton set of exact
accumulator values. -/
theorem singleton_exact_value_roundtrip (K : Type*) [Field K] (x : IOField K) :
    ∃ (encode : {y : IOField K // y = x} → K)
      (decode : K → {y : IOField K // y = x}),
      Function.LeftInverse decode encode := by
  refine ⟨fun _ => 0, fun _ => ⟨x, rfl⟩, ?_⟩
  intro y
  apply Subtype.ext
  exact y.property.symm

/-- The global obstruction and a real accepted sampled finite-field accumulator coexist over the
same finite field.  Hence the latter does not contradict the former. -/
theorem global_obstruction_and_sampled_honest_acceptance_coexist :
    (¬ ∃ (encode : IOField Batch26.F7 → Batch26.F7)
          (decode : Batch26.F7 → IOField Batch26.F7),
        Function.LeftInverse decode encode) ∧
      ∃ w : FiniteIO.PostChallengeIOWitness Batch26.honestRecords Batch26.honestCoins,
        FiniteIO.FiniteIOAccepts Batch26.honestRecords Batch26.honestCoins w :=
  ⟨no_scalar_roundtrip_IOField_to_finite Batch26.F7,
    Batch26.b26_honest_completeness⟩

/-- The concrete honest sampled accumulator is genuinely `K`-valued and nonconstant. -/
theorem sampled_honest_accumulator_values :
    Batch26.honestWitness.requestAcc (0 : Fin 2) = (0 : Batch26.F7) ∧
      Batch26.honestWitness.requestAcc (1 : Fin 2) = (2 : Batch26.F7) ∧
      Batch26.honestWitness.requestAcc (0 : Fin 2) ≠
        Batch26.honestWitness.requestAcc (1 : Fin 2) := by
  decide

/-- On the concrete honest record set, sampled finite-field acceptance is equivalent to existence
of the preserved exact symbolic accumulator system.  This is a finite-instance oracle agreement,
not a global injection of `IOField K` into `K`. -/
theorem sampled_honest_oracle_agreement :
    (∃ w : FiniteIO.PostChallengeIOWitness Batch26.honestRecords Batch26.honestCoins,
        FiniteIO.FiniteIOAccepts Batch26.honestRecords Batch26.honestCoins w)
      ↔ (∃ (mu : Fin Batch26.honestRecords.responses.length → ZMod 7)
             (accP accM : ℕ → RatFunc (RatFunc Batch26.F7))
             (requests responses out_mem : RatFunc (RatFunc Batch26.F7)),
            (∀ j, mu j ≠ 0)
            ∧ IO.ProgIOSat
                (fun i => SetEq.RLC (IO.listExt Batch26.honestRecords.requests i))
                accP requests Batch26.honestRecords.requests.length
            ∧ IO.MemIOSat
                (fun i => SetEq.RLC (IO.listExt Batch26.honestRecords.responses i))
                (IO.castμ mu) accM responses out_mem
                Batch26.honestRecords.responses.length
            ∧ requests = responses ∧ out_mem = 0) :=
  Batch26.b26_oracle_agreement

/-! ## 5. Consumed-scope guards -/

def strict_package_still_consumes_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.compTemplate F) P.compLanguage :=
  P.compSemanticTemplate

noncomputable def strict_capstone_is_still_conditional
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P :=
  strictNockVMROM_of_package P

theorem paper_alias_is_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end
end Nock.RedTeam.Batch51

#print axioms Nock.RedTeam.Batch51.overlay_cardinality
#print axioms Nock.RedTeam.Batch51.overlay_role_matrix
#print axioms Nock.RedTeam.Batch51.six_coordinates_roundtrip
#print axioms Nock.RedTeam.Batch51.op1_overlay_roundtrip
#print axioms Nock.RedTeam.Batch51.op6_overlay_roundtrip
#print axioms Nock.RedTeam.Batch51.same_witness_overlay_injective
#print axioms Nock.RedTeam.Batch51.arbitrary_overlay_payload_roundtrips
#print axioms Nock.RedTeam.Batch51.zero_payload_overwrites_nonzero_op1_role
#print axioms Nock.RedTeam.Batch51.no_degree_three_basis_IOField_over_finite_base
#print axioms Nock.RedTeam.Batch51.singleton_exact_value_roundtrip
#print axioms Nock.RedTeam.Batch51.global_obstruction_and_sampled_honest_acceptance_coexist
#print axioms Nock.RedTeam.Batch51.sampled_honest_accumulator_values
#print axioms Nock.RedTeam.Batch51.sampled_honest_oracle_agreement
#print axioms Nock.RedTeam.Batch51.strict_package_still_consumes_B29
#print axioms Nock.RedTeam.Batch51.strict_capstone_is_still_conditional
#print axioms Nock.RedTeam.Batch51.paper_alias_is_still_forest
