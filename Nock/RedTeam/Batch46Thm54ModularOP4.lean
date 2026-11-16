import Nock.NockVMROM.Thm54.StrictPackage

/-!
The semantic source is finite-field
OP4 and the appendix makes the operation explicit as
`+(n) = (1+n) mod p`.  The downstream OP4 row is transcribed at
the paper, and the consumed capstone is the paper.

The checks below compile:

* a concrete `ZMod 5` OP4 row whose child result is the top residue `4`, whose table
  `FP.inc`, noun target `incMod`, `lusFBy`, and complete `Vcomp` row semantics all wrap to atom `0`;
* rejection of a cell operand by the `Vcomp` size gate, despite the deliberately total fallback in
  `incMod`;
* rejection of modulus `4` at the operational-premise and strict-package types for `ZMod 5`;
* derivation of bounded Nat-cast injectivity from the package's characteristic pin.

No strict-package inhabitant is claimed.  The concrete non-vacuity witness is instead at the
strongest feasible production row theorem, `OpcodeSemantics.s4_vcomp_semantics`, with every one of
its substantive premises instantiated.
-/

namespace Nock.RedTeam.Batch46

open Nock Nock.Noun
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OpcodeSemantics
open Nock.NockVMROM.Thm54.StrictPackage

noncomputable section

local instance prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

abbrev K5 := ZMod 5

def subject : Noun := .atom 0
def top : Noun := .atom 4
def wrapped : Noun := .atom 0
def childFormula : Noun := .cell (.atom 1) top
def parentFormula : Noun := .cell (.atom 4) childFormula
def seed : K5 := 2

noncomputable def fp (n : Noun) : FP K5 :=
  GlobalCarryRecognizer.enc seed n

def inp : Inputs K5 where
  α := 1
  z := seed
  a := 1
  b := 1
  c := 1

noncomputable def dec : Dec K5 where
  f_h := fp (.atom 4)
  f_t := fp childFormula
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

noncomputable def pub : Pub K5 where
  state := .s4
  s := fp subject
  f := fp parentFormula
  e := fp wrapped
  sf1_s := fp subject
  sf1_f := fp childFormula
  sf1_e := fp top
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 0
  ln := 0
  mr1 := ⟨fp parentFormula, fp childFormula, 3, 0⟩
  mr2 := MemRec.zero
  mr3 := MemRec.zero

theorem seed_ne : seed ≠ 0 := by decide

theorem ringChar_K5 : ringChar K5 = 5 :=
  ringChar.eq K5 5

theorem top_stack_agrees :
    incMod 5 top = wrapped ∧
      FieldEmbedding.lusFBy 5 top = some wrapped ∧
      FP.inc seed (fp top) = fp wrapped ∧
      evalPaperMod 5 2 subject parentFormula = some wrapped ∧
      FieldEmbedding.evalFBy 5 2 subject parentFormula = some wrapped := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  simpa [fp, top, wrapped, incMod] using
    (fp_inc_enc_atom_eq_incMod (K := K5) (q := 5) seed 4)

theorem top_legacy_diverges :
    ¬ IncrementNoOverflow 5 top ∧
      incNoWrap top = .atom 5 ∧
      Noun.lus top = some (.atom 5) ∧
      Nock.evalN 2 subject parentFormula = some (.atom 5) ∧
      evalPaperMod 5 2 subject parentFormula = some wrapped := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  change ¬ (4 + 1 < 5)
  omega

theorem top_fp_bridge :
    FP.inc seed (GlobalCarryRecognizer.enc seed top) =
      GlobalCarryRecognizer.enc seed (incMod 5 top) :=
  fp_inc_enc_atom_eq_incMod seed 4

theorem vcomp_top_residue : Vcomp inp pub dec := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seed_ne (.atom 4) childFormula
  · simp only [SVhead]
    rw [if_neg (by decide)]
    norm_num [headAtom, pub, dec, inp, fp,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · simp [memBlk, pub, inp]
  · simp [evalV, pub, inp, dec, sfz2, sfz3, fp, top, wrapped,
      GlobalCarryRecognizer.enc_atom]
    simpa [GlobalCarryRecognizer.enc_atom, incMod] using
      (fp_inc_enc_atom_eq_incMod (K := K5) (q := 5) seed 4).symm

noncomputable def root :
    RootRealization inp pub dec where
  subject := subject
  formula := parentFormula
  result := wrapped
  head := .atom 4
  tail := childFormula
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

noncomputable def call :
    CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e where
  subject := subject
  formula := childFormula
  result := top
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

theorem pairFaithful_refl (n : Noun) (hb : FieldEmbedding.BoundedBy 5 n) :
    PairFaithful seed 5 n n where
  separates := by simp [GlobalCarryRecognizer.SepSeed]
  left_bounded := hb
  right_bounded := hb

theorem top_sizeWindow : SizeWindow seed top := by
  have ho : orderOf seed = 4 := by
    rw [orderOf_eq_iff (by norm_num [seed])]
    refine ⟨by decide, ?_⟩
    intro m hm hlt
    interval_cases m <;> decide
  exact ⟨by rw [ho]; omega, by rw [ho]; norm_num [top, Noun.leaves]⟩

theorem castInj_K5 :
    Set.InjOn (fun k : ℕ => (k : K5)) (Set.Iio 5) :=
  StrictRawReconstruction.charCast_injOn 5

theorem top_row_semantics :
    Verb.StepROM
        (Verb.program subject parentFormula)
        (.node .minus (.leaf 4)
          (.node .star (Verb.ofNoun subject) (Verb.ofNoun childFormula))) ∧
      FieldEmbedding.evalFBy 5 2 subject parentFormula = some wrapped := by
  have hhead := pairFaithful_refl (.atom 4) (by norm_num)
  have hformula := pairFaithful_refl parentFormula (by norm_num [parentFormula, childFormula, top])
  have h1s := pairFaithful_refl subject (by norm_num [subject])
  have h1f := pairFaithful_refl childFormula (by norm_num [childFormula, top])
  have hresult : PairFaithful seed 5 wrapped (incMod (ringChar K5) top) := by
    simpa [ringChar_K5, incMod, wrapped, top] using
      pairFaithful_refl wrapped (by norm_num [wrapped])
  simpa [root, call, inp, pub, dec] using
    (s4_vcomp_semantics
      (K := K5) (q := 5) (fuel := 1)
      (hstate := rfl) (hz := seed_ne) (hq := ringChar_K5.symm)
      (hcast := castInj_K5) (row := root) (call1 := call)
      (hhead := hhead) (hformula := hformula) (h1s := h1s) (h1f := h1f)
      (hresult := hresult) (hsize := top_sizeWindow)
      (hcall := by rfl) (hv := vcomp_top_residue))

/-! ## Cell-fallback attack -/

theorem total_fallback_does_not_make_cells_executable (a b : Noun) :
    incMod 5 (.cell a b) = wrapped ∧
      FieldEmbedding.lusFBy 5 (.cell a b) = none := by
  simp [incMod, wrapped, FieldEmbedding.lusFBy]

theorem s4_vcomp_size_gate_rejects_cell
    {K : Type*} [Field K]
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s4)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hsize : SizeWindow inp.z call1.result)
    {a b : Noun} (hcell : call1.result = .cell a b)
    (hv : Vcomp inp pub dec) : False := by
  have heval := hv.2.2.2.2
  simp only [evalV, hstate] at heval
  have hfpSize : pub.sf1_e.size = inp.z := heval.2.2.1
  have hencSize :
      (GlobalCarryRecognizer.enc inp.z call1.result).size = inp.z := by
    have hreal := call1.result_realizes
    change pub.sf1_e = GlobalCarryRecognizer.enc inp.z call1.result at hreal
    rw [← hreal]
    exact hfpSize
  obtain ⟨n, hn⟩ := atom_of_enc_size_eq hsize hencSize
  rw [hcell] at hn
  cases hn

/-! ## Wrong-modulus/type-transport attacks -/

theorem four_ne_ringChar_K5 : (4 : ℕ) ≠ ringChar K5 := by
  rw [ringChar_K5]
  omega

theorem operational_premises_reject_wrong_modulus
    {z : K5} {s : SemanticStrategy.ComputeRowSkeleton}
    (h : BoundSemanticTrace.SkeletonOperationalPremises (K := K5) 4 z s) : False :=
  four_ne_ringChar_K5 h.q_eq_ringChar

local instance char_ring_K5 : CharP K5 (ringChar K5) := ringChar.charP K5

theorem strict_package_rejects_wrong_modulus
    {hOrb Λ : ℕ}
    (P : StrictNockVMROMPackage K5 K5 hOrb 4 Λ) : False :=
  four_ne_ringChar_K5 P.q_eq_ringChar

theorem strict_package_cast_is_derived
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q) :=
  StrictNockVMROMPackage.castInj P

/-! ## Census target and collision-control attacks -/

theorem s4_census_uses_characteristic_incMod
    {K : Type*} [Field K] (s : SemanticStrategy.ComputeRowSkeleton)
    (hs : s.state = .s4) :
    P8Census.skeletonUse .producedResult s.evaluation
        (incMod (ringChar K) (P8Census.skeletonSubformula s 0 .result)) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, hs]

theorem top_wrap_ne_legacy_target :
    incMod (ringChar K5) top = wrapped ∧
      incNoWrap top = .atom 5 ∧
      incMod (ringChar K5) top ≠ incNoWrap top := by
  simp [ringChar_K5, incMod, incNoWrap, top, wrapped]

theorem top_wrap_ne_atom_characteristic :
    incMod (ringChar K5) top = wrapped ∧
      (.atom (ringChar K5) : Noun) ≠ wrapped := by
  simp [ringChar_K5, incMod, top, wrapped]


#print axioms Nock.RedTeam.Batch46.top_stack_agrees
#print axioms Nock.RedTeam.Batch46.top_legacy_diverges
#print axioms Nock.RedTeam.Batch46.top_fp_bridge
#print axioms Nock.RedTeam.Batch46.vcomp_top_residue
#print axioms Nock.RedTeam.Batch46.top_row_semantics
#print axioms Nock.RedTeam.Batch46.s4_vcomp_size_gate_rejects_cell
#print axioms Nock.RedTeam.Batch46.operational_premises_reject_wrong_modulus
#print axioms Nock.RedTeam.Batch46.strict_package_rejects_wrong_modulus
#print axioms Nock.RedTeam.Batch46.strict_package_cast_is_derived
#print axioms Nock.RedTeam.Batch46.s4_census_uses_characteristic_incMod
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.lusFBy_atom_eq_incMod
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.fp_inc_enc_atom_eq_incMod
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.op4_top_residue_regression
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s4_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.P8Census.skeletonComparisons
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.LocalOpcodeCertificate.s4
#print axioms Nock.NockVMROM.Thm54.BoundSemanticTrace.buildCoveredRow
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalLocalCertificate_s4
#print axioms Nock.NockVMROM.Thm54.GlobalOpcodeScheduling.canonicalRow_evalFBy
#print axioms
  Nock.NockVMROM.Thm54.ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.castInj
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.q_eq_ringChar
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.containment
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package

end

end Nock.RedTeam.Batch46
