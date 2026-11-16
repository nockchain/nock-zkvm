/-
  Nock/NockVMROM/Thm54/ComputeWalkSeed.lean

  **The verifier-computed compute walk seed: scaffold and honest identity.**

  Paper: with `rvt_root = (t_root, l_root)`, `l_root ∈ LT_comp`, the walk
  is seeded by `seed = α · RLC^γ(rvt_root)` and `initial_count = α`, and it suffices to check
  `out_walk = 0`.  `LT_comp = state × ((subject, formula), evaluation)` (`:1690`), so the seed is a
  function of the PUBLIC claim `(subject, formula, result)` and the verifier's coins alone: the
  root's state is the head opcode of the public formula (`:1743`: a cell head is `cons`).

  This module provides the verifier's seed (`seedOfClaim`) over the deployed ten-coordinate label
  (`ComputeTable.labelVecOfPub`), and proves that the honest family's prover-committed seed
  (`PlusIOSegmentedFamily.computeWalkSeed = curCol · α`) equals it **whenever the root row's
  `LT_comp` label is the claim's**: `s`, `f`, `e` are the claim's fingerprints — which
  `BindsAt.root_bindings` supplies for every honest package — and the root row's STATE is
  `rootStateOfFormula claim.formula`.

  No field of
  `OptimizedFullStrictNockVMROMPackage` / `OptimizedStrictNockVMROMPackage` supplies the root
  state binding: `BindComputeRow` binds `row.state = skeletonRow.state`, but nothing relates the
  skeleton root's `state` to its `formula`'s head (`SemanticStrategy.ComputeRowSkeleton` carries
  both as independent data).  Wiring `seedOfClaim` into the deployed publics (slots `3..5`) would
  therefore leave the honest identity `computeChipAt_honest_of_chalVal` unprovable for the
  generic package until that fact is added at every builder (`TraceGen/Gen.lean`'s
  `genComputeSkeleton` classifies the root by `formulaOpcode`; the fixtures by `rfl`).  Nothing here is wired into a RAP.
-/
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54
namespace ComputeWalkSeed

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Opcode `op` as a compute state. -/
def stateOfOpcode : ℕ → State
  | 0 => .s0
  | 1 => .s1
  | 2 => .s2
  | 3 => .s3
  | 4 => .s4
  | 5 => .s5
  | 6 => .s6
  | 7 => .s7
  | 8 => .s8
  | 9 => .s9
  | _ => .cons

/-- The root row's state as the verifier computes it from the public formula (the paper:
`type(formula_head) = cell ⇒ state = cons`; an atom head `op` is `OP_op`). -/
def rootStateOfFormula : Noun → State
  | .cell (.atom op) _ => stateOfOpcode op
  | _ => .cons

/-- The paper's `rvt_root ∈ LT_comp` as the deployed ten-coordinate
label vector: the root state tag, then `enc z` of subject, formula, result. -/
noncomputable def claimLabelVec (z : K) (claim : P8PublicClaim) : Fin 10 → K
  | 0 => stateTagField (rootStateOfFormula claim.formula)
  | 1 => (GlobalCarryRecognizer.enc z claim.subject).size
  | 2 => (GlobalCarryRecognizer.enc z claim.subject).dyck
  | 3 => (GlobalCarryRecognizer.enc z claim.subject).leaf
  | 4 => (GlobalCarryRecognizer.enc z claim.formula).size
  | 5 => (GlobalCarryRecognizer.enc z claim.formula).dyck
  | 6 => (GlobalCarryRecognizer.enc z claim.formula).leaf
  | 7 => (GlobalCarryRecognizer.enc z claim.result).size
  | 8 => (GlobalCarryRecognizer.enc z claim.result).dyck
  | 9 => (GlobalCarryRecognizer.enc z claim.result).leaf

/-- **The verifier's walk seed** `α · RLC^γ(rvt_root)` at a sampled tuple:
`α = alphaC`, `γ = gamma` (compute slot `10`), the fingerprints at `z = nprSeed`. -/
noncomputable def seedOfClaim [Fintype K] [Fintype F] (claim : P8PublicClaim)
    (c : OptimizedProductionChallengeTuple K F) : K :=
  Walk.rlc (gamma c.1) (claimLabelVec (nprSeed c.1) claim) * alphaC c.1

/-- A row whose `LT_comp` label is the claim's has the claim's label vector. -/
theorem labelVecOfPub_eq_claimLabelVec (pub : Pub K) (z : K) (claim : P8PublicClaim)
    (hst : pub.state = rootStateOfFormula claim.formula)
    (hs : pub.s = GlobalCarryRecognizer.enc z claim.subject)
    (hf : pub.f = GlobalCarryRecognizer.enc z claim.formula)
    (he : pub.e = GlobalCarryRecognizer.enc z claim.result) :
    labelVecOfPub pub = claimLabelVec z claim := by
  funext k
  fin_cases k <;> simp [labelVecOfPub, claimLabelVec, hst, hs, hf, he]

/-- **The honest seed is the verifier's seed** at every tuple carrying the family's `(αc, γ)`,
given the root row's `LT_comp` label is the claim's. -/
theorem computeWalkSeed_eq_seedOfClaim [Fintype K] [DecidableEq K] [Fintype F]
    (R : PlusIOSegmentedFamily F K)
    (hEnc : ∀ t, R.computeNodeVal t =
      Walk.rlc R.walkGamma (labelVecOfPub t.label.2.2.1))
    (claim : P8PublicClaim) (c : OptimizedProductionChallengeTuple K F)
    (hγ : gamma c.1 = R.walkGamma) (hα : alphaC c.1 = R.computeWalkAlpha)
    (hst : (R.problem.exec.computePubAt ⟨0, R.problem.cfg.compRows_pos⟩).state =
      rootStateOfFormula claim.formula)
    (hs : (R.problem.exec.computePubAt ⟨0, R.problem.cfg.compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed c.1) claim.subject)
    (hf : (R.problem.exec.computePubAt ⟨0, R.problem.cfg.compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed c.1) claim.formula)
    (he : (R.problem.exec.computePubAt ⟨0, R.problem.cfg.compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed c.1) claim.result) :
    R.computeWalkSeed = seedOfClaim claim c := by
  unfold PlusIOSegmentedFamily.computeWalkSeed seedOfClaim
  have h := OptimizedComputeSameExecution.curCol_eq_rlc_label (R := R) hEnc
    ⟨0, R.problem.cfg.compRows_pos⟩
  simp only [Fin.val_mk, Nat.zero_add] at h
  rw [h, hγ, hα, labelVecOfPub_eq_claimLabelVec _ _ claim hst hs hf he]

/-- The verifier's seed reads exactly the claim and the coins `(z, αc, γ)`: two tuples agreeing
there give the same seed.  (Constant walk: no trace value enters.) -/
theorem seedOfClaim_congr [Fintype K] [Fintype F] (claim : P8PublicClaim)
    (c c' : OptimizedProductionChallengeTuple K F)
    (hz : nprSeed c.1 = nprSeed c'.1) (hγ : gamma c.1 = gamma c'.1)
    (hα : alphaC c.1 = alphaC c'.1) :
    seedOfClaim claim c = seedOfClaim claim c' := by
  simp [seedOfClaim, hz, hγ, hα]

/-- A different public claim with a different formula head gives a different label vector at
coordinate `0` whenever the two heads' tags differ — the state coordinate of the seed is what a
prover cannot renegotiate through `s`/`f`/`e` alone. -/
theorem claimLabelVec_state_coord (z : K) (claim : P8PublicClaim) :
    claimLabelVec z claim 0 = stateTagField (rootStateOfFormula claim.formula) := rfl

theorem stateOfOpcode_toNat {st : ComputeTable.State} (hne : st ≠ .cons) :
    stateOfOpcode st.toNat = st := by
  cases st <;> first | contradiction | rfl

theorem rootStateOfFormula_cell_atom_eq (op : ℕ) (tl : Noun) :
    rootStateOfFormula (.cell (.atom op) tl) = stateOfOpcode op :=
  rfl

/-- `Vcomp.SVhead` plus a realized formula cell and fingerprint
    injectivity on the leaf window (`PairFaithful`) determine the row state from the
    public formula's head.  No package field. -/
theorem pub_state_eq_rootStateOfFormula
    {q : ℕ} {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    (row : OpcodeSemantics.RootRealization inp pub dec)
    (hv : ComputeTable.Vcomp inp pub dec)
    (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith_formula :
      OpcodeSemantics.PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (hfaith_atom : pub.state ≠ .cons →
      OpcodeSemantics.PairFaithful inp.z q row.head (.atom pub.state.toNat)) :
    pub.state = rootStateOfFormula row.formula := by
  have hcell :=
    OpcodeSemantics.root_formula_eq_cell hz hcast row hfaith_formula hv
  rw [hcell]
  by_cases hcons : pub.state = .cons
  · have ⟨left, right, hhead⟩ :=
      OpcodeSemantics.cons_head_is_cell hcons row.head row.head_realizes (hv.2.2.1)
    rw [hcons, hhead]
    rfl
  · have hsv : ComputeTable.SVhead inp pub dec := hv.2.2.1
    have hhead :=
      OpcodeSemantics.numeric_head_eq rfl hcons row.head row.head_realizes rfl hsv
        hcast (hfaith_atom hcons)
    rw [hhead, rootStateOfFormula_cell_atom_eq, stateOfOpcode_toNat hcons]

end ComputeWalkSeed
end Nock.NockVMROM.Thm54
