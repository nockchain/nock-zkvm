/-
  Nock/V1J8/GenAtomBig.lean

  **Multi-limb hardening — a scope-waived diagnostic verdict.**

  Atoms of `≥ 3` limbs (`≥ 2^64`), a first difference deeper than axis 2 and a shared comb suffix are UNREACHABLE by
  any accepted run of feasible length: `AcceptsJ8V`'s static block requires every claim leaf `< p` (`hclA`, `hcen`),
  the only atom-making step is OP4, and from a leaf `< p` the first atom `≥ 2^64` is `2^32 − 1` increments past `p`
  (every big atom of a shorter run is a two-limb `[l, B − 1]`: the same top limb, so two of them differ at axis 2).
  `checkJ8W` is a test harness verdict, NOT the
  verifier: a `checkJ8W` ACCEPT says every chip, every public equation and every other static conjunct holds on the
  generated traces.
-/
import Nock.V1J8.GenAtom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)

/-- **The static block, conjunct by conjunct** (`checkStaticJ8`'s conjuncts in order; `hcen` split in two).  The flag
is `true` on the claim-scope conjuncts (`hclA`, `hcen`'s leaf bound) that `checkJ8W` waives. -/
def staticPartsJ8 (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) :
    List (String × Bool × Bool) :=
  [("injX", false, injB Pb.nodes), ("adjX", false, adjB Pb.nodes Pb.orbit.ω),
   ("injC", false, injB Pb.nodesC), ("adjC", false, adjB Pb.nodesC Pb.orbitC.ω), ("nC<p", false, decide (Pb.nC < p)),
   ("injW", false, injB Pb.nodesW), ("adjW", false, adjB Pb.nodesW Pb.orbitW.ω),
   ("kroots", false, decide (1 ≤ Pb.kroots) && decide (Pb.kroots ≤ Pb.nW) && decide (Pb.kroots + Pb.nW < p)),
   ("injA", false, injB Pb.nodesA), ("adjA", false, adjB Pb.nodesA Pb.orbitA.ω), ("nA<p", false, decide (Pb.nA < p)),
   ("hlay", false, decide (List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids)),
   ("hsmall", false,
     decide (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)),
   ("huniq", false, decide (((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup)),
   ("axPos", false, decide (∀ i ∈ Pb.regs, axPosB (Pb.Rt i) = true)), ("hnd", false, decide Pb.regs.Nodup),
   ("hidx", false, decide (∀ id ∈ Pb.regs, Pb.idx id < p)),
   ("hrk", false, decide (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0))),
   ("hlt", false, decide (∀ id ∈ Pb.regs, (Pb.rk id).1 < p ∧ (Pb.rk id).2 < p ∧ Pb.idx id < p)),
   ("hclA (claim leaves < p)", true, decide (∀ k : Fin 3, atomLtB p (claimNoun c k) = true)),
   ("hclI", false, decide (∀ k : Fin 3, isCellN (claimNoun c k) = true → (m k).1 < p)),
   ("hclR", false, decide (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p)),
   ("hcen (census leaves <= fuelChip)", false, decide (∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip)),
   ("hcen (census leaf values < p)", true, decide (∀ x ∈ censusG Pb c, ∀ v ∈ x.leafList, v < p)),
   ("public lengths", false, decide (3 + Pb.regs.length + 2 * Pb.nC < p) && decide (Pb.nA + Pb.nV < p)),
   ("hcellF", false, isCellN c.formula), ("nA<=2^62", false, decide (Pb.nA ≤ 2 ^ 62)),
   ("budgets", false, budB Pb r (g + r.N) &&
     decide (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW))]

/-- The static parts of an input (`[]` when it is not valid). -/
def staticParts (I : InJ8) : List (String × Bool × Bool) :=
  if hv : validB I = true then staticPartsJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g else []

/-- **The scope-waived verdict** (test harness, NOT the verifier): `checkJ8` with the claim-scope conjuncts waived. -/
def checkJ8W (I : InJ8) : Bool :=
  if hv : validB I = true then
    ((staticPartsJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g).all fun x => x.2.1 || x.2.2) &&
    checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && chipsB I
  else false

/-- The first atom-table row satisfying `p` (else `0`). -/
def firstRow (q : ChipIn) (p : (Fin q.n) → Bool) : ℕ :=
  (((List.finRange q.n).find? p).map (·.val)).getD 0

/-- Set column `c` of row `i` to `v`. -/
def setCol (q : ChipIn) (c i : ℕ) (v : ZMod P) : ChipIn :=
  ⟨q.h, q.n, q.ω, fun c' i' => if c' = c ∧ (i' : ℕ) = i then v else q.cols c' i'⟩

/-- **The multi-limb tampers** (each must be rejected), on the atom table's carry rows: a LINK row (`c_out = 1`,
`kR_o = 1`: the carry runs into the suffix row at `idx + 1`) and an OVERFLOW row (`c_out = 1`, `kR_o = 0`).  Only the
tampers whose row exists are emitted. -/
def mlTampersOf (I : InJ8) : List (String × InJ8) :=
  let A := I.A
  let isLink := fun (i : Fin A.n) => A.cols 199 i == 1 && A.cols 202 i == 1
  let isOvf := fun (i : Fin A.n) => A.cols 199 i == 1 && A.cols 202 i == 0
  let hasLink := (List.finRange A.n).any isLink
  let hasOvf := (List.finRange A.n).any isOvf
  let lR := firstRow A isLink
  let oR := firstRow A isOvf
  let ovfW := (List.finRange A.n).any fun i => isOvf i && A.cols 6 i == 1
  let oRW := firstRow A fun i => isOvf i && A.cols 6 i == 1
  (if hasLink then
    [(s!"link row {lR}: carry c_out cleared", { I with A := setCol A 199 lR 0 }),
     (s!"link row {lR}: kR_o cleared (link read as overflow)", { I with A := setCol A 202 lR 0 }),
     (s!"link row {lR}: suffix pointer idR + 1", { I with A := bumpCol A 4 lR }),
     (s!"link row {lR}: next row's old serial idx_o + 1", { I with A := bumpCol A 200 (lR + 1) }),
     (s!"link row {lR}: next row's inc flag cleared", { I with A := setCol A 197 (lR + 1) 0 })] else []) ++
  (if hasOvf then
    [(s!"overflow row {oR}: old top limb vR_o + 1", { I with A := bumpCol A 203 oR }),
     (s!"overflow row {oR}: carry c_out cleared", { I with A := setCol A 199 oR 0 })] else []) ++
  (if ovfW then
    [(s!"overflow row {oRW} (new limb): next row's aR + 1 (not the row [0 1])", { I with A := bumpCol A 8 (oRW + 1) }),
     (s!"overflow row {oRW} (new limb): idR + 1", { I with A := bumpCol A 4 oRW })] else [])

/-! ## Kernel facts (structural) -/

/-- A link successor is the suffix of a row `[0 X]`, and is in the list. -/
theorem linkSucc_some (L : List Noun) (n m : Noun) (h : linkSucc L n = some m) :
    n = .cell (.atom 0) m ∧ m ∈ L := by
  match n, h with
  | .cell (.atom 0) (.cell a b), h =>
    simp only [linkSucc] at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h

/-- The scope-waived verdict waives ONLY claim-scope conjuncts: every non-flagged static conjunct is required. -/
theorem checkJ8W_static (I : InJ8) (h : checkJ8W I = true) : ∀ x ∈ staticParts I, x.2.1 = false → x.2.2 = true := by
  intro x hx hf
  unfold checkJ8W at h
  unfold staticParts at hx
  split at h
  · rename_i hv
    rw [dif_pos hv] at hx
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.1 x hx
    simpa [hf] using this
  · cases h

end Nock.V1J8.Gen

#print axioms Nock.V1J8.Gen.linkSucc_some
#print axioms Nock.V1J8.Gen.checkJ8W_static
