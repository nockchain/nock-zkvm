/-
  NockvmE2E/Exec/J8ShapeB.lean   (the Mathlib-free Bool half of the J-8 shape check)

  `j8ShapeOk : ExecInst -> Bool` -- total, Mathlib-free (imports only Verify).  It also adds the executable checks for the instance hypotheses of
  `HdagU.hdagU_of_tie`: `chipReadsLtB` (twin of `DagSem.chipReadsLt`), `hpreC`, `hS`, `hle`, `hcolB`, `hpubB`, `hnpub`, `hkind`.
  The soundness lemmas (`*_of_shape`) live in J8Shape.lean.  NOT wired into the verifier exe.
-/
import NockvmE2E.Exec.Verify

set_option autoImplicit false

namespace NockvmE2E.Exec.J8Shape
open NockvmE2E.Exec.V NockvmE2E.Exec.VF

/-! ## the check -/

/-- a DAG expression never reaches the `.chal 63` fallback of `verifierChip` -/
def exNo63 : Tr.Ex → Bool
  | .chal i => i != 63
  | .add a b | .sub a b | .mul a b => exNo63 a && exNo63 b
  | .neg a | .pow a _ => exNo63 a
  | _ => true

/-- Bool twin of `DagSem.exReadsLt` (Mathlib-free): every column / public / challenge a DAG expression reads is in range -/
def exReadsLtB (w npub nch bc : Nat) : Tr.Ex → Bool
  | .var 0 i | .var 1 i => decide (i < w)
  | .var _ i => decide (i < npub)
  | .extVar 0 e | .extVar 1 e => decide (bc + 3 * e + 2 < w)
  | .extVar _ e => decide (3 * e + 2 < npub)
  | .chal i => decide (i < nch)
  | .add a b | .sub a b | .mul a b => exReadsLtB w npub nch bc a && exReadsLtB w npub nch bc b
  | .neg a | .pow a _ => exReadsLtB w npub nch bc a
  | _ => true

def chipReadsLtB (ch : Tr.Chip) (w npub nch : Nat) : Bool :=
  ch.shared.all (exReadsLtB w npub nch ch.baseCols) && ch.cons.all (fun c => exReadsLtB w npub nch ch.baseCols c.e)

def chipNo63 (c : Tr.Chip) : Bool := c.shared.all exNo63 && c.cons.all (fun k => exNo63 k.e)

/-- the public point the prover writes -/
def pptJ8 : VF.K3 := ⟨11, 5, 2⟩

/-- column kinds and Merkle blocks as `FlatProver` writes them: preprocessed columns (kind 1) in block 0, trace columns (kind 0) in their round's block 0/1/2, public columns (kind 2) in block 2,
quotient columns in block 3 -/
def layoutShapeOk (XI : ExecInst) : Bool :=
  XI.colKind.size == XI.nc && XI.blockOf.size == XI.nc + XI.nq &&
  (List.range XI.nc).all (fun c =>
    if XI.colKind[c]! == 2 then XI.blockOf[c]! == 2
    else if XI.colKind[c]! == 1 then XI.blockOf[c]! == 0
    -- kind 0 (trace) columns sit in their commit round `colRound` ∈ {0,1,2}: round-2 aux/LogUp columns are in block 2 (FlatProver.lean:289-291; finding)
    else XI.colKind[c]! == 0 && XI.blockOf[c]! ≤ 2) &&
  (List.range XI.nq).all (fun j => XI.blockOf[XI.nc + j]! == 3)

/-- local indices of the preprocessed (kind 1) columns of a chip id (`FlatProver.preIdxOf` now calls it) -/
def preIdxJ8 (id : String) : Array Nat :=
  if id == "computeChipVCLHX" then #[17, 18]
  else if id == "cellChipHQKW" || id == "atomChipHQL" then #[0, 1]
  else if id == "walkChipJ8" || id == "walkChipHQK" then #[0, 1, 2]
  else if id == "jetChipJ8" then Array.range 18
  else #[]

def distinctB : List String → Bool
  | [] => true
  | a :: l => !l.contains a && distinctB l

/-- the chip ids of the tables are pairwise distinct, among the six J-8 chips, and the four mandatory ones all occur -/
def mandatoryOk (XI : ExecInst) : Bool :=
  let ids := XI.tabs.toList.map (·.chip.id)
  distinctB ids && ids.all (fun i => ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"].contains i) &&
  ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL"].all ids.contains

/-- exactly the columns `preIdxJ8` names are preprocessed (kind 1) among the non-public columns of each table -/
def preKindOk (XI : ExecInst) : Bool :=
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c =>
    (XI.colKind[t.col0 + c]! == 1) == (preIdxJ8 t.chip.id).contains c)

/-- the trace-domain generator has EXACT order `3·2^(k+1)` (J-8's `StrictOrbitDomain … 3 h` with `h = k+1`):
`g^(3·2^(k+1)) = 1`, and `g^(2^(k+1)) ≠ 1`, `g^(3·2^k) ≠ 1` (the two maximal proper divisors `n/3`, `n/2`). -/
def orbitOk (XI : ExecInst) : Bool :=
  VF.pow XI.hGen (3 * 2 ^ (XI.k + 1)) == 1 && VF.pow XI.hGen (2 ^ (XI.k + 1)) != 1 && VF.pow XI.hGen (3 * 2 ^ XI.k) != 1

/-- the non-public width of each J-8 chip (123/242/166/71/349/166 for compute/cell/walkJ8/jet/atomHQL/walkHQK) -/
def wJ8 (id : String) : Nat :=
  if id == "computeChipVCLHX" then 123
  else if id == "cellChipHQKW" then 242
  else if id == "walkChipJ8" then 166
  else if id == "jetChipJ8" then 71
  else if id == "atomChipHQL" then 349
  else if id == "walkChipHQK" then 166
  else 0

def widthOk (XI : ExecInst) : Bool := XI.tabs.all (fun t => t.nc - t.npub == wJ8 t.chip.id)

/-- the coin-slot permutation the prover writes (round-0 coins `{2,3,8..18}` then round-1 `{0,1,4..7}`, in frame order) -/
def slotOfJ8 : Array Nat := #[13, 14, 0, 1, 15, 16, 17, 18, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def slotOfOk (XI : ExecInst) : Bool := XI.slotOf == slotOfJ8 && XI.nCoins == #[13, 6]

/-- **the J-8 shape of an instance** -/
def j8ShapeOk (XI : ExecInst) : Bool :=
  paramsOk XI && tabsOk XI &&
  XI.r == 2 && XI.d == 1 && XI.l == 170 && XI.hShift == 1 && XI.hN == 2 ^ (XI.k + 1) && XI.nD == XI.k + 7 &&
  XI.pubMode == 0 && XI.derived.isEmpty && XI.nCoins.size == 2 && XI.nCoins[0]! + XI.nCoins[1]! == 19 &&
  XI.ppt == pptJ8 && XI.nq % 3 == 0 && layoutShapeOk XI &&
  XI.pre.size == XI.nc && XI.pre.all (fun a => decide (a.size ≤ XI.hN + 1)) &&
  XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) &&
  -- the instance hypotheses of `hdagU_of_tie`
  XI.tabs.all (fun t => chipReadsLtB t.chip (t.nc - t.npub) t.npub 19) &&
  XI.pre.all (·.all fun x => VF.based x.toNat) && VF.based XI.hShift.toNat &&
  XI.tabs.all (fun t => decide (t.hN ≤ XI.hN)) &&
  XI.tabs.all (fun t => decide (t.col0 + t.nc ≤ XI.nc)) &&
  XI.tabs.all (fun t => decide (t.pubBase + t.npub ≤ XI.pubOf.size)) &&
  XI.tabs.all (fun t => decide (t.npub ≤ t.nc)) &&
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c => XI.colKind[t.col0 + c]! == 0 || XI.colKind[t.col0 + c]! == 1) &&
  mandatoryOk XI && preKindOk XI &&
  -- 
  orbitOk XI && widthOk XI && slotOfOk XI

end NockvmE2E.Exec.J8Shape
