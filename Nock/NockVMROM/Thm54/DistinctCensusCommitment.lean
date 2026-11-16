import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.NockVMROM.Thm54.SemanticIntermediatePreimage

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The honest commitment of the distinct-pair `OP_5` execution

`HonestCommitment.Data` is the honest prover's seed-free commitment
(`Com(·)`, the paper; walk-table `Com(...)`).  The supplied execution is
`distinctCensusExecution`: three compute rows (an `OP_5` parent and two `OP_1` children) whose
`equalityOperand` census entry compares the genuinely distinct nouns `[7 9]` and `[8 10]`, and one
twenty-one-row serviced memory root that carries the four committed NMR records
(`Def:NMR`).

The comparison census still reads only the compute tree (`census_ignores_memoryForest`).  The
compute skeletons here differ from `op5Row` / `op1RowOf` only in the four real memory records, which
`skeletonComparisons` at `OP_5`/`OP_1` does not consult, so the
twenty-four pairs and the one distinct entry survive unchanged.

`1712` is the `OP_5` proof paragraph and is correct; the `OP_1` block is
Algorithm `NockCompute` lines `1754-1756` (`state = OP_1`, `evaluation = formula_tail`, all three
children `perp`), and `1708` is where the proof records that `OP_1` is in direct correspondence with
Table `tab:V_comp_equality`. -/

namespace Nock.NockVMROM.Thm54.DistinctCensusCommitment

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97c : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97c : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-! ## A. The committed NMR records (`Def:NMR`) -/

def recFSkel : MemRecSkeleton where
  root := op5Formula
  child := op5Tail
  axis := 3

def recTSkel : MemRecSkeleton where
  root := op5Tail
  child := leftFormula
  axis := 2

def recLSkel : MemRecSkeleton where
  root := leftFormula
  child := operandLeft
  axis := 3

def recRSkel : MemRecSkeleton where
  root := rightFormula
  child := operandRight
  axis := 3

/-! ## B. The three committed compute-row skeletons -/

/-- The `OP_5` parent, now carrying its two real formula/tail openings. -/
def op5SkelD : ComputeRowSkeleton :=
  { op5Row with
    memoryRecord := fun i _ => if (i : ℕ) = 0 then recFSkel else recTSkel }

def op1LSkelD : ComputeRowSkeleton :=
  { op1RowOf leftFormula operandLeft with memoryRecord := fun _ _ => recLSkel }

def op1RSkelD : ComputeRowSkeleton :=
  { op1RowOf rightFormula operandRight with memoryRecord := fun _ _ => recRSkel }

/-! ## C. The committed Nat timestamp exponents -/

def op5Stamp : ComputeTimestampRow where
  state := .s5
  lnPrevExponent := 0
  lnExponent := 2
  recordExponent := fun i => if (i : ℕ) = 0 then 1 else 2

def op1LStamp : ComputeTimestampRow where
  state := .s1
  lnPrevExponent := 2
  lnExponent := 3
  recordExponent := fun _ => 3

def op1RStamp : ComputeTimestampRow where
  state := .s1
  lnPrevExponent := 3
  lnExponent := 4
  recordExponent := fun _ => 4

def memStamp (st : MState) (e : ℕ) : MemoryTimestampRow where
  state := st
  recordExponent := e

/-! ## D. Honest-seed bindings of the three compute rows -/

theorem bind_op5 :
    BindComputeRow seedD op5SkelD op5RowD := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        op5SkelD, op5Row, op5RowD, op5Dec, encD, op5Head]
  · intro i
    fin_cases i
    · rw [dif_pos (by simp [op5SkelD, op5Row, ComputeTable.fanoutComp])]
      intro slot
      cases slot <;> rfl
    · rw [dif_pos (by simp [op5SkelD, op5Row, ComputeTable.fanoutComp])]
      intro slot
      cases slot <;> rfl
    · rw [dif_neg (by simp [op5SkelD, op5Row, ComputeTable.fanoutComp])]
      rfl
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [op5SkelD, op5Row, recFSkel, op5RowD, op5PubD, recF,
        computeMemRec]⟩
    · exact ⟨rfl, rfl, by norm_num [op5SkelD, op5Row, recTSkel, op5RowD, op5PubD, recT,
        computeMemRec]⟩
    · rfl

theorem bind_op1L :
    BindComputeRow seedD op1LSkelD op1LRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        op1LSkelD, op1RowOf, op1LRow, op1DecOf, encD, op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp op1LSkelD.state) := by
      simp [op1LSkelD, op1RowOf, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, op1LRow, op1LPub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [op1LSkelD, op1RowOf, recLSkel, op1LRow, op1LPub, op1PubOf,
        recL, computeMemRec]⟩
    · rfl
    · rfl

theorem bind_op1R :
    BindComputeRow seedD op1RSkelD op1RRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        op1RSkelD, op1RowOf, op1RRow, op1DecOf, encD, op1Head]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp op1RSkelD.state) := by
      simp [op1RSkelD, op1RowOf, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, op1RRow, op1RPub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [op1RSkelD, op1RowOf, recRSkel, op1RRow, op1RPub, op1PubOf,
        recR, computeMemRec]⟩
    · rfl
    · rfl

theorem stamp_op5 :
    ComputeTimestampSpecializesAt cfgD.challenges.α op5Stamp op5RowD := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show op5PubD.ln_prev = cfgD.challenges.α ^ 0
    rw [pow_zero]; rfl
  · show op5PubD.ln = cfgD.challenges.α ^ 2
    rfl
  · intro i
    fin_cases i
    · show op5PubD.mr1.ts = _
      rw [if_pos (by rfl)]
      show recF.ts = cfgD.challenges.α ^ 1
      rw [pow_one]; rfl
    · show op5PubD.mr2.ts = _
      rw [if_pos (by rfl)]; rfl
    · show op5PubD.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [op5Stamp, computeMemRecKind, Nock.Framework.recordCount])
    · exact absurd hi
        (by simp [op5Stamp, computeMemRecKind, Nock.Framework.recordCount])
    · rfl

theorem stamp_op1L :
    ComputeTimestampSpecializesAt cfgD.challenges.α op1LStamp op1LRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show op1LPub.ln_prev = cfgD.challenges.α ^ 2
    rfl
  · show op1LPub.ln = cfgD.challenges.α ^ 3
    rfl
  · intro i
    fin_cases i
    · show op1LPub.mr1.ts = _
      rw [if_pos (by rfl)]; rfl
    · show op1LPub.mr2.ts = _
      rw [if_neg (by decide)]; rfl
    · show op1LPub.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [op1LStamp, computeMemRecKind, Nock.Framework.recordCount])
    · rfl
    · rfl

theorem stamp_op1R :
    ComputeTimestampSpecializesAt cfgD.challenges.α op1RStamp op1RRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show op1RPub.ln_prev = cfgD.challenges.α ^ 3
    rfl
  · show op1RPub.ln = cfgD.challenges.α ^ 4
    rfl
  · intro i
    fin_cases i
    · show op1RPub.mr1.ts = _
      rw [if_pos (by rfl)]; rfl
    · show op1RPub.mr2.ts = _
      rw [if_neg (by decide)]; rfl
    · show op1RPub.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [op1RStamp, computeMemRecKind, Nock.Framework.recordCount])
    · rfl
    · rfl

/-! ## E. Generic memory-row skeletons and their bindings -/

def haltSkel (k : ℕ) : MemoryRowSkeleton where
  state := .halt
  parent := .atom k
  haltAtom := fun _ => k
  haltParent := by intro; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def readSkel (parent : Noun) (rec : MemRecSkeleton) : MemoryRowSkeleton where
  state := .read_root
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => parent
  memoryRecord := fun _ => rec

def verifySkel (parent : Noun) (rec : MemRecSkeleton) : MemoryRowSkeleton where
  state := .verify_child
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => parent
  memoryRecord := fun _ => rec

def decSkel (parent left right : Noun) : MemoryRowSkeleton where
  state := .decompose
  parent := parent
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then left else right
  memoryRecord := fun h => nomatch h

theorem bind_halt (k : ℕ) (acc : K97cubic) :
    BindMemoryRowA seedD (haltSkel k) (lblOf (haltPub k acc)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem (haltSkel k).state) := by
      simp [haltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_read (parent : Noun) (rec : MemRecSkeleton)
    (pt lc : MemoryTable.Cell K97cubic) (tableRec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic)
    (hpt : pt.noun = encD parent) (hlc : lc.noun = encD parent)
    (hroot : tableRec.root = encD rec.root) (hchild : tableRec.child = encD rec.child)
    (haxis : tableRec.axis = (rec.axis : K97cubic)) :
    BindMemoryRowA seedD (readSkel parent rec)
      (lblOf (readPubA pt lc tableRec ipre icur)) := by
  refine ⟨rfl, rfl, rfl, hpt, ?_, ⟨hroot, hchild, haxis⟩, rfl⟩
  intro i
  fin_cases i
  · rw [dif_pos (by simp [readSkel, MemoryTable.fanoutMem])]
    exact hlc
  · rw [dif_neg (by simp [readSkel, MemoryTable.fanoutMem])]
    rfl

theorem bind_verify (parent : Noun) (rec : MemRecSkeleton)
    (pt lc : MemoryTable.Cell K97cubic) (tableRec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic)
    (hpt : pt.noun = encD parent) (hlc : lc.noun = encD parent)
    (hroot : tableRec.root = encD rec.root) (hchild : tableRec.child = encD rec.child)
    (haxis : tableRec.axis = (rec.axis : K97cubic)) :
    BindMemoryRowA seedD (verifySkel parent rec)
      (lblOf (verifyPubA pt lc tableRec ipre icur)) := by
  refine ⟨rfl, rfl, rfl, hpt, ?_, ⟨hroot, hchild, haxis⟩, rfl⟩
  intro i
  fin_cases i
  · rw [dif_pos (by simp [verifySkel, MemoryTable.fanoutMem])]
    exact hlc
  · rw [dif_neg (by simp [verifySkel, MemoryTable.fanoutMem])]
    rfl

theorem bind_dec (parent left right : Noun)
    (pt lc rc : MemoryTable.Cell K97cubic) (lcSt rcSt : MState) (acc : K97cubic)
    (hpt : pt.noun = encD parent) (hlc : lc.noun = encD left)
    (hrc : rc.noun = encD right) :
    BindMemoryRowA seedD (decSkel parent left right)
      (lblOf (decPub pt lc rc lcSt rcSt acc)) := by
  refine ⟨rfl, rfl, rfl, hpt, ?_, rfl, rfl⟩
  intro i
  fin_cases i <;>
    rw [dif_pos (by simp [decSkel, MemoryTable.fanoutMem])] <;> first | exact hlc | exact hrc

theorem stamp_padding {st : MState} (hst : memoryMemRecKind st = .padding)
    (pub : MemoryTable.Pub K97cubic) (hpub : pub.st = st)
    (hmem : pub.mem = ComputeTable.MemRec.zero) (e : ℕ) :
    MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp st e) (lblOf pub) := by
  have hne : ¬ (memoryMemRecKind (memStamp st e).state = FPSlotKind.active) := by
    show ¬ (memoryMemRecKind st = FPSlotKind.active)
    rw [hst]; simp
  refine ⟨hpub, hpub, ?_, ?_⟩
  · show pub.mem.ts = _
    rw [if_neg hne, hmem]; rfl
  · intro _; exact hmem

theorem stamp_active (st : MState) (e : ℕ) (pub : MemoryTable.Pub K97cubic)
    (hpub : pub.st = st) (hact : memoryMemRecKind st = .active)
    (hts : pub.mem.ts = cfgD.challenges.α ^ e) :
    MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp st e) (lblOf pub) := by
  refine ⟨hpub, hpub, ?_, ?_⟩
  · show pub.mem.ts = _
    have hpos : memoryMemRecKind (memStamp st e).state = FPSlotKind.active := by
      simpa [memStamp] using hact
    rw [if_pos hpos, hts]
    simp [memStamp]
  · intro h
    exact absurd h (by simp [memStamp, hact])

/-! ## F. The twenty-one committed memory skeletons, matching `rootTreeD` -/

def skelN1 : MemoryRowSkeleton := readSkel op5Formula recFSkel
def skelN2 : MemoryRowSkeleton := decSkel op5Formula op5Head op5Tail
def skelN3 : MemoryRowSkeleton := haltSkel 5
def skelN4 : MemoryRowSkeleton := readSkel op5Tail recTSkel
def skelN5 : MemoryRowSkeleton := verifySkel op5Tail recFSkel
def skelN6 : MemoryRowSkeleton := decSkel op5Tail leftFormula rightFormula
def skelN7 : MemoryRowSkeleton := readSkel leftFormula recLSkel
def skelN8 : MemoryRowSkeleton := verifySkel leftFormula recTSkel
def skelN9 : MemoryRowSkeleton := decSkel leftFormula op1Head operandLeft
def skelN10 : MemoryRowSkeleton := haltSkel 1
def skelN11 : MemoryRowSkeleton := verifySkel operandLeft recLSkel
def skelN12 : MemoryRowSkeleton := decSkel operandLeft (.atom 7) (.atom 9)
def skelN13 : MemoryRowSkeleton := haltSkel 7
def skelN14 : MemoryRowSkeleton := haltSkel 9
def skelN15 : MemoryRowSkeleton := readSkel rightFormula recRSkel
def skelN16 : MemoryRowSkeleton := decSkel rightFormula op1Head operandRight
def skelN17 : MemoryRowSkeleton := haltSkel 1
def skelN18 : MemoryRowSkeleton := verifySkel operandRight recRSkel
def skelN19 : MemoryRowSkeleton := decSkel operandRight (.atom 8) (.atom 10)
def skelN20 : MemoryRowSkeleton := haltSkel 8
def skelN21 : MemoryRowSkeleton := haltSkel 10

theorem bind_n1 : BindMemoryRowA seedD skelN1 (lblOf pN1A) :=
  bind_read op5Formula recFSkel cF0 cFd recF 0 qF rfl rfl rfl rfl rfl
theorem bind_n2 : BindMemoryRowA seedD skelN2 (lblOf pN2) :=
  bind_dec op5Formula op5Head op5Tail cFd cH5 cT0 .halt .read_root qF rfl rfl rfl
theorem bind_n3 : BindMemoryRowA seedD skelN3 (lblOf pN3) := bind_halt 5 qF
theorem bind_n4 : BindMemoryRowA seedD skelN4 (lblOf pN4A) :=
  bind_read op5Tail recTSkel cT0 cTv recT qF (qF + qT) rfl rfl rfl rfl rfl
theorem bind_n5 : BindMemoryRowA seedD skelN5 (lblOf pN5A) :=
  bind_verify op5Tail recFSkel cTv cTd recF (qF + qT) qT rfl rfl rfl rfl rfl
theorem bind_n6 : BindMemoryRowA seedD skelN6 (lblOf pN6) :=
  bind_dec op5Tail leftFormula rightFormula cTd cL0 cR0 .read_root .read_root qT rfl rfl rfl
theorem bind_n7 : BindMemoryRowA seedD skelN7 (lblOf pN7A) :=
  bind_read leftFormula recLSkel cL0 cLv recL qT (qT + qL) rfl rfl rfl rfl rfl
theorem bind_n8 : BindMemoryRowA seedD skelN8 (lblOf pN8A) :=
  bind_verify leftFormula recTSkel cLv cLd recT (qT + qL + qR) (qL + qR) rfl rfl rfl rfl rfl
theorem bind_n9 : BindMemoryRowA seedD skelN9 (lblOf pN9) :=
  bind_dec leftFormula op1Head operandLeft cLd cA1 cOL0 .halt .verify_child (qL + qR) rfl rfl rfl
theorem bind_n10 : BindMemoryRowA seedD skelN10 (lblOf pN10) := bind_halt 1 qL
theorem bind_n11 : BindMemoryRowA seedD skelN11 (lblOf pN11A) :=
  bind_verify operandLeft recLSkel cOL0 cOLd recL qL 0 rfl rfl rfl rfl rfl
theorem bind_n12 : BindMemoryRowA seedD skelN12 (lblOf pN12) :=
  bind_dec operandLeft (.atom 7) (.atom 9) cOLd cA7 cA9 .halt .halt 0 rfl rfl rfl
theorem bind_n13 : BindMemoryRowA seedD skelN13 (lblOf pN13) := bind_halt 7 0
theorem bind_n14 : BindMemoryRowA seedD skelN14 (lblOf pN14) := bind_halt 9 0
theorem bind_n15 : BindMemoryRowA seedD skelN15 (lblOf pN15A) :=
  bind_read rightFormula recRSkel cR0 cRd recR (qT + qL) (qT + qL + qR) rfl rfl rfl rfl rfl
theorem bind_n16 : BindMemoryRowA seedD skelN16 (lblOf pN16) :=
  bind_dec rightFormula op1Head operandRight cRd cA1 cOR0 .halt .verify_child (qL + qR) rfl rfl rfl
theorem bind_n17 : BindMemoryRowA seedD skelN17 (lblOf pN17) := bind_halt 1 (qL + qR)
theorem bind_n18 : BindMemoryRowA seedD skelN18 (lblOf pN18A) :=
  bind_verify operandRight recRSkel cOR0 cORd recR (qL + qR) qL rfl rfl rfl rfl rfl
theorem bind_n19 : BindMemoryRowA seedD skelN19 (lblOf pN19) :=
  bind_dec operandRight (.atom 8) (.atom 10) cORd cA8 cA10 .halt .halt 0 rfl rfl rfl
theorem bind_n20 : BindMemoryRowA seedD skelN20 (lblOf pN20) := bind_halt 8 0
theorem bind_n21 : BindMemoryRowA seedD skelN21 (lblOf pN21) := bind_halt 10 0

theorem stamp_n1 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .read_root 1)
    (lblOf pN1A) :=
  stamp_active .read_root 1 pN1A rfl rfl (by rw [pow_one]; rfl)
theorem stamp_n2 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN2) :=
  stamp_padding (st := .decompose) rfl pN2 rfl rfl 0
theorem stamp_n3 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN3) :=
  stamp_padding (st := .halt) rfl pN3 rfl rfl 0
theorem stamp_n4 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .read_root 2)
    (lblOf pN4A) :=
  stamp_active .read_root 2 pN4A rfl rfl rfl
theorem stamp_n5 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .verify_child 1)
    (lblOf pN5A) :=
  stamp_active .verify_child 1 pN5A rfl rfl (by rw [pow_one]; rfl)
theorem stamp_n6 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN6) :=
  stamp_padding (st := .decompose) rfl pN6 rfl rfl 0
theorem stamp_n7 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .read_root 3)
    (lblOf pN7A) :=
  stamp_active .read_root 3 pN7A rfl rfl rfl
theorem stamp_n8 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .verify_child 2)
    (lblOf pN8A) :=
  stamp_active .verify_child 2 pN8A rfl rfl rfl
theorem stamp_n9 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN9) :=
  stamp_padding (st := .decompose) rfl pN9 rfl rfl 0
theorem stamp_n10 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN10) :=
  stamp_padding (st := .halt) rfl pN10 rfl rfl 0
theorem stamp_n11 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .verify_child 3)
    (lblOf pN11A) :=
  stamp_active .verify_child 3 pN11A rfl rfl rfl
theorem stamp_n12 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN12) :=
  stamp_padding (st := .decompose) rfl pN12 rfl rfl 0
theorem stamp_n13 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN13) :=
  stamp_padding (st := .halt) rfl pN13 rfl rfl 0
theorem stamp_n14 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN14) :=
  stamp_padding (st := .halt) rfl pN14 rfl rfl 0
theorem stamp_n15 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .read_root 4)
    (lblOf pN15A) :=
  stamp_active .read_root 4 pN15A rfl rfl rfl
theorem stamp_n16 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN16) :=
  stamp_padding (st := .decompose) rfl pN16 rfl rfl 0
theorem stamp_n17 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN17) :=
  stamp_padding (st := .halt) rfl pN17 rfl rfl 0
theorem stamp_n18 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .verify_child 4)
    (lblOf pN18A) :=
  stamp_active .verify_child 4 pN18A rfl rfl rfl
theorem stamp_n19 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .decompose 0)
    (lblOf pN19) :=
  stamp_padding (st := .decompose) rfl pN19 rfl rfl 0
theorem stamp_n20 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN20) :=
  stamp_padding (st := .halt) rfl pN20 rfl rfl 0
theorem stamp_n21 : MemoryTimestampSpecializesAt cfgD.challenges.α (memStamp .halt 0)
    (lblOf pN21) :=
  stamp_padding (st := .halt) rfl pN21 rfl rfl 0

/-! ## G. The committed node trees -/

def op5Node : ComputeNode K97cubic where
  skel := op5SkelD
  stamp := op5Stamp
  row := op5RowD

def op1LNode : ComputeNode K97cubic where
  skel := op1LSkelD
  stamp := op1LStamp
  row := op1LRow

def op1RNode : ComputeNode K97cubic where
  skel := op1RSkelD
  stamp := op1RStamp
  row := op1RRow

def computeNodesD : NTree (ComputeNode K97cubic) :=
  .node op5Node [.node op1LNode [], .node op1RNode []]

def memNode (skel : MemoryRowSkeleton) (e : ℕ) (pub : MemoryTable.Pub K97cubic) :
    MemoryNode K97cubic where
  skel := skel
  stamp := memStamp skel.state e
  row := lblOf pub

def nN14 : NTree (MemoryNode K97cubic) := .node (memNode skelN14 0 pN14) []
def nN13 : NTree (MemoryNode K97cubic) := .node (memNode skelN13 0 pN13) []
def nN12 : NTree (MemoryNode K97cubic) := .node (memNode skelN12 0 pN12) [nN13, nN14]
def nN11 : NTree (MemoryNode K97cubic) := .node (memNode skelN11 3 pN11A) [nN12]
def nN10 : NTree (MemoryNode K97cubic) := .node (memNode skelN10 0 pN10) []
def nN9 : NTree (MemoryNode K97cubic) := .node (memNode skelN9 0 pN9) [nN10, nN11]
def nN8 : NTree (MemoryNode K97cubic) := .node (memNode skelN8 2 pN8A) [nN9]
def nN7 : NTree (MemoryNode K97cubic) := .node (memNode skelN7 3 pN7A) [nN8]
def nN21 : NTree (MemoryNode K97cubic) := .node (memNode skelN21 0 pN21) []
def nN20 : NTree (MemoryNode K97cubic) := .node (memNode skelN20 0 pN20) []
def nN19 : NTree (MemoryNode K97cubic) := .node (memNode skelN19 0 pN19) [nN20, nN21]
def nN18 : NTree (MemoryNode K97cubic) := .node (memNode skelN18 4 pN18A) [nN19]
def nN17 : NTree (MemoryNode K97cubic) := .node (memNode skelN17 0 pN17) []
def nN16 : NTree (MemoryNode K97cubic) := .node (memNode skelN16 0 pN16) [nN17, nN18]
def nN15 : NTree (MemoryNode K97cubic) := .node (memNode skelN15 4 pN15A) [nN16]
def nN6 : NTree (MemoryNode K97cubic) := .node (memNode skelN6 0 pN6) [nN7, nN15]
def nN5 : NTree (MemoryNode K97cubic) := .node (memNode skelN5 1 pN5A) [nN6]
def nN4 : NTree (MemoryNode K97cubic) := .node (memNode skelN4 2 pN4A) [nN5]
def nN3 : NTree (MemoryNode K97cubic) := .node (memNode skelN3 0 pN3) []
def nN2 : NTree (MemoryNode K97cubic) := .node (memNode skelN2 0 pN2) [nN3, nN4]
def nN1 : NTree (MemoryNode K97cubic) := .node (memNode skelN1 1 pN1A) [nN2]

def memoryNodesD : List (NTree (MemoryNode K97cubic)) := [nN1]

/-! ## H. Local validity of every committed node at the honest sample -/

theorem computeNodesD_OK :
    ComputeNodesOK cfgD.challenges.z cfgD.challenges.α computeNodesD := by
  refine ComputeNodesOK.mk' ⟨rfl, rfl, bind_op5, stamp_op5⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ComputeNodesOK.mk' ⟨rfl, rfl, bind_op1L, stamp_op1L⟩ (by simp)
  · exact ComputeNodesOK.mk' ⟨rfl, rfl, bind_op1R, stamp_op1R⟩ (by simp)

theorem nN14_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN14 := by
  unfold nN14
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n14, stamp_n14⟩ (by simp)
theorem nN13_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN13 := by
  unfold nN13
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n13, stamp_n13⟩ (by simp)
theorem nN21_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN21 := by
  unfold nN21
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n21, stamp_n21⟩ (by simp)
theorem nN20_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN20 := by
  unfold nN20
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n20, stamp_n20⟩ (by simp)
theorem nN10_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN10 := by
  unfold nN10
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n10, stamp_n10⟩ (by simp)
theorem nN17_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN17 := by
  unfold nN17
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n17, stamp_n17⟩ (by simp)
theorem nN3_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN3 := by
  unfold nN3
  exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_n3, stamp_n3⟩ (by simp)

theorem nN12_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN12 := by
  unfold nN12
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n12, stamp_n12⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN13_OK
  · exact nN14_OK

theorem nN11_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN11 := by
  unfold nN11
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n11, stamp_n11⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN12_OK

theorem nN9_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN9 := by
  unfold nN9
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n9, stamp_n9⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN10_OK
  · exact nN11_OK

theorem nN8_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN8 := by
  unfold nN8
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n8, stamp_n8⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN9_OK

theorem nN7_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN7 := by
  unfold nN7
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n7, stamp_n7⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN8_OK

theorem nN19_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN19 := by
  unfold nN19
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n19, stamp_n19⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN20_OK
  · exact nN21_OK

theorem nN18_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN18 := by
  unfold nN18
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n18, stamp_n18⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN19_OK

theorem nN16_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN16 := by
  unfold nN16
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n16, stamp_n16⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN17_OK
  · exact nN18_OK

theorem nN15_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN15 := by
  unfold nN15
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n15, stamp_n15⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN16_OK

theorem nN6_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN6 := by
  unfold nN6
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n6, stamp_n6⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN7_OK
  · exact nN15_OK

theorem nN5_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN5 := by
  unfold nN5
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n5, stamp_n5⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN6_OK

theorem nN4_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN4 := by
  unfold nN4
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n4, stamp_n4⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN5_OK

theorem nN2_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN2 := by
  unfold nN2
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n2, stamp_n2⟩ ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact nN3_OK
  · exact nN4_OK

theorem nN1_OK : MemoryNodesOK cfgD.challenges.z cfgD.challenges.α nN1 := by
  unfold nN1
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_n1, stamp_n1⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact nN2_OK

/-! ## I. The committed skeleton and its BFS rows -/

def skelD : SemanticSkeleton := skeletonOfNodes computeNodesD memoryNodesD

theorem computeSkeletonRowsD :
    computeSkeletonRows skelD = [op5SkelD, op1LSkelD, op1RSkelD] := by
  norm_num [computeSkeletonRows, skelD, skeletonOfNodes, computeNodesD, mapNTree,
    op5Node, op1LNode, op1RNode, bfsForest, NTree.size, totalSize]

/-! ## J. Skeleton-only semantic obligations -/

theorem slotSemanticsD :
    ∀ s ∈ computeSkeletonRows skelD, ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  rw [computeSkeletonRowsD] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact
      { s0_slot := fun h => absurd h (by simp [op5SkelD, op5Row])
        s9_slot := fun h => absurd h (by simp [op5SkelD, op5Row]) }
  · exact
      { s0_slot := fun h => absurd h (by simp [op1LSkelD, op1RowOf])
        s9_slot := fun h => absurd h (by simp [op1LSkelD, op1RowOf]) }
  · exact
      { s0_slot := fun h => absurd h (by simp [op1RSkelD, op1RowOf])
        s9_slot := fun h => absurd h (by simp [op1RSkelD, op1RowOf]) }

theorem recordEquationsD :
    ∀ s ∈ computeSkeletonRows skelD, ServedLookupBridge.SkeletonRecordEquations s := by
  intro s hs
  rw [computeSkeletonRowsD] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact
      { s0_record := fun h => absurd h (by simp [op5SkelD, op5Row])
        s9_record := fun h => absurd h (by simp [op5SkelD, op5Row]) }
  · exact
      { s0_record := fun h => absurd h (by simp [op1LSkelD, op1RowOf])
        s9_record := fun h => absurd h (by simp [op1LSkelD, op1RowOf]) }
  · exact
      { s0_record := fun h => absurd h (by simp [op1RSkelD, op1RowOf])
        s9_record := fun h => absurd h (by simp [op1RSkelD, op1RowOf]) }

theorem sizeWindowBoundD :
    SizeWindowCounting.SizeWindowNounsBoundedBy skelD 7 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeSkeletonRowsD] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, op5SkelD, op5Row, op1LSkelD, op1RSkelD,
    op1RowOf] at hn

theorem skeletonComparisonCensusD :
    P8Census.skeletonComparisonCensus (K := K97cubic) skelD =
      P8Census.skeletonComparisons (K := K97cubic) op5SkelD ++
        P8Census.skeletonComparisons (K := K97cubic) op1LSkelD ++
          P8Census.skeletonComparisons (K := K97cubic) op1RSkelD := by
  rw [P8Census.skeletonComparisonCensus, computeSkeletonRowsD]
  simp

/-- The `OP_5`/`OP_1` comparison lists do not read `memoryRecord`, so the four real NMR records
do not change the census content. -/
theorem combinedPairsD :
    EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelD = op5Pairs := by
  rw [op5Pairs_eq, EdgeComparisonCensus.combinedSkeletonPairs,
    BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusD]
  simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonSubformula, SemanticTrace.ComparisonUse.pair,
    SemanticSkeleton.publicClaim, EdgeComparisonCensus.edgePairs,
    EdgeComparisonCensus.rowEdgePairs, EdgeComparisonCensus.edgeTriple, skelD,
    skeletonOfNodes, computeNodesD, mapNTree, op5Node, op1LNode, op1RNode, op5SkelD, op5Row,
    op1LSkelD, op1RSkelD, op1RowOf, decActive, hasTailDecomposition, ComputeTable.fanoutComp,
    bfsForest, NTree.childOpt, NTree.children, NTree.label, op5Result_is_tis]
  simp [op5Formula, op5Tail, leftFormula, rightFormula]

def censusD : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic skelD 7 where
  p8 :=
    { leaves_bounded := fun pair hp =>
        op5Pairs_bounded pair (by
          rw [← combinedPairsD, EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
          exact Or.inl hp) }
  edges :=
    { leaves_bounded := fun pair hp =>
        op5Pairs_bounded pair (by
          rw [← combinedPairsD, EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
          exact Or.inr hp) }

theorem censusD_has_distinct_pair :
    ∃ i : Fin censusD.census.count,
      censusD.census.pair i = (operandLeft, operandRight) ∧
        (censusD.census.pair i).1 ≠ (censusD.census.pair i).2 := by
  have hmem : (operandLeft, operandRight) ∈
      EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelD := by
    rw [combinedPairsD]
    exact operands_mem_op5Pairs
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
  let i : Fin censusD.census.count := ⟨j, by
    simpa only [EdgeComparisonCensus.CombinedSkeletonCensus.census,
      ComparisonCensus.ofPairList_count] using j.isLt⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [EdgeComparisonCensus.CombinedSkeletonCensus.census, i] using hj
  · have hi : censusD.census.pair i =
        (EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelD).get j := by
      simp [EdgeComparisonCensus.CombinedSkeletonCensus.census, i]
    rw [hi, hj]
    exact operands_ne

/-! ## K. Boundedness -/

theorem op5SkelD_bounded : op5SkelD.BoundedBy 97 := by
  refine ⟨by simp [op5SkelD, op5Row, op5Subject, FieldEmbedding.BoundedBy],
    bounded_op5Formula, by simp [op5SkelD, op5Row, op5Result, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [op5SkelD, op5Row, op5Head, op5Tail, leftFormula, rightFormula, operandLeft,
        operandRight, FieldEmbedding.BoundedBy]
  · intro i h slot
    fin_cases i <;> cases slot <;>
      simp [op5SkelD, op5Row, op5Subject, leftFormula, rightFormula, operandLeft, operandRight,
        FieldEmbedding.BoundedBy]
  · intro i h
    fin_cases i
    · exact ⟨bounded_op5Formula, bounded_op5Tail⟩
    · exact ⟨bounded_op5Tail, bounded_leftFormula⟩
    · simp [op5SkelD, op5Row, Nock.Framework.recordCount] at h

theorem op1LSkelD_bounded : op1LSkelD.BoundedBy 97 := by
  refine ⟨by simp [op1LSkelD, op1RowOf, op5Subject, FieldEmbedding.BoundedBy],
    bounded_leftFormula, bounded_operandLeft, ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [op1LSkelD, op1RowOf, op1Head, operandLeft, FieldEmbedding.BoundedBy]
  · intro i h
    simp [op1LSkelD, op1RowOf, ComputeTable.fanoutComp] at h
  · intro i h
    fin_cases i
    · exact ⟨bounded_leftFormula, bounded_operandLeft⟩
    · simp [op1LSkelD, op1RowOf, Nock.Framework.recordCount] at h
    · simp [op1LSkelD, op1RowOf, Nock.Framework.recordCount] at h

theorem op1RSkelD_bounded : op1RSkelD.BoundedBy 97 := by
  refine ⟨by simp [op1RSkelD, op1RowOf, op5Subject, FieldEmbedding.BoundedBy],
    bounded_rightFormula, bounded_operandRight, ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [op1RSkelD, op1RowOf, op1Head, operandRight, FieldEmbedding.BoundedBy]
  · intro i h
    simp [op1RSkelD, op1RowOf, ComputeTable.fanoutComp] at h
  · intro i h
    fin_cases i
    · exact ⟨bounded_rightFormula, bounded_operandRight⟩
    · simp [op1RSkelD, op1RowOf, Nock.Framework.recordCount] at h
    · simp [op1RSkelD, op1RowOf, Nock.Framework.recordCount] at h

theorem memoryRow_bounded :
    ∀ s ∈ [skelN1, skelN2, skelN3, skelN4, skelN5, skelN6, skelN7, skelN8, skelN9, skelN10,
      skelN11, skelN12, skelN13, skelN14, skelN15, skelN16, skelN17, skelN18, skelN19, skelN20,
      skelN21], s.BoundedBy 97 := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨bounded_op5Formula, fun _ _ => bounded_op5Formula,
      fun _ => ⟨bounded_op5Formula, bounded_op5Tail⟩⟩
  · refine ⟨bounded_op5Formula, ?_, fun h => by simp [skelN2, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i
    · simp [skelN2, decSkel, op5Head, FieldEmbedding.BoundedBy]
    · exact bounded_op5Tail
  · exact ⟨by simp [skelN3, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN3, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN3, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨bounded_op5Tail, fun _ _ => bounded_op5Tail,
      fun _ => ⟨bounded_op5Tail, bounded_leftFormula⟩⟩
  · exact ⟨bounded_op5Tail, fun _ _ => bounded_op5Tail,
      fun _ => ⟨bounded_op5Formula, bounded_op5Tail⟩⟩
  · refine ⟨bounded_op5Tail, ?_, fun h => by simp [skelN6, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i
    · exact bounded_leftFormula
    · exact bounded_rightFormula
  · exact ⟨bounded_leftFormula, fun _ _ => bounded_leftFormula,
      fun _ => ⟨bounded_leftFormula, bounded_operandLeft⟩⟩
  · exact ⟨bounded_leftFormula, fun _ _ => bounded_leftFormula,
      fun _ => ⟨bounded_op5Tail, bounded_leftFormula⟩⟩
  · refine ⟨bounded_leftFormula, ?_, fun h => by simp [skelN9, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i
    · simp [skelN9, decSkel, op1Head, FieldEmbedding.BoundedBy]
    · exact bounded_operandLeft
  · exact ⟨by simp [skelN10, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN10, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN10, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨bounded_operandLeft, fun _ _ => bounded_operandLeft,
      fun _ => ⟨bounded_leftFormula, bounded_operandLeft⟩⟩
  · refine ⟨bounded_operandLeft, ?_, fun h => by simp [skelN12, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i <;>
      simp [skelN12, decSkel, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [skelN13, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN13, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN13, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨by simp [skelN14, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN14, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN14, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨bounded_rightFormula, fun _ _ => bounded_rightFormula,
      fun _ => ⟨bounded_rightFormula, bounded_operandRight⟩⟩
  · refine ⟨bounded_rightFormula, ?_, fun h => by simp [skelN16, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i
    · simp [skelN16, decSkel, op1Head, FieldEmbedding.BoundedBy]
    · exact bounded_operandRight
  · exact ⟨by simp [skelN17, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN17, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN17, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨bounded_operandRight, fun _ _ => bounded_operandRight,
      fun _ => ⟨bounded_rightFormula, bounded_operandRight⟩⟩
  · refine ⟨bounded_operandRight, ?_, fun h => by simp [skelN19, decSkel, memoryMemRecKind] at h⟩
    intro i h; fin_cases i <;>
      simp [skelN19, decSkel, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [skelN20, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN20, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN20, haltSkel, memoryMemRecKind] at h⟩
  · exact ⟨by simp [skelN21, haltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [skelN21, haltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [skelN21, haltSkel, memoryMemRecKind] at h⟩

theorem memorySkeletonRowsD :
    memorySkeletonRows skelD =
      [skelN1, skelN2, skelN3, skelN4, skelN5, skelN6, skelN7, skelN15, skelN8, skelN16,
        skelN9, skelN17, skelN18, skelN10, skelN11, skelN19, skelN12, skelN20, skelN21,
        skelN13, skelN14] := by
  norm_num [memorySkeletonRows, skelD, skeletonOfNodes, memoryNodesD, mapNTree, memNode,
    nN1, nN2, nN3, nN4, nN5, nN6, nN7, nN8, nN9, nN10, nN11, nN12, nN13, nN14, nN15, nN16,
    nN17, nN18, nN19, nN20, nN21, bfsForest, NTree.size, totalSize]

theorem skeletonBoundedD : skelD.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeSkeletonRowsD]
    exact ⟨op5SkelD_bounded, op1LSkelD_bounded, op1RSkelD_bounded⟩
  · rw [List.forall_iff_forall_mem, memorySkeletonRowsD]
    intro s hs
    exact memoryRow_bounded s (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
      tauto)
  · intro tree htree node hnode
    have hm : node ∈ bfsForest skelD.memoryForest :=
      (mem_bfsForest skelD.memoryForest node).2 ⟨tree, htree, hnode⟩
    have hlbl : node.label ∈ memorySkeletonRows skelD :=
      List.mem_map_of_mem hm
    rw [memorySkeletonRowsD] at hlbl
    exact memoryRow_bounded _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlbl ⊢
      tauto)

theorem combinedBoundedD :
    ProductionP8Containment.CombinedBoundedBy K97cubic 97 skelD := by
  intro pair hpair
  have h : pair ∈ op5Pairs := by rwa [← combinedPairsD]
  exact op5_combinedBounded pair h

/-! ## L. The honest commitment -/


/-- **`HonestCommitment.Data` over the distinct-pair `OP_5` execution.**  The committed compute
tree is the three-row `OP_5`/`OP_1`/`OP_1` skeleton whose census contains `([7 9], [8 10])`; the
committed memory forest is the twenty-one-row serviced root.  Honest-seed bindings are at
`(z, α) = (8, 4)`. -/
def dataD : HonestCommitment.Data (distinctCensusExecution hfirstD) where
  computeNodes := computeNodesD
  memoryNodes := memoryNodesD
  compute_rows := by
    show mapNTree ComputeNode.row computeNodesD = computeTreeD
    simp [computeNodesD, op5Node, op1LNode, op1RNode, mapNTree, computeTreeD]
  memory_rows := by
    show memoryNodesD.map (mapNTree MemoryNode.row) = [rootTreeDA]
    simp [memoryNodesD, nN1, nN2, nN3, nN4, nN5, nN6, nN7, nN8, nN9, nN10, nN11, nN12, nN13,
      nN14, nN15, nN16, nN17, nN18, nN19, nN20, nN21, memNode, mapNTree, rootTreeDA, tN2A, tN3,
      tN4A, tN5A, tN6A, tN7A, tN8A, tN9A, tN10, tN11A, tN12, tN13, tN14, tN15A, tN16A, tN17,
          tN18A, tN19,
      tN20, tN21, mOne, mTwo, mLeaf, lblOf]
  computeOK := computeNodesD_OK
  memoryOK := by
    intro t ht
    simp only [memoryNodesD, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    exact nN1_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 7
  Λ := 7
  slotSemantics := slotSemanticsD
  recordEquations := recordEquationsD
  census := censusD
  sizeWindowBound := sizeWindowBoundD
  q_eq_ringChar := ringChar_K97.symm
  skeletonBounded := skeletonBoundedD
  combinedBounded := combinedBoundedD

theorem dataD_skeleton : (dataD hfirstD).skeleton = skelD := rfl

theorem dataD_has_distinct_pair :
    ∃ i : Fin (dataD hfirstD).census.census.count,
      (dataD hfirstD).census.census.pair i = (operandLeft, operandRight) ∧
        ((dataD hfirstD).census.census.pair i).1 ≠ ((dataD hfirstD).census.census.pair i).2 :=
  censusD_has_distinct_pair

/-- **`CommitmentResidual (distinctCensusExecution hfirstD)`.**  Post-challenge arrays are the all-zero
later-round message: they inhabit the constructor and claim **no** acceptance. -/
def residualD : BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD) :=
  HonestCommitment.commitmentResidualOfZero (dataD hfirstD)

/-! ## M. Pre-compilation backend inputs and the constructed package

The orbit height is `5` because twenty-one memory rows do not fit `2^4 = 16`
. Post-challenge arrays remain the all-zero later-round message, so the
constructed package does **not** claim acceptance. -/

open Module StrictExtension BuildableChips

theorem memoryBudgetD :
    RowLayout.memoryM execD = 13 ∧ RowLayout.memoryL execD = 4 ∧
      cfgD.memRows = RowLayout.memoryM execD + 2 * RowLayout.memoryL execD := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RowLayout.memoryM, memoryStateCountsD.2.2.1, memoryStateCountsD.2.2.2]
  · exact memoryStateCountsD.1
  · rw [RowLayout.memoryM, RowLayout.memoryL, memoryStateCountsD.2.2.1,
      memoryStateCountsD.2.2.2, memoryStateCountsD.1]
    norm_num [cfgD]

/-- Strict RAP orbit of exact order `3 · 2^5 = 96`. -/
def strictOrbitD : StrictOrbitDomain F97 3 5 where
  ω := Classical.choose (exists_zmod_generator_of_dvd_sub_one 97 96 (by norm_num))
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by
    simpa using Classical.choose_spec
      (exists_zmod_generator_of_dvd_sub_one 97 96 (by norm_num))
  βcoset_ne_zero := one_ne_zero

def sampledRecordsD : FiniteIO.PreChallengeRecords K97cubic 9 :=
  executionRecords (distinctCensusExecution hfirstD)

theorem sampledRecordsD_lengths :
    (sampledRecordsD hfirstD).requests.length = 4 ∧ (sampledRecordsD hfirstD).responses.length = 4 := by
  constructor
  · change execD.derivedRequestIO.length = 4
    rw [derived_requestsD]; rfl
  · change execD.derivedResponseIO.length = 4
    rw [derived_responsesD]; rfl

theorem ioFailureBoundD :
    (FiniteIO.IOFailureEvent (sampledRecordsD hfirstD)).card <
      Fintype.card (K97cubic × K97cubic) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le (sampledRecordsD hfirstD)) ?_
  rw [(sampledRecordsD_lengths hfirstD).1, (sampledRecordsD_lengths hfirstD).2]
  simp only [FiniteIO.ioFailureUnionBound, Fintype.card_prod]
  rw [MultiRootServedFixture.cardK97cubic]
  norm_num

theorem goodIOCoinsD_exists :
    ∃ coins : FiniteIO.IOCoins K97cubic,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsD hfirstD) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (distinctCensusExecution hfirstD)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecordsD hfirstD)
    (sampledRecordsD_lengths hfirstD).1.le (sampledRecordsD_lengths hfirstD).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, MultiRootServedFixture.cardK97cubic]
      norm_num)

def ioCoinsD : FiniteIO.IOCoins K97cubic := Classical.choose (goodIOCoinsD_exists hfirstD)

theorem ioCoinsD_good :
    ((ioCoinsD hfirstD).gamma, (ioCoinsD hfirstD).pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsD hfirstD) :=
  (Classical.choose_spec (goodIOCoinsD_exists hfirstD)).1

theorem ioCoinsD_good10 :
    ((ioCoinsD hfirstD).gamma, (ioCoinsD hfirstD).pole) ∉
      FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (distinctCensusExecution hfirstD)) :=
  (Classical.choose_spec (goodIOCoinsD_exists hfirstD)).2

theorem inputsD_interCard :
    2 * ((executionInterRecords (distinctCensusExecution hfirstD)).requests.length +
      (executionInterRecords (distinctCensusExecution hfirstD)).responses.length) + 1 < Fintype.card K97cubic :=
  executionInterRecords_card_lt_of_memRows (distinctCensusExecution hfirstD) (by
    have hmem : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
    have hcard : Fintype.card K97cubic = 97 ^ 3 := by
      rw [Fintype.card_eq_nat_card]
      exact GaloisField.card 97 3 (by norm_num)
    rw [hmem, hcard]
    norm_num)

/-- Honest `ver = (st = read_root)` on the distinct-census fixture. -/
theorem honestVerD :
    ∀ row ∈ (distinctCensusExecution hfirstD).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  change ∀ row ∈ execD.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  simp [execution_rowsD.2, memoryLabelsD, lblOf,
    pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10, pN11,
    pN19, pN12, pN20, pN21, pN13, pN14, readPub, decPub, haltPub, verifyPub]

def inputsD : Inputs (distinctCensusExecution hfirstD) where
  stateTagChar := stateTagChar97
  computeWalkAlpha := 2
  memoryWalkAlpha := 3
  walkGamma := 5
  hOrb := 5
  basis := basis97
  orbit := strictOrbitD
  activeDomains :=
    { computeCapacity := by
        change 3 ≤ 32
        norm_num
      memoryCapacity := by
        rw [show RowLayout.memoryM (distinctCensusExecution hfirstD).exec = 13 from memoryBudgetD.1,
          show RowLayout.memoryL (distinctCensusExecution hfirstD).exec = 4 from memoryBudgetD.2.1]
        norm_num }
  ioCoins := ioCoinsD hfirstD
  ioPoleHitGood := by
    intro h
    apply ioCoinsD_good hfirstD
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inr (Or.inl h)
  ioGammaGood := by
    intro h
    apply ioCoinsD_good hfirstD
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inl h
  ioLogDerivGood := by
    intro h
    apply ioCoinsD_good hfirstD
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inr (Or.inr h)
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F97) + 1
  memoryExtensionFold :=
    interPoleOfE (distinctCensusExecution hfirstD) (ioCoinsD hfirstD).gamma (inputsD_interCard hfirstD)
  interPoleHitGood :=
    interPoleOfE_good (distinctCensusExecution hfirstD) (ioCoinsD hfirstD).gamma (inputsD_interCard hfirstD)
  honestVer := honestVerD hfirstD
  ioGood10 := ioCoinsD_good10 hfirstD
  interPoleHitGood10 :=
    interPoleOfE_good10 (distinctCensusExecution hfirstD) (ioCoinsD hfirstD).gamma (inputsD_interCard hfirstD)

theorem inputsD_challenges : (inputsD hfirstD).computeChallenges = default := rfl

theorem walkOrderMemD :
    2 ≤ (distinctCensusExecution hfirstD).cfg.memRows →
      (distinctCensusExecution hfirstD).cfg.memRows ≤ orderOf (inputsD hfirstD).memoryWalkAlpha := fun _ => by
  have hα : (inputsD hfirstD).memoryWalkAlpha = (3 : K97cubic) := rfl
  have hrows : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
  rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega3_order, hrows]
  norm_num

/-- H1.5b Part 2a `rowsBound` of this fixture: `3·3 < 97` and `21 < 97`. -/
theorem rowsBoundD :
    3 * (distinctCensusExecution hfirstD).cfg.compRows < ringChar K97cubic ∧
      (distinctCensusExecution hfirstD).cfg.memRows < ringChar K97cubic := by
  have h1 : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
  have h2 : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
  rw [h1, h2, DistinctCensusExecution.ringChar_K97]
  norm_num



theorem dc_leafIs : GeneratedField.LeafIs (K := K97cubic) 2 (.atom 0) (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10))))) 7 := by
  gen_simp

theorem dc_evalIsSome : (FieldEmbedding.evalGBy (ringChar K97cubic) 2 (.atom 0) (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10)))))).isSome := by
  eval_simp

/-- Program-level `generated` at any window `Λ ≥ 7`. -/
theorem dc_program_generated (Λ : ℕ) (hΛ : 7 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) gfuel (.atom 0) (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10))))) = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K97cubic) fuel (.atom 0) (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10))))) = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 2 2 (GeneratedField.le_of_leafIs dc_leafIs hΛ)
    dc_evalIsSome

/-- Negative control: zero margin (`Λ = 6` is refuted). -/
theorem dc_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) 2 (.atom 0) (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10))))) = .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 6 := by
  rintro ⟨G, R, hx, hle⟩
  have h := dc_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem residualD_claim :
    (residualD hfirstD).verifier.raw.claim.subject = (.atom 0) ∧
      (residualD hfirstD).verifier.raw.claim.formula = (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10))))) := by
  show (dataD hfirstD).skeleton.computeTree.label.subject = (.atom 0) ∧
    (dataD hfirstD).skeleton.computeTree.label.formula = (.cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9))) (.cell (.atom 1) (.cell (.atom 8) (.atom 10)))))
  simp [HonestCommitment.Data.skeleton, HonestCommitment.skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

/-- `generated` at `residualD hfirstD` (window `7`). -/
theorem residualD_generated :
    GeneratedField.ClaimGenerated K97cubic (residualD hfirstD).verifier.raw.claim (residualD hfirstD).Λ :=
  GeneratedField.claimGenerated_of_eq (residualD_claim hfirstD).1 (residualD_claim hfirstD).2
    (dc_program_generated _ (le_of_eq rfl))

/-- `primeField` at `F97`. -/
theorem f97_primeFieldD : GeneratedField.PrimeFieldElems F97 := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

/-- The constructed package over the distinct-pair `OP_5` execution.  Acceptance is **not** claimed:
the residual is residual-of-zero. -/
def packageD : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5 :=
  BuildablePackage.buildFullPackage (distinctCensusExecution hfirstD) (inputsD hfirstD) (residualD hfirstD)
    (inputsD_challenges hfirstD)
    DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (fun _ => by
      have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
      norm_num)
    (fun _ => by
      have hα : (inputsD hfirstD).memoryWalkAlpha = (3 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega3_order, hrows]
      norm_num)
    (rowsBoundD hfirstD) (residualD_generated hfirstD) f97_primeFieldD

theorem statementD
    (hax : FormRAxisBound (packageD hfirstD).optimized.sampled (packageD hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageD hfirstD) :=
  BuildablePackage.universalOptimizedFullStrictThm54 (distinctCensusExecution hfirstD) (inputsD hfirstD) (residualD hfirstD)
    (inputsD_challenges hfirstD) DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD) (by
      change 1 ≤ 1; trivial))
    (fun _ => by
      have hα : (inputsD hfirstD).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.compRows = 3 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega2_order, hrows]
      norm_num)
    (fun _ => by
      have hα : (inputsD hfirstD).memoryWalkAlpha = (3 : K97cubic) := rfl
      have hrows : (distinctCensusExecution hfirstD).cfg.memRows = 21 := rfl
      rw [hα, Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete.omega3_order, hrows]
      norm_num)
    (rowsBoundD hfirstD) (residualD_generated hfirstD) f97_primeFieldD
    hax hbasis hwidth

theorem statementD_nonvacuous
    (hax : FormRAxisBound (packageD hfirstD).optimized.sampled (packageD hfirstD).optimized.basis)
    (hbasis : FormRBasis (packageD hfirstD).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageD hfirstD)) :=
  ⟨statementD hfirstD hax hbasis hwidth⟩

/-- The constructed package's committed census still contains the genuinely distinct pair.  This
does not claim that any coin is accepted. -/
theorem residualD_has_distinct_pair :
    ∃ i : Fin (residualD hfirstD).census.census.count,
      (residualD hfirstD).census.census.pair i = (operandLeft, operandRight) ∧
        ((residualD hfirstD).census.census.pair i).1 ≠ ((residualD hfirstD).census.census.pair i).2 :=
  dataD_has_distinct_pair hfirstD

end

end Nock.NockVMROM.Thm54.DistinctCensusCommitment

#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.dataD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.censusD_has_distinct_pair
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.residualD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.combinedPairsD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.inputsD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.packageD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.statementD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCommitment.residualD_has_distinct_pair
