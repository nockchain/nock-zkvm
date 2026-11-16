/-
  Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ9A.lean

* `PubJ9A` = `PubJ8` + `nX nS hnX hnS nodesX nodesS orbitX orbitS axOn spOn` (+ the heights `hX hS`);
    `MsgJ9A'` = `MsgJ8'` + `pubsX pubsS`; `TrJ9A` = the J-8 traces with `C : Fin 137` (the twin compute RAP's
    column order, `ChipHX9RAP.permX9`: round 0 = `0..82`, round 1 = `83..136`) + `X : Fin 52` + `S : Fin 90`;
    `TrJ9A.toJ8` is the old-column projection (the J-8 `C : Fin 123` read through `permX9`), so the J-8 views
    `qM qW qJ qA qV` apply verbatim to `tr.toJ8`.  `StJ9A`: every column staged at its round (`crC9`, `crAX`,
    `crSP`).  `RowsJ9A` = `RowsJ8` + `AX SP`; `cornerC9`.  `BudJ9A`.
  * The readouts: the axis limb / path consumes, the `TAG_ax` provides and the split provides read off the trace;
    along `StJ9A` each is constant (`ReadsOnC frameJ8 ∅`), i.e. reads round-0 columns only.  No new coin class:
    both chips take the handle coins through `chalsMJ8` (leaves `33..36`, `HQ.gamQ / rhoQ`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA staged_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (permX9 widthHX9 computeChipVCLHX9)

noncomputable section

/-! ## 1. Types -/

/-- **`PubJ9A`**: the J-8 public parameters plus the axis chip's and the split chip's row layouts and the two
presence flags (R8: absence is a public flag; `nX = 0` is uninhabited). -/
structure PubJ9A (p : ℕ) [Fact p.Prime] extends PubJ8 p where
  hX : ℕ
  nX : ℕ
  hnX : 0 < nX
  nodesX : Fin nX → ZMod p
  orbitX : StrictOrbitDomain (ZMod p) 3 hX
  hS : ℕ
  nS : ℕ
  hnS : 0 < nS
  nodesS : Fin nS → ZMod p
  orbitS : StrictOrbitDomain (ZMod p) 3 hS
  axOn : Bool
  spOn : Bool

/-- **`MsgJ9A'`**: `MsgJ8'` plus the two new chips' publics. -/
structure MsgJ9A' (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    extends MsgJ8' p K δ where
  pubsX : ℕ → K
  pubsS : ℕ → K

/-- Compute (twin RAP, `137`): round 0 = columns `0..82`, round 1 = `83..136`. -/
def crC9 (j : Fin 137) : ℕ := if (j : ℕ) < 83 then 0 else 1
/-- Axis chip (`22` base columns, round 0; the `𝕂`-roles after). -/
def crAX (j : Fin 52) : ℕ := if (j : ℕ) < 22 then 0 else 2
/-- Split chip (`72` base columns, round 0; the `𝕂`-roles after). -/
def crSP (j : Fin 90) : ℕ := if (j : ℕ) < 72 then 0 else 2

/-- **`TrJ9A`**: the eight chip traces; `C` is the twin compute RAP's trace in RAP column order. -/
structure TrJ9A (F : Type) [Field F] where
  C : Fin 137 → F[X]
  M : Fin 242 → F[X]
  W : Fin 166 → F[X]
  J : Fin 71 → F[X]
  A : Fin 349 → F[X]
  V : Fin 166 → F[X]
  X : Fin 52 → F[X]
  S : Fin 90 → F[X]

/-- The twin's old columns `0..122` in RAP column order (`permX9`). -/
def oldCol (j : Fin 123) : Fin 137 := ⟨permX9 (j : ℕ), by have := j.isLt; simp only [permX9, widthHX9] at *; split_ifs <;> omega⟩

/-- **The J-8 projection of a J-9 A trace** (the compute columns `0..122` read through `permX9`). -/
def TrJ9A.toJ8 {F : Type} [Field F] (tr : TrJ9A F) : TrJ8 F where
  C := fun j => tr.C (oldCol j)
  M := tr.M
  W := tr.W
  J := tr.J
  A := tr.A
  V := tr.V

/-- **`StJ9A`**: every column of every chip is staged at its round. -/
def StJ9A {F K : Type} [Field F] (Q : Coins frameJ8 K → TrJ9A F) : Prop :=
  StagedCols frameJ8 crC9 (fun χ => (Q χ).C) ∧ StagedCols frameJ8 crM (fun χ => (Q χ).M) ∧
    StagedCols frameJ8 crW (fun χ => (Q χ).W) ∧ StagedCols frameJ8 crJ (fun χ => (Q χ).J) ∧
    StagedCols frameJ8 crA (fun χ => (Q χ).A) ∧ StagedCols frameJ8 crW (fun χ => (Q χ).V) ∧
    StagedCols frameJ8 crAX (fun χ => (Q χ).X) ∧ StagedCols frameJ8 crSP (fun χ => (Q χ).S)

/-- **`RowsJ9A`** = `RowsJ8` + the axis and split row parameters. -/
structure RowsJ9A extends RowsJ8 where
  AX : ℕ
  SP : ℕ

/-- **The census corner of J-9 A**: the J-8 corner plus `AX = SP = 2^31`. -/
def cornerC9 : RowsJ9A := { toRowsJ8 := EncInjJ8.cornerC, AX := 2 ^ 31, SP := 2 ^ 31 }


/-! ## 3. The chip views -/

section Views
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p))

/-- The twin compute view (width `137`, the RAP column order). -/
def qX9 (chalV pubVal : ℕ → ZMod p) :
    Fin (computeChipVCLHX9 Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit).rap.w → (ZMod p)[X] := tr.C

/-- The axis chip view (width `52`). -/
def qAX (chals pubs : ℕ → K) :
    Fin (AxisChipJ9.axisChipJ9 δ b Pb.hnX Pb.nodesX Pb.orbitX chals pubs).rap.w → (ZMod p)[X] :=
  fun j => tr.X (Fin.cast (AxisChipJ9.width_eq δ b Pb.hnX Pb.nodesX Pb.orbitX chals pubs) j)

/-- The split chip view (width `90`; `nA = Pb.nA` is the verifier's template parameter). -/
def qSP (chals pubs : ℕ → K) :
    Fin (SplitChipJ9.splitChipJ9 δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS chals pubs).rap.w → (ZMod p)[X] :=
  fun j => tr.S (Fin.cast (SplitChipJ9.width_eq δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS chals pubs) j)

end Views

/-! ## 2. The budget -/

section Bud
open Nock.Jet.ChipJ8 (ents0T ents1T ents2T ents3 entsX)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
variable {p : ℕ} [Fact p.Prime]

/-- **`BudJ9A`** = `BudJ8` with `p1`, `s1`, `s2` changed: the axis rows are charged to
`N` (`p1`), to the service consumers (`s1`) and, with the split provides (two per row), to the providers (`s2`). -/
structure BudJ9A (Pb : PubJ9A p) (r : RowsJ9A) (g : ℕ) : Prop where
  x1 : 3 * Pb.n + Pb.nW + jCount entsX Pb.lay ≤ 3 * r.N + r.W + r.rd
  x2 : Pb.nC ≤ r.D
  p1 : Pb.n + Pb.nX ≤ r.N
  p2 : Pb.nW ≤ r.W
  s1 : 2 * Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) + Pb.nX ≤
    r.N + 2 * r.J + g + r.AX
  s2 : jCount ents2T Pb.lay + jCount ents3 Pb.lay + Pb.nA + 2 * Pb.nV + Pb.nX + 2 * Pb.nS ≤
    r.calls + r.heads + r.blocks + r.J + r.AX + 2 * r.SP

end Bud


/-! ## 4. The readouts of the new record lists: round-0 columns only -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (b : Basis (Fin 3) (ZMod p) K)

/-- The axis limb consumes read off the trace (coin-free: chals and publics `0`; no list reads either). -/
def axLimbReqsOf (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : List (Fin 8 → K) :=
  AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (fun _ => 0) (fun _ => 0) tr.X

/-- The axis path consumes (activity `1 − z1a ≠ 0`). -/
def axPathReqsOf (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : List (Fin 5 → K) :=
  AxisChipJ9.axPathReqs b Pb.nodesX Pb.orbitX (fun _ => 0) (fun _ => 0) tr.X

/-- The `TAG_ax` provides (activity `mu ≠ 0`). -/
def axTagProvsOf (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : List ((Fin 8 → K) × K) :=
  AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (fun _ => 0) (fun _ => 0) tr.X

/-- The split limb provides (activity `m ≠ 0`, two records per row). -/
def splitProvsOf (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : List ((Fin 8 → K) × K) :=
  SplitChipJ9.splitProvs b Pb.nodesS Pb.orbitS (fun _ => 0) (fun _ => 0) tr.S

/-- Two axis traces agreeing on the round-0 columns. -/
theorem axTrace_congr (Pb : PubJ9A p) {Q1 Q2 : Fin 52 → (ZMod p)[X]}
    (h : ∀ j : Fin 52, crAX j = 0 → Q1 j = Q2 j) (i : Fin Pb.nX) (j : ℕ) (hj : j < 22) :
    (AxisChipJ9.axEF b Pb.nodesX Pb.orbitX (fun _ => (0 : K)) (fun _ => (0 : K)) Q1 i).trace j =
      (AxisChipJ9.axEF b Pb.nodesX Pb.orbitX (fun _ => (0 : K)) (fun _ => (0 : K)) Q2 i).trace j := by
  have hj' : j < 52 := by omega
  simp only [AxisChipJ9.axEF, Reify.envOfTrace, dif_pos hj']
  rw [h ⟨j, hj'⟩ (by simp [crAX, hj])]

theorem spTrace_congr (Pb : PubJ9A p) {Q1 Q2 : Fin 90 → (ZMod p)[X]}
    (h : ∀ j : Fin 90, crSP j = 0 → Q1 j = Q2 j) (i : Fin Pb.nS) (j : ℕ) (hj : j < 72) :
    (SplitChipJ9.spEF b Pb.nodesS Pb.orbitS (fun _ => (0 : K)) (fun _ => (0 : K)) Q1 i).trace j =
      (SplitChipJ9.spEF b Pb.nodesS Pb.orbitS (fun _ => (0 : K)) (fun _ => (0 : K)) Q2 i).trace j := by
  have hj' : j < 90 := by omega
  simp only [SplitChipJ9.spEF, Reify.envOfTrace, dif_pos hj']
  rw [h ⟨j, hj'⟩ (by simp [crSP, hj])]

theorem axLimbReqsOf_congr (Pb : PubJ9A p) {tr tr' : TrJ9A (ZMod p)}
    (h : ∀ j : Fin 52, crAX j = 0 → tr.X j = tr'.X j) :
    axLimbReqsOf b Pb tr = axLimbReqsOf (K := K) b Pb tr' := by
  unfold axLimbReqsOf AxisChipJ9.axLimbReqs
  refine List.map_congr_left fun i _ => ?_
  have ht := axTrace_congr (K := K) b Pb h i
  funext c
  fin_cases c <;>
    simp [AxisChipJ9.keyVecL, AxisChipJ9.limbKey, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AxisChipJ9.R < 22),
      ht _ (by decide : AxisChipJ9.axK < 22), ht _ (by decide : AxisChipJ9.l < 22)]


theorem axPathReqsOf_congr (Pb : PubJ9A p) [DecidableEq (ZMod p)] {tr tr' : TrJ9A (ZMod p)}
    (h : ∀ j : Fin 52, crAX j = 0 → tr.X j = tr'.X j) :
    axPathReqsOf b Pb tr = axPathReqsOf (K := K) b Pb tr' := by
  unfold axPathReqsOf AxisChipJ9.axPathReqs
  refine List.flatMap_congr fun i _ => ?_
  have ht := axTrace_congr (K := K) b Pb h i
  have hz := ht _ (by decide : AxisChipJ9.z1a < 22)
  rw [hz]
  split_ifs
  · rfl
  · congr 1
    funext c
    fin_cases c <;>
      simp [AxisChipJ9.keyVecL, AxisChipJ9.pathKey, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv,
        ht _ (by decide : AxisChipJ9.hinv < 22), ht _ (by decide : AxisChipJ9.axS < 22),
        ht _ (by decide : AxisChipJ9.houtk < 22), ht _ (by decide : AxisChipJ9.houtv < 22)]

theorem axTagProvsOf_congr (Pb : PubJ9A p) [DecidableEq (ZMod p)] {tr tr' : TrJ9A (ZMod p)}
    (h : ∀ j : Fin 52, crAX j = 0 → tr.X j = tr'.X j) :
    axTagProvsOf b Pb tr = axTagProvsOf (K := K) b Pb tr' := by
  unfold axTagProvsOf AxisChipJ9.axTagProvs
  refine List.flatMap_congr fun i _ => ?_
  have ht := axTrace_congr (K := K) b Pb h i
  have hz := ht _ (by decide : AxisChipJ9.mu < 22)
  rw [hz]
  split_ifs
  · rfl
  · refine List.singleton_inj.mpr (Prod.ext ?_ ?_)
    · funext c
      fin_cases c <;>
        simp [AxisChipJ9.keyVecL, AxisChipJ9.tagKey, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv,
          ht _ (by decide : AxisChipJ9.hrv < 22), ht _ (by decide : AxisChipJ9.ftk < 22),
          ht _ (by decide : AxisChipJ9.ftv < 22), ht _ (by decide : AxisChipJ9.houtk < 22),
          ht _ (by decide : AxisChipJ9.houtv < 22), ht _ (by decide : AxisChipJ9.R < 22)]
    · rfl

theorem splitProvsOf_congr (Pb : PubJ9A p) [DecidableEq (ZMod p)] {tr tr' : TrJ9A (ZMod p)}
    (h : ∀ j : Fin 90, crSP j = 0 → tr.S j = tr'.S j) :
    splitProvsOf b Pb tr = splitProvsOf (K := K) b Pb tr' := by
  unfold splitProvsOf SplitChipJ9.splitProvs
  refine List.flatMap_congr fun i _ => ?_
  have ht := spTrace_congr (K := K) b Pb h i
  have hz := ht _ (by decide : SplitChipJ9.mult < 72)
  rw [hz]
  split_ifs
  · rfl
  · simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    refine ⟨?_, ?_⟩
    · funext c
      fin_cases c <;>
        simp [SplitChipJ9.keyVecL, SplitChipJ9.key2, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv,
          ht _ (by decide : SplitChipJ9.sid < 72), ht _ (by decide : SplitChipJ9.lo < 72)]
    · funext c
      fin_cases c <;>
        simp [SplitChipJ9.keyVecL, SplitChipJ9.key3, CoeffExpr.eval, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv,
          ht _ (by decide : SplitChipJ9.sid < 72), ht _ (by decide : SplitChipJ9.hi < 72)]

/-- **Along `StJ9A` the four new lists are constant in the coins** (`ReadsOnC frameJ8 ∅`): round-0 columns only.
No new coin class. -/
theorem lists_reads [DecidableEq (ZMod p)] (Pb : PubJ9A p) {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q) :
    ReadsOnC frameJ8 ∅ (fun χ => axLimbReqsOf b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => axPathReqsOf b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => axTagProvsOf b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => splitProvsOf b Pb (Q χ)) := by
  have hX : ∀ χ χ' : Coins frameJ8 K, ∀ j : Fin 52, crAX j = 0 → (Q χ).X j = (Q χ').X j :=
    fun χ χ' j hj => staged_eq hQ.2.2.2.2.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  have hS : ∀ χ χ' : Coins frameJ8 K, ∀ j : Fin 90, crSP j = 0 → (Q χ).S j = (Q χ').S j :=
    fun χ χ' j hj => staged_eq hQ.2.2.2.2.2.2.2 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  exact ⟨fun χ χ' _ => axLimbReqsOf_congr b Pb (hX χ χ'), fun χ χ' _ => axPathReqsOf_congr b Pb (hX χ χ'),
    fun χ χ' _ => axTagProvsOf_congr b Pb (hX χ χ'), fun χ χ' _ => splitProvsOf_congr b Pb (hS χ χ')⟩

end Lists

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
#print axioms lists_reads
#print axioms axLimbReqsOf_congr
end Axioms
