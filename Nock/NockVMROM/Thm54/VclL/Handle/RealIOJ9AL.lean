/-
  : `RealIOJ9A` is untouched.

  * `PubJ9AL` = `PubJ9A` + the ALU's row layout (`hL nL hnL nodesL orbitL`), the presence flag `aluOn`, the primitive
    table `prims : List (ℕ × PrimOp)` (id, op), the pin index `idxP`, the public rank `rkP` of each `primC op` and the verifier-fixed preprocessing `preL`
    (the `preg` layout `sP, pId, pOp`; `PregOK` in `AcceptsJ9AL` ties it to `prims`).
  * `MsgJ9AL'` = `MsgJ9A'` + `pubsL`; `TrJ9AL` = `TrJ9A` + `L : Fin 196 → F[X]` (the ALU trace, `aluSZ_width_eq`);
    `StJ9AL`: the ALU columns staged at their rounds (`crAL`: base `0..93` round 0, `𝕂′`-roles round 1 / round 2);
    `RowsJ9AL` = `RowsJ9A` + `AL`; `cornerC9L`; `BudJ9AL`.
  * Readout: `aluFpReqsOf` (the validity consumes `[z, 0, L, 0, sv]`, read off the ALU rows with `aV ≠ 0`, in `𝕂′`).
    No limb-read readout (SZ).  The validity consumes depend on the coin `z` and on the round-1 column `L`, so no
    `ReadsOnC` statement is made here.
  * Readouts (for `RR49AL`): `aluRegReqsOf` (`hdr` consumes `keyRg` + op record), `aluRegProvsOf`
    (`preg` provides, weight `sP·mP`), `aluJetProvsOf` (`keyJet`, weight `sH·mJ`), `aluExportReqsOf` (`keyX` on
    `hdr`); `lists_readsL`: along `StJ9AL` the four are constant in the coins (round-0 columns only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
import Nock.Jet.PrimJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. Types -/

/-- The op code of the ALU's op record (`AluSZChipJ9.opCode`: `add 1, sub 2, lt 3, mul 4, div 5, mod 6`); `dec` has
no ALU opcode (`0`: no `hdr` row can carry it, `sH·(Σ op − 1)`). -/
def primCode : PrimOp → ℕ
  | .add => 1 | .sub => 2 | .lt => 3 | .dec => 0 | .mul => 4 | .div => 5 | .mod => 6

/-- The ALU width (`aluSZ_width_eq`). -/
abbrev wAL : ℕ := 196

/-- **`PubJ9AL`**: `PubJ9A` plus the ALU's row layout, its presence flag, the primitive table `(id, op)`, the pin
index `idxP` (the cell-table index of `primC op`) and the verifier-fixed `preg` preprocessing `preL`
(`sP, pId, pOp`, as `AluSZChipJ9.preOf`). -/
structure PubJ9AL (p : ℕ) [Fact p.Prime] extends PubJ9A p where
  hL : ℕ
  nL : ℕ
  hnL : 0 < nL
  nodesL : Fin nL → ZMod p
  orbitL : StrictOrbitDomain (ZMod p) 3 hL
  aluOn : Bool
  prims : List (ℕ × PrimOp)
  idxP : ℕ → ℕ
  /-- The public rank limbs `(hi, lo)` of each primitive's formula noun `primC op` (the twin of `PubJ8.rk`):
  the cell-side pin `pinRecsP` carries `(encJ8 (primC op), rkP id, idxP id)`. -/
  rkP : ℕ → ℕ × ℕ
  preL : Fin 3 → (ZMod p)[X]

/-- **`MsgJ9AL'`**: `MsgJ9A'` plus the ALU's publics (`pubALv / pubALs / pubALx`, each `+ 1`). -/
structure MsgJ9AL' (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    extends MsgJ9A' p K δ where
  pubsL : ℕ → K

/-- ALU columns by round: base `0..93` round 0; the `𝕂′` roles are `3`-column groups, round 1 = `94..147`
(`H … RO`), round 2 = `148..195` (`invV … accX`). -/
def crAL (j : Fin wAL) : ℕ := if (j : ℕ) < 94 then 0 else if (j : ℕ) < 148 then 1 else 2

/-- **`TrJ9AL`**: the nine chip traces. -/
structure TrJ9AL (F : Type) [Field F] extends TrJ9A F where
  L : Fin wAL → F[X]

/-- **`StJ9AL`**: every column of every chip is staged at its round. -/
def StJ9AL {F K : Type} [Field F] (Q : Coins frameJ8 K → TrJ9AL F) : Prop :=
  StJ9A (fun χ => (Q χ).toTrJ9A) ∧ StagedCols frameJ8 crAL (fun χ => (Q χ).L)

/-- **`RowsJ9AL`** = `RowsJ9A` + the ALU row parameter. -/
structure RowsJ9AL extends RowsJ9A where
  AL : ℕ

/-- **The census corner of J-9 AL**: the J-9 A corner plus `AL = 2^31`. -/
def cornerC9L : RowsJ9AL := { toRowsJ9A := cornerC9, AL := 2 ^ 31 }

/-! ## 2. The ALU view -/

section Views
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p))

/-- The ALU chip view (width `196`). -/
def qAL (chals pubs : ℕ → K) :
    Fin (AluSZChipJ9.aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL).rap.w → (ZMod p)[X] :=
  fun j => tr.L (Fin.cast (AluSZChipJ9.aluSZ_width_eq δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL) j)

end Views

/-! ## 3. The budget -/

section Bud
variable {p : ℕ} [Fact p.Prime]
open Nock.Jet.ChipJ8 (ents0T ents1T ents2T ents3 entsX)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)

/-- **`BudJ9AL`** = `BudJ9A` with the ALU rows charged (`AL` rows, each: one export read (`x1`), at most two service
consumes (`s1`: `keyRg`, op record on a `hdr`) and at most two service provides (`s2`: `keyRg`, op record on a
`preg`, or one `keyJet` on a `hdr`)). -/
structure BudJ9AL (Pb : PubJ9AL p) (r : RowsJ9AL) (g : ℕ) : Prop where
  x1 : 3 * Pb.n + Pb.nW + jCount entsX Pb.lay + Pb.nL ≤ 3 * r.N + r.W + r.rd + r.AL
  x2 : Pb.nC ≤ r.D
  p1 : Pb.n + Pb.nX ≤ r.N
  p2 : Pb.nW ≤ r.W
  s1 : 2 * Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) + Pb.nX + 2 * Pb.nL ≤
    r.N + 2 * r.J + g + r.AX + 2 * r.AL
  s2 : jCount ents2T Pb.lay + jCount ents3 Pb.lay + Pb.nA + 2 * Pb.nV + Pb.nX + 2 * Pb.nS + 2 * Pb.nL ≤
    r.calls + r.heads + r.blocks + r.J + r.AX + 2 * r.SP + 2 * r.AL

end Bud

/-! ## 4. The validity readout -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- Row `i`'s base environment on the ALU chip. -/
abbrev alEF {n : ℕ} (nodes : Fin n → ZMod p) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) {w : ℕ} (Q' : Fin w → (ZMod p)[X]) (i : Fin n) : Env (ZMod p) :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 94 chals) (slotVal b 94 pubs)

/-- Row `i`'s gathered `𝕂` environment on the ALU chip. -/
abbrev alEK {n : ℕ} (nodes : Fin n → ZMod p) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) {w : ℕ} (Q' : Fin w → (ZMod p)[X]) (i : Fin n) : Env K :=
  gatherEnv b ((AluSZChipJ9.aluTemplateSZ δ).col0 3) (alEF b nodes orbit chals pubs Q' i)

/-- **The ALU validity consumes** (`qRead`): the key `[z, 0, L, 0, sv]` (`AluSZChipJ9.valKey`, evaluated in `𝕂′`)
on every ALU row with activity `aV ≠ 0` (`aV = fst·(mR + mV)`).  `chals` = the ALU challenge vector
(`chalsALJ8`: `z` at leaves `37 / 38`). -/
def aluFpReqsOf [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) (chals : ℕ → K) :
    List (Fin 5 → Quad (algebraMap (ZMod p) K δ)) :=
  (List.finRange Pb.nL).flatMap fun i =>
    if (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i).trace
        AluSZChipJ9.aV = 0 then [] else
      [fun c => ((AluSZChipJ9.valKey (F := ZMod p)).getD c QE.zero).ev δ
        (alEK δ b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i)
        (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i)]

end Lists

/-! ## 5. The service, jet and export readouts: round-0 columns only (for `RR49AL`)

The pattern of `RealIOJ9A.axTagProvsOf` / `lists_reads`: each list is read off the ALU rows at chals and publics
`0` (coin-free), filtered on its activity, and depends on round-0 columns only (`lists_readsL`).  The service
balance's per-row term `wS·(invR + invO) − sH·mJ·invJ` (`AluSZChipJ9.logupQ`, `wS = sH − sP·mP`) splits linearly into
the `hdr` consumes (`aluRegReqsOf`: `keyRg` and the op record, activity `sH`), the `preg` provides
(`aluRegProvsOf`: the same two keys, weight `sP·mP`) and the jet provides (`aluJetProvsOf`: `keyJet`, weight
`sH·mJ`); the export consumes `keyX` on `hdr` rows (`aluExportReqsOf`, activity `sH`). -/

section Svc
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- Row `i`'s coin-free base environment on the ALU chip (chals and publics `0`). -/
abbrev alE0 (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) (i : Fin Pb.nL) : Env (ZMod p) :=
  alEF b Pb.nodesL Pb.orbitL (fun _ => (0 : K)) (fun _ => (0 : K))
    (qAL δ b Pb tr (fun _ => (0 : K)) (fun _ => (0 : K))) i

/-- **The `hdr` service consumes**: `keyRg (idc, kc, vc, 0,0,0,0, 7)` (tag last) and the op record `(idc, opc, 0,0,0,0,0, 6)` on every
row with `sH ≠ 0`. -/
def aluRegReqsOf [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (Fin 8 → K) :=
  (List.finRange Pb.nL).flatMap fun i =>
    if (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sH = 0 then [] else
      [AxisChipJ9.keyVecL 8 AluSZChipJ9.keyRgE (alE0 (K := K) δ b Pb tr i),
        AxisChipJ9.keyVecL 8 AluSZChipJ9.opRecE (alE0 (K := K) δ b Pb tr i)]

/-- **The `preg` service provides**: `keyRg` and the op record, weight `sP·mP`, on every row where it is `≠ 0`. -/
def aluRegProvsOf [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List ((Fin 8 → K) × K) :=
  (List.finRange Pb.nL).flatMap fun i =>
    if (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sP * (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.mP = 0
    then [] else
      [(AxisChipJ9.keyVecL 8 AluSZChipJ9.keyRgE (alE0 (K := K) δ b Pb tr i),
          algebraMap (ZMod p) K ((alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sP *
            (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.mP)),
        (AxisChipJ9.keyVecL 8 AluSZChipJ9.opRecE (alE0 (K := K) δ b Pb tr i),
          algebraMap (ZMod p) K ((alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sP *
            (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.mP))]

/-- **The jet provides**: `keyJet (idc, kc, vc, kS, vS, kE, vE, 3)`, weight `sH·mJ`, on every row where it is
`≠ 0`. -/
def aluJetProvsOf [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List ((Fin 8 → K) × K) :=
  (List.finRange Pb.nL).flatMap fun i =>
    if (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sH * (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.mJ = 0
    then [] else
      [(AxisChipJ9.keyVecL 8 AluSZChipJ9.keyJetE (alE0 (K := K) δ b Pb tr i),
          algebraMap (ZMod p) K ((alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sH *
            (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.mJ))]

/-- **The export consumes**: `keyX (vS, kA, vA, kB, vB)` on every row with `sH ≠ 0`. -/
def aluExportReqsOf [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p)) : List (Fin 5 → K) :=
  (List.finRange Pb.nL).flatMap fun i =>
    if (alE0 (K := K) δ b Pb tr i).trace AluSZChipJ9.sH = 0 then [] else
      [AxisChipJ9.keyVecL 5 AluSZChipJ9.keyXE (alE0 (K := K) δ b Pb tr i)]

/-- Two ALU traces agreeing on the round-0 columns give the same coin-free row environments there. -/
theorem alTrace_congr (Pb : PubJ9AL p) {tr tr' : TrJ9AL (ZMod p)}
    (h : ∀ j : Fin wAL, crAL j = 0 → tr.L j = tr'.L j) (i : Fin Pb.nL) (j : ℕ) (hj : j < 94) :
    (alE0 (K := K) δ b Pb tr i).trace j = (alE0 (K := K) δ b Pb tr' i).trace j := by
  simp only [alE0, alEF, Reify.envOfTrace, qAL]
  split_ifs with hw
  · rw [h _ (by simp [crAL, hj])]
  · rfl

theorem aluRegReqsOf_congr [DecidableEq (ZMod p)] (Pb : PubJ9AL p) {tr tr' : TrJ9AL (ZMod p)}
    (h : ∀ j : Fin wAL, crAL j = 0 → tr.L j = tr'.L j) :
    aluRegReqsOf δ b Pb tr = aluRegReqsOf (K := K) δ b Pb tr' := by
  unfold aluRegReqsOf
  refine List.flatMap_congr fun i _ => ?_
  have ht := alTrace_congr (K := K) δ b Pb h i
  rw [ht _ (by decide : AluSZChipJ9.sH < 94)]
  split_ifs
  · rfl
  · simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩
    · funext c
      fin_cases c <;>
        simp [AxisChipJ9.keyVecL, AluSZChipJ9.keyRgE, AluSZChipJ9.keyRgRE, AluSZChipJ9.reE, CoeffExpr.eval,
          Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.idc < 94),
          ht _ (by decide : AluSZChipJ9.kc < 94), ht _ (by decide : AluSZChipJ9.vc < 94)]
    · funext c
      fin_cases c <;>
        simp [AxisChipJ9.keyVecL, AluSZChipJ9.opRecE, AluSZChipJ9.opRecRE, AluSZChipJ9.reE, CoeffExpr.eval,
          Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.idc < 94),
          ht _ (by decide : AluSZChipJ9.opc < 94)]

theorem aluRegProvsOf_congr [DecidableEq (ZMod p)] (Pb : PubJ9AL p) {tr tr' : TrJ9AL (ZMod p)}
    (h : ∀ j : Fin wAL, crAL j = 0 → tr.L j = tr'.L j) :
    aluRegProvsOf δ b Pb tr = aluRegProvsOf (K := K) δ b Pb tr' := by
  unfold aluRegProvsOf
  refine List.flatMap_congr fun i _ => ?_
  have ht := alTrace_congr (K := K) δ b Pb h i
  rw [ht _ (by decide : AluSZChipJ9.sP < 94), ht _ (by decide : AluSZChipJ9.mP < 94)]
  split_ifs
  · rfl
  · simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    refine ⟨?_, ?_⟩
    · funext c
      fin_cases c <;>
        simp [AxisChipJ9.keyVecL, AluSZChipJ9.keyRgE, AluSZChipJ9.keyRgRE, AluSZChipJ9.reE, CoeffExpr.eval,
          Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.idc < 94),
          ht _ (by decide : AluSZChipJ9.kc < 94), ht _ (by decide : AluSZChipJ9.vc < 94)]
    · funext c
      fin_cases c <;>
        simp [AxisChipJ9.keyVecL, AluSZChipJ9.opRecE, AluSZChipJ9.opRecRE, AluSZChipJ9.reE, CoeffExpr.eval,
          Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.idc < 94),
          ht _ (by decide : AluSZChipJ9.opc < 94)]

theorem aluJetProvsOf_congr [DecidableEq (ZMod p)] (Pb : PubJ9AL p) {tr tr' : TrJ9AL (ZMod p)}
    (h : ∀ j : Fin wAL, crAL j = 0 → tr.L j = tr'.L j) :
    aluJetProvsOf δ b Pb tr = aluJetProvsOf (K := K) δ b Pb tr' := by
  unfold aluJetProvsOf
  refine List.flatMap_congr fun i _ => ?_
  have ht := alTrace_congr (K := K) δ b Pb h i
  rw [ht _ (by decide : AluSZChipJ9.sH < 94), ht _ (by decide : AluSZChipJ9.mJ < 94)]
  split_ifs
  · rfl
  · refine List.singleton_inj.mpr (Prod.ext ?_ rfl)
    funext c
    fin_cases c <;>
      simp [AxisChipJ9.keyVecL, AluSZChipJ9.keyJetE, AluSZChipJ9.keyJetRE, AluSZChipJ9.reE, CoeffExpr.eval,
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.idc < 94),
        ht _ (by decide : AluSZChipJ9.kc < 94), ht _ (by decide : AluSZChipJ9.vc < 94),
        ht _ (by decide : AluSZChipJ9.kS < 94), ht _ (by decide : AluSZChipJ9.vS < 94),
        ht _ (by decide : AluSZChipJ9.kE < 94), ht _ (by decide : AluSZChipJ9.vE < 94)]

theorem aluExportReqsOf_congr [DecidableEq (ZMod p)] (Pb : PubJ9AL p) {tr tr' : TrJ9AL (ZMod p)}
    (h : ∀ j : Fin wAL, crAL j = 0 → tr.L j = tr'.L j) :
    aluExportReqsOf δ b Pb tr = aluExportReqsOf (K := K) δ b Pb tr' := by
  unfold aluExportReqsOf
  refine List.flatMap_congr fun i _ => ?_
  have ht := alTrace_congr (K := K) δ b Pb h i
  rw [ht _ (by decide : AluSZChipJ9.sH < 94)]
  split_ifs
  · rfl
  · refine List.singleton_inj.mpr ?_
    funext c
    fin_cases c <;>
      simp [AxisChipJ9.keyVecL, AluSZChipJ9.keyXE, AluSZChipJ9.keyXRE, AluSZChipJ9.reE, CoeffExpr.eval,
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, ht _ (by decide : AluSZChipJ9.vS < 94),
        ht _ (by decide : AluSZChipJ9.kA < 94), ht _ (by decide : AluSZChipJ9.vA < 94),
        ht _ (by decide : AluSZChipJ9.kB < 94), ht _ (by decide : AluSZChipJ9.vB < 94)]

/-- **Along `StJ9AL` the four ALU service / jet / export lists are constant in the coins** (`ReadsOnC frameJ8 ∅`):
round-0 columns only.  (The validity list `aluFpReqsOf` is NOT: it reads `z` and the round-1 column `L`.) -/
theorem lists_readsL [DecidableEq (ZMod p)] (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)}
    (hQ : StJ9AL Q) :
    ReadsOnC frameJ8 ∅ (fun χ => aluRegReqsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluRegProvsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluJetProvsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluExportReqsOf δ b Pb (Q χ)) := by
  have hL : ∀ χ χ' : Coins frameJ8 K, ∀ j : Fin wAL, crAL j = 0 → (Q χ).L j = (Q χ').L j :=
    fun χ χ' j hj => Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.staged_eq hQ.2 (r := 0)
      (fun i hi => absurd hi (by omega)) j hj.le
  exact ⟨fun χ χ' _ => aluRegReqsOf_congr δ b Pb (hL χ χ'), fun χ χ' _ => aluRegProvsOf_congr δ b Pb (hL χ χ'),
    fun χ χ' _ => aluJetProvsOf_congr δ b Pb (hL χ χ'), fun χ χ' _ => aluExportReqsOf_congr δ b Pb (hL χ χ')⟩

end Svc

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
#print axioms qAL
#print axioms aluFpReqsOf
#print axioms cornerC9L
#print axioms lists_readsL
#print axioms aluRegReqsOf
end Axioms
