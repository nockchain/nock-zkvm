/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatRows.lean

  **The honest ALU table satisfies every base
  gate and every `identQ` equation row by row (the row model, no polynomials).**

  * §1 read sets: `rdB` (base expressions), `rdM` (mixed expressions; coins free, publics forbidden) and their
    congruence lemmas; `baseGates_rd` (base gates read current columns `1..93`, next columns `2..93`: never
    `isFT`, never the next row's `isLT`) and `identQ_rd` (the `identQ` equations read `𝕂`-roles `< 18`, the same
    base columns, coins, no public).
  * §2 the row model: `RowB` (every base gate at a row against its successor), `RowQ` (every `identQ` equation),
    `Row2` (both, the successor's `𝕂′` row read by `kvec`), `TailP` (a row is good against every successor with
    `sL = 0`, `fst = 0`).  Quiet rows (preg, padding) satisfy `TailP` (`quiet2`); a block satisfies the chain
    and `TailP` at its last row from the block obligations `BlockBaseSat` / `BlockIdentSat` (`block_chain`).
  * §3 the honest table `tblP` = preg rows, the blocks (base rows zipped with the `𝕂′` rows at `y`), one padding
    row; `tblP_chain`: `List.IsChain Row2`, from `hblk` (the block obligations per call, a HYPOTHESIS until the
    four gate groups are merged) and `hpreg` (every preg row is a `pregRow`).
  * §4 `ofColB` / `ofKQ` (a base / `𝕂′` row reading arbitrary column values), `padLT` (the padding row with the
    last-row mask `isLT = 1`), `row_transfer` (a `Row2` fact gives the gates at any environment agreeing on the read
    sets).
  * §5 the honest trace `polyAL`: Lagrange interpolants of `colAL` (the table's base columns, the round-1 `𝕂′` roles
    by `kvec`, the round-2 roles `r2`), the preprocessing `pre` at columns `2..4`, and the `sL` column corrected by
    `AluTraceFix.fixAt` to vanish at the last node's successor; `aluRows_honest`: every base gate and every `identQ`
    equation at every row (the last row is `padLT` against a successor with `sL = 0`).
  * §6–§9 the LogUp lane: the key read sets (`RdQ`, `den_trace`), the denominators `dV dR dO dJ dX` and row terms
    `tV tS tX` from the table and the coins, the inverses and inclusive prefix sums `r2AL`; `logup_honest`.
  * §10 `aluSZChipJ9_honest_sat`: the honest trace satisfies `aluSZChipJ9` and binds its five preprocessing columns,
    from the table facts, `hpre`, `hden` (no ACTIVE denominator vanishes: the completeness bad events) and the three
    terminal publics; `aluSZChipJ9_honest_sat_tblP` at the honest table, with `hblk` as the hypothesis.

  Caveat (route F′, disclosed): the overlay's base data still puts primitive calls' J nouns into the cell table; `Rt`
  at primitive ids is the one fixed trivial template `trivTpl`, so prim calls leave one constant cell.  This module
  does not touch the cell side.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestTable
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluTraceFix
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemQ
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)

noncomputable section

/-! ## 1. Read sets and congruence -/

section Congr
variable {F : Type} [Field F]

/-- A base expression reads current columns in `pc`, next columns in `pn`; no coin, no public. -/
def rdB (pc pn : ℕ → Bool) : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur i => pc i
  | .var .traceNext i => pn i
  | .var .challenge _ => false
  | .var .publicVal _ => false
  | .add a b => rdB pc pn a && rdB pc pn b
  | .sub a b => rdB pc pn a && rdB pc pn b
  | .mul a b => rdB pc pn a && rdB pc pn b
  | .neg a => rdB pc pn a
  | .pow a _ => rdB pc pn a

theorem rdB_eval {pc pn : ℕ → Bool} {g : CoeffExpr F} (hg : rdB pc pn g = true) {e e' : Env F}
    (ht : ∀ j, pc j = true → e.trace j = e'.trace j) (hn : ∀ j, pn j = true → e.traceNext j = e'.traceNext j) :
    g.eval e = g.eval e' := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k <;> simp only [rdB, Bool.false_eq_true] at hg <;> simp only [CoeffExpr.eval]
    · exact ht i hg
    · exact hn i hg
  | add a b iha ihb =>
    simp only [rdB, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdB, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdB, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | neg a iha =>
    simp only [rdB] at hg
    simp only [CoeffExpr.eval, iha hg]
  | pow a m iha =>
    simp only [rdB] at hg
    simp only [CoeffExpr.eval, iha hg]

theorem rdB_sumList {ι : Type} (pc pn : ℕ → Bool) (l : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ l, rdB pc pn (f i) = true) : rdB pc pn (CoeffExpr.sumList l f) = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [CoeffExpr.sumList, List.foldr_cons] at ih ⊢
    simp only [rdB, Bool.and_eq_true]
    exact ⟨h a List.mem_cons_self, ih fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

/-- A mixed expression reads `𝕂`-roles in `kc` / `kn`, base columns by `rdB pc pn`, any coin, no public. -/
def rdM (kc kn pc pn : ℕ → Bool) : MixedExpr F → Bool
  | .Var .traceCur i => kc i
  | .Var .traceNext i => kn i
  | .Var .challenge _ => true
  | .Var .publicVal _ => false
  | .Lift g => rdB pc pn g
  | .Scale g u => rdB pc pn g && rdM kc kn pc pn u
  | .Const _ => true
  | .Add x y => rdM kc kn pc pn x && rdM kc kn pc pn y
  | .Sub x y => rdM kc kn pc pn x && rdM kc kn pc pn y
  | .Neg x => rdM kc kn pc pn x
  | .Mul x y => rdM kc kn pc pn x && rdM kc kn pc pn y
  | .Pow x _ => rdM kc kn pc pn x

variable {K : Type} [Field K] [Algebra F K]

theorem rdM_eval {kc kn pc pn : ℕ → Bool} {g : MixedExpr F} (hg : rdM kc kn pc pn g = true) {eK eK' : Env K}
    {eF eF' : Env F} (hKt : ∀ i, kc i = true → eK.trace i = eK'.trace i)
    (hKn : ∀ i, kn i = true → eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j, pc j = true → eF.trace j = eF'.trace j)
    (hFn : ∀ j, pn j = true → eF.traceNext j = eF'.traceNext j) :
    g.eval eK eF = g.eval eK' eF' := by
  induction g with
  | Var k i =>
    cases k <;> simp only [rdM, Bool.false_eq_true] at hg <;> simp only [MixedExpr.eval]
    · exact hKt i hg
    · exact hKn i hg
    · rw [hKc]
  | Lift g =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, rdB_eval hg hFt hFn]
  | Scale g u ih =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, rdB_eval hg.1 hFt hFn, ih hg.2]
  | Const c => rfl
  | Add x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Sub x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Neg x ih =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, ih hg]
  | Mul x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Pow x m ih =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, ih hg]

/-- A `𝕂′` equation whose two halves have a read set evaluates congruently. -/
theorem rdQ_ev (δ : F) {kc kn pc pn : ℕ → Bool} {e : QE F} (hre : rdM kc kn pc pn e.re = true)
    (him : rdM kc kn pc pn e.im = true) {eK eK' : Env K} {eF eF' : Env F}
    (hKt : ∀ i, kc i = true → eK.trace i = eK'.trace i)
    (hKn : ∀ i, kn i = true → eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j, pc j = true → eF.trace j = eF'.trace j)
    (hFn : ∀ j, pn j = true → eF.traceNext j = eF'.traceNext j) :
    e.ev δ eK eF = e.ev δ eK' eF' := by
  simp only [QE.ev, rdM_eval hre hKt hKn hKc hFt hFn, rdM_eval him hKt hKn hKc hFt hFn]

end Congr

/-! ### The ALU's read sets -/

section Reads
variable {F : Type} [Field F]

/-- Current base columns `1..93` (never `isFT`). -/
def pcB (j : ℕ) : Bool := decide (1 ≤ j ∧ j < 94)
/-- Next base columns `2..93` (never the masks). -/
def pnB (j : ℕ) : Bool := decide (2 ≤ j ∧ j < 94)
/-- The round-1 `𝕂`-roles `0..17`. -/
def kQ (j : ℕ) : Bool := decide (j < 18)

theorem rdB_bitSum (base m : ℕ) (hb : 2 ≤ base) (hm : base + m ≤ 94) :
    rdB pcB pnB (bitSum base m : CoeffExpr F) = true :=
  rdB_sumList _ _ _ _ fun i hi => by
    have := List.mem_range.mp hi
    simp only [rdB, cv, pcB, Bool.and_eq_true, decide_eq_true_eq, true_and]; omega

theorem rdB_lN : rdB pcB pnB (AluSZChipJ9.lN : CoeffExpr F) = true :=
  rdB_sumList _ _ _ _ fun i hi => by
    have := List.mem_range.mp hi
    show (true && pnB (34 + i)) = true
    simp only [Bool.true_and, pnB, decide_eq_true_eq]; omega

theorem rdB_sumC (l : List ℕ) (hl : ∀ j ∈ l, 1 ≤ j ∧ j < 94) :
    rdB pcB pnB (AluSZChipJ9.sumC l : CoeffExpr F) = true :=
  rdB_sumList _ _ _ _ fun j hj => by simpa [rdB, cv, pcB] using hl j hj

theorem rdB_opCode : rdB pcB pnB (AluSZChipJ9.opCode : CoeffExpr F) = true := by
  unfold AluSZChipJ9.opCode
  refine rdB_sumList _ _ _ _ fun i hi => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rdB_lE : rdB pcB pnB (AluSZChipJ9.lE : CoeffExpr F) = true := rdB_bitSum _ _ (by decide) (by decide)
theorem rdB_oE : rdB pcB pnB (AluSZChipJ9.oE : CoeffExpr F) = true := rdB_bitSum _ _ (by decide) (by decide)
theorem rdB_cnE : rdB pcB pnB (AluSZChipJ9.cnE : CoeffExpr F) = true := rdB_bitSum _ _ (by decide) (by decide)

/-- **Every ALU base gate reads current columns `1..93` and next columns `2..93`** (no coin, no public). -/
theorem baseAG_rd : (AluSZChipJ9.baseAG (F := F)).all (fun a => rdB pcB pnB (AG.gate a)) = true := by
  have h1 := rdB_lE (F := F)
  have h2 := rdB_oE (F := F)
  have h3 := rdB_cnE (F := F)
  have h4 := rdB_lN (F := F)
  have h5 := rdB_opCode (F := F)
  simp only [AluSZChipJ9.baseAG, List.all_append, Bool.and_eq_true]
  simp [AluSZChipJ9.gKind, AluSZChipJ9.gSlot, AluSZChipJ9.gSeq, AluSZChipJ9.gCompat, AluSZChipJ9.gFlag,
    AluSZChipJ9.gCoef, AluSZChipJ9.gHdr, AluSZChipJ9.gConst, AluSZChipJ9.gBind, AluSZChipJ9.gBits,
    AluSZChipJ9.gSplit, AluSZChipJ9.gCap, AluSZChipJ9.gHdrNotLast, AluSZChipJ9.succ, AluSZChipJ9.coef,
    AluSZChipJ9.bind, AluSZChipJ9.ar, AluSZChipJ9.gKS, AluSZChipJ9.gLtP, AluSZChipJ9.gSplitV, AluSZChipJ9.sgnLt,
    AluSZChipJ9.prod3, AluSZChipJ9.hzV, AluSZChipJ9.sumC, CoeffExpr.sumList, AluSZChipJ9.opCols,
    AluSZChipJ9.roleCols, AluSZChipJ9.modeCols, AG.gate, CopyG.gate, Op.expr, rdB, pcB, pnB, cv, nv, notE, boolE,
    h1, h2, h3, h4, h5, List.all_eq_true, AluSZChipJ9.isFT, AluSZChipJ9.isLT, AluSZChipJ9.sP, AluSZChipJ9.pId, AluSZChipJ9.pOp, AluSZChipJ9.sH, AluSZChipJ9.sL, AluSZChipJ9.oAdd, AluSZChipJ9.oSub, AluSZChipJ9.oLt, AluSZChipJ9.oMul, AluSZChipJ9.oDiv, AluSZChipJ9.oMod, AluSZChipJ9.ra, AluSZChipJ9.rb, AluSZChipJ9.rc, AluSZChipJ9.rd, AluSZChipJ9.rx, AluSZChipJ9.ry, AluSZChipJ9.rs, AluSZChipJ9.mR, AluSZChipJ9.mS, AluSZChipJ9.mV, AluSZChipJ9.mW, AluSZChipJ9.mQ1, AluSZChipJ9.mQM, AluSZChipJ9.fst, AluSZChipJ9.eos, AluSZChipJ9.f1, AluSZChipJ9.f2, AluSZChipJ9.sf, AluSZChipJ9.aV, AluSZChipJ9.cf1, AluSZChipJ9.cf2, AluSZChipJ9.bt0, AluSZChipJ9.Vc, AluSZChipJ9.invP, AluSZChipJ9.sk, AluSZChipJ9.sv, AluSZChipJ9.kA, AluSZChipJ9.vA, AluSZChipJ9.kB, AluSZChipJ9.vB, AluSZChipJ9.kE, AluSZChipJ9.vE, AluSZChipJ9.lb, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, AluSZChipJ9.opc, AluSZChipJ9.kS, AluSZChipJ9.vS, AluSZChipJ9.mJ, AluSZChipJ9.mP, AluSZChipJ9.cn, AluSZChipJ9.cb0, AluSZChipJ9.cA, AluSZChipJ9.cB]
  exact ⟨⟨fun x hx => by omega, fun x hx => by omega⟩, fun x hx => by omega⟩

theorem baseGates_rd : ∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)), rdB pcB pnB g = true := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  exact List.all_eq_true.mp baseAG_rd a ha

theorem sumQ_rd (kc kn pc pn : ℕ → Bool) :
    ∀ l : List (QE F), (∀ e ∈ l, rdM kc kn pc pn e.re = true ∧ rdM kc kn pc pn e.im = true) →
      rdM kc kn pc pn (AluSZChipJ9.sumQ l).re = true ∧ rdM kc kn pc pn (AluSZChipJ9.sumQ l).im = true
  | [], _ => ⟨rfl, rfl⟩
  | e :: l, h => by
    have ih := sumQ_rd kc kn pc pn l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have he := h e List.mem_cons_self
    simp only [AluSZChipJ9.sumQ, List.foldr_cons, QE.add, rdM, Bool.and_eq_true] at ih ⊢
    exact ⟨⟨he.1, ih.1⟩, ⟨he.2, ih.2⟩⟩

theorem packE_rd : rdM kQ kQ pcB pnB (AluSZChipJ9.packE : QE F).re = true ∧
    rdM kQ kQ pcB pnB (AluSZChipJ9.packE : QE F).im = true :=
  sumQ_rd _ _ _ _ _ fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    have := List.mem_range.mp ht
    simp only [QE.scale, AluSZChipJ9.ypow, QE.chal, rdM, rdB, cv, pcB, AluSZChipJ9.bt0, Bool.and_eq_true,
      decide_eq_true_eq, and_true]
    omega

/-- **Every `identQ` equation reads `𝕂`-roles `< 18`, base columns `1..93` / `2..93`, coins, no public.** -/
theorem identQ_rd (δ : F) : ∀ e ∈ AluSZChipJ9.identQ δ,
    rdM kQ kQ pcB pnB e.re = true ∧ rdM kQ kQ pcB pnB e.im = true := by
  have h1 := rdB_lE (F := F)
  have h2 := rdB_oE (F := F)
  have hp := packE_rd (F := F)
  simp only [AluSZChipJ9.identQ, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  simp [AluSZChipJ9.qz, QE.scale, QE.sub, QE.add, QE.mul, QE.var, QE.next, QE.base, AluSZChipJ9.yQ, QE.chal,
    AluSZChipJ9.ypow, AluSZChipJ9.yMB, AluSZChipJ9.hz, AluSZChipJ9.hzV, AluSZChipJ9.sumC, CoeffExpr.sumList,
    rdM, rdB, kQ, pcB, pnB, notE, cv, nv, h1, h2, hp, AluSZChipJ9.H, AluSZChipJ9.HO, AluSZChipJ9.L,
    AluSZChipJ9.D1, AluSZChipJ9.D2, AluSZChipJ9.S1, AluSZChipJ9.S2, AluSZChipJ9.RL, AluSZChipJ9.RO,
    AluSZChipJ9.isFT, AluSZChipJ9.isLT, AluSZChipJ9.sP, AluSZChipJ9.pId, AluSZChipJ9.pOp, AluSZChipJ9.sH, AluSZChipJ9.sL, AluSZChipJ9.oAdd, AluSZChipJ9.oSub, AluSZChipJ9.oLt, AluSZChipJ9.oMul, AluSZChipJ9.oDiv, AluSZChipJ9.oMod, AluSZChipJ9.ra, AluSZChipJ9.rb, AluSZChipJ9.rc, AluSZChipJ9.rd, AluSZChipJ9.rx, AluSZChipJ9.ry, AluSZChipJ9.rs, AluSZChipJ9.mR, AluSZChipJ9.mS, AluSZChipJ9.mV, AluSZChipJ9.mW, AluSZChipJ9.mQ1, AluSZChipJ9.mQM, AluSZChipJ9.fst, AluSZChipJ9.eos, AluSZChipJ9.f1, AluSZChipJ9.f2, AluSZChipJ9.sf, AluSZChipJ9.aV, AluSZChipJ9.cf1, AluSZChipJ9.cf2, AluSZChipJ9.bt0, AluSZChipJ9.Vc, AluSZChipJ9.invP, AluSZChipJ9.sk, AluSZChipJ9.sv, AluSZChipJ9.kA, AluSZChipJ9.vA, AluSZChipJ9.kB, AluSZChipJ9.vB, AluSZChipJ9.kE, AluSZChipJ9.vE, AluSZChipJ9.lb, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, AluSZChipJ9.opc, AluSZChipJ9.kS, AluSZChipJ9.vS, AluSZChipJ9.mJ, AluSZChipJ9.mP, AluSZChipJ9.cn, AluSZChipJ9.cb0, AluSZChipJ9.cA, AluSZChipJ9.cB]

end Reads

/-! ## 2. The row model -/

section Model
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chal : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- Every base gate at row `r` against the successor `nxt`. -/
def RowB (r nxt : BRow F) : Prop :=
  ∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)), g.eval (envB r.col nxt.col) = 0

/-- Every `identQ` equation at row `(r, q)` against the successor base row `nxt` and successor `𝕂`-roles `nq`,
at the coins `chal`. -/
def RowQ (r : BRow F) (q : QRow 𝕂′) (nxt : BRow F) (nq : ℕ → K) : Prop :=
  ∀ e ∈ AluSZChipJ9.identQ δ, e.ev δ ⟨kvec δ q, nq, chal, fun _ => 0⟩ (envB r.col nxt.col) = 0

/-- Both, the successor's `𝕂′` row read by `kvec`. -/
def Row2 (x x' : BRow F × QRow 𝕂′) : Prop := RowB x.1 x'.1 ∧ RowQ δ chal x.1 x.2 x'.1 (kvec δ x'.2)

/-- A row good against every successor with `sL = 0` and `fst = 0` (a hdr, preg or padding row). -/
def TailP (x : BRow F × QRow 𝕂′) : Prop :=
  ∀ x' : BRow F × QRow 𝕂′, x'.1.sL = 0 → x'.1.fst = 0 → Row2 δ chal x x'

theorem rowB_of_AG {r nxt : BRow F}
    (h : ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB r.col nxt.col) = 0) : RowB r nxt := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  exact h a ha

/-- **A preg row** is good against every successor with `sL = 0`. -/
theorem tail_preg (a b c d : ℕ) : TailP δ chal (pregRow a b c d, QRow.zero) := fun x' hs _ =>
  ⟨rowB_of_AG (pregRow_base a b c d x'.1 hs),
    quiet_ident δ _ x'.1 rfl rfl (fun _ => rfl) rfl rfl rfl rfl hs chal (kvec δ x'.2)⟩

/-- **The padding row** is good against every successor with `sL = 0`. -/
theorem tail_pad : TailP δ chal (padRow, QRow.zero) := fun x' hs _ =>
  ⟨rowB_of_AG (padRow_base x'.1 hs),
    quiet_ident δ _ x'.1 rfl rfl (fun _ => rfl) rfl rfl rfl rfl hs chal (kvec δ x'.2)⟩

theorem runSums_length {Q : Type} [CommRing Q] : ∀ (a : Q × Q) (l : List (Q × Q)), (runSums a l).length = l.length
  | _, [] => rfl
  | a, d :: ds => by simp [runSums, runSums_length _ ds]

theorem blockQ_length {Q : Type} [CommRing Q] (p : ℕ) (y : Q) (cl : CallL) :
    (blockQ p y cl).length = (blockB (F := F) p cl).length := by
  simp [blockQ, blockB, laneHL, laneD, slotRows, runSums_length, List.length_flatMap, List.length_zip]

/-- A block's base rows zipped with its `𝕂′` rows. -/
def zipB (p : ℕ) (y : 𝕂′) (cl : CallL) : List (BRow F × QRow 𝕂′) := (blockB p cl).zip (blockQ p y cl)

theorem zipB_length (p : ℕ) (y : 𝕂′) (cl : CallL) : (zipB δ p y cl).length = (blockB (F := F) p cl).length := by
  rw [zipB, List.length_zip, blockQ_length (F := F), Nat.min_self]

/-- **A block from the block obligations**: the chain inside the block, and its last row good against every
`sL = 0`, `fst = 0` successor. -/
theorem block_chain (p : ℕ) (y : 𝕂′) (cl : CallL) (hB : BlockBaseSat (F := F) p cl)
    (hI : BlockIdentSat (K := K) δ p cl) (hy : Quad.mk _ (chal 2) (chal 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk _ (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t) :
    List.IsChain (Row2 δ chal) (zipB δ p y cl) ∧ ∀ x ∈ (zipB δ p y cl).getLast?, TailP δ chal x := by
  have hlen := zipB_length δ p y cl
  have hQ := blockQ_length (F := F) p y cl
  refine ⟨List.isChain_iff_getElem.mpr fun i hi => ?_, fun x hx => ?_⟩
  · have hi' : i + 1 < (blockB (F := F) p cl).length := hlen ▸ hi
    have e0 : (zipB δ p y cl)[i] = ((blockB p cl)[i], (blockQ p y cl)[i]) := List.getElem_zip
    have e1 : (zipB δ p y cl)[i + 1] = ((blockB p cl)[i + 1], (blockQ p y cl)[i + 1]) := List.getElem_zip
    rw [e0, e1]
    have gB : (blockB (F := F) p cl).getD i BRow.zero = (blockB p cl)[i] := List.getD_eq_getElem _ _ (by omega)
    have gB1 : (blockB (F := F) p cl).getD (i + 1) BRow.zero = (blockB p cl)[i + 1] := List.getD_eq_getElem _ _ hi'
    have gQ : (blockQ p y cl).getD i QRow.zero = (blockQ p y cl)[i] := List.getD_eq_getElem _ _ (by omega)
    have gQ1 : (blockQ p y cl).getD (i + 1) QRow.zero = (blockQ p y cl)[i + 1] := List.getD_eq_getElem _ _ (by omega)
    have hN : NextOK (blockB p cl) i (blockB p cl)[i + 1] := ⟨fun _ => gB1.symm, fun h => absurd h (by omega)⟩
    refine ⟨fun g hg => ?_, fun e he => ?_⟩
    · have := hB i (by omega) _ hN g hg
      rwa [gB] at this
    · have := hI y chal hy hyp i (by omega) _ hN (blockQ p y cl)[i + 1] (fun _ => gQ1.symm) e he
      rwa [gB, gQ] at this
  · rw [List.getLast?_eq_getElem?] at hx
    have hpos : 0 < (zipB δ p y cl).length := by simp [zipB, blockB, blockQ]
    have hl : (zipB δ p y cl).length - 1 < (zipB δ p y cl).length := by omega
    rw [List.getElem?_eq_getElem hl, Option.mem_def, Option.some_inj] at hx
    subst hx
    intro x' hs hf
    set m := (zipB δ p y cl).length - 1 with hm
    have e0 : (zipB δ p y cl)[m] = ((blockB p cl)[m]'(by omega), (blockQ p y cl)[m]'(by omega)) := List.getElem_zip
    rw [e0]
    have gB : (blockB (F := F) p cl).getD m BRow.zero = (blockB p cl)[m]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have gQ : (blockQ p y cl).getD m QRow.zero = (blockQ p y cl)[m]'(by omega) := List.getD_eq_getElem _ _ (by omega)
    have hN : NextOK (blockB p cl) m x'.1 := ⟨fun h => absurd h (by omega), fun _ => ⟨hs, hf⟩⟩
    refine ⟨fun g hg => ?_, fun e he => ?_⟩
    · have := hB m (by omega) _ hN g hg
      rwa [gB] at this
    · have := hI y chal hy hyp m (by omega) _ hN x'.2 (fun h => absurd h (by omega)) e he
      rwa [gB, gQ] at this

theorem zipB_head (p : ℕ) (y : 𝕂′) (cl : CallL) :
    ∀ x ∈ (zipB δ p y cl).head?, x.1.sL = 0 ∧ x.1.fst = 0 := by
  intro x hx
  simp only [zipB, blockB, blockQ, List.zip_cons_cons, List.head?_cons, Option.mem_def, Option.some_inj] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- A list of rows each good against every quiet successor, each itself quiet, is a chain. -/
theorem chain_of_quiet : ∀ L : List (BRow F × QRow 𝕂′), (∀ x ∈ L, TailP δ chal x ∧ x.1.sL = 0 ∧ x.1.fst = 0) →
    List.IsChain (Row2 δ chal) L
  | [], _ => List.IsChain.nil
  | a :: t, h => by
    refine List.isChain_cons.mpr ⟨fun y hy => ?_, chain_of_quiet t fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    have hyt : y ∈ t := List.mem_of_mem_head? hy
    have := h y (List.mem_cons_of_mem _ hyt)
    exact (h a List.mem_cons_self).1 y this.2.1 this.2.2

theorem tail_append {A B : List (BRow F × QRow 𝕂′)} (hA : ∀ x ∈ A.getLast?, TailP δ chal x)
    (hB : ∀ x ∈ B.getLast?, TailP δ chal x) : ∀ x ∈ (A ++ B).getLast?, TailP δ chal x := by
  intro x hx
  rw [List.getLast?_append] at hx
  cases hb : B.getLast? with
  | none => rw [hb, Option.none_or] at hx; exact hA x hx
  | some z => rw [hb, Option.some_or] at hx; exact hB x (by rw [hb]; exact hx)

end Model

/-! ## 3. The honest table -/

section Table
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chal : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The honest ALU table** (base row, `𝕂′` row): preg rows, the blocks of the calls, one padding row. -/
def tblP (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL) : List (BRow F × QRow 𝕂′) :=
  pregs.map (fun r => (r, QRow.zero)) ++ cls.flatMap (zipB δ p y) ++ [(padRow, QRow.zero)]

theorem blocks_chain (p : ℕ) (y : 𝕂′) (hy : Quad.mk _ (chal 2) (chal 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk _ (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t) :
    ∀ cls : List CallL, (∀ cl ∈ cls, BlockBaseSat (F := F) p cl ∧ BlockIdentSat (K := K) δ p cl) →
      List.IsChain (Row2 δ chal) (cls.flatMap (zipB δ p y)) ∧
        (∀ x ∈ (cls.flatMap (zipB δ p y)).getLast?, TailP δ chal x) ∧
        (∀ x ∈ (cls.flatMap (zipB δ p y)).head?, x.1.sL = 0 ∧ x.1.fst = 0)
  | [], _ => ⟨List.IsChain.nil, by simp, by simp⟩
  | cl :: t, h => by
    obtain ⟨ihc, iht, ihh⟩ := blocks_chain p y hy hyp t fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨hB, hI⟩ := h cl List.mem_cons_self
    obtain ⟨bc, bt⟩ := block_chain δ chal p y cl hB hI hy hyp
    rw [List.flatMap_cons]
    refine ⟨List.isChain_append.mpr ⟨bc, ihc, fun x hx z hz => bt x hx z (ihh z hz).1 (ihh z hz).2⟩,
      tail_append δ chal bt iht, fun x hx => ?_⟩
    rw [List.head?_append] at hx
    cases hz : (zipB δ p y cl).head? with
    | none => simp [zipB, blockB, blockQ] at hz
    | some z => rw [hz] at hx; exact zipB_head δ p y cl x (by rw [hz]; exact hx)

/-- **`tblP_chain`: the honest ALU table is a `Row2` chain** — every base gate and every `identQ` equation at
every row against the next row — from the per-call block obligations `hblk` and preg rows `hpreg`. -/
theorem tblP_chain (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL)
    (hpreg : ∀ r ∈ pregs, ∃ a b c d : ℕ, r = pregRow a b c d)
    (hblk : ∀ cl ∈ cls, BlockBaseSat (F := F) p cl ∧ BlockIdentSat (K := K) δ p cl)
    (hy : Quad.mk _ (chal 2) (chal 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk _ (chal (40 + 2 * t)) (chal (41 + 2 * t)) = y ^ t) :
    List.IsChain (Row2 δ chal) (tblP δ p y pregs cls) := by
  have hP : ∀ x ∈ pregs.map (fun r => (r, (QRow.zero : QRow 𝕂′))), TailP δ chal x ∧ x.1.sL = 0 ∧ x.1.fst = 0 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, b, c, d, rfl⟩ := hpreg r hr
    exact ⟨tail_preg δ chal a b c d, rfl, rfl⟩
  have hPl : ∀ x ∈ (pregs.map (fun r => (r, (QRow.zero : QRow 𝕂′)))).getLast?, TailP δ chal x :=
    fun x hx => (hP x (List.mem_of_getLast? hx)).1
  obtain ⟨bc, bt, bh⟩ := blocks_chain δ chal p y hy hyp cls hblk
  unfold tblP
  refine List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨chain_of_quiet δ chal _ hP, bc,
    fun x hx z hz => (hP x (List.mem_of_getLast? hx)).1 z (bh z hz).1 (bh z hz).2⟩, List.isChain_singleton _,
    fun x hx z hz => ?_⟩
  simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hz
  subst hz
  exact tail_append δ chal hPl bt x hx _ rfl rfl

theorem tblP_getLast (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL) :
    (tblP δ p y pregs cls).getLast? = some (padRow, QRow.zero) := List.getLast?_concat

theorem tblP_ne_nil (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL) :
    tblP δ p y pregs cls ≠ [] := by simp [tblP]

/-- Every honest row's base part has `isLT = 0` (the last-row mask is the trace's, not the table's). -/
theorem tblP_isLT (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL)
    (hpreg : ∀ r ∈ pregs, ∃ a b c d : ℕ, r = pregRow a b c d) :
    ∀ x ∈ tblP δ p y pregs cls, x.1.isLT = 0 := by
  intro x hx
  simp only [tblP, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_singleton] at hx
  rcases hx with (⟨r, hr, rfl⟩ | ⟨cl, -, hx⟩) | rfl
  · obtain ⟨a, b, c, d, rfl⟩ := hpreg r hr; rfl
  · obtain ⟨xb, xq⟩ := x
    have hb := (List.of_mem_zip hx).1
    simp only [blockB, List.mem_cons, List.mem_flatMap, slotRows, List.mem_map] at hb
    rcases hb with rfl | ⟨s, -, i, -, rfl⟩ <;> rfl
  · rfl

/-- The first row's base part has `sL = 0` (a preg, hdr or padding row). -/
theorem tblP_head_sL (p : ℕ) (y : 𝕂′) (pregs : List (BRow F)) (cls : List CallL)
    (hpreg : ∀ r ∈ pregs, ∃ a b c d : ℕ, r = pregRow a b c d) :
    ∀ x ∈ (tblP δ p y pregs cls).head?, x.1.sL = 0 := by
  intro x hx
  cases pregs with
  | cons r t =>
    simp only [tblP, List.map_cons, List.cons_append, List.head?_cons, Option.mem_def, Option.some_inj] at hx
    subst hx
    obtain ⟨a, b, c, d, rfl⟩ := hpreg r List.mem_cons_self; rfl
  | nil =>
    simp only [tblP, List.map_nil, List.nil_append] at hx
    rw [List.head?_append] at hx
    cases hz : (cls.flatMap (zipB δ p y)).head? with
    | none => rw [hz] at hx; simp only [List.head?_cons, Option.none_or, Option.mem_def, Option.some_inj] at hx; subst hx; rfl
    | some z =>
      rw [hz] at hx
      simp only [Option.some_or, Option.mem_def, Option.some_inj] at hx
      subst hx
      cases cls with
      | nil => simp at hz
      | cons cl t =>
        rw [List.flatMap_cons, List.head?_append] at hz
        cases hz' : (zipB δ p y cl).head? with
        | none => simp [zipB, blockB, blockQ] at hz'
        | some w =>
          rw [hz'] at hz
          simp only [Option.some_or, Option.some_inj] at hz
          subst hz
          exact (zipB_head δ p y cl w (by rw [hz']; rfl)).1

end Table

/-! ## 4. Arbitrary successor rows and the last-row padding row -/

section Of
variable {F : Type} [Field F]

/-- The base row reading a column function on columns `< 94`. -/
def ofColB (f : ℕ → F) : BRow F :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, fun i => f (7 + i), fun i => f (13 + i), fun i => f (20 + i), f 26, f 27,
    f 28, f 29, f 30, f 31, f 32, f 33, fun t => f (34 + t), f 66, f 67, f 68, f 69, f 70, f 71, f 72, f 73, f 74,
    f 75, f 76, f 77, f 78, f 79, f 80, f 81, f 82, f 83, f 84, f 85, fun i => f (86 + i), f 92, f 93⟩

theorem ofColB_col (f : ℕ → F) (j : ℕ) (hj : j < 94) : (ofColB f).col j = f j := by
  interval_cases j <;> simp only [BRow.col, ofColB] <;> norm_num

theorem padRow_col (j : ℕ) : (padRow : BRow F).col j = 0 := by
  simp only [BRow.col, padRow, BRow.zero, ite_self]

/-- The padding row as the trace sees it at its last row (the last-row mask `isLT = 1`). -/
def padLT : BRow F := { (padRow : BRow F) with isLT := 1 }

theorem padLT_col (j : ℕ) (hj : j ≠ 1) : (padLT : BRow F).col j = 0 := by
  simp only [BRow.col, padLT, padRow, BRow.zero, if_neg hj, ite_self]

end Of

section OfK
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

theorem equiv_symm_mk (a c : K) : (Quad.equiv (algebraMap F K δ)).symm (Quad.mk _ a c) = (a, c) := by
  rw [Equiv.symm_apply_eq]; rfl

/-- The `𝕂′` row reading a `𝕂`-role function on roles `< 18`. -/
def ofKQ (g : ℕ → K) : QRow 𝕂′ :=
  ⟨Quad.mk _ (g 0) (g 1), Quad.mk _ (g 2) (g 3), Quad.mk _ (g 4) (g 5), Quad.mk _ (g 6) (g 7),
    Quad.mk _ (g 8) (g 9), Quad.mk _ (g 10) (g 11), Quad.mk _ (g 12) (g 13), Quad.mk _ (g 14) (g 15),
    Quad.mk _ (g 16) (g 17)⟩

theorem kvec_ofKQ (g : ℕ → K) (j : ℕ) (hj : j < 18) : kvec δ (ofKQ δ g) j = g j := by
  interval_cases j <;> simp [kvec, ofKQ, QRow.role, equiv_symm_mk]

/-- **Transfer**: a `Row2` fact at a row and successor gives every base gate and every `identQ` equation at any
environment agreeing with them on the read sets. -/
theorem row_transfer (chals : ℕ → K) (r : BRow F) (q : QRow 𝕂′) (x' : BRow F × QRow 𝕂′) (eF : Env F)
    (eK : Env K) (h2 : Row2 δ chals (r, q) x')
    (ht : ∀ j, pcB j = true → eF.trace j = r.col j) (hnx : ∀ j, pnB j = true → eF.traceNext j = x'.1.col j)
    (hKt : ∀ j, kQ j = true → eK.trace j = kvec δ q j)
    (hKn : ∀ j, kQ j = true → eK.traceNext j = kvec δ x'.2 j) (hKc : eK.chal = chals) :
    (∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)), g.eval eF = 0) ∧
      ∀ e ∈ AluSZChipJ9.identQ δ, e.ev δ eK eF = 0 := by
  refine ⟨fun g hg => ?_, fun e he => ?_⟩
  · rw [rdB_eval (baseGates_rd g hg) (e' := envB r.col x'.1.col) ht hnx]
    exact h2.1 g hg
  · rw [rdQ_ev δ (identQ_rd δ e he).1 (identQ_rd δ e he).2 (eK' := ⟨kvec δ q, kvec δ x'.2, chals, fun _ => 0⟩)
      (eF' := envB r.col x'.1.col) hKt hKn hKc ht hnx]
    exact h2.2 e he

end OfK

/-! ## 5. The honest trace -/

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X])

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- Row `i` of a table, the padding row beyond its end. -/
def rowAt (tb : List (BRow F × QRow 𝕂′)) (i : ℕ) : BRow F × QRow 𝕂′ := tb.getD i (padRow, QRow.zero)

/-- `𝕂`-role `r` of row `i`: round 1 (`r < 18`) from the table's `𝕂′` row, round 2 from `r2`. -/
def roleK (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (r : ℕ) (i : Fin n) : K :=
  if r < 18 then kvec δ (rowAt δ tb i).2 r else r2 r i

/-- **The honest column function**: base columns `< 94` from the table, `𝕂`-role coordinates above. -/
def colAL (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (c : ℕ) (i : Fin n) : F :=
  if c < 94 then (rowAt δ tb i).1.col c else coordN b (roleK δ tb r2 ((c - 94) / 3) i) (c - 94)

/-- The successor point of the last row node. -/
def xLast : F := orbit.ω * nodes ⟨n - 1, Nat.sub_lt hn (by omega)⟩

/-- **The honest ALU trace polynomials**: the preprocessing `pre` at columns `2..4`, the `sL` column corrected to
vanish at the last node's successor (`AluTraceFix.fixAt`), every other column the interpolant of `colAL`. -/
def polyAL (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) :
    Fin (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w → F[X] := fun j =>
  if hj : 2 ≤ (j : ℕ) ∧ (j : ℕ) < 5 then pre ⟨(j : ℕ) - 2, by omega⟩
  else if (j : ℕ) = AluSZChipJ9.sL then
    AluTraceFix.fixAt (honestQ hn nodes (colAL δ b tb r2) _ j) (AluTraceFix.zNodes nodes) (xLast hn nodes orbit)
  else honestQ hn nodes (colAL δ b tb r2) _ j

/-- Row `i`'s base environment. -/
abbrev EFa (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (i : Fin n) : Env F :=
  Reify.envOfTrace (polyAL δ b hn nodes orbit chals pubs pre tb r2) orbit.ω (nodes i) (slotVal b 94 chals)
    (slotVal b 94 pubs)

/-- Row `i`'s gathered `𝕂` environment. -/
abbrev EKa (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (i : Fin n) : Env K :=
  gatherEnv b ((AluSZChipJ9.aluTemplateSZ δ).col0 3) (EFa δ b hn nodes orbit chals pubs pre tb r2 i)

variable (tb : List (BRow F × QRow (Quad (algebraMap F K δ)))) (r2 : ℕ → Fin n → K)

theorem polyAL_eval_node (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (j : Fin (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w) (i : Fin n) :
    (polyAL δ b hn nodes orbit chals pubs pre tb r2 j).eval (nodes i) = fullCol hn (colAL δ b tb r2) j i := by
  unfold polyAL
  split_ifs with h1 h2
  · rw [hpre]
    have e : (j : ℕ) - 2 + 2 = j := by omega
    simp only [fullCol, if_neg (show (j : ℕ) ≠ 0 by omega), if_neg (show (j : ℕ) ≠ 1 by omega), e]
  · rw [AluTraceFix.fixAt_eval_node _ _ _ (AluTraceFix.zNodes_eval_node nodes i)]
    exact honestQ_eval hn nodes hinj _ _ i
  · exact honestQ_eval hn nodes hinj _ _ i

theorem EFa_trace (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) {j : ℕ} (hj : j < 196) :
    (EFa δ b hn nodes orbit chals pubs pre tb r2 i).trace j = fullCol hn (colAL δ b tb r2) j i := by
  have hw : j < (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w := by
    rw [AluSZChipJ9.aluSZ_width_eq]; exact hj
  simp only [Reify.envOfTrace, dif_pos hw]
  exact polyAL_eval_node δ b hn nodes orbit chals pubs pre tb r2 hinj hpre ⟨j, hw⟩ i

theorem EFa_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (EFa δ b hn nodes orbit chals pubs pre tb r2 i).traceNext j =
      (EFa δ b hn nodes orbit chals pubs pre tb r2 ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [Reify.envOfTrace]
  split_ifs with hw
  · rw [mul_comm, ← hadj i hi]
  · rfl

theorem orbit_ω_ne_zero : orbit.ω ≠ 0 := by
  have h0 : 0 < orderOf orbit.ω := by rw [orbit.order_ω]; positivity
  exact (orderOf_pos_iff.mp h0).isUnit.ne_zero

/-- **The last row's successor has `sL = 0`** (the virtual zero row, or row `0` when the successor is a node). -/
theorem EFa_next_last_sL (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hhead : (rowAt δ tb 0).1.sL = 0) :
    (EFa δ b hn nodes orbit chals pubs pre tb r2 ⟨n - 1, Nat.sub_lt hn (by omega)⟩).traceNext AluSZChipJ9.sL = 0 := by
  have hw : AluSZChipJ9.sL < (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w := by
    rw [AluSZChipJ9.aluSZ_width_eq]; decide
  simp only [Reify.envOfTrace, dif_pos hw, polyAL]
  rw [dif_neg (by decide), if_pos trivial]
  by_cases hz : (AluTraceFix.zNodes nodes).eval (orbit.ω * nodes ⟨n - 1, Nat.sub_lt hn (by omega)⟩) = 0
  · have hs := AluTraceFix.succ_last_mem_node hn nodes hinj orbit.ω (orbit_ω_ne_zero orbit) hadj
      (by rwa [mul_comm] at hz)
    rw [mul_comm, hs, AluTraceFix.fixAt_eval_node _ _ _ (AluTraceFix.zNodes_eval_node nodes _),
      honestQ_eval hn nodes hinj]
    simpa [fullCol, colAL, AluSZChipJ9.sL, ← BRow.col_sL] using hhead
  · exact AluTraceFix.fixAt_eval_x _ _ hz

theorem EKa_trace (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) {r : ℕ} (hr : r < 34) :
    (EKa δ b hn nodes orbit chals pubs pre tb r2 i).trace r = roleK δ tb r2 r i := by
  have hv : ∀ k : Fin 3, (EFa δ b hn nodes orbit chals pubs pre tb r2 i).trace (94 + 3 * r + k) =
      coord b (roleK δ tb r2 r i) k := fun k => by
    have hk := k.isLt
    rw [EFa_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i (by omega)]
    have h94 : ¬ (94 + 3 * r + (k : ℕ) < 94) := by omega
    have hmod : (94 + 3 * r + (k : ℕ) - 94) / 3 = r := by omega
    simp only [fullCol, colAL, if_neg h94, if_neg (show 94 + 3 * r + (k : ℕ) ≠ 0 by omega),
      if_neg (show 94 + 3 * r + (k : ℕ) ≠ 1 by omega), hmod]
    unfold coordN
    congr 1
    exact Fin.ext (by simp; omega)
  simp only [gatherEnv, ChipTemplate.col0, AluSZChipJ9.aluTemplateSZ_baseCols, hv, coord]
  exact b.sum_repr _

theorem EKa_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (EKa δ b hn nodes orbit chals pubs pre tb r2 i).traceNext r =
      (EKa δ b hn nodes orbit chals pubs pre tb r2 ⟨(i : ℕ) + 1, hi⟩).trace r :=
  TeleH.gather_next_T b _ _ _ (EFa_next δ b hn nodes orbit chals pubs pre tb r2 hinj hadj hpre i hi) r

theorem EKa_chal (i : Fin n) : (EKa δ b hn nodes orbit chals pubs pre tb r2 i).chal = chals := by
  funext r
  exact TeleH.gather_chal_T b _ 94 (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ chals rfl r

theorem EKa_pub (i : Fin n) : (EKa δ b hn nodes orbit chals pubs pre tb r2 i).pub = pubs := by
  funext r
  exact TeleH.gather_pub_T b _ 94 (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ pubs rfl r

/-! ### Table facts -/

theorem rowAt_pad (hlast : tb.getLast? = some (padRow, QRow.zero)) (k : ℕ) (hk : tb.length ≤ k + 1) :
    rowAt δ tb k = (padRow, QRow.zero) := by
  unfold rowAt
  by_cases hk' : k < tb.length
  · have hk1 : k = tb.length - 1 := by omega
    rw [List.getD_eq_getElem _ _ hk']
    rw [List.getLast?_eq_getElem?] at hlast
    subst hk1
    rw [List.getElem?_eq_getElem hk', Option.some_inj] at hlast
    exact hlast
  · exact List.getD_eq_default _ _ (by omega)

theorem rowAt_chain (hch : List.IsChain (Row2 δ chals) tb) (hlast : tb.getLast? = some (padRow, QRow.zero))
    (k : ℕ) : Row2 δ chals (rowAt δ tb k) (rowAt δ tb (k + 1)) := by
  by_cases hk : k + 1 < tb.length
  · have e0 : rowAt δ tb k = tb[k] := List.getD_eq_getElem _ _ (by omega)
    have e1 : rowAt δ tb (k + 1) = tb[k + 1] := List.getD_eq_getElem _ _ hk
    rw [e0, e1]
    exact List.isChain_iff_getElem.mp hch k hk
  · rw [rowAt_pad δ tb hlast k (by omega), rowAt_pad δ tb hlast (k + 1) (by omega)]
    exact tail_pad δ chals _ rfl rfl

theorem rowAt_isLT (hLT : ∀ x ∈ tb, x.1.isLT = 0) (k : ℕ) : (rowAt δ tb k).1.isLT = 0 := by
  unfold rowAt
  by_cases hk : k < tb.length
  · rw [List.getD_eq_getElem _ _ hk]; exact hLT _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem rowAt_head (hhead : ∀ x ∈ tb.head?, x.1.sL = 0) : (rowAt δ tb 0).1.sL = 0 := by
  unfold rowAt
  cases tb with
  | nil => rfl
  | cons a t => exact hhead a rfl

/-- **Stage 1: every base gate and every `identQ` equation at every row of the honest trace**, from a `Row2` chain
`tb` that ends with the padding row, starts with `sL = 0`, has `isLT = 0` throughout and fits in `n` rows. -/
theorem aluRows_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (hlen : tb.length ≤ n) (hch : List.IsChain (Row2 δ chals) tb)
    (hlast : tb.getLast? = some (padRow, QRow.zero)) (hhead : ∀ x ∈ tb.head?, x.1.sL = 0)
    (hLT : ∀ x ∈ tb, x.1.isLT = 0) (i : Fin n) :
    (∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)), g.eval (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0) ∧
      ∀ e ∈ AluSZChipJ9.identQ δ,
        e.ev δ (EKa δ b hn nodes orbit chals pubs pre tb r2 i) (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0 := by
  have hT := EFa_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre
  have hK := EKa_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre
  by_cases hi : (i : ℕ) + 1 < n
  · refine row_transfer δ chals (rowAt δ tb i).1 (rowAt δ tb i).2 (rowAt δ tb ((i : ℕ) + 1)) _ _
      (rowAt_chain δ chals tb hch hlast i) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      (EKa_chal δ b hn nodes orbit chals pubs pre tb r2 i)
    · simp only [pcB, decide_eq_true_eq] at hj
      rw [hT i (by omega)]
      by_cases h1 : j = 1
      · subst h1
        have hne : i ≠ ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        simp only [fullCol, if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true, if_neg hne, BRow.col_isLT]
        exact (rowAt_isLT δ tb hLT i).symm
      · simp only [fullCol, if_neg (show j ≠ 0 by omega), if_neg h1, colAL, if_pos hj.2]
    · simp only [pnB, decide_eq_true_eq] at hj
      rw [EFa_next δ b hn nodes orbit chals pubs pre tb r2 hinj hadj hpre i hi, hT _ (by omega)]
      simp only [fullCol, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), colAL, if_pos hj.2]
    · simp only [kQ, decide_eq_true_eq] at hj
      rw [hK i (by omega)]; simp only [roleK, if_pos hj]
    · simp only [kQ, decide_eq_true_eq] at hj
      rw [EKa_next δ b hn nodes orbit chals pubs pre tb r2 hinj hadj hpre i hi, hK _ (by omega)]
      simp only [roleK, if_pos hj]
  · have hil : i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := Fin.ext (by simp; omega)
    have hpad : rowAt δ tb (i : ℕ) = (padRow, QRow.zero) := rowAt_pad δ tb hlast _ (by omega)
    set eF := EFa δ b hn nodes orbit chals pubs pre tb r2 i with heF
    set eK := EKa δ b hn nodes orbit chals pubs pre tb r2 i with heK
    have hns : (ofColB eF.traceNext).sL = 0 := by
      show eF.traceNext AluSZChipJ9.sL = 0
      rw [heF, hil]
      exact EFa_next_last_sL δ b hn nodes orbit chals pubs pre tb r2 hinj hadj (rowAt_head δ tb hhead)
    have h2 : Row2 δ chals (padLT, QRow.zero) (ofColB eF.traceNext, ofKQ δ eK.traceNext) :=
      ⟨rowB_of_AG (quiet_base _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
        (fun _ => rfl) rfl (fun _ => rfl) rfl rfl (Or.inl rfl) rfl rfl rfl hns),
        quiet_ident δ _ _ rfl rfl (fun _ => rfl) rfl rfl rfl rfl hns chals _⟩
    refine row_transfer δ chals padLT QRow.zero _ eF eK h2 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      (fun j hj => ?_) (EKa_chal δ b hn nodes orbit chals pubs pre tb r2 i)
    · simp only [pcB, decide_eq_true_eq] at hj
      rw [heF, hT i (by omega)]
      by_cases h1 : j = 1
      · subst h1
        simp only [fullCol, if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true, if_pos hil]
        rfl
      · simp only [fullCol, if_neg (show j ≠ 0 by omega), if_neg h1, colAL, if_pos hj.2, hpad, padRow_col,
          padLT_col j h1]
    · simp only [pnB, decide_eq_true_eq] at hj
      exact (ofColB_col _ j hj.2).symm
    · simp only [kQ, decide_eq_true_eq] at hj
      rw [heK, hK i (by omega)]
      simp only [roleK, if_pos hj, hpad]
    · simp only [kQ, decide_eq_true_eq] at hj
      exact (kvec_ofKQ δ _ j hj).symm

end Trace

/-! ## 6. Read sets of the LogUp keys -/

section RdQ
variable {F : Type} [Field F]

/-- Both halves of a `𝕂′` expression have the read set. -/
def RdQ (kc kn pc pn : ℕ → Bool) (e : QE F) : Prop :=
  rdM kc kn pc pn e.re = true ∧ rdM kc kn pc pn e.im = true

variable {kc kn pc pn : ℕ → Bool}

theorem RdQ_add {a c : QE F} (ha : RdQ kc kn pc pn a) (hc : RdQ kc kn pc pn c) : RdQ kc kn pc pn (QE.add a c) := by
  simp only [RdQ, QE.add, rdM, Bool.and_eq_true] at *
  exact ⟨⟨ha.1, hc.1⟩, ⟨ha.2, hc.2⟩⟩

theorem RdQ_mul (δ : F) {a c : QE F} (ha : RdQ kc kn pc pn a) (hc : RdQ kc kn pc pn c) :
    RdQ kc kn pc pn (QE.mul δ a c) := by
  simp only [RdQ, QE.mul, rdM, rdB, Bool.and_eq_true, Bool.true_and] at *
  exact ⟨⟨⟨ha.1, hc.1⟩, ⟨ha.2, hc.2⟩⟩, ⟨⟨ha.1, hc.2⟩, ⟨ha.2, hc.1⟩⟩⟩

theorem RdQ_chal (i j : ℕ) : RdQ kc kn pc pn (QE.chal i j : QE F) := ⟨rfl, rfl⟩
theorem RdQ_zero : RdQ kc kn pc pn (QE.zero : QE F) := ⟨rfl, rfl⟩
theorem RdQ_one : RdQ kc kn pc pn (QE.one : QE F) := ⟨rfl, rfl⟩
theorem RdQ_base {g : CoeffExpr F} (hg : rdB pc pn g = true) : RdQ kc kn pc pn (QE.base g) := ⟨hg, rfl⟩
theorem RdQ_var {r : ℕ} (h1 : kc r = true) (h2 : kc (r + 1) = true) : RdQ kc kn pc pn (QE.var r : QE F) :=
  ⟨h1, h2⟩

theorem RdQ_rlcFold (δ : F) : ∀ (es : List (QE F)) (m : ℕ), (∀ e ∈ es, RdQ kc kn pc pn e) →
    RdQ kc kn pc pn ((es.zipIdx m).foldr (fun ei acc => QE.add (QE.mul δ (QE.gpow ei.2) ei.1) acc) QE.zero)
  | [], _, _ => RdQ_zero
  | e :: es, m, h => by
    simp only [List.zipIdx, List.foldr_cons]
    exact RdQ_add (RdQ_mul δ ⟨rfl, rfl⟩ (h e List.mem_cons_self))
      (RdQ_rlcFold δ es (m + 1) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem RdQ_den (δ : F) (es : List (QE F)) (h : ∀ e ∈ es, RdQ kc kn pc pn e) : RdQ kc kn pc pn (den δ es) :=
  RdQ_add (RdQ_chal _ _) (RdQ_rlcFold δ es 0 h)

theorem RdQ_gpowQ (δ : F) : ∀ m : ℕ, RdQ kc kn pc pn (HQ.gpowQ δ m : QE F)
  | 0 => RdQ_one
  | m + 1 => RdQ_mul δ (RdQ_chal _ _) (RdQ_gpowQ δ m)

theorem RdQ_rlcQ (δ : F) : ∀ (l : List (CoeffExpr F)) (m : ℕ), (∀ g ∈ l, rdB pc pn g = true) →
    RdQ kc kn pc pn (HQ.rlcQ δ m l)
  | [], _, _ => RdQ_zero
  | g :: l, m, h => RdQ_add (RdQ_mul δ (RdQ_gpowQ δ m) (RdQ_base (h g List.mem_cons_self)))
      (RdQ_rlcQ δ l (m + 1) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem RdQ_denKeyQ (δ : F) (l : List (CoeffExpr F)) (h : ∀ g ∈ l, rdB pc pn g = true) :
    RdQ kc kn pc pn (HQ.denKeyQ δ l) :=
  RdQ_add (RdQ_chal _ _) (RdQ_rlcQ δ l 0 h)

/-- Current base columns `2..93` (no mask). -/
def pcK (j : ℕ) : Bool := decide (2 ≤ j ∧ j < 94)
/-- Nothing read. -/
def noR (_ : ℕ) : Bool := false

theorem rdB_reE (l : List AluSZChipJ9.RE) (hl : ∀ j, ChipHX.RE.col j ∈ l → 2 ≤ j ∧ j < 94) :
    ∀ g ∈ l.map (AluSZChipJ9.reE (F := F)), rdB pcK noR g = true := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
  cases c with
  | col j => simpa [AluSZChipJ9.reE, cv, rdB, pcK] using hl j hc
  | k c => rfl

theorem rd_keyRg (δ : F) : RdQ kQ noR pcK noR (HQ.denKeyQ δ (AluSZChipJ9.keyRgE : List (CoeffExpr F))) :=
  RdQ_denKeyQ _ _ (rdB_reE _ fun j hj => by
    simp [AluSZChipJ9.keyRgRE, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc] at hj
    rcases hj with rfl | rfl | rfl <;> decide)
theorem rd_opRec (δ : F) : RdQ kQ noR pcK noR (HQ.denKeyQ δ (AluSZChipJ9.opRecE : List (CoeffExpr F))) :=
  RdQ_denKeyQ _ _ (rdB_reE _ fun j hj => by
    simp [AluSZChipJ9.opRecRE, AluSZChipJ9.idc, AluSZChipJ9.opc] at hj
    rcases hj with rfl | rfl <;> decide)
theorem rd_keyJet (δ : F) : RdQ kQ noR pcK noR (HQ.denKeyQ δ (AluSZChipJ9.keyJetE : List (CoeffExpr F))) :=
  RdQ_denKeyQ _ _ (rdB_reE _ fun j hj => by
    simp [AluSZChipJ9.keyJetRE, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, AluSZChipJ9.kS, AluSZChipJ9.vS,
      AluSZChipJ9.kE, AluSZChipJ9.vE] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
theorem rd_keyX (δ : F) : RdQ kQ noR pcK noR (HQ.denKeyQ δ (AluSZChipJ9.keyXE : List (CoeffExpr F))) :=
  RdQ_denKeyQ _ _ (rdB_reE _ fun j hj => by
    simp [AluSZChipJ9.keyXRE, AluSZChipJ9.vS, AluSZChipJ9.kA, AluSZChipJ9.vA, AluSZChipJ9.kB, AluSZChipJ9.vB] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide)
theorem rd_val (δ : F) : RdQ kQ noR pcK noR (den δ (AluSZChipJ9.valKey : List (QE F))) := by
  refine RdQ_den δ _ fun e he => ?_
  simp only [AluSZChipJ9.valKey, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact RdQ_chal _ _
  · exact RdQ_zero
  · exact RdQ_var rfl rfl
  · exact RdQ_zero
  · exact RdQ_base rfl

end RdQ

/-! ## 7. Prefix sums -/

section Acc
variable {Q : Type} [AddCommMonoid Q] {n : ℕ}

/-- Term `j` of a row function (`0` past the end). -/
def tN (t : Fin n → Q) (j : ℕ) : Q := if h : j < n then t ⟨j, h⟩ else 0

/-- The inclusive prefix sum. -/
def accN (t : Fin n → Q) (i : ℕ) : Q := ∑ j ∈ Finset.range (i + 1), tN t j

theorem accN_zero (t : Fin n → Q) : accN t 0 = tN t 0 := by simp [accN]
theorem accN_succ (t : Fin n → Q) (j : ℕ) : accN t (j + 1) = accN t j + tN t (j + 1) := by
  simp only [accN]; rw [Finset.sum_range_succ]
theorem tN_fin (t : Fin n → Q) (i : Fin n) : tN t i = t i := by simp [tN, i.isLt]
theorem accN_last (t : Fin n → Q) (hn : 0 < n) : accN t (n - 1) = ∑ i, t i := by
  simp only [accN, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (tN t) n]
  exact Finset.sum_congr rfl fun i _ => tN_fin t i

end Acc

/-! ## 8. The LogUp lane: values -/

section LogVals
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  {n : ℕ} (chals : ℕ → K) (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- Row `i`'s model `𝕂` environment (its round-1 roles, the coins). -/
def eKM (i : ℕ) : Env K := ⟨kvec δ (rowAt δ tb i).2, fun _ => 0, chals, fun _ => 0⟩
/-- Row `i`'s model base environment. -/
def eFM (i : ℕ) : Env F := envB (rowAt δ tb i).1.col (fun _ => 0)

/-- **A key denominator of row `i`**, from the table and the coins. -/
def dK (e : QE F) (i : ℕ) : 𝕂′ := e.ev δ (eKM δ chals tb i) (eFM δ tb i)

abbrev dV (i : ℕ) : 𝕂′ := dK δ chals tb (den δ AluSZChipJ9.valKey) i
abbrev dR (i : ℕ) : 𝕂′ := dK δ chals tb (HQ.denKeyQ δ AluSZChipJ9.keyRgE) i
abbrev dO (i : ℕ) : 𝕂′ := dK δ chals tb (HQ.denKeyQ δ AluSZChipJ9.opRecE) i
abbrev dJ (i : ℕ) : 𝕂′ := dK δ chals tb (HQ.denKeyQ δ AluSZChipJ9.keyJetE) i
abbrev dX (i : ℕ) : 𝕂′ := dK δ chals tb (HQ.denKeyQ δ AluSZChipJ9.keyXE) i

/-- The service weight `sH − sP·mP` of row `i`. -/
def wSv (i : ℕ) : F := (rowAt δ tb i).1.sH - (rowAt δ tb i).1.sP * (rowAt δ tb i).1.mP

/-- **The three LogUp row terms** (validity read, service, export). -/
def tV (i : Fin n) : 𝕂′ := liftQ δ (rowAt δ tb i).1.aV * (dV δ chals tb i)⁻¹
def tS (i : Fin n) : 𝕂′ :=
  liftQ δ (wSv δ tb i) * (dR δ chals tb i)⁻¹ + liftQ δ (wSv δ tb i) * (dO δ chals tb i)⁻¹ -
    liftQ δ ((rowAt δ tb i).1.sH * (rowAt δ tb i).1.mJ) * (dJ δ chals tb i)⁻¹
def tX (i : Fin n) : 𝕂′ := liftQ δ (rowAt δ tb i).1.sH * (dX δ chals tb i)⁻¹

/-- The eight round-2 `𝕂′` columns `invV invR invO invJ invX accV accS accX` of row `i`. -/
def qv2 (s : ℕ) (i : Fin n) : 𝕂′ :=
  match s with
  | 0 => (dV δ chals tb i)⁻¹
  | 1 => (dR δ chals tb i)⁻¹
  | 2 => (dO δ chals tb i)⁻¹
  | 3 => (dJ δ chals tb i)⁻¹
  | 4 => (dX δ chals tb i)⁻¹
  | 5 => accN (tV (n := n) δ chals tb) i
  | 6 => accN (tS (n := n) δ chals tb) i
  | 7 => accN (tX (n := n) δ chals tb) i
  | _ => 0

/-- **The honest round-2 `𝕂`-roles** (`18..33`: Re / Im of `qv2`). -/
def r2AL (r : ℕ) (i : Fin n) : K :=
  if r % 2 = 0 then Quad.re _ (qv2 δ chals tb ((r - 18) / 2) i) else Quad.im _ (qv2 δ chals tb ((r - 18) / 2) i)

theorem invG_zero (a : F) (d : 𝕂′) (h : a ≠ 0 → d ≠ 0) : liftQ δ a * (d⁻¹ * d - 1) = 0 := by
  by_cases ha : a = 0
  · simp [ha, liftQ]
  · rw [inv_mul_cancel₀ (h ha), sub_self, mul_zero]

end LogVals

/-! ## 9. The LogUp lane at the honest trace -/

section LogTrace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X])
  (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))

local notation "𝕂′" => Quad (algebraMap F K δ)
local notation "EF" => EFa δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb)
local notation "EK" => EKa δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb)

variable (hinj : Function.Injective nodes)
  (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb (r2AL δ chals tb) ((k : ℕ) + 2) i)

include hinj hpre

theorem EF_base (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (h94 : j < 94) : (EF i).trace j = (rowAt δ tb i).1.col j := by
  rw [EFa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by omega)]
  simp only [fullCol, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), colAL, if_pos h94]

theorem EF_isFT (i : Fin n) : (EF i).trace AluSZChipJ9.isFT = if (i : ℕ) = 0 then 1 else 0 := by
  rw [EFa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by decide)]
  simp [fullCol, AluSZChipJ9.isFT]

theorem EF_isLT (i : Fin n) : (EF i).trace AluSZChipJ9.isLT = if (i : ℕ) = n - 1 then 1 else 0 := by
  rw [EFa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by decide)]
  simp only [fullCol, AluSZChipJ9.isLT, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true]
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

theorem EK_q2 (i : Fin n) (s : ℕ) (hs : s < 8) :
    Quad.mk _ ((EK i).trace (18 + 2 * s)) ((EK i).trace (18 + 2 * s + 1)) = qv2 δ chals tb s i := by
  rw [EKa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by omega),
    EKa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by omega)]
  simp only [roleK, if_neg (show ¬ (18 + 2 * s < 18) by omega), if_neg (show ¬ (18 + 2 * s + 1 < 18) by omega),
    r2AL, show (18 + 2 * s) % 2 = 0 by omega, show (18 + 2 * s + 1) % 2 = 1 by omega,
    show (18 + 2 * s - 18) / 2 = s by omega, show (18 + 2 * s + 1 - 18) / 2 = s by omega, if_true, one_ne_zero,
    if_false]
  exact Quad.mk_re_im _ _

/-- **A LogUp key denominator at the honest trace is the model's.** -/
theorem den_trace (e : QE F) (he : RdQ kQ noR pcK noR e) (i : Fin n) :
    e.ev δ (EK i) (EF i) = dK δ chals tb e i :=
  rdQ_ev δ he.1 he.2
    (fun j hj => by
      rw [EKa_trace δ b hn nodes orbit chals pubs pre tb _ hinj hpre i (by simp [kQ] at hj; omega)]
      simp only [roleK, if_pos (show j < 18 by simpa [kQ] using hj)]; rfl)
    (fun j hj => absurd hj (by simp [noR]))
    (EKa_chal δ b hn nodes orbit chals pubs pre tb _ i)
    (fun j hj => by
      simp only [pcK, decide_eq_true_eq] at hj
      exact EF_base δ b hn nodes orbit chals pubs pre tb hinj hpre i hj.1 hj.2)
    (fun j hj => absurd hj (by simp [noR]))

theorem EF_baseN (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {j : ℕ} (h2 : 2 ≤ j) (h94 : j < 94) :
    (EF i).traceNext j = (rowAt δ tb ((i : ℕ) + 1)).1.col j := by
  rw [EFa_next δ b hn nodes orbit chals pubs pre tb _ hinj hadj hpre i hi]
  exact EF_base δ b hn nodes orbit chals pubs pre tb hinj hpre ⟨(i : ℕ) + 1, hi⟩ h2 h94

theorem EK_q2N (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (s : ℕ) (hs : s < 8) :
    Quad.mk _ ((EK i).traceNext (18 + 2 * s)) ((EK i).traceNext (18 + 2 * s + 1)) =
      qv2 δ chals tb s ⟨(i : ℕ) + 1, hi⟩ := by
  rw [EKa_next δ b hn nodes orbit chals pubs pre tb _ hinj hadj hpre i hi,
    EKa_next δ b hn nodes orbit chals pubs pre tb _ hinj hadj hpre i hi]
  exact EK_q2 δ b hn nodes orbit chals pubs pre tb hinj hpre ⟨(i : ℕ) + 1, hi⟩ s hs

/-- **An accumulator's three gates** (init, step, terminal) at the honest trace, for any inclusive prefix sum. -/
theorem acc_honest (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (acc pubI : ℕ) (c : Bool → QE F) (t : Fin n → 𝕂′)
    (hacc : ∀ i : Fin n, Quad.mk _ ((EK i).trace acc) ((EK i).trace (acc + 1)) = accN t i)
    (hc1 : ∀ i : Fin n, (c true).ev δ (EK i) (EF i) = t i)
    (hc2 : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), (c false).ev δ (EK i) (EF i) = t ⟨(i : ℕ) + 1, hi⟩)
    (hpub : Quad.mk _ (pubs pubI) (pubs (pubI + 1)) = ∑ i, t i) (i : Fin n) :
    ∀ e ∈ AluSZChipJ9.accG acc pubI c, e.ev δ (EK i) (EF i) = 0 := by
  have hF := EF_isFT δ b hn nodes orbit chals pubs pre tb hinj hpre i
  have hL := EF_isLT δ b hn nodes orbit chals pubs pre tb hinj hpre i
  intro e he
  simp only [AluSZChipJ9.accG, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [ev_scale, ev_sub, ev_var, hacc, hc1]
    simp only [cv, CoeffExpr.eval]
    rw [hF]
    by_cases h0 : (i : ℕ) = 0
    · have e1 : accN t (i : ℕ) = t i := by rw [h0, accN_zero, ← h0, tN_fin]
      rw [if_pos h0, e1, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by omega
      rw [hc2 i hi, EKa_next δ b hn nodes orbit chals pubs pre tb _ hinj hadj hpre i hi acc,
        EKa_next δ b hn nodes orbit chals pubs pre tb _ hinj hadj hpre i hi (acc + 1), hacc ⟨(i : ℕ) + 1, hi⟩,
        hacc i, if_neg hl]
      have h1 : tN t ((i : ℕ) + 1) = t ⟨(i : ℕ) + 1, hi⟩ := tN_fin t ⟨(i : ℕ) + 1, hi⟩
      have h3 : accN t ((⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℕ) = accN t ((i : ℕ) + 1) := rfl
      have h2 : accN t ((i : ℕ) + 1) - accN t (i : ℕ) - t ⟨(i : ℕ) + 1, hi⟩ = 0 := by
        rw [accN_succ, h1]; abel
      rw [h3, h2, mul_zero]
  · rw [ev_scale, ev_sub, ev_var, ev_pub, EKa_pub δ b hn nodes orbit chals pubs pre tb _ i, hacc]
    simp only [cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · have e1 : accN t (i : ℕ) = ∑ j, t j := by rw [hl]; exact accN_last t hn
      rw [if_pos hl, e1, hpub, sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]

/-- **Every LogUp equation at every row of the honest trace**, from no vanishing active denominator (`hden`) and
the three terminal publics. -/
theorem logup_honest (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hden : ∀ i : Fin n, ((rowAt δ tb i).1.aV ≠ 0 → dV δ chals tb i ≠ 0) ∧
      ((rowAt δ tb i).1.sH + (rowAt δ tb i).1.sP ≠ 0 → dR δ chals tb i ≠ 0 ∧ dO δ chals tb i ≠ 0) ∧
      ((rowAt δ tb i).1.sH ≠ 0 → dJ δ chals tb i ≠ 0 ∧ dX δ chals tb i ≠ 0))
    (hpV : Quad.mk _ (pubs AluSZChipJ9.pubALv) (pubs (AluSZChipJ9.pubALv + 1)) = ∑ i : Fin n, tV δ chals tb i)
    (hpS : Quad.mk _ (pubs AluSZChipJ9.pubALs) (pubs (AluSZChipJ9.pubALs + 1)) = ∑ i : Fin n, tS δ chals tb i)
    (hpX : Quad.mk _ (pubs AluSZChipJ9.pubALx) (pubs (AluSZChipJ9.pubALx + 1)) = ∑ i : Fin n, tX δ chals tb i)
    (i : Fin n) : ∀ e ∈ AluSZChipJ9.logupQ δ, e.ev δ (EK i) (EF i) = 0 := by
  have q := EK_q2 δ b hn nodes orbit chals pubs pre tb hinj hpre
  have qN := EK_q2N δ b hn nodes orbit chals pubs pre tb hinj hpre hadj
  have bF := EF_base δ b hn nodes orbit chals pubs pre tb hinj hpre
  have bN := EF_baseN δ b hn nodes orbit chals pubs pre tb hinj hpre hadj
  have dT := den_trace δ b hn nodes orbit chals pubs pre tb hinj hpre
  have hAcc := acc_honest δ b hn nodes orbit chals pubs pre tb hinj hpre hadj
  intro e he
  rw [AluSZChipJ9.logupQ] at he
  simp only [List.mem_append] at he
  rcases he with ((((he | he) | he) | he) | he) | he
  · -- invV
    rw [List.mem_singleton] at he
    subst he
    rw [AluSZChipJ9.invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one, show AluSZChipJ9.invV = 18 + 2 * 0 from rfl, q i 0 (by norm_num),
      dT _ (rd_val δ) i]
    simp only [cv, CoeffExpr.eval]
    rw [bF i (by decide) (by decide)]
    exact invG_zero δ _ _ (hden i).1
  · exact hAcc _ _ _ (tV δ chals tb) (fun j => q j 5 (by norm_num))
      (fun j => by
        show (QE.scale (cv AluSZChipJ9.aV) (QE.var AluSZChipJ9.invV)).ev δ (EK j) (EF j) = _
        rw [ev_scale, ev_var, show AluSZChipJ9.invV = 18 + 2 * 0 from rfl, q j 0 (by norm_num)]
        simp only [cv, CoeffExpr.eval]
        rw [bF j (by decide) (by decide)]; rfl)
      (fun j hj => by
        show (QE.scale (nv AluSZChipJ9.aV) (QE.next AluSZChipJ9.invV)).ev δ (EK j) (EF j) = _
        rw [ev_scale, ev_next, show AluSZChipJ9.invV = 18 + 2 * 0 from rfl, qN j hj 0 (by norm_num)]
        simp only [nv, CoeffExpr.eval]
        rw [bN j hj (by decide) (by decide)]; rfl)
      hpV i e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · -- invR
      rw [AluSZChipJ9.invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one, show AluSZChipJ9.invR = 18 + 2 * 1 from rfl, q i 1 (by norm_num),
        dT _ (rd_keyRg δ) i]
      simp only [AluSZChipJ9.sumC, CoeffExpr.sumList, List.foldr, CoeffExpr.eval, cv, add_zero]
      rw [bF i (by decide) (by decide), bF i (by decide) (by decide)]
      exact invG_zero δ _ _ fun h => ((hden i).2.1 h).1
    · -- invO
      rw [AluSZChipJ9.invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one, show AluSZChipJ9.invO = 18 + 2 * 2 from rfl, q i 2 (by norm_num),
        dT _ (rd_opRec δ) i]
      simp only [AluSZChipJ9.sumC, CoeffExpr.sumList, List.foldr, CoeffExpr.eval, cv, add_zero]
      rw [bF i (by decide) (by decide), bF i (by decide) (by decide)]
      exact invG_zero δ _ _ fun h => ((hden i).2.1 h).2
    · -- invJ
      rw [AluSZChipJ9.invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one, show AluSZChipJ9.invJ = 18 + 2 * 3 from rfl, q i 3 (by norm_num),
        dT _ (rd_keyJet δ) i]
      simp only [cv, CoeffExpr.eval]
      rw [bF i (by decide) (by decide)]
      exact invG_zero δ _ _ fun h => ((hden i).2.2 h).1
  · exact hAcc _ _ _ (tS δ chals tb) (fun j => q j 6 (by norm_num))
      (fun j => by
        show (QE.sub (QE.add (QE.scale (.sub (cv AluSZChipJ9.sH) (.mul (cv AluSZChipJ9.sP) (cv AluSZChipJ9.mP)))
            (QE.var AluSZChipJ9.invR)) (QE.scale (.sub (cv AluSZChipJ9.sH) (.mul (cv AluSZChipJ9.sP)
            (cv AluSZChipJ9.mP))) (QE.var AluSZChipJ9.invO))) (QE.scale (.mul (cv AluSZChipJ9.sH)
            (cv AluSZChipJ9.mJ)) (QE.var AluSZChipJ9.invJ))).ev δ (EK j) (EF j) = _
        rw [ev_sub, ev_add, ev_scale, ev_scale, ev_scale, ev_var, ev_var, ev_var,
          show AluSZChipJ9.invR = 18 + 2 * 1 from rfl, show AluSZChipJ9.invO = 18 + 2 * 2 from rfl,
          show AluSZChipJ9.invJ = 18 + 2 * 3 from rfl, q j 1 (by norm_num), q j 2 (by norm_num),
          q j 3 (by norm_num)]
        simp only [cv, CoeffExpr.eval]
        rw [bF j (by decide) (by decide), bF j (by decide) (by decide), bF j (by decide) (by decide),
          bF j (by decide) (by decide)]
        rfl)
      (fun j hj => by
        show (QE.sub (QE.add (QE.scale (.sub (nv AluSZChipJ9.sH) (.mul (nv AluSZChipJ9.sP) (nv AluSZChipJ9.mP)))
            (QE.next AluSZChipJ9.invR)) (QE.scale (.sub (nv AluSZChipJ9.sH) (.mul (nv AluSZChipJ9.sP)
            (nv AluSZChipJ9.mP))) (QE.next AluSZChipJ9.invO))) (QE.scale (.mul (nv AluSZChipJ9.sH)
            (nv AluSZChipJ9.mJ)) (QE.next AluSZChipJ9.invJ))).ev δ (EK j) (EF j) = _
        rw [ev_sub, ev_add, ev_scale, ev_scale, ev_scale, ev_next, ev_next, ev_next,
          show AluSZChipJ9.invR = 18 + 2 * 1 from rfl, show AluSZChipJ9.invO = 18 + 2 * 2 from rfl,
          show AluSZChipJ9.invJ = 18 + 2 * 3 from rfl, qN j hj 1 (by norm_num), qN j hj 2 (by norm_num),
          qN j hj 3 (by norm_num)]
        simp only [nv, CoeffExpr.eval]
        rw [bN j hj (by decide) (by decide), bN j hj (by decide) (by decide), bN j hj (by decide) (by decide),
          bN j hj (by decide) (by decide)]
        rfl)
      hpS i e he
  · -- invX
    rw [List.mem_singleton] at he
    subst he
    rw [AluSZChipJ9.invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one, show AluSZChipJ9.invX = 18 + 2 * 4 from rfl, q i 4 (by norm_num),
      dT _ (rd_keyX δ) i]
    simp only [cv, CoeffExpr.eval]
    rw [bF i (by decide) (by decide)]
    exact invG_zero δ _ _ fun h => ((hden i).2.2 h).2
  · exact hAcc _ _ _ (tX δ chals tb) (fun j => q j 7 (by norm_num))
      (fun j => by
        show (QE.scale (cv AluSZChipJ9.sH) (QE.var AluSZChipJ9.invX)).ev δ (EK j) (EF j) = _
        rw [ev_scale, ev_var, show AluSZChipJ9.invX = 18 + 2 * 4 from rfl, q j 4 (by norm_num)]
        simp only [cv, CoeffExpr.eval]
        rw [bF j (by decide) (by decide)]; rfl)
      (fun j hj => by
        show (QE.scale (nv AluSZChipJ9.sH) (QE.next AluSZChipJ9.invX)).ev δ (EK j) (EF j) = _
        rw [ev_scale, ev_next, show AluSZChipJ9.invX = 18 + 2 * 4 from rfl, qN j hj 4 (by norm_num)]
        simp only [nv, CoeffExpr.eval]
        rw [bN j hj (by decide) (by decide)]; rfl)
      hpX i e he

end LogTrace

/-! ## 10. Honest acceptance of the ALU chip -/

section Sat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X])
  (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))

/-- **Honest acceptance of `aluSZChipJ9`** (stages 1–2): the honest trace `polyAL` of a `Row2`
chain `tb` (the honest ALU table: preg rows, the call blocks, padding) satisfies the chip and binds its five
preprocessing columns, from
* the table facts: `hch` (every base gate and `identQ` equation at every row against the next, `tblP_chain`),
  `hlast` (it ends with the padding row), `hhead` (its first row has `sL = 0`), `hLT` (`isLT = 0` throughout),
  `hlen` (it fits in `n` rows);
* `hpre`: the preprocessing `pre` evaluates at the row nodes to the table's `sP / pId / pOp` columns;
* `hden`: no ACTIVE LogUp denominator vanishes at the coins (completeness bad events);
* `hpV hpS hpX`: the three terminal publics are the full LogUp sums;
* the orbit facts `hinj`, `hadj`. -/
theorem aluSZChipJ9_honest_sat (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb (r2AL δ chals tb) ((k : ℕ) + 2) i)
    (hlen : tb.length ≤ n) (hch : List.IsChain (Row2 δ chals) tb)
    (hlast : tb.getLast? = some (padRow, QRow.zero)) (hhead : ∀ x ∈ tb.head?, x.1.sL = 0)
    (hLT : ∀ x ∈ tb, x.1.isLT = 0)
    (hden : ∀ i : Fin n, ((rowAt δ tb i).1.aV ≠ 0 → dV δ chals tb i ≠ 0) ∧
      ((rowAt δ tb i).1.sH + (rowAt δ tb i).1.sP ≠ 0 → dR δ chals tb i ≠ 0 ∧ dO δ chals tb i ≠ 0) ∧
      ((rowAt δ tb i).1.sH ≠ 0 → dJ δ chals tb i ≠ 0 ∧ dX δ chals tb i ≠ 0))
    (hpV : Quad.mk _ (pubs AluSZChipJ9.pubALv) (pubs (AluSZChipJ9.pubALv + 1)) = ∑ i : Fin n, tV δ chals tb i)
    (hpS : Quad.mk _ (pubs AluSZChipJ9.pubALs) (pubs (AluSZChipJ9.pubALs + 1)) = ∑ i : Fin n, tS δ chals tb i)
    (hpX : Quad.mk _ (pubs AluSZChipJ9.pubALx) (pubs (AluSZChipJ9.pubALx + 1)) = ∑ i : Fin n, tX δ chals tb i) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies
        (polyAL δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb)) ∧
      (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing
        (polyAL δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb)) := by
  refine ⟨(expandChip_satisfies_iff_language (AluSZChipJ9.aluTemplateSZ δ) b _ _ orbit _ _).mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hr := aluRows_honest δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb) hinj hadj hpre hlen hch hlast
      hhead hLT i
    have hl := logup_honest δ b hn nodes orbit chals pubs pre tb hinj hpre hadj hden hpV hpS hpX i
    have e1 : (AluSZChipJ9.aluTemplateSZ δ).baseTransition = AluSZChipJ9.baseGates := by
      unfold AluSZChipJ9.aluTemplateSZ; rfl
    have e2 : (AluSZChipJ9.aluTemplateSZ δ).mixedTransition = AluSZChipJ9.aluMixed δ := by
      unfold AluSZChipJ9.aluTemplateSZ; rfl
    rw [e1, e2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hr.1
    · exact fun g hg => absurd (show g ∈ ([] : List (CoeffExpr F)) from hg) List.not_mem_nil
    · exact fun g hg => absurd (show g ∈ ([] : List _) from hg) List.not_mem_nil
    · intro g hg
      have hg' : g ∈ (AluSZChipJ9.aluQ δ).flatMap QE.gates := hg
      obtain ⟨e, he, hg''⟩ := List.mem_flatMap.mp hg'
      have hev : e.ev δ (EKa δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb) i)
          (EFa δ b hn nodes orbit chals pubs pre tb (r2AL δ chals tb) i) = 0 := by
        rcases List.mem_append.mp he with he | he
        · exact hr.2 e he
        · exact hl e he
      rw [QE.ev, Quad.mk_eq_zero_iff] at hev
      simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg''
      rcases hg'' with rfl | rfl
      · exact hev.1
      · exact hev.2
  · have hpp : (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).preprocessing =
        AluSZChipJ9.preOf hn nodes pre := by
      unfold AluSZChipJ9.aluSZChipJ9; rfl
    intro j
    obtain ⟨j, hj⟩ := j
    have hj5 : j < 5 := hj
    have hw : j < (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w := by
      rw [AluSZChipJ9.aluSZ_width_eq]; omega
    have hc : (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).preprocessingColumn ⟨j, hj⟩ = ⟨j, hw⟩ :=
      Fin.ext rfl
    rw [hc, hpp]
    interval_cases j
    · unfold polyAL; rw [dif_neg (by simp), if_neg (by simp [AluSZChipJ9.sL])]; exact honestQ_zero hn nodes _ _
    · unfold polyAL; rw [dif_neg (by simp), if_neg (by simp [AluSZChipJ9.sL])]; exact honestQ_one hn nodes _ _
    · unfold polyAL AluSZChipJ9.preOf; rw [dif_pos (by simp)]; rfl
    · unfold polyAL AluSZChipJ9.preOf; rw [dif_pos (by simp)]; rfl
    · unfold polyAL AluSZChipJ9.preOf; rw [dif_pos (by simp)]; rfl

/-- **Honest acceptance at the honest ALU table `tblP`** (preg rows, the call blocks, one padding row), the gate
satisfaction of each call's block taken as the hypothesis `hblk` (the block obligations `BlockBaseSat` /
`BlockIdentSat`, proved by the four gate groups). -/
theorem aluSZChipJ9_honest_sat_tblP (p : ℕ) (y : Quad (algebraMap F K δ)) (pregs : List (BRow F)) (cls : List CallL)
    (hpreg : ∀ r ∈ pregs, ∃ a b c d : ℕ, r = pregRow a b c d)
    (hblk : ∀ cl ∈ cls, BlockBaseSat (F := F) p cl ∧ BlockIdentSat (K := K) δ p cl)
    (hy : Quad.mk _ (chals 2) (chals 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk _ (chals (40 + 2 * t)) (chals (41 + 2 * t)) = y ^ t)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) =
      colAL δ b (tblP δ p y pregs cls) (r2AL δ chals (tblP δ p y pregs cls)) ((k : ℕ) + 2) i)
    (hlen : (tblP δ p y pregs cls).length ≤ n)
    (hden : ∀ i : Fin n, ((rowAt δ (tblP δ p y pregs cls) i).1.aV ≠ 0 → dV δ chals (tblP δ p y pregs cls) i ≠ 0) ∧
      ((rowAt δ (tblP δ p y pregs cls) i).1.sH + (rowAt δ (tblP δ p y pregs cls) i).1.sP ≠ 0 →
        dR δ chals (tblP δ p y pregs cls) i ≠ 0 ∧ dO δ chals (tblP δ p y pregs cls) i ≠ 0) ∧
      ((rowAt δ (tblP δ p y pregs cls) i).1.sH ≠ 0 →
        dJ δ chals (tblP δ p y pregs cls) i ≠ 0 ∧ dX δ chals (tblP δ p y pregs cls) i ≠ 0))
    (hpV : Quad.mk _ (pubs AluSZChipJ9.pubALv) (pubs (AluSZChipJ9.pubALv + 1)) =
      ∑ i : Fin n, tV δ chals (tblP δ p y pregs cls) i)
    (hpS : Quad.mk _ (pubs AluSZChipJ9.pubALs) (pubs (AluSZChipJ9.pubALs + 1)) =
      ∑ i : Fin n, tS δ chals (tblP δ p y pregs cls) i)
    (hpX : Quad.mk _ (pubs AluSZChipJ9.pubALx) (pubs (AluSZChipJ9.pubALx + 1)) =
      ∑ i : Fin n, tX δ chals (tblP δ p y pregs cls) i) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies
        (polyAL δ b hn nodes orbit chals pubs pre (tblP δ p y pregs cls) (r2AL δ chals (tblP δ p y pregs cls))) ∧
      (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing
        (polyAL δ b hn nodes orbit chals pubs pre (tblP δ p y pregs cls) (r2AL δ chals (tblP δ p y pregs cls))) :=
  aluSZChipJ9_honest_sat δ b hn nodes orbit chals pubs pre _ hinj hadj hpre hlen
    (tblP_chain δ chals p y pregs cls hpreg hblk hy hyp) (tblP_getLast δ p y pregs cls)
    (tblP_head_sL δ p y pregs cls hpreg) (tblP_isLT δ p y pregs cls hpreg) hden hpV hpS hpX

end Sat

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
#print axioms tblP_chain
#print axioms aluRows_honest
#print axioms logup_honest
#print axioms aluSZChipJ9_honest_sat
#print axioms aluSZChipJ9_honest_sat_tblP
end Axioms
