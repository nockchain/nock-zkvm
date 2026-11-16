/-
 Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbFree.lean

 **Honest acceptance of `genJ9ALXJ` with the ALU on any fitting orbit.**

 `GenPortJ9ALHOrb.OrbAdmL` pins the ALU orbit to the generator's own (`ALh : o.AL.h = I.AL.h`), because the ALU's
 next-row gates were unguarded and the honest trace had to wrap from the last row to row `0`. Every next-row
 transition gate of `aluTemplateSZ` now carries the last-row mask `(1 − isLT)`, so the honest trace is accepted on
 any orbit that fits the table (`OrbFits`), as the J-9 A chips already are.

 * §1 the honest last row (`padLT`) is good against EVERY successor row (`padLT_base_any`, `padLT_ident_any`): every
 next-row read is under a current-row selector that is `0` there, under the mask `(1 − isLT) = 0`, or is the
 S terminal `(1 − sL′)·S`, which needs `S1 = S2 = 0` on that row (`lastRow_S_zero`: the honest last row is the
 padding row, whose `𝕂′` roles are `0`);
 * §2 the LogUp lane reads no next-row `sL` (`logupQ_rd`);
 * §3 `polyAL0`: the honest trace with the plain interpolant in the `sL` column (no `AluTraceFix.fixAt`), and
 `sat0_of_sat` / `binds0_of_binds`: it satisfies the chip and binds its preprocessing whenever `polyAL` does;
 * §4 `alChipOK_exec'` / `alE_at'`: `alChipOK_exec` / `alE_at` without the full-orbit hypothesis `hfull`;
 * §5 `OrbAdmL'` (`OrbAdmL` without `ALh`), `validJ9AL_withOrbL'`, `nodes_withOrbL'`, `OrbAdmL.toOrbAdmL'`;
 * §6 `hALk_recL'`, `honest_rec_atJL'`, `genJ9ALXJ_honest_at'`, and `genJ9ALXJ_honest_at_of'` (the height-pinned form, from the fitting-orbit form).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)

noncomputable section

/-! ## 1. The honest last row against every successor -/

section Rows
variable {F : Type} [Field F]

/-- The base gates at a quiet row carrying the last-row mask `isLT = 1`: every gate is `0` against ANY successor
(`quiet_base` with the mask in place of `nxt.sL = 0`). -/
theorem quiet_base_LT (r nxt : BRow F) (hH : r.sH = 0) (hL : r.sL = 0) (hop : ∀ i, r.op i = 0)
    (hro : ∀ i, r.role i = 0) (hmo : ∀ i, r.mode i = 0) (hfst : r.fst = 0) (heos : r.eos = 0) (hf1 : r.f1 = 0)
    (hf2 : r.f2 = 0) (hsf : r.sf = 0) (haV : r.aV = 0) (hcf1 : r.cf1 = 0) (hcf2 : r.cf2 = 0)
    (hbit : ∀ t, r.bit t = 0) (hcn : r.cn = 0) (hcb : ∀ i, r.cb i = 0) (hcA : r.cA = 0) (hcB : r.cB = 0)
    (hsP : r.sP = 0 ∨ r.sP = 1) (hlb : r.lb = 0) (hopc : r.opc = r.pOp) (hid : r.idc = r.pId)
    (hLT : r.isLT = 1) :
    ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB r.col nxt.col) = 0 := by
  have hb : ∀ t < 32, r.col (AluSZChipJ9.bt0 + t) = 0 := fun t ht => (BRow.col_bit r t ht).trans (hbit t)
  have hc : ∀ i < 6, r.col (AluSZChipJ9.cb0 + i) = 0 := fun i hi => (BRow.col_cb r i hi).trans (hcb i)
  have hbN : ∀ t < 32, r.col (34 + t) = 0 := hb
  have hcN : ∀ i < 6, r.col (86 + i) = 0 := hc
  have hc0 : r.col AluSZChipJ9.cb0 = 0 := by simpa using hc 0 (by norm_num)
  have hsP' : r.sP = 0 ∨ r.sP - 1 = 0 := by rcases hsP with h | h <;> simp [h]
  simp only [AluSZChipJ9.baseAG, AluSZChipJ9.gKind, AluSZChipJ9.gSlot, AluSZChipJ9.gSeq, AluSZChipJ9.gCompat,
    AluSZChipJ9.gFlag, AluSZChipJ9.gCoef, AluSZChipJ9.gHdr, AluSZChipJ9.gConst, AluSZChipJ9.gBind,
    AluSZChipJ9.gBits, AluSZChipJ9.gSplit, AluSZChipJ9.gCap, AluSZChipJ9.opCols, AluSZChipJ9.roleCols,
    AluSZChipJ9.modeCols, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_range,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  simp (config := { contextual := true }) [AG.gate, AluSZChipJ9.ar, AluSZChipJ9.succ, AluSZChipJ9.coef,
    AluSZChipJ9.bind, CopyG.gate, Op.expr, CoeffExpr.eval, envB, AluSZChipJ9.prod3, boolE, notE,
    AluSZChipJ9.sumC, AluSZChipJ9.lE, AluSZChipJ9.lN, AluSZChipJ9.cnE, AluSZChipJ9.opCode,
    AluSZChipJ9.gHdrNotLast, AluSZChipJ9.gKS, AluSZChipJ9.gLtP, AluSZChipJ9.gSplitV, AluSZChipJ9.sgnLt,
    AluSZChipJ9.hzV, bitSum, CoeffExpr.eval_sumList, hH, hL, hop, hro, hmo, hfst, heos, hf1, hf2, hsf, haV, hcf1, hcf2, hcn,
    hcA, hcB, hlb, hopc, hid, hLT, hbN, hcN, hb, hc, hc0, hsP', cv, nv, BRow.col_isFT, BRow.col_isLT]
  all_goals
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hc i (List.mem_range.mp hi), mul_zero]

/-- **The honest last row `padLT`: every base gate against ANY successor.** -/
theorem padLT_base_any (nxt : BRow F) :
    ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB (padLT : BRow F).col nxt.col) = 0 :=
  quiet_base_LT _ nxt rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) rfl (fun _ => rfl) rfl rfl (Or.inl rfl) rfl rfl rfl rfl

end Rows

section QRows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The `identQ` equations at a quiet row with zero `𝕂′` roles and the last-row mask `isLT = 1`: every equation is
`0` against ANY successor (`quiet_ident` with the mask in place of `nxt.sL = 0`; the S terminal `(1 − sL′)·S` is `0`
because the row's roles, `S1` and `S2` among them, are `0`). -/
theorem quiet_ident_LT (r nxt : BRow F) (hH : r.sH = 0) (hL : r.sL = 0) (hmo : ∀ i, r.mode i = 0)
    (hfst : r.fst = 0) (heos : r.eos = 0) (hf1 : r.f1 = 0) (hf2 : r.f2 = 0) (hLT : r.isLT = 1)
    (chal : ℕ → K) (nq : ℕ → K) :
    ∀ e ∈ AluSZChipJ9.identQ δ,
      e.ev δ ⟨kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))), nq, chal, fun _ => 0⟩ (envB r.col nxt.col) = 0 := by
  have hz : ∀ j, kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))) j = 0 := kvec_zero δ
  simp only [AluSZChipJ9.identQ, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  simp [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_var, ev_base, ev_mul, ev_next, CoeffExpr.eval, envB, notE,
    AluSZChipJ9.hz, AluSZChipJ9.hzV, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, cv, nv, hH, hL, hmo, hfst, heos,
    hf1, hf2, hLT, hz, liftQ, Quad.mk_zero', BRow.col_isLT]

/-- **The honest last row `padLT`: every `identQ` equation against ANY successor.** -/
theorem padLT_ident_any (nxt : BRow F) (chal nq : ℕ → K) :
    ∀ e ∈ AluSZChipJ9.identQ δ,
      e.ev δ ⟨kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))), nq, chal, fun _ => 0⟩
        (envB (padLT : BRow F).col nxt.col) = 0 :=
  quiet_ident_LT δ _ nxt rfl rfl (fun _ => rfl) rfl rfl rfl rfl rfl chal nq

/-- **`padLT` with zero `𝕂′` roles is good against every successor** (`Row2`, no condition on the successor). -/
theorem padLT_row2_any (chal : ℕ → K) (x' : BRow F × QRow (Quad (algebraMap F K δ))) :
    Row2 δ chal (padLT, QRow.zero) x' :=
  ⟨rowB_of_AG (padLT_base_any x'.1), padLT_ident_any δ x'.1 chal _⟩

end QRows

/-! ## 2. The LogUp lane reads no next-row `sL` -/

section Reads
variable {F : Type} [Field F]

/-- Next-row base columns other than `sL`. -/
def pnNoSL (j : ℕ) : Bool := decide (j ≠ AluSZChipJ9.sL)

/-- Every column, role and coin. -/
def allR (_ : ℕ) : Bool := true

/-- `rdM` with public reads allowed (the LogUp terminals `(1 − sL′)`-free `isLT·(acc − pub)` read a public, which is
the same in both environments). -/
def rdP (kc kn pc pn : ℕ → Bool) : MixedExpr F → Bool
  | .Var .traceCur i => kc i
  | .Var .traceNext i => kn i
  | .Var .challenge _ => true
  | .Var .publicVal _ => true
  | .Lift g => rdB pc pn g
  | .Scale g u => rdB pc pn g && rdP kc kn pc pn u
  | .Const _ => true
  | .Add x y => rdP kc kn pc pn x && rdP kc kn pc pn y
  | .Sub x y => rdP kc kn pc pn x && rdP kc kn pc pn y
  | .Neg x => rdP kc kn pc pn x
  | .Mul x y => rdP kc kn pc pn x && rdP kc kn pc pn y
  | .Pow x _ => rdP kc kn pc pn x

variable {K : Type} [Field K] [Algebra F K]

theorem rdP_eval {kc kn pc pn : ℕ → Bool} {g : MixedExpr F} (hg : rdP kc kn pc pn g = true) {eK eK' : Env K}
    {eF eF' : Env F} (hKt : ∀ i, kc i = true → eK.trace i = eK'.trace i)
    (hKn : ∀ i, kn i = true → eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hKp : eK.pub = eK'.pub)
    (hFt : ∀ j, pc j = true → eF.trace j = eF'.trace j)
    (hFn : ∀ j, pn j = true → eF.traceNext j = eF'.traceNext j) :
    g.eval eK eF = g.eval eK' eF' := by
  induction g with
  | Var k i =>
    cases k <;> simp only [rdP, Bool.false_eq_true] at hg <;> simp only [MixedExpr.eval]
    · exact hKt i hg
    · exact hKn i hg
    · rw [hKc]
    · rw [hKp]
  | Lift g =>
    simp only [rdP] at hg
    simp only [MixedExpr.eval, rdB_eval hg hFt hFn]
  | Scale g u ih =>
    simp only [rdP, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, rdB_eval hg.1 hFt hFn, ih hg.2]
  | Const c => rfl
  | Add x y ihx ihy =>
    simp only [rdP, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Sub x y ihx ihy =>
    simp only [rdP, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Neg x ih =>
    simp only [rdP] at hg
    simp only [MixedExpr.eval, ih hg]
  | Mul x y ihx ihy =>
    simp only [rdP, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Pow x m ih =>
    simp only [rdP] at hg
    simp only [MixedExpr.eval, ih hg]

/-- A `𝕂′` equation with read sets (publics allowed) evaluates congruently. -/
theorem rdP_ev (δ : F) {kc kn pc pn : ℕ → Bool} {e : QE F} (hre : rdP kc kn pc pn e.re = true)
    (him : rdP kc kn pc pn e.im = true) {eK eK' : Env K} {eF eF' : Env F}
    (hKt : ∀ i, kc i = true → eK.trace i = eK'.trace i)
    (hKn : ∀ i, kn i = true → eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hKp : eK.pub = eK'.pub)
    (hFt : ∀ j, pc j = true → eF.trace j = eF'.trace j)
    (hFn : ∀ j, pn j = true → eF.traceNext j = eF'.traceNext j) :
    e.ev δ eK eF = e.ev δ eK' eF' := by
  simp only [QE.ev, rdP_eval hre hKt hKn hKc hKp hFt hFn, rdP_eval him hKt hKn hKc hKp hFt hFn]

/-- **Every LogUp equation reads no next-row `sL`** (any current column, role, coin and public). -/
theorem logupQ_rd (δ : F) : ∀ e ∈ AluSZChipJ9.logupQ δ,
    rdP allR allR allR pnNoSL e.re = true ∧ rdP allR allR allR pnNoSL e.im = true := by
  have h : ((AluSZChipJ9.logupQ δ).all fun e =>
      rdP allR allR allR pnNoSL e.re && rdP allR allR allR pnNoSL e.im) = true := by
    simp (config := {decide := true}) [AluSZChipJ9.logupQ, AluSZChipJ9.invG, AluSZChipJ9.accG, AluSZChipJ9.wS,
      AluSZChipJ9.rdQ, AluSZChipJ9.rdC, AluSZChipJ9.valKey, AluSZChipJ9.sumC, cv, nv,
      AluSZChipJ9.keyRgE, AluSZChipJ9.opRecE, AluSZChipJ9.keyJetE, AluSZChipJ9.keyXE, AluSZChipJ9.keyRgRE,
      AluSZChipJ9.opRecRE, AluSZChipJ9.keyJetRE, AluSZChipJ9.keyXRE, AluSZChipJ9.reE,
      den, QE.add, QE.sub, QE.mul, QE.scale, QE.var, QE.next, QE.base, QE.one, QE.zero, QE.pub, QE.rlc, QE.gpow,
      QE.chal, rQ, notE, rdP, rdB, pnNoSL, allR, CoeffExpr.sumList, AtomChipHQ.zAt, HQ.denKeyQ, HQ.rhoQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ]
  intro e he
  have := List.all_eq_true.mp h e he
  simpa only [Bool.and_eq_true] using this

end Reads

/-! ## 3. The honest trace without the `sL` correction -/

section Poly0
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (pre : Fin 3 → F[X])

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The honest trace with the plain interpolant in the `sL` column** (no `AluTraceFix.fixAt`). -/
def polyAL0 (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) :
    Fin (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w → F[X] := fun j =>
  if hj : 2 ≤ (j : ℕ) ∧ (j : ℕ) < 5 then pre ⟨(j : ℕ) - 2, by omega⟩
  else honestQ hn nodes (colAL δ b tb r2) _ j

abbrev EFa0 (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (i : Fin n) : Env F :=
  Reify.envOfTrace (polyAL0 δ b hn nodes orbit chals pubs pre tb r2) orbit.ω (nodes i) (slotVal b 94 chals)
    (slotVal b 94 pubs)

abbrev EKa0 (tb : List (BRow F × QRow 𝕂′)) (r2 : ℕ → Fin n → K) (i : Fin n) : Env K :=
  gatherEnv b ((AluSZChipJ9.aluTemplateSZ δ).col0 3) (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i)

variable (tb : List (BRow F × QRow (Quad (algebraMap F K δ)))) (r2 : ℕ → Fin n → K)

theorem polyAL_eq0 (j : Fin (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w)
    (hj : (j : ℕ) ≠ AluSZChipJ9.sL) :
    polyAL δ b hn nodes orbit chals pubs pre tb r2 j = polyAL0 δ b hn nodes orbit chals pubs pre tb r2 j := by
  unfold polyAL polyAL0
  split_ifs <;> first | rfl | exact absurd ‹_› hj

theorem polyAL0_eval_node (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (j : Fin (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w) (i : Fin n) :
    (polyAL0 δ b hn nodes orbit chals pubs pre tb r2 j).eval (nodes i) = fullCol hn (colAL δ b tb r2) j i := by
  unfold polyAL0
  split_ifs with h1
  · rw [hpre]
    have e : (j : ℕ) - 2 + 2 = j := by omega
    simp only [fullCol, if_neg (show (j : ℕ) ≠ 0 by omega), if_neg (show (j : ℕ) ≠ 1 by omega), e]
  · exact honestQ_eval hn nodes hinj _ _ i

theorem EFa0_trace_eq (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) :
    (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i).trace =
      (EFa δ b hn nodes orbit chals pubs pre tb r2 i).trace := by
  funext j
  simp only [Reify.envOfTrace]
  split_ifs with hw
  · rw [polyAL0_eval_node δ b hn nodes orbit chals pubs pre tb r2 hinj hpre ⟨j, hw⟩ i,
      polyAL_eval_node δ b hn nodes orbit chals pubs pre tb r2 hinj hpre ⟨j, hw⟩ i]
  · rfl

theorem EFa0_trace (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) {j : ℕ} (hj : j < 196) :
    (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i).trace j = fullCol hn (colAL δ b tb r2) j i := by
  rw [EFa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i]
  exact EFa_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i hj

/-- The next-row reads of the two traces agree off the `sL` column. -/
theorem EFa0_next_ne (i : Fin n) {j : ℕ} (hj : j ≠ AluSZChipJ9.sL) :
    (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i).traceNext j =
      (EFa δ b hn nodes orbit chals pubs pre tb r2 i).traceNext j := by
  simp only [Reify.envOfTrace]
  split_ifs with hw
  · rw [polyAL_eq0 δ b hn nodes orbit chals pubs pre tb r2 ⟨j, hw⟩ hj]
  · rfl

/-- Off the last row the two traces' next-row reads agree everywhere. -/
theorem EFa0_next_of_lt (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i).traceNext =
      (EFa δ b hn nodes orbit chals pubs pre tb r2 i).traceNext := by
  funext j
  simp only [Reify.envOfTrace]
  split_ifs with hw
  · rw [mul_comm, ← hadj i hi, polyAL0_eval_node δ b hn nodes orbit chals pubs pre tb r2 hinj hpre ⟨j, hw⟩ _,
      polyAL_eval_node δ b hn nodes orbit chals pubs pre tb r2 hinj hpre ⟨j, hw⟩ _]
  · rfl

theorem EKa0_trace_eq (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) :
    (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i).trace =
      (EKa δ b hn nodes orbit chals pubs pre tb r2 i).trace := by
  funext r
  simp only [gatherEnv, EFa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i]

theorem EKa0_next_ne (i : Fin n) :
    (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i).traceNext =
      (EKa δ b hn nodes orbit chals pubs pre tb r2 i).traceNext := by
  funext r
  simp only [gatherEnv, ChipTemplate.col0, AluSZChipJ9.aluTemplateSZ_baseCols]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EFa0_next_ne δ b hn nodes orbit chals pubs pre tb r2 i (j := 94 + 3 * r + (k : ℕ))
    (by simp only [AluSZChipJ9.sL]; omega)]

theorem EKa0_chal (i : Fin n) : (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i).chal = chals := by
  funext r
  exact TeleH.gather_chal_T b _ 94 (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ chals rfl r

theorem EKa0_pub (i : Fin n) : (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i).pub = pubs := by
  funext r
  exact TeleH.gather_pub_T b _ 94 (AluSZChipJ9.aluTemplateSZ_baseCols δ) _ pubs rfl r

theorem EKa0_trace (hinj : Function.Injective nodes)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (i : Fin n) {r : ℕ} (hr : r < 34) :
    (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i).trace r = roleK δ tb r2 r i := by
  rw [EKa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i]
  exact EKa_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i hr


theorem env_ext {e e' : Env F} (h1 : e.trace = e'.trace) (h2 : e.traceNext = e'.traceNext) (h3 : e.chal = e'.chal)
    (h4 : e.pub = e'.pub) : e = e' := by
  cases e; cases e'; simp_all

/-- **`S1 = S2 = 0` on the honest last ALU row**: the last row is the padding row, whose `𝕂′` roles are all `0`
(`kvec_zero`). So the S terminal `(1 − sL′)·S` of `identQ` vanishes there whatever the successor's `sL′`. -/
theorem lastRow_S_zero (r : QRow 𝕂′) (hr : r = QRow.zero) :
    kvec δ r AluSZChipJ9.S1 = 0 ∧ kvec δ r AluSZChipJ9.S2 = 0 := by
  subst hr; exact ⟨kvec_zero δ _, kvec_zero δ _⟩

/-- **Row by row: the gates of `polyAL0` from those of `polyAL`** (every base gate and every `𝕂′` equation). Off the
last row the two environments agree. On the last row (the padding row `padLT`, `isLT = 1`) the base gates and the
`identQ` equations vanish against ANY successor (`padLT_row2_any`) and the LogUp equations read no next-row `sL`
(`logupQ_rd`). -/
theorem rowGates0 (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (hlen : tb.length ≤ n) (hlast : tb.getLast? = some (padRow, QRow.zero)) (i : Fin n)
    (hQ : ∀ e ∈ AluSZChipJ9.logupQ δ,
      e.ev δ (EKa δ b hn nodes orbit chals pubs pre tb r2 i) (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0)
    (hB : ∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)),
      g.eval (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0)
    (hI : ∀ e ∈ AluSZChipJ9.identQ δ,
      e.ev δ (EKa δ b hn nodes orbit chals pubs pre tb r2 i) (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0) :
    (∀ g ∈ (AluSZChipJ9.baseGates : List (CoeffExpr F)),
      g.eval (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i) = 0) ∧
    ∀ e ∈ AluSZChipJ9.aluQ δ,
      e.ev δ (EKa0 δ b hn nodes orbit chals pubs pre tb r2 i) (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i) = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · have eF : EFa0 δ b hn nodes orbit chals pubs pre tb r2 i = EFa δ b hn nodes orbit chals pubs pre tb r2 i :=
      env_ext (EFa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i)
        (EFa0_next_of_lt δ b hn nodes orbit chals pubs pre tb r2 hinj hadj hpre i hi) rfl rfl
    have eK : EKa0 δ b hn nodes orbit chals pubs pre tb r2 i = EKa δ b hn nodes orbit chals pubs pre tb r2 i := by
      show gatherEnv b _ (EFa0 δ b hn nodes orbit chals pubs pre tb r2 i) = gatherEnv b _ _
      rw [eF]
    rw [eF, eK]
    exact ⟨hB, fun e he => (List.mem_append.mp he).elim (hI e) (hQ e)⟩
  · have hil : i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := Fin.ext (by simp; omega)
    have hpad : rowAt δ tb (i : ℕ) = (padRow, QRow.zero) := rowAt_pad δ tb hlast _ (by omega)
    have hT := EFa0_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre
    have hK := EKa0_trace δ b hn nodes orbit chals pubs pre tb r2 hinj hpre
    set eF := EFa0 δ b hn nodes orbit chals pubs pre tb r2 i with heF
    set eK := EKa0 δ b hn nodes orbit chals pubs pre tb r2 i with heK
    have h2 : Row2 δ chals (padLT, QRow.zero) (ofColB eF.traceNext, ofKQ δ eK.traceNext) := padLT_row2_any δ chals _
    have hrt := row_transfer δ chals padLT QRow.zero _ eF eK h2 (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
      (fun j hj => ?_) (EKa0_chal δ b hn nodes orbit chals pubs pre tb r2 i)
    · refine ⟨hrt.1, fun e he => ?_⟩
      rcases List.mem_append.mp he with he | he
      · exact hrt.2 e he
      · have hc := hQ e he
        have hr := logupQ_rd δ e he
        rw [← hc]
        refine rdP_ev δ hr.1 hr.2 (fun j _ => ?_) (fun r _ => ?_)
          ((EKa0_chal δ b hn nodes orbit chals pubs pre tb r2 i).trans
            (EKa_chal δ b hn nodes orbit chals pubs pre tb r2 i).symm)
          ((EKa0_pub δ b hn nodes orbit chals pubs pre tb r2 i).trans
            (EKa_pub δ b hn nodes orbit chals pubs pre tb r2 i).symm)
          (fun j _ => ?_) (fun j hj => ?_)
        · rw [EKa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i]
        · rw [EKa0_next_ne δ b hn nodes orbit chals pubs pre tb r2 i]
        · rw [EFa0_trace_eq δ b hn nodes orbit chals pubs pre tb r2 hinj hpre i]
        · exact EFa0_next_ne δ b hn nodes orbit chals pubs pre tb r2 i (by simpa [pnNoSL] using hj)
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

/-- **`sat0_of_sat`: the plain-interpolant trace satisfies the ALU chip whenever the corrected one does** (and the
table fits and ends with the padding row). The two traces agree at every row node; only the next-row read of the
last row differs, in the `sL` column. -/
theorem sat0_of_sat (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ (k : Fin 3) (i : Fin n), (pre k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i)
    (hlen : tb.length ≤ n) (hlast : tb.getLast? = some (padRow, QRow.zero))
    (hsat : (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies
      (polyAL δ b hn nodes orbit chals pubs pre tb r2)) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies
      (polyAL0 δ b hn nodes orbit chals pubs pre tb r2) := by
  have hsat' := (expandChip_satisfies_iff_language (AluSZChipJ9.aluTemplateSZ δ) b _ _ orbit _ _).mp hsat
  refine (expandChip_satisfies_iff_language (AluSZChipJ9.aluTemplateSZ δ) b _ _ orbit _ _).mpr ?_
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
  have hs := hsat' _ hx
  have e1 : (AluSZChipJ9.aluTemplateSZ δ).baseTransition = AluSZChipJ9.baseGates := by
    unfold AluSZChipJ9.aluTemplateSZ; rfl
  have e2 : (AluSZChipJ9.aluTemplateSZ δ).mixedTransition = AluSZChipJ9.aluMixed δ := by
    unfold AluSZChipJ9.aluTemplateSZ; rfl
  rw [e1, e2] at hs ⊢
  have hQ : ∀ e ∈ AluSZChipJ9.aluQ δ,
      e.ev δ (EKa δ b hn nodes orbit chals pubs pre tb r2 i) (EFa δ b hn nodes orbit chals pubs pre tb r2 i) = 0 := by
    intro e he
    rw [QE.ev, Quad.mk_eq_zero_iff]
    exact ⟨hs.2.2.2 _ (List.mem_flatMap.mpr ⟨e, he, by simp [QE.gates]⟩),
      hs.2.2.2 _ (List.mem_flatMap.mpr ⟨e, he, by simp [QE.gates]⟩)⟩
  have hr := rowGates0 δ b hn nodes orbit chals pubs pre tb r2 hinj hadj hpre hlen hlast i
    (fun e he => hQ e (List.mem_append_right _ he)) hs.1
    (fun e he => hQ e (List.mem_append_left _ he))
  refine ⟨hr.1, fun g hg => absurd (show g ∈ ([] : List (CoeffExpr F)) from hg) List.not_mem_nil,
    fun g hg => absurd (show g ∈ ([] : List _) from hg) List.not_mem_nil, ?_⟩
  intro g hg
  have hg' : g ∈ (AluSZChipJ9.aluQ δ).flatMap QE.gates := hg
  obtain ⟨e, he, hg''⟩ := List.mem_flatMap.mp hg'
  have hev := hr.2 e he
  rw [QE.ev, Quad.mk_eq_zero_iff] at hev
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg''
  rcases hg'' with rfl | rfl
  · exact hev.1
  · exact hev.2

/-- **`binds0_of_binds`**: `polyAL0` binds the preprocessing whenever `polyAL` does (the preprocessing columns
`2..4` are not the `sL` column). -/
theorem binds0_of_binds
    (hbind : (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing
      (polyAL δ b hn nodes orbit chals pubs pre tb r2)) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing
      (polyAL0 δ b hn nodes orbit chals pubs pre tb r2) := by
  intro j
  have hj5 : ((AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs pre).preprocessingColumn j : ℕ) < 5 :=
    j.2
  rw [← polyAL_eq0 δ b hn nodes orbit chals pubs pre tb r2 _ (by simp only [AluSZChipJ9.sL]; omega)]
  exact hbind j

end Poly0

/-! ## 4. The executable ALU chip on any fitting orbit -/

section Chip0

open Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE
open Nock.V1J9AL.GenAluE
open Nock.Jet.Prim (PrimOp)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb reorb)
open Nock.V1J8.Gen (chipOf hOf)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]
  [iA : Algebra Nock.Atoms.Fp KQ]

/-- The honest table ends with the padding row. -/
theorem tblP_getLast (y : KQ) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    (tblP (K := KC) deltaF p y pregs cls).getLast? = some (padRow, QRow.zero) := by
  unfold tblP
  exact List.getLast?_concat

/-- **(f) core, any fitting orbit: the executable ALU chip at an admissible orbit `O` (no fullness) is accepted**
(present branch): `alChipOK_exec` without `hfull`, the trace being `polyAL0` (the plain interpolant in `sL`). -/
theorem alChipOK_exec' (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) (vcOf mOf : ℕ → ℕ)
    (hpreg : (pregsOf cs ps ids : List (BRow (ZMod p))) = AluSatPreg.pregsP ps vcOf mOf)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hblk : ∀ cl ∈ callsLOf cs Hm ps pc, BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := KC) deltaF p cl)
    (hsz : (aluRowsB p (pregsOf cs ps ids : List (BRow (ZMod p))) (callsLOf cs Hm ps pc)).length ≤ 2 ^ 31)
    (q : ChipIn) (O : Orb) (hqc : q = reorb (chipOf (aluGenE χe cs Hm ps ids pc).1) O) (ho : OrbOK q)
    (hn0 : 0 < q.n) (hfit : q.n ≤ 3 * 2 ^ q.h)
    (hgood : ∀ e ∈ AluPoles.famAL deltaF
        (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) q.n,
      toχ χe ∉ e.ev)
    (on : Bool) (hon : on = true) (prs : List (ℕ × PrimOp)) (hprs : prs = ps)
    (chals pubs : ℕ → KC) (hch : chals = chalsALJ8 deltaF (toχ χe))
    (hpub : pubs = fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j))
    (pre : Fin 3 → (ZMod p)[X])
    (hpre : ∀ k : Fin 3, pre k =
      Lagrange.interpolate Finset.univ (nodesOf q) (fun i => Nock.V1J9AL.CheckJ9AL.pregCol ps (k : ℕ) (i : ℕ)))
    (P : Fin (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs pre).rap.w →
      (ZMod p)[X])
    (hP : ∀ j, P j = interpOf q (j : ℕ)) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 on prs hn0 (nodesOf q) (mkOrbit q ho) pre chals pubs P := by
  rw [hon, hprs]
  subst hch hpub
  have hTB : tbE (yE χe) (pregsOf cs ps ids) (callsLOf cs Hm ps pc) = tbH χe ps vcOf mOf (callsLOf cs Hm ps pc) := by
    show tblP (K := KC) deltaF p (K6.toQ (yE χe)) (pregsOf cs ps ids) (callsLOf cs Hm ps pc) = _
    rw [toQ_yE_yOf, hpreg]
  have hnE : q.n = NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) := by
    rw [hqc]; exact chipOf_aluGenE_n χe cs Hm ps ids pc O
  have hspec := GenPortJ9AHOrb.hOf_spec _ hsz
  have hlen : (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)).length ≤ q.n := by
    rw [← hTB, tbE_length, hnE]; exact hspec.2.1
  have hnp : q.n < p := by
    have h1 : q.n ≤ 3 * 2 ^ 32 := by
      rw [hnE]; exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) hspec.2.2)
    have h2 : (3 * 2 ^ 32 : ℕ) < p := by norm_num [Nock.Field.p]
    omega
  have hinj : Function.Injective (nodesOf q) := GenPortJ9AHOrb.nodesOf_inj q ho hfit
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [GenPortJ9AHOrb.nodesOf_adj q i hi, mul_comm]; rfl
  have hcol : ∀ (c : ℕ) (i : Fin q.n), c < 196 →
      q.cols c i = fullCol hn0 (colAL deltaF powerBasis3 (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))
        (r2AL (n := q.n) deltaF (chalsALJ8 deltaF (toχ χe)) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)))) c i := by
    intro c i hc
    have hi : (i : ℕ) < NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) := hnE ▸ i.2
    have e1 : q.cols c i = ((aluGenE χe cs Hm ps ids pc).1.getD i #[]).getD c 0 := by subst hqc; rfl
    rw [e1, aluGenE_getD χe cs Hm ps ids pc i hi, cols_eq' χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hn0 hnE i c hc, hTB]
  have hpre' : pre = AluSatPreg.preLOf deltaF (nodesOf q) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)) := by
    rw [← preL_eq_preLOf (nodesOf q) hinj _ ps vcOf mOf (callsLOf cs Hm ps pc) hnoDec hlen]
    exact funext hpre
  subst hpre'
  have hPe : P = polyAL0 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) (chalsALJ8 deltaF (toχ χe))
      (fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j)) (AluSatPreg.preLOf deltaF (nodesOf q) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)))
      (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))
      (r2AL deltaF (chalsALJ8 deltaF (toχ χe)) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))) := by
    funext j
    have hj : (j : ℕ) < 196 := j.2
    rw [hP j]
    unfold polyAL0
    split_ifs with h1
    · unfold AluSatPreg.preLOf interpOf
      congr 1
      funext i
      rw [hcol j i hj]
      simp only [fullCol, if_neg (show (j : ℕ) ≠ 0 by omega), if_neg (show (j : ℕ) ≠ 1 by omega), colAL,
        if_pos (show (j : ℕ) < 94 by omega), show (j : ℕ) - 2 + 2 = j by omega]
    · unfold honestQ interpOf
      congr 1
      funext i
      exact hcol j i hj
  rw [hPe]
  have hV := sumV_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  have hS := sumS_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  have hX := sumX_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  rw [hTB] at hV hS hX
  have hgood' := AluPoles.hden_of_famAL deltaF
    (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) (toχ χe) hgood
  obtain ⟨hs, hb, hpg⟩ := AluSatPreg.aluSZChipJ9_honest_sat_preg deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho)
    (chalsALJ8 deltaF (toχ χe)) (fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j)) p
    (AluPoles.yOf deltaF (toχ χe)) ps vcOf mOf (callsLOf cs Hm ps pc) hnoDec hblk
    (AluSZChipJ9.chalsALJ8_y deltaF (toχ χe))
    (fun t ht => AluSZChipJ9.chalsALJ8_ypow deltaF (toχ χe) t ht) hinj hadj hlen hgood'
    (by rw [← hV, aluGenE_snd]; rfl) (by rw [← hS, aluGenE_snd]; rfl) (by rw [← hX, aluGenE_snd]; rfl)
  have hlenT : (tblP (K := KC) deltaF p (AluPoles.yOf deltaF (toχ χe)) (AluSatPreg.pregsP ps vcOf mOf)
      (callsLOf cs Hm ps pc)).length ≤ q.n := hlen
  exact Or.inl ⟨rfl,
    sat0_of_sat deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) _ _ _ _ _ hinj hadj
      (AluSatPreg.preLOf_hpre deltaF powerBasis3 (nodesOf q) hinj _ _) hlenT (tblP_getLast _ _ _) hs,
    binds0_of_binds deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) _ _ _ _ _ hb, hinj, hadj, hnp, hpg⟩

/-- **`alE_at'`: the `hALk` field of `AcceptsJ9AL` at `mkPbAL I hv`** for an abstract input whose ALU chip is the
executable table at an orbit `O` that merely FITS (`I.AL.n ≤ 3·2^{I.AL.h}`, in place of `alE_at`'s `hfull`). -/
theorem alE_at' (I : Nock.V1J9AL.CheckJ9AL.InJ9AL) (hv : Nock.V1J9AL.CheckJ9ALIff.ValidJ9AL I)
    (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) (vcOf mOf : ℕ → ℕ)
    (hpreg : (pregsOf cs ps ids : List (BRow (ZMod p))) = AluSatPreg.pregsP ps vcOf mOf)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hblk : ∀ cl ∈ callsLOf cs Hm ps pc, BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := KC) deltaF p cl)
    (hsz : (aluRowsB p (pregsOf cs ps ids : List (BRow (ZMod p))) (callsLOf cs Hm ps pc)).length ≤ 2 ^ 31)
    (O : Orb) (hL : I.AL = reorb (chipOf (aluGenE χe cs Hm ps ids pc).1) O)
    (hpL : I.pubsL = (aluGenE χe cs Hm ps ids pc).2)
    (hon : I.aluOn = true) (hpr : I.prims = ps) (hχ : I.χ = χe)
    (hfit : I.AL.n ≤ 3 * 2 ^ I.AL.h)
    (hgood : ∀ e ∈ AluPoles.famAL deltaF
        (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) I.AL.n,
      toχ χe ∉ e.ev) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).aluOn
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).prims (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).hnL
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).nodesL (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).orbitL
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).preL (chalsALJ8 deltaF (toχ I.χ)) I.toMsgL.pubsL
      (RealIOJ9AL.qAL deltaF powerBasis3 (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv) I.toTrL
        (chalsALJ8 deltaF (toχ I.χ)) I.toMsgL.pubsL) :=
  alChipOK_exec' χe cs Hm ps ids pc vcOf mOf hpreg hnoDec hblk hsz I.AL O hL hv.oAL hv.nL hfit hgood
    I.aluOn hon I.prims hpr _ _ (by rw [hχ]) (by funext j; show K3.toK (I.pubsL j) = _; rw [hpL])
    _ (fun k => by show Lagrange.interpolate _ _ _ = _; rw [hpr]) _ (fun j => rfl)

end Chip0

/-! ## 5. Admissible orbits without the ALU pin -/

section Orbs

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (OrbJ9AL withOrbL orbOfL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm OrbFits reorb withOrb orbOf)
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff Nock.V1J9A.CheckJ9AIff

/-- **`OrbAdmL'`**: `GenPortJ9ALHOrb.OrbAdmL` without `ALh : o.AL.h = I.AL.h`. -/
structure OrbAdmL' (I : InJ9AL) (o : OrbJ9AL) : Prop where
  toA : OrbAdm I.toInJ9A o.toA
  AL : OrbFits I.AL o.AL

theorem _root_.Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbAdmL.toOrbAdmL' {I : InJ9AL} {o : OrbJ9AL}
    (h : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbAdmL I o) : OrbAdmL' I o := ⟨h.toA, h.AL⟩

theorem validJ9AL_withOrbL' {I : InJ9AL} {o : OrbJ9AL} (hv : ValidJ9AL I) (ho : OrbAdmL' I o) :
    ValidJ9AL (withOrbL I o) :=
  { Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.validJ9A_withOrb hv.toValidJ9A ho.toA with
    nL := hv.nL, oAL := ho.AL.1 }

theorem nodes_withOrbL' {I : InJ9AL} {o : OrbJ9AL} (ho : OrbAdmL' I o) (hv' : ValidJ9AL (withOrbL I o)) :
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.NodesFields
        (mkPbA (withOrbL I o).toInJ9A hv'.toValidJ9A) ∧
      Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.NodesFieldsL (mkPbAL (withOrbL I o) hv') :=
  ⟨Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.nodes_withOrb ho.toA hv'.toValidJ9A,
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.nodes_ok (reorb I.AL o.AL) ho.AL.1 ho.AL.2⟩

end Orbs

/-! ## 6. The deliverables -/

section Honest0

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb orbOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHLink (IL_AL IL_pubsL IL_aluOn IL_prims)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf rtP)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX
open Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.V1J9AL.GenAluE
open Nock.Jet.Prim (PrimOp primSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ

section Alu0
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (χe : CoinsE)

local notation "RN" => RnOf t r
local notation "CS" => csK Rt s f χe (RnOf t r)
local notation "HM" => HK Rt s f χe (RnOf t r)
local notation "PS" => psCLK Rt prims s f χe (RnOf t r)
local notation "IDS" => idsK Rt s f χe (RnOf t r)
local notation "PC" => pcLK Rt prims s f χe (RnOf t r)
local notation "VC" => ComplJ9ALData.idxPOf (csK Rt s f χe (RnOf t r)) prims
local notation "MR" => ComplJ9ALRun.mRun (t := t) prims
local notation "PSR" => ComplJ9ALRun.psRun (p := P) Rt hgen prims
local notation "VCR" => ComplJ9ALRun.vcRun (p := P) Rt hgen prims
local notation "CLR" => AluSatRun.clsRun (p := P) Rt prims hgen
local notation "TBR" => ComplJ9ALRun.tbR deltaF Rt hgen prims
local notation "ALEN" => ComplJ9ALRun.aluLen (K := KC) deltaF Rt hgen prims
local notation "NLR" => ComplJ9ALRun.nLRun (K := KC) deltaF Rt hgen prims
local notation "TE" => aluGenE χe (csK Rt s f χe (RnOf t r)) (HK Rt s f χe (RnOf t r))
  (psCLK Rt prims s f χe (RnOf t r)) (idsK Rt s f χe (RnOf t r)) (pcLK Rt prims s f χe (RnOf t r))
local notation "IL" => recJ9ALXJ Rt prims s f χe t r

/-- **`hALk` at the record, at any admissible orbit** (present branch when a primitive is called, absent otherwise). -/
theorem hALk_recL' (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (h31L : ALEN < 2 ^ 31) (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 Rt hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL' (IL) o) (hv' : ValidJ9AL (withOrbL (IL) o)) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv').aluOn
      (mkPbAL (withOrbL (IL) o) hv').prims (mkPbAL (withOrbL (IL) o) hv').hnL
      (mkPbAL (withOrbL (IL) o) hv').nodesL (mkPbAL (withOrbL (IL) o) hv').orbitL
      (mkPbAL (withOrbL (IL) o) hv').preL (chalsALJ8 deltaF (toχ (withOrbL (IL) o).χ))
      (withOrbL (IL) o).toMsgL.pubsL
      (RealIOJ9AL.qAL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv') (withOrbL (IL) o).toTrL
        (chalsALJ8 deltaF (toχ (withOrbL (IL) o).χ)) (withOrbL (IL) o).toMsgL.pubsL) := by
  by_cases hpc : PC = []
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · show (IL).aluOn = false
      rw [IL_aluOn]; exact aluOn_false Rt prims χe hpc
    · show (IL).prims = []
      rw [IL_prims, if_neg (by rw [aluOn_false Rt prims χe hpc]; decide)]
    · have hz : (withOrbL (IL) o).toMsgL.pubsL = fun _ => 0 := by
        show (fun i => K3.toK ((lRPLK Rt prims s f χe RN).2 i)) = _
        rw [lRP_off Rt prims χe hpc]; funext i; exact K3.toK_zero
      rw [hz]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
    have hon := aluOn_true Rt prims χe hpc
    have hT := lRP_on Rt prims χe hpc
    have hfam := ComplJ9ALRun.goodAL_famAL deltaF powerBasis3 Rt hgen prims hpG h31A h31 hχ
    have hL : (withOrbL (IL) o).AL = reorb (chipOf TE.1) o.AL := by
      rw [withOrbL_AL, IL_AL, hT]
    have hfit : (withOrbL (IL) o).AL.n ≤ 3 * 2 ^ (withOrbL (IL) o).AL.h := ho.AL.2
    exact alE_at' (withOrbL (IL) o) hv' χe CS HM PS IDS PC VC MR
      (preg_eqR Rt prims χe)
      (fun q hq => hnoDec q (List.mem_filter.mp hq).1)
      (hblkE Rt prims hgen χe hpG h31 hnd hprim hnoDec hlimb)
      (hszE Rt prims hgen χe h31L) o.AL hL
      (by show (lRPLK Rt prims s f χe RN).2 = _; rw [hT])
      (by show aluOnLK Rt prims s f χe RN = true; exact hon)
      (by show (if aluOnLK Rt prims s f χe RN then PS else []) = PS; rw [if_pos hon])
      rfl hfit (hgoodE Rt prims hgen χe hfam _)


end Alu0

section Core0
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt0 : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (χe : CoinsE)

local notation "IL" => recJ9ALXJ (rtP Rt0 prims) prims s f χe t r

/-- **Honest acceptance at any admissible ALU orbit:** for a generated run `IL = recJ9ALXJ …`, at a good coin and an
`OrbAdmL'` orbit, there exists `hv : ValidJ9AL (withOrbL IL o)` such that `AcceptsJ9AL` holds on the overlaid
record. -/
theorem honest_rec_atJL' (hpG : P = Nock.Atoms.p) (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL' (IL) o) :
    ∃ hv : ValidJ9AL (withOrbL (IL) o),
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL (IL) o) hv) Rg.R (withOrbL (IL) o).c
        (toχ (withOrbL (IL) o).χ) (withOrbL (IL) o).toMsgL (withOrbL (IL) o).toTrL (withOrbL (IL) o).toRowsL
        (withOrbL (IL) o).g := by
  -- the honest record and its acceptance
  have hcl := ComplJ9ALClosed.complJ9AL_closed_of deltaF powerBasis3 Rt0 hgen prims hpG hax9 hop5 hleaf hwalk9
    hwalkA hC hnd h31A h31L hlimb hnoDec
  have AH := hcl.1 (toχ χe) hχ
  have NC0 := GenPortJ9ALHNonChip.nonChip_of_acceptsL deltaF powerBasis3 AH
  obtain ⟨hRt, hregAx, hprim⟩ := CheckedRegistryP.hRt_hregAx_ofP hC hgen
  have hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨((rtP Rt0 prims) id).toTemplate P, Nock.Jet.Autogen.compile P ((rtP Rt0 prims) id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB ((rtP Rt0 prims) id) = true ∧ ((rtP Rt0 prims) id).WellTyped P := by
    intro id hid hn
    rw [ComplJ9ALData.rtP_of_not_mem Rt0 prims hn]
    exact hRt id hid hn
  have h31 := ComplJ9ALRun.rows31L_of_A (rtP Rt0 prims) hgen prims h31A
  have hχA := ComplJ9ALClosed.gBA_of deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A (toχ χe) hχ
  have hχ8 := ComplJ9ALClosed.gL_of deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A (toχ χe) hχ
  have L := GenPortJ9AHLinkJ.execLink_recJ9AXJ (rtP Rt0 prims) hgen hpG h31A hax9 hwalk9 hwalkA χe
  -- the ALU chip's shape and validity
  obtain ⟨hnL, hoAL, hAL34, -⟩ := al_shape (rtP Rt0 prims) prims hgen χe h31L
  have hv := validJ9AL_recJ9ALXJ' (rtP Rt0 prims) prims hgen hpG h31A χe hwalk9 hax9 hwalkA hnL hoAL
  have hv' : ValidJ9AL (withOrbL (IL) o) := validJ9AL_withOrbL' hv ho
  refine ⟨hv', ?_⟩
  have hvA : ValidJ9A (withOrb (IL).toInJ9A o.toA) := hv'.toValidJ9A
  have NC := nonChip_recL Rt0 prims hgen χe hpG hax9 hwalk9 hwalkA h31A o hv' hnd h31L NC0
  -- nodes
  obtain ⟨⟨⟨hinjX, hadjX⟩, ⟨hinjC, hadjC⟩, ⟨hinjW, hadjW⟩, ⟨hinjA, hadjA⟩⟩, -⟩ := nodes_withOrbL' ho hv'
  -- budgets
  have H := staticHypJL_withOrbL o (staticHypJL_rec (rtP Rt0 prims) prims (s := s) (f := f) (t := t) (r := r) χe)
  have hb := GenPortJ9ALHStaticJ.budJ9AL_staticJ (withOrbL (IL) o) hv' _ H
  have hbV := GenPortJ9ALHStaticJ.hbudV_staticJL (withOrbL (IL) o) hv' _ H
  have eB : (withOrbL (IL) o).g + (withOrbL (IL) o).toRowsL.N =
      (withOrbL (IL) o).g + max 10 (2 * mLK (rtP Rt0 prims) prims s f χe (RnOf t r)) := by
    show (withOrbL (IL) o).g + (withOrbL (IL) o).r.N = _
    rw [H.hr]; rfl
  -- chips
  have IA_χ : (IL).toInJ9A.χ = χe := (toInJ9A_χ (rtP Rt0 prims) prims s f χe t r).trans L.hχI
  have cell := GenPortJ9ALHCellE.cellE_atL (rtP Rt0 prims) prims hgen hpG h31A hleaf χe (IL).toInJ9A
    ((GenPortJ9ALHLink.IL_C (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg (fun x => chipOf x.1) (GenPortJ9ALHMsgJ.cRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    ((GenPortJ9ALHLink.IL_pubsC (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg Prod.snd (GenPortJ9ALHMsgJ.cRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    o.toA ho.toA hvA hχ8
  have atom := GenPortJ9ALHAtomE.atomE_atL (rtP Rt0 prims) prims hgen hpG h31A χe (IL).toInJ9A
    ((GenPortJ9ALHLink.IL_A (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg (fun x => chipOf x.1) (GenPortJ9ALHMsgJ.aRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    ((GenPortJ9ALHLink.IL_pubsA (rtP Rt0 prims) prims s f χe t r).trans
      (congrArg Prod.snd (GenPortJ9ALHMsgJ.aRPLK_eqL (rtP Rt0 prims) prims hgen χe)))
    o.toA ho.toA hvA hχ8
  have walk := GenPortJ9AHWalkE.walkE_at (rtP Rt0 prims) hgen hwalk9 hpG h31A χe (IL).toInJ9A
    ((toInJ9A_W (rtP Rt0 prims) prims s f χe t r).trans L.hW)
    ((toInJ9A_pubsW (rtP Rt0 prims) prims s f χe t r).trans L.hpW)
    ((toInJ9A_kroots (rtP Rt0 prims) prims s f χe t r).trans L.hkr) o.toA ho.toA hvA hχA
  have jchip := GenPortJ9ALHOrbJ.j_atL (rtP Rt0 prims) prims hgen hpG h31A hRtJ (IL).toInJ9A
    ((GenPortJ9ALHMsgJ.lay_eqL (rtP Rt0 prims) prims hgen χe).trans
      (ComplJ9ALData.jrows_preL (p := P) (rtP Rt0 prims) prims hgen).symm)
    (fun j i _ => by
      rw [cols_of_eqJ _ (GenPortJ9ALHLink.IL_J (rtP Rt0 prims) prims s f χe t r) j i, IA_χ]; rfl)
    ((GenPortJ9ALHLink.IL_pubsJ (rtP Rt0 prims) prims s f χe t r).trans (by rw [IA_χ]; rfl)) o.toA ho.toA hvA hχ8
  exact
    { hsatX := GenPortJ9AHXASE.hsatXE_at (rtP Rt0 prims) hgen hpG h31A hax9 hop5 χe (IL).toInJ9A
        ((toInJ9A_c (rtP Rt0 prims) prims s f χe t r).trans L.hc) IA_χ
        ((toInJ9A_X (rtP Rt0 prims) prims s f χe t r).trans L.hX)
        ((GenPortJ9ALHLink.IL_toMsg_m (rtP Rt0 prims) prims s f χe t r).trans L.hm)
        ((GenPortJ9ALHLink.IL_toMsg_rho (rtP Rt0 prims) prims s f χe t r).trans L.hρ)
        ((GenPortJ9ALHLink.IL_toMsg_rhoS (rtP Rt0 prims) prims s f χe t r).trans L.hρS)
        o.toA ho.toA hvA hχA
      hinjX := hinjX
      hadjX := hadjX
      hsatC := cell.1
      hbindC := cell.2
      hinjC := hinjC
      hadjC := hadjC
      hnpC := NC.hnpC
      hsatW := walk.1
      hbindW := walk.2
      hinjW := hinjW
      hadjW := hadjW
      hkW := NC.hkW
      hknW := NC.hknW
      hkpW := NC.hkpW
      hJk := jchip
      hsatA := atom.1.1
      hbindA := atom.1.2
      hinjA := hinjA
      hadjA := hadjA
      hnpA := NC.hnpA
      hVk := GenPortJ9AHAWE.awE_at (rtP Rt0 prims) hgen hax9 hwalkA hpG h31A χe (IL).toInJ9A IA_χ
        (fun h => ⟨(toInJ9A_V (rtP Rt0 prims) prims s f χe t r).trans (L.hVon h).1,
          (toInJ9A_pubsV (rtP Rt0 prims) prims s f χe t r).trans (L.hVon h).2⟩)
        (fun h => ⟨(toInJ9A_V (rtP Rt0 prims) prims s f χe t r).trans (L.hVoff h).1,
          (toInJ9A_pubsV (rtP Rt0 prims) prims s f χe t r).trans (L.hVoff h).2⟩)
        ((toInJ9A_krootsV (rtP Rt0 prims) prims s f χe t r).trans L.hkrV) o.toA ho.toA hvA hχA
      hGx := NC.hGx
      hGp := NC.hGp
      hGS := NC.hGS
      hlay := NC.hlay
      hsmall := NC.hsmall
      huniq := NC.huniq
      hTpl := NC.hTpl
      hnd := NC.hnd
      hidx := NC.hidx
      hrk := NC.hrk
      hlt := NC.hlt
      hsumC' := NC.hsumC'
      hbalA' := NC.hbalA'
      hvalA0 := NC.hvalA0
      hfxC := NC.hfxC
      hfxA := NC.hfxA
      hclI := NC.hclI
      hclR := NC.hclR
      hcen' := NC.hcen'
      hlenC := NC.hlenC
      hlenA := NC.hlenA
      hcellF := NC.hcellF
      hnAS := NC.hnAS
      hbud := by rw [eB]; exact hb
      hbudV := ⟨hbV.1, hbV.2.1, hbV.2.2.1, hbV.2.2.2.1, hbV.2.2.2.2.1, hbV.2.2.2.2.2.1⟩
      hsatL := atom.2.1
      hbindL := atom.2.2
      hAXk := GenPortJ9AHXASE.hAXkE_at (rtP Rt0 prims) hgen hpG h31A χe (IL).toInJ9A IA_χ
        ((toInJ9A_AX (rtP Rt0 prims) prims s f χe t r).trans L.hAX)
        ((toInJ9A_pubsX (rtP Rt0 prims) prims s f χe t r).trans L.hpX)
        ((toInJ9A_axOn (rtP Rt0 prims) prims s f χe t r).trans L.haxOn)
        ((congrArg ChipIn.n (toInJ9A_AX (rtP Rt0 prims) prims s f χe t r)).trans L.hszAX)
        o.toA ho.toA hvA hχA
      hSPk := GenPortJ9AHXASE.hSPkE_at (rtP Rt0 prims) hgen hpG h31A hax9 χe (IL).toInJ9A IA_χ
        (fun h => ⟨(toInJ9A_SP (rtP Rt0 prims) prims s f χe t r).trans (L.hSPon h).1,
          (toInJ9A_pubsS (rtP Rt0 prims) prims s f χe t r).trans (L.hSPon h).2⟩)
        (fun h => (toInJ9A_pubsS (rtP Rt0 prims) prims s f χe t r).trans (L.hSPoff h))
        ((toInJ9A_spOn (rtP Rt0 prims) prims s f χe t r).trans L.hspOn)
        ((congrArg ChipIn.n (toInJ9A_SP (rtP Rt0 prims) prims s f χe t r)).trans L.hszSP)
        (GenPortJ9ALHMsgJ.n_A_L (rtP Rt0 prims) prims hgen χe)
        o.toA ho.toA hvA hχA
      hlenX := NC.hlenX
      hALk := hALk_recL' (rtP Rt0 prims) prims hgen χe hpG h31A h31L hnd hprim hnoDec hlimb hχ o ho hv'
      hPrim := NC.hPrim
      hdisjP := NC.hdisjP
      hlenL := ⟨NC.hlenL.1, hbV.2.2.2.2.2.2, NC.hlenL.2⟩
      hndP := NC.hndP
      hrkP := NC.hrkP
      hltP := NC.hltP
      hlenCP := NC.hlenCP }


end Core0

section Final0
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9ALXJ_honest_at`**: every `genJ9ALXJ` output, at every admissible per-chip orbit, is valid and accepted
by `AcceptsJ9AL`. Binders: `complJ9AL_closed_of`'s at `Rt := rtP Rt0 prims`, plus `hI` and the coin `hχ`. -/

theorem genJ9ALXJ_honest_at' (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {χe : CoinsE} {I : InJ9AL}
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : OrbAdmL' I o) :
    ∃ hv : ValidJ9AL (withOrbL I o),
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I o) hv) Rg.R (withOrbL I o).c
        (toχ (withOrbL I o).χ) (withOrbL I o).toMsgL (withOrbL I o).toTrL (withOrbL I o).toRowsL
        (withOrbL I o).g := by
  obtain ⟨t', r', hgen', hIeq⟩ := genJ9ALXJ_some hI
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (hgen'.symm.trans hgen))
  rw [h1, h2] at hIeq
  subst hIeq
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact honest_rec_atJL' Rt0 prims hgen χe hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec hχ o ho

/-- **`genJ9ALXJ_honest_at_of'`:** `genJ9ALXJ_honest_at'` at an `OrbAdmL` orbit (the ALU orbit height equals the
generator's). -/
theorem genJ9ALXJ_honest_at_of' (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg (rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {χe : CoinsE} {I : InJ9AL}
    (hI : Nock.V1J9AL.GenJ9ALXJ.genJ9ALXJ Rg.R (rtP Rt0 prims) prims fuel s f χe = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (rtP Rt0 prims) hgen prims hpG h31A).Good (toχ χe))
    (o : OrbJ9AL) (ho : Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb.OrbAdmL I o) :
    ∃ hv : ValidJ9AL (withOrbL I o),
      AcceptsJ9AL.AcceptsJ9AL deltaF powerBasis3 (mkPbAL (withOrbL I o) hv) Rg.R (withOrbL I o).c
        (toχ (withOrbL I o).χ) (withOrbL I o).toMsgL (withOrbL I o).toTrL (withOrbL I o).toRowsL
        (withOrbL I o).g :=
  genJ9ALXJ_honest_at' hgen hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec hI hχ o ho.toOrbAdmL'

end Final0

end Honest0

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbFree
#print axioms padLT_base_any
#print axioms padLT_ident_any
#print axioms padLT_row2_any
#print axioms logupQ_rd
#print axioms lastRow_S_zero
#print axioms sat0_of_sat
#print axioms binds0_of_binds
#print axioms alChipOK_exec'
#print axioms alE_at'
#print axioms OrbAdmL'
#print axioms validJ9AL_withOrbL'
#print axioms nodes_withOrbL'
#print axioms hALk_recL'
#print axioms honest_rec_atJL'
#print axioms genJ9ALXJ_honest_at'
#print axioms genJ9ALXJ_honest_at_of'
end Axioms
