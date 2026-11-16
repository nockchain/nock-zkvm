/-
  Nock/RedTeam/Batch1390Thm54H2CellReadInstrument.lean

  The deployed compute chip's `𝕂` gates are the coordinatewise compile of TYPED sources
  (`correctedFinalComputeAllGates`): `correctedFinalExtGate i` (82), `accAfterChain`,
  `correctedAccAfterStep`, `correctedEndpoint2` (6), `correctedEndpoint4` (1), `formRLamPins` (2);
  `CorrectedComputeSourceObligations` reads them through exactly these trees.

  **Cell level.**  On an accepted row the selector columns `0..10` are a one-hot of the row's
  state and the base columns `11`/`12` are the fixed first/last masks.  `specWith cur nxt t`
  substitutes the known base values (`substBase`) and constant-folds (`simp1`); both steps are
  proved sound for `CorrectedFinalTypedExpr.eval` (`substBase_eval`, `simp1_eval`).  The read set
  of the result is then a read set of the gate ON THAT CELL (`eval_congr_of_reads`).

  Receipts (kernel `decide`, no `native_decide`):
  * `s2_cur_blind`: on a non-first, non-last row of state `s2` (`OP2`), NO typed source reads
    the current row's `𝕂`-roles `6`, `7` (the row's own `e.size`, `e.dyck`, which the `s2` label
    reads at coordinates `7`, `8` and the `s2` child-`2` payload reads at coordinates `7`, `8`).
    Positive control `s2_cur_reads_role0` (role `0`, the subject, is read).
  * `s2_next_blind_but_walkAcc`: when the SUCCESSOR row is of state `s2`, the only typed source
    reading the successor's roles `6`, `7` is `correctedFinalExtGate 75` (`packedWalkAccId`, the
    in-gate walk accumulator step).  Positive control `s2_next_walkAcc_reads`.
-/
import Nock.NockVMROM.Thm54.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1390

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

abbrev TE := CorrectedFinalTypedExpr

/-! ## A. Sound constant folding -/

/-- The integer value of a constant leaf. -/
def isC : TE → Option ℤ
  | .const c => some c
  | _ => none

theorem isC_some {x : TE} {a : ℤ} (h : isC x = some a) : x = .const a := by
  cases x <;> simp_all [isC]

/-- Syntactic equality of two trace leaves (the only cancellation `simp1` performs). -/
def leafEq : TE → TE → Bool
  | .extCur i, .extCur j => i == j
  | .extNext i, .extNext j => i == j
  | _, _ => false

theorem leafEq_eq {x y : TE} (h : leafEq x y = true) : x = y := by
  cases x <;> cases y <;> simp_all [leafEq]

def mkAdd (x y : TE) : TE :=
  match isC x, isC y with
  | some a, some b => .const (a + b)
  | some a, none => if a = 0 then y else .add x y
  | none, some b => if b = 0 then x else .add x y
  | none, none => .add x y

def mkSub (x y : TE) : TE :=
  if leafEq x y then .const 0 else
  match isC x, isC y with
  | some a, some b => .const (a - b)
  | some a, none => if a = 0 then .neg y else .sub x y
  | none, some b => if b = 0 then x else .sub x y
  | none, none => .sub x y

def mkMul (x y : TE) : TE :=
  match isC x, isC y with
  | some a, some b => .const (a * b)
  | some a, none => if a = 0 then .const 0 else if a = 1 then y else .mul x y
  | none, some b => if b = 0 then .const 0 else if b = 1 then x else .mul x y
  | none, none => .mul x y

def mkNeg (x : TE) : TE :=
  match isC x with
  | some a => .const (-a)
  | none => .neg x

def mkPow (x : TE) (n : ℕ) : TE :=
  if n = 0 then .const 1 else
  match isC x with
  | some a => .const (a ^ n)
  | none => .pow x n

/-- Bottom-up constant folding. -/
def simp1 : TE → TE
  | .add x y => mkAdd (simp1 x) (simp1 y)
  | .sub x y => mkSub (simp1 x) (simp1 y)
  | .mul x y => mkMul (simp1 x) (simp1 y)
  | .neg x => mkNeg (simp1 x)
  | .pow x n => mkPow (simp1 x) n
  | t => t

section Sound

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (env : CorrectedFinalTypedEnv F K)

theorem mkAdd_eval (x y : TE) : (mkAdd x y).eval env = x.eval env + y.eval env := by
  unfold mkAdd
  rcases hx : isC x with _ | a <;> rcases hy : isC y with _ | b
  · rfl
  · simp only
    split_ifs with hb
    · rw [isC_some hy, hb]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · simp only
    split_ifs with ha
    · rw [isC_some hx, ha]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · rw [isC_some hx, isC_some hy]; simp [CorrectedFinalTypedExpr.eval]

theorem mkSub_eval (x y : TE) : (mkSub x y).eval env = x.eval env - y.eval env := by
  unfold mkSub
  by_cases hl : leafEq x y = true
  · rw [if_pos hl, leafEq_eq hl]; simp [CorrectedFinalTypedExpr.eval]
  rw [if_neg hl]
  rcases hx : isC x with _ | a <;> rcases hy : isC y with _ | b
  · rfl
  · simp only
    split_ifs with hb
    · rw [isC_some hy, hb]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · simp only
    split_ifs with ha
    · rw [isC_some hx, ha]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · rw [isC_some hx, isC_some hy]; simp [CorrectedFinalTypedExpr.eval]

theorem mkMul_eval (x y : TE) : (mkMul x y).eval env = x.eval env * y.eval env := by
  unfold mkMul
  rcases hx : isC x with _ | a <;> rcases hy : isC y with _ | b
  · rfl
  · simp only
    split_ifs with hb hb1
    · rw [isC_some hy, hb]; simp [CorrectedFinalTypedExpr.eval]
    · rw [isC_some hy, hb1]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · simp only
    split_ifs with ha ha1
    · rw [isC_some hx, ha]; simp [CorrectedFinalTypedExpr.eval]
    · rw [isC_some hx, ha1]; simp [CorrectedFinalTypedExpr.eval]
    · rfl
  · rw [isC_some hx, isC_some hy]; simp [CorrectedFinalTypedExpr.eval]

theorem mkNeg_eval (x : TE) : (mkNeg x).eval env = -x.eval env := by
  unfold mkNeg
  rcases hx : isC x with _ | a
  · rfl
  · rw [isC_some hx]; simp [CorrectedFinalTypedExpr.eval]

theorem mkPow_eval (x : TE) (n : ℕ) : (mkPow x n).eval env = x.eval env ^ n := by
  unfold mkPow
  split_ifs with hn
  · subst hn; simp [CorrectedFinalTypedExpr.eval]
  rcases hx : isC x with _ | a
  · rfl
  · rw [isC_some hx]; simp [CorrectedFinalTypedExpr.eval]

theorem simp1_eval : ∀ t : TE, (simp1 t).eval env = t.eval env
  | .add x y => by
      rw [simp1, mkAdd_eval, simp1_eval x, simp1_eval y]; rfl
  | .sub x y => by
      rw [simp1, mkSub_eval, simp1_eval x, simp1_eval y]; rfl
  | .mul x y => by
      rw [simp1, mkMul_eval, simp1_eval x, simp1_eval y]; rfl
  | .neg x => by
      rw [simp1, mkNeg_eval, simp1_eval x]; rfl
  | .pow x n => by
      rw [simp1, mkPow_eval, simp1_eval x]; rfl
  | .baseCur _ => rfl | .baseNext _ => rfl | .extCur _ => rfl | .extNext _ => rfl
  | .challenge _ => rfl | .extensionPublic _ => rfl | .scalarPublic _ => rfl
  | .const _ => rfl | .certBase _ => rfl | .certExt _ => rfl | .lamPow _ => rfl
  | .expCur => rfl

end Sound

/-! ## B. Substituting the known base cells -/

/-- Replace `baseCur i` / `baseNext i` by the integer constant the row is known to carry. -/
def substBase (cur nxt : ℕ → Option ℤ) : TE → TE
  | .baseCur i => match cur i.val with | some c => .const c | none => .baseCur i
  | .baseNext i => match nxt i.val with | some c => .const c | none => .baseNext i
  | .add x y => .add (substBase cur nxt x) (substBase cur nxt y)
  | .sub x y => .sub (substBase cur nxt x) (substBase cur nxt y)
  | .mul x y => .mul (substBase cur nxt x) (substBase cur nxt y)
  | .neg x => .neg (substBase cur nxt x)
  | .pow x n => .pow (substBase cur nxt x) n
  | t => t

/-- An environment carries the base values `cur` (current row) and `nxt` (successor row). -/
def CarriesBase {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (cur nxt : ℕ → Option ℤ) : Prop :=
  (∀ (i : Fin 13) (c : ℤ), cur i.val = some c → algebraMap F K (env.baseTrace i) = (c : K)) ∧
    (∀ (i : Fin 13) (c : ℤ), nxt i.val = some c → algebraMap F K (env.baseTraceNext i) = (c : K))

theorem substBase_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (cur nxt : ℕ → Option ℤ) (h : CarriesBase env cur nxt) :
    ∀ t : TE, (substBase cur nxt t).eval env = t.eval env
  | .baseCur i => by
      simp only [substBase]
      rcases hc : cur i.val with _ | c
      · rfl
      · simp only [CorrectedFinalTypedExpr.eval]; exact (h.1 i c hc).symm
  | .baseNext i => by
      simp only [substBase]
      rcases hc : nxt i.val with _ | c
      · rfl
      · simp only [CorrectedFinalTypedExpr.eval]; exact (h.2 i c hc).symm
  | .add x y => by
      simp only [substBase, CorrectedFinalTypedExpr.eval, substBase_eval env cur nxt h x,
        substBase_eval env cur nxt h y]
  | .sub x y => by
      simp only [substBase, CorrectedFinalTypedExpr.eval, substBase_eval env cur nxt h x,
        substBase_eval env cur nxt h y]
  | .mul x y => by
      simp only [substBase, CorrectedFinalTypedExpr.eval, substBase_eval env cur nxt h x,
        substBase_eval env cur nxt h y]
  | .neg x => by
      simp only [substBase, CorrectedFinalTypedExpr.eval, substBase_eval env cur nxt h x]
  | .pow x n => by
      simp only [substBase, CorrectedFinalTypedExpr.eval, substBase_eval env cur nxt h x]
  | .extCur _ => rfl | .extNext _ => rfl
  | .challenge _ => rfl | .extensionPublic _ => rfl | .scalarPublic _ => rfl
  | .const _ => rfl | .certBase _ => rfl | .certExt _ => rfl | .lamPow _ => rfl
  | .expCur => rfl

/-- The cell specialization: substitute, then fold. -/
def specWith (cur nxt : ℕ → Option ℤ) (t : TE) : TE := simp1 (substBase cur nxt t)

theorem specWith_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (cur nxt : ℕ → Option ℤ) (h : CarriesBase env cur nxt)
    (t : TE) : (specWith cur nxt t).eval env = t.eval env := by
  rw [specWith, simp1_eval, substBase_eval env cur nxt h]

/-! ## C. Read sets and the congruence they license -/

/-- `𝕂`-roles read on the current row. -/
def curRoles : TE → List ℕ
  | .extCur i => [i.val]
  | .add x y | .sub x y | .mul x y => curRoles x ++ curRoles y
  | .neg x => curRoles x
  | .pow x _ => curRoles x
  | _ => []

/-- `𝕂`-roles read on the successor row. -/
def nextRoles : TE → List ℕ
  | .extNext i => [i.val]
  | .add x y | .sub x y | .mul x y => nextRoles x ++ nextRoles y
  | .neg x => nextRoles x
  | .pow x _ => nextRoles x
  | _ => []

/-- Two environments that differ at most in the current-row roles `R` and successor-row roles `R'`. -/
structure AgreeOff {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env env' : CorrectedFinalTypedEnv F K) (R R' : List ℕ) : Prop where
  base : env'.baseTrace = env.baseTrace
  baseNext : env'.baseTraceNext = env.baseTraceNext
  ext : ∀ i : Fin 63, i.val ∉ R → env'.extTrace i = env.extTrace i
  extNext : ∀ i : Fin 63, i.val ∉ R' → env'.extTraceNext i = env.extTraceNext i
  chal : env'.chal = env.chal
  extPub : env'.extensionPublic = env.extensionPublic
  scalarPub : env'.scalarPublic = env.scalarPublic
  certBase : env'.certBase = env.certBase
  certExt : env'.certExt = env.certExt
  expCol : env'.expCol = env.expCol

theorem eval_congr_of_reads {F K : Type*} [Field F] [Field K] [Algebra F K]
    {env env' : CorrectedFinalTypedEnv F K} {R R' : List ℕ} (h : AgreeOff env env' R R') :
    ∀ t : TE, (∀ r ∈ R, r ∉ curRoles t) → (∀ r ∈ R', r ∉ nextRoles t) →
      t.eval env' = t.eval env
  | .extCur i, h1, _ => by
      have : i.val ∉ R := fun hi => h1 _ hi (by simp [curRoles])
      simp only [CorrectedFinalTypedExpr.eval, h.ext i this]
  | .extNext i, _, h2 => by
      have : i.val ∉ R' := fun hi => h2 _ hi (by simp [nextRoles])
      simp only [CorrectedFinalTypedExpr.eval, h.extNext i this]
  | .add x y, h1, h2 => by
      simp only [CorrectedFinalTypedExpr.eval]
      rw [eval_congr_of_reads h x (fun r hr hx => h1 r hr (by simp [curRoles, hx]))
          (fun r hr hx => h2 r hr (by simp [nextRoles, hx])),
        eval_congr_of_reads h y (fun r hr hy => h1 r hr (by simp [curRoles, hy]))
          (fun r hr hy => h2 r hr (by simp [nextRoles, hy]))]
  | .sub x y, h1, h2 => by
      simp only [CorrectedFinalTypedExpr.eval]
      rw [eval_congr_of_reads h x (fun r hr hx => h1 r hr (by simp [curRoles, hx]))
          (fun r hr hx => h2 r hr (by simp [nextRoles, hx])),
        eval_congr_of_reads h y (fun r hr hy => h1 r hr (by simp [curRoles, hy]))
          (fun r hr hy => h2 r hr (by simp [nextRoles, hy]))]
  | .mul x y, h1, h2 => by
      simp only [CorrectedFinalTypedExpr.eval]
      rw [eval_congr_of_reads h x (fun r hr hx => h1 r hr (by simp [curRoles, hx]))
          (fun r hr hx => h2 r hr (by simp [nextRoles, hx])),
        eval_congr_of_reads h y (fun r hr hy => h1 r hr (by simp [curRoles, hy]))
          (fun r hr hy => h2 r hr (by simp [nextRoles, hy]))]
  | .neg x, h1, h2 => by
      simp only [CorrectedFinalTypedExpr.eval]
      rw [eval_congr_of_reads h x (fun r hr hx => h1 r hr (by simp [curRoles, hx]))
          (fun r hr hx => h2 r hr (by simp [nextRoles, hx]))]
  | .pow x _, h1, h2 => by
      simp only [CorrectedFinalTypedExpr.eval]
      rw [eval_congr_of_reads h x (fun r hr hx => h1 r hr (by simp [curRoles, hx]))
          (fun r hr hx => h2 r hr (by simp [nextRoles, hx]))]
  | .baseCur i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.base]
  | .baseNext i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.baseNext]
  | .challenge i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.chal]
  | .extensionPublic i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.extPub]
  | .scalarPublic i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.scalarPub]
  | .const _, _, _ => rfl
  | .certBase i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.certBase]
  | .certExt i, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.certExt]
  | .lamPow d, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.chal]
  | .expCur, _, _ => by simp only [CorrectedFinalTypedExpr.eval, h.expCol]

/-! ## D. The deployed typed sources and the `s2` cell receipts -/

/-- Every typed tree `CorrectedComputeSourceObligations` reads (`correctedCoreSemanticValue`,
`correctedAuxSemanticValue`, the endpoint and `λ`-pin buckets). -/
def obligationSources : List TE :=
  (List.finRange 82).map correctedFinalExtGate ++ [accAfterChain, correctedAccAfterStep] ++
    correctedEndpoint2 ++ correctedEndpoint4 ++ formRLamPins

/-- One-hot selectors of state index `s` (`opCol`). -/
def oneHotSel (s : ℕ) : ℕ → Option ℤ :=
  fun i => if i < 11 then some (if i = s then 1 else 0) else none

/-- Current row: state `s2` (`opCol.s2 = 2`), not first (`11 ↦ 0`), not last (`12 ↦ 0`). -/
def curS2 : ℕ → Option ℤ :=
  fun i => if i < 11 then oneHotSel 2 i else if i = 11 ∨ i = 12 then some 0 else none

def noBase : ℕ → Option ℤ := fun _ => none

/-- Cell specialization at a non-first, non-last `s2` row. -/
def specCurS2 (t : TE) : TE := specWith curS2 noBase t

/-- Cell specialization when the SUCCESSOR row is of state `s2`. -/
def specNextS2 (t : TE) : TE := specWith noBase (oneHotSel 2) t

set_option maxRecDepth 400000 in
/-- **No typed source reads roles `6`, `7` of a non-first, non-last `s2` row.** -/
theorem s2_cur_blind :
    obligationSources.all (fun t => !((curRoles (specCurS2 t)).contains 6) &&
      !((curRoles (specCurS2 t)).contains 7)) = true := by
  decide

set_option maxRecDepth 400000 in
/-- Positive control: role `0` (the subject `s.size`) IS read at an `s2` row. -/
theorem s2_cur_reads_role0 :
    obligationSources.any (fun t => (curRoles (specCurS2 t)).contains 0) = true := by
  decide

set_option maxRecDepth 400000 in
/-- **When the successor row is `s2`, only the walk accumulator step reads its roles `6`, `7`.** -/
theorem s2_next_blind_but_walkAcc :
    (obligationSources.filter (fun t => (nextRoles (specNextS2 t)).contains 6 ||
      (nextRoles (specNextS2 t)).contains 7)) = [correctedFinalExtGate 75] := by
  decide


/-! ## E. The walk accumulator at an `s2` successor: an RLC-invariant -/

/-- `specNextS2 (correctedFinalExtGate 75)`, printed by the instrument and checked by `decide`
(`walkAccNextS2_eq`).  Roles `6`, `7` of the successor enter only as
`γ⁷·K'6 + γ⁸·K'7` (`γ` = compute slot `10`), once in the successor's label RLC and once in its
child-`2` payload RLC. -/
def walkAccNextS2 : TE :=
  (.sub (.sub (.add (.mul (.extNext 61) (.add (.const 2) (.add (.mul (.pow (.challenge 10) 1) (.extNext 0)) (.add (.mul (.pow (.challenge 10) 2) (.extNext 1)) (.add (.mul (.pow (.challenge 10) 3) (.extNext 2)) (.add (.mul (.pow (.challenge 10) 4) (.extNext 3)) (.add (.mul (.pow (.challenge 10) 5) (.extNext 4)) (.add (.mul (.pow (.challenge 10) 6) (.extNext 5)) (.add (.mul (.pow (.challenge 10) 7) (.extNext 6)) (.add (.mul (.pow (.challenge 10) 8) (.extNext 7)) (.mul (.pow (.challenge 10) 9) (.extNext 8)))))))))))) (.extNext 10)) (.add (.mul (.baseCur 0) (.extCur 10)) (.add (.mul (.baseCur 1) (.extCur 7)) (.add (.mul (.baseCur 2) (.extCur 10)) (.add (.mul (.baseCur 3) (.extCur 19)) (.add (.mul (.baseCur 4) (.extCur 19)) (.add (.mul (.baseCur 5) (.extCur 28)) (.add (.mul (.baseCur 6) (.extCur 28)) (.add (.mul (.baseCur 7) (.extCur 28)) (.add (.mul (.baseCur 8) (.extCur 28)) (.add (.mul (.baseCur 9) (.extCur 28)) (.mul (.baseCur 10) (.extCur 28))))))))))))) (.mul (.add (.mul (.baseCur 0) (.extCur 9)) (.add (.mul (.baseCur 1) (.extCur 6)) (.add (.mul (.baseCur 2) (.extCur 9)) (.add (.mul (.baseCur 3) (.extCur 18)) (.add (.mul (.baseCur 4) (.extCur 18)) (.add (.mul (.baseCur 5) (.extCur 27)) (.add (.mul (.baseCur 6) (.extCur 27)) (.add (.mul (.baseCur 7) (.extCur 27)) (.add (.mul (.baseCur 8) (.extCur 27)) (.add (.mul (.baseCur 9) (.extCur 27)) (.mul (.baseCur 10) (.extCur 27)))))))))))) (.add (.mul (.pow (.challenge 6) 1) (.add (.extNext 11) (.add (.mul (.pow (.challenge 10) 1) (.extNext 0)) (.add (.mul (.pow (.challenge 10) 2) (.extNext 1)) (.add (.mul (.pow (.challenge 10) 3) (.extNext 2)) (.add (.mul (.pow (.challenge 10) 4) (.extNext 42)) (.add (.mul (.pow (.challenge 10) 5) (.extNext 43)) (.add (.mul (.pow (.challenge 10) 6) (.extNext 14)) (.add (.mul (.pow (.challenge 10) 7) (.extNext 15)) (.add (.mul (.pow (.challenge 10) 8) (.extNext 16)) (.mul (.pow (.challenge 10) 9) (.extNext 17)))))))))))) (.add (.mul (.pow (.challenge 6) 2) (.add (.extNext 12) (.add (.mul (.pow (.challenge 10) 1) (.extNext 18)) (.add (.mul (.pow (.challenge 10) 2) (.extNext 19)) (.add (.mul (.pow (.challenge 10) 3) (.extNext 20)) (.add (.mul (.pow (.challenge 10) 4) (.extNext 21)) (.add (.mul (.pow (.challenge 10) 5) (.extNext 22)) (.add (.mul (.pow (.challenge 10) 6) (.extNext 23)) (.add (.mul (.pow (.challenge 10) 7) (.extNext 24)) (.add (.mul (.pow (.challenge 10) 8) (.extNext 25)) (.mul (.pow (.challenge 10) 9) (.extNext 26)))))))))))) (.mul (.pow (.challenge 6) 3) (.add (.extNext 13) (.add (.mul (.pow (.challenge 10) 1) (.extNext 27)) (.add (.mul (.pow (.challenge 10) 2) (.extNext 28)) (.add (.mul (.pow (.challenge 10) 3) (.extNext 29)) (.add (.mul (.pow (.challenge 10) 4) (.extNext 30)) (.add (.mul (.pow (.challenge 10) 5) (.extNext 31)) (.add (.mul (.pow (.challenge 10) 6) (.extNext 26)) (.add (.mul (.pow (.challenge 10) 7) (.extNext 6)) (.add (.mul (.pow (.challenge 10) 8) (.extNext 7)) (.mul (.pow (.challenge 10) 9) (.extNext 8))))))))))))))))

set_option maxRecDepth 400000 in
theorem walkAccNextS2_eq : specNextS2 (correctedFinalExtGate 75) = walkAccNextS2 := by
  decide

section Shift

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The successor-row shift `K'6 ↦ K'6 + γ·d`, `K'7 ↦ K'7 − d` (`γ = chal 10`). -/
def shiftNext (env : CorrectedFinalTypedEnv F K) (d : K) : CorrectedFinalTypedEnv F K :=
  { env with
    extTraceNext := fun i =>
      if i = 6 then env.extTraceNext 6 + env.chal 10 * d
      else if i = 7 then env.extTraceNext 7 - d else env.extTraceNext i }

/-- The current-row shift `K6 ↦ K6 + γ·d`, `K7 ↦ K7 − d`. -/
def shiftCur (env : CorrectedFinalTypedEnv F K) (d : K) : CorrectedFinalTypedEnv F K :=
  { env with
    extTrace := fun i =>
      if i = 6 then env.extTrace 6 + env.chal 10 * d
      else if i = 7 then env.extTrace 7 - d else env.extTrace i }

theorem agreeOff_shiftCur (env : CorrectedFinalTypedEnv F K) (d : K) :
    AgreeOff env (shiftCur env d) [6, 7] [] where
  base := rfl
  baseNext := rfl
  ext := fun i hi => by
    have h6 : i ≠ 6 := fun h => hi (by simp [h])
    have h7 : i ≠ 7 := fun h => hi (by simp [h])
    simp [shiftCur, h6, h7]
  extNext := fun _ _ => rfl
  chal := rfl
  extPub := rfl
  scalarPub := rfl
  certBase := rfl
  certExt := rfl
  expCol := rfl

theorem agreeOff_shiftNext (env : CorrectedFinalTypedEnv F K) (d : K) :
    AgreeOff env (shiftNext env d) [] [6, 7] where
  base := rfl
  baseNext := rfl
  ext := fun _ _ => rfl
  extNext := fun i hi => by
    have h6 : i ≠ 6 := fun h => hi (by simp [h])
    have h7 : i ≠ 7 := fun h => hi (by simp [h])
    simp [shiftNext, h6, h7]
  chal := rfl
  extPub := rfl
  scalarPub := rfl
  certBase := rfl
  certExt := rfl
  expCol := rfl

set_option maxHeartbeats 4000000 in
/-- **The RLC cancellation**: the successor shift leaves the specialized walk step unchanged. -/
theorem walkAccNextS2_shift (env : CorrectedFinalTypedEnv F K) (d : K) :
    walkAccNextS2.eval (shiftNext env d) = walkAccNextS2.eval env := by
  simp only [walkAccNextS2, CorrectedFinalTypedExpr.eval, shiftNext, Fin.reduceEq, if_false,
    if_true]
  ring

end Shift


/-! ## F. Transfer of the whole source obligation -/

section Transfer

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem carriesBase_congr {env env' : CorrectedFinalTypedEnv F K} {cur nxt : ℕ → Option ℤ}
    (hb : env'.baseTrace = env.baseTrace) (hn : env'.baseTraceNext = env.baseTraceNext)
    (h : CarriesBase env cur nxt) : CarriesBase env' cur nxt :=
  ⟨fun i c hc => by rw [hb]; exact h.1 i c hc, fun i c hc => by rw [hn]; exact h.2 i c hc⟩

/-- **Current-row transfer.**  At a non-first, non-last `s2` row, every obligation source is
blind to the current-row shift of roles `6`, `7`. -/
theorem typed_cur_invariant (env : CorrectedFinalTypedEnv F K)
    (hc : CarriesBase env curS2 noBase) (d : K) :
    ∀ t ∈ obligationSources, t.eval (shiftCur env d) = t.eval env := by
  intro t ht
  have hc' : CarriesBase (shiftCur env d) curS2 noBase := carriesBase_congr rfl rfl hc
  have hall := List.all_eq_true.mp s2_cur_blind t ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  have h6 : 6 ∉ curRoles (specCurS2 t) := by simpa using hall.1
  have h7 : 7 ∉ curRoles (specCurS2 t) := by simpa using hall.2
  rw [← specWith_eval (shiftCur env d) curS2 noBase hc' t, ← specWith_eval env curS2 noBase hc t]
  refine eval_congr_of_reads (agreeOff_shiftCur env d) _ ?_ (by simp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h6
  · exact h7

/-- **Successor-row transfer.**  When the successor row is `s2`, every obligation source is
unchanged by the successor shift of roles `6`, `7`: all but the walk accumulator step are blind
to it, and that one is an RLC-invariant (`walkAccNextS2_shift`). -/
theorem typed_next_invariant (env : CorrectedFinalTypedEnv F K)
    (hc : CarriesBase env noBase (oneHotSel 2)) (d : K) :
    ∀ t ∈ obligationSources, t.eval (shiftNext env d) = t.eval env := by
  intro t ht
  have hc' : CarriesBase (shiftNext env d) noBase (oneHotSel 2) := carriesBase_congr rfl rfl hc
  rw [← specWith_eval (shiftNext env d) noBase (oneHotSel 2) hc' t,
    ← specWith_eval env noBase (oneHotSel 2) hc t]
  by_cases h75 : t = correctedFinalExtGate 75
  · subst h75
    change (specNextS2 _).eval _ = (specNextS2 _).eval _
    rw [walkAccNextS2_eq]
    exact walkAccNextS2_shift env d
  · have hnot : t ∉ obligationSources.filter (fun t => (nextRoles (specNextS2 t)).contains 6 ||
        (nextRoles (specNextS2 t)).contains 7) := by
      rw [s2_next_blind_but_walkAcc]; simpa using h75
    have hb : ¬ (((nextRoles (specNextS2 t)).contains 6 ||
        (nextRoles (specNextS2 t)).contains 7) = true) := fun hcon =>
      hnot (List.mem_filter.mpr ⟨ht, hcon⟩)
    have h6 : 6 ∉ nextRoles (specNextS2 t) := fun hm => hb (by simp [hm])
    have h7 : 7 ∉ nextRoles (specNextS2 t) := fun hm => hb (by simp [hm])
    refine eval_congr_of_reads (agreeOff_shiftNext env d) _ (by simp) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7

/-- The base-field gate lists of `correctedFinalComputeAllGates`. -/
noncomputable def baseLists (n : ℕ) : List (CoordinateCompiler.CoeffExpr F) :=
  OptimizedComputeFinal.finalBaseTransitionGates n ++ OptimizedComputeFinal.finalEndpointEqualityChecks ++
    OptimizedComputeRangeCertificate.formRCertificateGates ++ computeExpGates

/-- **The whole source obligation transfers** once the obligation trees, `isLast`, the residual
witnesses and the base-field lists evaluate the same. -/
theorem obligations_transfer [FiniteDimensional F K] {n : ℕ}
    {env env' : CorrectedFinalTypedEnv F K} {envF envF' : Env F}
    (htyped : ∀ t ∈ obligationSources, t.eval env' = t.eval env)
    (hb12 : env'.baseTrace 12 = env.baseTrace 12)
    (hres : ∀ j : CorrectedResidualWitnessId,
      env'.extTrace (residualWitnessRole j) = env.extTrace (residualWitnessRole j))
    (hF : ∀ g ∈ baseLists (F := F) n, CoordinateCompiler.CoeffExpr.eval g envF' =
      CoordinateCompiler.CoeffExpr.eval g envF)
    (h : OptimizedComputeSemanticRealization.CorrectedComputeSourceObligations n env envF) :
    OptimizedComputeSemanticRealization.CorrectedComputeSourceObligations n env' envF' := by
  have hext : ∀ i : CorrectedCoreExtGateId,
      (correctedFinalExtGate i).eval env' = (correctedFinalExtGate i).eval env := fun i =>
    htyped _ (by simp [obligationSources])
  have hchain : accAfterChain.eval env' = accAfterChain.eval env :=
    htyped _ (by simp [obligationSources])
  have hstep : correctedAccAfterStep.eval env' = correctedAccAfterStep.eval env :=
    htyped _ (by simp [obligationSources])
  have hnl : OptimizedComputeSemanticRealization.notLastScalar env' =
      OptimizedComputeSemanticRealization.notLastScalar env := by
    simp [OptimizedComputeSemanticRealization.notLastScalar, hb12]
  have hFm : ∀ L : List (CoordinateCompiler.CoeffExpr F), (∀ g ∈ L, g ∈ baseLists (F := F) n) →
      (∀ g ∈ L, CoordinateCompiler.CoeffExpr.eval g envF = 0) →
        ∀ g ∈ L, CoordinateCompiler.CoeffExpr.eval g envF' = 0 := by
    intro L hL h0 g hg
    rw [hF g (hL g hg)]; exact h0 g hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hFm _ (fun g hg => by simp [baseLists, hg]) h.base15
  · intro i
    have hi := h.extensionCore21 i
    unfold OptimizedComputeSemanticRealization.correctedCoreSemanticValue at hi ⊢
    split_ifs at hi ⊢ <;> simp_all
  · intro j
    have hj := h.residualAux3 j
    unfold OptimizedComputeSemanticRealization.correctedAuxSemanticValue at hj ⊢
    split_ifs at hj ⊢ with hj2
    · rw [hstep]; exact hj
    · have hsrc : (correctedFinalResidualSource j).eval env' =
          (correctedFinalResidualSource j).eval env := by
        fin_cases j
        · exact hext _
        · exact hext _
        · exact absurd rfl hj2
      rw [hres j, hsrc]; exact hj
  · intro t ht; rw [htyped t (by simp [obligationSources, ht])]; exact h.endpointDegreeTwo2 t ht
  · intro t ht; rw [htyped t (by simp [obligationSources, ht])]; exact h.endpointDegreeFour1 t ht
  · exact hFm _ (fun g hg => by simp [baseLists, hg]) h.selectorEquality2
  · exact hFm _ (fun g hg => by simp [baseLists, hg]) h.formR99
  · intro t ht; rw [htyped t (by simp [obligationSources, ht])]; exact h.formRLam t ht
  · exact hFm _ (fun g hg => by simp [baseLists, hg]) h.expGates

end Transfer

end Nock.RedTeam.Batch1390

#print axioms Nock.RedTeam.Batch1390.s2_cur_blind
#print axioms Nock.RedTeam.Batch1390.s2_next_blind_but_walkAcc
#print axioms Nock.RedTeam.Batch1390.walkAccNextS2_shift
#print axioms Nock.RedTeam.Batch1390.typed_cur_invariant
#print axioms Nock.RedTeam.Batch1390.typed_next_invariant
#print axioms Nock.RedTeam.Batch1390.obligations_transfer
