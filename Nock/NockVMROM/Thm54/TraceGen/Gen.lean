/-
  Nock/NockVMROM/Thm54/TraceGen/Gen.lean

  The three-phase worker that emits a
  `GenTrace` for a ROM program, together with the OP1 reproduction gate — the generator, run on the
  fresh program `*[0 [1 5]] = 5`, reproduces the already-verified `Op1Config.exec` compute row.

  The worker is the blueprint's three passes:

  * `genComputeSkeleton` — the DFS emission pass.  It classifies the formula's opcode, and for a
    non-branching opcode emits the pre-seed `ComputeRowSkeleton` and the value-keyed service
    requests, with placeholder timestamp/row columns.  Out-of-ROM opcodes decline via `Except`:
    `OP_10`/`OP_11` are `.error notROM` (`evalFBy` succeeds on `OP_11` but `ComputeTable.State` has
    no `s10`/`s11`, `ComputeTable.lean:142`); an atom formula or an opcode this stage does not yet
    emit is `.error malformed`; fuel `0` is `.error outOfFuel`.

  * `assignExponents` — the exponent pass.  A DFS prefix-sum over `Nock.Framework.recordCount`
    fills each node's `lnPrevExponent`/`lnExponent`/`recordExponent`.  Per-node
    `computeLineAdvance` / `computeRecordOffsets` hold on the assigned DFS tree
    (`assignTree_assignedStampsWellFormed`); they do not need BFS order.  The
    DFS flatten `dfsStamps (assignExponents t)` realises `ComputeLineExponentChain`
    and `ComputeLineStartsAtZero`.  That is **not** `computeLineChain`: the
    skeleton zips BFS `computeSkeletonRows` (`Walk.bfsForest`).  DFS stamp order
    equals BFS stamp order on path trees (`isPathTree`) and on height-1 stars
    (`childrenAreLeaves`: every child is a leaf).  On those families the
    DFS flatten is the `computeRows` list of a compute-only
    `SemanticSkeleton` (`genComputeSemanticSkeleton`), so
    `computeTopology` / `computeStartsAtZero` / `computeLineChain` /
    `computeLineAdvance` / `computeRecordOffsets` hold against
    `computeSkeletonRows`.  Cons-over-two-OP1 is the star theorem, not an
    accident.  They diverge at nested branching (height ≥ 2 with ≥ 2
    non-leaf children).  Do not zip BFS labels with DFS stamps off those
    families.      Path/star families inhabit `SemanticTimestampSkeleton`
    with empty memory (`genComputeTimestampSkeleton_of_isPathTree`,
    `_of_childrenAreLeaves`) and with the OP1/cons/OP0/OP3/OP4,
    two-record-star, OP6 three-record, and OP9 three-record served forests
    (`genOp1TimestampSkeleton_of_isPathTree`,
    `genConsTimestampSkeleton_of_childrenAreLeaves`,
    `genOp0TimestampSkeleton_of_isPathTree`,
    `genOp4TimestampSkeleton_of_isPathTree`,
    `genOp3TimestampSkeleton_of_isPathTree`,
    `genOp5TimestampSkeleton_of_childrenAreLeaves` and the OP7/OP8/OP2
    aliases, `genOp6TimestampSkeleton_of_childrenAreLeaves`,
    `genOp9TimestampSkeleton_of_childrenAreLeaves`); `F`/`Algebra`
    are binders on those inhabitants, not file-level variables.
    Not a `ForestExponentOrder` tick.

  * `renderRows` — the rendering pass.  It fills the `K`-columns of each row from the committed
    skeleton and the assigned exponents via the computable fingerprint `encC` (`= enc`,
    `Encode.encC_eq`), and stamps every service request with `ts = α^recordExponent`.

  `genTraceDFS` composes the three DFS passes and pairs the result with the memory reconstruction
  (`genMemForest`: `OP_1` leaf `[1 v]`, cons `[[1 v] [1 w]]`, the `OP_0` leaf `[0 1]`
  on an atom subject, the unary wrappers `[4 [1 v]]` / `[3 [1 v]]`, the two-record
  stars `[5 [1 v] [1 w]]` / `[7 [1 v] [1 w]]` / `[8 [1 v] [1 w]]` / `[2 [1 v] [1 w]]`,
  the three-record if/branch `[6 [[1 k] [[1 v] [1 w]]]]`, and the three-record invoke
  `[9 [1 [1 [1 v]]]]`).
  Dispatch already matches `OP_0`–`OP_9` and autocons (and declines `OP_10`/`OP_11` as
  `notROM`).  Remaining generator gap is `ForestExponentOrder` (alignment + all-stamps
  `hmemLine` + `hwin`).  That is
  still not a `ForestExponentOrder` tick.
-/
import Nock.NockVMROM.Thm54.TraceGen.Row
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Nock.NockVMROM.Thm54.P8Census
import Nock.Reference

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {K : Type} [Field K]

/-! ## Skeleton construction for the non-branching leaf `OP_1` -/

/-- The `OP_1` compute-row skeleton: a constant that returns the formula
    tail `result`, opening the formula `[head result]` at axis `3` as its single memory record.
    `OP_1` has compute fan-out `0` (`NockVM.lean:158`), so it is a leaf. -/
def genSkelOp1 (subject formula result head : Noun) : ComputeRowSkeleton where
  state := .s1
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => result
    | _ => .atom 0
  subformula := fun _ hi _ => absurd hi (by simp [ComputeTable.fanoutComp])
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, result, 3⟩ else ⟨.atom 0, .atom 0, 0⟩

/-! ## Skeleton construction for the branching autocons `.cons` root (PR-3) -/

/-- The tail noun of a formula cell (`.atom 0` on an atom). -/
def formulaTail : Noun → Noun
  | .cell _ t => t
  | _ => .atom 0

/-- The `.cons` autocons compute-row skeleton: fan-out `2` (the left/right
    subformula branches), one live memory record opening the whole formula `[leftF rightF]` at axis
    `3` with child the right branch.  This is the branching analogue of `genSkelOp1`. -/
def genSkelCons (subject leftF rightF leftR rightR : Noun) : ComputeRowSkeleton where
  state := .cons
  subject := subject
  formula := .cell leftF rightF
  evaluation := .cell leftR rightR
  decomposition := fun slot _ =>
    match slot with
    | .f_h => leftF
    | .f_t => rightF
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subject
      | .formula => leftF
      | .result => leftR
    else
      match slot with
      | .subject => subject
      | .formula => rightF
      | .result => rightR
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨.cell leftF rightF, rightF, 3⟩ else ⟨.atom 0, .atom 0, 0⟩

/-- The `OP_0` axis-read compute-row skeleton: a leaf (compute fan-out `0`,
    no recursive call) committing TWO live memory records — the formula-open record `[formula f_t] @3`
    and the actual slot read `[subject result] @axis`.  `head`/`tail`
    are the formula's head/tail, `result = /[axis subject]` the served slot value. -/
def genSkelOp0 (subject formula head tail result : Noun) (axis : ℕ) : ComputeRowSkeleton where
  state := .s0
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => tail
    | _ => .atom 0
  subformula := fun _ hi _ => absurd hi (by simp [ComputeTable.fanoutComp])
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, tail, 3⟩ else ⟨subject, result, axis⟩

/-- The `OP_4` increment compute-row skeleton: a one-recursive-call branch (the
    sub-evaluation `*[subject b]`) committing the single formula-open record `[formula b] @3`, with
    the increment result as its evaluation.  `callSubject`/`callFormula`/`callResult` are the
    recursive call's `(subject, formula, result)`, exposed as its one compute subformula slot. -/
def genSkelOp4 (subject formula head tail callSubject callFormula callResult result : Noun) :
    ComputeRowSkeleton where
  state := .s4
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => tail
    | _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .subject => callSubject
    | .formula => callFormula
    | .result => callResult
  memoryRecord := fun _ _ => ⟨formula, tail, 3⟩

/-- The `OP_3` cell-test compute-row skeleton: structurally identical to `OP_4`
    (a one-recursive-call branch committing the single formula-open record `[formula b] @3`, its one
    compute subformula slot carrying the recursive call's `(subject, formula, result)`) EXCEPT the
    evaluation is the total cell-test `?` of the call's result (`0` on a cell, `1` on an atom) rather
    than the increment.  `callSubject`/`callFormula`/`callResult` are the recursive call's data. -/
def genSkelOp3 (subject formula head tail callSubject callFormula callResult result : Noun) :
    ComputeRowSkeleton where
  state := .s3
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => tail
    | _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .subject => callSubject
    | .formula => callFormula
    | .result => callResult
  memoryRecord := fun _ _ => ⟨formula, tail, 3⟩

/-! ## Skeleton construction for the fan-out-3 eval `.s2` root (OP2) -/

/-- The `OP_2` eval compute-row skeleton:
    `*[a 2 b c] = *[*[a b] *[a c]]`.  It is the max-width compute row — fan-out `3`
    (`fanoutComp.s2 = 3`) and TWO live memory records (`recordCount.s2 = 2`):

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[2 [b c]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b c]` at axis `2`, the
      first `formula_tail@2` record.

    The tail decomposition is **active** (`decActive.s2.f_th = true`): `f_th ↦ formula_tail_head =
    b`, `f_tt ↦ formula_tail_tail = c`.  The three subformula slots are `(subject, b, sf1)`,
    `(subject, c, sf2)`, and `(sf1, sf2, result)` — the **third child's subject `sf1` is a computed
    evaluation**, not the row subject.  `head` is `.atom 2`; `fTail`,
    `fTh`, `fTt` the formula tail / tail-head / tail-tail; `sf1`, `sf2` the first two calls'
    evaluations; `result` the third call's evaluation. -/
def genSkelOp2 (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    ComputeRowSkeleton where
  state := .s2
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sf1
    else if (i : ℕ) = 1 then
      match slot with
      | .subject => subject
      | .formula => fTt
      | .result => sf2
    else
      match slot with
      | .subject => sf1
      | .formula => sf2
      | .result => result
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩ else ⟨fTail, fTh, 2⟩

/-! ## Skeleton construction for the compose `.s7` root with a threaded subject (OP7) -/

/-- The `OP_7` compose compute-row skeleton:
    `*[a 7 b c] = *[*[a b] c]`.  It is fan-out `2` (`fanoutComp.s7 = 2`) with TWO live memory
    records (`recordCount.s7 = 2`), the same record shape as OP2:

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[7 [b c]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b c]` at axis `2`.

    The tail decomposition is **active** (`decActive.s7.f_th = true`): `f_th ↦ formula_tail_head =
    b`, `f_tt ↦ formula_tail_tail = c`.  AIR `evalV` at `.s7` puts the **consumer** in `sf1` and the **helper** in `sf2`:
    `sf1_s = sf2_e`, `sf1_f = f_tt`, `e = sf1_e`, `sf2_s = s`, `sf2_f = f_th`.  Subformula
    slot `0` is therefore `(sb, c, result)` — the consumer `*[sb c]` whose subject is the
    computed helper result `sb`, not the row subject `a` — and slot `1` is `(subject, b, sb)`
    — the helper `*[a b]`.  DFS still emits children in helper-then-consumer order; slot
    numbering follows the AIR, not emission order.

    `head` is `.atom 7`; `fTail`, `fTh`, `fTt` the formula tail / tail-head / tail-tail (`= [b c]`,
    `b`, `c`); `sb` the helper's evaluation; `result` the consumer's evaluation (the row result). -/
def genSkelOp7 (subject formula head fTail fTh fTt sb result : Noun) :
    ComputeRowSkeleton where
  state := .s7
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => sb
      | .formula => fTt
      | .result => result
    else
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sb
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩ else ⟨fTail, fTh, 2⟩

/-! ## Skeleton construction for the push `.s8` root with an autocons threaded subject (OP8) -/

/-- The `OP_8` push/declare compute-row skeleton:
    `*[a 8 b c] = *[[*[a b] a] c]`.  It is fan-out `2` (`fanoutComp.s8 = 2`) with TWO live memory
    records (`recordCount.s8 = 2`), the same record shape as OP7:

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[8 [b c]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b c]` at axis `2`.

    The tail decomposition is **active** (`decActive.s8.f_th = true`): `f_th ↦ formula_tail_head =
    b`, `f_tt ↦ formula_tail_tail = c`.  AIR `evalV` at `.s8` puts the **consumer** in `sf1` and
    the **helper** in `sf2`: `sf1_s = cons(z, sf2_e, s)`, `sf1_f = f_tt`, `e = sf1_e`,
    `sf2_s = s`, `sf2_f = f_th`.  Subformula slot `0` is therefore
    `(cons(sb, a), c, result)` — the consumer `*[[sb a] c]` whose subject is the autocons
    `[sb a]` — and slot `1` is `(subject, b, sb)` — the helper `*[a b]`.  DFS still emits
    children in helper-then-consumer order; slot numbering follows the AIR.

    `head` is `.atom 8`; `fTail`, `fTh`, `fTt` the formula tail / tail-head / tail-tail (`= [b c]`,
    `b`, `c`); `sb` the helper's evaluation; `result` the consumer's evaluation (the row result). -/
def genSkelOp8 (subject formula head fTail fTh fTt sb result : Noun) :
    ComputeRowSkeleton where
  state := .s8
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => .cell sb subject
      | .formula => fTt
      | .result => result
    else
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sb
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩ else ⟨fTail, fTh, 2⟩

/-! ## Skeleton construction for the equality `.s5` root (OP5) -/

/-- The `OP_5` equality compute-row skeleton:
    `*[a 5 b c] = =[*[a b] *[a c]]`.  It is fan-out `2` (`fanoutComp.s5 = 2`) with TWO live memory
    records (`recordCount.s5 = 2`), the same record shape as OP2/OP7:

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[5 [b c]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b c]` at axis `2`.

    The tail decomposition is **active** (`decActive.s5.f_th = true`, `SemanticStrategy.lean:47`):
    `f_th ↦ formula_tail_head = b`, `f_tt ↦ formula_tail_tail = c`.  Both subformula slots are
    evaluated against the SAME row subject `a` (unlike OP7's threaded second subject): slot `0` is
    `(subject, b, sf1)` — the operand `*[a b]` — and slot `1` is `(subject, c, sf2)` — the operand
    `*[a c]` (per `evalN`, `Reference.lean:99-104`, `evalN subj b`/`evalN subj c`).  The evaluation
    is the equality gate `result = Noun.tis sf1 sf2` — atom `0` when the two operands are equal, atom
    `1` otherwise.

    `head` is `.atom 5`; `fTail`, `fTh`, `fTt` the formula tail / tail-head / tail-tail (`= [b c]`,
    `b`, `c`); `sf1`, `sf2` the two operands' evaluations; `result` the equality gate `tis sf1 sf2`. -/
def genSkelOp5 (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    ComputeRowSkeleton where
  state := .s5
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sf1
    else
      match slot with
      | .subject => subject
      | .formula => fTt
      | .result => sf2
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩ else ⟨fTail, fTh, 2⟩

/-! ## Skeleton construction for the invoke `.s9` root with a served arm fetch (OP9) -/

/-- The `OP_9` invoke compute-row skeleton:
    `*[a 9 b c] = *[*[a c] 2 [0 1] 0 b]` — compute the core `*[a c]`, then invoke the arm fetched at
    axis `b` off that core.  It is fan-out `2` (`fanoutComp.s9 = 2`, `requiredCallRealizations.s9 =
    2`) with **THREE** live memory records (`recordCount.s9 = 3`):

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[9 [b c]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b c]` at axis `2`;
    * `mr3 = ⟨core, arm, axis⟩` — the **served arm fetch**: its root is the
      computed core `sf_evaluation_1` (a MUTATED subject, not a subtree of the formula), its axis is
      the atom `formula_tail_head = b`, its child the fetched arm.

    The tail decomposition is **active** (`decActive.s9.f_th = true`): `f_th ↦ formula_tail_head =
    b` (the axis atom), `f_tt ↦ formula_tail_tail = c`.  The two subformula slots are
    `(subject, c, core)` — the core eval `*[a c]` — and `(core, arm, result)` — the invoke `*[core arm]` whose **subject is the
    computed core and formula the served arm**.  This is the first row whose memory
    record root is a subformula evaluation and whose served forest therefore needs a second root.

    `head` is `.atom 9`; `fTail`, `fTh`, `fTt` the formula tail / tail-head / tail-tail
    (`= [b c]`, `b`, `c`); `core` the core eval `sf1`; `arm` the fetched arm `mem_child_3`; `result`
    the invoke's evaluation (the row result); `axis` the arm-fetch axis `b`. -/
def genSkelOp9 (subject formula head fTail fTh fTt core arm result : Noun) (axis : ℕ) :
    ComputeRowSkeleton where
  state := .s9
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subject
      | .formula => fTt
      | .result => core
    else
      match slot with
      | .subject => core
      | .formula => arm
      | .result => result
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩
    else if (i : ℕ) = 1 then ⟨fTail, fTh, 2⟩
    else ⟨core, arm, axis⟩

/-! ## Skeleton construction for the branch `.s6` root with a value-selected taken child (OP6) -/

/-- The `OP_6` if/branch compute-row skeleton:
    `*[a 6 b c d]` = if `*[a b]` is `0` then `*[a c]` else `*[a d]`.  It is fan-out `2`
    (`fanoutComp.s6 = 2`) with **THREE** live memory records (`recordCount.s6 = 3`):

    * `mr1 = ⟨formula, formula_tail, 3⟩` — open the whole formula `[6 [b [c d]]]` at axis `3`;
    * `mr2 = ⟨formula_tail, formula_tail_head, 2⟩` — open the formula tail `[b [c d]]` at axis `2`
      to expose the condition formula `b`;
    * `mr3 = ⟨formula_tail_tail, formula_tail_tail_head, 2⟩` — open the branch pair `[c d]` at axis
      `2` to expose its head `c`, structurally verifying the `cons(c, d) = f_tt` shape of BOTH
      branch formulas.  This is the served-forest face of "both branches present
      structurally, only one evaluated".

    OP6 is the **only** state whose tail-tail decomposition is active
    (`decActive.s6.f_tth = decActive.s6.f_ttt = true`, `SemanticStrategy.lean:53`):
    `f_th ↦ b`, `f_tt ↦ [c d]`, `f_tth ↦ c`, `f_ttt ↦ d`.  Both branch formulas `c`/`d` are thus
    present as decomposition columns, but only the **taken** branch spawns a compute child.

    The two subformula slots follow the AIR/size-window convention
    (`AIR.evalRExprs_s6_sound`, `SizeWindowCounting.requiredSizeWindowNouns.s6 =
    [skeletonSubformula s 1.result]`): slot `0` is the **taken branch**
    `(subject, taken, result)` — `*[a c]` when the condition is `0`, `*[a d]` when it is `1`, its
    result the row result `e = sf_evaluation_1` — and slot `1` is the **condition**
    `(subject, b, cond)` — `*[a b]`, its result `cond = sf_evaluation_2 ∈ {0,1}` a **1-leaf** atom.  Unlike OP7/OP8 the
    subject `a` is SHARED by both children (no threading); the branch is fully resolved in the
    generator's value-consulting DFS, so exactly one branch — `taken` — is committed as slot `0`.

    `head` is `.atom 6`; `fTail`, `fTh`, `fTt` the formula tail / tail-head / tail-tail
    (`= [b [c d]]`, `b`, `[c d]`); `fTth`, `fTtt` the two branch formulas (`c`, `d`); `cond` the
    condition's evaluation (`atom 0`/`atom 1`); `taken` the value-selected branch formula (`fTth`
    or `fTtt`); `result` the taken branch's evaluation (the row result). -/
def genSkelOp6 (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun) :
    ComputeRowSkeleton where
  state := .s6
  subject := subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => head
    | .f_t => fTail
    | .f_th => fTh
    | .f_tt => fTt
    | .f_tth => fTth
    | .f_ttt => fTtt
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .subject => subject
      | .formula => taken
      | .result => result
    else
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => cond
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then ⟨formula, fTail, 3⟩
    else if (i : ℕ) = 1 then ⟨fTail, fTh, 2⟩
    else ⟨fTt, fTth, 2⟩

/-! ## Placeholder columns before the exponent and render passes -/

/-- A zero fingerprint-row for `st`, before `renderRows` overwrites the `K`-columns. -/
def zeroComputeRow (st : ComputeTable.State) : ComputeTable.State × ComputeTable.DTcomp K :=
  (st, ⟨0, 0, 0, 0, 0⟩,
    { state := st, s := 0, f := 0, e := 0
      sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := 0, ln := 0
      mr1 := ComputeTable.MemRec.zero, mr2 := ComputeTable.MemRec.zero
      mr3 := ComputeTable.MemRec.zero },
    ⟨0, 0, 0, 0, 0, 0⟩)

/-- A placeholder timestamp row for `st` (all exponents `0`), before `assignExponents`. -/
def zeroStamp (st : ComputeTable.State) : ComputeTimestampRow :=
  { state := st, lnPrevExponent := 0, lnExponent := 0, recordExponent := fun _ => 0 }

/-- The pre-seed compute node the DFS pass emits for a skeleton row and its requests. -/
def skelNode (skel : ComputeRowSkeleton) (requests : List (ServiceReq K)) : GenComputeRow K :=
  { skel := skel, stamp := zeroStamp skel.state, row := zeroComputeRow skel.state
    requests := requests }

/-! ## The DFS emission pass -/

/-- The opcode head of a formula, if it is a cell with an atom head. -/
def formulaOpcode : Noun → Option ℕ
  | .cell (.atom op) _ => some op
  | _ => none

/-- **Phase 1 (`genComputeSkeleton`).**  Classify the formula's opcode and emit the pre-seed
    compute tree (skeletons + value-keyed requests, placeholder columns) with the evaluation noun.
    Only the non-branching leaf `OP_1` is emitted in full at this stage. -/
def genComputeSkeleton (fuel : ℕ) (subject formula : Noun) :
    Except GenError (NTree (GenComputeRow K) × Noun) :=
  match fuel with
  | 0 => .error .outOfFuel
  | n + 1 =>
    match formula with
    | .atom _ => .error .malformed
    | .cell (.cell lh lt) rtail =>
      -- autocons (PR-3): `*[a [b c] d] = [*[a [b c]] *[a d]]`; recurse on both branches.
      match genComputeSkeleton n subject (.cell lh lt), genComputeSkeleton n subject rtail with
      | .ok (lTree, lRes), .ok (rTree, rRes) =>
        let skel := genSkelCons subject (.cell lh lt) rtail lRes rRes
        let req : ServiceReq K := ⟨.cell (.cell lh lt) rtail, rtail, 3, 0⟩
        .ok (.node (skelNode skel [req]) [lTree, rTree], .cell lRes rRes)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .cell (.atom op) tail =>
      match op with
      | 1 =>
        -- `OP_1`: constant, returns the formula tail `tail`; head is `.atom 1`.
        let result := tail
        let skel := genSkelOp1 subject formula result (.atom 1)
        let req : ServiceReq K := ⟨formula, result, 3, 0⟩
        .ok (.node (skelNode skel [req]) [], result)
      | 0 =>
        -- `OP_0`: the axis read `*[a 0 b] = /[b a]` — a leaf (0 recursive calls)
        -- with a served axis-descent lookup and TWO committed records (formula-open `@3`, slot `@b`).
        match tail with
        | .atom ax =>
          match Nock.Noun.slot ax subject with
          | some result =>
            let skel := genSkelOp0 subject formula (.atom 0) tail result ax
            let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
            let reqSlot : ServiceReq K := ⟨subject, result, ax, 0⟩
            .ok (.node (skelNode skel [reqOpen, reqSlot]) [], result)
          | none => .error .malformed
        | _ => .error .malformed
      | 4 =>
        -- `OP_4`: the increment `*[a 4 b] = +*[a b]` — one recursive call
        -- (the sub-evaluation `*[a b]`) committing the formula-open record `[formula b] @3`, whose
        -- evaluation is the increment of the call's result.  Its single subformula slot carries the
        -- call's `(subject, formula, result)`.
        match genComputeSkeleton n subject tail with
        | .ok (callTree, callResult) =>
          match Nock.Noun.lus callResult with
          | some result =>
            let skel := genSkelOp4 subject formula (.atom 4) tail subject tail callResult result
            let req : ServiceReq K := ⟨formula, tail, 3, 0⟩
            .ok (.node (skelNode skel [req]) [callTree], result)
          | none => .error .malformed
        | .error e => .error e
      | 3 =>
        -- `OP_3`: the cell-test `*[a 3 b] = ?*[a b]` — one recursive call
        -- (the sub-evaluation `*[a b]`) committing the formula-open record `[formula b] @3`, whose
        -- evaluation is the *total* cell-test `?` of the call's result (`0` on a cell, `1` on an
        -- atom).  Its single subformula slot carries the call's `(subject, formula, result)`.
        match genComputeSkeleton n subject tail with
        | .ok (callTree, callResult) =>
          let result := Noun.wut callResult
          let skel := genSkelOp3 subject formula (.atom 3) tail subject tail callResult result
          let req : ServiceReq K := ⟨formula, tail, 3, 0⟩
          .ok (.node (skelNode skel [req]) [callTree], result)
        | .error e => .error e
      | 2 =>
        -- `OP_2`: eval `*[a 2 b c] = *[*[a b] *[a c]]` — fan-out `3` with TWO
        -- committed records (formula-open `[2 [b c]] @3`, formula-tail `[b c] @2`).  Recurse on
        -- `b = head(n2)` and `c = tail(n2)` for `sf1`/`sf2`, then on `.cell sf1 sf2` (the third
        -- child, whose SUBJECT is the computed `sf1`) for the result.
        match tail with
        | .cell b c =>
          match genComputeSkeleton n subject b, genComputeSkeleton n subject c with
          | .ok (lTree, sf1), .ok (rTree, sf2) =>
            match genComputeSkeleton n sf1 sf2 with
            | .ok (mTree, result) =>
              let skel := genSkelOp2 subject formula (.atom 2) tail b c sf1 sf2 result
              let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
              let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
              .ok (.node (skelNode skel [reqOpen, reqTail]) [lTree, rTree, mTree], result)
            | .error e => .error e
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error .malformed
      | 7 =>
        -- `OP_7`: compose `*[a 7 b c] = *[*[a b] c]` — fan-out `2` with TWO
        -- committed records (formula-open `[7 [b c]] @3`, formula-tail `[b c] @2`).  Recurse on
        -- `b` against the row subject for the helper `sb = *[a b]`, then on `c` against the
        -- **computed helper `sb`** (the threaded subject) for the result `*[sb c]`.
        match tail with
        | .cell b c =>
          match genComputeSkeleton n subject b with
          | .ok (bTree, sb) =>
            match genComputeSkeleton n sb c with
            | .ok (cTree, result) =>
              let skel := genSkelOp7 subject formula (.atom 7) tail b c sb result
              let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
              let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
              .ok (.node (skelNode skel [reqOpen, reqTail]) [bTree, cTree], result)
            | .error e => .error e
          | .error e => .error e
        | _ => .error .malformed
      | 8 =>
        -- `OP_8`: push/declare `*[a 8 b c] = *[[*[a b] a] c]` — fan-out `2` with
        -- TWO committed records (formula-open `[8 [b c]] @3`, formula-tail `[b c] @2`).  Recurse on
        -- `b` against the row subject for the helper `sb = *[a b]`, then on `c` against the AUTOCONS
        -- `[sb a]` (the computed helper PAIRED WITH the original subject — the "push") for the result
        -- `*[[sb a] c]` (the paper; agrees with `evalN`, `Reference.lean:118-123`,
        -- `evalN (.cell sb subj) c`).  OP7 plus one autocons on the threaded subject.
        match tail with
        | .cell b c =>
          match genComputeSkeleton n subject b with
          | .ok (bTree, sb) =>
            match genComputeSkeleton n (.cell sb subject) c with
            | .ok (cTree, result) =>
              let skel := genSkelOp8 subject formula (.atom 8) tail b c sb result
              let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
              let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
              .ok (.node (skelNode skel [reqOpen, reqTail]) [bTree, cTree], result)
            | .error e => .error e
          | .error e => .error e
        | _ => .error .malformed
      | 5 =>
        -- `OP_5`: equality `*[a 5 b c] = =[*[a b] *[a c]]` — fan-out `2` with TWO
        -- committed records (formula-open `[5 [b c]] @3`, formula-tail `[b c] @2`).  Recurse on
        -- `b` and `c` BOTH against the row subject `a` for the two operands `sf1 = *[a b]`,
        -- `sf2 = *[a c]`, then produce the equality gate `Noun.tis sf1 sf2`.
        match tail with
        | .cell b c =>
          match genComputeSkeleton n subject b, genComputeSkeleton n subject c with
          | .ok (bTree, sf1), .ok (cTree, sf2) =>
            let result := Noun.tis sf1 sf2
            let skel := genSkelOp5 subject formula (.atom 5) tail b c sf1 sf2 result
            let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
            let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
            .ok (.node (skelNode skel [reqOpen, reqTail]) [bTree, cTree], result)
          | .error e, _ => .error e
          | _, .error e => .error e
        | _ => .error .malformed
      | 9 =>
        -- `OP_9`: invoke `*[a 9 b c] = *[*[a c] 2 [0 1] 0 b]` — fan-out `2` with
        -- THREE committed records (formula-open `[9 [b c]] @3`, formula-tail `[b c] @2`, and the
        -- served arm fetch `[core arm] @b`).  Recurse on `c` against the row subject for the core
        -- `core = *[a c]`, fetch the arm `slot b core` (the first generator dispatch that consults
        -- `Noun.slot` during emission), then recurse on `.cell core arm` against the **computed
        -- core** (the mutated subject) for the invoke result `*[core arm]`.  The arm-fetch record `⟨core, arm, b⟩` seeds the second served
        -- forest root.
        match tail with
        | .cell (.atom ax) c =>
          match genComputeSkeleton n subject c with
          | .ok (coreTree, core) =>
            match Nock.Noun.slot ax core with
            | some arm =>
              match genComputeSkeleton n core arm with
              | .ok (invokeTree, result) =>
                let skel := genSkelOp9 subject formula (.atom 9) tail (.atom ax) c core arm result ax
                let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
                let reqTail : ServiceReq K := ⟨tail, .atom ax, 2, 0⟩
                let reqArm : ServiceReq K := ⟨core, arm, ax, 0⟩
                .ok (.node (skelNode skel [reqOpen, reqTail, reqArm]) [coreTree, invokeTree], result)
              | .error e => .error e
            | none => .error .malformed
          | .error e => .error e
        | _ => .error .malformed
      | 6 =>
        -- `OP_6`: if/branch `*[a 6 b c d]` = if `*[a b]` is `0` then `*[a c]`
        -- else `*[a d]` — fan-out `2` with THREE committed records (formula-open `[6 [b [c d]]]
        -- @3`, formula-tail `[b [c d]] @2` exposing `b`, branch-pair `[c d] @2` exposing `c`).
        -- This is the FIRST generator arm that consults a computed VALUE to fix the tree shape:
        -- recurse on `b` against the row subject for the condition `cond = *[a b]`, then BRANCH on
        -- that value — `atom 0` selects `c`, `atom 1` selects `d` — and recurse on the TAKEN branch only (against the shared subject
        -- `a`) for the row result.  The untaken branch is present ONLY structurally (the `f_tth`/
        -- `f_ttt` decomposition columns + the third `[c d] @2` record's cons check); it spawns no
        -- compute child.  Slot `0` is the taken branch, slot `1` the condition (the AIR/size-window
        -- convention, `AIR.evalRExprs_s6_sound`).
        match tail with
        | .cell b (.cell c d) =>
          match genComputeSkeleton n subject b with
          | .ok (condTree, cond) =>
            match cond with
            | .atom 0 =>
              match genComputeSkeleton n subject c with
              | .ok (takenTree, result) =>
                let skel := genSkelOp6 subject formula (.atom 6) tail b (.cell c d) c d cond c result
                let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
                let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
                let reqPair : ServiceReq K := ⟨.cell c d, c, 2, 0⟩
                .ok (.node (skelNode skel [reqOpen, reqTail, reqPair]) [condTree, takenTree], result)
              | .error e => .error e
            | .atom 1 =>
              match genComputeSkeleton n subject d with
              | .ok (takenTree, result) =>
                let skel := genSkelOp6 subject formula (.atom 6) tail b (.cell c d) c d cond d result
                let reqOpen : ServiceReq K := ⟨formula, tail, 3, 0⟩
                let reqTail : ServiceReq K := ⟨tail, b, 2, 0⟩
                let reqPair : ServiceReq K := ⟨.cell c d, c, 2, 0⟩
                .ok (.node (skelNode skel [reqOpen, reqTail, reqPair]) [condTree, takenTree], result)
              | .error e => .error e
            | _ => .error .malformed
          | .error e => .error e
        | _ => .error .malformed
      | 10 => .error .notROM
      | 11 => .error .notROM
      | _ => .error .malformed

/-! ## The exponent prefix-sum pass -/

/-- Assign exponents to one node from a running record-count accumulator `acc`:
    `lnPrevExponent := acc`, `lnExponent := acc + recordCount state`, and every requested record is
    stamped with the requesting row's line `acc + 1` (the paper, `mr₁ = (f, f_t, 3,
    ln_prev·α)`, i.e. exponent `acc + 1`). -/
def stampOfAcc (st : ComputeTable.State) (acc : ℕ) : ComputeTimestampRow :=
  match st with
  | .s0 =>
    -- `OP_0` commits TWO records (formula-open `@3` then the slot read `@axis`), so its two
    -- exponents are the consecutive lines `acc+1`, `acc+2`.  This
    -- reproduces `MultiRootHonestCommitment.servedStamp`'s piecewise `fun i => if i = 0 then 2
    -- else 3` at `acc = 1`.
    { state := .s0, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s0
      recordExponent := fun i => if (i : ℕ) = 0 then acc + 1 else acc + 2 }
  | .s2 =>
    -- `OP_2` commits TWO records (formula-open `@3` then the formula-tail `@2`), so its two
    -- exponents are the consecutive lines `acc+1`, `acc+2`.  Same piecewise shape as the `.s0` branch.
    { state := .s2, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s2
      recordExponent := fun i => if (i : ℕ) = 0 then acc + 1 else acc + 2 }
  | .s5 =>
    -- `OP_5` commits TWO records (formula-open `@3` then the formula-tail `@2`), so its two
    -- exponents are the consecutive lines `acc+1`, `acc+2`.  Same
    -- piecewise shape as the `.s0`/`.s2`/`.s7` branches.
    { state := .s5, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s5
      recordExponent := fun i => if (i : ℕ) = 0 then acc + 1 else acc + 2 }
  | .s7 =>
    -- `OP_7` commits TWO records (formula-open `@3` then the formula-tail `@2`), so its two
    -- exponents are the consecutive lines `acc+1`, `acc+2`.  Same
    -- piecewise shape as the `.s0`/`.s2` branches.
    { state := .s7, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s7
      recordExponent := fun i => if (i : ℕ) = 0 then acc + 1 else acc + 2 }
  | .s8 =>
    -- `OP_8` commits TWO records (formula-open `@3` then the formula-tail `@2`), so its two
    -- exponents are the consecutive lines `acc+1`, `acc+2`.  Same
    -- piecewise shape as the `.s0`/`.s2`/`.s7` branches.
    { state := .s8, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s8
      recordExponent := fun i => if (i : ℕ) = 0 then acc + 1 else acc + 2 }
  | .s6 =>
    -- `OP_6` commits THREE records (formula-open `@3`, formula-tail `@2` exposing the condition
    -- formula `b`, then the branch-pair `[c d] @2` exposing `c`), so its three exponents are the
    -- consecutive lines `acc+1`, `acc+2`, `acc+3`.
    -- Same three-record schedule as `.s9`.
    { state := .s6, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s6
      recordExponent := fun i =>
        if (i : ℕ) = 0 then acc + 1 else if (i : ℕ) = 1 then acc + 2 else acc + 3 }
  | .s9 =>
    -- `OP_9` commits THREE records (formula-open `@3`, formula-tail `@2`, then the served arm fetch
    -- `@b`), so its three exponents are the consecutive lines `acc+1`, `acc+2`, `acc+3`.
    { state := .s9, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount .s9
      recordExponent := fun i =>
        if (i : ℕ) = 0 then acc + 1 else if (i : ℕ) = 1 then acc + 2 else acc + 3 }
  | s =>
    { state := s, lnPrevExponent := acc, lnExponent := acc + Nock.Framework.recordCount s
      recordExponent := fun _ => acc + 1 }

/-- `stampOfAcc` realises the two Nat equations `SemanticTimestampSkeleton` asks of every
    compute row: line advance by `recordCount`, and per-record offsets `acc + i + 1`.
    Generator infrastructure, not a `ForestExponentOrder` tick: the skeleton also needs
    BFS chain alignment (`assignExponents` is DFS) and `MemLineIdentification` on memory
    stamps -/
theorem stampOfAcc_state (st : ComputeTable.State) (acc : ℕ) :
    (stampOfAcc st acc).state = st := by
  cases st <;> rfl

theorem stampOfAcc_lnPrevExponent (st : ComputeTable.State) (acc : ℕ) :
    (stampOfAcc st acc).lnPrevExponent = acc := by
  cases st <;> rfl

theorem stampOfAcc_lnExponent (st : ComputeTable.State) (acc : ℕ) :
    (stampOfAcc st acc).lnExponent = acc + Nock.Framework.recordCount st := by
  cases st <;> simp [stampOfAcc, Nock.Framework.recordCount]

/-- `SemanticTimestampSkeleton.computeLineAdvance` at a single `stampOfAcc` row. -/
theorem stampOfAcc_computeLineAdvance (st : ComputeTable.State) (acc : ℕ) :
    (stampOfAcc st acc).lnExponent =
      (stampOfAcc st acc).lnPrevExponent +
        Nock.Framework.recordCount (stampOfAcc st acc).state := by
  rw [stampOfAcc_lnExponent, stampOfAcc_lnPrevExponent, stampOfAcc_state]

/-- `SemanticTimestampSkeleton.computeRecordOffsets` at a single `stampOfAcc` row. -/
theorem stampOfAcc_recordExponent (st : ComputeTable.State) (acc : ℕ)
    (i : Fin 3) (hi : (i : ℕ) < Nock.Framework.recordCount st) :
    (stampOfAcc st acc).recordExponent i = acc + (i : ℕ) + 1 := by
  cases st <;> simp [stampOfAcc, Nock.Framework.recordCount] at hi ⊢
  · split_ifs with h <;> omega
  · omega
  · split_ifs with h <;> omega
  · omega
  · omega
  · split_ifs with h <;> omega
  · split_ifs with h0 h1 <;> omega
  · split_ifs with h <;> omega
  · split_ifs with h <;> omega
  · split_ifs with h0 h1 <;> omega
  · omega

/-- Total number of live memory records over a whole compute subtree (the record-count sum used to
    advance the exponent accumulator across siblings). -/
def subtreeRecordCount : NTree (GenComputeRow K) → ℕ
  | .node g cs => Nock.Framework.recordCount g.skel.state + (cs.map subtreeRecordCount).sum

-- **Phase 2 (`assignExponents`).**  A DFS pre-order prefix-sum over `Nock.Framework.recordCount`
-- that threads the accumulator *across siblings* (via `subtreeRecordCount`), so a node's exponent
-- is the count of records emitted strictly before it in DFS.  Path trees coincide with the paper's
-- BFS line-number order (`Walk.bfsForest`); the first branching opcode (PR-3) is where that
-- coincidence breaks.  Cons-over-two-OP1 currently matches BFS coincidentally, emitting
-- `(0,1,1)`, `(1,2,2)`, `(2,3,3)`.  Do not zip BFS labels with DFS stamps.
mutual
/-- Assign exponents to a compute subtree from a running record-count accumulator `acc`. -/
def assignTree (acc : ℕ) : NTree (GenComputeRow K) → NTree (GenComputeRow K)
  | .node g cs =>
    let g' : GenComputeRow K := { g with stamp := stampOfAcc g.skel.state acc }
    .node g' (assignList (acc + Nock.Framework.recordCount g.skel.state) cs)
/-- Assign exponents across a sibling list, threading `acc` by each subtree's record count. -/
def assignList (acc : ℕ) : List (NTree (GenComputeRow K)) → List (NTree (GenComputeRow K))
  | [] => []
  | t :: ts => assignTree acc t :: assignList (acc + subtreeRecordCount t) ts
end

/-- Assign exponents starting from an empty accumulator. -/
def assignExponents (t : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  assignTree 0 t

/-! ### Tree-lift of `stampOfAcc_*` (generator infrastructure, not a tick)

Per-node `computeLineAdvance` / `computeRecordOffsets` hold on the assigned DFS tree.
They do not need BFS order.  `computeLineChain` / `computeTopology` zip BFS
`computeSkeletonRows` (`Walk.bfsForest`); `assignExponents` is DFS.  Path trees
and height-1 stars coincide with BFS; nested branching is where they diverge.
Do not zip BFS labels with DFS stamps off those families.
This is not a `ForestExponentOrder` tick
-/

theorem assignTree_node (acc : ℕ) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    assignTree acc (.node g cs) =
      .node { g with stamp := stampOfAcc g.skel.state acc }
        (assignList (acc + Nock.Framework.recordCount g.skel.state) cs) :=
  rfl

theorem assignList_nil (acc : ℕ) :
    assignList (K := K) acc [] = [] :=
  rfl

theorem assignList_cons (acc : ℕ) (t : NTree (GenComputeRow K))
    (ts : List (NTree (GenComputeRow K))) :
    assignList acc (t :: ts) =
      assignTree acc t :: assignList (acc + subtreeRecordCount t) ts :=
  rfl

theorem assignTree_root_stamp (acc : ℕ) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    (assignTree acc (.node g cs)).label.stamp =
      stampOfAcc g.skel.state acc := by
  rw [assignTree_node]; rfl

theorem assignTree_root_skel (acc : ℕ) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    (assignTree acc (.node g cs)).label.skel = g.skel := by
  rw [assignTree_node]; rfl

theorem assignTree_root_lnPrevExponent (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    (assignTree acc t).label.stamp.lnPrevExponent = acc := by
  cases t with
  | node g cs =>
    rw [assignTree_root_stamp, stampOfAcc_lnPrevExponent]

/-- Root of `assignExponents` starts at exponent 0.  `ComputeLineStartsAtZero`
    on the DFS flatten is `dfsStamps_assignExponents_startsAtZero` below.
    The BFS list `computeSkeletonRows` is a separate obligation. -/
theorem assignExponents_root_lnPrevExponent (t : NTree (GenComputeRow K)) :
    (assignExponents t).label.stamp.lnPrevExponent = 0 :=
  assignTree_root_lnPrevExponent 0 t

theorem assignTree_root_computeLineAdvance (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    (assignTree acc t).label.stamp.lnExponent =
      (assignTree acc t).label.stamp.lnPrevExponent +
        Nock.Framework.recordCount (assignTree acc t).label.stamp.state := by
  cases t with
  | node g cs =>
    rw [assignTree_root_stamp]
    exact stampOfAcc_computeLineAdvance g.skel.state acc

theorem assignTree_root_computeRecordOffsets (acc : ℕ)
    (t : NTree (GenComputeRow K)) (i : Fin 3)
    (hi : (i : ℕ) <
      Nock.Framework.recordCount (assignTree acc t).label.stamp.state) :
    (assignTree acc t).label.stamp.recordExponent i =
      (assignTree acc t).label.stamp.lnPrevExponent + (i : ℕ) + 1 := by
  cases t with
  | node g cs =>
    rw [assignTree_root_stamp] at hi ⊢
    rw [stampOfAcc_state] at hi
    rw [stampOfAcc_lnPrevExponent, stampOfAcc_recordExponent _ _ i hi]

/-- Local copy of `Checker.NTree.All` (Checker is downstream of Gen).  Every
    assigned label realises `stampOfAcc` at its own `lnPrevExponent`, hence the
    two per-row skeleton Nat equations.  Per-node only: **not** BFS
    `computeLineChain` / `computeTopology` -/
def assignedStampsWellFormed : NTree (GenComputeRow K) → Prop
  | .node g ch =>
      g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent ∧
      ∀ s ∈ ch, assignedStampsWellFormed s
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹s ∈ ch›
  omega

theorem assignedStampsWellFormed_iff (g : GenComputeRow K)
    (ch : List (NTree (GenComputeRow K))) :
    assignedStampsWellFormed (.node g ch) ↔
      g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent ∧
      ∀ s ∈ ch, assignedStampsWellFormed s := by
  constructor
  · intro h
    rw [assignedStampsWellFormed] at h
    exact h
  · intro h
    rwa [assignedStampsWellFormed]

theorem assignedStampsWellFormed_state {t : NTree (GenComputeRow K)}
    (h : assignedStampsWellFormed t) :
    t.label.stamp.state = t.label.skel.state := by
  cases t with
  | node g ch =>
    have heq : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent :=
      (assignedStampsWellFormed_iff g ch |>.mp h).1
    simp [NTree.label_node]
    rw [heq, stampOfAcc_state]

theorem assignedStampsWellFormed_computeLineAdvance
    {t : NTree (GenComputeRow K)} (h : assignedStampsWellFormed t) :
    t.label.stamp.lnExponent =
      t.label.stamp.lnPrevExponent +
        Nock.Framework.recordCount t.label.stamp.state := by
  cases t with
  | node g ch =>
    have heq : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent :=
      (assignedStampsWellFormed_iff g ch |>.mp h).1
    simp [NTree.label_node]
    rw [heq]
    exact stampOfAcc_computeLineAdvance g.skel.state g.stamp.lnPrevExponent

theorem assignedStampsWellFormed_computeRecordOffsets
    {t : NTree (GenComputeRow K)} (h : assignedStampsWellFormed t)
    (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount t.label.stamp.state) :
    t.label.stamp.recordExponent i =
      t.label.stamp.lnPrevExponent + (i : ℕ) + 1 := by
  cases t with
  | node g ch =>
    have heq : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent :=
      (assignedStampsWellFormed_iff g ch |>.mp h).1
    simp [NTree.label_node] at hi ⊢
    have hi' : (i : ℕ) < Nock.Framework.recordCount g.skel.state := by
      rw [heq, stampOfAcc_state] at hi
      exact hi
    rw [heq, stampOfAcc_lnPrevExponent, stampOfAcc_recordExponent _ _ i hi']

/-- A child is strictly smaller than its parent.  Nested `NTree` has no `induction`
    tactic; size is the well-founded measure.  Avoid `simp` on `∈` — nested
    `NTree` membership unfolds without bound. -/
theorem ntree_size_lt_of_mem {LT : Type*} {s : NTree LT}
    {ch : List (NTree LT)} (h : s ∈ ch) :
    s.size < 1 + (ch.map NTree.size).sum := by
  have : s.size ≤ (ch.map NTree.size).sum := by
    induction ch with
    | nil => nomatch h
    | cons t rest ih =>
      rw [List.mem_cons] at h
      cases h with
      | inl heq =>
        subst heq
        rw [List.map_cons]
        exact Nat.le_add_right s.size _
      | inr hrest =>
        rw [List.map_cons]
        exact Nat.le_trans (ih hrest) (Nat.le_add_left _ _)
  omega

theorem assignList_assignedStampsWellFormed
    (acc : ℕ) (ts : List (NTree (GenComputeRow K)))
    (h : ∀ t ∈ ts, ∀ acc', assignedStampsWellFormed (assignTree acc' t)) :
    ∀ s ∈ assignList acc ts, assignedStampsWellFormed s := by
  induction ts generalizing acc with
  | nil =>
    intro s hs
    rw [assignList_nil] at hs
    nomatch hs
  | cons t rest ih =>
    intro s hs
    rw [assignList_cons] at hs
    cases hs with
    | head => exact h t (.head _) acc
    | tail _ hs =>
      exact ih (acc + subtreeRecordCount t)
        (fun t' ht' acc' => h t' (.tail _ ht') acc') s hs

theorem assignTree_assignedStampsWellFormed (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    assignedStampsWellFormed (assignTree acc t) := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)) (acc : ℕ), t.size = n →
      assignedStampsWellFormed (assignTree acc t)
  refine Nat.strong_induction_on (p := p) t.size ?step t acc rfl
  intro n ih t acc hn
  cases t with
  | node g cs =>
    rw [assignTree_node]
    rw [assignedStampsWellFormed_iff]
    constructor
    · simp [stampOfAcc_lnPrevExponent]
    · apply assignList_assignedStampsWellFormed
      intro t' ht' acc'
      refine ih t'.size ?lt t' acc' rfl
      have : (NTree.node g cs).size = 1 + (cs.map NTree.size).sum := by
        rw [NTree.size]
      rw [← hn, this]
      exact ntree_size_lt_of_mem ht'

/-- Tree-wide: every node of `assignExponents t` realises `stampOfAcc` at its
    own `lnPrevExponent`.  Not a `ForestExponentOrder` tick: BFS chain
    alignment and `MemLineIdentification` remain -/
theorem assignExponents_assignedStampsWellFormed
    (t : NTree (GenComputeRow K)) :
    assignedStampsWellFormed (assignExponents t) :=
  assignTree_assignedStampsWellFormed 0 t

/-- Root of `assignExponents` realises `computeLineAdvance` via the tree-wide
    well-formedness predicate (not only the `assignTree_root_*` unfold).
    Same equation holds at every assigned node.  Not a tick -/
theorem assignExponents_label_computeLineAdvance
    (t : NTree (GenComputeRow K)) :
    (assignExponents t).label.stamp.lnExponent =
      (assignExponents t).label.stamp.lnPrevExponent +
        Nock.Framework.recordCount (assignExponents t).label.stamp.state :=
  assignedStampsWellFormed_computeLineAdvance
    (assignExponents_assignedStampsWellFormed t)

/-- Root of `assignExponents` realises `computeRecordOffsets` via the tree-wide
    well-formedness predicate.  Not a tick -/
theorem assignExponents_label_computeRecordOffsets
    (t : NTree (GenComputeRow K)) (i : Fin 3)
    (hi : (i : ℕ) <
      Nock.Framework.recordCount (assignExponents t).label.stamp.state) :
    (assignExponents t).label.stamp.recordExponent i =
      (assignExponents t).label.stamp.lnPrevExponent + (i : ℕ) + 1 :=
  assignedStampsWellFormed_computeRecordOffsets
    (assignExponents_assignedStampsWellFormed t) i hi

theorem assignedStampsWellFormed_children
    {t : NTree (GenComputeRow K)} (h : assignedStampsWellFormed t) :
    ∀ s ∈ t.children, assignedStampsWellFormed s := by
  cases t with
  | node g ch =>
    intro s hs
    exact (assignedStampsWellFormed_iff g ch |>.mp h).2 s hs

theorem assignExponents_children_assignedStampsWellFormed
    (t : NTree (GenComputeRow K)) :
    ∀ s ∈ (assignExponents t).children, assignedStampsWellFormed s :=
  assignedStampsWellFormed_children (assignExponents_assignedStampsWellFormed t)

/-! ### DFS prefix-sum: children and siblings

`assignTree` writes the node's stamp at `acc` and starts the first child at
`acc + recordCount`.  The next sibling starts at `acc + subtreeRecordCount t`.
Stamps change under assignment; skeleton / `recordCount` do not, so
`subtreeRecordCount` is invariant.  Still DFS, still not a
`ForestExponentOrder` tick
-/

theorem subtreeRecordCount_node (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    subtreeRecordCount (.node g cs) =
      Nock.Framework.recordCount g.skel.state + (cs.map subtreeRecordCount).sum := by
  rw [subtreeRecordCount]

theorem assignTree_children (acc : ℕ) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    (assignTree acc (.node g cs)).children =
      assignList (acc + Nock.Framework.recordCount g.skel.state) cs := by
  rw [assignTree_node, NTree.children_node]

theorem assignTree_children_cons (acc : ℕ) (g : GenComputeRow K)
    (t : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    (assignTree acc (.node g (t :: ts))).children =
      assignTree (acc + Nock.Framework.recordCount g.skel.state) t ::
        assignList (acc + Nock.Framework.recordCount g.skel.state +
          subtreeRecordCount t) ts := by
  rw [assignTree_children, assignList_cons]

/-- First child of an assigned node is the subtree assigned from
    `acc + recordCount` -/
theorem assignTree_firstChild_eq (acc : ℕ) (g : GenComputeRow K)
    (t : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    (assignTree acc (.node g (t :: ts))).children.head? =
      some (assignTree (acc + Nock.Framework.recordCount g.skel.state) t) := by
  rw [assignTree_children_cons, List.head?_cons]

/-- First child of the assigned parent starts at `acc + recordCount` -/
theorem assignTree_firstChild_lnPrevExponent (acc : ℕ) (g : GenComputeRow K)
    (t : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    ((assignTree acc (.node g (t :: ts))).children.head?.map
      fun s => s.label.stamp.lnPrevExponent) =
      some (acc + Nock.Framework.recordCount g.skel.state) := by
  rw [assignTree_firstChild_eq, Option.map_some]
  exact congrArg some (assignTree_root_lnPrevExponent _ t)

/-- After assigning `t` from `acc`, the remaining siblings start at
    `acc + subtreeRecordCount t` -/
theorem assignList_tail (acc : ℕ) (t : NTree (GenComputeRow K))
    (ts : List (NTree (GenComputeRow K))) :
    (assignList acc (t :: ts)).tail =
      assignList (acc + subtreeRecordCount t) ts := by
  rw [assignList_cons, List.tail_cons]

theorem assignList_next_eq (acc : ℕ) (t u : NTree (GenComputeRow K))
    (ts : List (NTree (GenComputeRow K))) :
    (assignList acc (t :: u :: ts)).tail.head? =
      some (assignTree (acc + subtreeRecordCount t) u) := by
  rw [assignList_tail, assignList_cons, List.head?_cons]

theorem assignList_next_lnPrevExponent (acc : ℕ)
    (t u : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    ((assignList acc (t :: u :: ts)).tail.head?.map
      fun s => s.label.stamp.lnPrevExponent) =
      some (acc + subtreeRecordCount t) := by
  rw [assignList_next_eq, Option.map_some]
  exact congrArg some (assignTree_root_lnPrevExponent _ u)

theorem assignList_map_subtreeRecordCount
    (acc : ℕ) (ts : List (NTree (GenComputeRow K)))
    (h : ∀ t ∈ ts, ∀ acc', subtreeRecordCount (assignTree acc' t) =
      subtreeRecordCount t) :
    (assignList acc ts).map subtreeRecordCount = ts.map subtreeRecordCount := by
  induction ts generalizing acc with
  | nil => rw [assignList_nil]
  | cons t rest ih =>
    rw [assignList_cons, List.map_cons, List.map_cons, h t (.head _) acc]
    rw [ih (acc + subtreeRecordCount t)
      (fun t' ht' acc' => h t' (.tail _ ht') acc')]

/-- Assignment rewrites stamps, not skeletons, so the DFS record-count
    prefix-sum is invariant -/
theorem subtreeRecordCount_assignTree (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    subtreeRecordCount (assignTree acc t) = subtreeRecordCount t := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)) (acc : ℕ), t.size = n →
      subtreeRecordCount (assignTree acc t) = subtreeRecordCount t
  refine Nat.strong_induction_on (p := p) t.size ?step t acc rfl
  intro n ih t acc hn
  cases t with
  | node g cs =>
    rw [assignTree_node, subtreeRecordCount_node, subtreeRecordCount_node]
    have hmaps :
        (assignList (acc + Nock.Framework.recordCount g.skel.state) cs).map
          subtreeRecordCount = cs.map subtreeRecordCount := by
      apply assignList_map_subtreeRecordCount
      intro t' ht' acc'
      refine ih t'.size ?lt t' acc' rfl
      have : (NTree.node g cs).size = 1 + (cs.map NTree.size).sum := by
        rw [NTree.size]
      rw [← hn, this]
      exact ntree_size_lt_of_mem ht'
    rw [hmaps]

/-- The next-sibling accumulator may equivalently be read off the *assigned*
    child's `subtreeRecordCount` -/
theorem assignList_tail_of_assigned (acc : ℕ)
    (t : NTree (GenComputeRow K)) (ts : List (NTree (GenComputeRow K))) :
    (assignList acc (t :: ts)).tail =
      assignList (acc + subtreeRecordCount (assignTree acc t)) ts := by
  rw [assignList_tail, subtreeRecordCount_assignTree]

/-! ### DFS flatten of assigned stamps

`dfsStamps` is the pre-order walk of `assignTree`.  True for all trees because
assignment is DFS.  This is **not** `computeLineChain` (that zips BFS
`computeSkeletonRows`).  Path / star BFS alignment is below.
Not a `ForestExponentOrder` tick.
-/

mutual
/-- Pre-order flatten of compute stamps. -/
def dfsStamps : NTree (GenComputeRow K) → List ComputeTimestampRow
  | .node g cs => g.stamp :: dfsStampsList cs
/-- Pre-order flatten of a sibling forest. -/
def dfsStampsList : List (NTree (GenComputeRow K)) → List ComputeTimestampRow
  | [] => []
  | t :: ts => dfsStamps t ++ dfsStampsList ts
end

theorem dfsStamps_node (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    dfsStamps (.node g cs) = g.stamp :: dfsStampsList cs :=
  rfl

theorem dfsStampsList_nil :
    dfsStampsList (K := K) [] = [] :=
  rfl

theorem dfsStampsList_cons (t : NTree (GenComputeRow K))
    (ts : List (NTree (GenComputeRow K))) :
    dfsStampsList (t :: ts) = dfsStamps t ++ dfsStampsList ts :=
  rfl

theorem dfsStamps_ne_nil (t : NTree (GenComputeRow K)) :
    dfsStamps t ≠ [] := by
  cases t with
  | node g cs =>
    rw [dfsStamps_node]
    exact List.cons_ne_nil _ _

/-- Local: head of a nonempty left factor survives append. -/
theorem head?_append_of_ne_nil {α : Type*} {l₁ l₂ : List α} (h : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  cases l₁ with
  | nil => exact (h rfl).elim
  | cons x xs => rw [List.cons_append, List.head?_cons, List.head?_cons]

/-- Local: last of a cons equals last of the nonempty tail. -/
theorem getLast?_cons_of_ne_nil {α : Type*} (a : α) {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact (h rfl).elim
  | cons b bs => rw [List.getLast?_cons_cons]

/-- Local: last of a nonempty right factor survives append. -/
theorem getLast?_append_of_ne_nil {α : Type*} {l₁ l₂ : List α} (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  induction l₁ with
  | nil => rw [List.nil_append]
  | cons a rest ih =>
    have hne : rest ++ l₂ ≠ [] := fun heq => by
      cases rest with
      | nil =>
        rw [List.nil_append] at heq
        exact h heq
      | cons _ _ =>
        rw [List.cons_append] at heq
        cases heq
    rw [List.cons_append, getLast?_cons_of_ne_nil a hne, ih]

theorem dfsStamps_assignTree_head_lnPrev (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    ((dfsStamps (assignTree acc t)).head?.map (·.lnPrevExponent)) = some acc := by
  cases t with
  | node g cs =>
    rw [assignTree_node, dfsStamps_node, List.head?_cons, Option.map_some]
    exact congrArg some (stampOfAcc_lnPrevExponent _ _)

theorem dfsStampsList_assignList_ne_nil (acc : ℕ)
    {ts : List (NTree (GenComputeRow K))} (h : ts ≠ []) :
    dfsStampsList (assignList acc ts) ≠ [] := by
  cases ts with
  | nil => exact (h rfl).elim
  | cons t rest =>
    rw [assignList_cons, dfsStampsList_cons]
    intro heq
    cases hst : dfsStamps (assignTree acc t) with
    | nil => exact dfsStamps_ne_nil (assignTree acc t) hst
    | cons _ _ =>
      rw [hst, List.cons_append] at heq
      cases heq

/-- Last assigned stamp of a sibling forest closes at `acc` plus the forest
    record-count sum, given the same fact at every tree -/
theorem dfsStampsList_assignList_getLast_lnExponent
    (acc : ℕ) (ts : List (NTree (GenComputeRow K)))
    (h : ∀ t ∈ ts, ∀ acc',
      (dfsStamps (assignTree acc' t)).getLast?.map (·.lnExponent) =
        some (acc' + subtreeRecordCount t))
    (hne : ts ≠ []) :
    (dfsStampsList (assignList acc ts)).getLast?.map (·.lnExponent) =
      some (acc + (ts.map subtreeRecordCount).sum) := by
  induction ts generalizing acc with
  | nil => exact (hne rfl).elim
  | cons t rest ih =>
    rw [assignList_cons, dfsStampsList_cons]
    cases rest with
    | nil =>
      rw [assignList_nil, dfsStampsList_nil, List.append_nil, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact h t (.head _) acc
    | cons u us =>
      have hright_ne :
          dfsStampsList (assignList (acc + subtreeRecordCount t) (u :: us)) ≠ [] :=
        dfsStampsList_assignList_ne_nil _ (List.cons_ne_nil _ _)
      rw [getLast?_append_of_ne_nil hright_ne]
      have ih' := ih (acc + subtreeRecordCount t)
        (fun t' ht' acc' => h t' (.tail _ ht') acc')
        (List.cons_ne_nil _ _)
      rw [ih']
      congr 1
      rw [show List.map subtreeRecordCount (t :: u :: us) =
            subtreeRecordCount t :: List.map subtreeRecordCount (u :: us)
          from List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Last assigned stamp of a tree closes at `acc + subtreeRecordCount t`. -/
theorem dfsStamps_assignTree_getLast_lnExponent (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    (dfsStamps (assignTree acc t)).getLast?.map (·.lnExponent) =
      some (acc + subtreeRecordCount t) := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)) (acc : ℕ), t.size = n →
      (dfsStamps (assignTree acc t)).getLast?.map (·.lnExponent) =
        some (acc + subtreeRecordCount t)
  refine Nat.strong_induction_on (p := p) t.size ?step t acc rfl
  intro n ih t acc hn
  cases t with
  | node g cs =>
    rw [assignTree_node, dfsStamps_node, subtreeRecordCount_node]
    cases cs with
    | nil =>
      rw [assignList_nil, dfsStampsList_nil, List.getLast?_singleton,
          Option.map_some, List.map_nil, List.sum_nil, stampOfAcc_lnExponent,
          Nat.add_zero]
    | cons t' rest =>
      have hright_ne :
          dfsStampsList (assignList
            (acc + Nock.Framework.recordCount g.skel.state) (t' :: rest)) ≠ [] :=
        dfsStampsList_assignList_ne_nil _ (List.cons_ne_nil _ _)
      rw [getLast?_cons_of_ne_nil _ hright_ne]
      have hlist := dfsStampsList_assignList_getLast_lnExponent
        (acc + Nock.Framework.recordCount g.skel.state) (t' :: rest)
        (fun s hs acc' => by
          refine ih s.size ?lt s acc' rfl
          have : (NTree.node g (t' :: rest)).size =
              1 + ((t' :: rest).map NTree.size).sum := by
            rw [NTree.size]
          rw [← hn, this]
          exact ntree_size_lt_of_mem hs)
        (List.cons_ne_nil _ _)
      rw [← Nat.add_assoc]
      exact hlist

/-- Cons onto a chain when the new head hands its exponent to the old head. -/
theorem computeLineExponentChain_cons_of_head
    (a : ComputeTimestampRow) (l : List ComputeTimestampRow)
    (hjoin : ∀ b, l.head? = some b → a.lnExponent = b.lnPrevExponent)
    (hl : ComputeLineExponentChain l) :
    ComputeLineExponentChain (a :: l) := by
  cases l with
  | nil => exact True.intro
  | cons b rest => exact ⟨hjoin b List.head?_cons, hl⟩

/-- Concatenate two chains when the last of `l₁` hands its exponent to the
    head of `l₂` -/
theorem computeLineExponentChain_append
    (l₁ l₂ : List ComputeTimestampRow)
    (h1 : ComputeLineExponentChain l₁)
    (h2 : ComputeLineExponentChain l₂)
    (hjoin : ∀ a b, l₁.getLast? = some a → l₂.head? = some b →
      a.lnExponent = b.lnPrevExponent) :
    ComputeLineExponentChain (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    rw [List.nil_append]
    exact h2
  | cons x rest ih =>
    rw [List.cons_append]
    cases rest with
    | nil =>
      refine computeLineExponentChain_cons_of_head x l₂ ?join h2
      intro b hb
      exact hjoin x b List.getLast?_singleton hb
    | cons y ys =>
      have ih' : ComputeLineExponentChain ((y :: ys) ++ l₂) :=
        ih h1.2 (fun a b ha hb =>
          hjoin a b (by
            rw [List.getLast?_cons_cons]
            exact ha) hb)
      refine computeLineExponentChain_cons_of_head x ((y :: ys) ++ l₂) ?_ ih'
      intro b hb
      have hy : ((y :: ys) ++ l₂).head? = some y := by
        rw [head?_append_of_ne_nil (List.cons_ne_nil _ _)]
        exact List.head?_cons
      have : b = y := Option.some.inj (hb.symm.trans hy)
      subst this
      exact h1.1

/-- Sibling-forest DFS flatten is a line-exponent chain, given the same at
    every tree -/
theorem dfsStampsList_assignList_chain
    (acc : ℕ) (ts : List (NTree (GenComputeRow K)))
    (h : ∀ t ∈ ts, ∀ acc',
      ComputeLineExponentChain (dfsStamps (assignTree acc' t))) :
    ComputeLineExponentChain (dfsStampsList (assignList acc ts)) := by
  induction ts generalizing acc with
  | nil =>
    rw [assignList_nil, dfsStampsList_nil]
    exact True.intro
  | cons t rest ih =>
    rw [assignList_cons, dfsStampsList_cons]
    refine computeLineExponentChain_append _ _
      (h t (.head _) acc)
      (ih (acc + subtreeRecordCount t)
        (fun t' ht' acc' => h t' (.tail _ ht') acc'))
      ?join
    intro a b ha hb
    cases rest with
    | nil =>
      rw [assignList_nil, dfsStampsList_nil, List.head?_nil] at hb
      cases hb
    | cons u us =>
      have ha' : a.lnExponent = acc + subtreeRecordCount t := by
        have hlast := dfsStamps_assignTree_getLast_lnExponent acc t
        rw [ha, Option.map_some] at hlast
        exact Option.some.inj hlast
      have hhead_eq :
          (dfsStampsList (assignList (acc + subtreeRecordCount t) (u :: us))).head? =
            (dfsStamps (assignTree (acc + subtreeRecordCount t) u)).head? := by
        rw [assignList_cons, dfsStampsList_cons,
            head?_append_of_ne_nil (dfsStamps_ne_nil _)]
      have hbprev : b.lnPrevExponent = acc + subtreeRecordCount t := by
        have hprev :=
          dfsStamps_assignTree_head_lnPrev (acc + subtreeRecordCount t) u
        rw [← hhead_eq, hb, Option.map_some] at hprev
        exact Option.some.inj hprev
      rw [ha', hbprev]

/-- Assigned-tree DFS flatten is a line-exponent chain.  Not
    `computeLineChain` (BFS).  Not a `ForestExponentOrder` tick. -/
theorem dfsStamps_assignTree_chain (acc : ℕ)
    (t : NTree (GenComputeRow K)) :
    ComputeLineExponentChain (dfsStamps (assignTree acc t)) := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)) (acc : ℕ), t.size = n →
      ComputeLineExponentChain (dfsStamps (assignTree acc t))
  refine Nat.strong_induction_on (p := p) t.size ?step t acc rfl
  intro n ih t acc hn
  cases t with
  | node g cs =>
    rw [assignTree_node, dfsStamps_node]
    have hlist : ComputeLineExponentChain
        (dfsStampsList (assignList
          (acc + Nock.Framework.recordCount g.skel.state) cs)) :=
      dfsStampsList_assignList_chain
        (acc + Nock.Framework.recordCount g.skel.state) cs
        (fun s hs acc' => by
          refine ih s.size ?lt s acc' rfl
          have : (NTree.node g cs).size = 1 + (cs.map NTree.size).sum := by
            rw [NTree.size]
          rw [← hn, this]
          exact ntree_size_lt_of_mem hs)
    refine computeLineExponentChain_cons_of_head _ _ ?join hlist
    intro b hb
    cases cs with
    | nil =>
      rw [assignList_nil, dfsStampsList_nil, List.head?_nil] at hb
      cases hb
    | cons t' rest =>
      have hhead_eq :
          (dfsStampsList (assignList
            (acc + Nock.Framework.recordCount g.skel.state) (t' :: rest))).head? =
            (dfsStamps (assignTree
              (acc + Nock.Framework.recordCount g.skel.state) t')).head? := by
        rw [assignList_cons, dfsStampsList_cons,
            head?_append_of_ne_nil (dfsStamps_ne_nil _)]
      have hbprev : b.lnPrevExponent =
          acc + Nock.Framework.recordCount g.skel.state := by
        have hprev := dfsStamps_assignTree_head_lnPrev
          (acc + Nock.Framework.recordCount g.skel.state) t'
        rw [← hhead_eq, hb, Option.map_some] at hprev
        exact Option.some.inj hprev
      have hln :
          ({g with stamp := stampOfAcc g.skel.state acc} : GenComputeRow K).stamp.lnExponent =
            acc + Nock.Framework.recordCount g.skel.state :=
        stampOfAcc_lnExponent g.skel.state acc
      rw [hln, hbprev]

/-- `assignExponents` DFS flatten realises `ComputeLineExponentChain`.
    Not `computeLineChain` (BFS).  Not a tick -/
theorem dfsStamps_assignExponents_chain
    (t : NTree (GenComputeRow K)) :
    ComputeLineExponentChain (dfsStamps (assignExponents t)) :=
  dfsStamps_assignTree_chain 0 t

/-- `assignExponents` DFS flatten starts at exponent zero.
    Not the BFS `computeSkeletonRows` list.  Not a tick -/
theorem dfsStamps_assignExponents_startsAtZero
    (t : NTree (GenComputeRow K)) :
    ComputeLineStartsAtZero (dfsStamps (assignExponents t)) := by
  cases t with
  | node g cs =>
    rw [assignExponents, assignTree_node, dfsStamps_node]
    exact stampOfAcc_lnPrevExponent g.skel.state 0

/-- First compute record of an assigned tree is exponent `1`.  `recordCount_pos`
    gives `1 ≤ recordCount`, so slot `0` is live, and `stampOfAcc` at `acc = 0`
    writes `0 + 0 + 1`.  Reused by live memory-line identification. -/
theorem dfsStamps_assignExponents_exists_recordExponent_one
    (t : NTree (GenComputeRow K)) :
    ∃ c ∈ dfsStamps (assignExponents t), ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧
        c.recordExponent i = 1 := by
  cases t with
  | node g cs =>
    rw [assignExponents, assignTree_node, dfsStamps_node]
    refine ⟨stampOfAcc g.skel.state 0, List.mem_cons.mpr (Or.inl rfl), ?inner⟩
    refine ⟨(0 : Fin 3), ?hi, ?heq⟩
    · change (0 : ℕ) <
        Nock.Framework.recordCount (stampOfAcc g.skel.state 0).state
      rw [stampOfAcc_state]
      exact Nat.lt_of_succ_le (Nock.Framework.recordCount_pos g.skel.state)
    · have hi0 : ((0 : Fin 3) : ℕ) <
          Nock.Framework.recordCount g.skel.state :=
        Nat.lt_of_succ_le (Nock.Framework.recordCount_pos g.skel.state)
      change (stampOfAcc g.skel.state 0).recordExponent 0 = 1
      rw [stampOfAcc_recordExponent g.skel.state 0 (0 : Fin 3) hi0]
      rfl

/-- Assigned sibling forest covers exponents `acc+1` through
    `acc + Σ subtreeRecordCount`.  Local to compute stamps; not a
    `ForestExponentOrder` tick -/
theorem dfsStampsList_assignList_exists_recordExponent
    (acc : ℕ) (ts : List (NTree (GenComputeRow K)))
    (hchild : ∀ t ∈ ts, ∀ acc' n',
      1 ≤ n' → n' ≤ subtreeRecordCount t →
        ∃ c ∈ dfsStamps (assignTree acc' t), ∃ i : Fin 3,
          (i : ℕ) < Nock.Framework.recordCount c.state ∧
            c.recordExponent i = acc' + n')
    (n : ℕ) (h1 : 1 ≤ n) (hn : n ≤ (ts.map subtreeRecordCount).sum) :
    ∃ c ∈ dfsStampsList (assignList acc ts), ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧
        c.recordExponent i = acc + n := by
  induction ts generalizing acc n with
  | nil =>
    rw [List.map_nil, List.sum_nil] at hn
    omega
  | cons t rest ih =>
    rw [List.map_cons, List.sum_cons] at hn
    rw [assignList_cons, dfsStampsList_cons]
    by_cases hleft : n ≤ subtreeRecordCount t
    · obtain ⟨c, hc, i, hi, heq⟩ :=
        hchild t (List.mem_cons.mpr (Or.inl rfl)) acc n h1 hleft
      exact ⟨c, List.mem_append.mpr (Or.inl hc), i, hi, heq⟩
    · have h1' : 1 ≤ n - subtreeRecordCount t := by omega
      have hn' : n - subtreeRecordCount t ≤
          (rest.map subtreeRecordCount).sum := by omega
      obtain ⟨c, hc, i, hi, heq⟩ :=
        ih (acc + subtreeRecordCount t)
          (fun s hs acc' n' h1n hnn =>
              hchild s (List.mem_cons.mpr (Or.inr hs)) acc' n' h1n hnn)
          (n - subtreeRecordCount t) h1' hn'
      refine ⟨c, List.mem_append.mpr (Or.inr hc), i, hi, ?_⟩
      omega

/-- Assigned tree covers exponents `acc+1` through `acc + subtreeRecordCount`.
    Strong induction on `NTree.size`.  Not a `ForestExponentOrder` tick. -/
theorem dfsStamps_assignTree_exists_recordExponent
    (acc : ℕ) (t : NTree (GenComputeRow K)) (n : ℕ)
    (h1 : 1 ≤ n) (hn : n ≤ subtreeRecordCount t) :
    ∃ c ∈ dfsStamps (assignTree acc t), ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧
        c.recordExponent i = acc + n := by
  let p : ℕ → Prop := fun sz =>
    ∀ (t : NTree (GenComputeRow K)) (acc n : ℕ),
      t.size = sz → 1 ≤ n → n ≤ subtreeRecordCount t →
        ∃ c ∈ dfsStamps (assignTree acc t), ∃ i : Fin 3,
          (i : ℕ) < Nock.Framework.recordCount c.state ∧
            c.recordExponent i = acc + n
  refine Nat.strong_induction_on (p := p) t.size ?step t acc n rfl h1 hn
  intro sz ih t acc n hsz h1 hn
  cases t with
  | node g cs =>
    rw [assignTree_node, dfsStamps_node]
    rw [subtreeRecordCount_node] at hn
    by_cases hroot : n ≤ Nock.Framework.recordCount g.skel.state
    · have hle : Nock.Framework.recordCount g.skel.state ≤ 3 := by
        simpa [Nock.NockVM.mem_record_arity] using
          Nock.Framework.recordCount_le g.skel.state
      have hiNat : n - 1 < Nock.Framework.recordCount g.skel.state := by omega
      have hi3 : n - 1 < 3 := Nat.lt_of_lt_of_le hiNat hle
      refine ⟨stampOfAcc g.skel.state acc, List.mem_cons.mpr (Or.inl rfl),
        ⟨n - 1, hi3⟩, ?hi, ?heq⟩
      · rw [stampOfAcc_state]; exact hiNat
      · rw [stampOfAcc_recordExponent g.skel.state acc ⟨n - 1, hi3⟩ hiNat]
        simp only [Fin.val_mk]
        omega
    · have h1' : 1 ≤ n - Nock.Framework.recordCount g.skel.state := by omega
      have hn' : n - Nock.Framework.recordCount g.skel.state ≤
          (cs.map subtreeRecordCount).sum := by omega
      obtain ⟨c, hc, i, hi, heq⟩ :=
        dfsStampsList_assignList_exists_recordExponent
          (acc + Nock.Framework.recordCount g.skel.state) cs
          (fun s hs acc' n' h1n hnn => by
            refine ih s.size ?lt s acc' n' rfl h1n hnn
            have hsz' : (NTree.node g cs).size =
                1 + (cs.map NTree.size).sum := by
              rw [NTree.size]
            rw [← hsz, hsz']
            exact ntree_size_lt_of_mem hs)
          (n - Nock.Framework.recordCount g.skel.state) h1' hn'
      refine ⟨c, List.mem_cons.mpr (Or.inr hc), i, hi, ?_⟩
      omega

/-- Assigned `assignExponents` tree covers exponents `1` through
    `subtreeRecordCount t`.  Specializes the `acc = 0` case. -/
theorem dfsStamps_assignExponents_exists_recordExponent
    (t : NTree (GenComputeRow K)) (n : ℕ)
    (h1 : 1 ≤ n) (hn : n ≤ subtreeRecordCount t) :
    ∃ c ∈ dfsStamps (assignExponents t), ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧
        c.recordExponent i = n := by
  simpa [assignExponents] using
    dfsStamps_assignTree_exists_recordExponent 0 t n h1 hn

/-! ### DFS stamp order = BFS stamp order on path trees and height-1 stars

`assignExponents` is DFS pre-order; `computeSkeletonRows` is `Walk.bfsForest`.
They agree on unary spines (`isPathTree`: OP4 recursion) and on height-1 stars
(`childrenAreLeaves`: cons-over-two-OP1).  Nested branching (height ≥ 2 with
≥ 2 non-leaf children) is where they diverge.  Not a `ForestExponentOrder`
tick: live identification is local on empty-memory, OP1, cons `{1,2,3}`,
OP0 `{1,2}`, unary OP3/OP4 `{1}`, binary OP5/7/8/2 `{1,2}`, and
OP6 `{1,2,3}`; alignment /
all-stamps `hmemLine` / `hwin` remain
-/

/-- Unary spine: every node has at most one child.  Well-founded recursive
    `Prop` (same shape as `assignedStampsWellFormed`); `Iff.rfl` fails. -/
def isPathTree {α : Type*} : NTree α → Prop
  | .node _ cs =>
      cs.length ≤ 1 ∧ ∀ s ∈ cs, isPathTree s
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹s ∈ cs›
  omega

theorem isPathTree_iff {α : Type*} (l : α) (cs : List (NTree α)) :
    isPathTree (.node l cs) ↔
      cs.length ≤ 1 ∧ ∀ s ∈ cs, isPathTree s := by
  constructor
  · intro h
    rw [isPathTree] at h
    exact h
  · intro h
    rwa [isPathTree]

/-- Height ≤ 1: every child is a leaf.  Not recursive.  Cons-over-two-OP1. -/
def childrenAreLeaves {α : Type*} (t : NTree α) : Prop :=
  ∀ s ∈ t.children, s.isLeaf

theorem assignList_length (acc : ℕ) (cs : List (NTree (GenComputeRow K))) :
    (assignList acc cs).length = cs.length := by
  induction cs generalizing acc with
  | nil => rw [assignList_nil, List.length_nil]
  | cons _t ts ih =>
    rw [assignList_cons, List.length_cons, List.length_cons, ih]

theorem assignList_exists_src (acc : ℕ)
    (cs : List (NTree (GenComputeRow K))) {s : NTree (GenComputeRow K)}
    (hs : s ∈ assignList acc cs) :
    ∃ t ∈ cs, ∃ acc', s = assignTree acc' t := by
  induction cs generalizing acc with
  | nil =>
    rw [assignList_nil] at hs
    nomatch hs
  | cons t ts ih =>
    rw [assignList_cons, List.mem_cons] at hs
    cases hs with
    | inl heq =>
      subst heq
      exact ⟨t, List.mem_cons.mpr (Or.inl rfl), acc, rfl⟩
    | inr hrest =>
      obtain ⟨t', ht', acc', heq⟩ := ih (acc + subtreeRecordCount t) hrest
      exact ⟨t', List.mem_cons.mpr (Or.inr ht'), acc', heq⟩

theorem isLeaf_assignTree (acc : ℕ) (t : NTree (GenComputeRow K))
    (h : t.isLeaf) : (assignTree acc t).isLeaf := by
  cases t with
  | node g cs =>
    have hcs : cs = [] := by
      rw [NTree.isLeaf, NTree.children_node] at h
      exact h
    subst hcs
    rw [NTree.isLeaf, assignTree_children, assignList_nil]

theorem isPathTree_assignTree (acc : ℕ)
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    isPathTree (assignTree acc t) := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)) (acc : ℕ), t.size = n →
      isPathTree t → isPathTree (assignTree acc t)
  refine Nat.strong_induction_on (p := p) t.size ?step t acc rfl h
  intro n ih t acc hn hp
  cases t with
  | node g cs =>
    rw [isPathTree_iff] at hp
    rw [assignTree_node, isPathTree_iff]
    constructor
    · rw [assignList_length]
      exact hp.1
    · intro s hs
      obtain ⟨t', ht', acc', rfl⟩ := assignList_exists_src _ cs hs
      refine ih t'.size ?lt t' acc' rfl (hp.2 t' ht')
      have : (NTree.node g cs).size = 1 + (cs.map NTree.size).sum := by
        rw [NTree.size]
      rw [← hn, this]
      exact ntree_size_lt_of_mem ht'

theorem childrenAreLeaves_assignTree (acc : ℕ)
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    childrenAreLeaves (assignTree acc t) := by
  cases t with
  | node g cs =>
    intro s hs
    rw [assignTree_children] at hs
    obtain ⟨t', ht', acc', rfl⟩ := assignList_exists_src _ cs hs
    have hleaf : t'.isLeaf := h t' (by
      rw [NTree.children_node]
      exact ht')
    exact isLeaf_assignTree acc' t' hleaf

theorem dfsStamps_of_isLeaf (t : NTree (GenComputeRow K)) (h : t.isLeaf) :
    dfsStamps t = [t.label.stamp] := by
  cases t with
  | node g cs =>
    have hcs : cs = [] := by
      rw [NTree.isLeaf, NTree.children_node] at h
      exact h
    subst hcs
    rw [dfsStamps_node, dfsStampsList_nil, NTree.label_node]

/-- Checker / RedTeam
    stay downstream of Gen. -/
theorem flatMap_children_nil {LT : Type*} (l : List (NTree LT))
    (h : ∀ t ∈ l, t.children = []) :
    l.flatMap NTree.children = [] := by
  induction l with
  | nil => rw [List.flatMap_nil]
  | cons t ts ih =>
    rw [List.flatMap_cons]
    have ht : t.children = [] := h t (List.mem_cons.mpr (Or.inl rfl))
    have hts : ∀ u ∈ ts, u.children = [] := fun u hu =>
      h u (List.mem_cons.mpr (Or.inr hu))
    rw [ht, List.nil_append, ih hts]

theorem bfsForest_of_leaves {LT : Type*} (l : List (NTree LT))
    (h : ∀ t ∈ l, t.children = []) :
    bfsForest l = l := by
  by_cases hne : l = []
  · subst hne
    rw [bfsForest_nil]
  · rw [bfsForest_cons_eq l hne, flatMap_children_nil l h, bfsForest_nil,
        List.append_nil]

theorem bfsForest_singleton {LT : Type*} (t : NTree LT) :
    bfsForest [t] = t :: bfsForest t.children := by
  have hne : [t] ≠ [] := List.cons_ne_nil _ _
  rw [bfsForest_cons_eq [t] hne, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons_append, List.nil_append]

theorem dfsStampsList_of_leaves
    (cs : List (NTree (GenComputeRow K)))
    (h : ∀ s ∈ cs, s.isLeaf) :
    dfsStampsList cs = cs.map (fun n => n.label.stamp) := by
  induction cs with
  | nil => rw [dfsStampsList_nil, List.map_nil]
  | cons s rest ih =>
    rw [dfsStampsList_cons, List.map_cons, dfsStamps_of_isLeaf s
        (h s (List.mem_cons.mpr (Or.inl rfl)))]
    have hrest : ∀ u ∈ rest, u.isLeaf := fun u hu =>
      h u (List.mem_cons.mpr (Or.inr hu))
    rw [ih hrest, List.cons_append, List.nil_append]

/-- Path-tree DFS stamps are the BFS stamp list.  Strong induction on `t.size`. -/
theorem dfsStamps_eq_bfs_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    dfsStamps t = (bfsForest [t]).map (fun n => n.label.stamp) := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)), t.size = n →
      isPathTree t →
        dfsStamps t = (bfsForest [t]).map (fun n => n.label.stamp)
  refine Nat.strong_induction_on (p := p) t.size ?step t rfl h
  intro n ih t hn hp
  cases t with
  | node g cs =>
    rw [isPathTree_iff] at hp
    rw [dfsStamps_node, bfsForest_singleton, NTree.children_node,
        List.map_cons, NTree.label_node]
    cases cs with
    | nil =>
      rw [dfsStampsList_nil, bfsForest_nil, List.map_nil]
    | cons c rest =>
      cases rest with
      | nil =>
        have hc : isPathTree c :=
          hp.2 c (List.mem_cons.mpr (Or.inl rfl))
        have hsz : c.size < n := by
          have hszdef :
              (NTree.node g [c]).size = 1 + ([c].map NTree.size).sum := by
            rw [NTree.size]
          rw [← hn, hszdef]
          exact ntree_size_lt_of_mem (List.mem_cons.mpr (Or.inl rfl))
        rw [dfsStampsList_cons, dfsStampsList_nil, List.append_nil]
        exact congrArg (fun l => g.stamp :: l)
          (ih c.size hsz c rfl hc)
      | cons c2 rest2 =>
        have hlen : (c :: c2 :: rest2).length ≤ 1 := hp.1
        rw [List.length_cons, List.length_cons] at hlen
        omega

/-- Height-1 star: DFS stamps are the BFS stamp list. -/
theorem dfsStamps_eq_bfs_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    dfsStamps t = (bfsForest [t]).map (fun n => n.label.stamp) := by
  cases t with
  | node g cs =>
    have hcs : ∀ s ∈ cs, s.isLeaf := fun s hs => h s (by
      rw [NTree.children_node]
      exact hs)
    have hch : ∀ s ∈ cs, s.children = [] := fun s hs => by
      have hsL : s.isLeaf := hcs s hs
      rw [NTree.isLeaf] at hsL
      exact hsL
    rw [dfsStamps_node, bfsForest_singleton, NTree.children_node,
        List.map_cons, NTree.label_node, bfsForest_of_leaves cs hch,
        dfsStampsList_of_leaves cs hcs]

theorem dfsStamps_assignExponents_eq_bfs_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    dfsStamps (assignExponents t) =
      (bfsForest [assignExponents t]).map (fun n => n.label.stamp) := by
  rw [assignExponents]
  exact dfsStamps_eq_bfs_of_isPathTree _ (isPathTree_assignTree 0 t h)

theorem dfsStamps_assignExponents_eq_bfs_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    dfsStamps (assignExponents t) =
      (bfsForest [assignExponents t]).map (fun n => n.label.stamp) := by
  rw [assignExponents]
  exact dfsStamps_eq_bfs_of_childrenAreLeaves _
    (childrenAreLeaves_assignTree 0 t h)

/-- Local copy of `ExactTraversal.forall₂_map_pair_iff`.  ExactTraversal is
    not imported from Gen. -/
theorem forall2_map_map_iff
    {α β γ : Type*} (R : β → γ → Prop) (f : α → β) (g : α → γ) :
    ∀ xs : List α,
      List.Forall₂ R (xs.map f) (xs.map g) ↔ ∀ x ∈ xs, R (f x) (g x) := by
  intro xs
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; nomatch hx
    · intro _; exact List.Forall₂.nil
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons]
    constructor
    · intro h y hy
      cases h with
      | cons hr hrest =>
        rw [List.mem_cons] at hy
        cases hy with
        | inl heq => subst heq; exact hr
        | inr hmem => exact ih.mp hrest y hmem
    · intro hall
      refine List.Forall₂.cons (hall x ?_) (ih.mpr (fun y hy => hall y ?_))
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr hy)

theorem assignedStampsWellFormed_of_inTree
    {t s : NTree (GenComputeRow K)}
    (h : assignedStampsWellFormed t) (hin : InTree t s) :
    assignedStampsWellFormed s := by
  revert h
  induction hin with
  | here _ => intro h; exact h
  | @sub c mid _deep hs _hin ih =>
    intro h
    cases c with
    | node g ch =>
      have hch := (assignedStampsWellFormed_iff g ch).mp h
      have hs' : mid ∈ ch := by
        rw [NTree.children_node] at hs
        exact hs
      exact ih (hch.2 mid hs')

theorem assignedStampsWellFormed_of_mem_bfsForest
    {t n : NTree (GenComputeRow K)}
    (h : assignedStampsWellFormed t) (hn : n ∈ bfsForest [t]) :
    assignedStampsWellFormed n := by
  have ⟨c, hc, hin⟩ := (mem_bfsForest [t] n).mp hn
  have hc' : c = t := by
    rw [List.mem_singleton] at hc
    exact hc
  subst hc'
  exact assignedStampsWellFormed_of_inTree h hin

/-- BFS labels of an assigned tree carry matching skeleton/stamp states. -/
theorem forall2_skel_stamp_of_assigned_bfsForest
    (t : NTree (GenComputeRow K))
    (h : assignedStampsWellFormed t) :
    List.Forall₂ (fun skel stamp => stamp.state = skel.state)
      ((bfsForest [t]).map (fun n => n.label.skel))
      ((bfsForest [t]).map (fun n => n.label.stamp)) := by
  rw [forall2_map_map_iff]
  intro n hn
  exact assignedStampsWellFormed_state
    (assignedStampsWellFormed_of_mem_bfsForest h hn)

theorem forall2_skel_dfsStamps_assignExponents_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    List.Forall₂ (fun skel stamp => stamp.state = skel.state)
      ((bfsForest [assignExponents t]).map (fun n => n.label.skel))
      (dfsStamps (assignExponents t)) := by
  rw [dfsStamps_assignExponents_eq_bfs_of_isPathTree t h]
  exact forall2_skel_stamp_of_assigned_bfsForest _
    (assignExponents_assignedStampsWellFormed t)

theorem forall2_skel_dfsStamps_assignExponents_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    List.Forall₂ (fun skel stamp => stamp.state = skel.state)
      ((bfsForest [assignExponents t]).map (fun n => n.label.skel))
      (dfsStamps (assignExponents t)) := by
  rw [dfsStamps_assignExponents_eq_bfs_of_childrenAreLeaves t h]
  exact forall2_skel_stamp_of_assigned_bfsForest _
    (assignExponents_assignedStampsWellFormed t)

/-! ### `computeSkeletonRows` on the DFS flatten

`computeSkeletonRows` is BFS of `SemanticSkeleton.computeTree`.  Mapping
`GenComputeRow.skel` commutes with BFS (`bfsForest_mapNTree`, already in
the `Thm54` namespace via HonestCommitment).  On path trees and height-1
stars the DFS flatten is that BFS stamp list, so the compute-side
`SemanticTimestampSkeleton` fields hold against `computeSkeletonRows`.
Empty memory forest: the path/star compute-only inhabitants below.
Live OP1/cons forests inhabit the same structure with nonempty
`memoryRows` later in this file.  Not a `ForestExponentOrder` tick.
-/

/-- Compute-only skeleton: BFS of this tree is `computeSkeletonRows`.
    Memory forest is empty -/
def genComputeSemanticSkeleton (t : NTree (GenComputeRow K)) :
    SemanticSkeleton where
  computeTree := mapNTree (fun g => g.skel) t
  memoryForest := []

/-- Skeleton with a served memory forest.  Compute tree matches
    `genComputeSemanticSkeleton`; BFS of the mapped forest is
    `memorySkeletonRows` -/
def genSemanticSkeleton (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) : SemanticSkeleton where
  computeTree := mapNTree (fun g => g.skel) t
  memoryForest := mf.map (mapNTree (fun g => g.skel))

theorem computeSkeletonRows_genCompute (t : NTree (GenComputeRow K)) :
    computeSkeletonRows (genComputeSemanticSkeleton t) =
      (bfsForest [t]).map (fun n => n.label.skel) := by
  change (bfsForest [mapNTree (fun g => g.skel) t]).map NTree.label =
    (bfsForest [t]).map (fun n => n.label.skel)
  rw [show [mapNTree (fun g => g.skel) t] =
        [t].map (mapNTree (fun g => g.skel)) from rfl,
      bfsForest_mapNTree, List.map_map]
  congr 1
  funext n
  exact mapNTree_label (fun g => g.skel) n

theorem memorySkeletonRows_genCompute (t : NTree (GenComputeRow K)) :
    memorySkeletonRows (genComputeSemanticSkeleton t) = [] := by
  change (bfsForest []).map NTree.label = []
  rw [bfsForest_nil, List.map_nil]

/-- Path-tree compute topology against `computeSkeletonRows`.
    Not a tick -/
theorem computeTopology_dfsStamps_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genComputeSemanticSkeleton (assignExponents t)))
      (dfsStamps (assignExponents t)) := by
  rw [computeSkeletonRows_genCompute]
  exact forall2_skel_dfsStamps_assignExponents_of_isPathTree t h

/-- Height-1 star compute topology against `computeSkeletonRows`.
    Cons-over-two-OP1 is this theorem.  Not a tick -/
theorem computeTopology_dfsStamps_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genComputeSemanticSkeleton (assignExponents t)))
      (dfsStamps (assignExponents t)) := by
  rw [computeSkeletonRows_genCompute]
  exact forall2_skel_dfsStamps_assignExponents_of_childrenAreLeaves t h

theorem memoryTopology_genCompute (t : NTree (GenComputeRow K)) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (memorySkeletonRows (genComputeSemanticSkeleton t))
      ([] : List MemoryTimestampRow) := by
  rw [memorySkeletonRows_genCompute]
  exact List.Forall₂.nil

theorem computeSkeletonRows_genSemantic
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    computeSkeletonRows (genSemanticSkeleton t mf) =
      computeSkeletonRows (genComputeSemanticSkeleton t) :=
  rfl

theorem memorySkeletonRows_genSemantic
    (_t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    memorySkeletonRows (genSemanticSkeleton _t mf) =
      (bfsForest mf).map (fun n => n.label.skel) := by
  change (bfsForest (mf.map (mapNTree (fun g => g.skel)))).map NTree.label =
    (bfsForest mf).map (fun n => n.label.skel)
  rw [bfsForest_mapNTree, List.map_map]
  congr 1
  funext n
  exact mapNTree_label (fun g => g.skel) n

/-- BFS stamps of a generated memory forest.  Paper order is BFS
    (`Walk.bfsForest`); OP1/cons trees are already that topology. -/
def genMemoryStamps (mf : List (NTree (GenMemoryRow K))) :
    List MemoryTimestampRow :=
  (bfsForest mf).map (fun n => n.label.stamp)

theorem genMemoryStamps_ne_nil (mf : List (NTree (GenMemoryRow K)))
    (h : mf ≠ []) : genMemoryStamps mf ≠ [] := by
  cases mf with
  | nil => exact (h rfl).elim
  | cons c rest =>
    have hne : c :: rest ≠ [] := List.cons_ne_nil c rest
    simp only [genMemoryStamps]
    rw [bfsForest_cons_eq (c :: rest) hne, List.map_append, List.map_cons]
    exact List.cons_ne_nil _ _

/-- Stamp state matches skeleton state at every node.  Forest analogue of
    `assignedStampsWellFormed`, but memory has no `stampOfAcc`. -/
def memoryStampsWellFormed : NTree (GenMemoryRow K) → Prop
  | .node g ch =>
      g.stamp.state = g.skel.state ∧
      ∀ s ∈ ch, memoryStampsWellFormed s
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹s ∈ ch›
  omega

theorem memoryStampsWellFormed_iff (g : GenMemoryRow K)
    (ch : List (NTree (GenMemoryRow K))) :
    memoryStampsWellFormed (.node g ch) ↔
      g.stamp.state = g.skel.state ∧
      ∀ s ∈ ch, memoryStampsWellFormed s := by
  constructor
  · intro h
    rw [memoryStampsWellFormed] at h
    exact h
  · intro h
    rwa [memoryStampsWellFormed]

theorem memoryStampsWellFormed_leaf (g : GenMemoryRow K)
    (hg : g.stamp.state = g.skel.state) :
    memoryStampsWellFormed (.node g []) :=
  (memoryStampsWellFormed_iff g []).mpr
    ⟨hg, fun _ hs => nomatch hs⟩

theorem memoryStampsWellFormed_node1 (g : GenMemoryRow K)
    (c : NTree (GenMemoryRow K))
    (hg : g.stamp.state = g.skel.state)
    (hc : memoryStampsWellFormed c) :
    memoryStampsWellFormed (.node g [c]) :=
  (memoryStampsWellFormed_iff g [c]).mpr ⟨hg, fun s hs => by
    rw [List.mem_singleton] at hs
    subst hs
    exact hc⟩

theorem memoryStampsWellFormed_node2 (g : GenMemoryRow K)
    (c₁ c₂ : NTree (GenMemoryRow K))
    (hg : g.stamp.state = g.skel.state)
    (h1 : memoryStampsWellFormed c₁) (h2 : memoryStampsWellFormed c₂) :
    memoryStampsWellFormed (.node g [c₁, c₂]) :=
  (memoryStampsWellFormed_iff g [c₁, c₂]).mpr ⟨hg, fun s hs => by
    rw [List.mem_cons] at hs
    cases hs with
    | inl heq => subst heq; exact h1
    | inr hs' =>
      rw [List.mem_singleton] at hs'
      subst hs'
      exact h2⟩

theorem memoryStampsWellFormed_state {t : NTree (GenMemoryRow K)}
    (h : memoryStampsWellFormed t) :
    t.label.stamp.state = t.label.skel.state := by
  cases t with
  | node g ch =>
    exact (memoryStampsWellFormed_iff g ch |>.mp h).1

theorem memoryStampsWellFormed_of_inTree
    {t s : NTree (GenMemoryRow K)}
    (h : memoryStampsWellFormed t) (hin : InTree t s) :
    memoryStampsWellFormed s := by
  revert h
  induction hin with
  | here _ => intro h; exact h
  | @sub c mid _deep hs _hin ih =>
    intro h
    cases c with
    | node g ch =>
      have hch := (memoryStampsWellFormed_iff g ch).mp h
      have hs' : mid ∈ ch := by
        rw [NTree.children_node] at hs
        exact hs
      exact ih (hch.2 mid hs')

theorem memoryStampsWellFormed_of_mem_bfsForest
    {mf : List (NTree (GenMemoryRow K))}
    {n : NTree (GenMemoryRow K)}
    (h : ∀ root ∈ mf, memoryStampsWellFormed root)
    (hn : n ∈ bfsForest mf) :
    memoryStampsWellFormed n := by
  have ⟨c, hc, hin⟩ := (mem_bfsForest mf n).mp hn
  exact memoryStampsWellFormed_of_inTree (h c hc) hin

theorem memoryTopology_of_wellFormed
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      ((bfsForest mf).map (fun n => n.label.skel))
      ((bfsForest mf).map (fun n => n.label.stamp)) := by
  rw [forall2_map_map_iff]
  intro n hn
  exact memoryStampsWellFormed_state
    (memoryStampsWellFormed_of_mem_bfsForest h hn)

theorem computeTopology_genSemantic_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t)
    (mf : List (NTree (GenMemoryRow K))) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genSemanticSkeleton (assignExponents t) mf))
      (dfsStamps (assignExponents t)) := by
  rw [computeSkeletonRows_genSemantic]
  exact computeTopology_dfsStamps_of_isPathTree t h

theorem computeTopology_genSemantic_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t)
    (mf : List (NTree (GenMemoryRow K))) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genSemanticSkeleton (assignExponents t) mf))
      (dfsStamps (assignExponents t)) := by
  rw [computeSkeletonRows_genSemantic]
  exact computeTopology_dfsStamps_of_childrenAreLeaves t h

theorem memoryTopology_genSemantic
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ root ∈ mf, memoryStampsWellFormed root) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (memorySkeletonRows (genSemanticSkeleton t mf))
      (genMemoryStamps mf) := by
  rw [memorySkeletonRows_genSemantic]
  simp only [genMemoryStamps]
  exact memoryTopology_of_wellFormed mf h

/-- DFS flatten membership is some in-tree node's stamp. -/
theorem mem_dfsStampsList_iff (ts : List (NTree (GenComputeRow K)))
    (stamp : ComputeTimestampRow) :
    stamp ∈ dfsStampsList ts ↔ ∃ t ∈ ts, stamp ∈ dfsStamps t := by
  induction ts with
  | nil =>
    rw [dfsStampsList_nil]
    constructor
    · intro h; nomatch h
    · intro ⟨_, ht, _⟩; nomatch ht
  | cons t rest ih =>
    rw [dfsStampsList_cons, List.mem_append, ih]
    constructor
    · intro h
      cases h with
      | inl h1 => exact ⟨t, List.mem_cons.mpr (Or.inl rfl), h1⟩
      | inr h2 =>
        obtain ⟨u, hu, hst⟩ := h2
        exact ⟨u, List.mem_cons.mpr (Or.inr hu), hst⟩
    · intro ⟨u, hu, hst⟩
      rw [List.mem_cons] at hu
      cases hu with
      | inl heq => subst heq; exact Or.inl hst
      | inr hmem => exact Or.inr ⟨u, hmem, hst⟩

theorem exists_inTree_of_mem_dfsStamps
    (t : NTree (GenComputeRow K)) :
    ∀ stamp ∈ dfsStamps t, ∃ s, InTree t s ∧ s.label.stamp = stamp := by
  let p : ℕ → Prop := fun n =>
    ∀ (t : NTree (GenComputeRow K)), t.size = n →
      ∀ stamp ∈ dfsStamps t, ∃ s, InTree t s ∧ s.label.stamp = stamp
  refine Nat.strong_induction_on (p := p) t.size ?step t rfl
  intro n ih t hn
  cases t with
  | node g cs =>
    intro stamp hmem
    rw [dfsStamps_node] at hmem
    rw [List.mem_cons] at hmem
    cases hmem with
    | inl heq =>
      subst heq
      refine ⟨NTree.node g cs, InTree.here (NTree.node g cs), ?_⟩
      rw [NTree.label_node]
    | inr hrest =>
      obtain ⟨c, hc, hst⟩ := (mem_dfsStampsList_iff cs stamp).mp hrest
      have hlt : c.size < n := by
        have : (NTree.node g cs).size = 1 + (cs.map NTree.size).sum := by
          rw [NTree.size]
        rw [← hn, this]
        exact ntree_size_lt_of_mem hc
      obtain ⟨s, hin, heq⟩ := ih c.size hlt c rfl stamp hst
      refine ⟨s, InTree.sub ?_ hin, heq⟩
      rw [NTree.children_node]
      exact hc

/-- Per-node `computeLineAdvance` on every DFS stamp of a well-formed tree.
    Independent of BFS order.  Not a tick -/
theorem dfsStamps_computeLineAdvance
    {t : NTree (GenComputeRow K)} (h : assignedStampsWellFormed t)
    {stamp : ComputeTimestampRow} (hst : stamp ∈ dfsStamps t) :
    stamp.lnExponent =
      stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state := by
  obtain ⟨s, hin, heq⟩ := exists_inTree_of_mem_dfsStamps t stamp hst
  have hw := assignedStampsWellFormed_of_inTree h hin
  rw [← heq]
  exact assignedStampsWellFormed_computeLineAdvance hw

/-- Per-node `computeRecordOffsets` on every DFS stamp of a well-formed tree.
    Independent of BFS order.  Not a tick -/
theorem dfsStamps_computeRecordOffsets
    {t : NTree (GenComputeRow K)} (h : assignedStampsWellFormed t)
    {stamp : ComputeTimestampRow} (hst : stamp ∈ dfsStamps t)
    (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1 := by
  obtain ⟨s, hin, heq⟩ := exists_inTree_of_mem_dfsStamps t stamp hst
  have hw := assignedStampsWellFormed_of_inTree h hin
  rw [← heq] at hi ⊢
  exact assignedStampsWellFormed_computeRecordOffsets hw i hi

theorem dfsStamps_assignExponents_computeLineAdvance
    (t : NTree (GenComputeRow K))
    {stamp : ComputeTimestampRow} (hst : stamp ∈ dfsStamps (assignExponents t)) :
    stamp.lnExponent =
      stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state :=
  dfsStamps_computeLineAdvance (assignExponents_assignedStampsWellFormed t) hst

theorem dfsStamps_assignExponents_computeRecordOffsets
    (t : NTree (GenComputeRow K))
    {stamp : ComputeTimestampRow} (hst : stamp ∈ dfsStamps (assignExponents t))
    (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount stamp.state) :
    stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1 :=
  dfsStamps_computeRecordOffsets (assignExponents_assignedStampsWellFormed t)
    hst i hi

/-- Compute-side `SemanticTimestampSkeleton` fields on path trees, against
    `computeSkeletonRows` of the compute-only projection.  Empty memory
    forest.  Bundled here; the inhabitant is
    `genComputeTimestampSkeleton_of_isPathTree`.  Not a tick. -/
theorem semanticTimestampComputeFields_of_isPathTree
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genComputeSemanticSkeleton (assignExponents t)))
      (dfsStamps (assignExponents t)) ∧
    ComputeLineStartsAtZero (dfsStamps (assignExponents t)) ∧
    ComputeLineExponentChain (dfsStamps (assignExponents t)) ∧
    (∀ stamp ∈ dfsStamps (assignExponents t),
      stamp.lnExponent =
        stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state) ∧
    (∀ stamp ∈ dfsStamps (assignExponents t), ∀ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state →
        stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1) :=
  ⟨computeTopology_dfsStamps_of_isPathTree t h,
   dfsStamps_assignExponents_startsAtZero t,
   dfsStamps_assignExponents_chain t,
   fun _ hst => dfsStamps_assignExponents_computeLineAdvance t hst,
   fun _ hst i hi =>
     dfsStamps_assignExponents_computeRecordOffsets t hst i hi⟩

/-- Compute-side `SemanticTimestampSkeleton` fields on height-1 stars.
    Cons-over-two-OP1 is this theorem.  Bundled here; the inhabitant is
    `genComputeTimestampSkeleton_of_childrenAreLeaves`.  Not a tick. -/
theorem semanticTimestampComputeFields_of_childrenAreLeaves
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    List.Forall₂ (fun row stamp => stamp.state = row.state)
      (computeSkeletonRows (genComputeSemanticSkeleton (assignExponents t)))
      (dfsStamps (assignExponents t)) ∧
    ComputeLineStartsAtZero (dfsStamps (assignExponents t)) ∧
    ComputeLineExponentChain (dfsStamps (assignExponents t)) ∧
    (∀ stamp ∈ dfsStamps (assignExponents t),
      stamp.lnExponent =
        stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state) ∧
    (∀ stamp ∈ dfsStamps (assignExponents t), ∀ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state →
        stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1) :=
  ⟨computeTopology_dfsStamps_of_childrenAreLeaves t h,
   dfsStamps_assignExponents_startsAtZero t,
   dfsStamps_assignExponents_chain t,
   fun _ hst => dfsStamps_assignExponents_computeLineAdvance t hst,
   fun _ hst i hi =>
     dfsStamps_assignExponents_computeRecordOffsets t hst i hi⟩

/-- Request-slot list matching `SemanticTimestampSkeleton.requestTopology`
    on the nose, so the inhabitant closes that field by `rfl`.
    Reducible so `rfl` can unfold it -/
@[reducible]
def genSemanticRequests (base : SemanticSkeleton)
    (computeRows : List ComputeTimestampRow) : List CanonicalRecordSlot :=
  let paired := (SemanticStrategy.computeSkeletonRows base).zip computeRows
  paired.flatMap fun pair =>
    (List.ofFn fun i : Fin 3 =>
      if h : (i : ℕ) < Nock.Framework.recordCount pair.1.state then
        some
          ({ record := pair.1.memoryRecord i h
             exponent := pair.2.recordExponent i } : CanonicalRecordSlot)
      else none).filterMap id

/-- Response-slot list matching `SemanticTimestampSkeleton.responseTopology`.
    The two `by simp [memoryMemRecKind, h]` proofs are not assumed
    definitionally equal; `genSemanticResponses_eq` identifies them. -/
@[reducible]
def genSemanticResponses (base : SemanticSkeleton)
    (memoryRows : List MemoryTimestampRow) : List CanonicalRecordSlot :=
  let paired := (SemanticStrategy.memorySkeletonRows base).zip memoryRows
  paired.filterMap fun pair =>
    if h : pair.1.state = .read_root then
      some
        ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
           exponent := pair.2.recordExponent } : CanonicalRecordSlot)
    else none

theorem genSemanticResponses_eq (base : SemanticSkeleton)
    (memoryRows : List MemoryTimestampRow) :
    genSemanticResponses base memoryRows =
      (let paired :=
          (SemanticStrategy.memorySkeletonRows base).zip memoryRows
       paired.filterMap fun pair =>
        if h : pair.1.state = .read_root then
          some
            ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
               exponent := pair.2.recordExponent } : CanonicalRecordSlot)
        else none) := by
  -- `@[reducible]` plus Prop proof-irrelevance: the inner `by simp` proofs
  -- of `memoryMemRecKind` are defeq, so this is `rfl` after unfolding.
  unfold genSemanticResponses
  rfl

/-- Empty `memoryRows` makes the response-slot list `[]`.  Not `rfl`:
    `List.zip` matches the first argument first, so an unreduced
    `memorySkeletonRows` application does not unfold against `[]`.
    The filter lambda matches `SemanticTimestampSkeleton.responseTopology`
    on the nose (`SemanticTimestampStrategy.lean:103-112`). -/
theorem genSemanticResponses_nil (base : SemanticSkeleton) :
    (let paired :=
        (SemanticStrategy.memorySkeletonRows base).zip
          ([] : List MemoryTimestampRow)
     paired.filterMap fun pair =>
      if h : pair.1.state = .read_root then
        some
          ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
             exponent := pair.2.recordExponent } : CanonicalRecordSlot)
      else none) = [] := by
  simp [List.zip_nil_right]

/-- Path-tree inhabitant of `SemanticTimestampSkeleton` over the compute-only
    projection, with empty memory.  `F`/`Algebra` are binders for later
    α-specialization; the fields themselves are Nat/noun topology.
    Empty `memoryRows` makes `semanticResponses` `[]` by
    `genSemanticResponses_nil`.  Not a `ForestExponentOrder` tick. -/
noncomputable def genComputeTimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    SemanticTimestampSkeleton F K (genComputeSemanticSkeleton (assignExponents t)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := []
  semanticRequests :=
    genSemanticRequests (genComputeSemanticSkeleton (assignExponents t))
      (dfsStamps (assignExponents t))
  semanticResponses := []
  computeTopology := computeTopology_dfsStamps_of_isPathTree t h
  memoryTopology := memoryTopology_genCompute (assignExponents t)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_nil _).symm

theorem genComputeTimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    (genComputeTimestampSkeleton_of_isPathTree F t h).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

/-- Height-1 star inhabitant of `SemanticTimestampSkeleton` over the
    compute-only projection, with empty memory.  Cons-over-two-OP1 is
    this construction.  Not a `ForestExponentOrder` tick. -/
noncomputable def genComputeTimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    SemanticTimestampSkeleton F K (genComputeSemanticSkeleton (assignExponents t)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := []
  semanticRequests :=
    genSemanticRequests (genComputeSemanticSkeleton (assignExponents t))
      (dfsStamps (assignExponents t))
  semanticResponses := []
  computeTopology := computeTopology_dfsStamps_of_childrenAreLeaves t h
  memoryTopology := memoryTopology_genCompute (assignExponents t)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_nil _).symm

theorem genComputeTimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    (genComputeTimestampSkeleton_of_childrenAreLeaves F t h).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

/-- Live-only memory-line identification: every `read_root` / `verify_child`
    stamp equals some compute-record exponent.  Generator infrastructure, not a `ForestExponentOrder` tick. -/
def LiveMemLineIdentification
    {F : Type} [Field F] [Algebra F K] {base : SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) : Prop :=
  ∀ stamp ∈ S.memoryRows,
    stamp.state = .read_root ∨ stamp.state = .verify_child →
      ∃ c ∈ S.computeRows, ∃ i : Fin 3,
        (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i

/-- Empty memory makes live identification vacuous -/
theorem liveMemLineIdentification_of_memoryRows_nil
    {F : Type} [Field F] [Algebra F K] {base : SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) (h : S.memoryRows = []) :
    LiveMemLineIdentification S := by
  intro stamp hst _hlive
  rw [h] at hst
  nomatch hst

theorem liveMemLineIdentification_genComputeTimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    LiveMemLineIdentification (genComputeTimestampSkeleton_of_isPathTree F t h) :=
  liveMemLineIdentification_of_memoryRows_nil _ rfl

theorem liveMemLineIdentification_genComputeTimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    LiveMemLineIdentification
      (genComputeTimestampSkeleton_of_childrenAreLeaves F t h) :=
  liveMemLineIdentification_of_memoryRows_nil _ rfl

/-- Nonvacuity specialization at `F := K` via `Algebra.id`.  Not the only
    inhabitant — the generic-`F` constructions above are the load-bearing
    ones -/
noncomputable def genComputeTimestampSkeleton_of_isPathTree_id
    (t : NTree (GenComputeRow K)) (h : isPathTree t) :
    SemanticTimestampSkeleton K K (genComputeSemanticSkeleton (assignExponents t)) :=
  letI : Algebra K K := Algebra.id K
  genComputeTimestampSkeleton_of_isPathTree (F := K) t h

noncomputable def genComputeTimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) :
    SemanticTimestampSkeleton K K (genComputeSemanticSkeleton (assignExponents t)) :=
  letI : Algebra K K := Algebra.id K
  genComputeTimestampSkeleton_of_childrenAreLeaves (F := K) t h

/-! ## The rendering pass -/

/-- The head noun of a formula cell (`.atom 0` on an atom formula). -/
def formulaHead : Noun → Noun
  | .cell h _ => h
  | _ => .atom 0

/-- Render the `K`-columns of one `OP_1` row from its skeleton and assigned exponents, via the
    computable fingerprint `encC`.  `ln_prev = α^lnPrevExponent`, `ln = α^lnExponent`, and the one
    live record `mr1 = (f, f_t, 3, α^recordExponent₀)`. -/
def renderOp1Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, ⟨α, z, 0, 0, 0⟩,
    { state := .s1
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z skel.evaluation, 3, α ^ stamp.recordExponent 0⟩
      mr2 := ComputeTable.MemRec.zero, mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z skel.evaluation
      f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the branching `.cons` row from its skeleton and assigned exponents.
    The two subformula slots carry the children's `(subject, formula, evaluation)`, the single record
    opens the whole formula `[leftF rightF]` at axis `3` (child the right branch), and the decompose
    columns split the formula into its head/tail. -/
def renderConsRow (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  let leftF := formulaHead skel.formula
  let rightF := formulaTail skel.formula
  let leftR := formulaHead skel.evaluation
  let rightR := formulaTail skel.evaluation
  (.cons, ⟨α, z, 0, 0, 0⟩,
    { state := .cons
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z skel.subject, sf1_f := encC z leftF, sf1_e := encC z leftR
      sf2_s := encC z skel.subject, sf2_f := encC z rightF, sf2_e := encC z rightR
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z rightF, 3, α ^ stamp.recordExponent 0⟩
      mr2 := ComputeTable.MemRec.zero, mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z leftF, f_t := encC z rightF
      f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the nonterminal `OP_4` increment row from its skeleton and assigned
    exponents.  The one live record opens the formula `[head tail]` at axis `3` (child the tail
    `tail`), the single subformula slot carries the recursive call's `(subject, formula, result)`
    read off the skeleton, and the evaluation is the increment result. -/
def renderOp4Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s4, ⟨α, z, 0, 0, 0⟩,
    { state := .s4
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ComputeTable.MemRec.zero, mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the nonterminal `OP_3` cell-test row from its skeleton and assigned
    exponents.  Structurally identical to the `OP_4` row (one formula-open record `[head tail] @3`
    with child the tail, one subformula slot carrying the call's `(subject, formula, result)`); the
    evaluation column is the cell-test result off the skeleton. -/
def renderOp3Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s3, ⟨α, z, 0, 0, 0⟩,
    { state := .s3
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ComputeTable.MemRec.zero, mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-3 `OP_2` eval row from its skeleton and assigned
    exponents.  All three subformula slots are live (`sf1_*`, `sf2_*`, `sf3_*`, read off the
    skeleton via `skeletonSubformula`), the tail decomposition columns `f_th`/`f_tt` are filled
    (`decActive.s2 = true`), and TWO records are committed: the formula-open `[formula f_t] @3`
    (timestamp `α^recordExponent 0`) and the formula-tail `[f_t f_th] @2` (timestamp
    `α^recordExponent 1`). -/
def renderOp2Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s2, ⟨α, z, 0, 0, 0⟩,
    { state := .s2
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := encC z (P8Census.skeletonSubformula skel 2 .subject)
      sf3_f := encC z (P8Census.skeletonSubformula skel 2 .formula)
      sf3_e := encC z (P8Census.skeletonSubformula skel 2 .result)
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-2 `OP_7` compose row from its skeleton and assigned
    exponents.  The two subformula slots are live (`sf1_*` the helper `*[a b]`, `sf2_*` the consumer
    `*[sb c]` whose SUBJECT is the computed helper `sb`, read off the skeleton via
    `skeletonSubformula`), the tail decomposition columns `f_th`/`f_tt` are filled
    (`decActive.s7 = true`), and TWO records are committed: the formula-open `[formula f_t] @3`
    (timestamp `α^recordExponent 0`) and the formula-tail `[f_t f_th] @2` (timestamp
    `α^recordExponent 1`).  Mirrors `renderOp2Row` with the
    third subformula slot vacant (fan-out `2`). -/
def renderOp7Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s7, ⟨α, z, 0, 0, 0⟩,
    { state := .s7
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-2 `OP_5` equality row from its skeleton and assigned
    exponents.  Structurally identical to `renderOp7Row` (two live subformula slots read off the
    skeleton via `skeletonSubformula`, the tail decomposition columns `f_th`/`f_tt` filled since
    `decActive.s5 = true`, and TWO committed records: the formula-open `[formula f_t] @3` and the
    formula-tail `[f_t f_th] @2`).  The evaluation column encodes the equality gate
    `e = encC z (tis sf1 sf2)` off the skeleton — atom `0` (equal) or `1` (distinct).  Unlike OP7 both subformula subjects are the row subject `a`
    (the two operands `*[a b]`, `*[a c]`), a fact carried by the skeleton the row renders. -/
def renderOp5Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s5, ⟨α, z, 0, 0, 0⟩,
    { state := .s5
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-2 `OP_8` push row from its skeleton and assigned
    exponents.  Structurally identical to `renderOp7Row` (two live subformula slots read off the
    skeleton via `skeletonSubformula`, the tail decomposition columns `f_th`/`f_tt` filled since
    `decActive.s8 = true`, and TWO committed records: the formula-open `[formula f_t] @3` and the
    formula-tail `[f_t f_th] @2`) EXCEPT the consumer subformula's SUBJECT is the autocons `[sb a]`
    (read off the skeleton), the OP8 "push". -/
def renderOp8Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s8, ⟨α, z, 0, 0, 0⟩,
    { state := .s8
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the `OP_0` axis-read row from its skeleton and assigned exponents.
    The two live records are the formula-open `[formula f_t] @3` and the actual slot read
    `[subject evaluation] @axis` (its axis the skeleton's second memory axis), timestamped by the two
    consecutive exponents `recordExponent 0`, `recordExponent 1`. -/
def renderOp0Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s0, ⟨α, z, 0, 0, 0⟩,
    { state := .s0
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z skel.subject, encC z skel.evaluation,
        ((P8Census.skeletonMemoryAxis skel 1 : ℕ) : K), α ^ stamp.recordExponent 1⟩
      mr3 := ComputeTable.MemRec.zero },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-2 `OP_9` invoke row from its skeleton and assigned
    exponents.  The two subformula slots are live (`sf1_*` the core eval `*[a c]`, `sf2_*` the invoke
    `*[core arm]` whose SUBJECT is the computed core and formula the served arm, read off the skeleton
    via `skeletonSubformula`), the tail decomposition columns `f_th`/`f_tt` are filled
    (`decActive.s9 = true`), and THREE records are committed: the formula-open `[formula f_t] @3`
    (timestamp `α^recordExponent 0`), the formula-tail `[f_t f_th] @2` (timestamp
    `α^recordExponent 1`), and the served arm fetch `[core arm] @axis` (timestamp
    `α^recordExponent 2`) whose root is the computed core `sf1` and whose axis is the skeleton's
    third memory axis. -/
def renderOp9Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s9, ⟨α, z, 0, 0, 0⟩,
    { state := .s9
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ⟨encC z (P8Census.skeletonSubformula skel 0 .result),
        encC z (P8Census.skeletonSubformula skel 1 .formula),
        ((P8Census.skeletonMemoryAxis skel 2 : ℕ) : K), α ^ stamp.recordExponent 2⟩ },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := 0, f_ttt := 0 })

/-- Render the `K`-columns of the fan-out-2 `OP_6` if/branch row from its skeleton and assigned
    exponents.  The two subformula slots are live (`sf1_*` the TAKEN branch `*[a taken]` whose
    formula is the value-selected `c`/`d`, `sf2_*` the CONDITION `*[a b]` whose result is the
    1-leaf `0`/`1`, both read off the skeleton via `skeletonSubformula`), ALL FOUR decomposition
    columns `f_th`/`f_tt`/`f_tth`/`f_ttt` are filled (`decActive.s6.f_tth =.f_ttt = true` — OP6
    is the only such state), and THREE records are committed: the formula-open `[formula f_t] @3`
    (timestamp `α^recordExponent 0`), the formula-tail `[f_t f_th] @2` exposing the condition
    formula `b` (timestamp `α^recordExponent 1`), and the branch-pair `[f_tt f_tth] @2` exposing the
    head branch `c` (timestamp `α^recordExponent 2`) — the record that structurally reads BOTH
    branches even though only the taken one is evaluated. -/
def renderOp6Row (z α : K) (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (.s6, ⟨α, z, 0, 0, 0⟩,
    { state := .s6
      s := encC z skel.subject
      f := encC z skel.formula
      e := encC z skel.evaluation
      sf1_s := encC z (P8Census.skeletonSubformula skel 0 .subject)
      sf1_f := encC z (P8Census.skeletonSubformula skel 0 .formula)
      sf1_e := encC z (P8Census.skeletonSubformula skel 0 .result)
      sf2_s := encC z (P8Census.skeletonSubformula skel 1 .subject)
      sf2_f := encC z (P8Census.skeletonSubformula skel 1 .formula)
      sf2_e := encC z (P8Census.skeletonSubformula skel 1 .result)
      sf3_s := 0, sf3_f := 0, sf3_e := 0
      ln_prev := α ^ stamp.lnPrevExponent
      ln := α ^ stamp.lnExponent
      mr1 := ⟨encC z skel.formula, encC z (formulaTail skel.formula), 3, α ^ stamp.recordExponent 0⟩
      mr2 := ⟨encC z (formulaTail skel.formula), encC z (formulaHead (formulaTail skel.formula)), 2,
        α ^ stamp.recordExponent 1⟩
      mr3 := ⟨encC z (formulaTail (formulaTail skel.formula)),
        encC z (formulaHead (formulaTail (formulaTail skel.formula))), 2,
        α ^ stamp.recordExponent 2⟩ },
    { f_h := encC z (formulaHead skel.formula), f_t := encC z (formulaTail skel.formula)
      f_th := encC z (formulaHead (formulaTail skel.formula))
      f_tt := encC z (formulaTail (formulaTail skel.formula))
      f_tth := encC z (formulaHead (formulaTail (formulaTail skel.formula)))
      f_ttt := encC z (formulaTail (formulaTail (formulaTail skel.formula))) })

/-- Render one node: its `OP_1` row, the branching `.cons` row, the `OP_4` increment row, the
    `OP_0` axis-read row (else the placeholder row for out-of-fragment states), and stamp its
    requests with `ts = α^recordExponent₀`. -/
def renderNode (z α : K) (g : GenComputeRow K) : GenComputeRow K :=
  match g.skel.state with
  | .s1 =>
    { g with
      row := renderOp1Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .cons =>
    { g with
      row := renderConsRow z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s4 =>
    { g with
      row := renderOp4Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s3 =>
    { g with
      row := renderOp3Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s2 =>
    { g with
      row := renderOp2Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s5 =>
    { g with
      row := renderOp5Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s7 =>
    { g with
      row := renderOp7Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s8 =>
    { g with
      row := renderOp8Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s0 =>
    { g with
      row := renderOp0Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s9 =>
    { g with
      row := renderOp9Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }
  | .s6 =>
    { g with
      row := renderOp6Row z α g.stamp g.skel
      requests := g.requests.map (fun r => { r with ts := α ^ g.stamp.recordExponent 0 }) }

/-- **Phase 3 (`renderRows`).**  Fill the `K`-columns of every node from the committed skeleton
    and the assigned exponents. -/
def renderRows (z α : K) : NTree (GenComputeRow K) → NTree (GenComputeRow K)
  | .node g cs => .node (renderNode z α g) (cs.map (renderRows z α))

/-- **`genServiceReqs`.**  The value-keyed memory service requests a generated compute tree actually
    emits, collected in DFS pre-order (a node's own `requests`, then its children left-to-right).
    This is the compute-side driver of the served memory forest: the requests threaded here are the
    fingerprint-VALUE carriers the memoryless matcher discharges, never a
    committed-line pointer (DESIGN-PRINCIPLES §0).  Computable/positionless. -/
def genServiceReqs : NTree (GenComputeRow K) → List (ServiceReq K)
  | .node g cs => g.requests ++ (cs.map genServiceReqs).flatten

/-! ## Memory reconstruction of the served forest

The `OP_1` row opens its formula `[head result]` at axis `3` as one live request; that request is
served by the five-row reconstruction `read_root -> decompose -> (halt_head, verify_child ->
halt_result)`.  The rows below are pure data — the fingerprint columns are the computable `encC`
(`= enc`, `Encode.encC_eq`), the cells and LogUp poles mirror the verified `Op1Config` served rows.
The served-forest exponent assignment is stamped directly for the `OP_1` leaf (its general pass is
the next increment); the values are the verified `Op1Config` node stamps verbatim. -/

/-- The seed-`z` memory inputs `(z, β, γ) = (z, 0, 0)`. -/
def memInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-- The reciprocal LogUp pole of the one committed record's root fingerprint. -/
def memPoleInv (z : K) (formula : Noun) : K := ((encC z formula).size)⁻¹

/-- The single live memory record `(f, f_t, 3, α)` served at `read_root`/`verify_child`. -/
def memReqRec (z α : K) (formula result : Noun) : ComputeTable.MemRec K :=
  ⟨encC z formula, encC z result, 3, α⟩

/-- A live memory record at an ARBITRARY axis (formula-open bakes in axis `3`). -/
def memReqRecAt (z α : K) (root child : Noun) (ax : ℕ) : ComputeTable.MemRec K :=
  ⟨encC z root, encC z child, ax, α⟩

/-- The `read_root` served row: reads the formula cell, decomposes it, and serves the record. -/
def memReadPub (z α : K) (formula result : Noun) : MemoryTable.Pub K where
  st := .read_root
  pt := ⟨encC z formula, 0, 0⟩
  lc := ⟨encC z formula, 4, 4⟩
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := memReqRec z α formula result
  ipre := 0
  icur := memPoleInv z formula

/-- The `decompose` served row: splits `[head result]` into its head and tail children. -/
def memDecomposePub (z : K) (formula head result : Noun) : MemoryTable.Pub K where
  st := .decompose
  pt := ⟨encC z formula, 4, 4⟩
  lc := ⟨encC z head, 0, 0⟩
  rc := ⟨encC z result, 4, 12⟩
  lcSt := .halt
  rcSt := .verify_child
  mem := ComputeTable.MemRec.zero
  ipre := memPoleInv z formula
  icur := memPoleInv z formula

/-- The `halt` leaf for the head child. -/
def memHeadPub (z : K) (formula head : Noun) : MemoryTable.Pub K where
  st := .halt
  pt := ⟨encC z head, 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := memPoleInv z formula
  icur := memPoleInv z formula

/-- The `verify_child` served row: pairs read/verify for the served result. -/
def memVerifyPub (z α : K) (formula result : Noun) : MemoryTable.Pub K where
  st := .verify_child
  pt := ⟨encC z result, 4, 12⟩
  lc := ⟨encC z result, 0, 0⟩
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := memReqRec z α formula result
  ipre := memPoleInv z formula
  icur := 0

/-- The `halt` leaf for the result child. -/
def memTailPub (z : K) (result : Noun) : MemoryTable.Pub K where
  st := .halt
  pt := ⟨encC z result, 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- The `read_root` memory-row skeleton serving the single request. -/
def memReadSkel (formula result : Noun) : MemoryRowSkeleton where
  state := .read_root
  parent := formula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then formula else .atom 0
  memoryRecord := fun _ => ⟨formula, result, 3⟩

/-- The `decompose` memory-row skeleton. -/
def memDecomposeSkel (formula head result : Noun) : MemoryRowSkeleton where
  state := .decompose
  parent := formula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then head else result
  memoryRecord := fun h => nomatch h

/-- A terminal `halt` leaf skeleton for the atom `a`. -/
def memHaltSkel (a : ℕ) : MemoryRowSkeleton where
  state := .halt
  parent := .atom a
  haltAtom := fun _ => a
  haltParent := by intro _; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-- The `verify_child` memory-row skeleton. -/
def memVerifySkel (formula result : Noun) : MemoryRowSkeleton where
  state := .verify_child
  parent := result
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => result
  memoryRecord := fun _ => ⟨formula, result, 3⟩

/-- A `read_root` skeleton at an ARBITRARY axis `ax` (the generic `memReadSkel`
    bakes in axis `3`; the `OP_0` slot record is at axis `1` on an atom). -/
def memReadSkelAt (root child : Noun) (ax : ℕ) : MemoryRowSkeleton where
  state := .read_root
  parent := root
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then root else .atom 0
  memoryRecord := fun _ => ⟨root, child, ax⟩

/-- A `verify_child` skeleton at an ARBITRARY axis `ax`. -/
def memVerifySkelAt (root child : Noun) (ax : ℕ) : MemoryRowSkeleton where
  state := .verify_child
  parent := child
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => child
  memoryRecord := fun _ => ⟨root, child, ax⟩

/-- The served forest of the `OP_1` request `[1 v]` (head `1`, result `v`) — the five-row
    reconstruction, with data rows via `encC` and stamps the verified `Op1Config` values. -/
def genOp1MemForest (z α : K) (v : ℕ) : List (NTree (GenMemoryRow K)) :=
  let formula : Noun := .cell (.atom 1) (.atom v)
  let head : Noun := .atom 1
  let result : Noun := .atom v
  let read : GenMemoryRow K :=
    { skel := memReadSkel formula result
      stamp := { state := .read_root, recordExponent := 1 }
      row := (.read_root, memInputs z, memReadPub z α formula result) }
  let decompose : GenMemoryRow K :=
    { skel := memDecomposeSkel formula head result
      stamp := { state := .decompose, recordExponent := 0 }
      row := (.decompose, memInputs z, memDecomposePub z formula head result) }
  let headN : GenMemoryRow K :=
    { skel := memHaltSkel 1
      stamp := { state := .halt, recordExponent := 0 }
      row := (.halt, memInputs z, memHeadPub z formula head) }
  let verify : GenMemoryRow K :=
    { skel := memVerifySkel formula result
      stamp := { state := .verify_child, recordExponent := 1 }
      row := (.verify_child, memInputs z, memVerifyPub z α formula result) }
  let tail : GenMemoryRow K :=
    { skel := memHaltSkel v
      stamp := { state := .halt, recordExponent := 0 }
      row := (.halt, memInputs z, memTailPub z result) }
  [.node read [.node decompose [.node headN [], .node verify [.node tail []]]]]

theorem genOp1MemForest_ne_nil (z α : K) (v : ℕ) :
    genOp1MemForest z α v ≠ [] := by
  simp only [genOp1MemForest]
  exact List.cons_ne_nil _ _

/-- BFS of the five-row OP1 reconstruction is the named stamp list in that
    order.  Abstract in the rows so `genOp1MemForest` does not need `encC`. -/
theorem genMemoryStamps_op1Shape
    (read decompose headN verify tail : GenMemoryRow K) :
    genMemoryStamps
      [.node read
        [.node decompose
          [.node headN [], .node verify [.node tail []]]]] =
      [read.stamp, decompose.stamp, headN.stamp, verify.stamp, tail.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_cons_eq
      [NTree.node headN [], NTree.node verify [NTree.node tail []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_singleton]
  simp only [NTree.children_node, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live OP1 memory stamps (`read_root` / `verify_child`) carry exponent `1`.
    Padding (`decompose` / `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_op1Shape_live
    (read decompose headN verify tail : GenMemoryRow K)
    (hread : read.stamp.state = .read_root ∧ read.stamp.recordExponent = 1)
    (hdec : decompose.stamp.state = .decompose)
    (hhead : headN.stamp.state = .halt)
    (hver : verify.stamp.state = .verify_child ∧ verify.stamp.recordExponent = 1)
    (htail : tail.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node read
        [.node decompose
          [.node headN [], .node verify [.node tail []]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  rw [genMemoryStamps_op1Shape] at hst
  rw [List.mem_cons] at hst
  rcases hst with h | hst
  · subst h; exact hread.2
  rw [List.mem_cons] at hst
  rcases hst with h | hst
  · subst h
    cases hlive with
    | inl hr => cases (hdec.symm.trans hr)
    | inr hv => cases (hdec.symm.trans hv)
  rw [List.mem_cons] at hst
  rcases hst with h | hst
  · subst h
    cases hlive with
    | inl hr => cases (hhead.symm.trans hr)
    | inr hv => cases (hhead.symm.trans hv)
  rw [List.mem_cons] at hst
  rcases hst with h | hst
  · subst h; exact hver.2
  rw [List.mem_singleton] at hst
  subst hst
  cases hlive with
  | inl hr => cases (htail.symm.trans hr)
  | inr hv => cases (htail.symm.trans hv)

/-- Live stamps of the served `OP_1` forest carry exponent `1`. -/
theorem genMemoryStamps_genOp1MemForest_live
    (z α : K) (v : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp1MemForest z α v))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  simp only [genOp1MemForest] at hst
  exact genMemoryStamps_op1Shape_live _ _ _ _ _
    ⟨rfl, rfl⟩ rfl rfl ⟨rfl, rfl⟩ rfl hst hlive

/-- OP1 served-tree topology: read → decompose → (halt-head, verify → halt-tail). -/
theorem memoryStampsWellFormed_op1Shape
    (read decompose headN verify tail : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hdec : decompose.stamp.state = decompose.skel.state)
    (hhead : headN.stamp.state = headN.skel.state)
    (hver : verify.stamp.state = verify.skel.state)
    (htail : tail.stamp.state = tail.skel.state) :
    memoryStampsWellFormed
      (.node read
        [.node decompose
          [.node headN [], .node verify [.node tail []]]]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_node2 _ _ _ hdec
      (memoryStampsWellFormed_leaf _ hhead)
      (memoryStampsWellFormed_node1 _ _ hver
        (memoryStampsWellFormed_leaf _ htail)))

theorem genOp1MemForest_memoryStampsWellFormed (z α : K) (v : ℕ) :
    ∀ root ∈ genOp1MemForest z α v, memoryStampsWellFormed root := by
  intro root hr
  simp only [genOp1MemForest] at hr
  rw [List.mem_singleton] at hr
  subst hr
  refine memoryStampsWellFormed_op1Shape _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  all_goals simp [memReadSkel, memDecomposeSkel, memHaltSkel, memVerifySkel]

/-- Axis-`1` atom slot topology: read → verify → halt (no decompose; `remainingAxis < 2`). -/
theorem memoryStampsWellFormed_axis1Shape
    (read verify halt : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hver : verify.stamp.state = verify.skel.state)
    (hhalt : halt.stamp.state = halt.skel.state) :
    memoryStampsWellFormed
      (.node read [.node verify [.node halt []]]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_node1 _ _ hver
      (memoryStampsWellFormed_leaf _ hhalt))

/-- Axis-`3` formula-open of a cell-tailed formula: one decompose to the tail, halt the
    atom head, and verify the cell child with no halt under verify (`remainingAxis = 1`
    at a cell) -/
theorem memoryStampsWellFormed_axis3CellTailShape
    (read decompose headN verify : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hdec : decompose.stamp.state = decompose.skel.state)
    (hhead : headN.stamp.state = headN.skel.state)
    (hver : verify.stamp.state = verify.skel.state) :
    memoryStampsWellFormed
      (.node read
        [.node decompose
          [.node headN [], .node verify []]]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_node2 _ _ _ hdec
      (memoryStampsWellFormed_leaf _ hhead)
      (memoryStampsWellFormed_leaf _ hver))

/-- Axis-`2` formula-tail of a cell whose head is itself a cell: one decompose
    to the head, then verify the cell child with no halt under verify and no
    halt sibling (the tail is also a cell) -/
theorem memoryStampsWellFormed_axis2CellHeadShape
    (read decompose verify : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hdec : decompose.stamp.state = decompose.skel.state)
    (hver : verify.stamp.state = verify.skel.state) :
    memoryStampsWellFormed
      (.node read
        [.node decompose
          [.node verify []]]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_node1 _ _ hdec
      (memoryStampsWellFormed_leaf _ hver))

/-- Axis-`2` formula-tail of a cell whose head is an atom: one decompose to the
    head, then verify the atom child with a halt under verify and no halt
    sibling (the tail is a cell) -/
theorem memoryStampsWellFormed_axis2AtomHeadShape
    (read decompose verify halt : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hdec : decompose.stamp.state = decompose.skel.state)
    (hver : verify.stamp.state = verify.skel.state)
    (hhalt : halt.stamp.state = halt.skel.state) :
    memoryStampsWellFormed
      (.node read
        [.node decompose
          [.node verify [.node halt []]]]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_node1 _ _ hdec
      (memoryStampsWellFormed_node1 _ _ hver
        (memoryStampsWellFormed_leaf _ hhalt)))

/-- Axis-`1` slot of a cell: read → verify with no halt under verify
    (`remainingAxis < 2`; cells cannot halt) -/
theorem memoryStampsWellFormed_axis1CellShape
    (read verify : GenMemoryRow K)
    (hread : read.stamp.state = read.skel.state)
    (hver : verify.stamp.state = verify.skel.state) :
    memoryStampsWellFormed
      (.node read [.node verify []]) :=
  memoryStampsWellFormed_node1 _ _ hread
    (memoryStampsWellFormed_leaf _ hver)

/-! ## Memory reconstruction of the branching two-request served forest

The `.cons` autocons root commits one request (`[leftF rightF]` @3) and each `OP_1` child commits
its own (`[1 v]`/`[1 w]` @3), so the served forest interleaves THREE `read_root`/`verify_child`
pairs into one tree: read the whole formula (serving the cons request), decompose it, read the left
subformula down to its own decompose/verify, then read the right subformula, verify the cons
request's child deep in the right branch, and finally read/verify the right subformula's own
request.  Every `read_root` is paired to its `verify_child` by the SHARED committed record
(fingerprint VALUE, never index — DESIGN-PRINCIPLES §0): the cons record `consRecCons` is carried by
both `read_root` at the root and `verify_child` deep right; `consRecL`/`consRecR` likewise pair each
child's own read/verify.  The field-valued LogUp accumulator `(ipre, icur)` threads in BFS order,
moving `+q` at each read and `-q` at each matching verify (`q = (pole rec)⁻¹`), telescoping
`0 → qCons → qCons+qL → qCons+qL+qR → qL+qR → qR → 0`.  All fingerprint columns are the computable
`encC` (`= enc`, `Encode.encC_eq`). -/

/-- Nouns of the branching program `[[1 v] [1 w]]`. -/
def consLeftF (v : ℕ) : Noun := .cell (.atom 1) (.atom v)
def consRightF (w : ℕ) : Noun := .cell (.atom 1) (.atom w)
def consForm (v w : ℕ) : Noun := .cell (consLeftF v) (consRightF w)

/-- The three LogUp pole reciprocals (`β = γ = 0`, so the pole is the root fingerprint size). -/
def consQCons (z : K) (v w : ℕ) : K := ((encC z (consForm v w)).size)⁻¹
def consQL (z : K) (v : ℕ) : K := ((encC z (consLeftF v)).size)⁻¹
def consQR (z : K) (w : ℕ) : K := ((encC z (consRightF w)).size)⁻¹

/-- The three committed records, timestamps `α, α², α³`. -/
def consRecCons (z α : K) (v w : ℕ) : ComputeTable.MemRec K :=
  ⟨encC z (consForm v w), encC z (consRightF w), 3, α⟩
def consRecL (z α : K) (v : ℕ) : ComputeTable.MemRec K :=
  ⟨encC z (consLeftF v), encC z (.atom v), 3, α ^ 2⟩
def consRecR (z α : K) (w : ℕ) : ComputeTable.MemRec K :=
  ⟨encC z (consRightF w), encC z (.atom w), 3, α ^ 3⟩

/-- Generic served-forest `read_root` pub: reads `pt`, decomposes to `lc`, serves `rec`. -/
def servReadPub (pt lc : MemoryTable.Cell K) (rec : ComputeTable.MemRec K) (ipre icur : K) :
    MemoryTable.Pub K where
  st := .read_root
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := rec
  ipre := ipre
  icur := icur

/-- Generic served-forest `decompose` pub: splits `pt` into children `lc`/`rc`. -/
def servDecPub (pt lc rc : MemoryTable.Cell K) (lcSt rcSt : MemoryTable.MState) (acc : K) :
    MemoryTable.Pub K where
  st := .decompose
  pt := pt
  lc := lc
  rc := rc
  lcSt := lcSt
  rcSt := rcSt
  mem := ComputeTable.MemRec.zero
  ipre := acc
  icur := acc

/-- Generic served-forest `verify_child` pub: verifies `pt` against its matching read via `rec`. -/
def servVerifyPub (pt lc : MemoryTable.Cell K) (rec : ComputeTable.MemRec K) (ipre icur : K) :
    MemoryTable.Pub K where
  st := .verify_child
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := rec
  ipre := ipre
  icur := icur

/-- Generic served-forest terminal `halt` pub for the atom `k`, accumulator held at `acc`. -/
def servHaltPub (z : K) (k : ℕ) (acc : K) : MemoryTable.Pub K where
  st := .halt
  pt := ⟨encC z (.atom k), 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := acc
  icur := acc

/-! ### The thirteen served-forest pubs, accumulator threaded in BFS order -/

def consPReadF (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (consForm v w), 0, 0⟩ ⟨encC z (consForm v w), α, α⟩
    (consRecCons z α v w) 0 (consQCons z v w)
def consPDecF (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servDecPub ⟨encC z (consForm v w), α, α⟩ ⟨encC z (consLeftF v), 0, 0⟩
    ⟨encC z (consRightF w), α, 3 * α⟩ .read_root .read_root (consQCons z v w)
def consPReadL (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (consLeftF v), 0, 0⟩ ⟨encC z (consLeftF v), α ^ 2, α ^ 2⟩
    (consRecL z α v) (consQCons z v w) (consQCons z v w + consQL z v)
def consPReadR (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (consRightF w), α, 3 * α⟩ ⟨encC z (consRightF w), α ^ 3 + α, α ^ 3 + 3 * α⟩
    (consRecR z α w) (consQCons z v w + consQL z v) (consQCons z v w + consQL z v + consQR z w)
def consPDecL (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servDecPub ⟨encC z (consLeftF v), α ^ 2, α ^ 2⟩ ⟨encC z (.atom 1), 0, 0⟩
    ⟨encC z (.atom v), α ^ 2, 3 * α ^ 2⟩ .halt .verify_child
    (consQCons z v w + consQL z v + consQR z w)
def consPVerifyF (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (consRightF w), α ^ 3 + α, α ^ 3 + 3 * α⟩ ⟨encC z (consRightF w), α ^ 3, α ^ 3⟩
    (consRecCons z α v w) (consQCons z v w + consQL z v + consQR z w) (consQL z v + consQR z w)
def consPHaltL1 (z : K) (v w : ℕ) : MemoryTable.Pub K :=
  servHaltPub z 1 (consQL z v + consQR z w)
def consPVerifyL (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (.atom v), α ^ 2, 3 * α ^ 2⟩ ⟨encC z (.atom v), 0, 0⟩
    (consRecL z α v) (consQL z v + consQR z w) (consQR z w)
def consPDecR (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servDecPub ⟨encC z (consRightF w), α ^ 3, α ^ 3⟩ ⟨encC z (.atom 1), 0, 0⟩
    ⟨encC z (.atom w), α ^ 3, 3 * α ^ 3⟩ .halt .verify_child (consQR z w)
def consPHaltL5 (z : K) (v w : ℕ) : MemoryTable.Pub K :=
  servHaltPub z v (consQR z w)
def consPHaltR1 (z : K) (w : ℕ) : MemoryTable.Pub K :=
  servHaltPub z 1 (consQR z w)
def consPVerifyR (z α : K) (w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (.atom w), α ^ 3, 3 * α ^ 3⟩ ⟨encC z (.atom w), 0, 0⟩
    (consRecR z α w) (consQR z w) 0
def consPHaltR6 (z : K) (w : ℕ) : MemoryTable.Pub K :=
  servHaltPub z w 0

/-! ### The thirteen served-forest rows and their tree -/

/-- Package a served pub with its skeleton and Nat timestamp exponent into a `GenMemoryRow`. -/
def servRow (skel : MemoryRowSkeleton) (recExp : ℕ) (z : K) (pub : MemoryTable.Pub K) :
    GenMemoryRow K :=
  { skel := skel
    stamp := { state := pub.st, recordExponent := recExp }
    row := (pub.st, memInputs z, pub) }

theorem servRow_states_agree (skel : MemoryRowSkeleton) (recExp : ℕ) (z : K)
    (pub : MemoryTable.Pub K) (h : pub.st = skel.state) :
    (servRow skel recExp z pub).stamp.state =
      (servRow skel recExp z pub).skel.state := by
  simp [servRow, h]

def consMemRowReadF (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (consForm v w) (consRightF w)) 1 z (consPReadF z α v w)
def consMemRowDecF (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (consForm v w) (consLeftF v) (consRightF w)) 0 z (consPDecF z α v w)
def consMemRowReadL (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (consLeftF v) (.atom v)) 2 z (consPReadL z α v w)
def consMemRowReadR (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (consRightF w) (.atom w)) 3 z (consPReadR z α v w)
def consMemRowDecL (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (consLeftF v) (.atom 1) (.atom v)) 0 z (consPDecL z α v w)
def consMemRowVerifyF (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (consForm v w) (consRightF w)) 1 z (consPVerifyF z α v w)
def consMemRowHaltL1 (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel 1) 0 z (consPHaltL1 z v w)
def consMemRowVerifyL (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (consLeftF v) (.atom v)) 2 z (consPVerifyL z α v w)
def consMemRowDecR (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (consRightF w) (.atom 1) (.atom w)) 0 z (consPDecR z α v w)
def consMemRowHaltL5 (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel v) 0 z (consPHaltL5 z v w)
def consMemRowHaltR1 (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel 1) 0 z (consPHaltR1 z w)
def consMemRowVerifyR (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (consRightF w) (.atom w)) 3 z (consPVerifyR z α w)
def consMemRowHaltR6 (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel w) 0 z (consPHaltR6 z w)

/-- **`genConsMemForest`.**  The thirteen-row served memory forest of the branching program
    `[[1 v] [1 w]]`, emitted as pure data with `encC` fingerprints and the BFS-threaded LogUp
    accumulator.  Its tree topology mirrors the verified `ConsConfig.rootTree`. -/
def genConsMemForest (z α : K) (v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  [.node (consMemRowReadF z α v w)
    [.node (consMemRowDecF z α v w)
      [.node (consMemRowReadL z α v w)
        [.node (consMemRowDecL z α v w)
          [.node (consMemRowHaltL1 z α v w) [],
           .node (consMemRowVerifyL z α v w) [.node (consMemRowHaltL5 z α v w) []]]],
       .node (consMemRowReadR z α v w)
        [.node (consMemRowVerifyF z α v w)
          [.node (consMemRowDecR z α v w)
            [.node (consMemRowHaltR1 z α v w) [],
             .node (consMemRowVerifyR z α v w) [.node (consMemRowHaltR6 z α v w) []]]]]]]]

theorem genConsMemForest_ne_nil (z α : K) (v w : ℕ) :
    genConsMemForest z α v w ≠ [] := by
  simp only [genConsMemForest]
  exact List.cons_ne_nil _ _

/-- Cons served-tree topology: ReadF → DecF → (ReadL subtree, ReadR subtree). -/
theorem memoryStampsWellFormed_consShape
    (ReadF DecF ReadL DecL HaltL1 VerifyL HaltL5
      ReadR VerifyF DecR HaltR1 VerifyR HaltR6 : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = ReadF.skel.state)
    (hDecF : DecF.stamp.state = DecF.skel.state)
    (hReadL : ReadL.stamp.state = ReadL.skel.state)
    (hDecL : DecL.stamp.state = DecL.skel.state)
    (hHaltL1 : HaltL1.stamp.state = HaltL1.skel.state)
    (hVerifyL : VerifyL.stamp.state = VerifyL.skel.state)
    (hHaltL5 : HaltL5.stamp.state = HaltL5.skel.state)
    (hReadR : ReadR.stamp.state = ReadR.skel.state)
    (hVerifyF : VerifyF.stamp.state = VerifyF.skel.state)
    (hDecR : DecR.stamp.state = DecR.skel.state)
    (hHaltR1 : HaltR1.stamp.state = HaltR1.skel.state)
    (hVerifyR : VerifyR.stamp.state = VerifyR.skel.state)
    (hHaltR6 : HaltR6.stamp.state = HaltR6.skel.state) :
    memoryStampsWellFormed
      (.node ReadF
        [.node DecF
          [.node ReadL
            [.node DecL
              [.node HaltL1 [],
               .node VerifyL [.node HaltL5 []]]],
           .node ReadR
            [.node VerifyF
              [.node DecR
                [.node HaltR1 [],
                 .node VerifyR [.node HaltR6 []]]]]]]) :=
  memoryStampsWellFormed_node1 _ _ hReadF
    (memoryStampsWellFormed_node2 _ _ _ hDecF
      (memoryStampsWellFormed_node1 _ _ hReadL
        (memoryStampsWellFormed_node2 _ _ _ hDecL
          (memoryStampsWellFormed_leaf _ hHaltL1)
          (memoryStampsWellFormed_node1 _ _ hVerifyL
            (memoryStampsWellFormed_leaf _ hHaltL5))))
      (memoryStampsWellFormed_node1 _ _ hReadR
        (memoryStampsWellFormed_node1 _ _ hVerifyF
          (memoryStampsWellFormed_node2 _ _ _ hDecR
            (memoryStampsWellFormed_leaf _ hHaltR1)
            (memoryStampsWellFormed_node1 _ _ hVerifyR
              (memoryStampsWellFormed_leaf _ hHaltR6))))))

theorem genConsMemForest_memoryStampsWellFormed (z α : K) (v w : ℕ) :
    ∀ root ∈ genConsMemForest z α v w, memoryStampsWellFormed root := by
  intro root hr
  simp only [genConsMemForest] at hr
  rw [List.mem_singleton] at hr
  subst hr
  refine memoryStampsWellFormed_consShape _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [consMemRowReadF, consMemRowDecF, consMemRowReadL, consMemRowDecL,
    consMemRowHaltL1, consMemRowVerifyL, consMemRowHaltL5, consMemRowReadR,
    consMemRowVerifyF, consMemRowDecR, consMemRowHaltR1, consMemRowVerifyR,
    consMemRowHaltR6, servRow, consPReadF, consPDecF, consPReadL, consPReadR,
    consPDecL, consPVerifyF, consPHaltL1, consPVerifyL, consPDecR, consPHaltL5,
    consPHaltR1, consPVerifyR, consPHaltR6, servReadPub, servDecPub,
    servVerifyPub, servHaltPub, memReadSkel, memDecomposeSkel, memHaltSkel,
    memVerifySkel]

/-- BFS of the thirteen-row cons reconstruction is the named stamp list in that
    order.  Abstract in the rows so `genConsMemForest` does not need `encC`. -/
theorem genMemoryStamps_consShape
    (ReadF DecF ReadL DecL HaltL1 VerifyL HaltL5
      ReadR VerifyF DecR HaltR1 VerifyR HaltR6 : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node ReadL
            [.node DecL
              [.node HaltL1 [],
               .node VerifyL [.node HaltL5 []]]],
           .node ReadR
            [.node VerifyF
              [.node DecR
                [.node HaltR1 [],
                 .node VerifyR [.node HaltR6 []]]]]]]] =
      [ReadF.stamp, DecF.stamp, ReadL.stamp, ReadR.stamp, DecL.stamp,
        VerifyF.stamp, HaltL1.stamp, VerifyL.stamp, DecR.stamp, HaltL5.stamp,
        HaltR1.stamp, VerifyR.stamp, HaltR6.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_cons_eq
      [NTree.node ReadL
        [NTree.node DecL
          [NTree.node HaltL1 [],
           NTree.node VerifyL [NTree.node HaltL5 []]]],
       NTree.node ReadR
        [NTree.node VerifyF
          [NTree.node DecR
            [NTree.node HaltR1 [],
             NTree.node VerifyR [NTree.node HaltR6 []]]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecL
        [NTree.node HaltL1 [],
         NTree.node VerifyL [NTree.node HaltL5 []]],
       NTree.node VerifyF
        [NTree.node DecR
          [NTree.node HaltR1 [],
           NTree.node VerifyR [NTree.node HaltR6 []]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltL1 [],
       NTree.node VerifyL [NTree.node HaltL5 []],
       NTree.node DecR
        [NTree.node HaltR1 [],
         NTree.node VerifyR [NTree.node HaltR6 []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltL5 [], NTree.node HaltR1 [],
       NTree.node VerifyR [NTree.node HaltR6 []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_singleton]
  simp only [NTree.children_node, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live cons memory stamps (`read_root` / `verify_child`) carry exponent
    `1`, `2`, or `3`.  Padding (`decompose` / `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_consShape_live
    (ReadF DecF ReadL DecL HaltL1 VerifyL HaltL5
      ReadR VerifyF DecR HaltR1 VerifyR HaltR6 : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hDecF : DecF.stamp.state = .decompose)
    (hReadL : ReadL.stamp.state = .read_root ∧ ReadL.stamp.recordExponent = 2)
    (hReadR : ReadR.stamp.state = .read_root ∧ ReadR.stamp.recordExponent = 3)
    (hDecL : DecL.stamp.state = .decompose)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hHaltL1 : HaltL1.stamp.state = .halt)
    (hVerifyL : VerifyL.stamp.state = .verify_child ∧
      VerifyL.stamp.recordExponent = 2)
    (hDecR : DecR.stamp.state = .decompose)
    (hHaltL5 : HaltL5.stamp.state = .halt)
    (hHaltR1 : HaltR1.stamp.state = .halt)
    (hVerifyR : VerifyR.stamp.state = .verify_child ∧
      VerifyR.stamp.recordExponent = 3)
    (hHaltR6 : HaltR6.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node ReadL
            [.node DecL
              [.node HaltL1 [],
               .node VerifyL [.node HaltL5 []]]],
           .node ReadR
            [.node VerifyF
              [.node DecR
                [.node HaltR1 [],
                 .node VerifyR [.node HaltR6 []]]]]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  rw [genMemoryStamps_consShape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl hReadF.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h; exact Or.inr (Or.inl hReadL.2)
  · subst h; exact Or.inr (Or.inr hReadR.2)
  · subst h
    cases hlive with
    | inl hr => cases (hDecL.symm.trans hr)
    | inr hv => cases (hDecL.symm.trans hv)
  · subst h; exact Or.inl hVerifyF.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltL1.symm.trans hr)
    | inr hv => cases (hHaltL1.symm.trans hv)
  · subst h; exact Or.inr (Or.inl hVerifyL.2)
  · subst h
    cases hlive with
    | inl hr => cases (hDecR.symm.trans hr)
    | inr hv => cases (hDecR.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltL5.symm.trans hr)
    | inr hv => cases (hHaltL5.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltR1.symm.trans hr)
    | inr hv => cases (hHaltR1.symm.trans hv)
  · subst h; exact Or.inr (Or.inr hVerifyR.2)
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltR6.symm.trans hr)
      | inr hv => cases (hHaltR6.symm.trans hv)
    · cases hempty

/-- Live stamps of the served cons forest carry exponent `1`, `2`, or `3`. -/
theorem genMemoryStamps_genConsMemForest_live
    (z α : K) (v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genConsMemForest z α v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  simp only [genConsMemForest] at hst
  exact genMemoryStamps_consShape_live _ _ _ _ _ _ _ _ _ _ _ _ _
    ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩
    rfl rfl rfl ⟨rfl, rfl⟩ rfl hst hlive

/-! ## Memory reconstruction of the `OP_0` identity-axis leaf

    The leaf program `*[.atom s [0 1]] =.atom s` commits two live records on independent forest
    roots (no interleaving): `mr1 = ⟨[0 1], 1, 3⟩` (formula-open, the same five-row OP1 topology)
    and `mr2 = ⟨subject, subject, 1⟩` (slot `/[1 subject]`, remaining axis `< 2` so
    `read → verify → halt`).  Each tree LogUp-telescopes `0 → q → 0` on its own.  Do not name this
    `genOp0MemForest` — that name is the OP4-parent + OP0-child fixture in `Op0Gen.lean`. -/

/-- The formula `[0 1]` of the identity-axis leaf. -/
def op0LeafForm : Noun := .cell (.atom 0) (.atom 1)

def op0LeafMemRowReadF (z α : K) : GenMemoryRow K :=
  servRow (memReadSkel op0LeafForm (.atom 1)) 1 z (memReadPub z α op0LeafForm (.atom 1))
def op0LeafMemRowDecF (z α : K) : GenMemoryRow K :=
  servRow (memDecomposeSkel op0LeafForm (.atom 0) (.atom 1)) 0 z
    (memDecomposePub z op0LeafForm (.atom 0) (.atom 1))
def op0LeafMemRowHaltH (z α : K) : GenMemoryRow K :=
  servRow (memHaltSkel 0) 0 z (memHeadPub z op0LeafForm (.atom 0))
def op0LeafMemRowVerifyF (z α : K) : GenMemoryRow K :=
  servRow (memVerifySkel op0LeafForm (.atom 1)) 1 z (memVerifyPub z α op0LeafForm (.atom 1))
def op0LeafMemRowHaltT (z α : K) : GenMemoryRow K :=
  servRow (memHaltSkel 1) 0 z (memTailPub z (.atom 1))

/-- The slot record `/[1 (.atom s)] =.atom s` at timestamp `α²`. -/
def op0LeafRecSlot (z α : K) (s : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 2) (.atom s) (.atom s) 1
def op0LeafQSlot (z : K) (s : ℕ) : K := memPoleInv z (.atom s)

def op0LeafPReadS (z α : K) (s : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (.atom s), 0, 0⟩ ⟨encC z (.atom s), 0, 0⟩
    (op0LeafRecSlot z α s) 0 (op0LeafQSlot z s)
def op0LeafPVerifyS (z α : K) (s : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (.atom s), 0, 0⟩ ⟨encC z (.atom s), 0, 0⟩
    (op0LeafRecSlot z α s) (op0LeafQSlot z s) 0
def op0LeafPHaltS (z : K) (s : ℕ) : MemoryTable.Pub K :=
  servHaltPub z s 0

def op0LeafMemRowReadS (z α : K) (s : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (.atom s) (.atom s) 1) 2 z (op0LeafPReadS z α s)
def op0LeafMemRowVerifyS (z α : K) (s : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (.atom s) (.atom s) 1) 2 z (op0LeafPVerifyS z α s)
def op0LeafMemRowHaltS (z α : K) (s : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel s) 0 z (op0LeafPHaltS z s)

/-- **`genOp0LeafMemForest`.**  Two independent served roots for `*[.atom s [0 1]]`. -/
def genOp0LeafMemForest (z α : K) (s : ℕ) : List (NTree (GenMemoryRow K)) :=
  [.node (op0LeafMemRowReadF z α)
    [.node (op0LeafMemRowDecF z α)
      [.node (op0LeafMemRowHaltH z α) [],
       .node (op0LeafMemRowVerifyF z α) [.node (op0LeafMemRowHaltT z α) []]]],
   .node (op0LeafMemRowReadS z α s)
    [.node (op0LeafMemRowVerifyS z α s)
      [.node (op0LeafMemRowHaltS z α s) []]]]

theorem genOp0LeafMemForest_ne_nil (z α : K) (s : ℕ) :
    genOp0LeafMemForest z α s ≠ [] := by
  simp only [genOp0LeafMemForest]
  exact List.cons_ne_nil _ _

theorem genOp0LeafMemForest_memoryStampsWellFormed (z α : K) (s : ℕ) :
    ∀ root ∈ genOp0LeafMemForest z α s, memoryStampsWellFormed root := by
  intro root hr
  simp only [genOp0LeafMemForest] at hr
  rw [List.mem_cons, List.mem_singleton] at hr
  obtain rfl | rfl := hr
  · refine memoryStampsWellFormed_op1Shape _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    all_goals simp [op0LeafMemRowReadF, op0LeafMemRowDecF, op0LeafMemRowHaltH,
      op0LeafMemRowVerifyF, op0LeafMemRowHaltT, servRow, memReadPub, memDecomposePub,
      memHeadPub, memVerifyPub, memTailPub, memReadSkel, memDecomposeSkel,
      memHaltSkel, memVerifySkel]
  · refine memoryStampsWellFormed_axis1Shape _ _ _ ?_ ?_ ?_
    all_goals simp [op0LeafMemRowReadS, op0LeafMemRowVerifyS, op0LeafMemRowHaltS,
      servRow, op0LeafPReadS, op0LeafPVerifyS, op0LeafPHaltS, servReadPub,
      servVerifyPub, servHaltPub, memReadSkelAt, memVerifySkelAt, memHaltSkel]

/-- BFS of the two-root OP0 identity-axis leaf is the named stamp list in that
    order.  Abstract in the rows so `genOp0LeafMemForest` does not need `encC`. -/
theorem genMemoryStamps_op0LeafShape
    (ReadF DecF HaltH VerifyF HaltT ReadS VerifyS HaltS : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF [.node HaltT []]]],
       .node ReadS
        [.node VerifyS
          [.node HaltS []]]] =
      [ReadF.stamp, ReadS.stamp, DecF.stamp, VerifyS.stamp, HaltH.stamp,
        VerifyF.stamp, HaltS.stamp, HaltT.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_cons_eq
      [NTree.node ReadF
        [NTree.node DecF
          [NTree.node HaltH [],
           NTree.node VerifyF [NTree.node HaltT []]]],
       NTree.node ReadS
        [NTree.node VerifyS [NTree.node HaltS []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecF
        [NTree.node HaltH [],
         NTree.node VerifyF [NTree.node HaltT []]],
       NTree.node VerifyS [NTree.node HaltS []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltH [],
       NTree.node VerifyF [NTree.node HaltT []],
       NTree.node HaltS []]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_singleton]
  simp only [NTree.children_node, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live OP0 identity-axis stamps (`read_root` / `verify_child`) carry exponent
    `1` or `2`.  Padding (`decompose` / `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_op0LeafShape_live
    (ReadF DecF HaltH VerifyF HaltT ReadS VerifyS HaltS : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hReadS : ReadS.stamp.state = .read_root ∧ ReadS.stamp.recordExponent = 2)
    (hDecF : DecF.stamp.state = .decompose)
    (hVerifyS : VerifyS.stamp.state = .verify_child ∧
      VerifyS.stamp.recordExponent = 2)
    (hHaltH : HaltH.stamp.state = .halt)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hHaltS : HaltS.stamp.state = .halt)
    (hHaltT : HaltT.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF [.node HaltT []]]],
       .node ReadS
        [.node VerifyS
          [.node HaltS []]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  rw [genMemoryStamps_op0LeafShape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h
  · subst h; exact Or.inl hReadF.2
  · subst h; exact Or.inr hReadS.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h; exact Or.inr hVerifyS.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltH.symm.trans hr)
    | inr hv => cases (hHaltH.symm.trans hv)
  · subst h; exact Or.inl hVerifyF.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltS.symm.trans hr)
    | inr hv => cases (hHaltS.symm.trans hv)
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltT.symm.trans hr)
      | inr hv => cases (hHaltT.symm.trans hv)
    · cases hempty

/-- Live stamps of the served OP0 identity-axis forest carry exponent `1` or `2`. -/
theorem genMemoryStamps_genOp0LeafMemForest_live
    (z α : K) (s : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp0LeafMemForest z α s))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genOp0LeafMemForest] at hst
  exact genMemoryStamps_op0LeafShape_live _ _ _ _ _ _ _ _
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl rfl hst hlive

/-! ## Memory reconstruction of a unary wrapper around `OP_1`

    Programs `[4 [1 v]]` / `[3 [1 v]]` commit one formula-open record at the parent
    (`⟨[op [1 v]], [1 v], 3⟩`) plus the inner `OP_1` formula-open.  The parent tail is a
    cell, so the axis-`3` tree is four rows (`read → decompose → (halt-head, verify)` with
    no halt under verify).  The inner `[1 v]` is the existing five-row OP1 tree.  Two
    independent roots; this is timestamp-skeleton WF (`stamp.state = skel.state`), not
    nested NMR descent and not a `ForestExponentOrder` tick. -/

/-- The unary formula `[op [1 v]]`. -/
def unaryOp1Form (op v : ℕ) : Noun := .cell (.atom op) (.cell (.atom 1) (.atom v))
/-- The cell tail `[1 v]` of a unary wrapper. -/
def unaryOp1Tail (v : ℕ) : Noun := .cell (.atom 1) (.atom v)

def unaryOp1MemRowReadF (z α : K) (op v : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (unaryOp1Form op v) (unaryOp1Tail v)) 1 z
    (memReadPub z α (unaryOp1Form op v) (unaryOp1Tail v))
def unaryOp1MemRowDecF (z α : K) (op v : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (unaryOp1Form op v) (.atom op) (unaryOp1Tail v)) 0 z
    (memDecomposePub z (unaryOp1Form op v) (.atom op) (unaryOp1Tail v))
def unaryOp1MemRowHaltH (z α : K) (op v : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel op) 0 z (memHeadPub z (unaryOp1Form op v) (.atom op))
def unaryOp1MemRowVerifyF (z α : K) (op v : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (unaryOp1Form op v) (unaryOp1Tail v)) 1 z
    (memVerifyPub z α (unaryOp1Form op v) (unaryOp1Tail v))

/-- Parent axis-`3` cell-tail tree plus the inner `OP_1` five-row forest. -/
def genUnaryOp1MemForest (z α : K) (op v : ℕ) : List (NTree (GenMemoryRow K)) :=
  .node (unaryOp1MemRowReadF z α op v)
    [.node (unaryOp1MemRowDecF z α op v)
      [.node (unaryOp1MemRowHaltH z α op v) [],
       .node (unaryOp1MemRowVerifyF z α op v) []]]
  :: genOp1MemForest z α v

def genOp4Op1MemForest (z α : K) (v : ℕ) : List (NTree (GenMemoryRow K)) :=
  genUnaryOp1MemForest z α 4 v
def genOp3Op1MemForest (z α : K) (v : ℕ) : List (NTree (GenMemoryRow K)) :=
  genUnaryOp1MemForest z α 3 v

theorem genUnaryOp1MemForest_ne_nil (z α : K) (op v : ℕ) :
    genUnaryOp1MemForest z α op v ≠ [] := by
  simp only [genUnaryOp1MemForest]
  exact List.cons_ne_nil _ _

theorem genOp4Op1MemForest_ne_nil (z α : K) (v : ℕ) :
    genOp4Op1MemForest z α v ≠ [] :=
  genUnaryOp1MemForest_ne_nil z α 4 v

theorem genOp3Op1MemForest_ne_nil (z α : K) (v : ℕ) :
    genOp3Op1MemForest z α v ≠ [] :=
  genUnaryOp1MemForest_ne_nil z α 3 v

theorem genUnaryOp1MemForest_memoryStampsWellFormed (z α : K) (op v : ℕ) :
    ∀ root ∈ genUnaryOp1MemForest z α op v, memoryStampsWellFormed root := by
  intro root hr
  simp only [genUnaryOp1MemForest] at hr
  rw [List.mem_cons] at hr
  obtain rfl | hr := hr
  · refine memoryStampsWellFormed_axis3CellTailShape _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [unaryOp1MemRowReadF, unaryOp1MemRowDecF, unaryOp1MemRowHaltH,
      unaryOp1MemRowVerifyF, servRow, memReadPub, memDecomposePub, memHeadPub,
      memVerifyPub, memReadSkel, memDecomposeSkel, memHaltSkel, memVerifySkel]
  · exact genOp1MemForest_memoryStampsWellFormed z α v root hr

theorem genOp4Op1MemForest_memoryStampsWellFormed (z α : K) (v : ℕ) :
    ∀ root ∈ genOp4Op1MemForest z α v, memoryStampsWellFormed root :=
  genUnaryOp1MemForest_memoryStampsWellFormed z α 4 v

theorem genOp3Op1MemForest_memoryStampsWellFormed (z α : K) (v : ℕ) :
    ∀ root ∈ genOp3Op1MemForest z α v, memoryStampsWellFormed root :=
  genUnaryOp1MemForest_memoryStampsWellFormed z α 3 v

/-- BFS of the two-root unary wrapper (parent axis-`3` cell-tail plus inner
    OP1) is the named stamp list in that order.  Abstract in the rows so
    `genUnaryOp1MemForest` does not need `encC`. -/
theorem genMemoryStamps_unaryOp1Shape
    (ReadF DecF HaltH VerifyF ReadI DecI HaltHI VerifyI HaltT : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadI
        [.node DecI
          [.node HaltHI [],
           .node VerifyI [.node HaltT []]]]] =
      [ReadF.stamp, ReadI.stamp, DecF.stamp, DecI.stamp, HaltH.stamp,
        VerifyF.stamp, HaltHI.stamp, VerifyI.stamp, HaltT.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_cons_eq
      [NTree.node ReadF
        [NTree.node DecF
          [NTree.node HaltH [],
           NTree.node VerifyF []]],
       NTree.node ReadI
        [NTree.node DecI
          [NTree.node HaltHI [],
           NTree.node VerifyI [NTree.node HaltT []]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecF
        [NTree.node HaltH [],
         NTree.node VerifyF []],
       NTree.node DecI
        [NTree.node HaltHI [],
         NTree.node VerifyI [NTree.node HaltT []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltH [],
       NTree.node VerifyF [],
       NTree.node HaltHI [],
       NTree.node VerifyI [NTree.node HaltT []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_singleton]
  simp only [NTree.children_node, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live unary-wrapper stamps (`read_root` / `verify_child`) carry exponent
    `1`.  Both independent roots share `α¹`.  Padding (`decompose` / `halt`)
    is excluded by `hlive`. -/
theorem genMemoryStamps_unaryOp1Shape_live
    (ReadF DecF HaltH VerifyF ReadI DecI HaltHI VerifyI HaltT : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hReadI : ReadI.stamp.state = .read_root ∧ ReadI.stamp.recordExponent = 1)
    (hDecF : DecF.stamp.state = .decompose)
    (hDecI : DecI.stamp.state = .decompose)
    (hHaltH : HaltH.stamp.state = .halt)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hHaltHI : HaltHI.stamp.state = .halt)
    (hVerifyI : VerifyI.stamp.state = .verify_child ∧
      VerifyI.stamp.recordExponent = 1)
    (hHaltT : HaltT.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadI
        [.node DecI
          [.node HaltHI [],
           .node VerifyI [.node HaltT []]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  rw [genMemoryStamps_unaryOp1Shape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h | h
  · subst h; exact hReadF.2
  · subst h; exact hReadI.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecI.symm.trans hr)
    | inr hv => cases (hDecI.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltH.symm.trans hr)
    | inr hv => cases (hHaltH.symm.trans hv)
  · subst h; exact hVerifyF.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHI.symm.trans hr)
    | inr hv => cases (hHaltHI.symm.trans hv)
  · subst h; exact hVerifyI.2
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltT.symm.trans hr)
      | inr hv => cases (hHaltT.symm.trans hv)
    · cases hempty

/-- Live stamps of the served unary wrapper forest carry exponent `1`. -/
theorem genMemoryStamps_genUnaryOp1MemForest_live
    (z α : K) (op v : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genUnaryOp1MemForest z α op v))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  simp only [genUnaryOp1MemForest, genOp1MemForest] at hst
  exact genMemoryStamps_unaryOp1Shape_live _ _ _ _ _ _ _ _ _
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl hst hlive

theorem genMemoryStamps_genOp4Op1MemForest_live
    (z α : K) (v : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp4Op1MemForest z α v))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  simp only [genOp4Op1MemForest] at hst
  exact genMemoryStamps_genUnaryOp1MemForest_live z α 4 v hst hlive

theorem genMemoryStamps_genOp3Op1MemForest_live
    (z α : K) (v : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp3Op1MemForest z α v))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 := by
  simp only [genOp3Op1MemForest] at hst
  exact genMemoryStamps_genUnaryOp1MemForest_live z α 3 v hst hlive

/-! ## Memory reconstruction of a two-record star around two `OP_1` leaves

    Programs `[5 [1 v] [1 w]]` / `[7 [1 v] [1 w]]` / `[8 [1 v] [1 w]]` /
    `[2 [1 v] [1 w]]` commit two live records at the parent: formula-open
    `⟨[op [[1 v] [1 w]]], [[1 v] [1 w]], 3⟩` (four-row axis-`3` cell-tail)
    and formula-tail `⟨[[1 v] [1 w]], [1 v], 2⟩` (three-row axis-`2`
    cell-head: both children of the tail are cells, so no halt sibling
    and no halt under verify).  Plus the two inner `OP_1` five-row
    forests.  Four independent roots; timestamp-skeleton WF only, not
    nested NMR and not a `ForestExponentOrder` tick.  Do not import
    `Op5Gen` / `Op9Gen`. -/

/-- The two-record star formula `[op [1 v] [1 w]]`. -/
def binaryOp1Form (op v w : ℕ) : Noun := .cell (.atom op) (consForm v w)

def binaryOp1MemRowReadF (z α : K) (op v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (binaryOp1Form op v w) (consForm v w)) 1 z
    (memReadPub z α (binaryOp1Form op v w) (consForm v w))
def binaryOp1MemRowDecF (z α : K) (op v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (binaryOp1Form op v w) (.atom op) (consForm v w)) 0 z
    (memDecomposePub z (binaryOp1Form op v w) (.atom op) (consForm v w))
def binaryOp1MemRowHaltH (z α : K) (op v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel op) 0 z (memHeadPub z (binaryOp1Form op v w) (.atom op))
def binaryOp1MemRowVerifyF (z α : K) (op v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (binaryOp1Form op v w) (consForm v w)) 1 z
    (memVerifyPub z α (binaryOp1Form op v w) (consForm v w))

/-- Axis-`2` formula-tail record of `[[1 v] [1 w]]` at timestamp `α²`. -/
def binaryOp1RecT (z α : K) (v w : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 2) (consForm v w) (consLeftF v) 2
def binaryOp1QT (z : K) (v w : ℕ) : K := memPoleInv z (consForm v w)

def binaryOp1PReadT (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (consForm v w), 0, 0⟩ ⟨encC z (consForm v w), 4, 4⟩
    (binaryOp1RecT z α v w) 0 (binaryOp1QT z v w)
def binaryOp1PVerifyT (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (consLeftF v), 4, 12⟩ ⟨encC z (consLeftF v), 0, 0⟩
    (binaryOp1RecT z α v w) (binaryOp1QT z v w) 0

def binaryOp1MemRowReadT (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (consForm v w) (consLeftF v) 2) 2 z (binaryOp1PReadT z α v w)
def binaryOp1MemRowDecT (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (consForm v w) (consLeftF v) (consRightF w)) 0 z
    (memDecomposePub z (consForm v w) (consLeftF v) (consRightF w))
def binaryOp1MemRowVerifyT (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (consForm v w) (consLeftF v) 2) 2 z (binaryOp1PVerifyT z α v w)

/-- Parent axis-`3` cell-tail, tail axis-`2` cell-head, plus both inner `OP_1` forests. -/
def genBinaryOp1MemForest (z α : K) (op v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  .node (binaryOp1MemRowReadF z α op v w)
    [.node (binaryOp1MemRowDecF z α op v w)
      [.node (binaryOp1MemRowHaltH z α op v w) [],
       .node (binaryOp1MemRowVerifyF z α op v w) []]]
  :: .node (binaryOp1MemRowReadT z α v w)
    [.node (binaryOp1MemRowDecT z α v w)
      [.node (binaryOp1MemRowVerifyT z α v w) []]]
  :: (genOp1MemForest z α v ++ genOp1MemForest z α w)

def genOp5Op1MemForest (z α : K) (v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  genBinaryOp1MemForest z α 5 v w
def genOp7Op1MemForest (z α : K) (v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  genBinaryOp1MemForest z α 7 v w
def genOp8Op1MemForest (z α : K) (v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  genBinaryOp1MemForest z α 8 v w
def genOp2Op1MemForest (z α : K) (v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  genBinaryOp1MemForest z α 2 v w

theorem genBinaryOp1MemForest_ne_nil (z α : K) (op v w : ℕ) :
    genBinaryOp1MemForest z α op v w ≠ [] := by
  simp only [genBinaryOp1MemForest]
  exact List.cons_ne_nil _ _

theorem genOp5Op1MemForest_ne_nil (z α : K) (v w : ℕ) :
    genOp5Op1MemForest z α v w ≠ [] :=
  genBinaryOp1MemForest_ne_nil z α 5 v w
theorem genOp7Op1MemForest_ne_nil (z α : K) (v w : ℕ) :
    genOp7Op1MemForest z α v w ≠ [] :=
  genBinaryOp1MemForest_ne_nil z α 7 v w
theorem genOp8Op1MemForest_ne_nil (z α : K) (v w : ℕ) :
    genOp8Op1MemForest z α v w ≠ [] :=
  genBinaryOp1MemForest_ne_nil z α 8 v w
theorem genOp2Op1MemForest_ne_nil (z α : K) (v w : ℕ) :
    genOp2Op1MemForest z α v w ≠ [] :=
  genBinaryOp1MemForest_ne_nil z α 2 v w

theorem genBinaryOp1MemForest_memoryStampsWellFormed (z α : K) (op v w : ℕ) :
    ∀ root ∈ genBinaryOp1MemForest z α op v w, memoryStampsWellFormed root := by
  intro root hr
  simp only [genBinaryOp1MemForest] at hr
  rw [List.mem_cons] at hr
  obtain rfl | hr := hr
  · refine memoryStampsWellFormed_axis3CellTailShape _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [binaryOp1MemRowReadF, binaryOp1MemRowDecF, binaryOp1MemRowHaltH,
      binaryOp1MemRowVerifyF, servRow, memReadPub, memDecomposePub, memHeadPub,
      memVerifyPub, memReadSkel, memDecomposeSkel, memHaltSkel, memVerifySkel]
  · rw [List.mem_cons] at hr
    obtain rfl | hr := hr
    · refine memoryStampsWellFormed_axis2CellHeadShape _ _ _ ?_ ?_ ?_
      all_goals simp [binaryOp1MemRowReadT, binaryOp1MemRowDecT, binaryOp1MemRowVerifyT,
        servRow, binaryOp1PReadT, binaryOp1PVerifyT, servReadPub, servVerifyPub,
        memDecomposePub, memReadSkelAt, memDecomposeSkel, memVerifySkelAt]
    · rw [List.mem_append] at hr
      obtain hr | hr := hr
      · exact genOp1MemForest_memoryStampsWellFormed z α v root hr
      · exact genOp1MemForest_memoryStampsWellFormed z α w root hr

theorem genOp5Op1MemForest_memoryStampsWellFormed (z α : K) (v w : ℕ) :
    ∀ root ∈ genOp5Op1MemForest z α v w, memoryStampsWellFormed root :=
  genBinaryOp1MemForest_memoryStampsWellFormed z α 5 v w
theorem genOp7Op1MemForest_memoryStampsWellFormed (z α : K) (v w : ℕ) :
    ∀ root ∈ genOp7Op1MemForest z α v w, memoryStampsWellFormed root :=
  genBinaryOp1MemForest_memoryStampsWellFormed z α 7 v w
theorem genOp8Op1MemForest_memoryStampsWellFormed (z α : K) (v w : ℕ) :
    ∀ root ∈ genOp8Op1MemForest z α v w, memoryStampsWellFormed root :=
  genBinaryOp1MemForest_memoryStampsWellFormed z α 8 v w
theorem genOp2Op1MemForest_memoryStampsWellFormed (z α : K) (v w : ℕ) :
    ∀ root ∈ genOp2Op1MemForest z α v w, memoryStampsWellFormed root :=
  genBinaryOp1MemForest_memoryStampsWellFormed z α 2 v w

/-- BFS of the four-root two-record star (parent axis-`3` cell-tail, tail
    axis-`2` cell-head, plus both inner OP1 forests) is the named stamp list
    in that order.  Abstract in the rows so `genBinaryOp1MemForest` does not
    need `encC`. -/
theorem genMemoryStamps_binaryOp1Shape
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT
      ReadV DecV HaltHV VerifyV HaltTV
      ReadW DecW HaltHW VerifyW HaltTW : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT []]],
       .node ReadV
        [.node DecV
          [.node HaltHV [],
           .node VerifyV [.node HaltTV []]]],
       .node ReadW
        [.node DecW
          [.node HaltHW [],
           .node VerifyW [.node HaltTW []]]]] =
      [ReadF.stamp, ReadT.stamp, ReadV.stamp, ReadW.stamp,
        DecF.stamp, DecT.stamp, DecV.stamp, DecW.stamp,
        HaltH.stamp, VerifyF.stamp, VerifyT.stamp, HaltHV.stamp,
        VerifyV.stamp, HaltHW.stamp, VerifyW.stamp,
        HaltTV.stamp, HaltTW.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_cons_eq
      [NTree.node ReadF
        [NTree.node DecF
          [NTree.node HaltH [],
           NTree.node VerifyF []]],
       NTree.node ReadT
        [NTree.node DecT
          [NTree.node VerifyT []]],
       NTree.node ReadV
        [NTree.node DecV
          [NTree.node HaltHV [],
           NTree.node VerifyV [NTree.node HaltTV []]]],
       NTree.node ReadW
        [NTree.node DecW
          [NTree.node HaltHW [],
           NTree.node VerifyW [NTree.node HaltTW []]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecF
        [NTree.node HaltH [],
         NTree.node VerifyF []],
       NTree.node DecT
        [NTree.node VerifyT []],
       NTree.node DecV
        [NTree.node HaltHV [],
         NTree.node VerifyV [NTree.node HaltTV []]],
       NTree.node DecW
        [NTree.node HaltHW [],
         NTree.node VerifyW [NTree.node HaltTW []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltH [],
       NTree.node VerifyF [],
       NTree.node VerifyT [],
       NTree.node HaltHV [],
       NTree.node VerifyV [NTree.node HaltTV []],
       NTree.node HaltHW [],
       NTree.node VerifyW [NTree.node HaltTW []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltTV [],
       NTree.node HaltTW []]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.flatMap_nil,
    List.append_nil, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live two-record-star stamps (`read_root` / `verify_child`) carry exponent
    `1` or `2`.  Parent and both inner OP1 roots share `α¹`; the tail root
    is `α²`.  Padding (`decompose` / `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_binaryOp1Shape_live
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT
      ReadV DecV HaltHV VerifyV HaltTV
      ReadW DecW HaltHW VerifyW HaltTW : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hReadT : ReadT.stamp.state = .read_root ∧ ReadT.stamp.recordExponent = 2)
    (hReadV : ReadV.stamp.state = .read_root ∧ ReadV.stamp.recordExponent = 1)
    (hReadW : ReadW.stamp.state = .read_root ∧ ReadW.stamp.recordExponent = 1)
    (hDecF : DecF.stamp.state = .decompose)
    (hDecT : DecT.stamp.state = .decompose)
    (hDecV : DecV.stamp.state = .decompose)
    (hDecW : DecW.stamp.state = .decompose)
    (hHaltH : HaltH.stamp.state = .halt)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hVerifyT : VerifyT.stamp.state = .verify_child ∧
      VerifyT.stamp.recordExponent = 2)
    (hHaltHV : HaltHV.stamp.state = .halt)
    (hVerifyV : VerifyV.stamp.state = .verify_child ∧
      VerifyV.stamp.recordExponent = 1)
    (hHaltHW : HaltHW.stamp.state = .halt)
    (hVerifyW : VerifyW.stamp.state = .verify_child ∧
      VerifyW.stamp.recordExponent = 1)
    (hHaltTV : HaltTV.stamp.state = .halt)
    (hHaltTW : HaltTW.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT []]],
       .node ReadV
        [.node DecV
          [.node HaltHV [],
           .node VerifyV [.node HaltTV []]]],
       .node ReadW
        [.node DecW
          [.node HaltHW [],
           .node VerifyW [.node HaltTW []]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  rw [genMemoryStamps_binaryOp1Shape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl hReadF.2
  · subst h; exact Or.inr hReadT.2
  · subst h; exact Or.inl hReadV.2
  · subst h; exact Or.inl hReadW.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecT.symm.trans hr)
    | inr hv => cases (hDecT.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecV.symm.trans hr)
    | inr hv => cases (hDecV.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecW.symm.trans hr)
    | inr hv => cases (hDecW.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltH.symm.trans hr)
    | inr hv => cases (hHaltH.symm.trans hv)
  · subst h; exact Or.inl hVerifyF.2
  · subst h; exact Or.inr hVerifyT.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHV.symm.trans hr)
    | inr hv => cases (hHaltHV.symm.trans hv)
  · subst h; exact Or.inl hVerifyV.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHW.symm.trans hr)
    | inr hv => cases (hHaltHW.symm.trans hv)
  · subst h; exact Or.inl hVerifyW.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltTV.symm.trans hr)
    | inr hv => cases (hHaltTV.symm.trans hv)
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltTW.symm.trans hr)
      | inr hv => cases (hHaltTW.symm.trans hv)
    · cases hempty

/-- Live stamps of the served two-record-star forest carry exponent `1` or `2`. -/
theorem genMemoryStamps_genBinaryOp1MemForest_live
    (z α : K) (op v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genBinaryOp1MemForest z α op v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genBinaryOp1MemForest, genOp1MemForest, List.singleton_append] at hst
  exact genMemoryStamps_binaryOp1Shape_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    rfl rfl rfl rfl
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩
    rfl rfl hst hlive

theorem genMemoryStamps_genOp5Op1MemForest_live
    (z α : K) (v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp5Op1MemForest z α v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genOp5Op1MemForest] at hst
  exact genMemoryStamps_genBinaryOp1MemForest_live z α 5 v w hst hlive

theorem genMemoryStamps_genOp7Op1MemForest_live
    (z α : K) (v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp7Op1MemForest z α v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genOp7Op1MemForest] at hst
  exact genMemoryStamps_genBinaryOp1MemForest_live z α 7 v w hst hlive

theorem genMemoryStamps_genOp8Op1MemForest_live
    (z α : K) (v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp8Op1MemForest z α v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genOp8Op1MemForest] at hst
  exact genMemoryStamps_genBinaryOp1MemForest_live z α 8 v w hst hlive

theorem genMemoryStamps_genOp2Op1MemForest_live
    (z α : K) (v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp2Op1MemForest z α v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 := by
  simp only [genOp2Op1MemForest] at hst
  exact genMemoryStamps_genBinaryOp1MemForest_live z α 2 v w hst hlive

/-! ## Memory reconstruction of the three-record `OP_6` if/branch around two `OP_1` leaves

    Program `[6 [[1 k] [[1 v] [1 w]]]]` commits THREE live records at the parent:
    formula-open `⟨[6 [b [c d]]], [b [c d]], 3⟩` (four-row axis-`3` cell-tail),
    formula-tail `⟨[b [c d]], b, 2⟩` (three-row axis-`2` cell-head exposing the
    condition `b = [1 k]`), and branch-pair `⟨[c d], c, 2⟩` (three-row axis-`2`
    cell-head exposing `c = [1 v]` always, even on ELSE).  Plus the condition
    `OP_1` forest and the taken-branch `OP_1` forest (`k = 0` takes `v`, else
    `w`).  Five independent roots; timestamp-skeleton WF only, not nested NMR
    and not a `ForestExponentOrder` tick.  Do not import `Op5Gen` / `Op9Gen`. -/

/-- Condition formula `[1 k]`. -/
def op6CondF (k : ℕ) : Noun := .cell (.atom 1) (.atom k)
/-- Branch pair `[c d] = [[1 v] [1 w]]`. -/
def op6Pair (v w : ℕ) : Noun := consForm v w
/-- Formula tail `[b [c d]]`. -/
def op6Tail (k v w : ℕ) : Noun := .cell (op6CondF k) (op6Pair v w)
/-- The three-record if/branch formula `[6 [b [c d]]]`. -/
def op6Form (k v w : ℕ) : Noun := .cell (.atom 6) (op6Tail k v w)

def op6MemRowReadF (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (op6Form k v w) (op6Tail k v w)) 1 z
    (memReadPub z α (op6Form k v w) (op6Tail k v w))
def op6MemRowDecF (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (op6Form k v w) (.atom 6) (op6Tail k v w)) 0 z
    (memDecomposePub z (op6Form k v w) (.atom 6) (op6Tail k v w))
def op6MemRowHaltH (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel 6) 0 z (memHeadPub z (op6Form k v w) (.atom 6))
def op6MemRowVerifyF (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (op6Form k v w) (op6Tail k v w)) 1 z
    (memVerifyPub z α (op6Form k v w) (op6Tail k v w))

/-- Axis-`2` formula-tail record of `[b [c d]]` at timestamp `α²`. -/
def op6RecT (z α : K) (k v w : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 2) (op6Tail k v w) (op6CondF k) 2
def op6QT (z : K) (k v w : ℕ) : K := memPoleInv z (op6Tail k v w)

def op6PReadT (z α : K) (k v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (op6Tail k v w), 0, 0⟩ ⟨encC z (op6Tail k v w), 4, 4⟩
    (op6RecT z α k v w) 0 (op6QT z k v w)
def op6PVerifyT (z α : K) (k v w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (op6CondF k), 4, 12⟩ ⟨encC z (op6CondF k), 0, 0⟩
    (op6RecT z α k v w) (op6QT z k v w) 0

def op6MemRowReadT (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (op6Tail k v w) (op6CondF k) 2) 2 z (op6PReadT z α k v w)
def op6MemRowDecT (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (op6Tail k v w) (op6CondF k) (op6Pair v w)) 0 z
    (memDecomposePub z (op6Tail k v w) (op6CondF k) (op6Pair v w))
def op6MemRowVerifyT (z α : K) (k v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (op6Tail k v w) (op6CondF k) 2) 2 z (op6PVerifyT z α k v w)

/-- Axis-`2` branch-pair record of `[c d]` at timestamp `α³`, always exposing `c`. -/
def op6RecP (z α : K) (v w : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 3) (op6Pair v w) (consLeftF v) 2
def op6QP (z : K) (v w : ℕ) : K := memPoleInv z (op6Pair v w)

def op6PReadP (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (op6Pair v w), 0, 0⟩ ⟨encC z (op6Pair v w), 4, 4⟩
    (op6RecP z α v w) 0 (op6QP z v w)
def op6PVerifyP (z α : K) (v w : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (consLeftF v), 4, 12⟩ ⟨encC z (consLeftF v), 0, 0⟩
    (op6RecP z α v w) (op6QP z v w) 0

def op6MemRowReadP (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (op6Pair v w) (consLeftF v) 2) 3 z (op6PReadP z α v w)
def op6MemRowDecP (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (op6Pair v w) (consLeftF v) (consRightF w)) 0 z
    (memDecomposePub z (op6Pair v w) (consLeftF v) (consRightF w))
def op6MemRowVerifyP (z α : K) (v w : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (op6Pair v w) (consLeftF v) 2) 3 z (op6PVerifyP z α v w)

/-- Taken-branch inner forest: THEN (`k = 0`) serves `[1 v]`, ELSE serves `[1 w]`. -/
def genOp6TakenMemForest (z α : K) (k v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  if k = 0 then genOp1MemForest z α v else genOp1MemForest z α w

/-- Parent axis-`3` cell-tail, tail axis-`2` cell-head, pair axis-`2` cell-head,
    condition `OP_1` forest, and taken-branch `OP_1` forest. -/
def genOp6Op1MemForest (z α : K) (k v w : ℕ) : List (NTree (GenMemoryRow K)) :=
  .node (op6MemRowReadF z α k v w)
    [.node (op6MemRowDecF z α k v w)
      [.node (op6MemRowHaltH z α k v w) [],
       .node (op6MemRowVerifyF z α k v w) []]]
  :: .node (op6MemRowReadT z α k v w)
    [.node (op6MemRowDecT z α k v w)
      [.node (op6MemRowVerifyT z α k v w) []]]
  :: .node (op6MemRowReadP z α v w)
    [.node (op6MemRowDecP z α v w)
      [.node (op6MemRowVerifyP z α v w) []]]
  :: (genOp1MemForest z α k ++ genOp6TakenMemForest z α k v w)

theorem genOp6Op1MemForest_ne_nil (z α : K) (k v w : ℕ) :
    genOp6Op1MemForest z α k v w ≠ [] := by
  simp only [genOp6Op1MemForest]
  exact List.cons_ne_nil _ _

theorem genOp6TakenMemForest_memoryStampsWellFormed (z α : K) (k v w : ℕ) :
    ∀ root ∈ genOp6TakenMemForest z α k v w, memoryStampsWellFormed root := by
  intro root hr
  unfold genOp6TakenMemForest at hr
  split_ifs at hr with hk
  · exact genOp1MemForest_memoryStampsWellFormed z α v root hr
  · exact genOp1MemForest_memoryStampsWellFormed z α w root hr

theorem genOp6Op1MemForest_memoryStampsWellFormed (z α : K) (k v w : ℕ) :
    ∀ root ∈ genOp6Op1MemForest z α k v w, memoryStampsWellFormed root := by
  intro root hr
  simp only [genOp6Op1MemForest] at hr
  rw [List.mem_cons] at hr
  obtain rfl | hr := hr
  · refine memoryStampsWellFormed_axis3CellTailShape _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [op6MemRowReadF, op6MemRowDecF, op6MemRowHaltH,
      op6MemRowVerifyF, servRow, memReadPub, memDecomposePub, memHeadPub,
      memVerifyPub, memReadSkel, memDecomposeSkel, memHaltSkel, memVerifySkel]
  · rw [List.mem_cons] at hr
    obtain rfl | hr := hr
    · refine memoryStampsWellFormed_axis2CellHeadShape _ _ _ ?_ ?_ ?_
      all_goals simp [op6MemRowReadT, op6MemRowDecT, op6MemRowVerifyT,
        servRow, op6PReadT, op6PVerifyT, servReadPub, servVerifyPub,
        memDecomposePub, memReadSkelAt, memDecomposeSkel, memVerifySkelAt]
    · rw [List.mem_cons] at hr
      obtain rfl | hr := hr
      · refine memoryStampsWellFormed_axis2CellHeadShape _ _ _ ?_ ?_ ?_
        all_goals simp [op6MemRowReadP, op6MemRowDecP, op6MemRowVerifyP,
          servRow, op6PReadP, op6PVerifyP, servReadPub, servVerifyPub,
          memDecomposePub, memReadSkelAt, memDecomposeSkel, memVerifySkelAt]
      · rw [List.mem_append] at hr
        obtain hr | hr := hr
        · exact genOp1MemForest_memoryStampsWellFormed z α k root hr
        · exact genOp6TakenMemForest_memoryStampsWellFormed z α k v w root hr

/-- BFS of the five-root three-record if/branch (parent axis-`3` cell-tail,
    tail axis-`2` cell-head, pair axis-`2` cell-head, plus condition and
    taken-branch OP1 forests) is the named stamp list in that order.
    Abstract in the rows so `genOp6Op1MemForest` does not need `encC`. -/
theorem genMemoryStamps_op6Op1Shape
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT
      ReadP DecP VerifyP
      ReadK DecK HaltHK VerifyK HaltTK
      ReadTaken DecTaken HaltHTaken VerifyTaken HaltTTaken : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT []]],
       .node ReadP
        [.node DecP
          [.node VerifyP []]],
       .node ReadK
        [.node DecK
          [.node HaltHK [],
           .node VerifyK [.node HaltTK []]]],
       .node ReadTaken
        [.node DecTaken
          [.node HaltHTaken [],
           .node VerifyTaken [.node HaltTTaken []]]]] =
      [ReadF.stamp, ReadT.stamp, ReadP.stamp, ReadK.stamp, ReadTaken.stamp,
        DecF.stamp, DecT.stamp, DecP.stamp, DecK.stamp, DecTaken.stamp,
        HaltH.stamp, VerifyF.stamp, VerifyT.stamp, VerifyP.stamp,
        HaltHK.stamp, VerifyK.stamp, HaltHTaken.stamp, VerifyTaken.stamp,
        HaltTK.stamp, HaltTTaken.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_cons_eq
      [NTree.node ReadF
        [NTree.node DecF
          [NTree.node HaltH [],
           NTree.node VerifyF []]],
       NTree.node ReadT
        [NTree.node DecT
          [NTree.node VerifyT []]],
       NTree.node ReadP
        [NTree.node DecP
          [NTree.node VerifyP []]],
       NTree.node ReadK
        [NTree.node DecK
          [NTree.node HaltHK [],
           NTree.node VerifyK [NTree.node HaltTK []]]],
       NTree.node ReadTaken
        [NTree.node DecTaken
          [NTree.node HaltHTaken [],
           NTree.node VerifyTaken [NTree.node HaltTTaken []]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecF
        [NTree.node HaltH [],
         NTree.node VerifyF []],
       NTree.node DecT
        [NTree.node VerifyT []],
       NTree.node DecP
        [NTree.node VerifyP []],
       NTree.node DecK
        [NTree.node HaltHK [],
         NTree.node VerifyK [NTree.node HaltTK []]],
       NTree.node DecTaken
        [NTree.node HaltHTaken [],
         NTree.node VerifyTaken [NTree.node HaltTTaken []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltH [],
       NTree.node VerifyF [],
       NTree.node VerifyT [],
       NTree.node VerifyP [],
       NTree.node HaltHK [],
       NTree.node VerifyK [NTree.node HaltTK []],
       NTree.node HaltHTaken [],
       NTree.node VerifyTaken [NTree.node HaltTTaken []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltTK [],
       NTree.node HaltTTaken []]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.flatMap_nil,
    List.append_nil, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live three-record if/branch stamps (`read_root` / `verify_child`) carry
    exponent `1`, `2`, or `3`.  Parent and both inner OP1 roots share `α¹`;
    the tail root is `α²`; the pair root is `α³`.  Padding (`decompose` /
    `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_op6Op1Shape_live
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT
      ReadP DecP VerifyP
      ReadK DecK HaltHK VerifyK HaltTK
      ReadTaken DecTaken HaltHTaken VerifyTaken HaltTTaken : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hReadT : ReadT.stamp.state = .read_root ∧ ReadT.stamp.recordExponent = 2)
    (hReadP : ReadP.stamp.state = .read_root ∧ ReadP.stamp.recordExponent = 3)
    (hReadK : ReadK.stamp.state = .read_root ∧ ReadK.stamp.recordExponent = 1)
    (hReadTaken : ReadTaken.stamp.state = .read_root ∧
      ReadTaken.stamp.recordExponent = 1)
    (hDecF : DecF.stamp.state = .decompose)
    (hDecT : DecT.stamp.state = .decompose)
    (hDecP : DecP.stamp.state = .decompose)
    (hDecK : DecK.stamp.state = .decompose)
    (hDecTaken : DecTaken.stamp.state = .decompose)
    (hHaltH : HaltH.stamp.state = .halt)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hVerifyT : VerifyT.stamp.state = .verify_child ∧
      VerifyT.stamp.recordExponent = 2)
    (hVerifyP : VerifyP.stamp.state = .verify_child ∧
      VerifyP.stamp.recordExponent = 3)
    (hHaltHK : HaltHK.stamp.state = .halt)
    (hVerifyK : VerifyK.stamp.state = .verify_child ∧
      VerifyK.stamp.recordExponent = 1)
    (hHaltHTaken : HaltHTaken.stamp.state = .halt)
    (hVerifyTaken : VerifyTaken.stamp.state = .verify_child ∧
      VerifyTaken.stamp.recordExponent = 1)
    (hHaltTK : HaltTK.stamp.state = .halt)
    (hHaltTTaken : HaltTTaken.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT []]],
       .node ReadP
        [.node DecP
          [.node VerifyP []]],
       .node ReadK
        [.node DecK
          [.node HaltHK [],
           .node VerifyK [.node HaltTK []]]],
       .node ReadTaken
        [.node DecTaken
          [.node HaltHTaken [],
           .node VerifyTaken [.node HaltTTaken []]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  rw [genMemoryStamps_op6Op1Shape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl hReadF.2
  · subst h; exact Or.inr (Or.inl hReadT.2)
  · subst h; exact Or.inr (Or.inr hReadP.2)
  · subst h; exact Or.inl hReadK.2
  · subst h; exact Or.inl hReadTaken.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecT.symm.trans hr)
    | inr hv => cases (hDecT.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecP.symm.trans hr)
    | inr hv => cases (hDecP.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecK.symm.trans hr)
    | inr hv => cases (hDecK.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecTaken.symm.trans hr)
    | inr hv => cases (hDecTaken.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltH.symm.trans hr)
    | inr hv => cases (hHaltH.symm.trans hv)
  · subst h; exact Or.inl hVerifyF.2
  · subst h; exact Or.inr (Or.inl hVerifyT.2)
  · subst h; exact Or.inr (Or.inr hVerifyP.2)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHK.symm.trans hr)
    | inr hv => cases (hHaltHK.symm.trans hv)
  · subst h; exact Or.inl hVerifyK.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHTaken.symm.trans hr)
    | inr hv => cases (hHaltHTaken.symm.trans hv)
  · subst h; exact Or.inl hVerifyTaken.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltTK.symm.trans hr)
    | inr hv => cases (hHaltTK.symm.trans hv)
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltTTaken.symm.trans hr)
      | inr hv => cases (hHaltTTaken.symm.trans hv)
    · cases hempty

/-- Live stamps of the served three-record if/branch forest carry exponent
    `1`, `2`, or `3`. -/
theorem genMemoryStamps_genOp6Op1MemForest_live
    (z α : K) (k v w : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp6Op1MemForest z α k v w))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  simp only [genOp6Op1MemForest, genOp6TakenMemForest] at hst
  split_ifs at hst
  · simp only [genOp1MemForest, List.singleton_append] at hst
    exact genMemoryStamps_op6Op1Shape_live
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl rfl rfl rfl rfl
      rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩
      rfl rfl hst hlive
  · simp only [genOp1MemForest, List.singleton_append] at hst
    exact genMemoryStamps_op6Op1Shape_live
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl rfl rfl rfl rfl
      rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩
      rfl rfl hst hlive


/-! ## Memory reconstruction of the three-record `OP_9` invoke around two `OP_1` leaves

    Program `[9 [1 [1 [1 v]]]]` commits THREE live records at the parent:
    formula-open `⟨[9 [b c]], [b c], 3⟩` (four-row axis-`3` cell-tail),
    formula-tail `⟨[b c], b, 2⟩` (four-row axis-`2` atom-head exposing the axis
    atom `b = 1`), and served arm-fetch `⟨core, arm, 1⟩` (two-row axis-`1` cell
    identity; the root is the computed core, not a formula subtree).  Compute
    children are core `*[s [1 [1 v]]] = [1 v]` (four-row unary OP1 parent) and
    invoke `*[[1 v] [1 v]]` (five-row OP1 leaf).  Do not name this
    `genOp9MemForest`.  Not a `ForestExponentOrder` tick. -/

/-- Fetched arm / computed core `[1 v]`. -/
def op9ArmF (v : ℕ) : Noun := unaryOp1Tail v
/-- Core formula `c = [1 [1 v]]`. -/
def op9CoreF (v : ℕ) : Noun := unaryOp1Form 1 v
/-- Formula tail `[b c] = [1 [1 [1 v]]]`. -/
def op9Tail (v : ℕ) : Noun := .cell (.atom 1) (op9CoreF v)
/-- The three-record invoke formula `[9 [1 [1 [1 v]]]]`. -/
def op9Form (v : ℕ) : Noun := .cell (.atom 9) (op9Tail v)

def op9MemRowReadF (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memReadSkel (op9Form v) (op9Tail v)) 1 z
    (memReadPub z α (op9Form v) (op9Tail v))
def op9MemRowDecF (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (op9Form v) (.atom 9) (op9Tail v)) 0 z
    (memDecomposePub z (op9Form v) (.atom 9) (op9Tail v))
def op9MemRowHaltH (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel 9) 0 z (memHeadPub z (op9Form v) (.atom 9))
def op9MemRowVerifyF (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkel (op9Form v) (op9Tail v)) 1 z
    (memVerifyPub z α (op9Form v) (op9Tail v))

/-- Axis-`2` formula-tail record of `[b c]` at timestamp `α²`, exposing atom `b = 1`. -/
def op9RecT (z α : K) (v : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 2) (op9Tail v) (.atom 1) 2
def op9QT (z : K) (v : ℕ) : K := memPoleInv z (op9Tail v)

def op9PReadT (z α : K) (v : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (op9Tail v), 0, 0⟩ ⟨encC z (op9Tail v), 4, 4⟩
    (op9RecT z α v) 0 (op9QT z v)
def op9PVerifyT (z α : K) (v : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (.atom 1), 0, 0⟩ ⟨encC z (.atom 1), 0, 0⟩
    (op9RecT z α v) (op9QT z v) 0
def op9PHaltT (z : K) : MemoryTable.Pub K :=
  servHaltPub z 1 0

def op9MemRowReadT (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (op9Tail v) (.atom 1) 2) 2 z (op9PReadT z α v)
def op9MemRowDecT (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memDecomposeSkel (op9Tail v) (.atom 1) (op9CoreF v)) 0 z
    (memDecomposePub z (op9Tail v) (.atom 1) (op9CoreF v))
def op9MemRowVerifyT (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (op9Tail v) (.atom 1) 2) 2 z (op9PVerifyT z α v)
def op9MemRowHaltT (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memHaltSkel 1) 0 z (op9PHaltT z)

/-- Axis-`1` arm-fetch record of `[1 v]` at timestamp `α³` (identity slot of a cell). -/
def op9RecA (z α : K) (v : ℕ) : ComputeTable.MemRec K :=
  memReqRecAt z (α ^ 3) (op9ArmF v) (op9ArmF v) 1
def op9QA (z : K) (v : ℕ) : K := memPoleInv z (op9ArmF v)

def op9PReadA (z α : K) (v : ℕ) : MemoryTable.Pub K :=
  servReadPub ⟨encC z (op9ArmF v), 0, 0⟩ ⟨encC z (op9ArmF v), 4, 4⟩
    (op9RecA z α v) 0 (op9QA z v)
def op9PVerifyA (z α : K) (v : ℕ) : MemoryTable.Pub K :=
  servVerifyPub ⟨encC z (op9ArmF v), 4, 12⟩ ⟨encC z (op9ArmF v), 0, 0⟩
    (op9RecA z α v) (op9QA z v) 0

def op9MemRowReadA (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memReadSkelAt (op9ArmF v) (op9ArmF v) 1) 3 z (op9PReadA z α v)
def op9MemRowVerifyA (z α : K) (v : ℕ) : GenMemoryRow K :=
  servRow (memVerifySkelAt (op9ArmF v) (op9ArmF v) 1) 3 z (op9PVerifyA z α v)

/-- Parent axis-`3` cell-tail, tail axis-`2` atom-head, arm axis-`1` cell,
    plus core unary-OP1 and invoke OP1 forests (`genUnaryOp1MemForest` at opcode 1). -/
def genOp9Op1MemForest (z α : K) (v : ℕ) : List (NTree (GenMemoryRow K)) :=
  .node (op9MemRowReadF z α v)
    [.node (op9MemRowDecF z α v)
      [.node (op9MemRowHaltH z α v) [],
       .node (op9MemRowVerifyF z α v) []]]
  :: .node (op9MemRowReadT z α v)
    [.node (op9MemRowDecT z α v)
      [.node (op9MemRowVerifyT z α v)
        [.node (op9MemRowHaltT z α v) []]]]
  :: .node (op9MemRowReadA z α v)
    [.node (op9MemRowVerifyA z α v) []]
  :: genUnaryOp1MemForest z α 1 v

theorem genOp9Op1MemForest_ne_nil (z α : K) (v : ℕ) :
    genOp9Op1MemForest z α v ≠ [] := by
  simp only [genOp9Op1MemForest]
  exact List.cons_ne_nil _ _

theorem genOp9Op1MemForest_memoryStampsWellFormed (z α : K) (v : ℕ) :
    ∀ root ∈ genOp9Op1MemForest z α v, memoryStampsWellFormed root := by
  intro root hr
  simp only [genOp9Op1MemForest] at hr
  rw [List.mem_cons] at hr
  obtain rfl | hr := hr
  · refine memoryStampsWellFormed_axis3CellTailShape _ _ _ _ ?_ ?_ ?_ ?_
    all_goals simp [op9MemRowReadF, op9MemRowDecF, op9MemRowHaltH,
      op9MemRowVerifyF, servRow, memReadPub, memDecomposePub, memHeadPub,
      memVerifyPub, memReadSkel, memDecomposeSkel, memHaltSkel, memVerifySkel]
  · rw [List.mem_cons] at hr
    obtain rfl | hr := hr
    · refine memoryStampsWellFormed_axis2AtomHeadShape _ _ _ _ ?_ ?_ ?_ ?_
      all_goals simp [op9MemRowReadT, op9MemRowDecT, op9MemRowVerifyT,
        op9MemRowHaltT, servRow, op9PReadT, op9PVerifyT, op9PHaltT,
        servReadPub, servVerifyPub, servHaltPub, memDecomposePub,
        memReadSkelAt, memDecomposeSkel, memVerifySkelAt, memHaltSkel]
    · rw [List.mem_cons] at hr
      obtain rfl | hr := hr
      · refine memoryStampsWellFormed_axis1CellShape _ _ ?_ ?_
        all_goals simp [op9MemRowReadA, op9MemRowVerifyA, servRow,
          op9PReadA, op9PVerifyA, servReadPub, servVerifyPub,
          memReadSkelAt, memVerifySkelAt]
      · exact genUnaryOp1MemForest_memoryStampsWellFormed z α 1 v root hr

/-- BFS of the five-root three-record invoke (parent axis-`3` cell-tail,
    tail axis-`2` atom-head, arm axis-`1` cell, plus unary-OP1 parent and
    invoke OP1 forests) is the named stamp list in that order.
    Abstract in the rows so `genOp9Op1MemForest` does not need `encC`.
    The arm root is two-row, so `VerifyA` sits at BFS level 1 among the
    `Dec*` stamps. -/
theorem genMemoryStamps_op9Op1Shape
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT HaltT
      ReadA VerifyA
      ReadC DecC HaltHC VerifyC
      ReadI DecI HaltHI VerifyI HaltTI : GenMemoryRow K) :
    genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT
            [.node HaltT []]]],
       .node ReadA
        [.node VerifyA []],
       .node ReadC
        [.node DecC
          [.node HaltHC [],
           .node VerifyC []]],
       .node ReadI
        [.node DecI
          [.node HaltHI [],
           .node VerifyI [.node HaltTI []]]]] =
      [ReadF.stamp, ReadT.stamp, ReadA.stamp, ReadC.stamp, ReadI.stamp,
        DecF.stamp, DecT.stamp, VerifyA.stamp, DecC.stamp, DecI.stamp,
        HaltH.stamp, VerifyF.stamp, VerifyT.stamp, HaltHC.stamp,
        VerifyC.stamp, HaltHI.stamp, VerifyI.stamp,
        HaltT.stamp, HaltTI.stamp] := by
  unfold genMemoryStamps
  rw [bfsForest_cons_eq
      [NTree.node ReadF
        [NTree.node DecF
          [NTree.node HaltH [],
           NTree.node VerifyF []]],
       NTree.node ReadT
        [NTree.node DecT
          [NTree.node VerifyT
            [NTree.node HaltT []]]],
       NTree.node ReadA
        [NTree.node VerifyA []],
       NTree.node ReadC
        [NTree.node DecC
          [NTree.node HaltHC [],
           NTree.node VerifyC []]],
       NTree.node ReadI
        [NTree.node DecI
          [NTree.node HaltHI [],
           NTree.node VerifyI [NTree.node HaltTI []]]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node DecF
        [NTree.node HaltH [],
         NTree.node VerifyF []],
       NTree.node DecT
        [NTree.node VerifyT
          [NTree.node HaltT []]],
       NTree.node VerifyA [],
       NTree.node DecC
        [NTree.node HaltHC [],
         NTree.node VerifyC []],
       NTree.node DecI
        [NTree.node HaltHI [],
         NTree.node VerifyI [NTree.node HaltTI []]]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltH [],
       NTree.node VerifyF [],
       NTree.node VerifyT
        [NTree.node HaltT []],
       NTree.node HaltHC [],
       NTree.node VerifyC [],
       NTree.node HaltHI [],
       NTree.node VerifyI [NTree.node HaltTI []]]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.nil_append,
    List.flatMap_nil, List.append_nil, List.cons_append]
  rw [bfsForest_cons_eq
      [NTree.node HaltT [],
       NTree.node HaltTI []]
      (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, NTree.children_node, List.flatMap_nil,
    List.append_nil, bfsForest_nil]
  simp [List.map_cons, List.map_nil, NTree.label_node]

/-- Live three-record invoke stamps (`read_root` / `verify_child`) carry
    exponent `1`, `2`, or `3`.  Parent, unary-OP1, and invoke OP1 roots
    share `α¹`; the tail root is `α²`; the arm-fetch root is `α³`.
    Padding (`decompose` / `halt`) is excluded by `hlive`. -/
theorem genMemoryStamps_op9Op1Shape_live
    (ReadF DecF HaltH VerifyF ReadT DecT VerifyT HaltT
      ReadA VerifyA
      ReadC DecC HaltHC VerifyC
      ReadI DecI HaltHI VerifyI HaltTI : GenMemoryRow K)
    (hReadF : ReadF.stamp.state = .read_root ∧ ReadF.stamp.recordExponent = 1)
    (hReadT : ReadT.stamp.state = .read_root ∧ ReadT.stamp.recordExponent = 2)
    (hReadA : ReadA.stamp.state = .read_root ∧ ReadA.stamp.recordExponent = 3)
    (hReadC : ReadC.stamp.state = .read_root ∧ ReadC.stamp.recordExponent = 1)
    (hReadI : ReadI.stamp.state = .read_root ∧ ReadI.stamp.recordExponent = 1)
    (hDecF : DecF.stamp.state = .decompose)
    (hDecT : DecT.stamp.state = .decompose)
    (hVerifyA : VerifyA.stamp.state = .verify_child ∧
      VerifyA.stamp.recordExponent = 3)
    (hDecC : DecC.stamp.state = .decompose)
    (hDecI : DecI.stamp.state = .decompose)
    (hHaltH : HaltH.stamp.state = .halt)
    (hVerifyF : VerifyF.stamp.state = .verify_child ∧
      VerifyF.stamp.recordExponent = 1)
    (hVerifyT : VerifyT.stamp.state = .verify_child ∧
      VerifyT.stamp.recordExponent = 2)
    (hHaltHC : HaltHC.stamp.state = .halt)
    (hVerifyC : VerifyC.stamp.state = .verify_child ∧
      VerifyC.stamp.recordExponent = 1)
    (hHaltHI : HaltHI.stamp.state = .halt)
    (hVerifyI : VerifyI.stamp.state = .verify_child ∧
      VerifyI.stamp.recordExponent = 1)
    (hHaltT : HaltT.stamp.state = .halt)
    (hHaltTI : HaltTI.stamp.state = .halt)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps
      [.node ReadF
        [.node DecF
          [.node HaltH [],
           .node VerifyF []]],
       .node ReadT
        [.node DecT
          [.node VerifyT
            [.node HaltT []]]],
       .node ReadA
        [.node VerifyA []],
       .node ReadC
        [.node DecC
          [.node HaltHC [],
           .node VerifyC []]],
       .node ReadI
        [.node DecI
          [.node HaltHI [],
           .node VerifyI [.node HaltTI []]]]])
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  rw [genMemoryStamps_op9Op1Shape] at hst
  simp only [List.mem_cons] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl hReadF.2
  · subst h; exact Or.inr (Or.inl hReadT.2)
  · subst h; exact Or.inr (Or.inr hReadA.2)
  · subst h; exact Or.inl hReadC.2
  · subst h; exact Or.inl hReadI.2
  · subst h
    cases hlive with
    | inl hr => cases (hDecF.symm.trans hr)
    | inr hv => cases (hDecF.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecT.symm.trans hr)
    | inr hv => cases (hDecT.symm.trans hv)
  · subst h; exact Or.inr (Or.inr hVerifyA.2)
  · subst h
    cases hlive with
    | inl hr => cases (hDecC.symm.trans hr)
    | inr hv => cases (hDecC.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hDecI.symm.trans hr)
    | inr hv => cases (hDecI.symm.trans hv)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltH.symm.trans hr)
    | inr hv => cases (hHaltH.symm.trans hv)
  · subst h; exact Or.inl hVerifyF.2
  · subst h; exact Or.inr (Or.inl hVerifyT.2)
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHC.symm.trans hr)
    | inr hv => cases (hHaltHC.symm.trans hv)
  · subst h; exact Or.inl hVerifyC.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltHI.symm.trans hr)
    | inr hv => cases (hHaltHI.symm.trans hv)
  · subst h; exact Or.inl hVerifyI.2
  · subst h
    cases hlive with
    | inl hr => cases (hHaltT.symm.trans hr)
    | inr hv => cases (hHaltT.symm.trans hv)
  · rcases h with h | hempty
    · subst h
      cases hlive with
      | inl hr => cases (hHaltTI.symm.trans hr)
      | inr hv => cases (hHaltTI.symm.trans hv)
    · cases hempty

/-- Live stamps of the served three-record invoke forest carry exponent
    `1`, `2`, or `3`. -/
theorem genMemoryStamps_genOp9Op1MemForest_live
    (z α : K) (v : ℕ)
    {stamp : MemoryTimestampRow}
    (hst : stamp ∈ genMemoryStamps (genOp9Op1MemForest z α v))
    (hlive : stamp.state = .read_root ∨ stamp.state = .verify_child) :
    stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 := by
  simp only [genOp9Op1MemForest, genUnaryOp1MemForest, genOp1MemForest] at hst
  exact genMemoryStamps_op9Op1Shape_live
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    rfl rfl ⟨rfl, rfl⟩ rfl rfl
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩
    rfl rfl hst hlive

/-- The served memory forest of a ROM formula.  The `OP_1` leaf `[1 v]` is reconstructed by
    `genOp1MemForest`; the branching autocons `[[1 v] [1 w]]` by `genConsMemForest`; the
    `OP_0` identity leaf `[0 1]` on an atom subject by `genOp0LeafMemForest`; the unary
    wrappers `[4 [1 v]]` / `[3 [1 v]]` by `genOp4Op1MemForest` / `genOp3Op1MemForest`;
    the two-record stars `[5 [1 v] [1 w]]` / `[7 [1 v] [1 w]]` / `[8 [1 v] [1 w]]` /
    `[2 [1 v] [1 w]]` by `genOp5Op1MemForest` and aliases; the three-record if/branch
    `[6 [[1 k] [[1 v] [1 w]]]]` by `genOp6Op1MemForest`; the three-record invoke
    `[9 [1 [1 [1 v]]]]` by `genOp9Op1MemForest`.  Default subject `.atom 0`
    keeps three-argument call sites compiling.  Every other formula has no generated
    served forest yet. -/
def genMemForest (z α : K) (formula : Noun) (subject : Noun := .atom 0) :
    List (NTree (GenMemoryRow K)) :=
  match formula, subject with
  | .cell (.atom 1) (.atom v), _ => genOp1MemForest z α v
  | .cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w)), _ =>
    genConsMemForest z α v w
  | .cell (.atom 0) (.atom 1), .atom s => genOp0LeafMemForest z α s
  | .cell (.atom 4) (.cell (.atom 1) (.atom v)), _ => genOp4Op1MemForest z α v
  | .cell (.atom 3) (.cell (.atom 1) (.atom v)), _ => genOp3Op1MemForest z α v
  | .cell (.atom 5) (.cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w))), _ =>
    genOp5Op1MemForest z α v w
  | .cell (.atom 7) (.cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w))), _ =>
    genOp7Op1MemForest z α v w
  | .cell (.atom 8) (.cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w))), _ =>
    genOp8Op1MemForest z α v w
  | .cell (.atom 2) (.cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w))), _ =>
    genOp2Op1MemForest z α v w
  | .cell (.atom 6) (.cell (.cell (.atom 1) (.atom k))
      (.cell (.cell (.atom 1) (.atom v)) (.cell (.atom 1) (.atom w)))), _ =>
    genOp6Op1MemForest z α k v w
  | .cell (.atom 9) (.cell (.atom 1) (.cell (.atom 1) (.cell (.atom 1) (.atom v)))), _ =>
    genOp9Op1MemForest z α v
  | _, _ => []

/-- Path-tree inhabitant of `SemanticTimestampSkeleton` over the OP1
    served forest.  `F`/`Algebra` are binders for later α-specialization.
    Nonempty `memoryRows` via `genMemoryStamps_ne_nil`.  Not a
    `ForestExponentOrder` tick. -/
noncomputable def genOp1TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp1MemForest (0 : K) (0 : K) v)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genOp1MemForest (0 : K) (0 : K) v)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genOp1MemForest (0 : K) (0 : K) v))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genOp1MemForest (0 : K) (0 : K) v))
      (genMemoryStamps (genOp1MemForest (0 : K) (0 : K) v))
  computeTopology :=
    computeTopology_genSemantic_of_isPathTree t h
      (genOp1MemForest (0 : K) (0 : K) v)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genOp1MemForest (0 : K) (0 : K) v)
      (genOp1MemForest_memoryStampsWellFormed (0 : K) (0 : K) v)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genOp1TimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp1TimestampSkeleton_of_isPathTree F t h v).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp1TimestampSkeleton_of_isPathTree_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp1TimestampSkeleton_of_isPathTree F t h v).memoryRows =
      genMemoryStamps (genOp1MemForest (0 : K) (0 : K) v) :=
  rfl

theorem genOp1TimestampSkeleton_of_isPathTree_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp1TimestampSkeleton_of_isPathTree F t h v).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp1MemForest_ne_nil (0 : K) (0 : K) v)

/-- Live OP1 memory stamps match the first compute-record exponent (`1`).
    Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genOp1TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    LiveMemLineIdentification (genOp1TimestampSkeleton_of_isPathTree F t h v) := by
  intro stamp hst hlive
  rw [genOp1TimestampSkeleton_of_isPathTree_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 :=
    genMemoryStamps_genOp1MemForest_live (0 : K) (0 : K) v hst hlive
  obtain ⟨c, hc, hrest⟩ :=
    dfsStamps_assignExponents_exists_recordExponent_one t
  obtain ⟨i, hi, hci⟩ := hrest
  refine ⟨c, ?_, i, hi, ?_⟩
  · rw [genOp1TimestampSkeleton_of_isPathTree_computeRows]
    exact hc
  · rw [hexp, hci]

/-- Height-1 star inhabitant of `SemanticTimestampSkeleton` over the cons
    served forest.  Cons-over-two-OP1 is this construction.  Not a
    `ForestExponentOrder` tick. -/
noncomputable def genConsTimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genConsMemForest (0 : K) (0 : K) v w)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genConsMemForest (0 : K) (0 : K) v w)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genConsMemForest (0 : K) (0 : K) v w))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genConsMemForest (0 : K) (0 : K) v w))
      (genMemoryStamps (genConsMemForest (0 : K) (0 : K) v w))
  computeTopology :=
    computeTopology_genSemantic_of_childrenAreLeaves t h
      (genConsMemForest (0 : K) (0 : K) v w)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genConsMemForest (0 : K) (0 : K) v w)
      (genConsMemForest_memoryStampsWellFormed (0 : K) (0 : K) v w)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genConsTimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genConsTimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genConsTimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genConsTimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows =
      genMemoryStamps (genConsMemForest (0 : K) (0 : K) v w) :=
  rfl

theorem genConsTimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genConsTimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genConsMemForest_ne_nil (0 : K) (0 : K) v w)

/-- Live cons memory stamps match compute-record exponents `{1,2,3}`.
    Needs `subtreeRecordCount ≥ 3` because the two OP1 children supply
    exponents `2` and `3`.  Padding is excluded.  Not a `ForestExponentOrder`
    tick -/
theorem liveMemLineIdentification_genConsTimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ)
    (hrec : 3 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genConsTimestampSkeleton_of_childrenAreLeaves F t h v w) := by
  intro stamp hst hlive
  rw [genConsTimestampSkeleton_of_childrenAreLeaves_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 :=
    genMemoryStamps_genConsMemForest_live (0 : K) (0 : K) v w hst hlive
  have go (n : ℕ) (hn : stamp.recordExponent = n) (h1 : 1 ≤ n)
      (hbound : n ≤ subtreeRecordCount t) :
      ∃ c ∈ (genConsTimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows,
        ∃ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i := by
    obtain ⟨c, hc, i, hi, hci⟩ :=
      dfsStamps_assignExponents_exists_recordExponent t n h1 hbound
    refine ⟨c, ?_, i, hi, ?_⟩
    · rw [genConsTimestampSkeleton_of_childrenAreLeaves_computeRows]
      exact hc
    · rw [hn, hci]
  rcases hexp with hn | hn | hn
  · exact go 1 hn (by omega) (by omega)
  · exact go 2 hn (by omega) (by omega)
  · exact go 3 hn (by omega) hrec

/-- Nonvacuity specialization at `F := K` via `Algebra.id`.  Not the only
    inhabitant — the generic-`F` constructions above are the load-bearing
    ones -/
noncomputable def genOp1TimestampSkeleton_of_isPathTree_id
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp1MemForest (0 : K) (0 : K) v)) :=
  letI : Algebra K K := Algebra.id K
  genOp1TimestampSkeleton_of_isPathTree (F := K) t h v

noncomputable def genConsTimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genConsMemForest (0 : K) (0 : K) v w)) :=
  letI : Algebra K K := Algebra.id K
  genConsTimestampSkeleton_of_childrenAreLeaves (F := K) t h v w

/-- Path-tree inhabitant of `SemanticTimestampSkeleton` over the `OP_0`
    identity-axis leaf forest (`*[.atom s [0 1]]`).  Two independent
    served roots.  Not a `ForestExponentOrder` tick. -/
noncomputable def genOp0TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp0LeafMemForest (0 : K) (0 : K) s)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genOp0LeafMemForest (0 : K) (0 : K) s)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genOp0LeafMemForest (0 : K) (0 : K) s))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genOp0LeafMemForest (0 : K) (0 : K) s))
      (genMemoryStamps (genOp0LeafMemForest (0 : K) (0 : K) s))
  computeTopology :=
    computeTopology_genSemantic_of_isPathTree t h
      (genOp0LeafMemForest (0 : K) (0 : K) s)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genOp0LeafMemForest (0 : K) (0 : K) s)
      (genOp0LeafMemForest_memoryStampsWellFormed (0 : K) (0 : K) s)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genOp0TimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ) :
    (genOp0TimestampSkeleton_of_isPathTree F t h s).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp0TimestampSkeleton_of_isPathTree_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ) :
    (genOp0TimestampSkeleton_of_isPathTree F t h s).memoryRows =
      genMemoryStamps (genOp0LeafMemForest (0 : K) (0 : K) s) :=
  rfl

theorem genOp0TimestampSkeleton_of_isPathTree_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ) :
    (genOp0TimestampSkeleton_of_isPathTree F t h s).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp0LeafMemForest_ne_nil (0 : K) (0 : K) s)

/-- Live OP0 identity-axis stamps match compute-record exponents `{1,2}`.
    Needs `subtreeRecordCount ≥ 2` because `.s0` emits two records.
    Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genOp0TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp0TimestampSkeleton_of_isPathTree F t h s) := by
  intro stamp hst hlive
  rw [genOp0TimestampSkeleton_of_isPathTree_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 :=
    genMemoryStamps_genOp0LeafMemForest_live (0 : K) (0 : K) s hst hlive
  have go (n : ℕ) (hn : stamp.recordExponent = n) (h1 : 1 ≤ n)
      (hbound : n ≤ subtreeRecordCount t) :
      ∃ c ∈ (genOp0TimestampSkeleton_of_isPathTree F t h s).computeRows,
        ∃ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i := by
    obtain ⟨c, hc, i, hi, hci⟩ :=
      dfsStamps_assignExponents_exists_recordExponent t n h1 hbound
    refine ⟨c, ?_, i, hi, ?_⟩
    · rw [genOp0TimestampSkeleton_of_isPathTree_computeRows]
      exact hc
    · rw [hn, hci]
  rcases hexp with hn | hn
  · exact go 1 hn (by omega) (by omega)
  · exact go 2 hn (by omega) hrec

noncomputable def genOp0TimestampSkeleton_of_isPathTree_id
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (s : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp0LeafMemForest (0 : K) (0 : K) s)) :=
  letI : Algebra K K := Algebra.id K
  genOp0TimestampSkeleton_of_isPathTree (F := K) t h s

/-- Path-tree inhabitant of `SemanticTimestampSkeleton` over a unary
    wrapper around `OP_1` (`*[s [op [1 v]]]`).  Parent four-row axis-`3`
    cell-tail plus inner five-row OP1 forest.  Not a `ForestExponentOrder`
    tick -/
noncomputable def genUnaryOp1TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (op v : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genUnaryOp1MemForest (0 : K) (0 : K) op v)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genUnaryOp1MemForest (0 : K) (0 : K) op v)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genUnaryOp1MemForest (0 : K) (0 : K) op v))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genUnaryOp1MemForest (0 : K) (0 : K) op v))
      (genMemoryStamps (genUnaryOp1MemForest (0 : K) (0 : K) op v))
  computeTopology :=
    computeTopology_genSemantic_of_isPathTree t h
      (genUnaryOp1MemForest (0 : K) (0 : K) op v)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genUnaryOp1MemForest (0 : K) (0 : K) op v)
      (genUnaryOp1MemForest_memoryStampsWellFormed (0 : K) (0 : K) op v)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genUnaryOp1TimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (op v : ℕ) :
    (genUnaryOp1TimestampSkeleton_of_isPathTree F t h op v).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genUnaryOp1TimestampSkeleton_of_isPathTree_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (op v : ℕ) :
    (genUnaryOp1TimestampSkeleton_of_isPathTree F t h op v).memoryRows =
      genMemoryStamps (genUnaryOp1MemForest (0 : K) (0 : K) op v) :=
  rfl

theorem genUnaryOp1TimestampSkeleton_of_isPathTree_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (op v : ℕ) :
    (genUnaryOp1TimestampSkeleton_of_isPathTree F t h op v).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genUnaryOp1MemForest_ne_nil (0 : K) (0 : K) op v)

/-- Live unary-wrapper memory stamps match the first compute-record exponent
    (`1`).  Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genUnaryOp1TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (op v : ℕ) :
    LiveMemLineIdentification
      (genUnaryOp1TimestampSkeleton_of_isPathTree F t h op v) := by
  intro stamp hst hlive
  rw [genUnaryOp1TimestampSkeleton_of_isPathTree_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 :=
    genMemoryStamps_genUnaryOp1MemForest_live (0 : K) (0 : K) op v hst hlive
  obtain ⟨c, hc, hrest⟩ :=
    dfsStamps_assignExponents_exists_recordExponent_one t
  obtain ⟨i, hi, hci⟩ := hrest
  refine ⟨c, ?_, i, hi, ?_⟩
  · rw [genUnaryOp1TimestampSkeleton_of_isPathTree_computeRows]
    exact hc
  · rw [hexp, hci]

noncomputable def genOp4TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp4Op1MemForest (0 : K) (0 : K) v)) :=
  genUnaryOp1TimestampSkeleton_of_isPathTree F t h 4 v

noncomputable def genOp3TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp3Op1MemForest (0 : K) (0 : K) v)) :=
  genUnaryOp1TimestampSkeleton_of_isPathTree F t h 3 v

theorem genOp4TimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp4TimestampSkeleton_of_isPathTree F t h v).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp4TimestampSkeleton_of_isPathTree_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp4TimestampSkeleton_of_isPathTree F t h v).memoryRows =
      genMemoryStamps (genOp4Op1MemForest (0 : K) (0 : K) v) :=
  rfl

theorem genOp4TimestampSkeleton_of_isPathTree_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp4TimestampSkeleton_of_isPathTree F t h v).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp4Op1MemForest_ne_nil (0 : K) (0 : K) v)

theorem genOp3TimestampSkeleton_of_isPathTree_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp3TimestampSkeleton_of_isPathTree F t h v).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp3TimestampSkeleton_of_isPathTree_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp3TimestampSkeleton_of_isPathTree F t h v).memoryRows =
      genMemoryStamps (genOp3Op1MemForest (0 : K) (0 : K) v) :=
  rfl

theorem genOp3TimestampSkeleton_of_isPathTree_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    (genOp3TimestampSkeleton_of_isPathTree F t h v).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp3Op1MemForest_ne_nil (0 : K) (0 : K) v)

/-- Live OP4 memory stamps match the first compute-record exponent (`1`).
    Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genOp4TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    LiveMemLineIdentification (genOp4TimestampSkeleton_of_isPathTree F t h v) :=
  liveMemLineIdentification_genUnaryOp1TimestampSkeleton_of_isPathTree F t h 4 v

/-- Live OP3 memory stamps match the first compute-record exponent (`1`).
    Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genOp3TimestampSkeleton_of_isPathTree
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    LiveMemLineIdentification (genOp3TimestampSkeleton_of_isPathTree F t h v) :=
  liveMemLineIdentification_genUnaryOp1TimestampSkeleton_of_isPathTree F t h 3 v

noncomputable def genOp4TimestampSkeleton_of_isPathTree_id
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp4Op1MemForest (0 : K) (0 : K) v)) :=
  letI : Algebra K K := Algebra.id K
  genOp4TimestampSkeleton_of_isPathTree (F := K) t h v

noncomputable def genOp3TimestampSkeleton_of_isPathTree_id
    (t : NTree (GenComputeRow K)) (h : isPathTree t) (v : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp3Op1MemForest (0 : K) (0 : K) v)) :=
  letI : Algebra K K := Algebra.id K
  genOp3TimestampSkeleton_of_isPathTree (F := K) t h v

/-- Height-1 star inhabitant of `SemanticTimestampSkeleton` over a two-record
    star around two `OP_1` leaves (`*[s [op [1 v] [1 w]]]`).  Parent four-row
    axis-`3` cell-tail, three-row axis-`2` cell-head, plus both inner five-row
    OP1 forests.  Not a `ForestExponentOrder` tick -/
noncomputable def genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (op v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genBinaryOp1MemForest (0 : K) (0 : K) op v w)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genBinaryOp1MemForest (0 : K) (0 : K) op v w)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genBinaryOp1MemForest (0 : K) (0 : K) op v w))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genBinaryOp1MemForest (0 : K) (0 : K) op v w))
      (genMemoryStamps (genBinaryOp1MemForest (0 : K) (0 : K) op v w))
  computeTopology :=
    computeTopology_genSemantic_of_childrenAreLeaves t h
      (genBinaryOp1MemForest (0 : K) (0 : K) op v w)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genBinaryOp1MemForest (0 : K) (0 : K) op v w)
      (genBinaryOp1MemForest_memoryStampsWellFormed (0 : K) (0 : K) op v w)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

noncomputable def genOp5TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp5Op1MemForest (0 : K) (0 : K) v w)) :=
  genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h 5 v w

noncomputable def genOp7TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp7Op1MemForest (0 : K) (0 : K) v w)) :=
  genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h 7 v w

noncomputable def genOp8TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp8Op1MemForest (0 : K) (0 : K) v w)) :=
  genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h 8 v w

noncomputable def genOp2TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp2Op1MemForest (0 : K) (0 : K) v w)) :=
  genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h 2 v w

theorem genBinaryOp1TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (op v w : ℕ) :
    (genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h op v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genBinaryOp1TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (op v w : ℕ) :
    (genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h op v w).memoryRows =
      genMemoryStamps (genBinaryOp1MemForest (0 : K) (0 : K) op v w) :=
  rfl

theorem genOp5TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp5TimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp5TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp5TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows =
      genMemoryStamps (genOp5Op1MemForest (0 : K) (0 : K) v w) :=
  rfl

theorem genOp5TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp5TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp5Op1MemForest_ne_nil (0 : K) (0 : K) v w)

theorem genOp7TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp7TimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp7TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp7TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows =
      genMemoryStamps (genOp7Op1MemForest (0 : K) (0 : K) v w) :=
  rfl

theorem genOp7TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp7TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp7Op1MemForest_ne_nil (0 : K) (0 : K) v w)

theorem genOp8TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp8TimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp8TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp8TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows =
      genMemoryStamps (genOp8Op1MemForest (0 : K) (0 : K) v w) :=
  rfl

theorem genOp8TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp8TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp8Op1MemForest_ne_nil (0 : K) (0 : K) v w)

theorem genOp2TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp2TimestampSkeleton_of_childrenAreLeaves F t h v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp2TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp2TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows =
      genMemoryStamps (genOp2Op1MemForest (0 : K) (0 : K) v w) :=
  rfl

theorem genOp2TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    (genOp2TimestampSkeleton_of_childrenAreLeaves F t h v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp2Op1MemForest_ne_nil (0 : K) (0 : K) v w)

/-- Live two-record-star memory stamps match compute-record exponents `{1,2}`.
    Needs `subtreeRecordCount ≥ 2` because the tail root supplies exponent `2`.
    Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (op v w : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genBinaryOp1TimestampSkeleton_of_childrenAreLeaves F t h op v w) := by
  intro stamp hst hlive
  rw [genBinaryOp1TimestampSkeleton_of_childrenAreLeaves_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 :=
    genMemoryStamps_genBinaryOp1MemForest_live (0 : K) (0 : K) op v w hst hlive
  have go (n : ℕ) (hn : stamp.recordExponent = n) (h1 : 1 ≤ n)
      (hbound : n ≤ subtreeRecordCount t) :
      ∃ c ∈ (genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
          F t h op v w).computeRows,
        ∃ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i := by
    obtain ⟨c, hc, i, hi, hci⟩ :=
      dfsStamps_assignExponents_exists_recordExponent t n h1 hbound
    refine ⟨c, ?_, i, hi, ?_⟩
    · rw [genBinaryOp1TimestampSkeleton_of_childrenAreLeaves_computeRows]
      exact hc
    · rw [hn, hci]
  rcases hexp with hn | hn
  · exact go 1 hn (by omega) (by omega)
  · exact go 2 hn (by omega) hrec

theorem liveMemLineIdentification_genOp5TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp5TimestampSkeleton_of_childrenAreLeaves F t h v w) :=
  liveMemLineIdentification_genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    F t h 5 v w hrec

theorem liveMemLineIdentification_genOp7TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp7TimestampSkeleton_of_childrenAreLeaves F t h v w) :=
  liveMemLineIdentification_genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    F t h 7 v w hrec

theorem liveMemLineIdentification_genOp8TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp8TimestampSkeleton_of_childrenAreLeaves F t h v w) :=
  liveMemLineIdentification_genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    F t h 8 v w hrec

theorem liveMemLineIdentification_genOp2TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ)
    (hrec : 2 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp2TimestampSkeleton_of_childrenAreLeaves F t h v w) :=
  liveMemLineIdentification_genBinaryOp1TimestampSkeleton_of_childrenAreLeaves
    F t h 2 v w hrec

noncomputable def genOp5TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp5Op1MemForest (0 : K) (0 : K) v w)) :=
  letI : Algebra K K := Algebra.id K
  genOp5TimestampSkeleton_of_childrenAreLeaves (F := K) t h v w

noncomputable def genOp7TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp7Op1MemForest (0 : K) (0 : K) v w)) :=
  letI : Algebra K K := Algebra.id K
  genOp7TimestampSkeleton_of_childrenAreLeaves (F := K) t h v w

noncomputable def genOp8TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp8Op1MemForest (0 : K) (0 : K) v w)) :=
  letI : Algebra K K := Algebra.id K
  genOp8TimestampSkeleton_of_childrenAreLeaves (F := K) t h v w

noncomputable def genOp2TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp2Op1MemForest (0 : K) (0 : K) v w)) :=
  letI : Algebra K K := Algebra.id K
  genOp2TimestampSkeleton_of_childrenAreLeaves (F := K) t h v w

/-- Height-1 star inhabitant of `SemanticTimestampSkeleton` over the three-record
    `OP_6` if/branch around two `OP_1` leaves (`*[s [6 [[1 k] [[1 v] [1 w]]]]]`).
    Parent four-row axis-`3` cell-tail, two three-row axis-`2` cell-heads (tail
    exposing `b`, pair exposing `c`), plus condition and taken-branch OP1 forests.
    Parameterized by `k` (THEN at `0`, ELSE otherwise).  Not a
    `ForestExponentOrder` tick -/
noncomputable def genOp6TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp6Op1MemForest (0 : K) (0 : K) k v w)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genOp6Op1MemForest (0 : K) (0 : K) k v w)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genOp6Op1MemForest (0 : K) (0 : K) k v w))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genOp6Op1MemForest (0 : K) (0 : K) k v w))
      (genMemoryStamps (genOp6Op1MemForest (0 : K) (0 : K) k v w))
  computeTopology :=
    computeTopology_genSemantic_of_childrenAreLeaves t h
      (genOp6Op1MemForest (0 : K) (0 : K) k v w)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genOp6Op1MemForest (0 : K) (0 : K) k v w)
      (genOp6Op1MemForest_memoryStampsWellFormed (0 : K) (0 : K) k v w)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genOp6TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ) :
    (genOp6TimestampSkeleton_of_childrenAreLeaves F t h k v w).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp6TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ) :
    (genOp6TimestampSkeleton_of_childrenAreLeaves F t h k v w).memoryRows =
      genMemoryStamps (genOp6Op1MemForest (0 : K) (0 : K) k v w) :=
  rfl

theorem genOp6TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ) :
    (genOp6TimestampSkeleton_of_childrenAreLeaves F t h k v w).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp6Op1MemForest_ne_nil (0 : K) (0 : K) k v w)

/-- Live three-record if/branch memory stamps match compute-record exponents
    `{1,2,3}`.  Needs `subtreeRecordCount ≥ 3` because the pair root supplies
    exponent `3`.  Padding is excluded.  Not a `ForestExponentOrder` tick. -/
theorem liveMemLineIdentification_genOp6TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ)
    (hrec : 3 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp6TimestampSkeleton_of_childrenAreLeaves F t h k v w) := by
  intro stamp hst hlive
  rw [genOp6TimestampSkeleton_of_childrenAreLeaves_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 :=
    genMemoryStamps_genOp6Op1MemForest_live (0 : K) (0 : K) k v w hst hlive
  have go (n : ℕ) (hn : stamp.recordExponent = n) (h1 : 1 ≤ n)
      (hbound : n ≤ subtreeRecordCount t) :
      ∃ c ∈ (genOp6TimestampSkeleton_of_childrenAreLeaves F t h k v w).computeRows,
        ∃ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i := by
    obtain ⟨c, hc, i, hi, hci⟩ :=
      dfsStamps_assignExponents_exists_recordExponent t n h1 hbound
    refine ⟨c, ?_, i, hi, ?_⟩
    · rw [genOp6TimestampSkeleton_of_childrenAreLeaves_computeRows]
      exact hc
    · rw [hn, hci]
  rcases hexp with hn | hn | hn
  · exact go 1 hn (by omega) (by omega)
  · exact go 2 hn (by omega) (by omega)
  · exact go 3 hn (by omega) hrec


noncomputable def genOp6TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (k v w : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp6Op1MemForest (0 : K) (0 : K) k v w)) :=
  letI : Algebra K K := Algebra.id K
  genOp6TimestampSkeleton_of_childrenAreLeaves (F := K) t h k v w

/-- Height-1 star inhabitant of `SemanticTimestampSkeleton` over the three-record
    `OP_9` invoke around two `OP_1` leaves (`*[s [9 [1 [1 [1 v]]]]]`).
    Parent four-row axis-`3` cell-tail, tail four-row axis-`2` atom-head
    exposing `b = 1`, arm two-row axis-`1` cell identity, plus core unary-OP1
    and invoke OP1 forests.  Not a `ForestExponentOrder` tick. -/
noncomputable def genOp9TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ) :
    SemanticTimestampSkeleton F K
      (genSemanticSkeleton (assignExponents t)
        (genOp9Op1MemForest (0 : K) (0 : K) v)) where
  computeRows := dfsStamps (assignExponents t)
  memoryRows := genMemoryStamps (genOp9Op1MemForest (0 : K) (0 : K) v)
  semanticRequests :=
    genSemanticRequests
      (genSemanticSkeleton (assignExponents t)
        (genOp9Op1MemForest (0 : K) (0 : K) v))
      (dfsStamps (assignExponents t))
  semanticResponses :=
    genSemanticResponses
      (genSemanticSkeleton (assignExponents t)
        (genOp9Op1MemForest (0 : K) (0 : K) v))
      (genMemoryStamps (genOp9Op1MemForest (0 : K) (0 : K) v))
  computeTopology :=
    computeTopology_genSemantic_of_childrenAreLeaves t h
      (genOp9Op1MemForest (0 : K) (0 : K) v)
  memoryTopology :=
    memoryTopology_genSemantic (assignExponents t)
      (genOp9Op1MemForest (0 : K) (0 : K) v)
      (genOp9Op1MemForest_memoryStampsWellFormed (0 : K) (0 : K) v)
  computeStartsAtZero := dfsStamps_assignExponents_startsAtZero t
  computeLineChain := dfsStamps_assignExponents_chain t
  computeLineAdvance := fun _ hst =>
    dfsStamps_assignExponents_computeLineAdvance t hst
  computeRecordOffsets := fun _ hst i hi =>
    dfsStamps_assignExponents_computeRecordOffsets t hst i hi
  requestTopology := rfl
  responseTopology := (genSemanticResponses_eq _ _).symm

theorem genOp9TimestampSkeleton_of_childrenAreLeaves_computeRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ) :
    (genOp9TimestampSkeleton_of_childrenAreLeaves F t h v).computeRows =
      dfsStamps (assignExponents t) :=
  rfl

theorem genOp9TimestampSkeleton_of_childrenAreLeaves_memoryRows
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ) :
    (genOp9TimestampSkeleton_of_childrenAreLeaves F t h v).memoryRows =
      genMemoryStamps (genOp9Op1MemForest (0 : K) (0 : K) v) :=
  rfl

theorem genOp9TimestampSkeleton_of_childrenAreLeaves_memoryRows_ne_nil
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ) :
    (genOp9TimestampSkeleton_of_childrenAreLeaves F t h v).memoryRows ≠ [] :=
  genMemoryStamps_ne_nil _ (genOp9Op1MemForest_ne_nil (0 : K) (0 : K) v)

/-- Live three-record invoke memory stamps match compute-record exponents
    `{1,2,3}`.  Needs `subtreeRecordCount ≥ 3` because the arm-fetch root
    supplies exponent `3`.  Padding is excluded.  Not a `ForestExponentOrder`
    tick. -/
theorem liveMemLineIdentification_genOp9TimestampSkeleton_of_childrenAreLeaves
    (F : Type) [Field F] [Algebra F K]
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ)
    (hrec : 3 ≤ subtreeRecordCount t) :
    LiveMemLineIdentification
      (genOp9TimestampSkeleton_of_childrenAreLeaves F t h v) := by
  intro stamp hst hlive
  rw [genOp9TimestampSkeleton_of_childrenAreLeaves_memoryRows] at hst
  have hexp : stamp.recordExponent = 1 ∨ stamp.recordExponent = 2 ∨
      stamp.recordExponent = 3 :=
    genMemoryStamps_genOp9Op1MemForest_live (0 : K) (0 : K) v hst hlive
  have go (n : ℕ) (hn : stamp.recordExponent = n) (h1 : 1 ≤ n)
      (hbound : n ≤ subtreeRecordCount t) :
      ∃ c ∈ (genOp9TimestampSkeleton_of_childrenAreLeaves F t h v).computeRows,
        ∃ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i := by
    obtain ⟨c, hc, i, hi, hci⟩ :=
      dfsStamps_assignExponents_exists_recordExponent t n h1 hbound
    refine ⟨c, ?_, i, hi, ?_⟩
    · rw [genOp9TimestampSkeleton_of_childrenAreLeaves_computeRows]
      exact hc
    · rw [hn, hci]
  rcases hexp with hn | hn | hn
  · exact go 1 hn (by omega) (by omega)
  · exact go 2 hn (by omega) (by omega)
  · exact go 3 hn (by omega) hrec

noncomputable def genOp9TimestampSkeleton_of_childrenAreLeaves_id
    (t : NTree (GenComputeRow K)) (h : childrenAreLeaves t) (v : ℕ) :
    SemanticTimestampSkeleton K K
      (genSemanticSkeleton (assignExponents t)
        (genOp9Op1MemForest (0 : K) (0 : K) v)) :=
  letI : Algebra K K := Algebra.id K
  genOp9TimestampSkeleton_of_childrenAreLeaves (F := K) t h v

/-! ## The whole worker -/

/-- **`genTraceDFS`.**  DFS three-pass worker: compute stamps via `assignExponents`.
    Path/star timestamp-skeleton inhabitants still go through this assignment.
    Production traces use `genTrace` in `BFSAssign.lean` (`bfsAssign`). -/
def genTraceDFS (q Λ : ℕ) (z α : K) (fuel : ℕ) (subject formula : Noun) :
    Except GenError (GenTrace K K) :=
  match genComputeSkeleton fuel subject formula with
  | .error e => .error e
  | .ok (ct, result) =>
    .ok
      { subject := subject, formula := formula, result := result, fuel := fuel
        computeNodes := renderRows z α (assignExponents ct)
        memoryNodes := genMemForest z α formula subject }

end Nock.NockVMROM.Thm54.TraceGen
