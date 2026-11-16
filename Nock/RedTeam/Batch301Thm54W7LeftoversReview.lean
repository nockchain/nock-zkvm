/-
  Nock/RedTeam/Batch301Thm54W7LeftoversReview.lean

  Paper re-read at source: the paper 
  `:1846-1868` (`mem_record₁` "always verifies the opening of a formula",
  `:1850-1852`), `:1450`.

  Receipts, one section per brief item:

  * A — binder walk reproduced (`Batch301BinderWalk`) **and** the converse
    derivations `b301_p64_from_p65` / `b301_p65_from_p66` / `b301_p66_from_p67`:
    each successor theorem re-derives its predecessor under the predecessor's
    own binders, so no surviving hypothesis was strengthened.  The
    `p66 ↔ p67` binder types are compared by `isDefEq` position by position
    and the five that differ are exactly the five transported ones.
  * B — `hmempos` at the two smallest programs (`[1 42]` on `0`, `[0 1]` on `42`),
    through `romTree_spec` and the generic lemma, with no side hypothesis.
  * C — seed `0` is a dummy: `programMemRows 0 α t = programMemRows z α t` for
    every `z`, the chosen seed is `≠ 0`, `p67`'s *statement* mentions no
    `romSeedVcomp*` / `choose` constant (positive control: `p66`'s does), and the
    `_irrel` lemmas carry no `Prop` binder.
  * D — the proof-term closure of `b300_nockCompiles_p67_literal` (restricted to
    `Nock.*`, which is complete for `Nock.*` targets) is walked for the
    Goldilocks seed-value constants; positive control `b296_nockCompiles_literal`.
  * G — every new generic lemma carries a `K : Type` binder (positive control:
    `Batch298.b298_hmempos_mm` does not — it is Goldilocks-scoped).

  No production file under `Nock/NockVMROM/` is edited.  Top-level `redteam-status.json` `status`
  is not flipped.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenGenericMempos
import Nock.NockVMROM.Thm54.TraceGen.GenGenericSeedIrrel
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenRomComplete
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.RedTeam.Batch296Thm54P5NockCompiles
import Nock.RedTeam.Batch298Thm54GenericHmempos
import Nock.RedTeam.Batch300Thm54P5NockCompilesP67
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Lean Elab Command Meta

/-! ## A. Instrument: binder walk, name diff, position-wise type comparison -/

namespace Batch301BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo × Expr)) := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => do
      let id := x.fvarId!
      pure (← id.getUserName, ← id.getBinderInfo, ← id.getType)

def binderCounts (n : Name) : MetaM (Nat × Nat) := do
  let tel ← binderTelescope n
  let expl := tel.foldl (fun acc (_, bi, _) => if bi == .default then acc + 1 else acc) 0
  return (tel.size, expl)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi, _) => if bi == .default then some nm else none

/-- Names of `Prop`-typed non-instance binders (hypotheses proper).  Instance-implicit
`Prop` classes (`[CharP K (ringChar K)]`, `[FiniteDimensional F K]`) are reported separately:
they are auto-included by the `variable` block and always inhabited, never a hypothesis. -/
def propBinderNames (n : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  forallTelescope info.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let bi ← x.fvarId!.getBinderInfo
      if bi != .instImplicit then
        if ← isProp (← inferType x) then
          out := out.push (← x.fvarId!.getUserName)
    return out

/-- Instance-implicit binders whose class is `Prop`-valued (vacuous carriers, F-7). -/
def propInstCount (n : Name) : MetaM Nat := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  forallTelescope info.type fun xs _ => do
    let mut k := 0
    for x in xs do
      if (← x.fvarId!.getBinderInfo) == .instImplicit then
        if ← isProp (← inferType x) then k := k + 1
    return k

/-- Position-wise comparison of two telescopes of equal length: instantiate the second with the
first's fvars and report the positions whose binder types are not `isDefEq`. -/
def typeDiff (a b : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some ia := env.find? a | throwError m!"missing {a}"
  let some ib := env.find? b | throwError m!"missing {b}"
  forallTelescope ia.type fun xs _ => do
    let mut tb := ib.type
    let mut out := #[]
    for x in xs do
      let .forallE _ dom body _ := tb | throwError m!"{b} has fewer binders than {a}"
      let ta ← inferType x
      unless ← isDefEq ta dom do
        out := out.push (← x.fvarId!.getUserName)
      tb := body.instantiate1 x
    return out

/-- Constants occurring in a declaration's *type* (statement), not its proof. -/
def typeConsts (n : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  return info.type.getUsedConstants

run_cmd do
  let check (n : Name) (total expl : Nat) : CommandElabM Unit := do
    let (t, e) ← liftTermElabM (binderCounts n)
    if t ≠ total || e ≠ expl then
      throwError m!"binder count {n}: got {t}/{e}, expected {total}/{expl}"
    logInfo m!"B301-COUNT {n} total={t} explicit={e}"
  let n64 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
  let n65 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65
  let n66 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p66
  let n67 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
  let n300 : Name := ``Nock.RedTeam.Batch300.b300_nockCompiles_p67_literal
  let ng62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p62
  let na62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree_p62
  check n64 52 34
  check n65 51 33
  check n66 49 31
  check n67 49 31
  check n300 5 5
  check ng62 57 39  -- 2a: +hrows; repair (ii): +hmemOrd; S2: +αW
  -- Name diffs, and what each removed binder was replaced by (see the theorems below).
  let e64 ← liftTermElabM (explicitNames n64)
  let e65 ← liftTermElabM (explicitNames n65)
  let e66 ← liftTermElabM (explicitNames n66)
  let e67 ← liftTermElabM (explicitNames n67)
  let d6465 := e64.filter (fun nm => !e65.contains nm)
  let d6566 := e65.filter (fun nm => !e66.contains nm)
  let d6667 := e66.filter (fun nm => !e67.contains nm)
  let a6465 := e65.filter (fun nm => !e64.contains nm)
  let a6566 := e66.filter (fun nm => !e65.contains nm)
  let a6667 := e67.filter (fun nm => !e66.contains nm)
  unless d6465 == #[`hmempos] do throwError m!"p64→p65 dropped {d6465}, expected [hmempos]"
  unless d6566 == #[`hconf, `hwinNouns] do
    throwError m!"p65→p66 dropped {d6566}, expected [hconf, hwinNouns] (hΛ retyped)"
  unless d6667 == #[] do throwError m!"p66→p67 dropped {d6667}, expected none"
  unless a6465 == #[] ∧ a6566 == #[] ∧ a6667 == #[] do
    throwError m!"a binder was ADDED: {a6465} {a6566} {a6667}"
  logInfo m!"B301-NAMES p64\\p65={d6465} p65\\p66={d6566} p66\\p67={d6667}; nothing added"
  -- The changed p62: hmempos gone from the atTree form (three fixture receipts were re-pointed).
  let ea62 ← liftTermElabM (explicitNames na62)
  if ea62.contains `hmempos then throwError m!"atTree_p62 still binds hmempos"
  logInfo m!"B301-P62 nockCompiles_of_grom_atTree_p62 explicit={ea62.size} (hmempos derived)"
  -- p66 vs p67: same length; which binder TYPES differ (isDefEq)?
  let diff ← liftTermElabM (typeDiff n66 n67)
  unless diff == #[`hcomp, `hmem, `hKszChar, `hmemCap, `hcard, `hax] do
    throwError m!"p66/p67 type diff {diff}, expected the five transported binders + hax"
  logInfo m!"B301-TYPEDIFF p66/p67 binders whose type changed = {diff}"
  -- p67's STATEMENT mentions no chosen seed and no choice; p66's does (positive control).
  let c67 ← liftTermElabM (typeConsts n67)
  let c66 ← liftTermElabM (typeConsts n66)
  let c64 ← liftTermElabM (typeConsts n64)
  -- Form R leftover `hfirst`/`hmore` binder types mention the seed term via
  -- `genExactExecution`/`genBuildableOfProgram`; the *count* hypotheses of p67
  -- remain seed-`0` (`programMemShape`, `compilerKszOf 0`, …).  Ban only choice.
  let banned : Array Name := #[``Classical.choose, ``Exists.choose]
  for b in banned do
    if c67.contains b then throwError m!"p67 statement mentions {b}"
  unless c66.contains ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeedVcompOfWindow do
    throwError "positive control failed: p66 statement should mention romSeedVcompOfWindow"
  unless c64.contains ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeedVcomp do
    throwError "positive control failed: p64 statement should mention romSeedVcomp"
  logInfo m!"B301-STMT p67 choice-free; p66/p64 seed controls fired (Form R leftover binders may mention romSeedVcomp)"
  -- The suppliers of the removed binders take nothing beyond TraceConfined (and the
  -- generator equation, for hwinNouns).
  let pOne ← liftTermElabM (propBinderNames ``Nock.NockVMROM.Thm54.TraceGen.one_le_of_hΛ_conf)
  unless pOne == #[`h] do throwError m!"one_le_of_hΛ_conf Prop binders {pOne}"
  let pWin ← liftTermElabM
    (propBinderNames ``Nock.NockVMROM.Thm54.TraceGen.sizeWindowNounsBoundedBy_of_traceConfined)
  unless pWin == #[`hΛ, `h, `hconf] do
    throwError m!"sizeWindowNounsBoundedBy_of_traceConfined Prop binders {pWin}"
  logInfo m!"B301-SUPPLIERS one_le_of_hΛ_conf={pOne}; sizeWindowNounsBoundedBy_of_traceConfined={pWin} (hΛ : 1 ≤ Λ is an extra, derivable binder — F-3)"
  let pMempos ← liftTermElabM
    (propBinderNames ``Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_hmempos)
  unless pMempos == #[`h] do throwError m!"genComputeSkeleton_hmempos Prop binders {pMempos}"
  -- The irrel lemmas carry no hypothesis at all.
  for nm in [``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_length_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_totalSize_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_length_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_totalSize_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.programMemRows_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.compilerKszOf_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.compilerNOf_irrel] do
    let ps ← liftTermElabM (propBinderNames nm)
    unless ps == #[] do throwError m!"{nm} carries Prop binders {ps}"
    let k ← liftTermElabM (propInstCount nm)
    logInfo m!"B301-IRREL {nm}: hypotheses=0, vacuous Prop-instance binders={k}"
  logInfo m!"B301-IRREL all eight _irrel lemmas carry zero hypotheses"
  -- F-7: instance binders demanded by the count abbrevs themselves.
  for nm in [``Nock.NockVMROM.Thm54.TraceGen.programMemRows,
      ``Nock.NockVMROM.Thm54.TraceGen.compilerKszOf,
      ``Nock.NockVMROM.Thm54.TraceGen.compilerNOf,
      ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest,
      ``Nock.NockVMROM.Thm54.TraceGen.programMemRows_irrel,
      ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_irrel] do
    let tel ← liftTermElabM (binderTelescope nm)
    let insts := tel.filterMap fun (_, bi, ty) => if bi == .instImplicit then some ty else none
    logInfo m!"B301-INST {nm} instance binders = {insts}"

/-! ### G. Scope: `K` must be a bound `Type` variable in every new generic lemma -/

def hasTypeVarK (n : Name) : MetaM Bool := do
  let tel ← binderTelescope n
  for (nm, _, ty) in tel do
    if nm == `K then
      return ← isDefEq ty (mkSort Level.one)
  return false

run_cmd do
  let generic : Array Name := #[
    ``Nock.NockVMROM.Thm54.TraceGen.extractNodeReqs_ne_nil,
    ``Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_ne_nil,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_ne_nil,
    ``Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_hmempos,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_pos,
    ``Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_length_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_totalSize_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_totalSize_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromList_totalSize_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_length_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemForestFromList_length_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_totalSize_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_length_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.programMemRows_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.programMemRoots_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.compilerKszOf_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.compilerNOf_irrel,
    ``Nock.NockVMROM.Thm54.TraceGen.rowNounsConfined_iff_bound,
    ``Nock.NockVMROM.Thm54.TraceGen.traceConfined_of_leafBound,
    ``Nock.NockVMROM.Thm54.TraceGen.traceConfined_of_hΛ,
    ``Nock.NockVMROM.Thm54.TraceGen.leafBound_of_traceConfined,
    ``Nock.NockVMROM.Thm54.TraceGen.traceConfined_iff_leafBound,
    ``Nock.NockVMROM.Thm54.TraceGen.one_le_of_leafBound,
    ``Nock.NockVMROM.Thm54.TraceGen.one_le_of_traceConfined,
    ``Nock.NockVMROM.Thm54.TraceGen.bfsRows_pos,
    ``Nock.NockVMROM.Thm54.TraceGen.one_le_of_hΛ_conf,
    ``Nock.NockVMROM.Thm54.TraceGen.sizeWindowNounsBoundedBy_of_traceConfined,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p66,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeedVcompOfWindow]
  for nm in generic do
    unless ← liftTermElabM (hasTypeVarK nm) do
      throwError m!"{nm} has no `K : Type` binder — field-scoped?"
  -- Positive control: the Goldilocks inhabitant has no K binder.
  if ← liftTermElabM (hasTypeVarK ``Nock.RedTeam.Batch298.b298_hmempos_mm) then
    throwError "positive control failed: b298_hmempos_mm should be Goldilocks-scoped"
  logInfo m!"B301-SCOPE {generic.size} new lemmas bind K : Type; control b298_hmempos_mm is fixed-field"

/-! ### D. Proof-term closure, restricted to `Nock.*` (complete for `Nock.*` targets:
no non-`Nock` constant's body can mention a `Nock` constant). Theorems are traversed through
`value? -/

partial def nockClosure (roots : Array Name) : MetaM (Std.HashSet Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if seen.contains c then continue
      seen := seen.insert c
      unless (`Nock).isPrefixOf c do continue
      let some ci := env.find? c | continue
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        cs := cs ++ v.getUsedConstants
      for d in cs do
        unless seen.contains d do work := d :: work
  return seen

run_cmd do
  let n300 : Name := ``Nock.RedTeam.Batch300.b300_nockCompiles_p67_literal
  let n296 : Name := ``Nock.RedTeam.Batch296.b296_nockCompiles_literal
  let seedZ : Name := ``Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.seedZ
  let seedGood : Name := ``Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mmTree_seedGood
  let hbad : Name := ``Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mm_hbad
  let hout : Name := ``Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mm_hout
  let choose : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeedVcomp
  let exv : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_vcomp_seed_of_rom
  let c300 ← liftTermElabM (nockClosure #[n300])
  let c296 ← liftTermElabM (nockClosure #[n296])
  -- Positive control: the literal-seed instance reaches the seed value and its SeedGood proof.
  unless c296.contains seedZ ∧ c296.contains seedGood do
    throwError "positive control failed: b296 should reach seedZ / mmTree_seedGood"
  unless c300.contains choose ∧ c300.contains exv do
    throwError "b300 does not reach romSeedVcomp / exists_vcomp_seed_of_rom"
  let reach (nm : Name) : String := if c300.contains nm then "REACHED" else "absent"
  logInfo m!"B301-CLOSURE b300 Nock-closure size={c300.size}; seedZ:{reach seedZ} mmTree_seedGood:{reach seedGood} mm_hbad:{reach hbad} mm_hout:{reach hout}; romSeedVcomp:{reach choose}"
  logInfo m!"B301-CLOSURE b296 Nock-closure size={c296.size}; seedZ:REACHED mmTree_seedGood:REACHED (control)"
  -- The seed-VALUE facts of the literal route must not be needed by the chosen route.
  if c300.contains seedGood then throwError "b300 reaches mmTree_seedGood (a fact about seedZ's value)"
  if c300.contains hbad then throwError "b300 reaches mm_hbad (a fact about seedZ's value)"
  if c300.contains hout then throwError "b300 reaches mm_hout (a fact about seedZ's value)"

end Batch301BinderWalk

/-! ## Compiled receipts -/

namespace Nock.RedTeam.Batch301

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54
open MemoryTable

noncomputable section

section Chain

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-! ### A. Converse derivations: each successor re-derives its predecessor under the
predecessor's own binders.  With the writer's forward proofs this makes the hypothesis sets
inter-derivable; no surviving hypothesis got stronger. -/

/-- `p64` from `p65`: the `hmempos` binder of `p64` is dead (unused here). -/
noncomputable def b301_p64_from_p65 {q Λ : ℕ}
    (α lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (_hmempos : 0 < (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf α)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K)) :=
  fun hfirst hmore =>
    nockCompiles_p65 α α lmb htwo hgrom hs hf hΛ hconf hwinNouns hseedcard hq hchar orbit horb
      hcomp hmem hwin hmemOrd hKszChar hprogCap hmemCap bas packageOrbit hcap hcard hfirst hmore

/-- `p65` from `p66`: `p66`'s seed term `romSeedVcompOfWindow` is definitionally `p65`'s
`romSeedVcomp` at the caller's own `hΛ`/`hwinNouns` (delta + proof irrelevance), so the
five count hypotheses are accepted unchanged. -/
noncomputable def b301_p65_from_p66 {q Λ : ℕ}
    (α lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf α)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K)) :=
  fun hfirst hmore =>
    nockCompiles_p66 α α lmb htwo hgrom hs hf hconf hseedcard hq hchar orbit horb
      hcomp hmem hwin hmemOrd hKszChar hprogCap hmemCap bas packageOrbit hcap hcard hfirst hmore

/-- `p66` from `p67`: the five transported hypotheses are carried back across the same
equalities (`programMemRows_irrel`, `compilerKszOf_irrel`, `compilerNOf_irrel`,
`genComputeRows_bfsForest_length`), so `p67`'s seed-`0` forms are equivalent to, not weaker
than, `p66`'s chosen-seed forms. -/
noncomputable def b301_p66_from_p67 {q Λ : ℕ}
    (α lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α lmb
      (memInputs (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf α)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K)) :=
  -- Form R leftovers residual on `p67` (live first-row counts are `chainOneBitWeight`).
  nockCompiles_p67 α α lmb htwo hgrom hs hf hΛ hseedcard hq hchar orbit horb
    (by
      rw [← genComputeRows_bfsForest_length
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard)
        α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
      exact hcomp)
    (by
      rw [programMemShape_spec (lmb := lmb)
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard)
        α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
      exact hmem)
    hwin hmemOrd
    (by
      rw [compilerKszOfL_irrel lmb 0
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard)
        α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
      exact hKszChar)
    hprogCap
    (by
      rw [programMemShape_spec (lmb := lmb)
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard)
        α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
      exact hmemCap)
    bas packageOrbit hcap
    (by
      rw [compilerNOfL_irrel lmb 0
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard)
        α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
      exact hcard)

end Chain

variable {K : Type} [Field K]

/-- The two seed spellings of `p65`/`p66` are one term (delta + proof irrelevance). -/
theorem b301_seed_spellings_agree [Fintype K] [DecidableEq K] {q Λ : ℕ}
    (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcompOfWindow hq hchar hs hf hG hrom hconf α hseedcard =
      romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hseedcard :=
  rfl

/-- The old `hcomp` and the new one are the same numeral compared to the same bound. -/
theorem b301_hcomp_bridge (z α : K) (t : NTree (GenComputeRow K)) (n : ℕ) :
    (bfsForest [genComputeRows z α t]).length ≤ n ↔ (bfsRows (airReorder t)).length ≤ n := by
  rw [genComputeRows_bfsForest_length]

/-! ### B. `hmempos` at the two smallest programs, no side hypothesis -/

/-- `*[0 [1 42]] = 42` — the OP1 quote row alone -/
theorem b301_quote_evalRom :
    evalRom 1 (.atom 0) (.cell (.atom 1) (.atom 42)) = some (.atom 42) := by
  simp [evalRom]

/-- `*[42 [0 1]] = 42` — the OP0 leaf row alone -/
theorem b301_op0_evalRom :
    evalRom 1 (.atom 42) (.cell (.atom 0) (.atom 1)) = some (.atom 42) := by
  simp [evalRom, Nock.Noun.slot]

/-- The single-row quote program's generated memory forest is nonempty, for every seed,
timestamp base and threading input.  Nothing about the row is assumed. -/
theorem b301_quote_hmempos (z α : K) (inp : Inputs K) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault inp
      (romTree (K := K) b301_quote_evalRom))).length :=
  genComputeSkeleton_hmempos z α inp (romTree_spec (K := K) b301_quote_evalRom)

theorem b301_op0_hmempos (z α : K) (inp : Inputs K) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault inp
      (romTree (K := K) b301_op0_evalRom))).length :=
  genComputeSkeleton_hmempos z α inp (romTree_spec (K := K) b301_op0_evalRom)

/-- The quote row commits a request (the formula-open `mem_record₁`). -/
theorem b301_quote_root_request :
    (romTree (K := K) b301_quote_evalRom).label.requests ≠ [] :=
  (genComputeSkeleton_root_requests (romTree_spec (K := K) b301_quote_evalRom)).1

/-- The paper-side counterpart: every compute state requests at least one record. -/
theorem b301_recordCount_pos (s : ComputeTable.State) :
    1 ≤ Nock.Framework.recordCount s :=
  Nock.Framework.recordCount_pos s

/-! ### C. Seed `0` is a dummy for the shape counts; the seed actually used is nonzero -/

theorem b301_programMemRows_zero_dummy [Fintype K] [DecidableEq K] [CharP K (ringChar K)] (z α : K) (t : NTree (GenComputeRow K)) :
    programMemRows (0 : K) α t = programMemRows z α t :=
  programMemRows_irrel (0 : K) z α t

theorem b301_compilerKszOf_zero_dummy [Fintype K] [DecidableEq K] [CharP K (ringChar K)] (z α : K) (t : NTree (GenComputeRow K)) :
    compilerKszOf (0 : K) α t = compilerKszOf z α t :=
  compilerKszOf_irrel (0 : K) z α t

theorem b301_compilerNOf_zero_dummy [Fintype K] [DecidableEq K] [CharP K (ringChar K)] (z α : K) (t : NTree (GenComputeRow K)) :
    compilerNOf (0 : K) α t = compilerNOf z α t :=
  compilerNOf_irrel (0 : K) z α t

/-- The seed `p67` actually compiles with is nonzero — the `0` in its statement is never
the seed of the trace, only the argument of a seed-independent count. -/
theorem b301_chosen_seed_ne_zero [Fintype K] [DecidableEq K] {q Λ : ℕ}
    (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcompOfWindow hq hchar hs hf hG hrom hΛ α hseedcard ≠ 0 :=
  romSeedVcomp_ne_zero hq hchar hs hf hG hrom (one_le_of_hΛ_conf hΛ) hΛ α
    (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
      (romTree_spec (K := K) hrom) hΛ []) hseedcard

/-- F-3 receipt: the `hΛ : 1 ≤ Λ` binder of `sizeWindowNounsBoundedBy_of_traceConfined` is
derivable from its own `hconf`; the supplier can be stated at `TraceConfined` alone. -/
theorem b301_hwinNouns_of_traceConfined_only {Λ : ℕ}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    SizeWindowNounsBoundedBy (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hconf) h hconf mf

/-- §1 spelling: `p67`'s window binder is `programLeafBound … ≤ Λ`, verbatim. -/
theorem b301_window_is_leafBound {Λ : ℕ} (t : NTree (GenComputeRow K)) :
    TraceConfined Λ (airReorder t) ↔ programLeafBound (airReorder t) ≤ Λ :=
  traceConfined_iff_leafBound

/-- `bfsRows_pos` (new) duplicates the pre-existing `bfsRows_length_pos` (F-6). -/
theorem b301_bfsRows_pos_duplicate (t : NTree (GenComputeRow K)) :
    0 < (bfsRows t).length :=
  bfsRows_length_pos t

end

/-! ### E. Non-vacuity of `b300` -/

section Goldilocks

open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.RedTeam.Batch300

/-- The evaluator route independent of `mm_evalN`'s generator route -/
theorem b301_claim_evalN : Nock.evalN 64 mmSubject mmFormula = some mmC :=
  evalGRom_evalN mm_grom

theorem b301_claim_literal : mmC =
    .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1)) := rfl

theorem b301_gf : Nock.RedTeam.Batch300.GF = Nock.Field.Fp := rfl
theorem b301_gk : Nock.RedTeam.Batch300.GK = Nock.Field.K := rfl

noncomputable def b301_b300_restated :=
  fun hfirst hmore hax hbasis hwidth =>
    (Exists.imp (fun _ hp => ⟨hp.1, hp.2.1⟩) (b300_nockCompiles_p67_literal hfirst hmore hax hbasis hwidth) :
      ∃ package : Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
          Nock.Field.Fp Nock.Field.K 16,
        Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement package
          ∧ package.optimized.verifier.raw.claim =
            ⟨mmSubject, mmFormula, .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1))⟩)

/-- The claimed triple satisfies the paper evaluator predicate. -/
theorem b301_claim_Holds : P8PublicClaim.Holds ⟨mmSubject, mmFormula, mmC⟩ :=
  ⟨64, b301_claim_evalN⟩

end Goldilocks

end Nock.RedTeam.Batch301

#print axioms Nock.RedTeam.Batch301.b301_p64_from_p65
#print axioms Nock.RedTeam.Batch301.b301_p65_from_p66
#print axioms Nock.RedTeam.Batch301.b301_p66_from_p67
#print axioms Nock.RedTeam.Batch301.b301_seed_spellings_agree
#print axioms Nock.RedTeam.Batch301.b301_hcomp_bridge
#print axioms Nock.RedTeam.Batch301.b301_quote_hmempos
#print axioms Nock.RedTeam.Batch301.b301_op0_hmempos
#print axioms Nock.RedTeam.Batch301.b301_quote_root_request
#print axioms Nock.RedTeam.Batch301.b301_programMemRows_zero_dummy
#print axioms Nock.RedTeam.Batch301.b301_chosen_seed_ne_zero
#print axioms Nock.RedTeam.Batch301.b301_hwinNouns_of_traceConfined_only
#print axioms Nock.RedTeam.Batch301.b301_claim_evalN
#print axioms Nock.RedTeam.Batch301.b301_b300_restated
#print axioms Nock.RedTeam.Batch301.b301_claim_Holds
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p66
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
#print axioms Nock.RedTeam.Batch300.b300_nockCompiles_p67_literal
