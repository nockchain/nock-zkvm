/-
  Nock/RedTeam/Batch1351Thm54CompletenessCut.lean

  Build-enforced measurement; no new theorem about the package.

  That was
  incomplete.  Measured by a proof-term walk (type and `value? (allowOpaque := true)`) with the
  named constants OPAQUE (type walked, body not):

  | opaque set                   | `finiteIO_complete_of_LIO` from each of the three roots |
  |------------------------------|----------------------------------------------------------|
  | none                         | reached (shortest paths of length 18 / 19 / 22)          |
  | `masks_at_row_at` only       | reached (via `compute_requests_eq_memory_requests`, which reads `P.optimized.sampled.witness10.terminal`, `→ witness10 → witness10_exists`) |
  | `witness10_exists` only      | UNREACHED                                                |
  | both                         | UNREACHED                                                |

  * **(A) `witness10_exists` is the single route.**  With it opaque, the constant is unreached
    from all three roots; with nothing opaque it is reached.  `witness10_exists` is a definitional
    dependency of the package's `witness10` field (data built by choice), not a completeness
    premise.
  * **(B) The mask route is a sub-route through it.**  `masks_at_row_at` reaches
    `witness10_exists` (`→ computeRealization → computeRealization_of_leafCover →
    optimizedComputeRealization → ExactFinalRequestsCoordinate → witness10 → witness10_exists`),
    and with `witness10_exists` opaque `masks_at_row_at` no longer reaches the constant.

  The
  soundness proof reads `witness10`/masks as committed package data and never unfolds how the
  compiler produced them; the type scan and the entry measurement rule out a hidden premise.

  * Negative controls: the same scan flags
    the types of the three soundness roots and of `consumedFailureEvent`.
  * **(E) Where the cut is entered.**  Every in-edge of the cut is a VALUE edge (the definition `witness10`, `Classical.choose`, and
    `witness10_accepts`); every route into the data side passes through
    `ExactFinalRequestsCoordinate`.  The soundness proof reads `witness10`/masks as committed
    package data and never unfolds how the compiler produced them; the type scan and the entry
    measurement rule out a hidden premise.
  * **(F) Reached, not used: the specification of `witness10`.**  The soundness roots reach
    `witness10_accepts` only inside the proof argument `canonical_satisfies` of
    `optimizedComputeRealization`'s constructor; no root projects that field (measured over the
    37905 constants of the reach set), and the two projected fields reduce to
    `P.computeNodes_injective` / `P.computeAdjacentOrbit`; by proof irrelevance the specification
    of `witness10` is reached, not used.  The only field projections of
    `OptimizedComputeRealizationAt` in the reach set are `nodes_injective` (in
    `Batch457.masks_at_row_at`) and `adjacent_orbit` (in `Batch459.envF_traceNext_eq`); there is no
    `casesOn`/`rec` on the structure; all ten fields are Props.  Path: root →
    `acceptance_outside_failure_implies_target` → `holds_of_acceptance_evOnly` →
    `tracesWalkHyps_of_acc_evOnly` → `Batch489.tracesWalkHyps_of_deployed_ev` →
    `tracesWalkHyps_of_failureEvent_ev` → `WalkQueueDeployed.tracesWalkHyps_of_chips` →
    `tracesWalkHyps_compute` → `deployed_tiling` → `count_eq_ln_last` →
    `Batch459.isLast_source_last` → `Batch457.masks_at_row_at` (projects `nodes_injective`) →
    `computeRealization` → `computeRealization_of_leafCover` → `optimizedComputeRealization`
    (`mk`) → `correctedCanonicalFinalTrace_satisfies` → `canonical_corrected_source_obligations`
    → `canonical_endpoint_obligations` → `witness10_accepts`.  Negative control: a probe theorem
    projecting `canonical_satisfies` is flagged by the same scan.
  * **History / retype.**  The `witness10_exists` opaque-cut table above is the earlier measurement
    (kept).
-/
import Nock.RedTeam.Batch264Thm54IOTrackReview
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch1351

open Lean Elab Command Meta
open Nock.RedTeam.Batch264.Audit

def target : Name := `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_complete_of_LIO
def maskRoot : Name := `Nock.RedTeam.Batch457.masks_at_row_at
def cut : Name := `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10_exists

/-- The mask sub-route's intermediate constants (measured BFS path). -/
def maskSubRoute : List Name :=
  [ `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.computeRealization,
    `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10 ]

/-- The receipt's cut is `Batch264`'s. -/
theorem cut_is_batch264_cut : cut = completenessCut := rfl


/-! ## (D) The type of the cut, measured -/

/-- Last name components that the cut's type must not mention (hostile-side objects). -/
def forbiddenLast : List String :=
  [ "DeployedAcceptanceAt", "OptimizedProductionAcceptanceAt", "consumedFailureEvent",
    "optimizedFailureEvent", "optimizedFailureEventEv", "familyQc", "familyQm" ]

def forbiddenBinders : List String := [ "Qc", "Qm", "c" ]

def isForbiddenConst (n : Name) : Bool :=
  match n with
  | .str _ s => forbiddenLast.contains s || s.endsWith "ChallengeTuple"
  | _ => false

/-- Binder names occurring anywhere in an expression. -/
partial def binderNames : Expr → List Name
  | .forallE n t b _ => n :: binderNames t ++ binderNames b
  | .lam n t b _ => n :: binderNames t ++ binderNames b
  | .letE n t v b _ => n :: binderNames t ++ binderNames v ++ binderNames b
  | .app f a => binderNames f ++ binderNames a
  | .mdata _ e => binderNames e
  | .proj _ _ e => binderNames e
  | _ => []

/-- The scan: forbidden constants and forbidden binder names in the TYPE of `n`. -/
def typeScan (env : Environment) (n : Name) : Option (List Name × List Name) :=
  (env.find? n).map fun ci =>
    ((ci.type.getUsedConstants.toList.filter isForbiddenConst),
     (binderNames ci.type).filter fun b => forbiddenBinders.contains b.toString)

/-- The hostile-data names reachable from the type by walking TYPES and the VALUES of
definitions (theorem proof terms are not walked: they are proofs, not data). -/
partial def typeDataClosure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [n]
  while true do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if seen.contains m then continue
      seen := seen.insert m
      match env.find? m with
      | none => pure ()
      | some ci =>
        let used := ci.type.getUsedConstants
        let used := match ci with
          | .defnInfo d => used ++ d.value.getUsedConstants
          | _ => used
        for u in used do
          if !seen.contains u then stack := u :: stack
  return seen

/-! ## (E) Where the cut is entered, measured -/

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

def kindOfName (env : Environment) (n : Name) : String := ((env.find? n).map kindOf).getD "?"

/-- Out-edges of `n`, labelled `"type"` (binder / statement) or `"value"` (definition body or
proof term). -/
def succs (env : Environment) (n : Name) : Array (Name × String) :=
  match env.find? n with
  | none => #[]
  | some ci =>
    (ci.type.getUsedConstants.map (·, "type")) ++
      (match ci.value? (allowOpaque := true) with
       | some v => v.getUsedConstants.map (·, "value") | none => #[])

/-- Shortest path (BFS) from `r` to `cut`, each edge as `(src, via, dst)`. -/
def bfsPath (env : Environment) (r : Name) : List (Name × String × Name) := Id.run do
  let mut parent : Std.HashMap Name (Name × String) := {}
  let mut seen : NameSet := NameSet.empty.insert r
  let mut q : Array Name := #[r]
  let mut i := 0
  while i < q.size do
    let n := q[i]!
    i := i + 1
    if n == cut then break
    for (u, v) in succs env n do
      if !seen.contains u then
        seen := seen.insert u
        parent := parent.insert u (n, v)
        q := q.push u
  let mut path : List (Name × String × Name) := []
  let mut cur := cut
  while cur != r do
    match parent[cur]? with
    | some (p, v) => path := (p, v, cur) :: path; cur := p
    | none => break
  return path

/-- All constants that reach `cut` inside the reach set `R` of the soundness roots. -/
def ancestors (env : Environment) (R : NameSet) : NameSet := Id.run do
  let mut preds : Std.HashMap Name (Array Name) := {}
  for n in R do
    for (u, _) in succs env n do
      if R.contains u then preds := preds.insert u ((preds.getD u #[]).push n)
  let mut A : NameSet := NameSet.empty.insert cut
  let mut st : Array Name := #[cut]
  while !st.isEmpty do
    let n := st.back!
    st := st.pop
    for p in preds.getD n #[] do
      if !A.contains p then
        A := A.insert p
        st := st.push p
  return A


/-! ## (F) Reached, not used -/

end Nock.RedTeam.Batch1351

open Nock.RedTeam.Batch1351 Nock.RedTeam.Batch264.Audit Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  for n in [target, maskRoot, cut] ++ maskSubRoute ++ soundnessRoots do
    if env.find? n |>.isNone then throwError "[B1351] VACUOUS: unresolved name {n}"
  for r in soundnessRoots do
    -- positive control: reached with nothing opaque
    if !(reach env [r]).contains target then
      throwError "[B1351] {target} unreached from {r} with nothing opaque — instrument suspect"
    -- (C): the mask cut alone does not suffice
    if !(reachOpaque env [r] [maskRoot]).contains target then
      throwError "[B1351] {target} unreached from {r} with only {maskRoot} opaque — table row 2 changed"
    -- (A): the single cut
    if (reachOpaque env [r] [cut]).contains target then
      throwError "[B1351] {target} reached from {r} avoiding {cut}"
    if (reachOpaque env [r] [cut, maskRoot]).contains target then
      throwError "[B1351] {target} reached from {r} with both cuts opaque"
    logInfo m!"[B1351] {r}: reached; with {maskRoot} opaque reached; with {cut} opaque UNREACHED"
  -- (B): the mask route is a sub-route through the cut
  let sm := reach env [maskRoot]
  for n in maskSubRoute ++ [cut, target] do
    if !sm.contains n then throwError "[B1351] {n} not reached from {maskRoot}"
  if (reachOpaque env [maskRoot] [cut]).contains target then
    throwError "[B1351] {maskRoot} reaches {target} avoiding {cut}"
  logInfo m!"[B1351] {maskRoot} reaches {cut} through {maskSubRoute}; with {cut} opaque it does not reach {target}"

open Nock.RedTeam.Batch1351 Nock.RedTeam.Batch264.Audit Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  -- (D) the type of the cut
  let some (cs, bs) := typeScan env cut | throwError "[B1351] {cut} missing"
  logInfo m!"[B1351 D] type of {cut}: forbidden constants {cs}, forbidden binder names {bs}"
  unless cs.isEmpty && bs.isEmpty do throwError "[B1351 D] STOP: the cut's type mentions hostile data"
  let cl := typeDataClosure env cut
  let hits := (cl.toList).filter isForbiddenConst
  logInfo m!"[B1351 D] type/def-value closure of the cut: {cl.size} constants, forbidden hits {hits}"
  unless hits.isEmpty do throwError "[B1351 D] STOP: the cut's data closure reaches {hits}"
  -- negative controls: the scan flags types that do mention the names
  for r in soundnessRoots do
    let some (cs', bs') := typeScan env r | throwError "[B1351] {r} missing"
    if cs'.isEmpty && bs'.isEmpty then throwError "[B1351 D] NC FAILED: scan did not flag the type of {r}"
    logInfo m!"[B1351 D] NC {r}: constants {cs'}, binders {bs'}"
  let some (csN, _) := typeScan env `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.consumedFailureEvent
    | throwError "[B1351] consumedFailureEvent missing"
  if csN.isEmpty then throwError "[B1351 D] NC FAILED: consumedFailureEvent's type not flagged"
  let hitsN := ((typeDataClosure env soundnessRoots.head!).toList).filter isForbiddenConst
  if hitsN.isEmpty then throwError "[B1351 D] NC FAILED: closure scan flags nothing from a soundness root"
  -- (E) where the cut is entered
  let R := reach env soundnessRoots
  let A := ancestors env R
  logInfo m!"[B1351 E] reach set {R.size}; ancestors of the cut {A.size}"
  for r in soundnessRoots do
    let path := bfsPath env r
    let ks := path.map fun (a, _, _) => kindOfName env a
    logInfo m!"[B1351 E] {r}: shortest path, {path.length} edges, source kinds {ks}"
    for (a, v, b) in path do
      logInfo m!"[B1351 E]   {a} [{kindOfName env a}] --{v}--> {b} [{kindOfName env b}]"
    -- shape: theorem proof terms, then data (def) nodes, then the cut; no theorem between data nodes
    let firstDef := ks.findIdx? (· == "def")
    match firstDef with
    | none => throwError "[B1351 E] {r}: no data node on the path"
    | some i =>
      if (ks.drop i).any (· == "thm") then throwError "[B1351 E] STOP: {r}: a theorem sits between data nodes on the path"
      if (ks.take i).any (· != "thm") then throwError "[B1351 E] {r}: unexpected kind before first data node"
    match path.getLast? with
    | some (a, "value", b) =>
      unless a == `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10 && b == cut do
        throwError "[B1351 E] {r}: last edge is not witness10 --value--> cut"
    | _ => throwError "[B1351 E] {r}: last edge is not a value edge"
    -- a hypothesis of the root (an edge from its TYPE) must not lie in the ancestor set of the cut
    for (u, v) in succs env r do
      if v == "type" && A.contains u then throwError "[B1351 E] STOP: the type of {r} reaches {u}, an ancestor of the cut"
  -- negative control: the same hypothesis check flags a theorem whose premise `hreq` is in the set
  let ncT := `Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction.correctedCanonicalFinalTrace_satisfies
  if !((succs env ncT).any fun (u, v) => v == "type" && A.contains u) then
    throwError "[B1351 E] NC FAILED: hypothesis check does not flag {ncT}"
  logInfo m!"[B1351 E] hypothesis check: no soundness root's type reaches the {A.size} ancestors; NC {ncT} flagged"
  -- every in-edge of the cut
  let mut ins : List (Name × String) := []
  for n in A do
    for (u, v) in succs env n do
      if u == cut then ins := (n, v) :: ins
  logInfo m!"[B1351 E] in-edges of the cut: {ins.map fun (n, v) => (n, kindOfName env n, v)}"
  for (n, v) in ins do
    if v != "value" then throwError "[B1351 E] STOP: {n} enters the cut through its TYPE"
    unless n == `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10 ||
        n == `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10_accepts do
      throwError "[B1351 E] unexpected in-edge {n}"
  -- every edge inside the ancestor set, classified; data-to-theorem and statement edges listed
  let mut cnt : Std.HashMap String Nat := {}
  let mut dataThm : List Name := []
  let mut stmt : List (Name × Name) := []
  for n in A do
    for (u, v) in succs env n do
      if A.contains u then
        let kn := kindOfName env n
        let ku := kindOfName env u
        let key := s!"{kn} --{v}--> {ku}"
        cnt := cnt.insert key (cnt.getD key 0 + 1)
        if (kn == "def" || kn == "ctor") && ku == "thm" && u != cut then dataThm := u :: dataThm
        if v == "type" && kn != "thm" then stmt := (n, u) :: stmt
  for (k, c) in cnt.toList do logInfo m!"[B1351 E] edge class {k}: {c}"
  logInfo m!"[B1351 E] data-to-theorem edges (not into the cut): {dataThm}"
  logInfo m!"[B1351 E] statement (type) edges out of data nodes: {stmt}"

open Nock.RedTeam.Batch1351 Nock.RedTeam.Batch264.Audit Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let R := reach env soundnessRoots
  let mut seenUses : List String := []
  for n in R do
    for u in usesOf env n do
      unless allowedUses.contains u do
        throwError "[B1351 F] STOP: {n} uses OptimizedComputeRealizationAt ({u})"
      seenUses := u :: seenUses
  logInfo m!"[B1351 F] reach set {R.size}; uses of OptimizedComputeRealizationAt: {seenUses.eraseDups}"
  for need in ["const nodes_injective", "const adjacent_orbit", "const mk"] do
    unless seenUses.contains need do throwError "[B1351 F] instrument suspect: no {need} found"
  -- negative control: the probe is flagged
  let probe := `Nock.RedTeam.Batch264.Audit.probe_projects_canonical_satisfies
  let pu := usesOf env probe
  if allowedUses.contains "const canonical_satisfies" || !pu.contains "const canonical_satisfies" then
    throwError "[B1351 F] NC FAILED: probe not flagged ({pu})"
  logInfo m!"[B1351 F] NC: the probe's uses {pu} include canonical_satisfies (flagged)"

#print axioms Nock.RedTeam.Batch1351.cut_is_batch264_cut
