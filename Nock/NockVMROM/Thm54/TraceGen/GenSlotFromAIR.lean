/-
  Nock/NockVMROM/Thm54/TraceGen/GenSlotFromAIR.lean

  **The `served` field of `ServedMemoryTrace.Service` is not primitive data.**

  `Service` (`ServedMemoryTrace.lean:184-194`) carries the Nock semantic fact
  `served : Noun.slot axis root = some child` as a *field*, and every packager of a service at an
  arbitrary accepted execution therefore takes it as a hypothesis
  (`TraceGen/GenServedRoots.lean:241`'s `hslot`; `GenGlobalCollision.ServedSlotCovers` asks for a
  whole `Service`, `served` included).  On the generated route the fact is free — `Gen.lean:575`
  builds `genSkelOp0` inside `match Nock.Noun.slot ax subject with | some result =>`, so it is the
  generator's own matched hypothesis — which is exactly why it reads as irreducible off that route.

  It is not.  `ServedMemoryTrace.VerifyRoute` (`:222-244`) is a *structural* object: a noun-indexed
  descent inside one committed memory tree, whose step list is the **binary expansion of the
  committed axis** and whose terminal constructor binds the verify node's
  realized noun to the record's child and its committed `address` column to the record's axis.  `VerifyRoute.served` already derives `Noun.slot (pathAxis bs) n = some child`
  from that data, and `pathAxis_axisPath` (`:117`) evaluates `pathAxis (axisPath a) = a` for
  `1 ≤ a`.  Composing the two turns the slot fact into a theorem about route data.

  So this module records the reduction, in the only place it changes the accounting:

  * `ServiceCore` is `Service` **minus `served`**, plus the positivity `1 ≤ axis` that `Service`
    currently derives *from* `served` (`Service.axis_pos`).  Positivity is not a new premise on a
    refinement route either: `pathAxis_pos` (`:70`) makes every route axis `≥ 1`, so a route plus
    `RealizesMemRec.axis_realizes` and cast injectivity forces it.  Every field of it is either a
    membership in committed data (`request_mem`), a committed-column equation (`timestamp`), or the
    fingerprint↔noun realization datum `OpcodeSemantics.RealizesMemRec` — the paper's
    "check that the initial input is the valid public noun" setup datum.
    None of them is a Nock evaluation fact.
  * `served_of_verifyRoute` / `ServiceCore.toService` produce the full `Service` from a
    `ServiceCore` and one route, so a supplier of route data supplies `served` for free.

  ## What this does NOT close, stated exactly

  The route's noun index is still supplied, not decoded.  `AxisBridge.toMTree` (`:129`) erases
  every fingerprint column, `NounShape` is free at `canonNoun` (`:2296`), and no `FP K → Noun`
  decoder exists or can: `FPDecoderCounterRegression.old_global_injectivity_false` compiles a
  bounded-domain collision.  The residual is therefore a **memory-walk noun refinement** — a noun
  label at every committed memory node, tied to `pt.noun` by `Realizes` and upgraded from the
  `eqBlk` decompose/halt *fingerprint* equations (`MemoryTable.lean:204-225`) to noun equations by a
  counted good-seed event (`GlobalCarryRecognizer.decompose_forces_cons` is the induction step).
  That premise is strictly weaker than `hslot`: it is a fingerprint-realization datum, not a Nock
  semantic claim.  Ancestry is a second, separate residual — `AxisBridge.readVerifyNested_wall_harmful`
  shows the paper's arithmetized memory gates do not force `ReadVerifyNested`, and this tree closes
  it with an explicit Boolean structure check
  (`ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_accepts`), not with a gate of
  `Algorithm:Memspec`.

  Scope: `∀ cfg : ExactConfig F K`, `∀ exec : ExactExecution cfg`.  No `Data`, no
  `BuildableNockExecution`, no generated object, no fixed field, no fixed axis.  `Gen.lean`
  unedited; no `sorry`, no new axiom, no carrier field.
-/
import Nock.NockVMROM.Thm54.ServedMemoryTrace

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR

open Nock
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. The served-free service datum -/

/-- **`Service` minus its Nock fact.**  `exponent`/`record`/`root`/`child`/`axis` and the three
non-semantic obligations of `ServedMemoryTrace.Service`, plus the axis positivity that `Service`
obtains from `served` (`Service.axis_pos`).  `realization` is the fingerprint↔noun datum; nothing here mentions
`Noun.slot`. -/
structure ServiceCore (cfg : ExactConfig F K) (exec : ExactExecution cfg) where
  exponent : ℕ
  record : ComputeTable.MemRec K
  root : Noun
  child : Noun
  axis : ℕ
  axis_pos : 1 ≤ axis
  request_mem : record ∈ exec.rawRequests
  timestamp : record.ts = cfg.challenges.α ^ exponent
  realization : OpcodeSemantics.RealizesMemRec cfg.challenges.z record root child axis

/-- A `Service` forgets to a `ServiceCore` (positivity from `Service.axis_pos`). -/
def Service.toCore {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : Service cfg exec) : ServiceCore cfg exec where
  exponent := s.exponent
  record := s.record
  root := s.root
  child := s.child
  axis := s.axis
  axis_pos := s.axis_pos
  request_mem := s.request_mem
  timestamp := s.timestamp
  realization := s.realization

/-! ## B. The slot fact from route data -/

/-- **The slot fact at the ordinary Nock axis.**  A route whose step list is the binary expansion
of `ax` derives `\(ax, n\) ↦ child`: `VerifyRoute.served` gives it at `pathAxis (axisPath ax)` and
`pathAxis_axisPath` evaluates that to `ax`.  No slot equation, acceptance predicate or carrier
field is used. -/
theorem served_of_verifyRoute {e ax : ℕ} {child n : Noun} {recAxis : K} {c : MTree K}
    (hax : 1 ≤ ax) (route : VerifyRoute e child recAxis (axisPath ax) n c) :
    Noun.slot ax n = some child := by
  have h := route.served
  rwa [pathAxis_axisPath ax hax] at h

/-- **`served` is derivable, not primitive.**  A `ServiceCore` together with one route inside a
committed memory tree — the route indexed by the core's own root noun and stepped by the binary
expansion of its own axis — yields the full `Service`, its `served` field discharged by
`served_of_verifyRoute`. -/
def ServiceCore.toService {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : ServiceCore cfg exec) {c : MTree K}
    (route : VerifyRoute s.exponent s.child s.record.axis (axisPath s.axis) s.root c) :
    Service cfg exec where
  exponent := s.exponent
  record := s.record
  root := s.root
  child := s.child
  axis := s.axis
  request_mem := s.request_mem
  timestamp := s.timestamp
  realization := s.realization
  served := served_of_verifyRoute s.axis_pos route

/-- The reduction is faithful on the data: `toService` changes no field except by adding the
derived one. -/
theorem ServiceCore.toService_toCore {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : ServiceCore cfg exec) {c : MTree K}
    (route : VerifyRoute s.exponent s.child s.record.axis (axisPath s.axis) s.root c) :
    Service.toCore (s.toService route) = s := rfl

/-- Existential form: route data at a core supplies the `∃ svc : Service` that
`GenGlobalCollision.ServedSlotCovers` asks for, with the record, nouns and axis of the core. -/
theorem exists_service_of_verifyRoute {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : ServiceCore cfg exec) {c : MTree K}
    (route : VerifyRoute s.exponent s.child s.record.axis (axisPath s.axis) s.root c) :
    ∃ svc : Service cfg exec,
      svc.record = s.record ∧ svc.root = s.root ∧ svc.child = s.child ∧ svc.axis = s.axis :=
  ⟨s.toService route, rfl, rfl, rfl, rfl⟩

end

/-! ## C. Axiom receipts -/

#print axioms Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR.served_of_verifyRoute
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR.ServiceCore.toService
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR.ServiceCore.toService_toCore
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR.exists_service_of_verifyRoute

end Nock.NockVMROM.Thm54.TraceGen.GenSlotFromAIR
