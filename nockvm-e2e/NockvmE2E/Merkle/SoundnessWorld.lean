/-
Merkle (B) file 10a: the instrumented real world W' (`worldW`: `verifiedFS A` with the
reduction and Phases observers, then the honest check of the memo-pointed claims). `pr_real_eq`
(W' is the succinct experiment), `hmem_of_support` (memo/checkpoint invariant), `good_of_support` and
`pr_world_split` (off the bad event the run is good), `pr_bad_le` (BadBound), bound transport.
-/
import NockvmE2E.Merkle.BadBound
import NockvmE2E.Merkle.FreshKeys
import NockvmE2E.Merkle.NonVacuous

open OracleComp OracleSpec MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.SoundnessWorld

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good

section Defs

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
/-- compiled execution paths -/
abbrev PathC (Y Op : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op] (ms : MRounds Y) :=
  (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath
/-- output of A followed by its compiled FS verification -/
abbrev Out1 (Y Op Statement Salt W : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) :=
  Option ((Statement × SaltedProof Salt (compiledRoundsK Y Op ms) × W) × Option (PathC Y Op ms))
/-- the verified output with the reduction observer state -/
abbrev OutO (Y Op Query Statement Salt W : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) := Out1 Y Op Statement Salt W ms × Reduction.Obs Query Statement Salt Y
/-- FS challenges of the compiled keys -/
abbrev KC (Y Op Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms) → Type := Key.Challenge
/-- **`verifiedFS`**: A, then QD's compiled public stopped FS verification of its proof
(FS queries only). -/
def verifiedFS (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) (Out1 Y Op Statement Salt W ms) := do
  match ← A with
  | none => pure none
  | some o => (fun p? => some (o, p?)) <$>
      simulateQ fsQueriesK (publicStoppedVerify _ guards (o.1, o.2.1.1) o.2.1.2)
/-- the hash-check acceptance bits of a verified output (claims with empty logs) -/
def bitsProg (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms)) :
    Out1 Y Op Statement Salt W ms → OracleComp (Query →ₒ Y) (List Bool)
  | some (_, some p) => acceptBits <$> verifyOpeningClaims model
      (mkClaims (merkleSkels ms) (pathRootsK Y Op ms p).1 (pathRootsK_length_skels p)
        (decode (pathRootsK Y Op ms p).2) fun _ => [])
  | _ => pure []
/-- the succinct verdict from a verified output and the hash-check bits -/
def finOut (localAccepts : (Statement × Salt) → PathC Y Op ms → Bool) :
    Out1 Y Op Statement Salt W ms → List Bool →
      Option ((Statement × Salt) × PathC Y Op ms × W)
  | some (o, some p), bits =>
      if bits.all id && localAccepts (o.1, o.2.1.1) p then some ((o.1, o.2.1.1), p, o.2.2) else none
  | _, _ => none
theorem succinct_eq (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (decode : Op → OpenAll Y (merkleSkels ms))
    (localAccepts : (Statement × Salt) → PathC Y Op ms → Bool)
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    succinctAcceptedExecutionK guards (merkleCheck (merkleSkels ms) model decode) localAccepts A =
      verifiedFS guards A >>= fun a =>
        finOut localAccepts a <$> simulateQ hashQueriesK (bitsProg model decode a) := by
  unfold succinctAcceptedExecutionK verifiedFS
  simp only [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with _ | ⟨statement, ⟨salt, msgs⟩, w⟩
  · simp [bitsProg, finOut]
  · simp only [succinctVerifyK, bind_map_left, bind_assoc]
    refine bind_congr fun p? => ?_
    rcases p? with _ | p
    · simp [bitsProg, finOut]
    · dsimp only
      rw [merkleCheck_of_length _ model decode _ _ (pathRootsK_length_skels p)]
      simp only [bitsProg, finOut, simulateQ_map, Functor.map_map, bind_pure_comp]
      refine congrArg (fun f => f <$> _) (funext fun a => ?_)
      split_ifs <;> rfl


/-! ## The reduction observer on A's oracle (`obsR`), and the Phases instance -/

/-- observer step on any query of A's oracle (coins are not observed) -/
def stepR (s : Obs Query Statement Salt Y) :
    (t : (SuccinctSpecK Y Op Query Statement Salt ms).Domain) →
      (SuccinctSpecK Y Op Query Statement Salt ms).Range t → Obs Query Statement Salt Y
  | .inl _, _ => s
  | .inr t, a => obsStep Y Op ms s t a
/-- the reduction's observer (hash log, memo) as a forwarding handler on A's own oracle -/
def obsR : QueryImpl (SuccinctSpecK Y Op Query Statement Salt ms)
    (StateT (Obs Query Statement Salt Y) (OracleComp (SuccinctSpecK Y Op Query Statement Salt ms))) :=
  fun t => StateT.mk fun s => (fun a => (a, stepR s t a)) <$>
    (liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) :
      OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) _)
theorem obsR_fst (t : (SuccinctSpecK Y Op Query Statement Salt ms).Domain)
    (s : Obs Query Statement Salt Y) :
    Prod.fst <$> ((obsR (ms := ms) (Op := Op)) t).run s =
      (liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) :
        OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) _) := by
  simp [obsR]
theorem obsR_run_bind {α : Type} (t : (SuccinctSpecK Y Op Query Statement Salt ms).Domain)
    (k : (SuccinctSpecK Y Op Query Statement Salt ms).Range t →
      OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α)
    (s : Reduction.Obs Query Statement Salt Y) :
    (simulateQ obsR (liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) >>= k)).run s =
      (liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) :
        OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) _) >>= fun a =>
          (simulateQ obsR (k a)).run (stepR s t a) := by
  simp [obsR, simulateQ_bind, StateT.run_bind]
/-- the instrumented A₁: `verifiedFS A` with the reduction observer -/
def instrA (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) (OutO Y Op Query Statement Salt W ms) :=
  (simulateQ obsR (verifiedFS guards A)).run Obs.init
theorem fst_instrA (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    Prod.fst <$> instrA guards A = verifiedFS guards A :=
  Derand.observer_run' obsR obsR_fst _ _

variable (hpos : 0 < (merkleSkels ms).length)

/-- tag of a root prefix of length `n` -/
def tagOf (n : ℕ) : Fin (merkleSkels ms).length :=
  if h : n < (merkleSkels ms).length then ⟨n, h⟩ else ⟨0, hpos⟩
/-- Phases' checkpoint roots of an FS key: (tag = prefix length, root) of each memo entry -/
def keyRootsK (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) :
    List (Fin (merkleSkels ms).length × Y) :=
  (keyEntries ms [] d).map fun e => (tagOf hpos e.1.length, e.2)
/-- the `j`-th root of a compiled path -/
def rootAt (p : PathC Y Op ms) (j : Fin (merkleSkels ms).length) : Y :=
  (pathRootsK Y Op ms p).1.get (j.cast (pathRootsK_length_skels p).symm)
/-- (root prefix, root) of each merkle round of a compiled path -/
def pathEntries (p : PathC Y Op ms) : List (List Y × Y) :=
  List.ofFn fun j : Fin (merkleSkels ms).length => ((pathRootsK Y Op ms p).1.take j, rootAt p j)
/-- (tag, root) of each merkle round of a compiled path -/
def pathCkpts (p : PathC Y Op ms) : List (Fin (merkleSkels ms).length × Y) :=
  List.ofFn fun j : Fin (merkleSkels ms).length => (j, rootAt p j)
/-- the end-of-run memo: checkpoints (current log) for the roots of the verified path -/
def finObsR (s : Obs Query Statement Salt Y) (z : Statement × Salt) (p : PathC Y Op ms) :
    Obs Query Statement Salt Y :=
  { s with memo := addEntries z (pathEntries p) (s.nck, s.log) s.memo }
/-- the statement and salt of A's output -/
def zOf (o : Statement × SaltedProof Salt (compiledRoundsK Y Op ms) × W) : Statement × Salt :=
  (o.1, o.2.1.1)
/-- Phases' final roots: the roots of the verified path -/
def finalRootsK (a : OutO Y Op Query Statement Salt W ms) :
    List (Fin (merkleSkels ms).length × Y) :=
  match a.1 with
  | some (_, some p) => pathCkpts p
  | _ => []
/-- Phases' terminal claims: the memo-pointed claims of the verified path -/
def mkT (decode : Op → OpenAll Y (merkleSkels ms)) (a : OutO Y Op Query Statement Salt W ms)
    (_ : ExtractorState (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y
      (mconfig (merkleSkels ms))) :
    List (OpeningClaim Query Y (mconfig (merkleSkels ms))) :=
  match a with
  | (some (o, some p), s) =>
      memoClaims (merkleSkels ms) (finObsR s (zOf o) p) (zOf o) (pathRootsK Y Op ms p).1
        (pathRootsK_length_skels p) (decode (pathRootsK Y Op ms p).2)
  | _ => []

end Defs

section World

open NockvmE2E.Merkle.Phases NockvmE2E.Merkle.BadBound NockvmE2E.Merkle.Derand

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y] [Inhabited Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
  (hpos : 0 < (merkleSkels ms).length) [Inhabited (Fin (merkleSkels ms).length)]
  (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
  (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
  (decode : Op → OpenAll Y (merkleSkels ms)) (A : SuccinctAdversaryK Y Op Query Statement Salt W ms)
abbrev Tr (Y Query : Type) [DecidableEq Y] (ms : MRounds Y) :=
  Transcript (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))
abbrev PObs (Y Op Query Statement Salt : Type) [Finite Y] [DecidableEq Y] [Finite Op] [DecidableEq Op]
    (ms : MRounds Y) :=
  Phases.Obs Query Y (KC Y Op Statement Salt ms)
    (mconfig (merkleSkels ms))
/-- **The instrumented real world W'**: `verifiedFS A` with both observers (reduction memo,
Phases checkpoints), then the honest verification of the memo-pointed claims. Its first
component is BadBound's `realWorld`. -/
def worldW (rounds : ℕ) (A₂ : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
      (OutO Y Op Query Statement Salt W ms)) :
    OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
      (Tr Y Query ms × ((OutO Y Op Query Statement Salt W ms) ×
        PObs Y Op Query Statement Salt ms) ×
        List (AnyEvaluatedOpeningClaim (Fin (merkleSkels ms).length) Query
          (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms)))) :=
  instr (config := mconfig (merkleSkels ms)) (keyRootsK hpos) A₂ >>= fun r =>
    let E := finalExt (Address := MAddress (merkleSkels ms)) (finalRootsK (W := W)) rounds r.1 r.2
    liftV (verifyOpeningClaims model (mkT decode r.1 E)) >>= fun att =>
      pure (({ extractorState := E, attempts := att, terminalSuffix := [] } : Tr Y Query ms), r, att)
theorem realWorld_eq (rounds : ℕ) (A₂ : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
      (OutO Y Op Query Statement Salt W ms)) :
    realWorld (keyRootsK hpos) model (finalRootsK (W := W)) (mkT decode) rounds A₂ =
      (·.1) <$> worldW hpos model decode rounds A₂ := by
  simp [realWorld, worldW, map_bind]
theorem hashQueriesK_liftV {β : Type} (g : OracleComp (Query →ₒ Y) β) :
    simulateQ (hashQueriesK (Y := Y) (Op := Op) (Statement := Statement) (Salt := Salt) (ms := ms)) g =
      liftV (Rc := (KC Y Op Statement Salt ms)) g := by
  unfold liftV
  congr 1


theorem mkT_bits (a : OutO Y Op Query Statement Salt W ms) (E) :
    acceptBits <$> verifyOpeningClaims model (mkT decode a E) = bitsProg model decode a.1 := by
  rcases a with ⟨_ | ⟨o, _ | p⟩, s⟩
  · simp [mkT, bitsProg, verifyOpeningClaims, acceptBits]
  · simp [mkT, bitsProg, verifyOpeningClaims, acceptBits]
  · exact bits_mkClaims_root_only _ model _ _ _ _
theorem fst_instr {α : Type} (A₂ : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) :
    Prod.fst <$> instr (config := mconfig (merkleSkels ms)) (keyRootsK hpos) A₂ = A₂ := by
  refine Derand.observer_run' _ (fun t s => ?_) A₂ _
  rcases t with n | q | k <;> simp [obsImpl, qC, qH, qF]
/-- W' projected to (verified output, hash bits) is `verifiedFS A` followed by the hash check. -/
theorem worldW_proj (rounds : ℕ) :
    (fun x => (x.2.1.1.1, acceptBits x.2.2)) <$> worldW hpos model decode rounds (instrA guards A) =
      verifiedFS guards A >>= fun a => (fun b => (a, b)) <$> liftV (bitsProg model decode a) := by
  have h1 : ∀ (r : (OutO Y Op Query Statement Salt W ms) ×
      PObs Y Op Query Statement Salt ms) (E : ExtractorState (Fin (merkleSkels ms).length) Query
        (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))),
      (fun x : Tr Y Query ms × ((OutO Y Op Query Statement Salt W ms) ×
          PObs Y Op Query Statement Salt ms) × List (AnyEvaluatedOpeningClaim
            (Fin (merkleSkels ms).length) Query (MAddress (merkleSkels ms)) Y
            (mconfig (merkleSkels ms))) => (x.2.1.1.1, acceptBits x.2.2)) <$>
        (liftV (Rc := (KC Y Op Statement Salt ms))
          (verifyOpeningClaims model (mkT decode r.1 E)) >>=
          fun att => pure ((⟨E, att, []⟩ : Tr Y Query ms), r, att)) =
      (fun b => (r.1.1, b)) <$> liftV (bitsProg model decode r.1.1) := by
    intro r E
    rw [← mkT_bits model decode r.1 E]
    simp [liftV, simulateQ_map, Functor.map_map]
  unfold worldW
  rw [map_bind]
  simp only [h1]
  set G : Out1 Y Op Statement Salt W ms → OracleComp (SuccinctSpecK Y Op Query Statement Salt ms)
    (Out1 Y Op Statement Salt W ms × List Bool) := fun a => (fun b => (a, b)) <$>
      liftV (bitsProg model decode a) with hG
  calc _ = ((fun a => a.1.1) <$> instr (config := mconfig (merkleSkels ms)) (keyRootsK hpos)
        (instrA guards A)) >>= G := by rw [bind_map_left]
    _ = _ := by
      rw [show (fun a : (OutO Y Op Query Statement Salt W ms) ×
          PObs Y Op Query Statement Salt ms => a.1.1) <$> instr (config := mconfig (merkleSkels ms))
          (keyRootsK hpos) (instrA guards A) = Prod.fst <$> (Prod.fst <$> instr
            (config := mconfig (merkleSkels ms)) (keyRootsK hpos) (instrA guards A)) by
        simp [Functor.map_map], fst_instr hpos, fst_instrA]
/-- the acceptance event of the succinct experiment -/
def evt (L : Set Statement) : Option ((Statement × Salt) × PathC Y Op ms × W) → Prop
  | none => False
  | some (z, _, _) => z.1 ∉ L
/-- **Real world = W'** on the acceptance event. -/
theorem pr_real_eq (localAccepts : (Statement × Salt) → PathC Y Op ms → Bool) (rounds : ℕ)
    (L : Set Statement) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels ms) model decode) localAccepts A) ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ L] =
    Pr{let x ← randomOracleLoggedRun (worldW hpos model decode rounds (instrA guards A)) ∅}[
      evt L (finOut localAccepts x.1.1.2.1.1.1 (acceptBits x.1.1.2.2))] := by
  have hprog : succinctAcceptedExecutionK guards (merkleCheck (merkleSkels ms) model decode)
      localAccepts A = (fun y => finOut localAccepts y.1 y.2) <$>
        ((fun x => (x.2.1.1.1, acceptBits x.2.2)) <$> worldW hpos model decode rounds (instrA guards A)) := by
    rw [worldW_proj, succinct_eq, map_bind]
    simp only [hashQueriesK_liftV, Functor.map_map]
  rw [hprog, FreshKeys.loggedRun_map, FreshKeys.loggedRun_map, prEvent_map, prEvent_map]
  refine prEvent_congr _ _ _ fun x => ?_
  rcases finOut localAccepts x.1.1.2.1.1.1 (acceptBits x.1.1.2.2) with _ | ⟨z, _, _⟩ <;> rfl


/-! ## The memo / checkpoint invariant (`hmem`) -/

/-- `addEntries` returns an old value or the inserted one, at an inserted key. -/
theorem addEntries_value {V : Type} (z : Statement × Salt) (es : List (List Y × Y)) (v : V)
    (m : (Statement × Salt) × List Y × Y → Option V) (k) (w : V)
    (h : addEntries z es v m k = some w) :
    m k = some w ∨ (m k = none ∧ k.1 = z ∧ k.2 ∈ es ∧ w = v) := by
  induction es generalizing m with
  | nil => exact Or.inl h
  | cons e es ih =>
    rcases ih _ h with h1 | ⟨h1, h2, h3, h4⟩
    · dsimp only [memoAdd] at h1
      split_ifs at h1 with hk
      · subst hk
        cases hm : m (z, e) with
        | none => rw [hm] at h1; exact Or.inr ⟨rfl, rfl, List.mem_cons_self .., by simpa using h1.symm⟩
        | some u => rw [hm] at h1; exact Or.inl (by simpa using h1)
      · exact Or.inl h1
    · have : m k = none := by
        dsimp only [memoAdd] at h1; split_ifs at h1 with hk
        · cases hm : m k <;> simp_all [Option.or]
        · exact h1
      exact Or.inr ⟨this, h2, List.mem_cons_of_mem _ h3, h4⟩
theorem toLog_append (l : List (Query × Y)) (q : Query) (y : Y) :
    toLog (l ++ [(q, y)]) = toLog l ++ [⟨q, y⟩] := by
  simp [toLog]
/-- the joint invariant of the two observers -/
def JInv (s : Reduction.Obs Query Statement Salt Y) (ob : PObs Y Op Query Statement Salt ms) : Prop :=
  toLog s.log = ob.hlog ∧
  (∀ z pre root n lg, s.memo (z, pre, root) = some (n, lg) →
    ∀ h : pre.length < (merkleSkels ms).length,
      (⟨⟨pre.length, h⟩, { root := root, cumulativeLog := toLog lg }⟩ :
        AnyCheckpoint _ Query (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))) ∈
        ob.ext.checkpoints) ∧
  (∀ d, (ob.seen d).isSome → ∀ e ∈ keyEntries ms [] d, s.memo (d.input, e) ≠ none)
theorem recQ_mem (h : Phases.Log Query Y) (ext : ExtractorState (Fin (merkleSkels ms).length) Query
    (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms)))
    (q : List (Fin (merkleSkels ms).length × Y)) (c) :
    c ∈ (recQ h ext q).checkpoints ↔
      c ∈ ext.checkpoints ∨ ∃ x ∈ q, c = ⟨x.1, { root := x.2, cumulativeLog := h }⟩ := by
  induction q generalizing ext with
  | nil => simp [recQ]
  | cons x qs ih =>
    have := ih (ext.recordCumulative x.1 h x.2)
    simp only [recQ, List.foldl_cons] at this ⊢
    rw [this, ExtractorState.recordCumulative_checkpoints]
    simp only [List.mem_append, List.mem_cons, exists_eq_or_imp]
    tauto
theorem fresh_mem (ob : PObs Y Op Query Statement Salt ms)
    (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) (v : d.Challenge) (c) :
    c ∈ (ob.fresh (keyRootsK hpos) d v).ext.checkpoints ↔
      c ∈ ob.ext.checkpoints ∨ ∃ x ∈ keyRootsK hpos d, c = ⟨x.1, { root := x.2, cumulativeLog := ob.hlog }⟩ := by
  unfold Phases.Obs.fresh
  rcases h : keyRootsK hpos d with _ | ⟨x, xs⟩
  · simp
  · simp only [Obs.stop_ext]
    rw [← h, recQ_mem, h]
theorem fresh_hlog (ob : PObs Y Op Query Statement Salt ms)
    (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) (v : d.Challenge) :
    (ob.fresh (keyRootsK hpos) d v).hlog = ob.hlog := by
  unfold Phases.Obs.fresh
  rcases keyRootsK hpos d with _ | ⟨x, xs⟩ <;> rfl
theorem jinv_hash (s : Reduction.Obs Query Statement Salt Y) (ob : PObs Y Op Query Statement Salt ms)
    (h : JInv s ob) (q : Query) (y : Y) :
    JInv (obsStep Y Op ms s (.inl q) y) (ob.hash q y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  simp [obsStep, Phases.Obs.hash, toLog_append, h1]
theorem jinv_fs (s : Reduction.Obs Query Statement Salt Y) (ob : PObs Y Op Query Statement Salt ms)
    (h : JInv s ob) (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) (v : d.Challenge) :
    JInv (obsStep Y Op ms s (.inr d) v) (ob.fs (keyRootsK hpos) d v) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hext := obsStep_extends (Op := Op) (ms := ms) s (.inr d) v
  rcases hs : ob.seen.toFn d with _ | w
  · rw [Phases.Obs.fs_of_none _ _ _ _ hs]
    refine ⟨by rw [fresh_hlog]; exact h1, ?_, ?_⟩
    · intro z pre root n lg hm hl
      rw [fresh_mem]
      rcases addEntries_value _ _ _ _ _ _ hm with hm' | ⟨_, hz, he, hv⟩
      · exact Or.inl (h2 z pre root n lg hm' hl)
      · refine Or.inr ⟨(tagOf hpos pre.length, root), List.mem_map.mpr ⟨(pre, root), he, rfl⟩, ?_⟩
        obtain ⟨-, rfl⟩ := Prod.mk.inj hv
        have ht : tagOf hpos pre.length = ⟨pre.length, hl⟩ := dite_eq_left hl
        simp only [h1]
        rw [ht]
    · intro d' hd' e he
      rw [Phases.Obs.fresh_seen, QueryCache.isSome_cacheQuery_apply_iff] at hd'
      rcases hd' with rfl | hd'
      · exact obsStep_defined (Op := Op) (ms := ms) s d' v e he
      · intro h0
        exact h3 d' hd' e he (by
          cases hm : s.memo (d'.input, e) with
          | none => rfl
          | some u => rw [hext _ _ hm] at h0; cases h0)
  · rw [Phases.Obs.fs_of_some _ _ _ _ _ hs]
    have hd : (ob.seen d).isSome := by
      rw [show ob.seen d = ob.seen.toFn d from rfl, hs]; rfl
    refine ⟨h1, ?_, ?_⟩
    · intro z pre root n lg hm hl
      rcases addEntries_value _ _ _ _ _ _ hm with hm' | ⟨hn, hz, he, _⟩
      · exact h2 z pre root n lg hm' hl
      · exact absurd (by rw [← hz]; exact hn) (h3 d hd _ he)
    · intro d' hd' e he h0
      exact h3 d' hd' e he (by
        cases hm : s.memo (d'.input, e) with
        | none => rfl
        | some u => rw [hext _ _ hm] at h0; cases h0)


theorem jinv_run {α : Type} (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) :
    ∀ (s : Reduction.Obs Query Statement Salt Y) (ob : PObs Y Op Query Statement Salt ms),
      JInv s ob → ∀ r ∈ support ((simulateQ (obsImpl (config := mconfig (merkleSkels ms))
        (keyRootsK hpos)) ((simulateQ obsR oa).run s)).run ob), JInv r.1.2 r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s ob h r hr
    simp at hr
    subst hr
    exact h
  | query_bind t k ih =>
    intro s ob h r hr
    rw [obsR_run_bind] at hr
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨p, hp, hr⟩ := hr
    rcases t with n | q | d
    · rw [obs_coin] at hp
      simp [qC] at hp
      obtain ⟨u, rfl⟩ := hp
      exact ih _ _ _ h r hr
    · rw [obs_hash] at hp
      simp [qH] at hp
      obtain ⟨y, -, rfl⟩ := hp
      exact ih _ _ _ (jinv_hash s ob h q y) r hr
    · rw [obs_fs] at hp
      simp [qF] at hp
      obtain ⟨v, -, rfl⟩ := hp
      exact ih _ _ _ (jinv_fs hpos s ob h d v) r hr


theorem padExt_mem (m : ℕ) (ext : ExtractorState (Fin (merkleSkels ms).length) Query
    (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))) (c)
    (h : c ∈ ext.checkpoints) : c ∈ (padExt m ext).checkpoints := by
  induction m generalizing ext with
  | zero => exact h
  | succ m ih => exact ih _ (by simp [h])
theorem ckpt_tag_congr {t t' : Fin (merkleSkels ms).length} (ht : t = t') (root : Y)
    (lg : MerkleTreeExtractor.QueryLog Query Y)
    (X : List (AnyCheckpoint _ Query (MAddress (merkleSkels ms)) Y (mconfig (merkleSkels ms))))
    (h : (⟨t, { root := root, cumulativeLog := lg }⟩ : AnyCheckpoint _ Query _ Y _) ∈ X) :
    (⟨t', { root := root, cumulativeLog := lg }⟩ : AnyCheckpoint _ Query _ Y _) ∈ X := by
  subst ht; exact h
theorem jinv_init : JInv (Op := Op) (ms := ms) (Reduction.Obs.init : Reduction.Obs Query Statement Salt Y)
    (Phases.Obs.init : PObs Y Op Query Statement Salt ms) := by
  refine ⟨rfl, fun _ _ _ _ _ h => by simp [Reduction.Obs.init] at h, fun d hd => ?_⟩
  simp [Phases.Obs.init] at hd
/-- **`hmem`**: every memo-pointed terminal claim names a checkpoint of the final extractor state. -/
theorem hmem_of_support (rounds : ℕ) (r : (OutO Y Op Query Statement Salt W ms) ×
      PObs Y Op Query Statement Salt ms)
    (hr : r ∈ support (instr (config := mconfig (merkleSkels ms)) (keyRootsK hpos) (instrA guards A))) :
    ∀ c ∈ mkT decode r.1 (finalExt (Address := MAddress (merkleSkels ms)) (finalRootsK (W := W))
        rounds r.1 r.2),
      (⟨c.tag, c.checkpoint⟩ : AnyCheckpoint _ Query _ Y _) ∈
        (finalExt (Address := MAddress (merkleSkels ms)) (finalRootsK (W := W)) rounds r.1 r.2).checkpoints := by
  obtain ⟨⟨a, s⟩, ob⟩ := r
  have hJ := jinv_run hpos _ _ _ jinv_init _ hr
  obtain ⟨h1, h2, -⟩ := hJ
  rcases a with _ | ⟨o, _ | p⟩
  · simp [mkT]
  · simp [mkT]
  intro c hc
  simp only [mkT, memoClaims, mkClaims, List.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  refine padExt_mem _ _ _ ?_
  have hne : finalRootsK (W := W) ((some (o, some p), s) : Out1 Y Op Statement Salt W ms × _) =
      (finalNE (finalRootsK (W := W)) ((some (o, some p), s) : Out1 Y Op Statement Salt W ms × _)).1 ::
      (finalNE (finalRootsK (W := W)) ((some (o, some p), s) : Out1 Y Op Statement Salt W ms × _)).2 := by
    unfold finalNE
    rcases h : finalRootsK (W := W) ((some (o, some p), s) : Out1 Y Op Statement Salt W ms × _) with _ | ⟨x, xs⟩
    · have := congrArg List.length h
      simp only [finalRootsK, pathCkpts, List.length_ofFn, List.length_nil] at this
      omega
    · rfl
  simp only [Phases.finalObs, Phases.Obs.stop_ext]
  rw [← hne, recQ_mem]
  set roots := (pathRootsK Y Op ms p).1
  have hlen : roots.length = (merkleSkels ms).length := pathRootsK_length_skels p
  have hjl : (roots.take j).length = j := by rw [List.length_take]; omega
  simp only [memoLog, finObsR]
  cases hm : s.memo (zOf o, roots.take j, roots.get (j.cast hlen.symm)) with
  | some w =>
    obtain ⟨n, lg⟩ := w
    rw [Reduction.addEntries_extends _ _ _ _ _ _ hm]
    exact Or.inl (ckpt_tag_congr (Fin.ext hjl) _ _ _ (h2 _ _ _ n lg hm (by omega)))
  | none =>
    have hmem : (roots.take j, roots.get (j.cast hlen.symm)) ∈ pathEntries p :=
      List.mem_ofFn.mpr ⟨j, rfl⟩
    have hd := Reduction.addEntries_defined (zOf o) (pathEntries p) (s.nck, s.log) s.memo _ hmem
    cases hv : addEntries (zOf o) (pathEntries p) (s.nck, s.log) s.memo
        (zOf o, roots.take j, roots.get (j.cast hlen.symm)) with
    | none => exact absurd hv hd
    | some w =>
      rcases addEntries_value _ _ _ _ _ _ hv with hw | ⟨-, -, -, rfl⟩
      · rw [hm] at hw; cases hw
      · refine Or.inr ⟨(j, rootAt p j), List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
        simp only [h1]
        rfl


/-! ## Good on the support of W' -/

theorem loggedRun_out_mem {D : Type} {R : D → Type} [DecidableEq D] [∀ d, SampleableType (R d)]
    {α : Type} (oa : OracleComp (unifSpec + ofFn R) α) (c : (ofFn R).QueryCache)
    (y : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache) (hy : y ∈ support (randomOracleLoggedRun oa c)) :
    y.1.1 ∈ support oa := by
  have h1 : (y.1.1, y.2) ∈ support ((simulateQ (ofFn R).romImpl oa).run c) := by
    rw [← randomOracleLoggedRun_project, support_map]; exact ⟨y, hy, rfl⟩
  refine support_simulateQ_run'_subset (n := ProbComp) (ofFn R).romImpl oa c ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨_, h1, rfl⟩
/-- the reduction-side good event: A's verified output, its statement outside `L`, and the paired
check accepts the memo words of the end-of-run memo -/
def goodB (L : Set Statement)
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message) :
    OutO Y Op Query Statement Salt W ms → Prop
  | (some (o, some p), s) => o.1 ∉ L ∧
      pairAccepts Y ms accepts (zOf o)
        (pairPath (fun r hr => memoWords ext (finObsR s (zOf o) p) r hr (zOf o)) ms [] p) = true
  | _ => False
/-- **Good on the support of W'**: an accepted run off the bad event is good for the reduction. -/
theorem good_of_support (y0 : Y)
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : (Statement × Salt) → PathC Y Op ms → Bool)
    (hlocal : QueryOnly ms decode accepts localAccepts) (rounds : ℕ) (L : Set Statement)
    (x) (hx : x ∈ support (randomOracleLoggedRun (worldW hpos model decode rounds (instrA guards A)) ∅))
    (hE : evt L (finOut localAccepts x.1.1.2.1.1.1 (acceptBits x.1.1.2.2)))
    (hno : ¬ Transcript.HasAnyCheckpointExtractionDisagreement model x.1.1.1) :
    goodB L accepts (NonVacuous.extTree ms model.view y0) x.1.1.2.1.1 := by
  have hx' := loggedRun_out_mem _ _ x hx
  unfold worldW at hx'
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx'
  obtain ⟨r, hr, att, hatt, hxe⟩ := hx'
  rw [hxe] at hE hno ⊢
  obtain ⟨⟨a, s⟩, ob⟩ := r
  rcases a with _ | ⟨o, _ | p⟩
  · exact hE.elim
  · exact hE.elim
  simp only [finOut] at hE
  split_ifs at hE with hok
  swap
  · exact hE.elim
  simp only [evt] at hE
  simp only [Bool.and_eq_true] at hok
  refine ⟨hE, ?_⟩
  have hatt' := support_simulateQ_subset _ _ hatt
  refine good_accepts_of_not_any model decode y0 _ (NonVacuous.extTree_isTree ms model.view y0)
    (finObsR s (zOf o) p) (zOf o) p _ att [] hatt' ?_ hno
    (hmem_of_support hpos guards decode A rounds _ hr) accepts localAccepts hlocal hok.2
  intro c hc
  have := List.all_eq_true.mp hok.1 c.2.accepted (by simp only [acceptBits, List.mem_map]; exact ⟨c, hc, rfl⟩)
  simpa using this


/-! ## The bad event of W' (BadBound) -/

theorem inst_rfam : (fun d => succinctRange_sampleable Y Op Query Statement Salt ms d) =
    (fun d => instSampRfam (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms)) d) := by
  funext d; cases d <;> rfl
theorem keyEntries_length : ∀ (ms : MRounds Y) (pre : List Y)
    (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)),
    (keyEntries ms pre d).length ≤ merkleCount Y ms
  | [], _, _ => by simp [keyEntries]
  | ⟨_, .clear⟩ :: _, _, .inl _ => by simp [keyEntries]
  | ⟨_, .clear⟩ :: ms, pre, .inr (_, _, k) => keyEntries_length ms pre k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, _, .inl _ => by simp [keyEntries, merkleCount]
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, pre, .inr (root, _, k) => by
      simp only [keyEntries, merkleCount, List.length_cons]
      exact Nat.succ_le_succ (keyEntries_length ms _ k)
/-- **The bad event of W'** has probability at most VCVio's multi-checkpoint ROM error. -/
theorem pr_bad_le (Q_FS Q_H V P : ℕ)
    (hQ : IsQueryBoundP (instrA guards A) (isHashQuery (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms))) Q_H)
    (hFS : FsBound (Q := Query) (Y := Y)
      (∅ : (ofFn (KC Y Op Statement Salt ms)).QueryCache)
      Q_FS (instrA guards A))
    (hterm : ∀ (roots : List Y) (h : roots.length = (merkleSkels ms).length) (op : Op)
      (logs : Fin (merkleSkels ms).length → MerkleTreeExtractor.QueryLog Query Y),
      claimsQueryCount (mkClaims (merkleSkels ms) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels ms)).nodeBudget tag ≤ P) :
    Pr{let x ← randomOracleLoggedRun (worldW hpos model decode
        ((merkleSkels ms).length * (Q_FS + 1)) (instrA guards A)) ∅}[
      Transcript.HasAnyCheckpointExtractionDisagreement model x.1.1.1] ≤
    (multiCheckpointROMErrorNumerator (((merkleSkels ms).length * (Q_FS + 1)) * P)
      ((merkleSkels ms).length * (Q_FS + 1)) V Q_H : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  have hk : ∀ key, (keyRootsK hpos key).length ≤ (merkleSkels ms).length := fun key => by
    simp only [keyRootsK, List.length_map, merkleSkels_length]
    exact keyEntries_length (Statement := Statement) (Salt := Salt) (Op := Op) ms [] key
  have hfin : ∀ a : OutO Y Op Query Statement Salt W ms,
      (finalRootsK a).length ≤ (merkleSkels ms).length := by
    rintro ⟨_ | ⟨o, _ | p⟩, s⟩ <;> simp [finalRootsK, pathCkpts]
  have hterm' : ∀ (a : OutO Y Op Query Statement Salt W ms) E,
      claimsQueryCount (mkT decode a E) ≤ V := by
    rintro ⟨_ | ⟨o, _ | p⟩, s⟩ E
    · simp [mkT, claimsQueryCount]
    · simp [mkT, claimsQueryCount]
    · exact hterm _ (pathRootsK_length_skels p) _ _
  have h := bad_real_le_of_bounds (keyRootsK hpos) (rd := id)
    (C := (KC Y Op Statement Salt ms))
    (e := fun k => Equiv.refl _) model finalRootsK (mkT decode) (instrA guards A)
    (merkleSkels ms).length Q_FS Q_H V P hpos hk hfin hQ hFS hterm' hconfig
  rw [realWorld_eq, FreshKeys.loggedRun_map, Functor.map_map, prEvent_map] at h
  rw [inst_rfam]
  exact h


/-! ## Splitting W' on the bad event, and the projection to the instrumented A₁ -/

theorem pr_world_split (y0 : Y)
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : (Statement × Salt) → PathC Y Op ms → Bool)
    (hlocal : QueryOnly ms decode accepts localAccepts) (rounds : ℕ) (L : Set Statement) :
    Pr{let x ← randomOracleLoggedRun (worldW hpos model decode rounds (instrA guards A)) ∅}[
      evt L (finOut localAccepts x.1.1.2.1.1.1 (acceptBits x.1.1.2.2))] ≤
    Pr{let y ← randomOracleLoggedRun (instrA guards A) ∅}[
      goodB L accepts (NonVacuous.extTree ms model.view y0) y.1.1] +
    Pr{let x ← randomOracleLoggedRun (worldW hpos model decode rounds (instrA guards A)) ∅}[
      Transcript.HasAnyCheckpointExtractionDisagreement model x.1.1.1] := by
  refine (prEvent_mono_of_support _ _ (fun x => goodB L accepts (NonVacuous.extTree ms model.view y0)
    x.1.1.2.1.1 ∨ Transcript.HasAnyCheckpointExtractionDisagreement model x.1.1.1) fun x hx hE => ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  · by_cases hb : Transcript.HasAnyCheckpointExtractionDisagreement model x.1.1.1
    · exact Or.inr hb
    · exact Or.inl (good_of_support hpos guards model decode A y0 accepts localAccepts hlocal rounds L x hx hE hb)
  · unfold worldW
    rw [randomOracleLoggedRun_bind]
    refine (prEvent_bind_le_prEvent_of_support _ _
      (fun q => goodB L accepts (NonVacuous.extTree ms model.view y0) q.1.1.1) _ fun q _ hq => ?_).trans
      (le_of_eq ?_)
    · refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy hg => hq ?_
      rw [support_map] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      have hw' := loggedRun_out_mem _ _ w hw
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw'
      obtain ⟨att, -, hwe⟩ := hw'
      simp only [hwe] at hg
      exact hg
    · conv_rhs => rw [← fst_instr hpos (instrA guards A), FreshKeys.loggedRun_map]
      rw [prEvent_map]

/-! ## Query bounds of the instrumented A₁ -/

theorem fs_hash_zero {α : Type}
    (V : OracleComp (oracleSpec (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) α) :
    IsQueryBoundP (simulateQ (fsQueriesK (Y := Y) (Op := Op) (Query := Query) (ms := ms)) V)
      (isHashQuery (Q := Query) (Y := Y)
        (Rc := (KC Y Op Statement Salt ms))) 0 := by
  induction V using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind d k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    show IsQueryBoundP ((liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inr (.inr d))) :
      OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) _) >>= fun x => simulateQ fsQueriesK (k x)) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [isHashQuery]), fun u => by simpa [isHashQuery] using ih u⟩
theorem hQ_instrA (Q_H : ℕ) (hH : IsQueryBoundP A (isHashQuery (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms))) Q_H) :
    IsQueryBoundP (instrA guards A) (isHashQuery (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms))) Q_H := by
  have hv : IsQueryBoundP (verifiedFS guards A) (isHashQuery (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms))) Q_H := by
    have := isQueryBoundP_bind (m := 0) hH (ob := fun r => match r with
      | none => pure none
      | some o => (fun p? => some (o, p?)) <$>
          simulateQ fsQueriesK (publicStoppedVerify _ guards (o.1, o.2.1.1) o.2.1.2)) fun r _ => by
        rcases r with _ | o
        · trivial
        · exact (isQueryBoundP_map_iff _ _ _).mpr (fs_hash_zero _)
    simpa [verifiedFS] using this
  refine IsQueryBoundP.simulateQ_run_StateT_of_step hv (fun t s => ?_) _
  simp only [obsR, StateT.run_mk]
  rw [isQueryBoundP_map_iff]
  rw [show (liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) :
      OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) _) =
      liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query t) >>= pure from (bind_pure _).symm,
    isQueryBoundP_query_bind_iff]
  by_cases h : isHashQuery (Q := Query) (Y := Y)
      (Rc := (KC Y Op Statement Salt ms)) t
  · simp only [h, ite_true]; exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩
  · simp only [h, ite_false]; exact ⟨Or.inl not_false, fun _ => trivial⟩
theorem fsBound_obsR {α : Type} {seen} {n : ℕ}
    {oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α}
    (h : FsBound (Q := Query) (Y := Y) seen n oa) :
    ∀ s : Reduction.Obs Query Statement Salt Y, FsBound seen n ((simulateQ obsR oa).run s) := by
  induction h with
  | pure a seen n => intro s; exact FsBound.pure _ _ _
  | coin c k seen n _ ih =>
    intro s
    rw [show (OracleComp.queryBind (Sum.inl c) k : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) =
      liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inl c)) >>= k from rfl, obsR_run_bind]
    exact FsBound.coin c _ seen n fun u => ih u _
  | hash q k seen n _ ih =>
    intro s
    rw [show (OracleComp.queryBind (Sum.inr (Sum.inl q)) k : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) =
      liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inr (.inl q))) >>= k from rfl, obsR_run_bind]
    exact FsBound.hash q _ seen n fun u => ih u _
  | fs key k seen n _ hn _ ih1 ih2 =>
    intro s
    rw [show (OracleComp.queryBind (Sum.inr (Sum.inr key)) k : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) =
      liftM ((SuccinctSpecK Y Op Query Statement Salt ms).query (.inr (.inr key))) >>= k from rfl, obsR_run_bind]
    exact FsBound.fs key _ seen n (fun v hv => ih1 v hv _) hn (fun v hv => ih2 v hv _)

end World

end NockvmE2E.Merkle.SoundnessWorld
