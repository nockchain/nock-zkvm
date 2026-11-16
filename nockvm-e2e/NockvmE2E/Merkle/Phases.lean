/-
Merkle (B) file 7: the VCVio phase adversary `advOf σ` ("Phases (D2)"). Generic over Derand's parameters.
-/
import NockvmE2E.Merkle.Derand
import NockvmE2E.Merkle.Opening
import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.StrongBound

open OracleComp OracleSpec MerkleTreeMultiExtractability
open NockvmE2E.Merkle.Derand

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Phases

section Defs

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]

/-- the hash log type of VCVio's extractor -/
abbrev Log (Q Y : Type) := MerkleTreeExtractor.QueryLog Q Y

/-- observer state: cumulative hash log, the checkpoints recorded at the root-bearing fresh FS keys,
and the FS cache (to decide freshness). -/
structure Obs (Q Y : Type) {K : Type} (Rc : K → Type) {Cfg Address : Type}
    (config : Configuration Cfg Address) where
  hlog : Log Q Y
  ext : ExtractorState Cfg Q Address Y config
  seen : (ofFn Rc).QueryCache

def Obs.init : Obs Q Y Rc config := ⟨[], ExtractorState.empty, ∅⟩

/-- record one hash query -/
def Obs.hash (ob : Obs Q Y Rc config) (q : Q) (y : Y) : Obs Q Y Rc config :=
  { ob with hlog := ob.hlog ++ [⟨q, y⟩] }

/-- record the roots `hd :: tl` of a stop, all against the current cumulative log -/
def Obs.stop (ob : Obs Q Y Rc config) (hd : Cfg × Y) (tl : List (Cfg × Y)) : Obs Q Y Rc config :=
  { ob with ext := (hd :: tl).foldl (fun e x => e.recordCumulative x.1 ob.hlog x.2) ob.ext }

/-- a fresh FS key `key` answered `v`: cache it, and record its roots if it has any -/
def Obs.fresh (keyRoots : K → List (Cfg × Y)) (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    Obs Q Y Rc config :=
  let ob' : Obs Q Y Rc config := { ob with seen := ob.seen.cacheQuery key v }
  match keyRoots key with
  | [] => ob'
  | x :: xs => ob'.stop x xs

/-- observer step on an FS answer (idempotent on cached keys) -/
def Obs.fs (keyRoots : K → List (Cfg × Y)) (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    Obs Q Y Rc config :=
  match ob.seen key with
  | some _ => ob
  | none => ob.fresh keyRoots key v

/-- coin query of the real program -/
def qC (n : ℕ) : OracleComp (realSpec Q Y Rc) ((realSpec Q Y Rc).Range (.inl n)) :=
  liftM ((realSpec Q Y Rc).query (.inl n))

/-- hash query of the real program -/
def qH (q : Q) : OracleComp (realSpec Q Y Rc) ((realSpec Q Y Rc).Range (.inr (.inl q))) :=
  liftM ((realSpec Q Y Rc).query (.inr (.inl q)))

/-- FS query of the real program -/
def qF (k : K) : OracleComp (realSpec Q Y Rc) ((realSpec Q Y Rc).Range (.inr (.inr k))) :=
  liftM ((realSpec Q Y Rc).query (.inr (.inr k)))

theorem simulateQ_qC {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (realSpec Q Y Rc) m) (n : ℕ) : simulateQ impl (qC n) = impl (.inl n) :=
  simulateQ_spec_query _ _

theorem simulateQ_qH {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (realSpec Q Y Rc) m) (q : Q) : simulateQ impl (qH q) = impl (.inr (.inl q)) :=
  simulateQ_spec_query _ _

theorem simulateQ_qF {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (realSpec Q Y Rc) m) (k : K) : simulateQ impl (qF k) = impl (.inr (.inr k)) :=
  simulateQ_spec_query _ _

/-- cast of a hash answer to the dependent range of `realSpec` (defeq, but not reducibly so) -/
def ofH (q : Q) (y : Y) : (realSpec Q Y Rc).Range (.inr (.inl q)) := y

/-- cast of an FS answer to the dependent range of `realSpec` -/
def ofF (k : K) (v : Rc k) : (realSpec Q Y Rc).Range (.inr (.inr k)) := v

/-- inverse casts -/
def toH (q : Q) (y : (realSpec Q Y Rc).Range (.inr (.inl q))) : Y := y
def toF (k : K) (v : (realSpec Q Y Rc).Range (.inr (.inr k))) : Rc k := v

/-- the observer: every query is forwarded unchanged and recorded -/
def obsImpl (keyRoots : K → List (Cfg × Y)) :
    QueryImpl (realSpec Q Y Rc) (StateT (Obs Q Y Rc config) (OracleComp (realSpec Q Y Rc))) :=
  fun t => match t with
  | .inl n => StateT.mk fun ob => qC n >>= fun u => pure (u, ob)
  | .inr (.inl q) => StateT.mk fun ob => qH q >>= fun y => pure (y, ob.hash q (toH q y))
  | .inr (.inr k) => StateT.mk fun ob => qF k >>= fun v => pure (v, ob.fs keyRoots k (toF k v))

/-- the instrumented real program -/
def instr (keyRoots : K → List (Cfg × Y)) {α : Type} (A : OracleComp (realSpec Q Y Rc) α) :
    OracleComp (realSpec Q Y Rc) (α × Obs Q Y Rc config) :=
  (simulateQ (obsImpl keyRoots) A).run Obs.init

end Defs

section Run1

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]
variable [∀ j, SampleableType (C j)] [∀ j, Nonempty (C j)]

/-- pop a coin from the seed (default when exhausted): the pure form of `sodImpl` on coins -/
noncomputable def popCoin (sd : QuerySeed (progSpec Q Y C)) (c : (coinSpec C).Domain) :
    (coinSpec C).Range c × QuerySeed (progSpec Q Y C) :=
  match sd (.inl c) with
  | u :: us => (u, sd.update (.inl c) us)
  | [] => (dflt c, sd)

/-- result of one phase of the real program: it stopped at a fresh root-bearing FS key
(already answered), or finished -/
inductive Stop (Q Y : Type) {K : Type} (Rc : K → Type) {J : Type} (C : J → Type) (Cfg : Type)
    (α : Type) : Type
  | fresh (hd : Cfg × Y) (tl : List (Cfg × Y)) (A' : OracleComp (realSpec Q Y Rc) α)
      (seen : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)) (seg : Log Q Y)
  | done (a : α) (seen : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)) (seg : Log Q Y)

def Stop.consLog {α : Type} (s : (_ : Q) × Y) : Stop Q Y Rc C Cfg α → Stop Q Y Rc C Cfg α
  | .fresh hd tl A' seen sd seg => .fresh hd tl A' seen sd (s :: seg)
  | .done a seen sd seg => .done a seen sd (s :: seg)

variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)

/-- `stepUntilFS`: run the real program (coins from the seed, raw hash queries, FS cache) up to the
next fresh root-bearing FS key, or to the end. Structural recursion on the free monad. -/
noncomputable def run1 {α : Type} :
    OracleComp (realSpec Q Y Rc) α → (ofFn Rc).QueryCache → QuerySeed (progSpec Q Y C) →
    OracleComp (hashSpec Q Y) (Stop Q Y Rc C Cfg α)
  | .pure a, seen, sd => pure (.done a seen sd [])
  | .queryBind (.inl n) k, seen, sd =>
      run1 (k (popCoin (Y := Y) sd (.inl n)).1) seen (popCoin (Y := Y) sd (.inl n)).2
  | .queryBind (.inr (.inl q)) k, seen, sd => do
      let y ← (liftM ((hashSpec Q Y).query q) : OracleComp (hashSpec Q Y) Y)
      Stop.consLog ⟨q, y⟩ <$> run1 (k (ofH q y)) seen sd
  | .queryBind (.inr (.inr key)) k, seen, sd =>
      match seen key with
      | some v => run1 (k (ofF key v)) seen sd
      | none =>
          match keyRoots key with
          | [] => run1 (k (ofF key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)))
                    (seen.cacheQuery key (e key (popCoin (Y := Y) sd (.inr (rd key))).1))
                    (popCoin (Y := Y) sd (.inr (rd key))).2
          | x :: xs => pure (.fresh x xs (k (ofF key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)))
                    (seen.cacheQuery key (e key (popCoin (Y := Y) sd (.inr (rd key))).1))
                    (popCoin (Y := Y) sd (.inr (rd key))).2 [])

/-- big-step reference run of the real program with observer and seed threaded -/
noncomputable def bs {α : Type} :
    OracleComp (realSpec Q Y Rc) α → Obs Q Y Rc config → QuerySeed (progSpec Q Y C) →
    OracleComp (hashSpec Q Y) (α × Obs Q Y Rc config × QuerySeed (progSpec Q Y C))
  | .pure a, ob, sd => pure (a, ob, sd)
  | .queryBind (.inl n) k, ob, sd =>
      bs (k (popCoin (Y := Y) sd (.inl n)).1) ob (popCoin (Y := Y) sd (.inl n)).2
  | .queryBind (.inr (.inl q)) k, ob, sd => do
      let y ← (liftM ((hashSpec Q Y).query q) : OracleComp (hashSpec Q Y) Y)
      bs (k (ofH q y)) (ob.hash q y) sd
  | .queryBind (.inr (.inr key)) k, ob, sd =>
      match ob.seen key with
      | some v => bs (k (ofF key v)) ob sd
      | none =>
          bs (k (ofF key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)))
            (ob.fresh keyRoots key (e key (popCoin (Y := Y) sd (.inr (rd key))).1))
            (popCoin (Y := Y) sd (.inr (rd key))).2

/-- continue `bs` after a stop of `run1` -/
noncomputable def resume {α : Type} (ob : Obs Q Y Rc config) :
    Stop Q Y Rc C Cfg α → OracleComp (hashSpec Q Y) (α × Obs Q Y Rc config × QuerySeed (progSpec Q Y C))
  | .fresh hd tl A' seen sd seg =>
      bs keyRoots rd e A' (({ ob with hlog := ob.hlog ++ seg, seen := seen } : Obs Q Y Rc config).stop hd tl) sd
  | .done a seen sd seg => pure (a, { ob with hlog := ob.hlog ++ seg, seen := seen }, sd)

theorem resume_consLog {α : Type} (ob : Obs Q Y Rc config) (s : (_ : Q) × Y)
    (r : Stop Q Y Rc C Cfg α) :
    resume keyRoots rd e ob (r.consLog s) = resume keyRoots rd e (ob.hash s.1 s.2) r := by
  cases r <;> simp [Stop.consLog, resume, Obs.hash]

/-- `bs` is `run1` followed by `resume` -/
theorem bs_eq_run1 {α : Type} (A : OracleComp (realSpec Q Y Rc) α) :
    ∀ (ob : Obs Q Y Rc config) (sd : QuerySeed (progSpec Q Y C)),
    bs keyRoots rd e A ob sd = run1 keyRoots rd e A ob.seen sd >>= resume keyRoots rd e ob := by
  induction A with
  | pure a => intro ob sd; simp [bs, run1, resume]
  | queryBind t k ih =>
    intro ob sd
    rcases t with n | q | key
    · simp only [bs, run1]; exact ih _ _ _
    · simp only [bs, run1, bind_assoc, map_eq_bind_pure_comp, pure_bind]
      refine bind_congr fun y => ?_
      rw [ih (ofH q y) (ob.hash q y) sd]
      simp [resume_consLog, Obs.hash]
    · simp only [bs, run1]
      rcases hs : ob.seen key with _ | v
      · simp only [hs]
        rcases hk : keyRoots key with _ | ⟨x, xs⟩
        · simp only [Obs.fresh, hk]
          exact ih _ _ _
        · simp [Obs.fresh, hk, resume]
      · simp only [hs]
        exact ih _ _ _

def Stop.seg {α : Type} : Stop Q Y Rc C Cfg α → Log Q Y
  | .fresh _ _ _ _ _ seg => seg
  | .done _ _ _ seg => seg

/-- the VCVio phase log of one `run1` phase is its own hash segment -/
theorem run1_withQueryLog {α : Type} (A : OracleComp (realSpec Q Y Rc) α) :
    ∀ (seen : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)),
    (run1 keyRoots rd e A seen sd).withQueryLog =
      (fun r => (r, r.seg)) <$> run1 keyRoots rd e A seen sd := by
  induction A with
  | pure a => intro seen sd; simp [run1, Stop.seg]
  | queryBind t k ih =>
    intro seen sd
    rcases t with n | q | key
    · simp only [run1]; exact ih _ _ _
    · simp only [run1, withQueryLog_bind, withQueryLog_query, bind_assoc, map_eq_bind_pure_comp,
        pure_bind]
      refine bind_congr fun y => ?_
      rw [ih (ofH q y) seen sd]
      simp [Stop.consLog, Stop.seg]
      refine congrArg (· <$> run1 keyRoots rd e (k (ofH q y)) seen sd) (funext fun r => ?_)
      cases r <;> rfl
    · simp only [run1]
      rcases hs : seen key with _ | v
      · simp only
        rcases hk : keyRoots key with _ | ⟨x, xs⟩
        · exact ih _ _ _
        · simp [Stop.seg]
      · exact ih _ _ _

end Run1

section L1

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]
variable [∀ j, SampleableType (C j)] [∀ j, Finite (C j)] [∀ j, Nonempty (C j)]
variable [SampleableType Y] [Finite Y] [Nonempty Y]
variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)

theorem sodImpl_coin (c : (coinSpec C).Domain) (sd : QuerySeed (progSpec Q Y C)) :
    (sodImpl (Q := Q) (Y := Y) (C := C) (.inl c)).run sd = pure (popCoin (Y := Y) sd c) := by
  simp only [sodImpl, popCoin]
  change (match sd (.inl c) with
    | u :: us => (pure (u, sd.update (.inl c) us) : OracleComp (hashSpec Q Y) _)
    | [] => pure (dflt c, sd)) = _
  rcases h : sd (.inl c) with _ | ⟨u, us⟩ <;> simp [h]

theorem obs_coin (n : ℕ) (ob : Obs Q Y Rc config) :
    (obsImpl keyRoots (.inl n)).run ob = qC n >>= fun u => pure (u, ob) := rfl

theorem obs_hash (q : Q) (ob : Obs Q Y Rc config) :
    (obsImpl keyRoots (.inr (.inl q))).run ob =
      qH q >>= fun y => pure (y, ob.hash q (toH q y)) := rfl

theorem obs_fs (key : K) (ob : Obs Q Y Rc config) :
    (obsImpl keyRoots (.inr (.inr key))).run ob =
      qF key >>= fun v => pure (v, ob.fs keyRoots key (toF key v)) := rfl

theorem sodImpl_hash (q : Q) (sd : QuerySeed (progSpec Q Y C)) :
    (sodImpl (Q := Q) (Y := Y) (C := C) (.inr q)).run sd =
      (fun y => (y, sd)) <$> (liftM ((hashSpec Q Y).query q) : OracleComp (hashSpec Q Y) Y) := by
  simp [sodImpl, map_eq_bind_pure_comp]

theorem toF_ofF (key : K) (v : Rc key) : toF (Q := Q) (Y := Y) key (ofF key v) = v := rfl
theorem toH_ofH (q : Q) (y : Y) : toH (Rc := Rc) q (ofH q y) = y := rfl

theorem sf_qC (n : ℕ) (fsc : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)) :
    (simulateQ (sodImpl (Q := Q) (Y := Y) (C := C))
      ((simulateQ (foldImpl rd e) (qC n)).run fsc)).run sd =
      pure (((popCoin (Y := Y) sd (.inl n)).1, fsc), (popCoin (Y := Y) sd (.inl n)).2) := by
  simp only [simulateQ_qC, foldImpl]
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure]
  rw [show (sodImpl (Q := Q) (Y := Y) (C := C) (Sum.inl (Sum.inl n))).run sd =
    pure (popCoin (Y := Y) sd (.inl n)) from sodImpl_coin (.inl n) sd]
  simp

theorem sf_qH (q : Q) (fsc : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)) :
    (simulateQ (sodImpl (Q := Q) (Y := Y) (C := C))
      ((simulateQ (foldImpl rd e) (qH q)).run fsc)).run sd =
      (fun y => ((ofH (Rc := Rc) q y, fsc), sd)) <$>
        (liftM ((hashSpec Q Y).query q) : OracleComp (hashSpec Q Y) Y) := by
  rw [simulateQ_qH]
  change (simulateQ (sodImpl (Q := Q) (Y := Y) (C := C))
    ((StateT.lift (liftM ((progSpec Q Y C).query (.inr q)) : OracleComp (progSpec Q Y C) Y) :
      StateT (ofFn Rc).QueryCache (OracleComp (progSpec Q Y C)) Y).run fsc)).run sd = _
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [simulateQ_spec_query, sodImpl_hash]
  simp [Functor.map_map, ofH]

theorem sf_qF (key : K) (fsc : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C)) :
    (simulateQ (sodImpl (Q := Q) (Y := Y) (C := C))
      ((simulateQ (foldImpl rd e) (qF key)).run fsc)).run sd =
      match fsc.toFn key with
      | some v => pure ((ofF (Q := Q) (Y := Y) key v, fsc), sd)
      | none => pure ((ofF (Q := Q) (Y := Y) key (e key (popCoin (Y := Y) sd (.inr (rd key))).1),
          fsc.cacheQuery key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)),
          (popCoin (Y := Y) sd (.inr (rd key))).2) := by
  simp only [simulateQ_qF]
  rcases hq : fsc.toFn key with _ | v
  · simp [foldImpl, hq]
    rw [show (sodImpl (Q := Q) (Y := Y) (C := C) (Sum.inl (Sum.inr (rd key)))).run sd =
      pure (popCoin (Y := Y) sd (.inr (rd key))) from sodImpl_coin (.inr (rd key)) sd]
    simp [ofF]
  · simp [foldImpl, hq, ofF]

theorem Obs.fresh_seen (keyRoots : K → List (Cfg × Y)) (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    (ob.fresh keyRoots key v).seen = ob.seen.cacheQuery key v := by
  unfold Obs.fresh
  rcases keyRoots key with _ | ⟨x, xs⟩ <;> rfl

theorem Obs.fs_of_some (keyRoots : K → List (Cfg × Y)) (ob : Obs Q Y Rc config) (key : K)
    (v : Rc key) (w : Rc key) (h : ob.seen.toFn key = some w) : ob.fs keyRoots key v = ob := by
  unfold Obs.fs
  rw [show ob.seen key = some w from h]

theorem Obs.fs_of_none (keyRoots : K → List (Cfg × Y)) (ob : Obs Q Y Rc config) (key : K)
    (v : Rc key) (h : ob.seen.toFn key = none) : ob.fs keyRoots key v = ob.fresh keyRoots key v := by
  unfold Obs.fs
  rw [show ob.seen key = none from h]

/-- the triple `simulateQ` nesting of `seededProg rd e (instr A) σ` (with free seed and cache) is `bs` -/
theorem seeded_instr_eq_bs {α : Type} (A : OracleComp (realSpec Q Y Rc) α) :
    ∀ (ob : Obs Q Y Rc config) (sd : QuerySeed (progSpec Q Y C)) (fsc : (ofFn Rc).QueryCache),
    ob.seen = fsc →
    (simulateQ (sodImpl (Q := Q) (Y := Y) (C := C))
      ((simulateQ (foldImpl rd e) ((simulateQ (obsImpl keyRoots) A).run ob)).run fsc)).run sd =
      (fun r => (((r.1, r.2.1), r.2.1.seen), r.2.2)) <$> bs keyRoots rd e A ob sd := by
  induction A with
  | pure a => intro ob sd fsc h; subst h; simp [bs]
  | queryBind t k ih =>
    intro ob sd fsc h
    subst h
    have hq : (OracleComp.queryBind t k : OracleComp (realSpec Q Y Rc) α) =
        (liftM (OracleSpec.query t) : OracleComp (realSpec Q Y Rc) _) >>= k := rfl
    rcases t with n | q | key
    · have hb : bs keyRoots rd e (OracleComp.queryBind (Sum.inl n) k) ob sd =
          bs keyRoots rd e (k (popCoin (Y := Y) sd (.inl n)).1) ob (popCoin (Y := Y) sd (.inl n)).2 := by
        simp only [bs]
      rw [hb, hq]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, obs_coin, bind_assoc,
        pure_bind, sf_qC]
      exact ih _ _ _ _ rfl
    · have hb : bs keyRoots rd e (OracleComp.queryBind (Sum.inr (Sum.inl q)) k) ob sd =
          (do let y ← (liftM ((hashSpec Q Y).query q) : OracleComp (hashSpec Q Y) Y)
              bs keyRoots rd e (k (ofH q y)) (ob.hash q y) sd) := by
        simp only [bs]
      rw [hb, hq]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, obs_hash, bind_assoc,
        pure_bind, sf_qH, map_bind, bind_map_left]
      refine bind_congr fun y => ?_
      exact ih (ofH q y) (ob.hash q y) sd ob.seen rfl
    · rcases hs : ob.seen.toFn key with _ | v
      · have hb : bs keyRoots rd e (OracleComp.queryBind (Sum.inr (Sum.inr key)) k) ob sd =
            bs keyRoots rd e (k (ofF key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)))
              (ob.fresh keyRoots key (e key (popCoin (Y := Y) sd (.inr (rd key))).1))
              (popCoin (Y := Y) sd (.inr (rd key))).2 := by
          simp only [bs]
          rw [show ob.seen key = none from hs]
        rw [hb, hq]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, obs_fs, bind_assoc,
          pure_bind, sf_qF, hs, toF_ofF]
        rw [Obs.fs_of_none keyRoots ob key _ hs]
        exact ih _ _ _ _ (Obs.fresh_seen keyRoots ob key _)
      · have hb : bs keyRoots rd e (OracleComp.queryBind (Sum.inr (Sum.inr key)) k) ob sd =
            bs keyRoots rd e (k (ofF key v)) ob sd := by
          simp only [bs]
          rw [show ob.seen key = some v from hs]
        rw [hb, hq]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, obs_fs, bind_assoc,
          pure_bind, sf_qF, hs, toF_ofF]
        rw [Obs.fs_of_some keyRoots ob key _ v hs]
        exact ih _ _ _ _ rfl

end L1


section Committer

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J]
variable [∀ j, SampleableType (C j)] [∀ j, Finite (C j)] [∀ j, Nonempty (C j)]
variable [SampleableType Y] [Finite Y] [Nonempty Y]
variable [Inhabited Cfg] [Inhabited Y]
variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)
variable {α : Type}

/-- committer mode -/
inductive Mode (Q Y : Type) {K : Type} (Rc : K → Type) (α : Type)
  | running (A : OracleComp (realSpec Q Y Rc) α)
  | done (a : α)

/-- committer private state: mode, FS cache, remaining seed, queue of pending (tag, root) -/
structure PS (Q Y : Type) {K : Type} (Rc : K → Type) {J : Type} (C : J → Type) (Cfg : Type)
    (α : Type) where
  mode : Mode Q Y Rc α
  seen : (ofFn Rc).QueryCache
  sd : QuerySeed (progSpec Q Y C)
  queue : List (Cfg × Y)

/-- the final roots of A as head and tail (a padding root if there are none) -/
def finalNE (finalRoots : α → List (Cfg × Y)) (a : α) : (Cfg × Y) × List (Cfg × Y) :=
  match finalRoots a with
  | [] => (default, [])
  | x :: xs => (x, xs)

/-- one commitment phase -/
noncomputable def commitPhase (finalRoots : α → List (Cfg × Y)) (_round : ℕ)
    (ps : PS Q Y Rc C Cfg α) : OracleComp (hashSpec Q Y) (Cfg × Y × PS Q Y Rc C Cfg α) :=
  match ps.queue with
  | x :: qs => pure (x.1, x.2, { ps with queue := qs })
  | [] =>
    match ps.mode with
    | .done _ => pure (default, default, ps)
    | .running A => do
        let r ← run1 keyRoots rd e A ps.seen ps.sd
        pure (match r with
          | .fresh hd tl A' seen sd _ => (hd.1, hd.2, ⟨.running A', seen, sd, tl⟩)
          | .done a seen sd _ =>
              ((finalNE finalRoots a).1.1, (finalNE finalRoots a).1.2,
                ⟨.done a, seen, sd, (finalNE finalRoots a).2⟩))

/-- the sequential committer of `advOf` -/
noncomputable def committerOf (finalRoots : α → List (Cfg × Y)) (A : OracleComp (realSpec Q Y Rc) α)
    (σ : QuerySeed (progSpec Q Y C)) : SequentialCommitter Cfg Q Y where
  State := PS Q Y Rc C Cfg α
  initialState := ⟨.running A, ∅, σ, []⟩
  commit := commitPhase keyRoots rd e finalRoots

/-- **`advOf σ`** -/
noncomputable def advOf (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) :
    Adversary Cfg Q Address Y config where
  committer := committerOf keyRoots rd e finalRoots A σ
  opening := fun ps ext =>
    pure (match ps.mode with
      | .done a => mkTerminal a ext
      | .running _ => [])

/-- pending roots recorded against the cumulative log `h` -/
def recQ (h : Log Q Y) (ext : ExtractorState Cfg Q Address Y config) (q : List (Cfg × Y)) :
    ExtractorState Cfg Q Address Y config :=
  q.foldl (fun e x => e.recordCumulative x.1 h x.2) ext

/-- `m` padding checkpoints `(default, default)` -/
def padExt : ℕ → ExtractorState Cfg Q Address Y config → ExtractorState Cfg Q Address Y config
  | 0, ext => ext
  | m + 1, ext => padExt m (ext.record default [] default)

/-- the observer state after the final stop of A -/
def finalObs (finalRoots : α → List (Cfg × Y)) (a : α) (ob : Obs Q Y Rc config) :
    Obs Q Y Rc config :=
  ob.stop (finalNE finalRoots a).1 (finalNE finalRoots a).2

theorem recQ_length (h : Log Q Y) (ext : ExtractorState Cfg Q Address Y config)
    (q : List (Cfg × Y)) :
    (recQ h ext q).checkpoints.length = ext.checkpoints.length + q.length := by
  induction q generalizing ext with
  | nil => simp [recQ]
  | cons x qs ih =>
      have := ih (ext.recordCumulative x.1 h x.2)
      simp only [recQ, List.foldl_cons] at this ⊢
      rw [this]; simp; omega

theorem padExt_length (m : ℕ) (ext : ExtractorState Cfg Q Address Y config) :
    (padExt m ext).checkpoints.length = ext.checkpoints.length + m := by
  induction m generalizing ext with
  | zero => rfl
  | succ m ih => rw [padExt, ih]; simp; omega

theorem Obs.stop_ext (ob : Obs Q Y Rc config) (hd : Cfg × Y) (tl : List (Cfg × Y)) :
    (ob.stop hd tl).ext = recQ ob.hlog ob.ext (hd :: tl) := rfl

theorem run_done (finalRoots : α → List (Cfg × Y)) (A₀ : OracleComp (realSpec Q Y Rc) α)
    (σ₀ : QuerySeed (progSpec Q Y C)) (a : α) :
    ∀ (n : ℕ) (seen : (ofFn Rc).QueryCache) (sd : QuerySeed (progSpec Q Y C))
      (q : List (Cfg × Y)) (extV : ExtractorState Cfg Q Address Y config) (first : ℕ),
    q.length ≤ n →
    (committerOf keyRoots rd e finalRoots A₀ σ₀).runCommitments (config := config) n first
        (⟨.done a, seen, sd, q⟩ : PS Q Y Rc C Cfg α) extV =
      pure (⟨.done a, seen, sd, []⟩, padExt (n - q.length) (recQ extV.cumulativeLog extV q)) := by
  intro n
  induction n with
  | zero =>
      intro seen sd q extV first hq
      have : q = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp [SequentialCommitter.runCommitments, recQ, padExt]
  | succ n ih =>
      intro seen sd q extV first hq
      rcases q with _ | ⟨x, qs⟩
      · simp only [SequentialCommitter.runCommitments, committerOf, commitPhase, withQueryLog_pure,
          pure_bind]
        have := ih seen sd [] (extV.record default [] default) (first + 1) (by simp)
        simp only [committerOf, List.length_nil, Nat.sub_zero] at this ⊢
        rw [this]
        simp [recQ, padExt]
      · simp only [SequentialCommitter.runCommitments, committerOf, commitPhase, withQueryLog_pure,
          pure_bind]
        have := ih seen sd qs (extV.record x.1 [] x.2) (first + 1) (by simp at hq; omega)
        simp only [committerOf] at this ⊢
        rw [this]
        simp [recQ, List.length_cons, show n + 1 - (qs.length + 1) = n - qs.length by omega,
          ← ExtractorState.recordCumulative_append]

theorem Obs.fresh_ext_length (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    ob.ext.checkpoints.length ≤ (ob.fresh keyRoots key v).ext.checkpoints.length := by
  unfold Obs.fresh
  rcases keyRoots key with _ | ⟨x, xs⟩
  · exact le_rfl
  · simp only [Obs.stop_ext, recQ_length]; simp

/-- `bs` never removes checkpoints -/
theorem bs_mono (A : OracleComp (realSpec Q Y Rc) α) :
    ∀ (ob : Obs Q Y Rc config) (sd : QuerySeed (progSpec Q Y C))
      (r : α × Obs Q Y Rc config × QuerySeed (progSpec Q Y C)),
    r ∈ support (bs keyRoots rd e A ob sd) →
    ob.ext.checkpoints.length ≤ r.2.1.ext.checkpoints.length := by
  induction A with
  | pure a =>
      intro ob sd r hr
      simp only [bs, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
  | queryBind t k ih =>
    intro ob sd r hr
    rcases t with n | q | key
    · simp only [bs] at hr; exact ih _ _ _ _ hr
    · simp only [bs, mem_support_bind_iff] at hr
      obtain ⟨y, _, hy⟩ := hr
      exact ih (ofH q y) (ob.hash q y) sd r hy
    · simp only [bs] at hr
      rcases hs : ob.seen key with _ | v
      · simp only [hs] at hr
        exact (Obs.fresh_ext_length keyRoots ob key _).trans (ih _ _ _ _ hr)
      · simp only [hs] at hr
        exact ih _ _ _ _ hr

/-- closed form of the committer run: the final private state and the padded extractor state -/
def closedRun (finalRoots : α → List (Cfg × Y)) (m : ℕ)
    (r : α × Obs Q Y Rc config × QuerySeed (progSpec Q Y C)) :
    PS Q Y Rc C Cfg α × ExtractorState Cfg Q Address Y config :=
  (⟨.done r.1, r.2.1.seen, r.2.2, []⟩,
    padExt (m - (finalObs finalRoots r.1 r.2.1).ext.checkpoints.length)
      (finalObs finalRoots r.1 r.2.1).ext)

theorem finalObs_length (finalRoots : α → List (Cfg × Y)) (a : α) (ob : Obs Q Y Rc config) :
    (finalObs finalRoots a ob).ext.checkpoints.length =
      ob.ext.checkpoints.length + 1 + (finalNE finalRoots a).2.length := by
  simp only [finalObs, Obs.stop_ext, recQ_length]; simp; omega

theorem run_running (finalRoots : α → List (Cfg × Y)) (A₀ : OracleComp (realSpec Q Y Rc) α)
    (σ₀ : QuerySeed (progSpec Q Y C)) :
    ∀ (n : ℕ) (A : OracleComp (realSpec Q Y Rc) α) (ob : Obs Q Y Rc config)
      (sd : QuerySeed (progSpec Q Y C)) (q : List (Cfg × Y))
      (extV : ExtractorState Cfg Q Address Y config) (first : ℕ),
    ob.ext = recQ ob.hlog extV q → ob.hlog = extV.cumulativeLog →
    (∀ r ∈ support (bs keyRoots rd e A ob sd),
      (finalObs finalRoots r.1 r.2.1).ext.checkpoints.length ≤ extV.checkpoints.length + n) →
    (committerOf keyRoots rd e finalRoots A₀ σ₀).runCommitments (config := config) n first
        (⟨.running A, ob.seen, sd, q⟩ : PS Q Y Rc C Cfg α) extV =
      closedRun finalRoots (extV.checkpoints.length + n) <$> bs keyRoots rd e A ob sd := by
  intro n
  induction n with
  | zero =>
      intro A ob sd q extV first hext hlog hdem
      exfalso
      obtain ⟨r, hr⟩ := OracleComp.support_nonempty (bs keyRoots rd e A ob sd)
      have h1 := hdem r hr
      have h2 := bs_mono keyRoots rd e A ob sd r hr
      rw [finalObs_length] at h1
      rw [hext, recQ_length] at h2
      omega
  | succ n ih =>
      intro A ob sd q extV first hext hlog hdem
      rcases q with _ | ⟨x, qs⟩
      · have hext0 : ob.ext = extV := hext
        simp only [SequentialCommitter.runCommitments, committerOf, commitPhase]
        rw [bs_eq_run1 keyRoots rd e A ob sd, map_bind]
        simp only [withQueryLog_bind, run1_withQueryLog, withQueryLog_pure, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, Function.comp_def, List.append_nil]
        refine OracleComp.bind_congr_of_forall_mem_support _ fun r hr => ?_
        have hdem' : ∀ z ∈ support (resume keyRoots rd e ob r),
            (finalObs finalRoots z.1 z.2.1).ext.checkpoints.length ≤
              extV.checkpoints.length + (n + 1) := fun z hz =>
          hdem z (by rw [bs_eq_run1 keyRoots rd e A ob sd, mem_support_bind_iff]; exact ⟨r, hr, hz⟩)
        rcases r with ⟨hd, tl, A', seen', sd', seg⟩ | ⟨a, seen', sd', seg⟩
        · simp only [resume] at hdem' ⊢
          simp only [Prod.map_apply, Stop.seg, List.append_nil, pure_bind, id_eq]
          have h := ih A' (({ hlog := ob.hlog ++ seg, ext := ob.ext, seen := seen' } :
              Obs Q Y Rc config).stop hd tl) sd' tl (extV.record hd.1 seg hd.2) (first + 1)
            (by
              rw [Obs.stop_ext, hext0]
              unfold recQ
              simp only [List.foldl_cons]
              rw [hlog, ExtractorState.recordCumulative_append]
              rfl)
            (by simp [Obs.stop, hlog])
            (by
              intro z hz
              have := hdem' z hz
              simp only [ExtractorState.record_checkpoints_length]
              omega)
          simp only [committerOf, ExtractorState.record_checkpoints_length] at h
          rw [show extV.checkpoints.length + 1 + n = extV.checkpoints.length + (n + 1) by omega,
            map_eq_bind_pure_comp] at h
          exact h
        · simp only [resume] at hdem' ⊢
          simp only [Prod.map_apply, Stop.seg, List.append_nil, pure_bind, id_eq]
          have hlen : (finalNE finalRoots a).2.length ≤ n := by
            have := hdem' (a, { hlog := ob.hlog ++ seg, ext := ob.ext, seen := seen' }, sd')
              (by simp)
            rw [finalObs_length] at this
            simp only [hext0] at this
            omega
          have h := run_done keyRoots rd e finalRoots A₀ σ₀ a n seen' sd' (finalNE finalRoots a).2
            (extV.record (finalNE finalRoots a).1.1 seg (finalNE finalRoots a).1.2) (first + 1) hlen
          simp only [committerOf] at h ⊢
          rw [h]
          have hl : (finalObs finalRoots a
              ({ hlog := ob.hlog ++ seg, ext := ob.ext, seen := seen' } : Obs Q Y Rc config)).ext.checkpoints.length
              = extV.checkpoints.length + 1 + (finalNE finalRoots a).2.length := by
            rw [finalObs_length]; simp [hext0]
          simp only [closedRun, hl]
          have hn : extV.checkpoints.length + (n + 1) - (extV.checkpoints.length + 1 +
              (finalNE finalRoots a).2.length) = n - (finalNE finalRoots a).2.length := by omega
          rw [hn]
          congr 2
          simp only [finalObs, Obs.stop_ext, hext0]
          unfold recQ
          simp only [List.foldl_cons, ExtractorState.record_cumulativeLog]
          rw [hlog, ExtractorState.recordCumulative_append]
      · simp only [SequentialCommitter.runCommitments, committerOf, commitPhase, withQueryLog_pure,
          pure_bind]
        have hrec : extV.record x.1 [] x.2 = extV.recordCumulative x.1 ob.hlog x.2 := by
          rw [hlog, ← ExtractorState.recordCumulative_append, List.append_nil]
        have := ih A ob sd qs (extV.record x.1 [] x.2) (first + 1)
          (by rw [hext, hrec]; rfl)
          (by rw [hlog]; simp)
          (by
            intro r hr
            have := hdem r hr
            simp only [ExtractorState.record_checkpoints_length]
            omega)
        simp only [committerOf] at this ⊢
        rw [this]
        simp only [ExtractorState.record_checkpoints_length]
        have hh : extV.checkpoints.length + 1 + n = extV.checkpoints.length + (n + 1) := by omega
        rw [hh]

end Committer

section Assembly

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J] [DecidableEq Y]
variable [∀ j, SampleableType (C j)] [∀ j, Finite (C j)] [∀ j, Nonempty (C j)]
variable [SampleableType Y] [Finite Y] [Nonempty Y]
variable [Inhabited Cfg] [Inhabited Y]
variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)
variable {α : Type}

/-- the final extractor state of the game for the run `(a, ob)` of the instrumented program:
the observer's checkpoints, the final stop, and padding up to `rounds` phases -/
def finalExt (finalRoots : α → List (Cfg × Y)) (rounds : ℕ) (a : α) (ob : Obs Q Y Rc config) :
    ExtractorState Cfg Q Address Y config :=
  padExt (rounds - (finalObs finalRoots a ob).ext.checkpoints.length) (finalObs finalRoots a ob).ext

/-- **`ourInner`**: VCVio's `runFromEmptyThen` with a terminal step that also returns the private
state. -/
def ourInner (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (adversary : Adversary Cfg Q Address Y config) :
    OracleComp (Q →ₒ Y) (Transcript Cfg Q Address Y config × adversary.committer.State) :=
  adversary.committer.runFromEmptyThen config rounds fun ps ext =>
    (fun t => (t, ps)) <$> adversary.terminalExecution model ps ext

theorem extractabilityInner_eq_map_ourInner
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (adversary : Adversary Cfg Q Address Y config) :
    extractabilityInner model config rounds adversary =
      Prod.fst <$> ourInner model config rounds adversary := by
  rw [extractabilityInner_eq_runFromEmptyThen]
  simp [ourInner, SequentialCommitter.runFromEmptyThen, SequentialCommitter.runCommitmentsThen,
    Functor.map_map]

/-- **The phase theorem.** For every seed σ, VCVio's executable game for `advOf σ` is the big-step
run of the instrumented program followed by the pure opening phase and honest verification. -/
theorem extractabilityInner_advOf_bs
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) (rounds : ℕ)
    (hbud : ∀ r ∈ support (bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ),
      (finalObs finalRoots r.1 r.2.1).ext.checkpoints.length ≤ rounds) :
    extractabilityInner model config rounds (advOf keyRoots rd e finalRoots mkTerminal A σ) =
      (do
        let r ← bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ
        let ext := finalExt finalRoots rounds r.1 r.2.1
        let attempts ← verifyOpeningClaims model (mkTerminal r.1 ext)
        pure ({ extractorState := ext, attempts, terminalSuffix := [] } :
          Transcript Cfg Q Address Y config)) := by
  rw [extractabilityInner_eq_runFromEmptyThen]
  have h := run_running keyRoots rd e finalRoots A σ rounds A Obs.init σ [] ExtractorState.empty 0
    rfl rfl (by simpa using hbud)
  simp only [SequentialCommitter.runFromEmptyThen, SequentialCommitter.runCommitmentsThen,
    SequentialCommitter.runFromEmpty]
  refine (congrArg (fun m => m >>= fun x =>
    Adversary.terminalExecution model (advOf keyRoots rd e finalRoots mkTerminal A σ) x.1 x.2)
      h : _).trans ?_
  refine (bind_map_left _ _ _).trans ?_
  refine bind_congr fun r => ?_
  simp [closedRun, finalExt, Adversary.terminalExecution, advOf]

/-- `ourInner (advOf σ)`: the game transcript together with the final private state. -/
theorem ourInner_advOf_bs
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) (rounds : ℕ)
    (hbud : ∀ r ∈ support (bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ),
      (finalObs finalRoots r.1 r.2.1).ext.checkpoints.length ≤ rounds) :
    ourInner model config rounds (advOf keyRoots rd e finalRoots mkTerminal A σ) =
      (do
        let r ← bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ
        let ext := finalExt finalRoots rounds r.1 r.2.1
        let attempts ← verifyOpeningClaims model (mkTerminal r.1 ext)
        pure (({ extractorState := ext, attempts, terminalSuffix := [] } :
          Transcript Cfg Q Address Y config),
          (closedRun (Address := Address) finalRoots rounds r).1)) := by
  have h := run_running keyRoots rd e finalRoots A σ rounds A Obs.init σ [] ExtractorState.empty 0
    rfl rfl (by simpa using hbud)
  unfold ourInner
  simp only [SequentialCommitter.runFromEmptyThen, SequentialCommitter.runCommitmentsThen]
  refine (congrArg (fun m => m >>= fun x =>
    (fun t => (t, x.1)) <$>
      Adversary.terminalExecution model (advOf keyRoots rd e finalRoots mkTerminal A σ) x.1 x.2)
      h : _).trans ?_
  refine (bind_map_left _ _ _).trans ?_
  refine bind_congr fun r => ?_
  simp [closedRun, finalExt, Adversary.terminalExecution, advOf]

/-- the instrumented `P_σ` of Derand is the projection of the big-step run `bs` -/
theorem seededProg_instr (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) :
    seededProg rd e (instr (config := config) keyRoots A) σ =
      (fun r => ((r.1, r.2.1), r.2.1.seen)) <$> bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ := by
  have h := seeded_instr_eq_bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ ∅ rfl
  simp only [seededProg, foldProg, instr, StateT.run'_eq, h, Functor.map_map]

/-- **Phase theorem, in terms of Derand's instrumented `P_σ`.** -/
theorem extractabilityInner_advOf
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) (rounds : ℕ)
    (hbud : ∀ z ∈ support (seededProg rd e (instr (config := config) keyRoots A) σ),
      (finalObs finalRoots z.1.1 z.1.2).ext.checkpoints.length ≤ rounds) :
    extractabilityInner model config rounds (advOf keyRoots rd e finalRoots mkTerminal A σ) =
      (do
        let z ← seededProg rd e (instr (config := config) keyRoots A) σ
        let ext := finalExt finalRoots rounds z.1.1 z.1.2
        let attempts ← verifyOpeningClaims model (mkTerminal z.1.1 ext)
        pure ({ extractorState := ext, attempts, terminalSuffix := [] } :
          Transcript Cfg Q Address Y config)) := by
  rw [seededProg_instr] at hbud ⊢
  rw [extractabilityInner_advOf_bs keyRoots rd e model finalRoots mkTerminal A σ rounds
    (fun r hr => hbud _ (by rw [support_map]; exact ⟨r, hr, rfl⟩))]
  rw [bind_map_left]

/-- Transport of `hquery`: if the instrumented `P_σ` makes at most `Q_H` hash queries, so does the whole
adversarial prefix of `advOf σ` (all commitment phases and the opening phase). -/
theorem hquery_advOf
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) (rounds Q_H : ℕ)
    (hbud : ∀ z ∈ support (seededProg rd e (instr (config := config) keyRoots A) σ),
      (finalObs finalRoots z.1.1 z.1.2).ext.checkpoints.length ≤ rounds)
    (hH : IsTotalQueryBound (seededProg rd e (instr (config := config) keyRoots A) σ) Q_H) :
    (advOf keyRoots rd e finalRoots mkTerminal A σ).IsAdversaryPrefixQueryBound rounds Q_H := by
  rw [seededProg_instr] at hbud hH
  have hbs : IsTotalQueryBound (bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ) Q_H :=
    (isQueryBound_map_iff _ _ _ _ _).mp hH
  have hbud' : ∀ r ∈ support (bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ),
      (finalObs finalRoots r.1 r.2.1).ext.checkpoints.length ≤ rounds :=
    fun r hr => hbud _ (by rw [support_map]; exact ⟨r, hr, rfl⟩)
  have h := run_running keyRoots rd e finalRoots A σ rounds A Obs.init σ [] ExtractorState.empty 0
    rfl rfl (by simpa using hbud')
  have hp : (advOf keyRoots rd e finalRoots mkTerminal A σ).prefixProgram (config := config) rounds =
      (fun _ => ()) <$> bs keyRoots rd e A (Obs.init : Obs Q Y Rc config) σ := by
    unfold Adversary.prefixProgram
    refine (congrArg (fun m => m >>= fun x =>
      (advOf keyRoots rd e finalRoots mkTerminal A σ).opening x.1 x.2 >>= fun _ => pure ())
        (h : (advOf keyRoots rd e finalRoots mkTerminal A σ).committer.runFromEmpty config rounds =
          _)).trans ?_
    refine (bind_map_left _ _ _).trans ?_
    simp only [map_eq_bind_pure_comp]
    refine bind_congr fun r => ?_
    simp [advOf, closedRun]
  unfold Adversary.IsAdversaryPrefixQueryBound
  rw [hp]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr hbs

/-- Transport of `hverifier`: the opening phase is the pure function `mkTerminal`. -/
theorem hverifier_advOf
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α) (σ : QuerySeed (progSpec Q Y C)) (V : ℕ)
    (hterm : ∀ a ext, claimsQueryCount (mkTerminal a ext) ≤ V) :
    (advOf keyRoots rd e finalRoots mkTerminal A σ).HasVerifierQueryBound V := by
  intro ps ext claims hc
  simp only [advOf, support_pure, Set.mem_singleton_iff] at hc
  subst hc
  rcases ps with ⟨mode, _, _, _⟩
  cases mode with
  | running _ => simp [claimsQueryCount]
  | done a => exact hterm a ext

/-- **Pointwise-in-σ bad-event bound for `advOf σ`** (VCVio `StrongBound.lean:516`, with every
hypothesis transported). `hconfig`, `hnodes`, `hcheckpoints` do not mention the adversary and are
passed through; `hbud` says the observed run fits in `rounds` phases (`rounds = k·(Q_FS+1)`),
`hH` bounds the hash queries of the instrumented `P_σ`, `hterm` bounds the verifier overhead. -/
theorem pr_bad_advOf_le [DecidableEq Address]
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α)
    (rounds Q_H nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hbud : ∀ σ : QuerySeed (progSpec Q Y C),
      ∀ z ∈ support (seededProg rd e (instr (config := config) keyRoots A) σ),
      (finalObs finalRoots z.1.1 z.1.2).ext.checkpoints.length ≤ rounds)
    (hH : ∀ σ : QuerySeed (progSpec Q Y C),
      IsTotalQueryBound (seededProg rd e (instr (config := config) keyRoots A) σ) Q_H)
    (hterm : ∀ a ext, claimsQueryCount (mkTerminal a ext) ≤ verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) (σ : QuerySeed (progSpec Q Y C)) :
    Pr{let z ← extractabilityExperiment model config rounds
        (advOf keyRoots rd e finalRoots mkTerminal A σ)}[
        Transcript.HasAnyCheckpointExtractionDisagreement model z] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead Q_H : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds
    (advOf keyRoots rd e finalRoots mkTerminal A σ) Q_H nodeBudget checkpointCount verifierOverhead
    perCheckpoint
    (hquery_advOf keyRoots rd e finalRoots mkTerminal A σ rounds Q_H (hbud σ) (hH σ))
    (hverifier_advOf keyRoots rd e finalRoots mkTerminal A σ verifierOverhead hterm)
    hconfig hnodes hcheckpoints

end Assembly

end NockvmE2E.Merkle.Phases
