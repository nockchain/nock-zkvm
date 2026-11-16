/-
 (1.2 term (b), 1.3 row "FRI-layer Merkle"; KERNEL-checked).

The FRI-layer Merkle trees of the side proof.  The batched FRI mask is `bMask := (batchRound S, clear) :: friMask`
(the batching round has no prover message, hence no tree), so its merkle part is exactly the `k` FRI layer trees.
  * `fri_hclear_batched`      : the batched analogue of `Merkle/FriGlue.lean fri_hclear`: the `hclear` hypothesis of
                                `merkle_singleSalt_soundness` over `pairedRoundsK bMask`, discharged with `bfriErr`
                                (the right-hand side of `batchedFri_singleSalt_soundness`), for any statement map `stm`;
  * `bMask_queryOnly`         : `QueryOnly bMask decode bAccepts bLocal` (from `fri_queryOnly` on the tail);
  * `side_merkle_singleSalt_soundness` : `merkle_singleSalt_soundness` at `bMask`: the compiled path accepts and
                                `stm z.1 ∉ language` has probability <= `bfriErr Q + multiCheckpointROMErrorNumerator(k(Q+1)P, k(Q+1), V, Q_H)/|Y|`
                                (term (b) of `εfix`);
  * `sideStmt_merkle_soundness` : the same at `Stmt := SideStmt`, `stm := stmtOf C hn`.
SEAM: the compiled side path's acceptance `localAccepts` is a PARAMETER with `hlocal : QueryOnly bMask decode bAccepts localAccepts`;
7-5 supplies the flat verifier's check as `localAccepts` and proves `hlocal` for it; `bLocal` is a witness (satisfiability).
-/
import NockvmE2E.Merkle.FriGlue
import NockvmE2E.Merkle.Soundness
import NockvmE2E.Exec.SideStmt

open BinaryTree OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain NockvmE2E.FriPort NockvmE2E.FriPort.Batched NockvmE2E.Merkle.Fri
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good NockvmE2E.Merkle.SoundnessWorld NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.Merkle.BadBound
open MerkleTreeMultiExtractability
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.SideMerkle

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l m : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)

/-- the batched-FRI error `Q·max(ε, max_j challengeError_j) + ε + Σ foldingError + (1 − min θ δ)^l`: the right-hand side of
`batchedFri_singleSalt_soundness` -/
noncomputable def bfriErr (θ : ℝ) (δ ε : ℝ≥0) (Q : ℕ) : ℝ≥0∞ :=
  Q * ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))) +
    ((ε : ℝ≥0∞) +
      (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞))

/-! ## 1. The batched mask -/

/-- the batched FRI mask: the batching round `(Unit, cs)` in the clear, then the FRI mask (`f_1 … f_k` merkle) -/
noncomputable def bMask : MRounds Dg :=
  ⟨batchRound S, .clear⟩ :: friMask s d l L Dg enc

theorem baseRounds_bMask : baseRounds Dg (bMask (S := S) s d l L Dg enc) = batchedRounds (ω := ω) (S := S) s d l :=
  congrArg (_ :: ·) (baseRounds_friMask s d l L Dg enc)

theorem merkleSkels_bMask : merkleSkels (bMask (S := S) s d l L Dg enc) = merkleSkels (friMask s d l L Dg enc) := rfl

theorem merkleCount_friMerkleMask : (i c : ℕ) → (h : i + c = k) →
    merkleCount Dg (friMerkleMask s d l L Dg enc i c h) = c
  | _, 0, _ => rfl
  | i, c + 1, h => by
      show merkleCount Dg (friMerkleMask s d l L Dg enc i.succ c _) + 1 = c + 1
      rw [merkleCount_friMerkleMask i.succ c (by omega)]

/-- the merkle part of `bMask` is exactly the `k` FRI layer trees -/
theorem merkleSkels_bMask_length : (merkleSkels (bMask (S := S) s d l L Dg enc)).length = k := by
  rw [merkleSkels_length]
  exact merkleCount_friMerkleMask s d l L Dg enc 0 k (by omega)

/-- `hpos` of `merkle_singleSalt_soundness` at `bMask`: at least one merkle round iff `k ≥ 1` -/
theorem hpos_bMask (hk : 1 ≤ k) : 0 < (merkleSkels (bMask (S := S) s d l L Dg enc)).length := by
  rw [merkleSkels_bMask_length]; exact hk

theorem merkleSkels_friMerkleMask : (i c : ℕ) → (h : i + c = k) →
    merkleSkels (friMerkleMask s d l L Dg enc i c h) = (List.finRange c).map (fun j : Fin c => L.skel ⟨i + j.1, by have := j.2; omega⟩)
  | _, 0, _ => rfl
  | i, c + 1, h => by
      show L.skel ⟨i, _⟩ :: merkleSkels (friMerkleMask s d l L Dg enc i.succ c _) = _
      rw [merkleSkels_friMerkleMask i.succ c (by omega), List.finRange_succ]
      simp only [List.map_cons, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro a _
      congr 2
      first | omega | (simp; omega) | simp

/-- the skeletons of the merkle part of `bMask` are the `k` FRI layer skeletons `L.skel 0 … L.skel (k-1)`, in order
(these are the tail of `skelsF` = VK rag tree followed by these) -/
theorem merkleSkels_bMask_eq : merkleSkels (bMask (S := S) s d l L Dg enc) = (List.finRange k).map L.skel := by
  show merkleSkels (friMerkleMask s d l L Dg enc 0 k _) = _
  rw [merkleSkels_friMerkleMask]
  apply List.map_congr_left
  intro j _
  congr 1
  exact Fin.ext (by simp)

/-! ## 2. `hclear` for the batched mask -/

/-- **Batched paired soundness over any round list equal to `batchRound :: friAltP.rounds`**, for any statement map `stm`
and any acceptance predicate `acc` that implies FRI's legacy `queryBad` on the legacy transcript of the combined statement. -/
theorem batched_soundness_of_rounds_eq (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Stmt Salt W : Type} [DecidableEq Stmt] [DecidableEq Salt]
    (stm : Stmt → BStmt ω m)
    (R : List Round) (e : batchRound S :: (friAltP (ω := ω) s d l Dg).rounds = R)
    (guards : GuardSchedule (Stmt × Salt) PUnit R)
    (acc : Stmt × Salt → (protocol R).tree.ExecutionPath → Bool)
    (hacc : ∀ z p (p' : (protocol (batchRound S :: (friAltP (ω := ω) s d l Dg).rounds)).tree.ExecutionPath),
      castPath e p' = p → acc z p = true →
      queryBad s d l (round_bound hdom) (initialOracle s (combinedStmt s m G p'.2.1 (stm z.1)))
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          ((friAltP (ω := ω) s d l Dg).pathTranscript p'.2.2)))
    (adversary : SingleSaltAdversary Stmt Salt W R)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution R guards acc adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {st | stm st ∈ (inputRelation (ω := ω) s d m δ).language}] ≤
    bfriErr (ω := ω) s d l θ δ ε Q := by
  subst e
  classical
  have hs := round_bound hdom
  have h := singleSalt_soundness_cons (friAltP (ω := ω) s d l Dg) (batchRound S)
    {st : Stmt | stm st ∈ (inputRelation (ω := ω) s d m δ).language}
    (fun st cs => friState s d l hs θ δ (combinedStmt s m G cs (stm st)))
    (fun st cs m' hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m' hm _ tr hb msg hafter)
    (ε : ℝ≥0∞) (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun st hnot => by
      refine le_trans (prEvent_mono _ _ _ ?_) (batching_error s d m G hdom δ ε hε (stm st) hnot)
      intro c hc
      rcases hc with hc | ⟨_, hi, _⟩
      · exact mem_inputLanguage_of_proximity s d hdom δ _ hc
      · exact absurd hi (Nat.not_lt_zero _))
    (fun st _ cs => friState_challengeLaw_all s d l hs θ δ _)
    guards acc adversary (fun _ _ _ => True)
    (fun z path _ hacc' _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr (hacc z path path rfl hacc')⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact (hbad : False).elim
  · exact ⟨hbad, trivial⟩

/-- the in-the-clear acceptance on base paths of `bMask`: FRI's `friAccepts` on the combined word of `stm z.1` (seed = the batching challenge) -/
noncomputable def bAccepts (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) {Stmt Salt : Type}
    (stm : Stmt → BStmt ω m)
    (z : Stmt × Salt) (q : (protocol (baseRounds Dg (bMask (S := S) s d l L Dg enc))).tree.ExecutionPath) : Bool :=
  friAccepts' s d l L Dg enc hdom (combinedStmt s m G q.2.1 (stm z.1), z.2) q.2.2

/-- **`fri_hclear_batched`**: the batched analogue of `fri_hclear`.  The hypothesis `hclear` of `merkle_singleSalt_soundness` over
`pairedRoundsK bMask` (with `pairGuards` and `pairAccepts bAccepts`), at the event `stm z.1 ∉ (inputRelation s d m δ).language`,
discharged with `bfriErr`.  Route: prepend `batchRound` via `singleSalt_soundness_cons` (`consExt`) onto `friAltP`. -/
theorem fri_hclear_batched (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Stmt Salt W : Type} [DecidableEq Stmt] [DecidableEq Salt]
    (stm : Stmt → BStmt ω m)
    (Op : Type) [Finite Op] [DecidableEq Op]
    (guards : GuardSchedule (Stmt × Salt) PUnit (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc)))
    (B : SingleSaltAdversary Stmt Salt W (pairedRoundsK Dg (bMask (S := S) s d l L Dg enc)))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (bMask (S := S) s d l L Dg enc))
        (pairGuards Dg Op (bMask (S := S) s d l L Dg enc) guards)
        (pairAccepts Dg (bMask (S := S) s d l L Dg enc)
          (bAccepts s d l m G L Dg enc hdom stm (Salt := Salt))) B) ∅}[
      match j.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {st | stm st ∈ (inputRelation (ω := ω) s d m δ).language}] ≤
    bfriErr (ω := ω) s d l θ δ ε Q := by
  have e : batchRound S :: (friAltP (ω := ω) s d l Dg).rounds = pairedRoundsK Dg (bMask (S := S) s d l L Dg enc) :=
    congrArg (_ :: ·) (friAltP_rounds s d l L Dg enc)
  refine le_trans (prEvent_mono _ _ _ ?_) (batched_soundness_of_rounds_eq s d l m G Dg hdom θ δ ε hε stm _ e
    (pairGuards Dg Op (bMask (S := S) s d l L Dg enc) guards)
    (pairAccepts Dg (bMask (S := S) s d l L Dg enc) (bAccepts s d l m G L Dg enc hdom stm (Salt := Salt)))
    (fun z p p' hpp hacc => ?_) B Q queryBound)
  · rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
    · exact hb
    · exact hb
  obtain ⟨h1, h2, h3⟩ := castPath_cons (r := batchRound S) (r' := batchRound S) rfl
    (friAltP_rounds s d l L Dg enc) e p' p hpp
  have e2 := eq_of_heq h2
  rw [e2]
  have key := pairAccepts_friAccepts'_imp s d l L Dg enc hdom
    (combinedStmt s m G p.2.1 (stm z.1), z.2) p.2.2 hacc
  have hq : castPath (friAltP_rounds s d l L Dg enc).symm p.2.2 = p'.2.2 := by
    rw [← h3]; unfold castPath; rw [cast_cast]; exact cast_eq _ _
  rw [hq] at key
  exact key

/-! ## 3. The query-only law and the local check (the 7-5 seam) -/

/-- the compiled FRI-layer local check at `bMask`: the clear batching challenge gives the combined statement; FRI's local check on the tail.
A witness that `hlocal` is satisfiable; 7-5 replaces it by the flat verifier's check. -/
noncomputable def bLocal (Op : Type) [Finite Op] [DecidableEq Op] (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    {Stmt Salt : Type} (stm : Stmt → BStmt ω m)
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s d l L Dg enc)))
    (z : Stmt × Salt)
    (p : (protocol (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc))).tree.ExecutionPath) : Bool :=
  friLocal s d l L Dg enc Op hdom decode (combinedStmt s m G p.2.1 (stm z.1), z.2) p.2.2

/-- **query-only at `bMask`**: from `fri_queryOnly` at the tail, with the statement read off the (clear, agreed) batching challenge. -/
theorem bMask_queryOnly (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (Op : Type) [Finite Op] [DecidableEq Op] {Stmt Salt : Type} (stm : Stmt → BStmt ω m)
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s d l L Dg enc))) :
    QueryOnly (bMask (S := S) s d l L Dg enc) decode
      (bAccepts s d l m G L Dg enc hdom stm (Salt := Salt))
      (bLocal s d l m G L Dg enc Op hdom stm decode) := by
  intro z p q hag hl
  obtain ⟨-, h2, hag'⟩ := hag
  unfold bAccepts
  rw [← h2]
  exact fri_queryOnly s d l L Dg enc Op hdom decode (combinedStmt s m G p.2.1 (stm z.1), z.2) p.2.2 q.2.2 hag' hl

/-! ## 4. The Merkle compilation of the FRI-layer trees -/

/-- **`side_merkle_singleSalt_soundness`**: `merkle_singleSalt_soundness` at the batched FRI mask `bMask` (the `k` FRI layer trees),
for any statement map `stm`.  Probability that the compiled path accepts (`succinctAcceptedExecutionK`, local check `localAccepts`)
but `stm z.1` is not in batched FRI's input language, at most
`bfriErr Q_FS + multiCheckpointROMErrorNumerator(k (Q_FS+1) P, k (Q_FS+1), V, Q_H) / |Dg|`  (= term (b) of `εfix` plus the batched FRI term).
`hpos` is `1 ≤ k` (`hpos_bMask`).  SEAM (7-5): `localAccepts` with `hlocal`; `bMask_queryOnly` is the instance `localAccepts := bLocal`. -/
theorem side_merkle_singleSalt_soundness [SampleableType Dg] [Inhabited Dg] (hk : 1 ≤ k)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
    {Stmt Salt W : Type} [DecidableEq Stmt] [DecidableEq Salt]
    (stm : Stmt → BStmt ω m)
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s d l L Dg enc)))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (bMask (S := S) s d l L Dg enc))) Dg)
    (guards : GuardSchedule (Stmt × Salt) PUnit (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc)))
    (localAccepts : Stmt × Salt → (protocol (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc))).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly (bMask (S := S) s d l L Dg enc) decode
      (bAccepts s d l m G L Dg enc hdom stm (Salt := Salt)) localAccepts)
    (A : SuccinctAdversaryK Dg Op Query Stmt Salt W (bMask (S := S) s d l L Dg enc)) (Q_FS Q_H V P : ℕ)
    (hFS : FsBound (Q := Query)
      (∅ : (ofFn (KC Dg Op Stmt Salt (bMask (S := S) s d l L Dg enc))).QueryCache) Q_FS (verifiedFS guards A))
    (hH : IsQueryBoundP A (@isHashQuery Query Dg _ (KC Dg Op Stmt Salt (bMask (S := S) s d l L Dg enc))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (bMask (S := S) s d l L Dg enc)).length) (op : Op)
      (logs : Fin (merkleSkels (bMask (S := S) s d l L Dg enc)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (bMask (S := S) s d l L Dg enc)) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (bMask (S := S) s d l L Dg enc))).nodeBudget tag ≤ P) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (bMask (S := S) s d l L Dg enc)) model decode) localAccepts A) ∅}[
      match j.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {st | stm st ∈ (inputRelation (ω := ω) s d m δ).language}] ≤
    bfriErr (ω := ω) s d l θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) *
        (Nat.card Dg : ℝ≥0∞)⁻¹ := by
  have h := merkle_singleSalt_soundness (bMask (S := S) s d l L Dg enc) (hpos_bMask s d l L Dg enc hk) decode model guards
    (bAccepts s d l m G L Dg enc hdom stm (Salt := Salt)) localAccepts hlocal
    {st | stm st ∈ (inputRelation (ω := ω) s d m δ).language} (bfriErr (ω := ω) s d l θ δ ε)
    (fun B Q hQ => by
      refine le_trans (prEvent_mono _ _ _ ?_) (fri_hclear_batched s d l m G L Dg enc hdom θ δ ε hε stm Op guards B Q hQ)
      rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
      · exact hb
      · exact hb)
    A Q_FS Q_H V P hFS hH hterm hconfig
  rw [merkleSkels_bMask_length] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

/-! ## 5. The side statement -/

open NockvmE2E.Exec NockvmE2E.Exec.V in
set_option maxHeartbeats 4000000 in
/-- **`sideStmt_merkle_soundness`**: the composition.  The adversary outputs `SideStmt`s; the FRI words are those of
`stmtOf C hn z.1` (DEEP words of the honest spec words at the claimed values).  The probability that the compiled side path
accepts although `stmtOf C hn z.1` is not in batched FRI's input language is at most `bfriErr + term (b)`, in the lazy
`randomOracleLoggedRun` form.  SEAM (7-5): `localAccepts`/`hlocal`.  Left out: eager ⇒ lazy and the flat glue (7-5), the VK tree (7-4). -/
theorem sideStmt_merkle_soundness {m : ℕ} (C : SideCfg m) (hn : C.XI.nD ≤ 32) {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
    [∀ j, SampleableType ((pSpec k (ω := smoothDomain C.XI.nD hn) s l).Challenge j)]
    {S : Type} [Fintype S] [Nonempty S] [SampleableType S] [SampleableType KC]
    (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
    (L : FriLeaves (ω := smoothDomain C.XI.nD hn) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg]
    (enc : KC ↪ Dg) (hk : 1 ≤ k)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ C.XI.nD) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code ((smoothDomain C.XI.nD hn : SmoothCosetFftDomain C.XI.nD KC) : Fin (2 ^ C.XI.nD) ↪ KC)
        (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
    {Salt W : Type} [DecidableEq SideStmt] [DecidableEq Salt]
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s d l L Dg enc)))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (bMask (S := S) s d l L Dg enc))) Dg)
    (guards : GuardSchedule (SideStmt × Salt) PUnit (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc)))
    (localAccepts : SideStmt × Salt → (protocol (compiledRoundsK Dg Op (bMask (S := S) s d l L Dg enc))).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly (bMask (S := S) s d l L Dg enc) decode
      (bAccepts s d l m G L Dg enc hdom (stmtOf C hn) (Salt := Salt)) localAccepts)
    (A : SuccinctAdversaryK Dg Op Query SideStmt Salt W (bMask (S := S) s d l L Dg enc)) (Q_FS Q_H V P : ℕ)
    (hFS : FsBound (Q := Query)
      (∅ : (ofFn (KC Dg Op SideStmt Salt (bMask (S := S) s d l L Dg enc))).QueryCache) Q_FS (verifiedFS guards A))
    (hH : IsQueryBoundP A (@isHashQuery Query Dg _ (KC Dg Op SideStmt Salt (bMask (S := S) s d l L Dg enc))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (bMask (S := S) s d l L Dg enc)).length) (op : Op)
      (logs : Fin (merkleSkels (bMask (S := S) s d l L Dg enc)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount
        (mkClaims (merkleSkels (bMask (S := S) s d l L Dg enc)) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (bMask (S := S) s d l L Dg enc))).nodeBudget tag ≤ P) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (bMask (S := S) s d l L Dg enc)) model decode) localAccepts A) ∅}[
      match j.1.1 with
      | none => False
      | some (z, _, _) => stmtOf C hn z.1 ∉ (inputRelation (ω := smoothDomain C.XI.nD hn) s d m δ).language] ≤
    bfriErr (ω := smoothDomain C.XI.nD hn) s d l θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) *
        (Nat.card Dg : ℝ≥0∞)⁻¹ := by
  have h := side_merkle_singleSalt_soundness s d l m G L Dg enc hk hdom θ δ ε hε (stmtOf C hn) decode model guards localAccepts hlocal
    A Q_FS Q_H V P hFS hH hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end NockvmE2E.Merkle.SideMerkle

#print axioms NockvmE2E.Merkle.SideMerkle.fri_hclear_batched
#print axioms NockvmE2E.Merkle.SideMerkle.bMask_queryOnly
#print axioms NockvmE2E.Merkle.SideMerkle.merkleSkels_bMask_eq
#print axioms NockvmE2E.Merkle.SideMerkle.side_merkle_singleSalt_soundness
#print axioms NockvmE2E.Merkle.SideMerkle.sideStmt_merkle_soundness
