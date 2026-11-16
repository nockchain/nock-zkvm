/-
  NockvmE2E/Exec/SideStmt.lean   (pcs,  1.2-1.3; KERNEL-checked)

  The side statement of the verification-key proof and what batched FRI over it proves.
    * `SideStmt`            = (z, ctx, vF), the FS prefix of `fixMsgs` (messages 0 and 1; ctx carries zeta);
    * `sideRounds_*`        : the side rounds `(.,cs),(.,alpha0),(f_w,alpha_w).., (pfinal,xs)` ARE `batchedRounds`, and the challenge widths of
                              `fixMsgs`/`fixNl` are those rounds (3, 3, 3 x k, l);
    * `stmtOf cfg s`        : the batched-FRI statement of a side statement: the input words are the DEEP words of the HONEST spec words
                              (`specWord`, a fixed oracle) at the claimed values;
    * `batchedFri_sideStmt_soundness` : `FriPort/SideFri.lean batchedFri_stmtOf_soundness` at `stmtOf` (same bound as `batchedFri_singleSalt_soundness`);
    * `vF_correct_of_language`        : `stmtOf s` in the input language + opening points off the domain => every claimed value is `fixTrue`.
  No axiom, no `sorry`.
-/
import NockvmE2E.Exec.VKSpec
import NockvmE2E.Exec.Inst
import NockvmE2E.Deep.UDFri
import NockvmE2E.FriPort.SideFri

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.Inst
open NockvmE2E.Deep NockvmE2E.FriPort.Batched Domain Polynomial
open scoped NNReal ENNReal

/-! ### 1. the side statement and the side rounds -/

/-- the side statement: the Fiat-Shamir prefix of `fixMsgs` that is NOT a prover message of the FRI part:
message 0 = `ctx` (the four main block roots and `zeta`), message 1 = the claimed values `vF`; and the statement `z` -/
structure SideStmt where
  z : List Nat
  ctx : List Nat
  vF : Array (Array VF.K3)

/-- the first two messages of `fixMsgs` are exactly the side statement (ctx, vF) -/
theorem fixMsgs_stmt_prefix (k : Nat) (st : SideStmt) (roots : Array Dg5) (pfinal : Array VF.K3) :
    (fixMsgs k st.ctx st.vF roots pfinal)[0]? = some st.ctx ∧
    (fixMsgs k st.ctx st.vF roots pfinal)[1]? = some (st.vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs)) := by
  simp [fixMsgs]

/-- the messages after the statement are the batched-FRI messages: `[]` (the batching round has no prover message), the `k` FRI roots,
`pfinal` (`k + 4` messages in all) -/
theorem fixMsgs_size (k : Nat) (ctx : List Nat) (vF : Array (Array VF.K3)) (roots : Array Dg5) (pfinal : Array VF.K3)
    (hr : roots.size = k) : (fixMsgs k ctx vF roots pfinal).size = k + 4 := by
  simp [fixMsgs, hr]; omega

/-- the challenge widths of the side verifier: round `i` (`1 <= i <= k + 3`) has `fixNl k l i` limbs: `cs`, `alpha_0..alpha_k` are `K3`
(3 limbs), the query challenge `xs` has `l` limbs.  This is the shape `0 :: replicate (k+2) 3 ++ [l]`, i.e. `k + 3` challenges. -/
theorem fixNl_profile (k l : Nat) :
    (List.range (k + 4)).map (fixNl k l) = 0 :: (List.replicate (k + 2) 3 ++ [l]) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rcases i with _ | i
    · simp [fixNl]
    · rw [List.getElem_cons_succ]
      by_cases h : i < k + 2
      · rw [List.getElem_append_left (by simpa using h), List.getElem_replicate]
        simp only [fixNl, beq_iff_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
        split_ifs <;> first | rfl | omega
      · have hi : i = k + 2 := by omega
        subst hi
        rw [List.getElem_append_right (by simp)]
        simp
        unfold fixNl
        simp
        split_ifs <;> first | rfl | omega

section Rounds
open Interaction.Oracle Fri.Spec NockvmE2E.FriPort
variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]

/-- **the side rounds are `batchedRounds`**: `(Unit, cs)` (no prover message, seed `cs`), then FRI's native rounds
`(Unit, alpha_0), (f_1, alpha_1), .., (f_k, alpha_k), (pfinal, xs)` -/
theorem sideRounds_eq : batchedRounds (ω := ω) (S := S) s d l = batchRound S :: friRounds (ω := ω) s d l := rfl

/-- `k + 3` rounds = the `k + 3` nonzero challenge slots of `fixNl` (`cs`, `alpha_0..alpha_k`, `xs`) -/
theorem sideRounds_length : (batchedRounds (ω := ω) (S := S) s d l).length = k + 3 := by
  rw [sideRounds_eq, List.length_cons, friRounds_length]

end Rounds

/-! ### 2. `stmtOf`: the batched-FRI statement of a side statement -/

/-- the configuration that turns a side statement into batched openings: the instance, the `m + 1` openings `(column rank j, point index o)`,
and the opening points as a function of `ctx` (`openPts X zeta [o]`, `zeta` read from `ctx`).  Nothing here is a hypothesis: any such
functions are a configuration. -/
structure SideCfg (m : ℕ) where
  XI : ExecInst
  opIdx : Fin (m + 1) → ℕ × ℕ
  ptK : List Nat → Fin (m + 1) → VF.K3

variable {m : ℕ}

/-- the fixed column of opening `j` -/
def SideCfg.col (C : SideCfg m) (j : Fin (m + 1)) : FixCol := (fixCols C.XI)[(C.opIdx j).1]!

/-- the claimed value of opening `j` (read in `KC`) -/
noncomputable def SideCfg.val (C : SideCfg m) (st : SideStmt) (j : Fin (m + 1)) : KC :=
  toKV ((st.vF[(C.opIdx j).1]!)[(C.opIdx j).2]!)

/-- the opening point of opening `j` (read in `KC`) -/
noncomputable def SideCfg.pt (C : SideCfg m) (st : SideStmt) (j : Fin (m + 1)) : KC := toKV (C.ptK st.ctx j)

/-- the HONEST committed word of a fixed column: the spec LDE, `i |-> specWord XI col i` (a fixed oracle, not a prover message) -/
noncomputable def honestWord (XI : ExecInst) (col : FixCol) : Fin (2 ^ XI.nD) → KC := fun i => psiV (specWord XI col i.1)

/-- **`stmtOf`**: the batched-FRI statement of a side statement: the words are the DEEP quotient words `(w_{col j} - v_j)/(X - pt_j)`
of the honest spec words `w` at the claimed values `v_j` -/
noncomputable def stmtOf (C : SideCfg m) (hn : C.XI.nD ≤ 32) (st : SideStmt) : BStmt (smoothDomain C.XI.nD hn) m :=
  ((), fun j x => NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j)
    ((smoothDomain C.XI.nD hn).equivToFinset.symm x))

theorem stmtOf_words (C : SideCfg m) (hn : C.XI.nD ≤ 32) (st : SideStmt) (j : Fin (m + 1)) (i : Fin (2 ^ C.XI.nD)) :
    (stmtOf C hn st).2 j ((smoothDomain C.XI.nD hn).equivToFinset i) =
      NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j) i := by
  show NockvmE2E.Deep.deepWord _ _ _ _ (((smoothDomain C.XI.nD hn).equivToFinset).symm ((smoothDomain C.XI.nD hn).equivToFinset i)) = _
  rw [Equiv.symm_apply_apply]

/-! ### 3. batched FRI over `SideStmt` -/

section Fri
open OracleComp OracleSpec ProtocolSpec Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir Fri.Spec BatchedFri.Spec BatchedFri.Spec.BatchingRound

variable {k : ℕ} [SampleableType KC]

/-- **Batched FRI over `SideStmt`.**  A single-salt adversary outputs `SideStmt`s (z, ctx, vF); the FRI words are those of `stmtOf C z.1`
(the DEEP words of the honest spec words at the claimed values).  The probability that it outputs an accepted proof although
`stmtOf C z.1` is not in batched FRI's input language is at most `bfriErr` (the right-hand side of
`batchedFri_singleSalt_soundness`).  Hypotheses are those of that theorem (`hdom`, `hε`, the generator `G`, the query bound). -/
theorem batchedFri_sideStmt_soundness (C : SideCfg m) (hn : C.XI.nD ≤ 32)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
    [∀ j, SampleableType ((pSpec k (ω := smoothDomain C.XI.nD hn) s l).Challenge j)]
    {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
    (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ C.XI.nD)
    (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code ((smoothDomain C.XI.nD hn : SmoothCosetFftDomain C.XI.nD KC) : Fin (2 ^ C.XI.nD) ↪ KC)
        (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Salt W : Type} [DecidableEq SideStmt] [DecidableEq Salt]
    (guards : GuardSchedule (SideStmt × Salt) PUnit
      (batchedRounds (ω := smoothDomain C.XI.nD hn) (S := S) s d l))
    (adversary : SingleSaltAdversary SideStmt Salt W
      (batchedRounds (ω := smoothDomain C.XI.nD hn) (S := S) s d l))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution (batchedRounds (ω := smoothDomain C.XI.nD hn) (S := S) s d l) guards
        (stmAccepts s d l m G (stmtOf C hn) hdom) adversary) ∅)}[
      badOpt (stmtOf C hn) (inputRelation (ω := smoothDomain C.XI.nD hn) s d m δ).language joint.1.1.1] ≤
    Q * ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j =>
        (challengeError (ω := smoothDomain C.XI.nD hn) s d l θ δ j : ℝ≥0∞))) +
      ((ε : ℝ≥0∞) +
        (((∑ i, foldingError (ω := smoothDomain C.XI.nD hn) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞)) :=
  batchedFri_stmtOf_soundness s d l m G (stmtOf C hn) hdom θ δ ε hε guards adversary Q queryBound

end Fri

/-! ### 4. language => the claimed values are the true evaluations -/

section Correct
variable {k : ℕ}

theorem dense_univ {ι : Type} [Fintype ι] (δ : ℝ≥0) : Deep.Dense δ (Finset.univ : Finset ι) := by
  unfold Deep.Dense
  rw [Finset.card_univ]
  exact mul_le_of_le_one_left (by positivity) tsub_le_self

/-- the honest word is the evaluation of `f_j` on the domain -/
theorem honestWord_eval (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L : DomLink XI hn)
    (col : FixCol) (i : Fin (2 ^ XI.nD)) :
    honestWord XI col i = eval (smoothDomain XI.nD hn i) ((fj XI col).map (algebraMap (ZMod NockvmE2E.Exec.p) KC)) := by
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  have h1 := specWord_eval XI hS hpre col i.1
  unfold honestWord psiV
  rw [h1, hω_of_domLink XI hn L i, Polynomial.eval_map_algebraMap]
  unfold psiV
  rw [← map_pow, ← map_mul, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]

/-- **language => `vF` correct.**  Let `stmtOf C st` be in batched FRI's input language `inputRelation s d m δ`, every opening
point off the domain (`OffDom`, a verifier check), the FRI degree bound `friBound s d` at least `2^(k+1) >= deg f_j`
(`natDegree_fj_le_J8`), `friBound + 1 <= 2^nD`, and `delta` within the unique-decoding radius.  Then every claimed value is
the true evaluation of the fixed polynomial: `v_j = fixTrue (col j) (pt_j)`.
Route: `deep_of_inputRelation` (one polynomial `P_j`, delta-close to the honest word, `P_j(pt_j) = v_j`); the honest word is `f_{col j}` on the whole
domain and `deg f <= friBound`, so unique decoding gives `P_j = f_{col j}`; `fixTrue_eq_fj`. -/
theorem vF_correct_of_language (C : SideCfg m) (hg : setupGates C.XI = true) (hsh : J8Shape.j8ShapeOk C.XI = true)
    (hn : C.XI.nD ≤ 32) {s : Fin (k + 1) → ℕ+} {d : ℕ+} {δ : ℝ≥0}
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s d) (hN : friBound s d + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s d + 1) : Set (Fin (2 ^ C.XI.nD) → KC)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    (st : SideStmt) (hcanon : ∀ j, canon3 (C.ptK st.ctx j))
    (hz : ∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt st j)
    (hmem : stmtOf C hn st ∈ (BatchedFri.Spec.BatchingRound.inputRelation (ω := smoothDomain C.XI.nD hn) s d m δ).language) :
    ∀ j, C.val st j = toKV (fixTrue C.XI (C.col j) (C.ptK st.ctx j)) := by
  obtain ⟨sw, hsw, hsw1⟩ := hmem
  have L : DomLink C.XI hn := J8Shape.domLink_of_paramsOk C.XI (J8Shape.paramsOk_of_shape hsh) hn
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  have hwords : ∀ j i, sw.1.2 j ((smoothDomain C.XI.nD hn).equivToFinset i) =
      NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j) i := by
    intro j i
    rw [hsw1]; exact stmtOf_words C hn st j i
  obtain ⟨P, ⟨S, hS', hA⟩, hdeg, hop, huniq⟩ := deep_of_inputRelation (m := m) (s := s) (d := d)
    (ω := smoothDomain C.XI.nD hn) (id : Fin (m + 1) → Fin (m + 1)) (C.pt st) (C.val st)
    (fun j => honestWord C.XI (C.col j)) Function.surjective_id hz hN hδ sw hsw hwords
  intro j
  have hmemc : C.col j ∈ fixCols C.XI := by
    unfold SideCfg.col
    rw [getElem!_pos (fixCols C.XI) (C.opIdx j).1 (hcol j)]
    exact Array.getElem_mem _
  have hdegf : ((fj C.XI (C.col j)).map (algebraMap (ZMod NockvmE2E.Exec.p) KC)).natDegree < friBound s d + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod NockvmE2E.Exec.p) KC).injective]
    exact Nat.lt_succ_of_le ((natDegree_fj_le_J8 hsh _ hmemc).trans hfb)
  have hPe := huniq j _ Finset.univ hdegf (dense_univ δ)
    (fun i _ => honestWord_eval C.XI hg hn L (C.col j) i)
  rw [show P j = P (id j) from rfl] at hPe; rw [← hop j, ← hPe, fixTrue_eq_fj C.XI hS hpre (C.col j) _ (hcanon j)]
  rfl

end Correct

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.batchedFri_sideStmt_soundness
#print axioms NockvmE2E.Exec.V.vF_correct_of_language
#print axioms NockvmE2E.Exec.V.fixNl_profile
#print axioms NockvmE2E.Exec.V.sideRounds_length
#print axioms NockvmE2E.Exec.V.fixMsgs_size
