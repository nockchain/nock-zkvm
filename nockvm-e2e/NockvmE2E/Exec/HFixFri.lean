/-
  NockvmE2E/Exec/HFixFri.lean   (pcs,  1.2-1.3; KERNEL-checked unless labelled)

  Assembly of `hFix` for the FRI + Merkle side proof.
  Section 1: `VKcoll` (the VK-tree binding failure, concrete;  discharges `hcoll` about it).
  Later sections: `hFix_fri`, `exec_e2e_J8V''`, numbers.
-/
import NockvmE2E.Exec.VKSpec
import NockvmE2E.Exec.SideStmt
import NockvmE2E.Merkle.SideMerkle
import NockvmE2E.Exec.E2EOnlineP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.VF NockvmE2E.Exec.VL

/-! ### 1. `VKcoll`: the VK-tree (tree 0) binding failure -/

/-- the side proof laid out as a `FlatProof` (tree 0 = the VK tree, trees 1..3 empty, then the `k` FRI trees): exactly the adapter `πa` of
`verifyFix`/`verifyFix'` -/
def fixAdapt (vk : VK) (πF : FixProof) : FlatProof :=
  let z5 : Dg5 := [0, 0, 0, 0, 0]
  { roots := #[vk.root, z5, z5, z5] ++ πF.roots, vT := #[], vQ := #[], pfinal := πF.pfinal, pos := πF.pos,
    vals := #[πF.vals[0]!, #[], #[], #[]] ++ πF.vals.extract 1 (1 + vk.X.k),
    sibs := #[πF.sibs[0]!, #[], #[], #[]] ++ πF.sibs.extract 1 (1 + vk.X.k) }

/-- the HONEST value of VK-tree leaf position `p` (row-major `g * 2F + s * F + r`: group `g`, side `s`, column rank `r`): the spec word of
column `r` at FRI index `g + s * half0`; this is the leaf layout of `specGroup`/`specSub`. -/
def honestLeaf (X0 : ExecInst) (F half0 p : Nat) : Nat :=
  (specWord X0 (fixCols X0)[(p % (2 * F)) % F]! (p / (2 * F) + ((p % (2 * F)) / F) * half0)).toNat

/-- **`VKcoll X0 vk Hf πF`**: the VK-tree (tree 0) check of `verifyFix'` PASSES against `vk.root` although some opened leaf differs from the honest
spec leaf.  This is the (semantic) binding failure of the VK tree: by collision resistance of `Hf` on the tree-0 nodes it forces two distinct
inputs with the same digest among {the nodes of the honest tree, the verifier's recomputation};  proves `Pr[VKcoll] ≤ (Q_Hf + Vf + T)²/(2|Dg|)`
(`hcoll` below). -/
def VKcoll (X0 : ExecInst) (vk : VK) (Hf : HFn) (πF : FixProof) : Prop :=
  let XV := vk.X
  let F := vk.cols.size
  let half0 := 2 ^ (XV.nD - 1)
  let sels : Array (Array Nat) := (Array.range (4 + XV.k)).map fun j =>
    if j == 0 then treeSel XV F 0 πF.pos else if j < 4 then #[] else treeSel XV 0 j πF.pos
  treeCheck XV Hf (fixAdapt vk πF) #[F, 0, 0, 0] half0 sels 0 = .ok () ∧
  ∃ r, r < (treeSel XV F 0 πF.pos).size ∧ (πF.vals[0]!)[r]! ≠ honestLeaf X0 F half0 ((treeSel XV F 0 πF.pos)[r]!)



/-! ### 2. eager tables: the main oracle fixed, the side oracle left -/

section Tables
open OracleComp OracleSpec ENNReal NockvmE2E.Exec.E2EOnlineP NockvmE2E.Exec.E2E

variable {D : Type} {R : D → Type} [DecidableEq D] {DF : Type} {RF : DF → Type} [DecidableEq DF] {O : Type}

/-- the main oracle answered from the table `g` (unif and side queries pass through), as a computation over the side oracle only -/
noncomputable def mainImpl (g : ∀ d, R d) :
    QueryImpl ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (OracleComp (unifSpec + OracleSpec.ofFn RF)) :=
  fun t => match t with
  | .inl (.inl n) => liftM ((unifSpec + OracleSpec.ofFn RF).query (.inl n))
  | .inl (.inr d) => pure (g d)
  | .inr d => liftM ((unifSpec + OracleSpec.ofFn RF).query (.inr d))

theorem sim_main (g : ∀ d, R d) (gF : ∀ d, RF d)
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O)) :
    simulateQ (withTable gF) (simulateQ (mainImpl g) A) = simulateQ (withTable2 g gF) A := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) A
  rcases t with (n | d) | d
  · simp [mainImpl, withTable2, withTable]
  · simp [mainImpl, withTable2, withTable]
    rfl
  · simp [mainImpl, withTable2, withTable]

/-- a bound on the inner two draws for every value of the first bounds the three-draw event -/
theorem triple_le {A B C : Type} (mx : ProbComp A) (f : A → ProbComp B) (h : A → B → ProbComp C) (P : A → B → C → Prop) (ε : ℝ≥0∞)
    (hh : ∀ a, Pr{let b ← f a; let c ← h a b}[P a b c] ≤ ε) :
    Pr{let a ← mx; let b ← f a; let c ← h a b}[P a b c] ≤ ε := by
  rw [NockvmE2E.Exec.E2EOnline.pr_triple]
  refine prEvent_bind_le_of_forall_le mx _ _ (fun a => ?_)
  have := hh a
  rw [NockvmE2E.Exec.E2EOnline.pr_pair] at this
  refine le_trans (le_of_eq ?_) this
  simp [prEvent_eq_evalDist_map]

end Tables

/-! ### 3. `hFix_fri` -/

section Assembly
open OracleComp OracleSpec ProtocolSpec ENNReal
open BinaryTree
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain NockvmE2E.FriPort NockvmE2E.FriPort.Batched NockvmE2E.Merkle.Fri
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good NockvmE2E.Merkle.SoundnessWorld
  NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.Merkle.BadBound
open MerkleTreeMultiExtractability
open NockvmE2E.Exec.Emb NockvmE2E.Exec.E2E NockvmE2E.Exec.E2EOnlineP NockvmE2E.Merkle.SideMerkle NockvmE2E.Deep NockvmE2E.Exec.Inst
open scoped NNReal ENNReal

/-- the side adversary of the compiled side protocol obtained from the online adversary `Aon` with the MAIN oracle fixed to the table `g`
(unif and side queries pass through, main queries are answered from `g`), its output re-packed by `sideOf` (the side statement, salt and
public messages that the side proof of `o` is in the compiled protocol; witness trivial) -/
noncomputable def sideAdv {D : Type} {R : D → Type} {O : Type} {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op]
    [DecidableEq Op] {Query Stmt Salt : Type} {ms : MRounds Dg}
    (sideOf : (∀ d, R d) → O → Stmt × Salt × PublicMessages (compiledRoundsK Dg Op ms))
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn (succinctRange Dg Op Query Stmt Salt ms)) (Option O))
    (g : ∀ d, R d) : SuccinctAdversaryK Dg Op Query Stmt Salt PUnit ms :=
  (Option.map fun o => ((sideOf g o).1, (sideOf g o).2, PUnit.unit)) <$>
    simulateQ (mainImpl (RF := succinctRange Dg Op Query Stmt Salt ms) g) Aon

section Main
variable {m : ℕ} {k : ℕ} {D : Type} {R : D → Type} [DecidableEq D] [instR : SampleableType (∀ d, R d)] {O : Type}

/-- **language ⇒ ¬FixFail'** (pointwise): a side statement whose `stmtOf` lies in batched FRI's input language cannot carry a wrong claimed value
(`vF_correct_of_language` + the injectivity of `toKV` on canonical values).  `hglue`-style hypotheses are inputs. -/
theorem fix_not_language (C : SideCfg m) (hn : C.XI.nD ≤ 32)
    (hg : setupGates C.XI = true) (hsh : J8Shape.j8ShapeOk C.XI = true)
    {s : Fin (k + 1) → ℕ+} {dd : ℕ+} {δ : ℝ≥0}
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s dd) (hN : friBound s dd + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s dd + 1) : Set (Fin (2 ^ C.XI.nD) → NockvmE2E.Exec.KC)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    (hC1 : ∀ j o, j < (fixCols C.XI).size → o < fixLen C.XI (fixCols C.XI)[j]! → ∃ i, C.opIdx i = (j, o))
    (hC2 : ∀ π ζ i, C.ptK (fixCtx π ζ) i = (openPts C.XI ζ)[(C.opIdx i).2]!)
    (π : FlatProof) (ζ : VF.K3) (πF : FixProof) (st : SideStmt) (hst : st = ⟨[], fixCtx π ζ, πF.vF⟩)
    (hcanon : ∀ j, canon3 (C.ptK st.ctx j))
    (hz : ∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt st j)
    (hcanV : ∀ j o', j < (fixCols C.XI).size → o' < fixLen C.XI (fixCols C.XI)[j]! →
      canon3 ((πF.vF[j]!)[o']!) ∧ canon3 (fixTrue C.XI (fixCols C.XI)[j]! ((openPts C.XI ζ)[o']!)))
    (j0 o0 : ℕ) (hj0 : j0 < (fixCols C.XI).size) (ho0 : o0 < fixLen C.XI (fixCols C.XI)[j0]!)
    (hne : (πF.vF[j0]!)[o0]! ≠ fixTrue C.XI (fixCols C.XI)[j0]! ((openPts C.XI ζ)[o0]!)) :
    stmtOf C hn st ∉ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language := by
  intro hmem
  have hv := vF_correct_of_language C hg hsh hn hfb hN hδ hcol st hcanon hz hmem
  obtain ⟨i, hi⟩ := hC1 j0 o0 hj0 ho0
  have h1 := hv i
  have e1 : C.val st i = toKV ((πF.vF[j0]!)[o0]!) := by
    unfold SideCfg.val; rw [hi, hst]
  have e2 : C.col i = (fixCols C.XI)[j0]! := by unfold SideCfg.col; rw [hi]
  have e3 : C.ptK st.ctx i = (openPts C.XI ζ)[o0]! := by rw [hst, hC2, hi]
  rw [e1, e2, e3] at h1
  obtain ⟨c1, c2⟩ := hcanV j0 o0 hj0 ho0
  exact hne (toKV_inj _ _ c1 c2 h1)

local notation "KCf" => NockvmE2E.Exec.KC

set_option maxHeartbeats 4000000 in
/-- **`hFix_fri`**.  For the compiled side protocol (batched FRI mask `bMask`, `k` FRI-layer trees) and an online adversary `Aon`
with oracle access to the main oracle (table `g`) and the side oracle (table `gF`, eager): the probability that some output passes `verifyFix'`
at the spec VK while claiming a wrong fixed-column value is at most
`bfriErr + (multiCheckpointROMErrorNumerator ..)/|Dg| + (Q_H + V + T)^2/(2|Dg|)`.
Route: split on `VKcoll`; on `¬VKcoll` the glue (`hglue`) makes the compiled path accept, `fix_not_language` makes the statement leave the
language, and `sideStmt` soundness (`side_merkle_singleSalt_soundness`, lazy) is transferred to the eager table by `pr_flat_le_audited`
(fixing `g`, simulating the main oracle from it, averaging over `g`).  NAMED hypotheses: `hglue` (7-5), `hcoll` (7-4), `hvk` (= `hspec`). -/
theorem hFix_fri (C : SideCfg m) (hn : C.XI.nD ≤ 32)
    (hg : setupGates C.XI = true) (hsh : J8Shape.j8ShapeOk C.XI = true)
    (s : Fin (k + 1) → ℕ+) (dd : ℕ+) (l : ℕ)
    [∀ j, SampleableType ((pSpec k (ω := smoothDomain C.XI.nD hn) s l).Challenge j)]
    {S : Type} [Fintype S] [Nonempty S] [SampleableType S] [SampleableType KCf]
    (G : CoreDefinitions.Generator S (Fin (m + 1)) KCf)
    (L : FriLeaves (ω := smoothDomain C.XI.nD hn) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg]
    (enc : KCf ↪ Dg) (hk : 1 ≤ k)
    (hdom : 2 ^ (∑ j, (s j).val) * dd.val ≤ 2 ^ C.XI.nD) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code ((smoothDomain C.XI.nD hn : SmoothCosetFftDomain C.XI.nD KCf) : Fin (2 ^ C.XI.nD) ↪ KCf)
        (2 ^ (∑ i, (s i).1) * dd)).carrier δ δ ≤ ε)
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s dd) (hN : friBound s dd + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s dd + 1) : Set (Fin (2 ^ C.XI.nD) → KCf)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query] [Finite Query]
    {Stmt Salt : Type} [DecidableEq Stmt] [DecidableEq Salt] [Finite Stmt] [Finite Salt]
    [instRF : SampleableType (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d')]
    (decS : Stmt → SideStmt)
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s dd l L Dg enc)))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (bMask (S := S) s dd l L Dg enc))) Dg)
    (guards : GuardSchedule (Stmt × Salt) PUnit (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc)))
    (localAccepts : Stmt × Salt →
      (protocol (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc))).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly (bMask (S := S) s dd l L Dg enc) decode
      (bAccepts s dd l m G L Dg enc hdom (fun st => stmtOf C hn (decS st)) (Salt := Salt)) localAccepts)
    (HfOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → HFn)
    (FSOf : (∀ d, R d) → FSFn)
    (FSfOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → FSFn)
    (vkOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → VK)
    (hvk : ∀ gF, vkOf gF = vkSpec C.XI (HfOf gF))
    (zO : O → List Nat) (πO : O → FlatProof) (πFO : O → FixProof)
    (sideOf : (∀ d, R d) → O → Stmt × Salt × PublicMessages (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc)))
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn R) +
      OracleSpec.ofFn (succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc))) (Option O))
    (Q_FS Q_H V P T : ℕ)
    (hFS : ∀ g, FsBound (Q := Query)
      (∅ : (ofFn (SoundnessWorld.KC Dg Op Stmt Salt (bMask (S := S) s dd l L Dg enc))).QueryCache) Q_FS
      (verifiedFS guards (sideAdv sideOf Aon g)))
    (hH : ∀ g, IsQueryBoundP (sideAdv sideOf Aon g)
      (@isHashQuery Query Dg _ (SoundnessWorld.KC Dg Op Stmt Salt (bMask (S := S) s dd l L Dg enc))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (bMask (S := S) s dd l L Dg enc)).length) (op : Op)
      (logs : Fin (merkleSkels (bMask (S := S) s dd l L Dg enc)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (bMask (S := S) s dd l L Dg enc)) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (bMask (S := S) s dd l L Dg enc))).nodeBudget tag ≤ P)
    (hC1 : ∀ j o, j < (fixCols C.XI).size → o < fixLen C.XI (fixCols C.XI)[j]! → ∃ i, C.opIdx i = (j, o))
    (hC2 : ∀ π ζ i, C.ptK (fixCtx π ζ) i = (openPts C.XI ζ)[(C.opIdx i).2]!)
    (hglue : ∀ g gF o,
      FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) →
        decS (sideOf g o).1 = ⟨[], fixCtx (πO o) (zetaOf C.XI (FSOf g) (zO o) (πO o)), (πFO o).vF⟩ ∧
        (∀ j, canon3 (C.ptK (decS (sideOf g o).1).ctx j)) ∧
        (∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt (decS (sideOf g o).1) j) ∧
        (∀ j o', j < (fixCols C.XI).size → o' < fixLen C.XI (fixCols C.XI)[j]! →
          canon3 ((πFO o).vF[j]!)[o']! ∧
          canon3 (fixTrue C.XI (fixCols C.XI)[j]! ((openPts C.XI (zetaOf C.XI (FSOf g) (zO o) (πO o)))[o']!))) ∧
        (¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o) →
          ∃ p, tabEval (tabK gF) (succinctVerifyK guards
            (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
            ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2) = some (some p)))
    (hcoll : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
        match o with
        | none => False
        | some o => VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] ≤ ((Q_H + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞))) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤
    bfriErr (ω := smoothDomain C.XI.nD hn) s dd l θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ +
      ((Q_H + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞)) := by
  classical
  have hX : ∀ gF, (vkOf gF).cols = fixCols C.XI := fun gF => by rw [hvk]; rfl
  let stm : Stmt → BStmt (smoothDomain C.XI.nD hn) m := fun st => stmtOf C hn (decS st)
  -- pointwise (the hpt of E2E.exec_e2e_of_pointwise): a FixFail' that is not a VKcoll is an accepted compiled side path whose statement leaves the language
  have hpt : ∀ g gF o,
      (FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)) →
      (∃ p, tabEval (tabK gF) (succinctVerifyK guards
            (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
            ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2) = some (some p)) ∧
      (sideOf g o).1 ∉ {st | stm st ∈ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language} := by
    intro g gF o ⟨hF, hnc⟩
    obtain ⟨hstm, hcan, hz, hcanV, hacc⟩ := hglue g gF o hF
    refine ⟨hacc hnc, ?_⟩
    obtain ⟨_, j0, o0, hj0, ho0, hne⟩ := hF
    have hc := (hX gF)
    rw [hc] at hj0 ho0 hne
    exact fix_not_language C hn hg hsh hfb hN hδ hcol hC1 hC2 (πO o) (zetaOf C.XI (FSOf g) (zO o) (πO o)) (πFO o)
      (decS (sideOf g o).1) hstm hcan hz hcanV j0 o0 hj0 ho0 hne
  -- one main table: eager side table => lazy side oracle
  have hper : ∀ g : (∀ d, R d),
      Pr{let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
        match o with
        | none => False
        | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] ≤
      bfriErr (ω := smoothDomain C.XI.nD hn) s dd l θ δ ε Q_FS +
        (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by
    intro g
    have hre : ∀ gF, simulateQ (withTable2 g gF) Aon = simulateQ (withTable gF) (simulateQ (mainImpl g) Aon) :=
      fun gF => (sim_main g gF Aon).symm
    simp only [hre]
    let cont : Option O → OracleComp (SuccinctSpecK Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc))
        (Option ((Stmt × Salt) × (protocol (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc))).tree.ExecutionPath × PUnit)) :=
      fun o => match o with
        | none => pure none
        | some o => do
            let path ← succinctVerifyK guards (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
              ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2
            pure (path.map fun p => (((sideOf g o).1, (sideOf g o).2.1), p, PUnit.unit))
    have hshape : succinctAcceptedExecutionK guards (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
        (sideAdv sideOf Aon g) = simulateQ (mainImpl g) Aon >>= cont := by
      simp only [succinctAcceptedExecutionK, sideAdv, map_eq_bind_pure_comp, bind_assoc, bind_pure_comp]
      refine bind_congr fun o => ?_
      cases o <;> rfl
    refine le_trans (pr_flat_le_audited (simulateQ (mainImpl g) Aon) cont
      (fun gF o => match o with
        | none => False
        | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o))
      (fun c => match c with
        | none => False
        | some (z, _, _) => z.1 ∉ {st | stm st ∈ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language}) ?_) ?_
    · intro gF o hE
      rcases o with _ | o
      · exact hE.elim
      · obtain ⟨⟨p, hp⟩, hnot⟩ := hpt g gF o hE
        refine ⟨some (((sideOf g o).1, (sideOf g o).2.1), p, PUnit.unit), ?_, hnot⟩
        simp only [cont, simulateQ_bind, simulate_of_tabEval gF _ _ hp, pure_bind, simulateQ_pure]
        rfl
    · rw [← hshape]
      have h := side_merkle_singleSalt_soundness s dd l m G L Dg enc hk hdom θ δ ε hε stm decode model guards localAccepts hlocal
        (sideAdv sideOf Aon g) Q_FS Q_H V P (hFS g) (hH g) hterm hconfig
      refine le_trans (prEvent_mono _ _ _ ?_) h
      rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
      · exact hb
      · exact hb
  -- average over the main table, then the union bound with the collision event
  let M : ProbComp ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) :=
    do let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon; pure (g, gF, o)
  let Pfx : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => FixFail' C.XI (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o)
  let Pnc : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => FixFail' C.XI (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf x.2.1) (HfOf x.2.1) (πFO o)
  let Pcl : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => VKcoll C.XI (vkOf x.2.1) (HfOf x.2.1) (πFO o)
  have e1 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] = Pr{let x ← M}[Pfx x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))
  have e2 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] = Pr{let x ← M}[Pnc x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o))
  have e3 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] = Pr{let x ← M}[Pcl x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o))
  have hnc := triple_le ($ᵗ (∀ d, R d)) (fun _ => $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'))
    (fun g gF => simulateQ (withTable2 g gF) Aon) (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFail' C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)) _ hper
  rw [e2] at hnc
  rw [e3] at hcoll
  have hmono : Pr{let x ← M}[Pfx x] ≤ Pr{let x ← M}[Pnc x ∨ Pcl x] := by
    refine prEvent_mono_of_support M Pfx _ ?_
    rintro ⟨g, gF, o⟩ _ h
    rcases o with _ | o
    · exact absurd h id
    · by_cases hc : VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)
      · exact Or.inr hc
      · exact Or.inl ⟨h, hc⟩
  rw [e1]
  exact hmono.trans ((prEvent_or_le M Pnc Pcl).trans (add_le_add hnc hcoll))

end Main

end Assembly


end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.VKcoll
#print axioms NockvmE2E.Exec.V.sim_main
#print axioms NockvmE2E.Exec.V.triple_le
#print axioms NockvmE2E.Exec.V.fix_not_language
#print axioms NockvmE2E.Exec.V.hFix_fri
