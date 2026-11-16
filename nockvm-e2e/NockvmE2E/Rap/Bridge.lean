/-
RAP-PORT, part 3b: the bridge.

`SoundG` (the pointwise premise of the nockvm library's `standaloneG_of_sound`, twinned in `Rap/Frame.lean`) plus
column-locality of every summand ⇒ a round-by-round knowledge certificate, in Quang Dao's native format,
for the staged-RAP protocol `rapRounds` of `Rap/Protocol.lean`, with per-round error the part of
`epsilonOf` priced on that round's coin block. The extractor is trivial (witness `PUnit`, every map `id`);
the knowledge state is "`Holds`, or some summand whose coins are all sampled has fired".
The certificate is then fed, unchanged, to `singleSalt_knowledge_soundness`. 
-/
import NockvmE2E.Rap.Protocol
import ArkLibFs.Interaction.Oracle.FiatShamir.SingleSaltSecurity

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Rap

/-! ## 1. Counting and union bounds -/

section Bounds

/-- Union bound over a list, keeping only the members selected by `c`. -/
theorem prEvent_list_exists_le {α γ : Type} (mx : ProbComp α) (c : γ → Prop) [DecidablePred c]
    (Q : γ → α → Prop) :
    ∀ L : List γ, Pr{let x ← mx}[∃ s ∈ L, c s ∧ Q s x] ≤
      (L.map fun s => if c s then Pr{let x ← mx}[Q s x] else 0).sum
  | [] => by
    rw [prEvent_eq_zero_of_forall_not mx _ (fun x h => by simp at h)]
    exact zero_le
  | a :: L => by
    have hor : Pr{let x ← mx}[∃ s ∈ a :: L, c s ∧ Q s x] ≤
        Pr{let x ← mx}[c a ∧ Q a x] + Pr{let x ← mx}[∃ s ∈ L, c s ∧ Q s x] := by
      refine le_trans (prEvent_mono mx _ (fun x => (c a ∧ Q a x) ∨ ∃ s ∈ L, c s ∧ Q s x) ?_)
        (prEvent_or_le mx _ _)
      intro x hx
      simpa using hx
    refine hor.trans ?_
    rw [List.map_cons, List.sum_cons]
    refine add_le_add ?_ (prEvent_list_exists_le mx c Q L)
    by_cases hc : c a
    · simp only [hc, ite_true, true_and]
      exact le_rfl
    · simp only [hc, ite_false, false_and]
      rw [prEvent_false]

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι β : Type} {colRound : ι → ℕ}

open Classical in
/-- **The per-summand fresh-block bound**: a summand local at block `r`, at any fixed traces and coins,
fires on a fresh uniform block `r` with probability at most `weight / |K|^|coins|` (the twin of
the nockvm library's `cylinder₂_card_le` pricing, now as the probability of ONE round's challenge). -/
theorem mem_setBlock_prob (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) {r : ℕ}
    (hs : Local s r) (tr : Tr ι β) (χ : Coins Φ K) :
    Pr{let b ← $ᵗ (Block Φ K r)}[s.mem tr (setBlock r b χ)] ≤
      (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card := by
  -- split the block into the priced coins `P` and the rest
  let D := {i : Fin Φ.n // Φ.sampledAfter i = r}
  let P : D → Prop := fun d => d.1 ∈ s.coins
  let X := {d : D // P d} → K
  let Y := {d : D // ¬ P d} → K
  let e : (D → K) ≃ X × Y := Equiv.piEquivPiSubtypeProd P (fun _ => K)
  let g : X → (s.coins → K) := fun x i => x ⟨⟨i.1, hs.coins_block i.1 i.2⟩, i.2⟩
  let x0 : X := fun _ => Classical.arbitrary K
  let T : Y → Finset (s.coins → K) := fun y => s.badSet tr (setBlock r (e.symm (x0, y)) χ)
  have key : ∀ b : D → K, s.mem tr (setBlock r b χ) ↔ g (e b).1 ∈ T (e b).2 := by
    intro b
    have h1 : (fun i : s.coins => setBlock r b χ i) = g (e b).1 := by
      funext i
      simp [setBlock, hs.coins_block i.1 i.2, g, e, Equiv.piEquivPiSubtypeProd]
    have h2 : s.badSet tr (setBlock r b χ) = T (e b).2 := by
      refine hs.congr tr tr _ _ (fun _ _ => rfl) ?_
      intro i hi
      have hni : i ∉ s.coins := fun hc => Finset.disjoint_left.mp s.disj hc hi
      by_cases h : Φ.sampledAfter i = r
      · simp [setBlock, h, e, Equiv.piEquivPiSubtypeProd, P, hni]
      · simp [setBlock, h]
    simp only [BadSummand.mem, h1, h2]
  have hg : Function.Injective g := by
    intro x x' hxx
    funext d
    have := congrFun hxx ⟨d.1.1, d.2⟩
    simpa [g] using this
  -- count
  have hcount : (Finset.univ.filter fun b : D → K => s.mem tr (setBlock r b χ)).card ≤
      Fintype.card Y * s.weight := by
    rw [← Fintype.card_subtype]
    have e1 : {b : D → K // s.mem tr (setBlock r b χ)} ≃ {p : Y × X // g p.2 ∈ T p.1} :=
      (e.trans (Equiv.prodComm X Y)).subtypeEquiv (fun b => by
        rw [key b]; rfl)
    rw [Fintype.card_congr (e1.trans (Equiv.subtypeProdEquivSigmaSubtype
      (fun (y : Y) (x : X) => g x ∈ T y))), Fintype.card_sigma]
    calc (∑ y : Y, Fintype.card {x : X // g x ∈ T y}) ≤ ∑ _y : Y, s.weight := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          refine le_trans ?_ (s.card_le tr (setBlock r (e.symm (x0, y)) χ))
          rw [← Fintype.card_coe]
          exact Fintype.card_le_of_injective (fun x => ⟨g x.1, x.2⟩)
            (fun x x' h => Subtype.ext (hg (congrArg Subtype.val h)))
      _ = Fintype.card Y * s.weight := by simp
  have hX : Fintype.card {d : D // P d} = s.coins.card := by
    rw [← Fintype.card_coe s.coins]
    exact Fintype.card_congr
      { toFun := fun d => ⟨d.1.1, d.2⟩
        invFun := fun i => ⟨⟨i.1, hs.coins_block i.1 i.2⟩, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Fintype.card (D → K) = Fintype.card X * Fintype.card Y := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hXc : (Fintype.card X : ℝ≥0∞) = (Fintype.card K : ℝ≥0∞) ^ s.coins.card := by
    simp only [X, Fintype.card_fun, hX, Nat.cast_pow]
  rw [SampleableType.prEvent_uniformSample]
  change ((Finset.univ.filter fun b : D → K => s.mem tr (setBlock r b χ)).card : ℝ≥0∞) /
    (Fintype.card (D → K) : ℝ≥0∞) ≤ _
  have hY0 : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card Y := Fintype.card_pos
    exact_mod_cast this.ne'
  have hYt : (Fintype.card Y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((Finset.univ.filter fun b : D → K => s.mem tr (setBlock r b χ)).card : ℝ≥0∞) /
        (Fintype.card (D → K) : ℝ≥0∞)
      ≤ ((Fintype.card Y * s.weight : ℕ) : ℝ≥0∞) / (Fintype.card (D → K) : ℝ≥0∞) := by
        gcongr
    _ = (Fintype.card Y : ℝ≥0∞) * s.weight / ((Fintype.card Y : ℝ≥0∞) * Fintype.card X) := by
        rw [hcard]; push_cast; rw [mul_comm (Fintype.card X : ℝ≥0∞)]
    _ = (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card := by
        rw [ENNReal.mul_div_mul_left _ _ hY0 hYt, hXc]

end Bounds

/-! ## 2. The knowledge state and the trivial extractor -/

/-- A knowledge state with the trivial witness carrier. -/
def ks (P : Prop) : KnowledgeState.{0} := ⟨PUnit, fun _ => P⟩

/-- Every witness of a state equal to `ks P` is known once `P` holds. -/
theorem holds_of_eq_ks {S : KnowledgeState.{0}} {P : Prop} (h : S = ks P) (w : S.Witness) (hp : P) :
    S.holds w := by
  subst h; exact hp

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}
  (R : RapStatement Φ K ι β colRound)
  (blk : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound) → ℕ)

/-- Some summand priced on a block `< r` (so all its coins are sampled) has fired. -/
def Fired (m0 : R.M0) (tr : Tr ι β) (χ : Coins Φ K) (r : ℕ) : Prop :=
  ∃ s ∈ R.summands m0, blk s < r ∧ s.mem tr χ

/-- **The state** after `r` coin blocks. -/
def St (m0 : R.M0) (tr : Tr ι β) (χ : Coins Φ K) (r : ℕ) : Prop :=
  R.Holds ∨ Fired R blk m0 tr χ r

/-- The per-round error: the part of `epsilonOf (R.summands m0)` priced on block `r`. -/
noncomputable def roundBound (m0 : R.M0) (r : ℕ) : ℝ≥0∞ :=
  ((R.summands m0).map fun s =>
    if blk s = r then (s.weight : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ^ s.coins.card else 0).sum

/-- **The bridge hypotheses**: the nockvm library's pointwise soundness (`SoundG`), column-locality of every summand
at its block `blk s` (`Local`), and every block among the `nb` sampled ones. -/
structure Certificate (nb : ℕ) : Prop where
  sound : SoundG R
  local_ : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)
  blk_lt : ∀ m0, ∀ s ∈ R.summands m0, blk s < nb

section Extractor

variable [SampleableType K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (Ifin : OracleInterface R.Mfin)

/-- The final-message round. -/
abbrev finRound := unitRound R.Mfin Ifin

/-- The trivial extractor on the column rounds `r, …, r+k-1` and the final round, from traces `tr` and
coins `χ` accumulated so far. -/
noncomputable def extCols (m0 : R.M0) : (r k : ℕ) → (tr : Tr ι β) → (χ : Coins Φ K) →
    RoundExtractor (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).tree
      (ks (St R blk m0 tr χ r))
  | r, 0, tr, χ => fun _ =>
      ⟨ks (St R blk m0 tr χ r), id, fun _ => ⟨ks (St R blk m0 tr χ r), id, PUnit.unit⟩⟩
  | r, k + 1, tr, χ => fun c =>
      ⟨ks (St R blk m0 (setCols r c tr) χ r), id, fun b =>
        ⟨ks (St R blk m0 (setCols r c tr) (setBlock r b χ) (r + 1)), id,
          extCols m0 (r + 1) k (setCols r c tr) (setBlock r b χ)⟩⟩

/-- The traces, coins and final message a path writes, from an accumulator. -/
def finalOf : (r k : ℕ) → Tr ι β → Coins Φ K →
    (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).tree.ExecutionPath →
    Tr ι β × Coins Φ K × R.Mfin
  | _, 0, tr, χ, path => (tr, χ, path.1)
  | r, k + 1, tr, χ, path =>
      finalOf (r + 1) k (setCols r path.1 tr) (setBlock r path.2.1 χ) path.2.2

theorem extCols_terminal (m0 : R.M0) : ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K) path,
    (extCols R blk I Ifin m0 r k tr χ).terminalState path =
      ks (St R blk m0 (finalOf R I Ifin r k tr χ path).1 (finalOf R I Ifin r k tr χ path).2.1 (r + k))
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    have h := extCols_terminal m0 (r + 1) k (setCols r path.1 tr) (setBlock r path.2.1 χ) path.2.2
    rw [show r + 1 + k = r + (k + 1) by omega] at h
    exact h

variable {R blk}

/-- Writing round-`r` columns does not change which summands of blocks `< r` fired. -/
theorem st_setCols (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) (r : ℕ)
    (c : Cols colRound β r) (tr : Tr ι β) (χ : Coins Φ K) :
    St R blk m0 (setCols r c tr) χ r → St R blk m0 tr χ r := by
  rintro (h | ⟨s, hs, hlt, hm⟩)
  · exact Or.inl h
  · refine Or.inr ⟨s, hs, hlt, ?_⟩
    have := (hc m0 s hs).congr (setCols r c tr) tr χ χ
      (fun j hj => setCols_of_ne c tr (by omega)) (fun _ _ => rfl)
    simpa [BadSummand.mem, this] using hm

/-- A fresh block `r` can only make a block-`r` summand fire. -/
theorem st_setBlock (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) (r : ℕ)
    (tr : Tr ι β) (χ : Coins Φ K) (b : Block Φ K r)
    (h0 : ¬ St R blk m0 tr χ r) (h1 : St R blk m0 tr (setBlock r b χ) (r + 1)) :
    ∃ s ∈ R.summands m0, blk s = r ∧ s.mem tr (setBlock r b χ) := by
  rcases h1 with h | ⟨s, hs, hlt, hm⟩
  · exact absurd (Or.inl h) h0
  · refine ⟨s, hs, ?_, hm⟩
    by_contra hne
    have hlt' : blk s < r := by omega
    have hL := hc m0 s hs
    have hset : s.badSet tr (setBlock r b χ) = s.badSet tr χ :=
      hL.congr tr tr _ χ (fun _ _ => rfl) (fun i hi =>
        setBlock_of_ne b χ (by have := hL.dep_le i hi; omega))
    have hv : (fun i : s.coins => setBlock r b χ i) = fun i : s.coins => χ i := by
      funext i
      exact setBlock_of_ne b χ (by rw [hL.coins_block i.1 i.2]; omega)
    exact h0 (Or.inr ⟨s, hs, hlt', by simpa [BadSummand.mem, hset, hv] using hm⟩)

theorem extCols_preserving (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) :
    ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K),
      (extCols R blk I Ifin m0 r k tr χ).IsProverPreserving
        (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).roles
  | _, 0, _, _ => ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun _ => trivial⟩⟩
  | r, k + 1, tr, χ => ⟨fun c _ h => st_setCols hc m0 r c tr χ h,
      fun c => ⟨fun _ hrole => (nomatch hrole),
        fun b => extCols_preserving hc m0 (r + 1) k (setCols r c tr) (setBlock r b χ)⟩⟩

theorem extCols_bounded (hc : ∀ m0, ∀ s ∈ R.summands m0, Local s (blk s)) (m0 : R.M0) :
    ∀ (r k : ℕ) (tr : Tr ι β) (χ : Coins Φ K)
      (errs : RoundErrors (colRounds Φ K β colRound I (finRound R Ifin) r k)),
      (∀ j : Fin (colRounds Φ K β colRound I (finRound R Ifin) r k).length, (j : ℕ) < k →
        roundBound R blk m0 (r + j) ≤ errs j) →
      (extCols R blk I Ifin m0 r k tr χ).IsLocallyBounded
        (protocol (colRounds Φ K β colRound I (finRound R Ifin) r k)).roles
        (roundErrorSchedule (colRounds Φ K β colRound I (finRound R Ifin) r k) errs)
  | r, 0, tr, χ, errs, _ => by
    intro _
    refine ⟨?_, fun _ => trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ (fun _ ⟨_, h0, h1⟩ => h0 h1)
  | r, k + 1, tr, χ, errs, herr => by
    intro c
    refine ⟨?_, fun b => extCols_bounded hc m0 (r + 1) k (setCols r c tr) (setBlock r b χ)
      (fun j => errs j.succ) (fun j hj => ?_)⟩
    · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      have h0 := herr ⟨0, by simp [colRounds_length]⟩ (by simp)
      simp only [Nat.add_zero] at h0
      refine le_trans ?_ h0
      refine le_trans (prEvent_mono _ _ (fun b : Block Φ K r =>
          ∃ s ∈ R.summands m0, blk s = r ∧ s.mem (setCols r c tr) (setBlock r b χ)) ?_) ?_
      · rintro b ⟨_, h0', h1'⟩
        exact st_setBlock hc m0 r (setCols r c tr) χ b h0' h1'
      · refine le_trans (prEvent_list_exists_le _ (fun s => blk s = r)
          (fun s b => s.mem (setCols r c tr) (setBlock r b χ)) _) ?_
        unfold roundBound
        refine le_of_eq_of_le rfl (List.sum_le_sum (fun s hs => ?_))
        by_cases hb : blk s = r
        · simp only [hb, ite_true]
          exact mem_setBlock_prob s (hb ▸ hc m0 s hs) _ _
        · simp [hb]
    · have := herr j.succ (by simp; omega)
      rwa [Fin.val_succ, show r + (↑j + 1) = r + 1 + ↑j by omega] at this

end Extractor

/-! ## 3. The full protocol -/

section Full

variable [SampleableType K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β] [Inhabited K]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq R.Mfin] [Finite R.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
  (Ifin : OracleInterface R.Mfin) (nb : ℕ)

/-- The protocol's round list. -/
noncomputable abbrev rounds : List Round :=
  rapRounds Φ K β colRound R.M0 R.Mfin I0 I Ifin nb

/-- **The round extractor of the staged-RAP protocol** (trivial witnesses). -/
noncomputable def rapExtractor : RoundExtractor (protocol (rounds R I0 I Ifin nb)).tree (ks R.Holds) :=
  fun m0 => ⟨ks R.Holds, id, fun _ =>
    ⟨ks (St R blk m0 (fun _ => default) (fun _ => default) 0), id,
      extCols R blk I Ifin m0 0 nb (fun _ => default) (fun _ => default)⟩⟩

/-- The verifier's decision on a full path: `AcceptsG` of what the path wrote. -/
def rapAccepts (path : (protocol (rounds R I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  let f := finalOf R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2
  R.Accepts path.1 f.1 f.2.2 f.2.1

/-- The errors: `err r` at column round `r` (protocol index `r+1`), `0` at the two `Unit` rounds. -/
noncomputable def rapErrors (err : ℕ → ℝ≥0∞) : RoundErrors (rounds R I0 I Ifin nb) :=
  fun j => if 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ nb then err ((j : ℕ) - 1) else 0

variable {R blk I0 I Ifin nb}

theorem rapExtractor_terminal (path : (protocol (rounds R I0 I Ifin nb)).tree.ExecutionPath) :
    (rapExtractor R blk I0 I Ifin nb).terminalState path =
      ks (St R blk path.1 (finalOf R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).1
        (finalOf R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).2.1 (0 + nb)) :=
  extCols_terminal R blk I Ifin path.1 0 nb _ _ path.2.2

/-- **Bridge, prover law.** -/
theorem rapExtractor_preserving (hC : Certificate R blk nb) :
    (rapExtractor R blk I0 I Ifin nb).IsProverPreserving (protocol (rounds R I0 I Ifin nb)).roles :=
  ⟨fun _ _ h => h, fun m0 => ⟨fun _ hrole => (nomatch hrole),
    fun _ => extCols_preserving I Ifin hC.local_ m0 0 nb _ _⟩⟩

/-- **Bridge, local law**: every verifier node is bounded by `err r` (column round `r`) or `0`. -/
theorem rapExtractor_bounded (hC : Certificate R blk nb) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blk m0 r ≤ err r) :
    (rapExtractor R blk I0 I Ifin nb).IsLocallyBounded (protocol (rounds R I0 I Ifin nb)).roles
      (roundErrorSchedule (rounds R I0 I Ifin nb) (rapErrors R I0 I Ifin nb err)) := by
  intro m0
  refine ⟨?_, fun _ => extCols_bounded I Ifin hC.local_ m0 0 nb _ _ _ (fun j hj => ?_)⟩
  · rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (le_of_eq ?_) zero_le
    refine prEvent_eq_zero_of_forall_not _ _ (fun _ ⟨_, h0, h1⟩ => h0 ?_)
    rcases h1 with h | ⟨_, _, hlt, _⟩
    · exact h
    · exact absurd hlt (Nat.not_lt_zero _)
  · refine le_trans (herr m0 _) (le_of_eq ?_)
    simp only [rapErrors, Fin.val_succ]
    rw [ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by omega⟩ h)]
    congr 1
    omega

/-- **Bridge, terminal law**: an accepting path ends in a true state (`SoundG`). -/
theorem rapExtractor_output (hC : Certificate R blk nb)
    (path : (protocol (rounds R I0 I Ifin nb)).tree.ExecutionPath) (hacc : rapAccepts R I0 I Ifin nb path) :
    ((rapExtractor R blk I0 I Ifin nb).terminalState path).holds
      (rapExtractor_terminal (R := R) (blk := blk) path ▸ PUnit.unit) := by
  refine holds_of_eq_ks (rapExtractor_terminal path) _ ?_
  by_cases hf : ∃ s ∈ R.summands path.1,
      s.mem (finalOf R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).1
        (finalOf R I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2).2.1
  · obtain ⟨s, hs, hm⟩ := hf
    exact Or.inr ⟨s, hs, by have := hC.blk_lt path.1 s hs; omega, hm⟩
  · push Not at hf
    exact Or.inl (hC.sound _ _ _ _ hacc hf)

/-- **The bridge** (RAP-PORT deliverable 3): `SoundG` + column-locality ⇒ the native round-by-round
knowledge certificate of the staged-RAP protocol, with the error of column round `r` bounding the part of
`epsilonOf` priced on block `r`, and `0` at the two `Unit` rounds. -/
theorem rap_rbr_knowledge (hC : Certificate R blk nb) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blk m0 r ≤ err r) :
    (rapExtractor R blk I0 I Ifin nb).IsProverPreserving (protocol (rounds R I0 I Ifin nb)).roles ∧
    (rapExtractor R blk I0 I Ifin nb).IsLocallyBounded (protocol (rounds R I0 I Ifin nb)).roles
      (roundErrorSchedule (rounds R I0 I Ifin nb) (rapErrors R I0 I Ifin nb err)) ∧
    (∀ path, rapAccepts R I0 I Ifin nb path →
      ((rapExtractor R blk I0 I Ifin nb).terminalState path).holds
        (rapExtractor_terminal (R := R) (blk := blk) path ▸ PUnit.unit)) :=
  ⟨rapExtractor_preserving hC, rapExtractor_bounded hC err herr, rapExtractor_output hC⟩

open Classical in
/-- **Fiat–Shamir knowledge soundness of the staged-RAP protocol** (Quang Dao's
`singleSalt_knowledge_soundness`, zk-base `SingleSaltSecurity.lean:218`, applied to the bridge): for every
single-salt adversary, the probability of an accepted proof (`rapAccepts`) of a FALSE claim (`¬ Holds`)
is at most the expected fresh-query charge with round errors `rapErrors err`. -/
theorem rap_singleSalt_knowledge_soundness (hC : Certificate R blk nb) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blk m0 r ≤ err r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (rounds R I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (rounds R I0 I Ifin nb))
    (Z : Set (Statement × GlobalSalt)) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution (rounds R I0 I Ifin nb) guards
      (fun _ path => decide (rapAccepts R I0 I Ifin nb path)) adversary) ∅)}[
      badStoppedRelation (fun _ => ks R.Holds) (fun _ => rapExtractor R blk I0 I Ifin nb)
        (fun _ _ => R.Holds) (fun _ _ _ => True)
        (fun _ path _ => rapExtractor_terminal (R := R) (blk := blk) path ▸ PUnit.unit) Z
        joint.1.1.1] ≤
    expectedFreshQueryCharge (singleSaltAcceptedExecution (rounds R I0 I Ifin nb) guards
      (fun _ path => decide (rapAccepts R I0 I Ifin nb path)) adversary)
      (keyError (rapErrors R I0 I Ifin nb err)) :=
  singleSalt_knowledge_soundness guards (fun _ path => decide (rapAccepts R I0 I Ifin nb path))
    (rapErrors R I0 I Ifin nb err) adversary (fun _ => ks R.Holds)
    (fun _ => rapExtractor R blk I0 I Ifin nb) Z
    (fun _ _ => rapExtractor_preserving hC) (fun _ _ => rapExtractor_bounded hC err herr)
    (fun _ _ => R.Holds) (fun _ _ _ => True)
    (fun _ path _ => rapExtractor_terminal (R := R) (blk := blk) path ▸ PUnit.unit)
    (fun _ _ => Iff.rfl)
    (fun _ path _ hacc _ => rapExtractor_output hC path (of_decide_eq_true hacc))

end Full

end NockvmE2E.Rap
