/-
  Nock/RedTeam/Batch4Framework.lean

  Independent verification of definitional faithfulness + non-vacuity witnesses.

This artifact provides MACHINE-CHECKED evidence for:
  1. Def:IOP — Framework.IOP (Definition 2.1)
  2. Def:RAP — Framework.RAP (Definition 2.2) [def⚠]
  3. Def:Canonical_RAP — Framework.CanonicalRAP (Definition 3.2)
  4. Def:NPR_Phi — NPR.Φ (Definition 4.6)
  5.
  6.

  HYGIENE: No `sorry`, `admit`, or `native_decide`. Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}.
  NPR/Φ items over extension field K legitimately use `Nock.Field.goldilocks_prime` (whitelisted).
-/
import Nock.Framework
import Nock.NPR
import Nock.Walk
import Nock.NockVM

namespace Nock.RedTeam

open Nock.Framework Nock.Walk Nock.NPR

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Def:IOP` (Definition 2.1) — `Framework.IOP`
    ══════════════════════════════════════════════════════════════════════════════════════

    Drift check + consistency (non-vacuity): the structure captures the paper's two properties —
    perfect completeness `(x,w)∈L ⇒ Pr[accept]=1` and state-restoration soundness `Pr[bad] ≤ ε`.

    Witnesses:
    (a) Concrete `IOP` instance proving non-vacuity (structure is inhabited/consistent)
    (b) `example`-cite the `completeness` and `soundness` fields
    (c) doc-comment: probabilities are abstract ℝ, crypto realization out of scope (Tier-3)

    Disposition: PASSED (def, faithful interface)
-/

/-- **[1.a] Non-vacuity: concrete IOP instance.** A trivial IOP with:
    - Language: the universal language `L := fun _ _ => True`
    - 1 round, ε = 1 (trivial soundness), probAccept = 1
    This proves the `IOP` structure is inhabited (not contradictory/vacuous). -/
def trivialIOP : IOP Unit Unit Unit where
  L := fun _ _ => True
  rounds := fun _ => 1
  rounds_pos := fun _ => le_refl 1
  ε := fun _ => 1
  ε_mem := fun _ => ⟨by norm_num, le_refl 1⟩
  probAccept := fun _ _ => 1
  completeness := fun _ _ _ => rfl
  extractor := fun _ _ => ()
  probBad := fun _ => 0
  soundness := fun _ => by norm_num

/-- **[1.b.i] Completeness field citation.**  The `IOP` structure carries the paper's
    perfect completeness: `(x,w) ∈ L ⇒ Pr[accept] = 1`. -/
example (I : IOP Stmt Wit Tr) (x : Stmt) (w : Wit) (h : I.L x w) : I.probAccept x w = 1 :=
  I.completeness x w h

/-- **[1.b.ii] Soundness field citation.**  The `IOP` structure carries state-restoration
    soundness: `Pr[bad] ≤ ε(|x|)`. -/
example (I : IOP Stmt Wit Tr) (x : Stmt) : I.probBad x ≤ I.ε x :=
  I.soundness x

/-- **[1.c] Drift note: abstract probabilities (Tier-3 boundary).**  The `IOP` probabilities
    `probAccept`, `probBad` are abstract `ℝ`-valued fields. The cryptographic state-restoration
    soundness (that a real protocol achieves this bound) is the Tier-3 crypto boundary and is
    NOT proved in the Lean formalization (per the paper, the SNARK layer). -/
def drift_IOP_abstract_prob : String :=
  "IOP probabilities are abstract ℝ; crypto realization is Tier-3 boundary (main.tex:164)."


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Def:RAP` (Definition 2.2) — `Framework.RAP` [def⚠]
    ══════════════════════════════════════════════════════════════════════════════════════

    CONFIRM the documented under-specification (4 paper constraints NOT enforced):
    1. ord(ω) = e·2^h
    2. β ≠ 0
    3. I ⊆ [w] × {0,…,2^h−1}
    4. H = β⟨ω^{1/ρ}⟩ coset

    Adversarial witness: construct `badRAP : RAP F` with `β = 0` that type-checks.

    Disposition: PASSED
-/

/-- **[2.a] REGRESSION (P2, Gate B): `β = 0` is now REJECTED by the `RAP` structure.**
    The paper requires `β ∈ 𝔽∖{0}`. Enforcement
    is a theorem: every `RAP` has `β ≠ 0`. -/
theorem RAP_enforces_beta_ne_zero {F : Type*} [CommRing F] (R : RAP F) : R.β ≠ 0 :=
  R.β_ne_zero

/-- **[2.b] REGRESSION (P2, Gate B): out-of-bounds `I` is now REJECTED.**
    The paper requires `I ⊆ [w] × {0,…,2^h−1}`. Enforcement is a theorem: every symbolic row-offset is a genuine trace row. -/
theorem RAP_enforces_I_bound {F : Type*} [CommRing F] (R : RAP F) : ∀ q ∈ R.I, q.2 < 2 ^ R.h :=
  R.I_bound

/-- **[2.c] Faithfulness: `RAP.Satisfies` IS present.**  The satisfaction predicate
    `∀ i ∈ [s], x ∈ H ⇒ (C_i ∘ P)(x) = 0`. -/
example {F : Type*} [CommRing F] (R : RAP F) (P : Fin R.w → Polynomial F) : Prop := R.Satisfies P

/-- **[2.d] Faithfulness: `RAP.compose` IS present.**  The assignment `Y_{i,j} ↦ P_i(ω^j·X)`
. -/
noncomputable example {F : Type*} [CommRing F] (R : RAP F) (P : Fin R.w → Polynomial F) (i : Fin R.s) : Polynomial F := R.compose P i

/-- **[2.e] Drift documentation: RAP validity — 2 of 4 now ENFORCED (P2), 2 disclosed Tier-3.** -/
def drift_RAP_underspec_documented : String :=
  "RAP validity (paper Def:RAP, main.tex:144-145): (2) β ≠ 0 and (3) I ⊆ [w]×{0,…,2^h−1} are now " ++
  "ENFORCED as structure fields β_ne_zero / I_bound (P2, Gate B: badRAP_beta_zero / " ++
  "badRAP_I_out_of_bounds no longer construct). (1) ord(ω) = e·2^h and (4) H = β⟨ω^{1/ρ}⟩ coset " ++
  "are the FRI evaluation-domain facts, disclosed Tier-3-adjacent in CENSUS."


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3. `Def:Canonical_RAP` (Definition 3.2) — `Framework.CanonicalRAP`
    ══════════════════════════════════════════════════════════════════════════════════════

    Drift check: the structure has two sub-RAPs `Rprog`/`Rmem` sharing common params
    (`common_e/h/d/ω/β`) and the two equivalences `compute_iff`/`memory_iff`.

    Disposition: PASSED (def, faithful)
-/

/-- **[3.a] Field signature: `compute_iff` is the paper's biconditional.**
    `LangVMComputation(x_prog, T_prog, IO_prog) = 0 ⟺ RAP_prog.Satisfies(encode(...))`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) (xp : mes.Xprog) (tp : mes.Tprog) (iop : mes.IOprog) :
    mes.LangVMComputation xp tp iop ↔ c.Rprog.Satisfies (c.encodeProg xp tp iop) :=
  c.compute_iff xp tp iop

/-- **[3.b] Field signature: `memory_iff` is the paper's biconditional.**
    `LangVMMemory(x_mem, T_mem, IO_mem) = 0 ⟺ RAP_mem.Satisfies(encode(...))`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) (xm : mes.Xmem) (tm : mes.Tmem) (iom : mes.IOmem) :
    mes.LangVMMemory xm tm iom ↔ c.Rmem.Satisfies (c.encodeMem xm tm iom) :=
  c.memory_iff xm tm iom

/-- **[3.c] Common parameter enforcement: `common_e`.**  The two sub-RAPs share `e`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) : c.Rprog.e = c.Rmem.e := c.common_e

/-- **[3.d] Common parameter enforcement: `common_h`.**  The two sub-RAPs share `h`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) : c.Rprog.h = c.Rmem.h := c.common_h

/-- **[3.e] Common parameter enforcement: `common_ω`.**  The two sub-RAPs share `ω`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) : c.Rprog.ω = c.Rmem.ω := c.common_ω

/-- **[3.f] Common parameter enforcement: `common_β`.**  The two sub-RAPs share `β`. -/
example {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] {mes : MES X Tw M} {F : Type*} [CommRing F]
    (c : CanonicalRAP mes F) : c.Rprog.β = c.Rmem.β := c.common_β

/-- **[3.g] Drift note: CanonicalRAP is faithful to paper structure.** -/
def drift_CanonicalRAP : String :=
  "CanonicalRAP faithfully models main.tex:409-442: two sub-RAPs with shared params " ++
  "and the compute_iff/memory_iff biconditionals. No drift detected."


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 4. `Def:NPR_Phi` (Definition 4.6) — `NPR.Φ`
    ══════════════════════════════════════════════════════════════════════════════════════

    Drift check + computation (non-vacuity): Φ(n) = (X^|dt|, Σ dt_i X^{i−1}, Σ w_i X^{i−1}).

    NOTE: Uses `Nock.Field.K` which depends on `goldilocks_prime` (whitelisted axiom).

    Disposition: PASSED (def, faithful)
-/

open Nock.Field in
/-- **[4.a] Φ computes on a concrete atom.** `Φ (atom 5)` is well-defined. -/
example : (Φ (K := K) (Noun.atom 5)).1 = Polynomial.X ^ 1 := by simp [Noun.leaves]

/-- **[4.b] Φ computes on a concrete cell.** `Φ (cell (atom 1) (atom 2))` is well-defined. -/
example : (Φ (K := Nock.Field.K) (Noun.cell (Noun.atom 1) (Noun.atom 2))).1 = Polynomial.X ^ 2 := by
  simp [Noun.leaves]

/-- **[4.c] First component: `Φ_fst n = X ^ n.leaves`.** -/
example (n : Noun) : (Φ (K := Nock.Field.K) n).1 = Polynomial.X ^ n.leaves := Φ_fst n

/-- **[4.d] Second component: `Φ_snd_fst n = listPoly (leafF n)`.** -/
example (n : Noun) : (Φ (K := Nock.Field.K) n).2.1 = listPoly (leafF n) := Φ_snd_fst n

/-- **[4.e] Third component: `Φ_snd_snd n = listPoly (dyckBits n)`.** -/
example (n : Noun) : (Φ (K := Nock.Field.K) n).2.2 = listPoly (dyckBits n) := Φ_snd_snd n

/-- **[4.f] Fingerprint evaluation: `fn n r = Φ n [r,r,r]`.** -/
example (n : Noun) (r : Nock.Field.K) :
    fn n r = ((Φ n).1.eval r, (Φ n).2.1.eval r, (Φ n).2.2.eval r) :=
  fn_eq_Φ_eval n r

/-- **[4.g] Leaves count sanity: atom has 1 leaf.** -/
example (k : ℕ) : (Noun.atom k).leaves = 1 := rfl

/-- **[4.h] Leaves count sanity: cell has sum of subtree leaves.** -/
example (l r : Noun) : (Noun.cell l r).leaves = l.leaves + r.leaves := rfl

/-- **[4.i] Drift note: NPR.Φ is faithful to paper.** -/
def drift_NPR_Phi : String :=
  "NPR.Φ faithfully models main.tex:1170-1178: Φ(dt,w) = (X^λ, listPoly dt, listPoly w). " ++
  "Uses field K which depends on goldilocks_prime (whitelisted)."


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 5. `Lem:NPR_decomp` (Lemma 4.8) — `NPR.NPR_decomp`
    ══════════════════════════════════════════════════════════════════════════════════════

Disposition: PASSED
-/

section NPR_decomp_witnesses

open Polynomial

/-- Concrete nouns for testing. -/
def l_noun : Noun := Noun.atom 1
def r_noun : Noun := Noun.atom 2

/-- **[5.a.i] Phi1_cons fires on concrete nouns.**
    `(Φ (cell l r)).1 = (Φ l).1 * (Φ r).1`. -/
example : (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).1
    = (Φ l_noun).1 * (Φ r_noun).1 := Phi1_cons l_noun r_noun

/-- **[5.a.ii] Phi2_cons fires on concrete nouns.**
    `(Φ (cell l r)).2.1 = (Φ l).2.1 + X^l.leaves * (Φ r).2.1`. -/
example : (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).2.1
    = (Φ l_noun).2.1 + X ^ l_noun.leaves * (Φ r_noun).2.1 := Phi2_cons l_noun r_noun

/-- **[5.a.iii] Phi3_cons fires on concrete nouns — CORRECTED form.**
    `(Φ (cell l r)).2.2 = X * (Φ l).2.2 + X^(2*l.leaves-1) + X^(2*l.leaves) * (Φ r).2.2`. -/
example : (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).2.2
    = X * (Φ l_noun).2.2 + X ^ (2 * l_noun.leaves - 1) + X ^ (2 * l_noun.leaves) * (Φ r_noun).2.2 :=
  Phi3_cons l_noun r_noun

/-- The CORRECT identity (proven in Lean) is:
    `Φ(n)₃ = X·Φ(nL)₃ + X^{2λL−1} + X^{2λL}·Φ(nR)₃`. The paper's form is off by a global factor of `X` (HIGH severity paper math-error). -/
def census_A1_Phi3_correction : String :=
  "CENSUS #A1 (HIGH): Paper's Φ₃ identity (main.tex:1223) is " ++
  "'Φ(n)₃ = Φ(nL)₃ + X^{2(λL−1)} + X^{2λL−1}·Φ(nR)₃' — MISSING the leading X factor. " ++
  "Lean's Phi3_cons proves the CORRECTED identity: " ++
  "'Φ(n)₃ = X·Φ(nL)₃ + X^{2λL−1} + X^{2λL}·Φ(nR)₃'. " ++
  "Concretely: for n=cons(atom,atom), dyck=[0,1], F_w=X. " ++
  "Correct: X·0 + X^1 + X^2·0 = X. Paper: 0 + X^0 + X^1·0 = 1. Off by X."

/-- **[5.c] NPR_decomp_of_cons derives the three identities from structural equality.** -/
example : (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).1 = (Φ (K := Nock.Field.K) l_noun).1 * (Φ (K := Nock.Field.K) r_noun).1
    ∧ (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).2.1 = (Φ (K := Nock.Field.K) l_noun).2.1 + X ^ l_noun.leaves * (Φ (K := Nock.Field.K) r_noun).2.1
    ∧ (Φ (K := Nock.Field.K) (Noun.cell l_noun r_noun)).2.2 = X * (Φ (K := Nock.Field.K) l_noun).2.2 + X ^ (2 * l_noun.leaves - 1)
        + X ^ (2 * l_noun.leaves) * (Φ (K := Nock.Field.K) r_noun).2.2 :=
  NPR_decomp_of_cons rfl

/-- **[5.d] NPR_decomp biconditional RHS is FIELD-noun equality `Φ n = Φ (cell nL nR)`.**
    NOT structural `n = cell nL nR`. The structural forward direction is `NPR_decomp_of_cons`. -/
example (n nL nR : Noun) :
    Φ (K := Nock.Field.K) n = Φ (K := Nock.Field.K) (Noun.cell nL nR)
      ↔ ( (Φ (K := Nock.Field.K) n).1 = (Φ (K := Nock.Field.K) nL).1 * (Φ (K := Nock.Field.K) nR).1
        ∧ (Φ (K := Nock.Field.K) n).2.1 = (Φ (K := Nock.Field.K) nL).2.1 + X ^ nL.leaves * (Φ (K := Nock.Field.K) nR).2.1
        ∧ (Φ (K := Nock.Field.K) n).2.2 = X * (Φ (K := Nock.Field.K) nL).2.2 + X ^ (2 * nL.leaves - 1)
            + X ^ (2 * nL.leaves) * (Φ (K := Nock.Field.K) nR).2.2 ) :=
  NPR_decomp n nL nR

/-- **[5.e] Field-eq delta documentation.** -/
def delta_NPR_decomp_field_eq : String :=
  "NPR_decomp RHS is field-noun equality 'Φ n = Φ (cell nL nR)', NOT structural 'n = cell nL nR'. " ++
  "The structural forward direction is NPR_decomp_of_cons. " ++
  "The converse to structural equality would need injectivity of Nat→K (fails in small char)."

end NPR_decomp_witnesses


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 6. `Thm:Walk_IOP` (Theorem 3.6) — `Walk_IOP_final_card`/`_prob`
    ══════════════════════════════════════════════════════════════════════════════════════

    The big soundness theorem. CONFIRM the two documented deltas:

Disposition: PASSED
-/

section Walk_IOP_witnesses

open scoped Classical

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {S DT : Type*} {n : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **[6.a] Completeness (⟹ direction) — `walk_completeness_RVT` statement.**
    For an `RVT F root`, there exists a satisfying `WalkSat` trace with `acc = 0`. -/
example (nodeVal : NTree (S × DT) → K) (root : NTree (S × DT)) (α : K)
    (hrvt : RVT F root) :
    ∃ ln count acc : ℕ → K,
      WalkSat (curCol nodeVal (bfsForest [root])) (chldCol nodeVal (bfsForest [root]))
        (foCol (bfsForest [root])) ln count acc α (curCol nodeVal (bfsForest [root]) 1 * α) α
        (bfsForest [root]).length
      ∧ (∀ t ∈ bfsForest [root], Fcon F t)
      ∧ acc (bfsForest [root]).length = 0 :=
  walk_completeness_RVT nodeVal root α hrvt

/-- **[6.b.i] QGate structure IS present.**
    The queue-validity gate with boundary, transition, no-underflow, and terminal constraints. -/
example (fo : ℕ → ℕ) (q qinv : ℕ → K) (q0 h : ℕ) : Prop := QGate fo q qinv q0 h

/-- **[6.b.ii] QGate ⟹ BFSValid (`bfsValid_of_qgate`).**
    The gate implies queue-validity: at every row, the queue has ≥1 element. -/
example {fo : ℕ → ℕ} {q qinv : ℕ → K} {h : ℕ} (hq : QGate fo q qinv 1 h) : BFSValid fo h :=
  bfsValid_of_qgate hq

/-- **[6.b.iii] witness_020_excluded: malicious fo=(0,2,0) at h=3 is REJECTED by QGate.**
    The paper's "self-evident" node_list=node_queue ⟹ full-BFT step is FALSE without QGate.
    This specific counterexample (fo(1)=0, fo(2)=2, fo(3)=0) produces queue underflow at row 2:
    q(1)=1, q(2)=1+0-1=0, so no inverse qinv(2) with q(2)·qinv(2)=1 can exist. -/
example (q qinv : ℕ → K) : ¬ QGate (fun i => if i = 2 then 2 else 0) q qinv 1 3 :=
  witness_020_excluded q qinv

/-- **[6.b.iv] qgate_of_bfsValid: the gate IS satisfiable by genuine BFS layouts.**
    Shows the soundness capstone is NON-VACUOUS. -/
example {p : ℕ} [CharP K p] {fo : ℕ → ℕ} {q0 h : ℕ}
    (hh : 1 ≤ h) (hq0 : 1 ≤ q0)
    (hvalid : ∀ i, 1 ≤ i → i ≤ h → i ≤ q0 + Sf fo (i - 1))
    (htile : q0 + Sf fo h = h) (hb : q0 + Sf fo h < p) :
    ∃ q qinv : ℕ → K, QGate fo q qinv q0 h :=
  qgate_of_bfsValid hh hq0 hvalid htile hb


def census_5_QGate : String :=
  "CENSUS #5 (HIGH): The paper's 'self-evident' node_list=node_queue ⟹ full-BFT step " ++
  "(main.tex:2266) is FALSE without queue-validity. witness_020_excluded shows a malicious " ++
  "fo=(0,2,0) at h=3 that satisfies the polynomial identity but causes queue underflow " ++
  "(q(2)=0, not invertible). QGate (bfsValid_of_qgate) CLOSES this gap by constraining " ++
  "the prover to commit queue values + inverses, enforcing queue validity."

/-- **[6.c.i] Walk_IOP_final_prob TYPE citation.**
    The honest bound is `h/|K| + (h*(node_size-1))/|K|`, i.e. `h/|K| + ε_RLC`. -/
example {node_size n : ℕ} {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_final_prob St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit

/-- Honest proven bound is `h/|K| + ε_RLC`
    where `ε_RLC = h*(node_size-1)/|K|` is the RLC-compression term. -/
def census_A4_eps_RLC : String :=
  "CENSUS #A4 (MED): Paper's Walk_IOP bound (main.tex:966) states 'h/|K|'. " ++
  "The honest proven bound (Walk_IOP_final_prob) is 'h/|K| + ε_RLC' where " ++
  "ε_RLC = h*(node_size-1)/|K| is the RLC random-linear-combination compression term. " ++
  "The paper OMITS this ε_RLC term. Honest bound proven in Lean."

/-- **[6.d] Walk_IOP_final_card TYPE citation (cardinality form).**
    The bad set has size ≤ |K|*h + |K|*(h*(node_size-1)). -/
example {node_size n : ℕ} {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) :=
  Walk_IOP_final_card St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit

end Walk_IOP_witnesses


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch4_drift_summary : String :=
  "BATCH 4 FRAMEWORK DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Def:IOP — PASSED (faithful interface; probabilities abstract ℝ, Tier-3 boundary)\n" ++
  "2. Def:RAP — PASSED (P2: β≠0 & I-bound ENFORCED [Gate B]; ord(ω)/H-coset Tier-3-disclosed)\n" ++
  "3. Def:Canonical_RAP — PASSED (faithful; compute_iff/memory_iff present)\n" ++
  "4. Def:NPR_Phi — PASSED (faithful; Φ computes on concrete nouns; uses goldilocks_prime)\n" ++
  "5. Lem:NPR_decomp — PASSED (CENSUS #A1: X-factor CORRECTED in Phi3_cons; field-eq RHS)\n" ++
  "6. Thm:Walk_IOP — PASSED (CENSUS #5: QGate present; CENSUS #A4: ε_RLC in bound)\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. All deltas match documented CORRESPONDENCE.md / CENSUS.md."

end Nock.RedTeam
