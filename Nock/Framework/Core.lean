import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
Core interfaces of the verifiable-VM framework: the `VMSystem` statement/witness verifier class, memory encoding families (`MEF`), the interactive oracle proof interface (`IOP`, whose soundness is a field, not a theorem), and randomized AIR with preprocessing (`RAP`) with its satisfaction predicate `RAP.Satisfies`.
-/

namespace Nock.Framework

open scoped Polynomial

/-! ## `VMSystem` — verifier interface: a statement/witness language -/

/-- **`VMSystem ι`** — the minimal verifier interface keyed by an instance-selecting tag `ι`:
    a `Statement` type, a `Witness` type, and an acceptance relation `accepts`.  The recognized
    language is `Language ι x := ∃ w, accepts x w`.  Kept index-explicit (no `outParam`) so that
    distinct field/seed choices are distinct instance keys. -/
class VMSystem (ι : Type u) where
  /-- Statement (public input) type. -/
  Statement : Type v
  /-- Witness (private trace/certificate) type. -/
  Witness : Type w
  /-- Acceptance relation of the verifier. -/
  accepts : Statement → Witness → Prop

/-- **`Language ι x`** — membership in the language recognized by the `VMSystem` on tag `ι`:
    there exists a witness the verifier accepts against the statement `x`. -/
abbrev Language (ι : Type u) [VMSystem ι] (x : VMSystem.Statement ι) : Prop :=
  ∃ w : VMSystem.Witness ι, VMSystem.accepts (ι := ι) x w

/-! ## `Def:MEF` — memory encoding family -/

/-- **`Def:MEF`.**  A memory encoding family `MEM = (𝒜, 𝒱𝒟, 𝒯)`: an address
    space `A`, a value domain `VD`, and an *ordered* set `T` of timestamps.  A memory record is a
    triple `(a,v,t) ∈ A × VD × T = Rec^MEM`; a record *sequence* of size `k` is an ordered list. -/
structure MEF where
  /-- Address space `𝒜`. -/
  A : Type
  /-- Value domain `𝒱𝒟`. -/
  VD : Type
  /-- Timestamp set `𝒯` — an *ordered* set. -/
  T : Type
  /-- `𝒯` is ordered. -/
  Tord : LinearOrder T

/-- A memory record `(a,v,t) ∈ 𝒜 × 𝒱𝒟 × 𝒯 = Rec^MEM`. -/
abbrev MEF.Rec (M : MEF) : Type := M.A × M.VD × M.T

/-- A memory record sequence of size `k` — an ordered list of `k` records; `Seq^MEM_k` is the
    universe of such.  Modeled as `Fin k → Rec` (a length-`k` ordered tuple). -/
abbrev MEF.Seq (M : MEF) (k : ℕ) : Type := Fin k → M.Rec

/-! ## `Def IOP` — interactive oracle proof (INTERFACE; crypto boundary Tier-3)

  A structural interface capturing the shape of Definition: a language relation,
  `k` rounds, soundness error `ε : {0,1}* → [0,1]`, an abstract acceptance-probability, perfect
  completeness, a state-restoration extractor, and the soundness bound.  The *cryptographic*
  soundness (that a real protocol achieves this bound) is Tier-3 and is NOT proved — this is the
  axiom boundary; here it is an honest constraint on the abstract fields. -/

/-- **`Def IOP`.**  An interactive oracle proof interface for a language on
    statements `Stmt` with witnesses `Wit`, transcripts `Tr`.  The two properties of the paper:
    perfect **completeness** `Pr[⟨P(x,w),V(x)⟩=1 | (x,w)∈L] = 1`, and
    **state-restoration soundness** via an extractor `E_L` with error `≤ ε(|x|)`.
    Probabilities are abstract `ℝ`-valued fields; the cryptographic realisation is out of scope. -/
structure IOP (Stmt Wit Tr : Type*) where
  /-- The language relation: `(x,w) ∈ L`. -/
  L : Stmt → Wit → Prop
  /-- Rounds of interaction `k : {0,1}* → ℕ_+`. -/
  rounds : Stmt → ℕ
  /-- `k(|x|) ∈ ℕ_+`. -/
  rounds_pos : ∀ x, 1 ≤ rounds x
  /-- Soundness error `ε : {0,1}* → [0,1]`. -/
  ε : Stmt → ℝ
  /-- `ε(x) ∈ [0,1]`. -/
  ε_mem : ∀ x, 0 ≤ ε x ∧ ε x ≤ 1
  /-- Abstract acceptance probability `Pr[⟨P(x,w),V(x)⟩ = 1]`. -/
  probAccept : Stmt → Wit → ℝ
  /-- **Completeness:** `(x,w) ∈ L ⇒ Pr[accept] = 1`. -/
  completeness : ∀ x w, L x w → probAccept x w = 1
  /-- State-restoration extractor `E_L`. -/
  extractor : Stmt → Tr → Wit
  /-- Abstract probability of the soundness-breaking event
      `tr accepts ∧ (x, E_L(x,tr)) ∉ L`. -/
  probBad : Stmt → ℝ
  /-- **State-restoration soundness:** `Pr[bad] ≤ ε(|x|)`.  (Tier-3 crypto
      boundary — a *constraint* on the interface, not a theorem proved here.) -/
  soundness : ∀ x, probBad x ≤ ε x

/-! ## `Def RAP` — randomized AIR with preprocessing -/

/-- **`Def RAP`.**  A Randomized AIR with Preprocessing
    `RAP = (𝔽, (𝕂,e), (k, w_RAP), h, d, s, (ω,β), I, Cset)`.  We fix `𝔽 = F` as the structure
    parameter; the extension field `𝕂` of degree `e` is recorded by `e` (its algebra enters only
    in the concrete IO accumulators).  Constraints `Cset` are multivariate polynomials over the
    symbolic variables `Y_{i,j}` indexed by `I ⊆ [w] × {0,…,2^h−1}`. -/
structure RAP (F : Type*) [CommRing F] where
  /-- Extension degree `e` (`𝕂 = ` degree-`e` extension of `𝔽`). -/
  e : ℕ
  /-- Rounds of interaction `k`. -/
  k : ℕ
  /-- `w_RAP(i)` = number of columns of round `i`; `w_RAP(1)` = preprocessing. -/
  wRAP : Fin k → ℕ
  /-- Total column count `w_RAP := Σ w_RAP(i)`. -/
  w : ℕ
  /-- `w = Σ w_RAP(i)`. -/
  w_eq : w = ∑ i, wRAP i
  /-- `h`: columns have length `2^h`. -/
  h : ℕ
  /-- `d`: maximal constraint degree. -/
  d : ℕ
  /-- `s`: number of constraint polynomials. -/
  s : ℕ
  /-- `ω ∈ 𝔽` of multiplicative order `e·2^h`. -/
  ω : F
  /-- `β ∈ 𝔽 \ {0}`. -/
  β : F
  /-- `I ⊆ {1,…,w} × {0,…,2^h−1}`.  Positions of the symbolic variables `Y_{i,j}`. -/
  I : Finset (Fin w × ℕ)
  /-- The `s` constraint polynomials `C_i ∈ 𝔽^{≤d}[Y]`. -/
  C : Fin s → MvPolynomial (Fin w × ℕ) F
  /-- Each `C_i` uses only symbolic variables indexed by `I`. -/
  C_vars : ∀ i, (C i).vars ⊆ I
  /-- Each `C_i` is at most degree `d`. -/
  C_deg : ∀ i, (C i).totalDegree ≤ d
  /-- The trace-domain coset `H`, as the set of evaluation points. -/
  H : Finset F
  /-- **Enforced RAP validity — `β ∈ 𝔽 ∖ {0}`.**  The RLC/LogUp challenge is
      nonzero. -/
  β_ne_zero : β ≠ 0
  /-- **Enforced RAP validity — `I ⊆ {1,…,w} × {0,…,2^h−1}`.**  Every symbolic
      variable `Y_{i,j}` references a genuine trace row (`j < 2^h`); the column `i` is already
      `< w` (a `Fin w`).  Rejects the adversarial out-of-bounds-`I` witness.  (The remaining two
      paper `Def:RAP` constraints — `ord(ω) = e·2^h` and the coset `H = β⟨ω^{1/ρ}⟩` — are the FRI
      evaluation-domain facts, not enforced here.) -/
  I_bound : ∀ q ∈ I, q.2 < 2 ^ h

/-- **Assignment `Q ∘ P`.**  Substituting each symbolic `Y_{i,j}` with
    `P_i(ω^j · X)` in the constraint `C_i` yields the univariate `(C_i ∘ P) ∈ 𝔽[X]`. -/
noncomputable def RAP.compose {F : Type*} [CommRing F] (R : RAP F)
    (P : Fin R.w → F[X]) (i : Fin R.s) : F[X] :=
  MvPolynomial.aeval
    (fun q : Fin R.w × ℕ => (P q.1).comp (Polynomial.C (R.ω ^ q.2) * Polynomial.X)) (R.C i)

/-- **RAP satisfaction.**  The trace `P = (P_1,…,P_w)` *satisfies* the RAP iff
    `∀ i ∈ [s], x ∈ H ⇒ (C_i ∘ P)(x) = 0`. -/
def RAP.Satisfies {F : Type*} [CommRing F] (R : RAP F) (P : Fin R.w → F[X]) : Prop :=
  ∀ i : Fin R.s, ∀ x ∈ R.H, (R.compose P i).eval x = 0

end Nock.Framework
