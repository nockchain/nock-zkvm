/-
  Nock/RedTeam/Batch5IO.lean

  Independent verification of definitional faithfulness + non-vacuity witnesses.

This artifact provides MACHINE-CHECKED evidence for:
  1. Lem:MEM_1 — `L_IO ⊊ L_mIO`
  2. Lem:MEM_2 — `L_IO ⊊ L_SE`, `L_IO ≡ L_uSE`

  HYGIENE: No `sorry`, `admit`, or `native_decide`. Axiom-clean.
-/
import Nock.IO

namespace Nock.RedTeam

open Nock.IO

/-! ## 1. Lem:MEM_1 — `L_IO ⊊ L_mIO`

    Paper: Every `L_IO` pair is also `L_mIO` (⊆), but `L_mIO` is strictly larger (⊊)
    because it permits request multiplicities (duplicates).

-/

section MEM_1

/-! ### [1.a] The ⊆ direction: cite `MEM_1_subset` -/

/-- **[1.a] `L_IO ⊆ L_mIO`**: Every `L_IO` pair is `L_mIO`.
    This is the forward direction of the inclusion. -/
example {R : Type*} [DecidableEq R] (K : ℕ) (requests responses : List R)
    (h : LIO K requests responses) : LmIO K requests responses :=
  MEM_1_subset K requests responses h

/-! ### [1.b] Strictness: instantiate `MEM_1_strict` concretely -/

/-- **[1.b.i] Concrete separating element**: For `K = 2`, `R = ℕ`, `x = 0`,
    the pair `([0,0], [0])` is in `L_mIO` but NOT in `L_IO`.
    This witnesses properness of `⊊`. -/
theorem MEM_1_strict_concrete :
    LmIO (R := ℕ) 2 [0, 0] [0] ∧ ¬ LIO (R := ℕ) 2 [0, 0] [0] :=
  MEM_1_strict 2 (by norm_num : 2 ≤ 2) 0

/-- **[1.b.ii] Alternative witness**: Same with `K = 3` and `x = 42`. -/
theorem MEM_1_strict_alt :
    LmIO (R := ℕ) 3 [42, 42] [42] ∧ ¬ LIO (R := ℕ) 3 [42, 42] [42] :=
  MEM_1_strict 3 (by norm_num : 2 ≤ 3) 42

/-- **[1.b.iii] Concrete element in `L_mIO ∖ L_IO`**: The positive witness. -/
theorem separating_element_in_LmIO :
    LmIO (R := ℕ) 2 [0, 0] [0] :=
  (MEM_1_strict_concrete).1

/-- **[1.b.iv] Concrete element NOT in `L_IO`**: The negative witness. -/
theorem separating_element_not_in_LIO :
    ¬ LIO (R := ℕ) 2 [0, 0] [0] :=
  (MEM_1_strict_concrete).2

/-! ### [1.c] The `K=1` degeneracy: why `2 ≤ K` is load-bearing -/

/-- **[1.c.i] At `K=1`, the witness `[x,x]` fails `InRange 1 [x,x].length`**.
    Since `[x,x].length = 2 > 1 = K`, the request list exceeds the bound.
    This is why `MEM_1_strict` requires `2 ≤ K`. -/
theorem K1_witness_fails_InRange (x : ℕ) : ¬ InRange 1 ([x, x] : List ℕ).length := by
  simp only [List.length_cons, InRange]
  omega

/-- **[1.c.ii] Length of the witness list is 2**. -/
example (x : ℕ) : ([x, x] : List ℕ).length = 2 := rfl

/-- **[1.c.iii] `InRange 1 2` fails since `2 > 1`**. -/
theorem InRange_1_2_false : ¬ InRange 1 2 := by
  simp [InRange]

/-- **[1.c.iv] Documentation**: `⊊` is equality at `K=1`, strict for `K≥2`. -/
def MEM_1_K1_degeneracy_doc : String :=
  "At K=1, the strict inclusion L_IO ⊊ L_mIO degenerates to equality. " ++
  "The witness [x,x] (a request with multiplicity) has length 2, but " ++
  "InRange 1 2 requires length ≤ 1. Hence MEM_1_strict needs 2 ≤ K. " ++
  "This matches the paper's Minor note: ⊊ is strict only for K ≥ 2."



/-- **[1.d.i] The `LmIO` definition unfolds to show the bidirectional clause**. Paper has one-directional `set(req) ⊆ set(resp)`. Lean's `LmIO` has `∀ x, x ∈ requests ↔ x ∈ uniq` — both directions. -/
example {R : Type*} [DecidableEq R] (K : ℕ) (requests responses : List R) :
    LmIO K requests responses ↔
      (InRange K requests.length ∧
       ∃ uniq : List R,
         uniq.length ≤ requests.length ∧
         uniq.Nodup ∧
         (∀ x, x ∈ requests ↔ x ∈ uniq) ∧  -- ← THE BIDIRECTIONAL CLAUSE
         responses.Perm uniq) :=
  Iff.rfl

/-- **[1.d.ii] The `←` direction (x ∈ uniq → x ∈ requests) is the REPAIR**.
    Paper omits this; Lean includes it to make `lem_mio_ldse` provable. -/
def CENSUS_6_repair_doc : String :=
  "CENSUS #6 (LOW): Paper's L_mIO condition 3 (main.tex:198) is one-directional: " ++
  "set(requests) ⊆ set(unique_requests). The Lean definition uses the " ++
  "BIDIRECTIONAL clause `∀ x, x ∈ requests ↔ x ∈ uniq`, which also ensures " ++
  "set(unique_requests) ⊆ set(requests). This REPAIR is necessary for " ++
  "`lem_mio_ldse` (main.tex:279) to hold, as its proof requires set equality."

/-- **[1.d.iii] `LmIO_iff` shows the equivalent characterisation with `toFinset` equality**. -/
example {R : Type*} [DecidableEq R] (K : ℕ) (requests responses : List R) :
    LmIO K requests responses ↔
      (InRange K requests.length ∧ responses.length ≤ requests.length ∧ responses.Nodup
        ∧ requests.toFinset = responses.toFinset) :=
  LmIO_iff K requests responses

end MEM_1

/-! ## 2. Lem:MEM_2 — `L_IO ⊊ L_SE`, `L_IO ≡ L_uSE`

    Paper: The identity `L_IO ≡ L_uSE` (unique-response SE), and the strict
    inclusion `L_IO ⊊ L_SE` (SE allows duplicate responses).

    Lean: Over `𝔽^M` records with `InRange K M` (the paper uses `char > K`, dropped).

    Adversarial checks:
    (a) cite `MEM_2_uSE` (the `≡` biconditional)
    (b) cite `MEM_2_subset` (⊆ into `L_SE`)
    (c) instantiate `MEM_2_strict` concretely to witness properness
    (d) document the "drops char>K (benign)" delta -/

section MEM_2

/-! ### [2.a] The `≡` biconditional: cite `MEM_2_uSE` -/

/-- **[2.a] `L_IO ≡ L_uSE`**: The identity map.
    Both say "distinct responses, and request/response multisets coincide".
    Requires `InRange K M` (the `M ∈ [K]` bound). -/
example {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p] {M : ℕ}
    (K : ℕ) (hM : InRange K M) (req resp : List (Fin M → 𝔽)) :
    LIO K req resp ↔ LuSE K req resp :=
  MEM_2_uSE K hM req resp

/-! ### [2.b] The ⊆ direction: cite `MEM_2_subset` -/

/-- **[2.b] `L_IO ⊆ L_SE`**: Forward direction of the inclusion.
    Requires `InRange K M`. -/
example {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p] {M : ℕ}
    (K : ℕ) (hM : InRange K M) (req resp : List (Fin M → 𝔽))
    (h : LIO K req resp) : LSE K req resp :=
  MEM_2_subset K hM req resp h

/-! ### [2.c] Strictness: instantiate `MEM_2_strict` concretely -/

/-- **[2.c.i] Abstract strictness witness**:
    For any `K ≥ 2`, `M ∈ [K]`, and record `x : Fin M → 𝔽`,
    the pair `([x,x], [x,x])` is in `L_SE` but NOT in `L_IO`.

    The separating element has DUPLICATE RESPONSES: `[x,x],[x,x]` satisfies
    the multiset-equality (SEcond) because `⟦x,x⟧ = ⟦x,x⟧`, but `L_IO`
    requires `responses.Nodup` which fails for `[x,x]`. -/
theorem MEM_2_strict_abstract {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p] {M : ℕ}
    (K : ℕ) (hK : 2 ≤ K) (hM : InRange K M) (x : Fin M → 𝔽) :
    LSE K [x, x] [x, x] ∧ ¬ LIO K [x, x] [x, x] :=
  MEM_2_strict K hK hM x

/-- **[2.c.ii] Concrete instantiation over `ℚ`**: `K = 2`, `M = 1`, `x = 0`.
    This witnesses properness with a concrete field and record. -/
theorem MEM_2_strict_concrete :
    let x : Fin 1 → ℚ := fun _ => 0
    LSE (𝔽 := ℚ) (M := 1) 2 [x, x] [x, x] ∧ ¬ LIO 2 [x, x] [x, x] :=
  MEM_2_strict (𝔽 := ℚ) (M := 1) 2 (by norm_num : 2 ≤ 2)
    (by simp [InRange]) (fun _ => 0)

/-- **[2.c.iii] Alternative instantiation with `M = 2`**. -/
theorem MEM_2_strict_M2 :
    let x : Fin 2 → ℚ := ![1, 2]
    LSE (𝔽 := ℚ) (M := 2) 2 [x, x] [x, x] ∧ ¬ LIO 2 [x, x] [x, x] :=
  MEM_2_strict (𝔽 := ℚ) (M := 2) 2 (by norm_num : 2 ≤ 2)
    (by simp [InRange]) ![1, 2]

/-- **[2.c.iv] The failure mode**: `[x,x]` is not `Nodup`.
    This is why `([x,x],[x,x]) ∈ L_SE ∖ L_IO`. -/
theorem duplicate_responses_not_nodup {α : Type*} (x : α) :
    ¬ ([x, x] : List α).Nodup := by simp [List.nodup_cons]

/-! ### [2.d] Documentation: "drops char>K (benign)" delta -/

/-- **[2.d.i] The CORRESPONDENCE delta**: `MEM_2_uSE` needs only `InRange K M`,
    not the paper's `char > K` side condition.

    Paper states `L_IO ≡ L_uSE` for "characteristic > K".
    Lean's `MEM_2_uSE` requires only `hM : InRange K M`, which is `1 ≤ M ≤ K`.
    This is a RELAXATION: the Lean result holds for MORE cases than the paper claims.

    For the
    `L_IO ≡ L_uSE` identity itself (which is just about multiset equality
    vs permutation), no characteristic condition is needed — the algebraic
    content is independent of `p`. The `char > K` is only load-bearing for
    `lem_mio_ldse` (the `L_mIO ≡ L_umLDSE` equivalence). -/
def MEM_2_charK_delta_doc : String :=
  "CORRESPONDENCE delta (Lem:MEM_2): Paper requires char > K; Lean uses only " ++
  "InRange K M. This is a RELAXATION (benign): the L_IO ≡ L_uSE identity " ++
  "holds without characteristic assumptions. The char > K condition is only " ++
  "load-bearing for lem_mio_ldse (L_mIO ≡ L_umLDSE), not for MEM_2 itself."

/-- **[2.d.ii] Verification**: The `MEM_2_uSE` signature has no `CharP` hypothesis
    beyond the section variable — it works for ANY characteristic. -/
example {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p] {M : ℕ}
    (K : ℕ) (hM : InRange K M) (req resp : List (Fin M → 𝔽)) :
    LIO K req resp ↔ LuSE K req resp :=
  -- Works for any characteristic p; no char > K hypothesis needed
  MEM_2_uSE K hM req resp

end MEM_2

/-! ## Summary: Disposition per object -/


def batch5_summary : List (String × String) :=
  [("Lem:MEM_1 (L_IO ⊊ L_mIO)", "passed — subset via MEM_1_subset; " ++
      "strictness via MEM_1_strict instantiated at K=2,R=ℕ,x=0; " ++
      "K=1 degeneracy documented (2≤K load-bearing); " ++
      "CENSUS #6 bidirectional repair confirmed"),
   ("Lem:MEM_2 (L_IO ⊊ L_SE, L_IO ≡ L_uSE)", "passed — biconditional via MEM_2_uSE; " ++
      "subset via MEM_2_subset; " ++
      "strictness via MEM_2_strict instantiated at K=2,M=1,𝔽=ℚ,x=0; " ++
      "char>K relaxation documented (benign)")]

/-! ## Documented deltas reproduced

    1. **2≤K strictness** (MEM_1_strict, MEM_2_strict): Both strict witnesses require
       `2 ≤ K` because the separating element `[x,x]` has length 2, which exceeds
       the `InRange 1` bound at `K=1`. Reproduced in `MEM_1_K1_degeneracy_doc`.

    2.

    3. **char>K drop (benign)**: `MEM_2_uSE` requires only `InRange K M`, not `char > K`.
       This is a relaxation; the algebraic content of `L_IO ≡ L_uSE` is independent of
       characteristic. Reproduced in `MEM_2_charK_delta_doc`. -/

def documented_deltas_reproduced : List String :=
  ["2≤K strictness: MEM_1_strict/MEM_2_strict need 2≤K (witness [x,x] has length 2)",
   "CENSUS #6 bidirectional: LmIO condition-3 is ↔, not ⊆ (repair for lem_mio_ldse)",
   "char>K relaxation: MEM_2_uSE needs InRange K M only, not char>K (benign)"]

/-! ## DRIFT FINDINGS

    **No new drift discovered.** All deviations are documented deltas:
    - 2≤K requirement: expected, documented in CORRESPONDENCE

    - char>K relaxation: expected, documented as benign in CORRESPONDENCE -/

def drift_findings : String :=
  "No new drift discovered. All deviations match documented deltas: " ++
  "(1) 2≤K strictness requirement, (2) CENSUS #6 bidirectional repair, " ++
  "(3) char>K relaxation (benign). See CORRESPONDENCE.md."

end Nock.RedTeam
