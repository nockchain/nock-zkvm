/-
  Nock/IO.lean

  The compute↔memory IO linking — paper §2.1 and §3.1.
  This is what makes the compute
  table's memory *requests* and the memory table's *responses* provably the same
  multiset.

  Builds directly on `Nock/SetEq.lean`:
    * record-set inclusion ⟺ RLC-value-set inclusion (via `RLC_injective`), then
    * `set_inclusion` / `set_inclusion_eq` / `set_inclusion_eq_of_injective`;
    * `SEcond` (multiplicative set-equality) ⟺ record-multiset equality (via unique
      factorization, `roots_multiset_prod_X_sub_C`, + `RLC_injective`).

  Contents
  --------
  §1  Def:MEF records + the record-level IO languages `L_IO`, `L_mIO`,
      characterisations, `Lem:MEM_1`, `Def:unique_request`/`cor_uni_req_uni_resp`.
  §2  The field languages `L_SE = L_MSE≡L_LDSE`, `L_uSE`,
      `L_umLDSE`; `Lem:MEM_2` and `lem_mio_ldse`.
  §3  The extended RAPs `RAP_prog-IO` / `RAP_mem-IO`
      as `Prop`s over adjacent rows (à la `Walk.WalkSat`); `Thm:IO_result`.

  FAITHFULNESS NOTE.  The paper's `L_mIO` lists five conditions
  on `unique_requests`; condition 3 only requires every *request* to appear among the
  `unique_requests`, but NOT the converse.  As written this yields only
  `set(requests) ⊆ set(responses)`, which is strictly weaker than the `set(requests) =
  set(responses)` that the proof of `lem_mio_ldse` explicitly asserts ("the underlying sets
  of responses and requests are equal") and that the equivalence `L_mIO ≡ L_umLDSE`
  requires.  We repair this by reading `unique_requests` as the deduplication of `requests`
  (both membership directions), matching the name and the proof.  See `LmIO`.
-/
import Nock.SetEq

open Polynomial BigOperators
open scoped Classical

namespace Nock
namespace IO

/-- `n ∈ [K]`, i.e. `n ∈ {1, …, K}`. -/
def InRange (K n : ℕ) : Prop := 1 ≤ n ∧ n ≤ K

/-! ## §1  Memory records and the record-level IO languages -/

section Records

/- **`Def:MEF`.**  A memory record `(a,v,t) ∈ 𝒜 × 𝒱𝒟 × 𝒯 = Rec^MEM`.
   The three components play no algebraic role at this level, so we work over an abstract
   record type `R`; the concrete `Rec^MEM = 𝒜 × 𝒱𝒟 × 𝒯` is any such `R`.  A memory record
   *sequence* `Seq^MEM_k` is an ordered list; `Sym_k = Equiv.Perm (Fin k)` acts by
   reordering, so "∃ σ ∈ Sym_k with σ(s) = s'" is exactly `List.Perm s' s`. -/
variable {R : Type*} [DecidableEq R]

/-- **`L_IO^{MEM,K}` — unique IO record matching.**  Pairs
    `(requests, responses)` with `∃ k ∈ [K]` s.t. `responses ∈ Seq_k`, the responses are
    pairwise distinct, and `∃ σ ∈ Sym_k, σ(responses) = requests` — i.e. `requests` is a
    reordering of `responses` (`List.Perm`). -/
def LIO (K : ℕ) (requests responses : List R) : Prop :=
  InRange K responses.length ∧ responses.Nodup ∧ requests.Perm responses

/-- **`L_mIO^{MEM,K}` — IO record matching with multiplicities.**  `requests`
    may repeat; `unique_requests` collects the distinct request records and `responses` is a
    reordering of them.  The literal paper conditions are the five conjuncts below; the last
    membership direction (`x ∈ uniq → x ∈ requests`) is the repair discussed in the
    module header (the paper omits it, but its proof and `lem_mio_ldse` require it). -/
def LmIO (K : ℕ) (requests responses : List R) : Prop :=
  InRange K requests.length ∧
    ∃ uniq : List R,
      uniq.length ≤ requests.length ∧          -- k₂ ≤ k
      uniq.Nodup ∧                               -- unique_requests distinct (cond 4)
      (∀ x, x ∈ requests ↔ x ∈ uniq) ∧           -- cond 3 (→) + REPAIR (←)
      responses.Perm uniq                        -- responses = σ(unique_requests) (cond 5)

/-- `toFinset` characterisation of `L_mIO`: distinct responses whose value-set equals the
    request value-set, with the length bounds `1 ≤ |req| ≤ K` and `|resp| ≤ |req|`. -/
theorem LmIO_iff (K : ℕ) (requests responses : List R) :
    LmIO K requests responses ↔
      (InRange K requests.length ∧ responses.length ≤ requests.length ∧ responses.Nodup
        ∧ requests.toFinset = responses.toFinset) := by
  constructor
  · rintro ⟨hK, uniq, hlen, hnd, hmem, hperm⟩
    refine ⟨hK, ?_, (hperm.nodup_iff).2 hnd, ?_⟩
    · rw [hperm.length_eq]; exact hlen
    · have h1 : requests.toFinset = uniq.toFinset := by
        ext x; simp only [List.mem_toFinset]; exact hmem x
      have h2 : responses.toFinset = uniq.toFinset := List.toFinset_eq_of_perm _ _ hperm
      rw [h1, h2]
  · rintro ⟨hK, hle, hnd, hfin⟩
    refine ⟨hK, responses, hle, hnd, ?_, List.Perm.refl _⟩
    intro x; rw [← List.mem_toFinset, ← List.mem_toFinset, hfin]

/-! ### `Lem:MEM_1`: `L_IO ⊊ L_mIO`. -/

/-- `L_IO ⊆ L_mIO`. -/
theorem MEM_1_subset (K : ℕ) (requests responses : List R)
    (h : LIO K requests responses) : LmIO K requests responses := by
  obtain ⟨hK, hnd, hperm⟩ := h
  rw [LmIO_iff]
  refine ⟨?_, ?_, hnd, List.toFinset_eq_of_perm _ _ hperm⟩
  · rw [hperm.length_eq]; exact hK
  · rw [hperm.length_eq]

/-- Strictness of `L_IO ⊊ L_mIO`: a request sequence with multiplicities lies
    in `L_mIO` but not `L_IO`.  (Needs room `2 ≤ K` — the strict inclusion is vacuous for
    `K = 1`, where multiplicities cannot arise; the paper's "trivial to see" witness.) -/
theorem MEM_1_strict (K : ℕ) (hK : 2 ≤ K) (x : R) :
    LmIO K [x, x] [x] ∧ ¬ LIO K [x, x] [x] := by
  constructor
  · rw [LmIO_iff]
    refine ⟨⟨by norm_num, by simpa using hK⟩, by norm_num, by simp, ?_⟩
    ext y; simp
  · rintro ⟨-, -, hperm⟩
    have := hperm.length_eq
    simp at this

/-! ### `Def:unique_request` / `cor_uni_req_uni_resp`

  At the flattened record level a language is *unique request* if its request records are
  pairwise distinct, and *unique response* if its response records are.  We model these as
  `Nodup` of the respective record lists.  `cor_uni_req_uni_resp` then upgrades an `L_mIO`
  membership to `L_IO` (whence responses are also distinct — unique response). -/

/-- **`Def:unique_request` — unique request.**  The paper's condition
    `(io(i₁)=1) ∩ (io(i₂)=1) ⇒ ((i₁,j₁)≠(i₂,j₂) ⇒ IO_prog(i₁,j₁) ≠ IO_prog(i₂,j₂))`, read at the
    flattened record level, says: distinct compute request slots carry distinct memory records —
    i.e. the request record list has no repeats. -/
def UniqueRequest (requests : List R) : Prop := requests.Nodup

/-- **`Def:unique_request` — unique response.**  Likewise `i ≠ j ⇒ IO_mem(i,·) ≠
    IO_mem(j,·)`: the response record list has no repeats. -/
def UniqueResponse (responses : List R) : Prop := responses.Nodup

/-- **`cor_uni_req_uni_resp`.**  For an `L_mIO` pair whose *requests* are
    distinct (unique request), the responses are distinct too (unique response) and the pair
    already lies in `L_IO`. -/
theorem cor_uni_req_uni_resp (K : ℕ) (requests responses : List R)
    (hreq : requests.Nodup) (h : LmIO K requests responses) :
    LIO K requests responses := by
  rw [LmIO_iff] at h
  obtain ⟨hK, _hle, hnd, hfin⟩ := h
  have hperm : requests.Perm responses := List.perm_of_nodup_nodup_toFinset_eq hreq hnd hfin
  refine ⟨?_, hnd, hperm⟩
  rw [← hperm.length_eq]; exact hK

/-- **`cor_uni_req_uni_resp`, stated in the `Def:unique_request` vocabulary.**  If a
    matched (`L_mIO`) language is unique request then it is unique response — and lies in `L_IO` a
    priori.  This is the corollary the proof of `Thm:IO_result` invokes to obtain
    `(IO_prog,IO_mem) ∈ L_IO` "a priori". -/
theorem ureq_uresp (K : ℕ) (requests responses : List R)
    (hreq : UniqueRequest requests) (h : LmIO K requests responses) :
    UniqueResponse responses ∧ LIO K requests responses :=
  let hlio := cor_uni_req_uni_resp K requests responses hreq h
  ⟨hlio.2.1, hlio⟩

end Records

/-! ## §2  Multiset-argument languages over `MEM = 𝔽^M`

  Following `SetEq.lean`: `𝔽` has characteristic `p`, the RLC variable lives in `𝔽(Y) =
  RatFunc 𝔽`, and the log-derivative variable in `𝔽(X,Y) = RatFunc (RatFunc 𝔽)`.  A memory
  record is `Fin M → 𝔽`. -/

section Field

variable {𝔽 : Type*} [Field 𝔽] {p : ℕ} [CharP 𝔽 p] {M : ℕ}

/-! ### Multiset unique-factorisation over an arbitrary field. -/

section MSInj
variable {L : Type*} [Field L]

/-- Roots of `∏_{c∈s} (X + C c)` are the negated multiset (via `X + C c = X - C (-c)`). -/
theorem roots_ms_prod (s : Multiset L) :
    ((s.map (fun c => X + C c)).prod).roots = s.map (fun c => -c) := by
  have hrw : (s.map (fun c => X + C c))
      = (s.map (fun c => -c)).map (fun d => X - C d) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun c _ => ?_)
    rw [Function.comp_apply, map_neg]; ring
  rw [hrw, Polynomial.roots_multiset_prod_X_sub_C]

/-- **Product ⇔ multiset (unique factorisation).**  `∏(X + C c) = ∏(X + C c')` over two
    multisets iff the multisets coincide. -/
theorem prodXaddC_ms_inj (s t : Multiset L) :
    (s.map (fun c => X + C c)).prod = (t.map (fun c => X + C c)).prod ↔ s = t := by
  constructor
  · intro h
    have hr := congrArg Polynomial.roots h
    rw [roots_ms_prod, roots_ms_prod] at hr
    exact Multiset.map_injective neg_injective hr
  · intro h; rw [h]

end MSInj

/-- **The defining equation of `L_MSE^{Y,K}`** over record *lists*:
    `∏_i (X + RLC^Y(requests(i))) = ∏_j (X + RLC^Y(responses(j)))` in `𝔽(Y)[X]`. -/
def SEcond (requests responses : List (Fin M → 𝔽)) : Prop :=
  (requests.map (fun v => X + C (SetEq.RLC v))).prod
    = (responses.map (fun v => X + C (SetEq.RLC v))).prod

/-- `SEcond` ⟺ the record multisets coincide (via unique factorisation + `RLC_injective`).
    This is the record-level content of `L_SE = L_MSE ≡ L_LDSE`. -/
theorem SEcond_iff (requests responses : List (Fin M → 𝔽)) :
    SEcond requests responses ↔ (↑requests : Multiset (Fin M → 𝔽)) = ↑responses := by
  unfold SEcond
  have hmap : ∀ l : List (Fin M → 𝔽),
      (l.map (fun v => X + C (SetEq.RLC v))).prod
        = (((↑l : Multiset (Fin M → 𝔽)).map SetEq.RLC).map (fun c => X + C c)).prod := by
    intro l
    rw [Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe, List.map_map]
    rfl
  rw [hmap requests, hmap responses, prodXaddC_ms_inj]
  constructor
  · intro h
    exact Multiset.map_injective (SetEq.RLC_injective) h
  · intro h; rw [h]

/-- **`L_SE^{Y,K}(𝔽) = L_MSE ≡ L_LDSE`.**  Bounds `k₁,k₂,M ∈ [K]` plus
    the multiplicative set-equality equation. -/
def LSE (K : ℕ) (requests responses : List (Fin M → 𝔽)) : Prop :=
  InRange K requests.length ∧ InRange K responses.length ∧ InRange K M
    ∧ SEcond requests responses

/-- **`L_uSE^{Y,K}(𝔽)`.**  `L_SE` restricted to distinct responses. -/
def LuSE (K : ℕ) (requests responses : List (Fin M → 𝔽)) : Prop :=
  LSE K requests responses ∧ responses.Nodup

/-- **`L_umLDSE^{Y,K}(𝔽)`.**  Distinct responses, and there is a nonzero
    multiplicity vector `m ∈ (𝔽_p∖{0})^{k₂}` with
    `Σ_i 1/(X + RLC(req_i)) = Σ_j m_j / (X + RLC(resp_j))`. -/
def LumLDSE (K : ℕ) (requests responses : List (Fin M → 𝔽)) : Prop :=
  InRange K requests.length ∧ InRange K responses.length ∧ InRange K M
    ∧ responses.Nodup
    ∧ ∃ m : Fin responses.length → ZMod p,
        (∀ j, m j ≠ 0) ∧
        (∑ i : Fin requests.length, SetEq.frac (SetEq.RLC (requests.get i))
          = ∑ j : Fin responses.length,
              (SetEq.castZ p (m j) : RatFunc 𝔽) • SetEq.frac (SetEq.RLC (responses.get j)))

/-! ### RLC-value image bridge. -/

/-- The set of records of a list is the image of `get` over all indices. -/
theorem image_univ_get {R : Type*} [DecidableEq R] (l : List R) :
    Finset.univ.image l.get = l.toFinset := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩; exact List.get_mem _ _
  · intro ha
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem ha
    exact ⟨⟨i, hi⟩, by simpa [List.get_eq_getElem] using hget⟩

/-- The RLC-value image of a record list is `l.toFinset.image RLC`. -/
theorem image_univ_RLC_get (l : List (Fin M → 𝔽)) :
    Finset.univ.image (fun i : Fin l.length => SetEq.RLC (l.get i))
      = l.toFinset.image SetEq.RLC := by
  rw [show (fun i : Fin l.length => SetEq.RLC (l.get i))
        = SetEq.RLC ∘ l.get from rfl, ← Finset.image_image, image_univ_get]

/-- **The image bridge (via `RLC_injective`).**  Equality of the RLC-value sets of two record
    lists is equivalent to equality of their record sets.  This is the reduction the paper
    uses to feed `lem:set_inclusion` (whose `S ⊆ T` is on RLC-values) from record-set
    equality (the IO-language content). -/
theorem RLC_image_eq_iff (req resp : List (Fin M → 𝔽)) :
    (Finset.univ.image (fun i : Fin req.length => SetEq.RLC (req.get i))
        = Finset.univ.image (fun j : Fin resp.length => SetEq.RLC (resp.get j)))
      ↔ req.toFinset = resp.toFinset := by
  rw [image_univ_RLC_get, image_univ_RLC_get]
  exact (Finset.image_injective SetEq.RLC_injective).eq_iff

/-! ### `Lem:MEM_2`: `L_IO ⊊ L_SE` and `L_IO ≡ L_uSE`. -/

/-- **`Lem:MEM_2`(2): `L_IO ≡ L_uSE`.**  The identity map; both say "distinct
    responses, and the request/response record multisets coincide".  Needs `M ∈ [K]`. -/
theorem MEM_2_uSE (K : ℕ) (hM : InRange K M) (req resp : List (Fin M → 𝔽)) :
    LIO K req resp ↔ LuSE K req resp := by
  constructor
  · rintro ⟨hK, hnd, hperm⟩
    refine ⟨⟨?_, hK, hM, ?_⟩, hnd⟩
    · rw [hperm.length_eq]; exact hK
    · rw [SEcond_iff]; exact Multiset.coe_eq_coe.mpr hperm
  · rintro ⟨⟨_, hK, _, hse⟩, hnd⟩
    refine ⟨hK, hnd, ?_⟩
    rw [SEcond_iff] at hse; exact Multiset.coe_eq_coe.mp hse

/-- **`Lem:MEM_2`(1): `L_IO ⊆ L_SE`.** -/
theorem MEM_2_subset (K : ℕ) (hM : InRange K M) (req resp : List (Fin M → 𝔽))
    (h : LIO K req resp) : LSE K req resp :=
  ((MEM_2_uSE K hM req resp).mp h).1

/-- Strictness of `L_IO ⊊ L_SE`: a pair with repeated responses lies in
    `L_SE` but not `L_IO` (needs `2 ≤ K` and `M ∈ [K]`). -/
theorem MEM_2_strict (K : ℕ) (hK : 2 ≤ K) (hM : InRange K M) (x : Fin M → 𝔽) :
    LSE K [x, x] [x, x] ∧ ¬ LIO K [x, x] [x, x] := by
  refine ⟨⟨⟨by norm_num, by simpa using hK⟩, ⟨by norm_num, by simpa using hK⟩, hM, ?_⟩, ?_⟩
  · rw [SEcond_iff]
  · rintro ⟨-, hnd, -⟩; simp at hnd

/-! ### `lem_mio_ldse`: `L_mIO ≡ L_umLDSE`. -/

/-- **`lem_mio_ldse`: `L_mIO ≡ L_umLDSE`** for `MEM = 𝔽^M` with
    `char 𝔽 = p > K ≥ M`.  Both are the identity image of "distinct responses with matching
    request/response value-sets"; the bridge is `lem:set_inclusion` in the `S = T` /
    `injective b, mᵢ≠0` forms, fed by `RLC_image_eq_iff`. -/
theorem mio_ldse (K : ℕ) (hKp : K < p) (hM : InRange K M) (req resp : List (Fin M → 𝔽)) :
    LmIO K req resp ↔ LumLDSE K req resp := by
  rw [LmIO_iff]
  -- index-length bounds below the characteristic
  constructor
  · rintro ⟨hKreq, hle, hnd, hfin⟩
    -- responses nonempty & bounded
    have hrespne : 1 ≤ resp.length := by
      have hpos : 0 < req.toFinset.card := by
        apply Finset.card_pos.mpr
        obtain ⟨x, hx⟩ : ∃ x, x ∈ req := by
          cases req with
          | nil => exact absurd hKreq.1 (by norm_num)
          | cons y ys => exact ⟨y, by simp⟩
        exact ⟨x, List.mem_toFinset.mpr hx⟩
      rw [hfin] at hpos
      have hle2 : resp.toFinset.card ≤ resp.length := List.toFinset_card_le _
      omega
    have hRresp : InRange K resp.length := ⟨hrespne, le_trans hle hKreq.2⟩
    -- feed set_inclusion_eq via the image bridge
    have himg := (RLC_image_eq_iff req resp).mpr hfin
    have hk₁ : req.length < p := lt_of_le_of_lt hKreq.2 hKp
    have hk₂ : resp.length < p := lt_of_le_of_lt hRresp.2 hKp
    obtain ⟨m, hm, hsum⟩ :=
      SetEq.set_inclusion_eq hk₁ hk₂
        (fun i => SetEq.RLC (req.get i)) (fun j => SetEq.RLC (resp.get j)) himg
    exact ⟨hKreq, hRresp, hM, hnd, m, hm, hsum⟩
  · rintro ⟨hKreq, hKresp, _, hnd, m, hm, hsum⟩
    have hk₁ : req.length < p := lt_of_le_of_lt hKreq.2 hKp
    have hk₂ : resp.length < p := lt_of_le_of_lt hKresp.2 hKp
    have hbinj : Function.Injective (fun j : Fin resp.length => SetEq.RLC (resp.get j)) :=
      SetEq.RLC_injective.comp (List.nodup_iff_injective_get.mp hnd)
    have himg :=
      SetEq.set_inclusion_eq_of_injective hk₁ hk₂
        (fun i => SetEq.RLC (req.get i)) (fun j => SetEq.RLC (resp.get j)) hbinj m hm hsum
    have hfin := (RLC_image_eq_iff req resp).mp himg
    refine ⟨hKreq, ?_, hnd, hfin⟩
    -- |resp| = |resp.toFinset| = |req.toFinset| ≤ |req|
    calc resp.length = resp.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = req.toFinset.card := by rw [hfin]
      _ ≤ req.length := List.toFinset_card_le _

/-! ## §3  The IO accumulator RAPs and `Thm:IO_result` -/

/-! ### The accumulator columns as `Prop`s over adjacent rows (à la `Walk.WalkSat`).

  Over a field `L`, the log-derivative accumulator aggregates `frac c = 1/(X+c)` summands.
  In the IO setting `L = 𝔽(Y) = RatFunc 𝔽` and the accumulator values live in
  `𝔽(X,Y) = RatFunc L`.  The paper's aggregation constraints are the
  cleared-denominator (division-free) *polynomial* encodings of the divided per-row rules
  below; over `L(X)` the denominators `X + RLC(·)` are units, so the two are equivalent and
  we take the divided form as the row constraint.  The `io(i)`/`ver(i)` selectors and the
  per-opcode `regs` grouping only determine *which* rows contribute a summand; flattening to
  the sequence of contributed records leaves the terminal sum unchanged, so we index the
  accumulator directly by the contributed records `1..k`. -/

section Accumulators

variable {L : Type*} [Field L]

/-- **`RAP_prog-IO` accumulator.**  `acc_prog` starts at `0`, each of the
    `k₁` requested records adds its `frac = 1/(X + RLC(record))`, and the terminal
    `requests ∈ 𝕂` is the last accumulator value. -/
structure ProgIOSat (a : ℕ → L) (acc : ℕ → RatFunc L) (requests : RatFunc L) (k₁ : ℕ) :
    Prop where
  /-- Empty accumulator to start (the paper's `acc_prog(0)`). -/
  init : acc 0 = 0
  /-- Per-row aggregation: add `1/(X + RLC(record i))`. -/
  step : ∀ i, i < k₁ → acc (i + 1) = acc i + SetEq.frac (a i)
  /-- Terminal output `requests = acc_prog(h₁)`. -/
  term : requests = acc k₁

/-- The prog accumulator telescopes to the partial log-derivative sum. -/
theorem progIO_closed {a : ℕ → L} {acc : ℕ → RatFunc L} {requests : RatFunc L} {k₁ : ℕ}
    (hP : ProgIOSat a acc requests k₁) :
    ∀ j, j ≤ k₁ → acc j = ∑ i ∈ Finset.range j, SetEq.frac (a i) := by
  intro j
  induction j with
  | zero => intro _; simpa using hP.init
  | succ n ih =>
    intro hle
    rw [hP.step n (by omega), ih (by omega), Finset.sum_range_succ]

/-- **Terminal `requests` = the full request log-derivative sum** `Σ 1/(X + RLC(req_i))`. -/
theorem progIO_requests {a : ℕ → L} {acc : ℕ → RatFunc L} {requests : RatFunc L} {k₁ : ℕ}
    (hP : ProgIOSat a acc requests k₁) :
    requests = ∑ i : Fin k₁, SetEq.frac (a i) := by
  rw [hP.term, progIO_closed hP k₁ le_rfl, Finset.sum_range]

/-- **`RAP_mem-IO` accumulator.**  `acc_mem` is seeded by `responses`,
    each verified record (`ver(i)`, here as a scalar multiplicity `μ i`) *removes* its
    `μ i · frac`, and the terminal `out_mem ∈ 𝕂` is the last accumulator value. -/
structure MemIOSat (b : ℕ → L) (μ : ℕ → L) (acc : ℕ → RatFunc L)
    (responses out_mem : RatFunc L) (k₂ : ℕ) : Prop where
  /-- Seeded by `responses` (the paper's `acc_mem(0)`). -/
  init : acc 0 = responses
  /-- Per-row aggregation: remove `μ i · 1/(X + RLC(record i))`. -/
  step : ∀ i, i < k₂ → acc (i + 1) = acc i - μ i • SetEq.frac (b i)
  /-- Terminal output `out_mem = acc_mem(h₂)`. -/
  term : out_mem = acc k₂

/-- The mem accumulator telescopes: `acc = responses − partial sum`. -/
theorem memIO_closed {b μ : ℕ → L} {acc : ℕ → RatFunc L} {responses out_mem : RatFunc L}
    {k₂ : ℕ} (hM : MemIOSat b μ acc responses out_mem k₂) :
    ∀ j, j ≤ k₂ → acc j = responses - ∑ i ∈ Finset.range j, μ i • SetEq.frac (b i) := by
  intro j
  induction j with
  | zero => intro _; simpa using hM.init
  | succ n ih =>
    intro hle
    rw [hM.step n (by omega), ih (by omega), Finset.sum_range_succ]; ring

/-- **Terminal `out_mem` = `responses − Σ μ_j · 1/(X + RLC(resp_j))`.** -/
theorem memIO_out {b μ : ℕ → L} {acc : ℕ → RatFunc L} {responses out_mem : RatFunc L}
    {k₂ : ℕ} (hM : MemIOSat b μ acc responses out_mem k₂) :
    out_mem = responses - ∑ i : Fin k₂, μ i • SetEq.frac (b i) := by
  rw [hM.term, memIO_closed hM k₂ le_rfl, Finset.sum_range]

end Accumulators

/-! ### §3.5  The paper's LITERAL selector-weighted, cleared-denominator IO gates

  The `ProgIOSat`/`MemIOSat` above are the *flattened divided per-record* forms of the paper's
  RAP constraints (each row contributes a single `frac = 1/(X + RLC)` summand).  This block adds
  the paper's **literal** polynomial gates — the `x_prog(i,l)`/`ver(i)`-selector-weighted,
  product-over-registers, cleared-denominator constraints — and
  proves `progIO_collapse`/`memIO_collapse`, genuine `⟺`s to the flattened forms, mirroring
  `Nock.Walk.paperWalkSat_collapse`.

  Over `RatFunc L` (the log-derivative variable `X` playing the role of `−β`), the paper's pole
  `RLC^α(record) − β` is `pole c := X + C c`, a unit with `pole c · frac c = 1`.  Clearing this
  unit turns each divided per-row rule into the paper's polynomial gate and back — the source of
  the equivalences.  We keep the accumulator indexed as the paper's **per-record flattening**: one
  accumulator row per contributed record (so `io ≡ 1` on the prog side, `regs` of the active
  opcode `= 1`), which is exactly the setting `ProgIOSat`/`MemIOSat` model. -/

section PaperGates

variable {L : Type*} [Field L]

/-- **The pole `RLC^α(record) − β` as a `RatFunc L` unit.**  With the
    log-derivative variable `X = −β`, this is `X + C c`; it is the denominator whose inverse is
    `SetEq.frac c`.  The paper's cleared-denominator gates multiply through by these poles. -/
noncomputable def pole (c : L) : RatFunc L :=
  algebraMap (Polynomial L) (RatFunc L) (Polynomial.X + Polynomial.C c)

/-- The pole is nonzero (`X + C c` is monic of degree 1). -/
theorem pole_ne_zero (c : L) : pole c ≠ 0 := SetEq.algebraMap_poleP_ne_zero c

/-- **`pole c · frac c = 1`.**  This unit-ness of the pole is what makes the cleared-denominator
    (polynomial) gate equivalent to the divided per-row rule. -/
theorem pole_mul_frac (c : L) : pole c * SetEq.frac c = 1 := by
  unfold pole SetEq.frac
  exact mul_inv_cancel₀ (SetEq.algebraMap_poleP_ne_zero c)

/-! #### The generic selector gate ⟺ divided rule (shared by prog seeding/removal, mem) -/

/-- **The cleared-denominator selector gate ⟺ its divided rule.**  For a boolean selector
    `w ∈ {0,1}` (encoded `w·(w−1)=0`) and a pole/`frac` pair (`pole·frac = 1`), the paper's
    literal gate `w · pole · (u − v) = (u − v)·(1 − w) + w` holds **iff**
    `v = u − w·frac`.  When `w = 0` the record is not accounted (`v = u`); when `w = 1` it is
    (`v = u − frac`).  This is the algebraic heart of both the prog and mem collapses. -/
theorem gate_iff {w u v poleV fracV : RatFunc L}
    (hb : w * (w - 1) = 0) (hpf : poleV * fracV = 1) :
    (w * poleV * (u - v) = (u - v) * (1 - w) + w) ↔ (v = u - w * fracV) := by
  have hpole : poleV ≠ 0 := left_ne_zero_of_mul_eq_one hpf
  rcases mul_eq_zero.mp hb with hw | hw
  · subst hw
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  · have hw1 : w = 1 := sub_eq_zero.mp hw
    subst hw1
    constructor
    · intro h
      have h' : poleV * (u - v) = poleV * fracV := by rw [hpf]; linear_combination h
      have hc := mul_left_cancel₀ hpole h'
      linear_combination -hc
    · intro h
      have hc : u - v = fracV := by linear_combination -h
      linear_combination poleV * hc + hpf

/-! #### `RAP_prog-IO` — the `io(i)` selector, literal gate, and collapse -/

/-- **`io(i)` — the IO-active selector.**  `io(i) := Σ_{l∈OP_IO} x_prog(i,l)`, the
    sum of the row's one-hot opcode selectors over the memory-reading opcodes `OP_IO`. -/
noncomputable def ioSel {numOps : ℕ} (xprog : Fin numOps → RatFunc L) : RatFunc L := ∑ l, xprog l

/-- **`RAP_prog-IO` literal aggregation gate.**  The paper's degree-`1+M_IO`
    cleared-denominator constraint, indexed 0-based (the transition `acc(i) → acc(i+1)`): the
    `x_prog(i,l)`-selector-weighted product `∏_{k=1}^{regs(l)}(RLC−β)` over the opcode's registers,
    times the accumulator increment, equals the `(1 − io(i))` no-op branch plus the `x_prog(i,m)`-
    weighted derivative sum `Σ_{l=1}^{regs(m)} ∏_{k≠l}(RLC−β)`. -/
structure PaperProgIOSat {numOps : ℕ} (regs : Fin numOps → ℕ)
    (xprog : ℕ → Fin numOps → RatFunc L) (rlc : ℕ → ℕ → L)
    (acc : ℕ → RatFunc L) (requests : RatFunc L) (k₁ : ℕ) : Prop where
  /-- Empty accumulator to start (the paper's `acc_prog(0)`). -/
  init : acc 0 = 0
  /-- The literal selector-weighted, product-over-regs, cleared-denominator gate. -/
  step : ∀ i, i < k₁ →
    (∑ l, xprog i l * ∏ k ∈ Finset.Icc 1 (regs l), pole (rlc i k)) * (acc (i + 1) - acc i)
      = (acc (i + 1) - acc i) * (1 - ∑ l, xprog i l)
        + ∑ m, xprog i m *
            (∑ l ∈ Finset.Icc 1 (regs m),
              ∏ k ∈ (Finset.Icc 1 (regs m)).erase l, pole (rlc i k))
  /-- Terminal output `requests = acc_prog(h₁)`. -/
  term : requests = acc k₁

/-- **Product/derivative identity.**  `(∏_{k=1}^{r} pole_k) · (Σ_{l=1}^{r} frac_l) =
    Σ_{l=1}^{r} ∏_{k≠l} pole_k`: multiplying the log-derivative sum by the full pole product clears
    each denominator, leaving the paper's derivative-of-product term.  This is what
    makes the cleared-denominator prog gate equivalent to "add all `regs(op)` fracs". -/
theorem prod_frac_identity {r : ℕ} (rlci : ℕ → L) :
    (∏ k ∈ Finset.Icc 1 r, pole (rlci k)) * (∑ l ∈ Finset.Icc 1 r, SetEq.frac (rlci l))
      = ∑ l ∈ Finset.Icc 1 r, ∏ k ∈ (Finset.Icc 1 r).erase l, pole (rlci k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have h1 : ∏ k ∈ Finset.Icc 1 r, pole (rlci k)
      = pole (rlci l) * ∏ k ∈ (Finset.Icc 1 r).erase l, pole (rlci k) :=
    (Finset.mul_prod_erase _ (fun k => pole (rlci k)) hl).symm
  rw [h1,
    show pole (rlci l) * (∏ k ∈ (Finset.Icc 1 r).erase l, pole (rlci k)) * SetEq.frac (rlci l)
      = (∏ k ∈ (Finset.Icc 1 r).erase l, pole (rlci k)) * (pole (rlci l) * SetEq.frac (rlci l)) by
        ring,
    pole_mul_frac, mul_one]

/-- **One-hot collapse of the prog gate for an active row.**  Under one-hot
    `x_prog(i,·)` with active opcode `oprow` (so `io(i) = 1`), the literal aggregation gate holds
    **iff** the increment `Δ` equals the sum of the active opcode's register fracs,
    `Δ = Σ_{l=1}^{regs(oprow)} frac(rlc(i,l))`.  This genuinely exercises the product-over-regs and
    the derivative sum (via `prod_frac_identity`) for arbitrary `regs`. -/
theorem paperProgIO_active_gate_iff {numOps : ℕ} {regs : Fin numOps → ℕ}
    {xprog : Fin numOps → RatFunc L} {oprow : Fin numOps} {rlci : ℕ → L}
    (hoh : ∀ j, xprog j = if j = oprow then 1 else 0) (Δ : RatFunc L) :
    ((∑ l, xprog l * ∏ k ∈ Finset.Icc 1 (regs l), pole (rlci k)) * Δ
       = Δ * (1 - ∑ l, xprog l)
         + ∑ m, xprog m *
             (∑ l ∈ Finset.Icc 1 (regs m), ∏ k ∈ (Finset.Icc 1 (regs m)).erase l, pole (rlci k)))
      ↔ Δ = ∑ l ∈ Finset.Icc 1 (regs oprow), SetEq.frac (rlci l) := by
  have hA : (∑ l, xprog l * ∏ k ∈ Finset.Icc 1 (regs l), pole (rlci k))
      = ∏ k ∈ Finset.Icc 1 (regs oprow), pole (rlci k) := by
    simp only [hoh, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hE : (∑ l, xprog l) = 1 := by
    simp only [hoh, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hB : (∑ m, xprog m *
        (∑ l ∈ Finset.Icc 1 (regs m), ∏ k ∈ (Finset.Icc 1 (regs m)).erase l, pole (rlci k)))
      = ∑ l ∈ Finset.Icc 1 (regs oprow),
          ∏ k ∈ (Finset.Icc 1 (regs oprow)).erase l, pole (rlci k) := by
    simp only [hoh, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hA, hE, hB]
  have hprod : (∏ k ∈ Finset.Icc 1 (regs oprow), pole (rlci k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pole_ne_zero (rlci k))
  have hid := prod_frac_identity (r := regs oprow) rlci
  constructor
  · intro h
    have h' : (∏ k ∈ Finset.Icc 1 (regs oprow), pole (rlci k)) * Δ
        = (∏ k ∈ Finset.Icc 1 (regs oprow), pole (rlci k))
            * (∑ l ∈ Finset.Icc 1 (regs oprow), SetEq.frac (rlci l)) := by
      rw [hid]; linear_combination h
    exact mul_left_cancel₀ hprod h'
  · intro h; rw [h]; linear_combination hid

/-- **`progIO_collapse`: the literal `RAP_prog-IO` gate ⟺ `ProgIOSat`.**  Under
    one-hot selectors with active opcode `oprow i` on each accumulator row (so `io ≡ 1`, the
    per-record flattening) and one register per request (`regs(oprow i) = 1`), the paper's literal
    aggregation gate is equivalent to the flattened divided form `ProgIOSat` (which adds a single
    `frac(rlc(i,1))` per row).  A genuine `⟺`, not a weakening. -/
theorem progIO_collapse {numOps : ℕ} {regs : Fin numOps → ℕ}
    {xprog : ℕ → Fin numOps → RatFunc L} {oprow : ℕ → Fin numOps}
    {rlc : ℕ → ℕ → L} {acc : ℕ → RatFunc L} {requests : RatFunc L} {k₁ : ℕ}
    (hoh : ∀ i j, xprog i j = if j = oprow i then 1 else 0)
    (hregs : ∀ i, regs (oprow i) = 1) :
    PaperProgIOSat regs xprog rlc acc requests k₁
      ↔ ProgIOSat (fun i => rlc i 1) acc requests k₁ := by
  have hsum1 : ∀ i, (∑ l ∈ Finset.Icc 1 (regs (oprow i)), SetEq.frac (rlc i l))
      = SetEq.frac (rlc i 1) := by
    intro i; rw [hregs i, Finset.Icc_self, Finset.sum_singleton]
  constructor
  · intro P
    refine { init := P.init, term := P.term, step := ?_ }
    intro i hi
    have hg := (paperProgIO_active_gate_iff (regs := regs)
      (oprow := oprow i) (rlci := rlc i) (hoh i) (acc (i + 1) - acc i)).mp (P.step i hi)
    rw [hsum1 i] at hg
    linear_combination hg
  · intro P
    refine { init := P.init, term := P.term, step := ?_ }
    intro i hi
    apply (paperProgIO_active_gate_iff (regs := regs)
      (oprow := oprow i) (rlci := rlc i) (hoh i) (acc (i + 1) - acc i)).mpr
    rw [hsum1 i]
    have hs := P.step i hi
    linear_combination hs

/-! #### `ver` column + booleanity, and the mem-IO gates -/

/-- **Booleanity of the `ver` column.**  `ver(i)·(ver(i) − 1) = 0` for every row —
    the `ver ∈ {0,1}^{h₂}` boolean column witnessing whether a memory access is verified.  As a
    multiplicity this is the unique-response specialization `μ = ver` of the generic `MemIOSat`
    multiplicity `μ`. -/
def BoolCol (ver : ℕ → L) : Prop := ∀ i, ver i * (ver i - 1) = 0

/-- Booleanity ⟺ each entry is `0` or `1`. -/
theorem boolCol_iff {ver : ℕ → L} : BoolCol ver ↔ ∀ i, ver i = 0 ∨ ver i = 1 := by
  constructor
  · intro h i
    rcases mul_eq_zero.mp (h i) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · intro h i
    rcases h i with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring

/-- Booleanity transports through the embedding `L → RatFunc L`. -/
theorem embBool {c : L} (h : c * (c - 1) = 0) :
    algebraMap L (RatFunc L) c * (algebraMap L (RatFunc L) c - 1) = 0 := by
  have h2 : algebraMap L (RatFunc L) (c * (c - 1)) = 0 := by rw [h, map_zero]
  rwa [map_mul, map_sub, map_one] at h2

/-- **`RAP_mem-IO` literal seeding + removal gates.**  The boolean `ver`
    column, the initial `responses = acc_mem(0)`, the
    literal `ver`-selector-weighted, cleared-denominator **seeding** gate at the first record relating `responses` and `acc_mem(1)`, the same-shape
    **removal** gates for the remaining records, and the terminal `out_mem = acc_mem(h₂)`.
    Indexed 0-based: record `i` drives the transition `acc(i) → acc(i+1)`. -/
structure PaperMemIOSat (ver rec : ℕ → L) (acc : ℕ → RatFunc L)
    (responses out_mem : RatFunc L) (k₂ : ℕ) : Prop where
  /-- `ver` is a boolean column. -/
  boolver : BoolCol ver
  /-- `responses` is the first element of `acc_mem`. -/
  init : acc 0 = responses
  /-- Literal seeding gate at the first record. -/
  seed : algebraMap L (RatFunc L) (ver 0) * pole (rec 0) * (responses - acc 1)
      = (responses - acc 1) * (1 - algebraMap L (RatFunc L) (ver 0))
        + algebraMap L (RatFunc L) (ver 0)
  /-- Literal degree-3 removal gates for the remaining records. -/
  step : ∀ i, 1 ≤ i → i < k₂ →
      algebraMap L (RatFunc L) (ver i) * pole (rec i) * (acc i - acc (i + 1))
        = (acc i - acc (i + 1)) * (1 - algebraMap L (RatFunc L) (ver i))
          + algebraMap L (RatFunc L) (ver i)
  /-- Terminal output `out_mem = acc_mem(h₂)`. -/
  term : out_mem = acc k₂

/-- **`memIO_collapse`: the literal `RAP_mem-IO` gates ⟺ `MemIOSat`.**  For
    at least one response (`1 ≤ k₂`), the paper's literal booleanity + seeding + removal gates are
    equivalent to booleanity of `ver` together with the flattened divided form `MemIOSat` with the
    multiplicity `μ` specialized to the boolean `ver` column.  The seeding gate is the removal rule
    at the seed `responses = acc(0)`.  A genuine `⟺`, not a weakening. -/
theorem memIO_collapse {ver rec : ℕ → L} {acc : ℕ → RatFunc L}
    {responses out_mem : RatFunc L} {k₂ : ℕ} (hk₂ : 1 ≤ k₂) :
    PaperMemIOSat ver rec acc responses out_mem k₂
      ↔ (BoolCol ver ∧ MemIOSat rec ver acc responses out_mem k₂) := by
  constructor
  · intro P
    refine ⟨P.boolver, { init := P.init, term := P.term, step := ?_ }⟩
    intro i hi
    have hbool := embBool (P.boolver i)
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hg := (gate_iff hbool (pole_mul_frac (rec 0))).mp P.seed
      rw [P.init, Algebra.smul_def]
      exact hg
    · have hg := (gate_iff hbool (pole_mul_frac (rec i))).mp (P.step i hpos hi)
      rw [Algebra.smul_def]
      exact hg
  · rintro ⟨hbc, M⟩
    refine { boolver := hbc, init := M.init, term := M.term, seed := ?_, step := ?_ }
    · have hbool := embBool (hbc 0)
      apply (gate_iff hbool (pole_mul_frac (rec 0))).mpr
      have h0 := M.step 0 hk₂
      rw [Algebra.smul_def, M.init] at h0
      exact h0
    · intro i _ hi2
      have hbool := embBool (hbc i)
      apply (gate_iff hbool (pole_mul_frac (rec i))).mpr
      have hs := M.step i hi2
      rw [Algebra.smul_def] at hs
      exact hs

/-- **Unique-response specialization `μ = ver ≡ 1`.**  When every response is
    verified (`ver ≡ 1`, the unique-response / no-multiplicities setting), each `MemIOSat` step
    removes exactly one `frac` — the paper's basic (multiplicity-free) accumulator. -/
theorem memIO_ver_one {ver rec : ℕ → L} {acc : ℕ → RatFunc L}
    {responses out_mem : RatFunc L} {k₂ : ℕ} (hone : ∀ i, ver i = 1)
    (M : MemIOSat rec ver acc responses out_mem k₂) :
    ∀ i, i < k₂ → acc (i + 1) = acc i - SetEq.frac (rec i) := by
  intro i hi
  have hs := M.step i hi
  rw [hone i, one_smul] at hs
  exact hs

end PaperGates

/-- The mem-side multiplicities: cast the `𝔽_p` vector `m` into `L = 𝔽(Y)` (`0` past `k₂`).
    For `ver ∈ {0,1}` (unique response) all entries are `1`; in general these are the
    `set_inclusion` multiplicities of `L_umLDSE`. -/
noncomputable def castμ {k₂ : ℕ} (m : Fin k₂ → ZMod p) : ℕ → RatFunc 𝔽 :=
  fun i => if h : i < k₂ then (SetEq.castZ p (m ⟨i, h⟩)) else 0

theorem castμ_fin {k₂ : ℕ} (m : Fin k₂ → ZMod p) (i : Fin k₂) :
    castμ (𝔽 := 𝔽) m (i : ℕ) = SetEq.castZ p (m i) := by
  simp only [castμ, i.isLt, dif_pos]

/-- **`Thm:IO_result`, algebraic core.**  For a unique-request
    language the IO consistency reduces (via `cor_uni_req_uni_resp`) to `(IO_prog,IO_mem) ∈
    L_IO`, and the aggregation + terminal constraints are — by `lem:set_inclusion` — exactly
    `L_umLDSE` membership.  Concretely: there exist accumulator columns and a nonzero
    multiplicity vector for which both extended RAPs are satisfied and the two IO consistency
    checks hold **iff** the request
    and response RLC-value sets coincide (the `L_mIO`/`L_IO` content).

    Hypotheses: `k₁,k₂ < p` (`char > K`) and response records with distinct RLC (`hbinj`, i.e.
    unique response — guaranteed by `cor_uni_req_uni_resp` for unique-request languages). -/
theorem io_result {k₁ k₂ : ℕ} (hk₁ : k₁ < p) (hk₂ : k₂ < p)
    (a b : ℕ → (Fin M → 𝔽))
    (hbinj : Function.Injective (fun j : Fin k₂ => SetEq.RLC (b j))) :
    (∃ (m : Fin k₂ → ZMod p) (accP accM : ℕ → RatFunc (RatFunc 𝔽))
        (requests responses out_mem : RatFunc (RatFunc 𝔽)),
        (∀ j, m j ≠ 0)
        ∧ ProgIOSat (fun i => SetEq.RLC (a i)) accP requests k₁
        ∧ MemIOSat (fun i => SetEq.RLC (b i)) (castμ m) accM responses out_mem k₂
        ∧ requests = responses ∧ out_mem = 0)
      ↔ Finset.univ.image (fun i : Fin k₁ => SetEq.RLC (a i))
          = Finset.univ.image (fun j : Fin k₂ => SetEq.RLC (b j)) := by
  constructor
  · rintro ⟨m, accP, accM, requests, responses, out_mem, hm, hP, hM, hrr, hout⟩
    -- terminal outputs = the log-derivative sums
    have hreq := progIO_requests hP
    have houtsum := memIO_out hM
    rw [hout] at houtsum
    replace houtsum := sub_eq_zero.mp houtsum.symm
    -- rewrite the mem side's `castμ m ↑j` as `castZ (m j)`
    have hmemsum : responses
        = ∑ j : Fin k₂, (SetEq.castZ p (m j) : RatFunc 𝔽) • SetEq.frac (SetEq.RLC (b j)) := by
      rw [houtsum]
      exact Finset.sum_congr rfl (fun j _ => by rw [castμ_fin])
    have heq : (∑ i : Fin k₁, SetEq.frac (SetEq.RLC (a i)))
        = ∑ j : Fin k₂, (SetEq.castZ p (m j) : RatFunc 𝔽) • SetEq.frac (SetEq.RLC (b j)) := by
      rw [← hreq, ← hmemsum, hrr]
    exact SetEq.set_inclusion_eq_of_injective hk₁ hk₂
      (fun i => SetEq.RLC (a i)) (fun j => SetEq.RLC (b j)) hbinj m hm heq
  · intro himg
    obtain ⟨m, hm, hsum⟩ :=
      SetEq.set_inclusion_eq hk₁ hk₂
        (fun i => SetEq.RLC (a i)) (fun j => SetEq.RLC (b j)) himg
    -- build the accumulators explicitly
    set requests : RatFunc (RatFunc 𝔽) := ∑ i : Fin k₁, SetEq.frac (SetEq.RLC (a i)) with hreqdef
    refine ⟨m, (fun j => ∑ i ∈ Finset.range j, SetEq.frac (SetEq.RLC (a i))),
      (fun j => requests - ∑ i ∈ Finset.range j, castμ (𝔽 := 𝔽) m i • SetEq.frac (SetEq.RLC (b i))),
      requests, requests, 0, hm, ?_, ?_, rfl, rfl⟩
    · exact
      { init := by simp
        step := fun i _ => by rw [Finset.sum_range_succ]
        term := by rw [hreqdef, Finset.sum_range] }
    · refine
      { init := by simp
        step := fun i _ => by rw [Finset.sum_range_succ]; ring
        term := ?_ }
      -- term : (0 : RatFunc (RatFunc 𝔽)) = requests − Σ_{range k₂} castμ m i • frac(resp i)
      show (0 : RatFunc (RatFunc 𝔽))
        = requests - ∑ i ∈ Finset.range k₂, castμ (𝔽 := 𝔽) m i • SetEq.frac (SetEq.RLC (b i))
      have hcast : (∑ i ∈ Finset.range k₂, castμ (𝔽 := 𝔽) m i • SetEq.frac (SetEq.RLC (b i)))
          = ∑ j : Fin k₂, (SetEq.castZ p (m j) : RatFunc 𝔽) • SetEq.frac (SetEq.RLC (b j)) := by
        rw [Finset.sum_range]
        exact Finset.sum_congr rfl (fun j _ => by rw [castμ_fin])
      rw [hcast, hsum, sub_self]

/-- **`Thm:IO_result`, record-set form.**  The RLC-value image condition of `io_result` is,
    via `RLC_injective`, exactly equality of the request/response *record* sets — the content
    of `(IO_prog, IO_mem) ∈ L_IO` for unique request/response sequences (`cor_uni_req_uni_resp`),
    and of `L_mIO` membership by `lem_mio_ldse`. -/
theorem io_result_image_records {k₁ k₂ : ℕ}
    (a b : ℕ → (Fin M → 𝔽)) :
    (Finset.univ.image (fun i : Fin k₁ => SetEq.RLC (a i))
        = Finset.univ.image (fun j : Fin k₂ => SetEq.RLC (b j)))
      ↔ Finset.univ.image (fun i : Fin k₁ => a i)
          = Finset.univ.image (fun j : Fin k₂ => b j) := by
  rw [show (fun i : Fin k₁ => SetEq.RLC (a i)) = SetEq.RLC ∘ (fun i : Fin k₁ => a i) from rfl,
    show (fun j : Fin k₂ => SetEq.RLC (b j)) = SetEq.RLC ∘ (fun j : Fin k₂ => b j) from rfl,
    ← Finset.image_image, ← Finset.image_image]
  exact (Finset.image_injective SetEq.RLC_injective).eq_iff

/-- Extend a record list to `ℕ → Fin M → 𝔽` (zero past the end), so it can index the
    accumulator columns.  Agrees with `get` on the valid range (`listExt_get`). -/
noncomputable def listExt (l : List (Fin M → 𝔽)) : ℕ → (Fin M → 𝔽) :=
  fun i => if h : i < l.length then l.get ⟨i, h⟩ else 0

theorem listExt_get (l : List (Fin M → 𝔽)) (i : Fin l.length) :
    listExt l (i : ℕ) = l.get i := by
  simp only [listExt, i.isLt, dif_pos, Fin.eta]

/-- **`Thm:IO_result`, the fused paper statement over record lists.**  For a
    unique-request (`hreqnd`) / unique-response (`hrespnd`, guaranteed by
    `cor_uni_req_uni_resp` at the language level) instance with request/response record lists
    `req, resp` (lengths in `[K]`, `char > K`), the two extended RAPs `RAP_prog-IO` /
    `RAP_mem-IO` are jointly satisfiable together with the two IO consistency checks
    (`requests = responses`, `out_mem = 0`) **iff** `(req, resp) ∈ L_IO` — the a-priori
    endpoint of the reduction (`(IO_prog,IO_mem) ∈ L_mIO ⟺ ∈ L_IO`). -/
theorem io_result_LIO (K : ℕ) (hKp : K < p)
    (req resp : List (Fin M → 𝔽))
    (hKreq : InRange K req.length) (hKresp : resp.length ≤ K)
    (hreqnd : req.Nodup) (hrespnd : resp.Nodup) :
    (∃ (m : Fin resp.length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc 𝔽))
        (requests responses out_mem : RatFunc (RatFunc 𝔽)),
        (∀ j, m j ≠ 0)
        ∧ ProgIOSat (fun i => SetEq.RLC (listExt req i)) accP requests req.length
        ∧ MemIOSat (fun i => SetEq.RLC (listExt resp i)) (castμ m) accM
            responses out_mem resp.length
        ∧ requests = responses ∧ out_mem = 0)
      ↔ LIO K req resp := by
  have hk₁ : req.length < p := lt_of_le_of_lt hKreq.2 hKp
  have hk₂ : resp.length < p := lt_of_le_of_lt hKresp hKp
  have hbinj : Function.Injective (fun j : Fin resp.length => SetEq.RLC (listExt resp (j : ℕ))) := by
    have hfun : (fun j : Fin resp.length => SetEq.RLC (listExt resp (j : ℕ)))
        = fun j => SetEq.RLC (resp.get j) := by funext j; rw [listExt_get]
    rw [hfun]
    exact SetEq.RLC_injective.comp (List.nodup_iff_injective_get.mp hrespnd)
  rw [io_result hk₁ hk₂ (listExt req) (listExt resp) hbinj]
  have eR : Finset.univ.image (fun i : Fin req.length => SetEq.RLC (listExt req (i : ℕ)))
      = Finset.univ.image (fun i : Fin req.length => SetEq.RLC (req.get i)) :=
    Finset.image_congr (fun i _ => by rw [listExt_get])
  have eS : Finset.univ.image (fun j : Fin resp.length => SetEq.RLC (listExt resp (j : ℕ)))
      = Finset.univ.image (fun j : Fin resp.length => SetEq.RLC (resp.get j)) :=
    Finset.image_congr (fun j _ => by rw [listExt_get])
  rw [eR, eS, RLC_image_eq_iff]
  constructor
  · intro hfin
    have hperm := List.perm_of_nodup_nodup_toFinset_eq hreqnd hrespnd hfin
    exact ⟨⟨by rw [← hperm.length_eq]; exact hKreq.1,
      by rw [← hperm.length_eq]; exact hKreq.2⟩, hrespnd, hperm⟩
  · rintro ⟨_, _, hperm⟩
    exact List.toFinset_eq_of_perm _ _ hperm

end Field

end IO
end Nock
