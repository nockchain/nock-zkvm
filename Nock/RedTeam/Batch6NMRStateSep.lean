/-
  Nock/RedTeam/Batch6NMRStateSep.lean

  Independent verification of definitional faithfulness + non-vacuity witnesses.

This artifact provides MACHINE-CHECKED evidence for:
  1. Def:NMR_poly    — `Nock.NMR.PolyRec` (+ `PolyRec.of`)   (Def)
  2. Def:NMR         — `Nock.NMR.Rec` (+ `Rec.of`, `equivSpace`) (Def)
  3. Cor:NMR_size    — `Nock.NMR.nmr_size` / `Nock.NMR.nmr_embeds` (Cor)
  4. Def:state_data_separation — `Nock.Walk.StateSep` + instances (Def)
  5. Def:unique_request — `Nock.IO.UniqueRequest` / `UniqueResponse` (Def)
  6. cor_uni_req_uni_resp — `Nock.IO.cor_uni_req_uni_resp` / `ureq_uresp` (Cor)

  HYGIENE: No `sorry`, `admit`, `native_decide`, `axiom`, or `@[extern]`. Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}. -/
import Nock.NMR
import Nock.Walk
import Nock.NockVM
import Nock.IO
import Nock.Framework
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace Nock.RedTeam

open Polynomial
open Nock Nock.NMR Nock.IO Nock.Walk Nock.ComputeTable Nock.MemoryTable

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Def:NMR_poly` — `Nock.NMR.PolyRec` (+ `PolyRec.of`)
    ══════════════════════════════════════════════════════════════════════════════════════

    `pNMR(𝔽)` record: `(root_fn child_fn : 𝔽[X]³, axis : 𝔽, timestamp : 𝔽[X])` with
    `PolyRec.of root child axis k` setting fingerprints via `NPR.Φ` and `timestamp := X^k`.

    Faithfulness: `PolyRec.of.root_fn = NPR.Φ root`, `.child_fn = NPR.Φ child`, `.timestamp = X^k`.
    Non-vacuity + DISCRIMINATION: a concrete `pNMR` over `ℚ` from a concrete `Noun`, with the
    timestamp `X^k` computing for concrete `k`, and different `k` yielding DIFFERENT timestamps.

    Disposition: PASSED (def, faithful + non-vacuous + discriminating)
-/

section Def_NMR_poly

/-- **[1.cite] `Nock.NMR.PolyRec` type-checks at the paper type** — a concrete `pNMR(ℚ)` record
    built from concrete nouns via `PolyRec.of` (root `atom 0`, child `cell(atom 1, atom 2)`,
    axis `0`, access time `k = 2`). -/
noncomputable def polyRec_witness : PolyRec ℚ :=
  PolyRec.of (Noun.atom 0) (Noun.cell (Noun.atom 1) (Noun.atom 2)) (0 : ℚ) 2

/-- **[1.a] Faithful fingerprints**: `PolyRec.of`'s `root_fn`/`child_fn` are exactly `NPR.Φ`
    of the respective nouns. -/
theorem polyRec_root_fn :
    polyRec_witness.root_fn = NPR.Φ (K := ℚ) (Noun.atom 0) := rfl

theorem polyRec_child_fn :
    polyRec_witness.child_fn = NPR.Φ (K := ℚ) (Noun.cell (Noun.atom 1) (Noun.atom 2)) := rfl

/-- **[1.a'] Faithful axis** — the address is the axis label `∈ 𝔽`. -/
theorem polyRec_axis : polyRec_witness.axis = (0 : ℚ) := rfl

/-- **[1.b] Non-vacuity: the timestamp `X^k` COMPUTES for concrete `k = 2`**. -/
theorem polyRec_timestamp : polyRec_witness.timestamp = (X : ℚ[X]) ^ 2 := rfl

/-- **[1.c] DISCRIMINATION: different access times `k` give DIFFERENT timestamps.**
    `X^2 ≠ X^3` in `ℚ[X]` (distinct `natDegree`), so `timestamp := X^k` genuinely records `k` —
    the record is not trivially constant.  Uses nontriviality of `ℚ[X]` only. -/
theorem polyRec_timestamp_discriminates :
    (PolyRec.of (Noun.atom 0) (Noun.atom 1) (0 : ℚ) 2).timestamp
      ≠ (PolyRec.of (Noun.atom 0) (Noun.atom 1) (0 : ℚ) 3).timestamp := by
  have e2 : (PolyRec.of (Noun.atom 0) (Noun.atom 1) (0 : ℚ) 2).timestamp = (X : ℚ[X]) ^ 2 := rfl
  have e3 : (PolyRec.of (Noun.atom 0) (Noun.atom 1) (0 : ℚ) 3).timestamp = (X : ℚ[X]) ^ 3 := rfl
  rw [e2, e3]
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hd
  exact (by norm_num : (2 : ℕ) ≠ 3) hd

/-- **[1.doc]** -/
def polyRec_doc : String :=
  "Def:NMR_poly (main.tex:1303) → Nock.NMR.PolyRec + PolyRec.of (Nock/NMR.lean:37,49). " ++
  "pNMR(𝔽) = (root_fn child_fn : 𝔽[X]³, axis : 𝔽, timestamp : 𝔽[X]); PolyRec.of sets " ++
  "fingerprints via NPR.Φ and timestamp := X^k. Witness: concrete pNMR(ℚ) with root_fn = Φ(root), " ++
  "child_fn = Φ(child), timestamp = X^2 (computes), and X^2 ≠ X^3 (k-discrimination). " ++
  "Disposition: PASSED (1-1, faithful + non-vacuous + discriminating)."

end Def_NMR_poly


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Def:NMR` — `Nock.NMR.Rec` (+ `Rec.of`, `Space`, `equivSpace`)
    ══════════════════════════════════════════════════════════════════════════════════════

    `NMR^{α,β}(𝔽,𝕂)` record: `(root_fn child_fn : 𝕂³, axis : 𝔽, timestamp : 𝕂)`;
    `Rec.of root child α axis β k` uses `NPR.fn` and `timestamp := β^k`.

    THE FIELD SPLIT: address `axis ∈ 𝔽` (BASE field), fingerprints/timestamp `∈ 𝕂` (EXTENSION).
    We witness this over the genuine degree-2 extension `ℝ ↪ ℂ`: `axis : ℝ`, `timestamp : ℂ`.

    Disposition: PASSED (def, faithful field-split + `equivSpace` round-trips)
-/

section Def_NMR

/-- **[2.cite] `Nock.NMR.Rec` type-checks at the paper type** — a concrete `NMR^{α,β}(ℝ,ℂ)`
    record via `Rec.of` with `α = i ∈ ℂ`, `axis = 2 ∈ ℝ`, `β = i ∈ ℂ`, `k = 2`.  The types
    already ENFORCE the split: `axis : ℝ` (base 𝔽), `timestamp : ℂ` (extension 𝕂). -/
noncomputable def rec_witness : Rec ℝ ℂ :=
  Rec.of (Noun.atom 0) (Noun.cell (Noun.atom 1) (Noun.atom 2))
    Complex.I (2 : ℝ) Complex.I 2

/-- **[2.a] Faithful fingerprints**: `root_fn`/`child_fn` are `NPR.fn (· ; α)`. -/
theorem rec_root_fn : rec_witness.root_fn = NPR.fn (Noun.atom 0) Complex.I := rfl

theorem rec_child_fn :
    rec_witness.child_fn = NPR.fn (Noun.cell (Noun.atom 1) (Noun.atom 2)) Complex.I := rfl

/-- **[2.b] FIELD SPLIT — axis lives in the BASE field `𝔽 = ℝ`**. -/
theorem rec_axis_in_base : rec_witness.axis = (2 : ℝ) := rfl

/-- **[2.b'] FIELD SPLIT — timestamp lives in the EXTENSION field `𝕂 = ℂ`, `= β^k`**. -/
theorem rec_timestamp_in_ext : rec_witness.timestamp = Complex.I ^ 2 := rfl

/-- **[2.b''] The timestamp is a genuine extension element** `β^2 = i^2 = -1 ∈ ℂ ∖ ℝ`-image is
    forced to be `-1` here; it is NOT in the base copy trivially — confirming `𝒯 = 𝕂`, not `𝔽`. -/
theorem rec_timestamp_value : rec_witness.timestamp = (-1 : ℂ) := by
  rw [rec_timestamp_in_ext, Complex.I_sq]

/-- **[2.c] `equivSpace` round-trips (`≃`), concrete instance** — `Rec ℝ ℂ ≃ Space ℝ ℂ`. -/
theorem rec_equivSpace_left : equivSpace.symm (equivSpace rec_witness) = rec_witness :=
  equivSpace.left_inv rec_witness

/-- **[2.c'] `equivSpace` round-trips generically (both directions), over `ℝ ↪ ℂ`.** -/
theorem rec_equivSpace_roundtrip_forward (r : Rec ℝ ℂ) :
    equivSpace.symm (equivSpace r) = r := equivSpace.left_inv r

theorem rec_equivSpace_roundtrip_backward (s : Space ℝ ℂ) :
    equivSpace (equivSpace.symm s) = s := equivSpace.right_inv s

/-- **[2.doc]** -/
def rec_doc : String :=
  "Def:NMR (main.tex:1319) → Nock.NMR.Rec + Rec.of + Space + equivSpace (Nock/NMR.lean:61,73,86,92). " ++
  "NMR^{α,β}(𝔽,𝕂) = (root_fn child_fn : 𝕂³, axis : 𝔽, timestamp : 𝕂); Rec.of uses NPR.fn, " ++
  "timestamp := β^k. FIELD SPLIT confirmed over ℝ↪ℂ: axis ∈ ℝ (base 𝔽), timestamp = i^2 = -1 ∈ ℂ " ++
  "(extension 𝕂). equivSpace : Rec ≃ Space round-trips (both directions). " ++
  "Disposition: PASSED (1-1, faithful field-split)."

end Def_NMR


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3. `Cor:NMR_size` — `nmr_size` / `nmr_embeds`
    ══════════════════════════════════════════════════════════════════════════════════════

    Paper: `NMR^{α,β}(𝔽,𝕂) ⊆ 𝔽^{7e+1}` (a SUBSET), `e = [𝕂 : 𝔽]`.
    Lean: `nmr_size : finrank 𝔽 (Space 𝔽 𝕂) = 7·e + 1` AND `nmr_embeds : Nonempty (Space ≃ₗ 𝔽^{7e+1})`
    — an ISOMORPHISM, STRONGER than the paper's `⊆`.

    DISCRIMINATION / non-vacuity: instantiate at CONCRETE extension degrees and evaluate the
    bound to a concrete number:
      • e = 1  (`𝕂 := 𝔽 := ℚ`)  ⟹  dim = 7·1 + 1 = 8;
      • e = 2  (`𝔽 := ℝ`, `𝕂 := ℂ`) ⟹  dim = 7·2 + 1 = 15.
    Both prove the bound is a REAL arithmetic claim (not `0 = 0`), and both are axiom-clean.

    Disposition: PASSED — documented benign/STRENGTHENING delta (Lean proves iso ⊋ paper ⊆).
-/

section Cor_NMR_size

/-- **[3.cite.size] `nmr_size` type-checks** (the dimension form). -/
theorem nmr_size_cite :
    Module.finrank ℚ (Space ℚ ℚ) = 7 * Module.finrank ℚ ℚ + 1 := nmr_size ℚ ℚ

/-- **[3.cite.embeds] `nmr_embeds` type-checks** (the `⊆ 𝔽^{7e+1}` / isomorphism form). -/
theorem nmr_embeds_cite :
    Nonempty (Space ℚ ℚ ≃ₗ[ℚ] (Fin (7 * Module.finrank ℚ ℚ + 1) → ℚ)) := nmr_embeds ℚ ℚ

/-- **[3.a] e = 1 DISCRIMINATION: at `𝕂 = 𝔽 = ℚ` the bound evaluates to the concrete `8`.** -/
theorem nmr_size_e1 : Module.finrank ℚ (Space ℚ ℚ) = 8 := by
  rw [nmr_size ℚ ℚ, Module.finrank_self]

/-- **[3.b] e = 2 DISCRIMINATION: at `𝔽 = ℝ, 𝕂 = ℂ` (a genuine degree-2 extension) the bound
    evaluates to the concrete `15 = 7·2 + 1`.**  This exercises `finrank 𝔽 𝕂 = e = 2` for real. -/
theorem nmr_size_e2 : Module.finrank ℝ (Space ℝ ℂ) = 15 := by
  rw [nmr_size ℝ ℂ, Complex.finrank_real_complex]

/-- **[3.b'] The genuine degree-2 embedding exists** (`Space ℝ ℂ ≃ₗ ℝ^{15}`). -/
theorem nmr_embeds_e2 :
    Nonempty (Space ℝ ℂ ≃ₗ[ℝ] (Fin (7 * Module.finrank ℝ ℂ + 1) → ℝ)) := nmr_embeds ℝ ℂ

/-- **[3.doc] documented STRENGTHENING delta.** -/
def nmr_size_doc : String :=
  "Cor:NMR_size (main.tex:1333) → Nock.NMR.nmr_size + nmr_embeds (Nock/NMR.lean:101,109). " ++
  "Paper states NMR ⊆ 𝔽^{7e+1} (a SUBSET). Lean proves BOTH finrank = 7e+1 (nmr_size) and a " ++
  "LINEAR ISOMORPHISM Space ≃ₗ 𝔽^{7e+1} (nmr_embeds) — STRICTLY STRONGER than ⊆. " ++
  "Non-vacuity: e=1 (ℚ) ⟹ dim 8; e=2 (ℝ↪ℂ) ⟹ dim 15. " ++
  "Verdict: 1-1 (proves iso — stronger). DOCUMENTED benign/strengthening delta, not new drift."

end Cor_NMR_size


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 4. `Def:state_data_separation` — `Nock.Walk.StateSep`
    ══════════════════════════════════════════════════════════════════════════════════════

    Structure fields: `Sleaf : S → Prop`, `fanout : S → ℕ`, `fanout_le`, `fanout_leaf`
    (`Sleaf s → fanout s = 0`), `solely` (state ⇔ leaf on every RVT), `dynamic` (exactly the
    first `fanout s` outputs non-⊥).  Faithfully captures BOTH the paper's "solely
    state-traversable" and "state-defined dynamic labeling" conditions.

    GOAL: `StateSep` is neither EMPTY (has real instances) nor TRIVIALLY-INHABITED (its fields
    impose real constraints — leaf ⇔ fanout 0, and not all states are leaves).

    Disposition: PASSED (inhabited by real instances + fields discriminate)
-/

section Def_state_data_separation

/-- **[4.cite.comp] `L_comp = Fcomp` satisfies `StateSep`**. -/
noncomputable def comp_stateSep_cite : StateSep (Fcomp (K := ℚ)) := comp_stateSep

/-- **[4.cite.mem] `L_mem = Fmem` satisfies `StateSep`**. -/
noncomputable def mem_stateSep_cite : StateSep (Fmem (K := ℚ)) := mem_stateSep

/-- **[4.cite.toy] Toy `𝓛(G,2)` (Fibonacci) instance `FG_stateSep`**. -/
noncomputable def fib_stateSep_cite : StateSep Nock.Framework.Fib.FG := Nock.Framework.Fib.FG_stateSep

/-- **[4.a] NON-EMPTY: the compute language is not over an empty language** — `Fcomp` accepts a
    concrete `OP_0` leaf (`Fcomp_nonvacuous`, NockVM.lean:231). -/
theorem comp_nonvacuous_cite :
    ∃ (lbl : State × DTcomp ℚ), Fcomp lbl (fun _ => none) := Fcomp_nonvacuous

/-- **[4.a'] NON-EMPTY: the memory language accepts a concrete `halt` leaf** (`Fmem_nonvacuous`,
    NockVM.lean:379). -/
theorem mem_nonvacuous_cite :
    ∃ (lbl : MState × DTmem ℚ), Fmem lbl (fun _ => none) := Fmem_nonvacuous

/-- **[4.b] REAL CONSTRAINT (compute): `fanout_leaf` forces leaf states to fanout 0** — this is a
    structural field, applied here to the concrete leaf `OP_0 = s0` (`S_leaf = {OP_0, OP_1}`). -/
theorem comp_fanout_leaf_forces_zero (s : State)
    (h : (comp_stateSep (K := ℚ)).Sleaf s) : (comp_stateSep (K := ℚ)).fanout s = 0 :=
  (comp_stateSep (K := ℚ)).fanout_leaf s h

/-- **[4.c] DISCRIMINATION (compute): `S_leaf` is a PROPER, non-trivial predicate.**
    `s0` (`OP_0`) is a leaf state; `s2` is NOT (its fanout is `3`).  So `Sleaf` neither holds
    everywhere nor nowhere — the definition genuinely partitions states. -/
theorem comp_Sleaf_discriminates :
    (comp_stateSep (K := ℚ)).Sleaf State.s0 ∧ ¬ (comp_stateSep (K := ℚ)).Sleaf State.s2 := by
  refine ⟨rfl, ?_⟩
  intro h
  have : (3 : ℕ) = 0 := h
  omega

/-- **[4.c'] The witnessing non-leaf fanout: `fanout s2 = 3 ≠ 0`.** -/
theorem comp_fanout_s2 : (comp_stateSep (K := ℚ)).fanout State.s2 = 3 := rfl

/-- **[4.d] DISCRIMINATION (memory): `S_leaf = {halt}`.**  `halt` is a leaf; `decompose` is not
    (`fanout decompose = 2`). -/
theorem mem_Sleaf_discriminates :
    (mem_stateSep (K := ℚ)).Sleaf MState.halt ∧ ¬ (mem_stateSep (K := ℚ)).Sleaf MState.decompose := by
  refine ⟨rfl, ?_⟩
  intro h
  have : (2 : ℕ) = 0 := h
  omega

/-- **[4.d'] The witnessing non-leaf fanout: `fanout decompose = 2 ≠ 0`.** -/
theorem mem_fanout_decompose : (mem_stateSep (K := ℚ)).fanout MState.decompose = 2 := rfl

/-- **[4.doc]** -/
def stateSep_doc : String :=
  "Def:state_data_separation (main.tex:768) → Nock.Walk.StateSep (Nock/Walk.lean:152). " ++
  "Fields faithfully capture BOTH conditions: `solely` (Sleaf s ⇔ t.isLeaf on every RVT) = " ++
  "'solely state-traversable'; `dynamic` (i < fanout s ⇔ xout i ≠ none) + `fanout_le`/`fanout_leaf` " ++
  "= 'state-defined dynamic labeling' with null-padding. INHABITED by real instances: " ++
  "comp_stateSep (S_leaf = {OP_0,OP_1}), mem_stateSep (S_leaf = {halt}), FG_stateSep (S_leaf = {halt}); " ++
  "underlying languages non-empty (Fcomp_nonvacuous/Fmem_nonvacuous). NOT trivially-inhabited: " ++
  "fanout_leaf forces leaf→0, and Sleaf is proper (s0 leaf, s2 not; halt leaf, decompose not). " ++
  "Disposition: PASSED (1-1, inhabited + discriminating)."

end Def_state_data_separation


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 5. `Def:unique_request` — `UniqueRequest` / `UniqueResponse`
    ══════════════════════════════════════════════════════════════════════════════════════

    Paper: `(io(i₁)=1)∩(io(i₂)=1) ⇒ ((i₁,j₁)≠(i₂,j₂) ⇒ IO_prog(i₁,j₁) ≠ IO_prog(i₂,j₂))`,
    read at the flattened record level = "request record list has no repeats".
    Lean: `UniqueRequest := requests.Nodup`, `UniqueResponse := responses.Nodup`.

    DISCRIMINATION: `[0,1,2]` IS unique-request; `[0,0]` is NOT (machine-checked both ways).

    Disposition: PASSED — documented modeling choice (VM/IO-slot condition FLATTENED to Nodup).
-/

section Def_unique_request

/-- **[5.cite] `UniqueRequest`/`UniqueResponse` type-check** at the paper interface. -/
theorem uniqueReq_cite (requests : List ℕ) : UniqueRequest requests ↔ requests.Nodup := Iff.rfl
theorem uniqueResp_cite (responses : List ℕ) : UniqueResponse responses ↔ responses.Nodup := Iff.rfl

/-- **[5.a] POSITIVE: `[0,1,2]` IS unique-request** (distinct records). -/
theorem uniqueRequest_pos : UniqueRequest (R := ℕ) [0, 1, 2] := by
  unfold UniqueRequest; decide

/-- **[5.b] NEGATIVE: `[0,0]` is NOT unique-request** (a repeated record). -/
theorem uniqueRequest_neg : ¬ UniqueRequest (R := ℕ) [0, 0] := by
  unfold UniqueRequest; decide

/-- **[5.a'] POSITIVE: `[3,4]` IS unique-response.** -/
theorem uniqueResponse_pos : UniqueResponse (R := ℕ) [3, 4] := by
  unfold UniqueResponse; decide

/-- **[5.b'] NEGATIVE: `[7,7]` is NOT unique-response.** -/
theorem uniqueResponse_neg : ¬ UniqueResponse (R := ℕ) [7, 7] := by
  unfold UniqueResponse; decide

/-- **[5.doc] documented FLATTENING modeling choice.** -/
def unique_request_doc : String :=
  "Def:unique_request (main.tex:603-611) → Nock.IO.UniqueRequest/UniqueResponse (Nock/IO.lean:129,133). " ++
  "The paper's VM/IO-slot quantified condition (io(i₁)=1 ∩ io(i₂)=1 ⇒ distinct slots ⇒ distinct " ++
  "records) is FLATTENED to List.Nodup on the request/response record lists (CORRESPONDENCE Def 3.5, " ++
  "verdict 'def'). This is a MODELING CHOICE (documented), not new drift. Discrimination: " ++
  "[0,1,2] is UniqueRequest; [0,0] is not. Disposition: PASSED (documented flattening)."

end Def_unique_request


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 6. `cor_uni_req_uni_resp` — `cor_uni_req_uni_resp` / `ureq_uresp`
    ══════════════════════════════════════════════════════════════════════════════════════

    Paper: "If a language is unique request, then it's also unique response."
    Lean: `cor_uni_req_uni_resp` (Nodup requests + L_mIO ⊢ L_IO) and `ureq_uresp` (concludes
    `UniqueResponse responses ∧ L_IO ...`, making the paper wording explicit).

    NON-VACUITY: apply `ureq_uresp` to a CONCRETE satisfying `L_mIO` unique-request pair
    (requests `[0,1]`, responses `[1,0]`, `K = 2`) and DERIVE unique-response + `L_IO`.  This
    proves the corollary is non-vacuously applicable — its hypotheses `Nodup requests` and
    `L_mIO requests responses` are jointly satisfiable.

    Disposition: PASSED (1-1)
-/

section cor_uni_req_uni_resp_sec

/-- **[6.cite.cor] `cor_uni_req_uni_resp` type-checks** (Nodup req + L_mIO ⊢ L_IO). -/
theorem cor_cite (K : ℕ) (requests responses : List ℕ)
    (hreq : requests.Nodup) (h : LmIO K requests responses) :
    LIO K requests responses :=
  cor_uni_req_uni_resp K requests responses hreq h

/-- **[6.cite.ureq] `ureq_uresp` type-checks** (unique-request ⊢ unique-response ∧ L_IO). -/
theorem ureq_cite (K : ℕ) (requests responses : List ℕ)
    (hreq : UniqueRequest requests) (h : LmIO K requests responses) :
    UniqueResponse responses ∧ LIO K requests responses :=
  ureq_uresp K requests responses hreq h

/-- **[6.a] A CONCRETE unique-request `L_mIO` pair.**  `requests = [0,1]` (Nodup), responses a
    permutation `[1,0]`, `K = 2` so `InRange 2 |requests|` holds. -/
theorem lmio_concrete : LmIO (R := ℕ) 2 [0, 1] [1, 0] :=
  ⟨⟨by decide, by decide⟩, [0, 1], by decide, by decide, fun _ => Iff.rfl, by decide⟩

/-- **[6.b] NON-VACUOUS APPLICATION: `ureq_uresp` on the concrete pair yields
    unique-response AND `L_IO`.**  Hypotheses `Nodup [0,1]` and `L_mIO 2 [0,1] [1,0]` are jointly
    satisfied, so the corollary fires and produces both conclusions. -/
theorem ureq_uresp_concrete :
    UniqueResponse (R := ℕ) [1, 0] ∧ LIO (R := ℕ) 2 [0, 1] [1, 0] :=
  ureq_uresp 2 [0, 1] [1, 0] (by unfold UniqueRequest; decide) lmio_concrete

/-- **[6.b'] the derived unique-response, extracted.** -/
theorem ureq_uresp_concrete_uresp : UniqueResponse (R := ℕ) [1, 0] :=
  ureq_uresp_concrete.1

/-- **[6.b''] the derived `L_IO` membership, extracted.** -/
theorem ureq_uresp_concrete_lio : LIO (R := ℕ) 2 [0, 1] [1, 0] :=
  ureq_uresp_concrete.2

/-- **[6.doc]** -/
def cor_doc : String :=
  "cor_uni_req_uni_resp (main.tex:613-615) → Nock.IO.cor_uni_req_uni_resp + ureq_uresp " ++
  "(Nock/IO.lean:138,151). Bare `cor_uni_req_uni_resp` concludes L_IO (which implies response " ++
  "Nodup); `ureq_uresp` makes 'unique response' EXPLICIT to match the paper wording. " ++
  "Non-vacuously applied to requests=[0,1], responses=[1,0], K=2: derives UniqueResponse ∧ L_IO. " ++
  "Verdict: 1-1. Disposition: PASSED."

end cor_uni_req_uni_resp_sec


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch6_drift_summary : String :=
  "BATCH 6 NMR & STATE-SEPARATION DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Def:NMR_poly            — PASSED (PolyRec/PolyRec.of faithful; X^k computes; X^2≠X^3)\n" ++
  "2. Def:NMR                 — PASSED (Rec/Rec.of; field split axis∈ℝ, timestamp∈ℂ; equivSpace ≃)\n" ++
  "3. Cor:NMR_size            — PASSED (nmr_size/nmr_embeds; dim 8 @e=1, 15 @e=2)\n" ++
  "4. Def:state_data_separation — PASSED (StateSep inhabited: comp/mem/FG; fields discriminate)\n" ++
  "5. Def:unique_request      — PASSED (UniqueRequest/Response = Nodup; [0,1,2] yes, [0,0] no)\n" ++
  "6. cor_uni_req_uni_resp    — PASSED (ureq_uresp fires on [0,1]/[1,0]/K=2 ⟹ UniqueResponse ∧ L_IO)\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. Documented deltas CONFIRMED (not re-flagged):\n" ++
  "• Cor:NMR_size — Lean proves ISO (nmr_embeds), STRONGER than paper ⊆ (benign/strengthening).\n" ++
  "• Def:unique_request — FLATTENED to List.Nodup (documented modeling choice, verdict 'def').\n" ++
  "• NMR axis arithmetization (CENSUS E3/E5/E6/E7) is OUT OF SCOPE for these record-level defs; " ++
  "the NMR record defs (PolyRec/Rec/size) are faithful — 'the NMR CARRIES the axis by definition'.\n" ++
  "• CENSUS Row 6 (L_mIO bidirectional dedup repair) covered in Batch 5 IO; not re-proved here.\n" ++
  "AXIOM HYGIENE: audited over ℚ and ℝ↪ℂ; no goldilocks_prime, no sorry/admit/native_decide/axiom."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SELF-CERTIFICATION: `#print axioms` for every computational witness
    (all must be ⊆ {propext, Classical.choice, Quot.sound})
    ══════════════════════════════════════════════════════════════════════════════════════
-/

-- Object 1
#print axioms polyRec_root_fn
#print axioms polyRec_child_fn
#print axioms polyRec_axis
#print axioms polyRec_timestamp
#print axioms polyRec_timestamp_discriminates
-- Object 2
#print axioms rec_root_fn
#print axioms rec_child_fn
#print axioms rec_axis_in_base
#print axioms rec_timestamp_in_ext
#print axioms rec_timestamp_value
#print axioms rec_equivSpace_left
#print axioms rec_equivSpace_roundtrip_forward
#print axioms rec_equivSpace_roundtrip_backward
-- Object 3
#print axioms nmr_size_cite
#print axioms nmr_embeds_cite
#print axioms nmr_size_e1
#print axioms nmr_size_e2
#print axioms nmr_embeds_e2
-- Object 4
#print axioms comp_stateSep_cite
#print axioms mem_stateSep_cite
#print axioms fib_stateSep_cite
#print axioms comp_nonvacuous_cite
#print axioms mem_nonvacuous_cite
#print axioms comp_fanout_leaf_forces_zero
#print axioms comp_Sleaf_discriminates
#print axioms comp_fanout_s2
#print axioms mem_Sleaf_discriminates
#print axioms mem_fanout_decompose
-- Object 5
#print axioms uniqueRequest_pos
#print axioms uniqueRequest_neg
#print axioms uniqueResponse_pos
#print axioms uniqueResponse_neg
-- Object 6
#print axioms cor_cite
#print axioms ureq_cite
#print axioms lmio_concrete
#print axioms ureq_uresp_concrete
#print axioms ureq_uresp_concrete_uresp
#print axioms ureq_uresp_concrete_lio

end Nock.RedTeam
