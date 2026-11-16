/-
  Nock/RedTeam/Batch10Capstones.lean

  Independent verification of definitional faithfulness + non-vacuity/discrimination witnesses,
  and CONFIRMATION (not re-flagging) of the documented "carries"/scoping deltas of the §5 capstone.

This artifact provides MACHINE-CHECKED evidence for:
  1. Thm:Noun_Validation  — `Nock.Noun_Validation`                          (Thm) 1-1
  2.
  3. Thm:NockVMROM        — `Nock.NockVM.V_NockVMROM` + `_forest`           (Thm) ⚠ CARRIES (b)(c)(d)

  HYGIENE: No `sorry`, `admit`, `native_decide`, `stop`, `axiom`, or `@[extern]`.
  Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}.  Non-vacuity is audited over the
  AXIOM-CLEAN finite prime field `ZMod 7` (`Fact (Nat.Prime 7)` via `norm_num`), over `ℕ` record
  lists, and over `Noun`/`Bool` — so NOT EVEN the whitelisted `Nock.Field.goldilocks_prime` is
  needed anywhere in this batch.  (`Classical.choice` appears only via the classical
  `DecidableEq (MemRec K)` baked into `reqRecs` — whitelisted.)
-/
import Nock.NounValidation
import Nock.IO
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.Walk
import Nock.NockVM
import Mathlib.Tactic.NormNum.Prime

open scoped Classical

namespace Nock.RedTeam

open Nock Nock.Walk Nock.NockVM Nock.ComputeTable Nock.MemoryTable

/-- Axiom-clean primality fact for the small finite prime field used as concrete witness. -/
instance fact_prime_7_b10 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Thm:Noun_Validation` — `Nock.Noun_Validation`
    ══════════════════════════════════════════════════════════════════════════════════════

    `theorem Noun_Validation (n : Noun) (lam : ℕ) :
        n.leaves = lam ↔ ∃ T : Transcript, checkValidNoun n T = Result.accept ∧ T.length = 2*lam-1`

    A GENUINE biconditional (NOT `:= True`).  CORRESPONDENCE verdict: 1-1 (faithful, no delta).

    NON-VACUITY: two concrete nouns — an atom (`atom 0`, λ=1) and a small cell `⟦0 1⟧`
    (`cell (atom 0) (atom 1)`, λ=2) — for which BOTH directions fire: we compute `n.leaves`,
    exhibit the accepting transcript `transcript n`, and check its length `= 2λ−1`.

    DISCRIMINATION: for the cell (λ=2) there is NO accepting transcript of the WRONG length
    `2·1−1 = 1` (the biconditional forces `n.leaves = 1`, contradicting `leaves = 2`); and the
    empty transcript does NOT accept (`{n} ≠ ∅`).

    The `1 ≤ leaves` guard (`Noun.one_le_leaves`) makes the `2λ−1` truncated subtraction sound:
    `n.size + 1 = 2·n.leaves` (`Noun.size_add_one`), so `size = 2·leaves − 1 ≥ 1`.

    Disposition: PASSED (verdict 1-1; both directions fire on two concrete nouns; discrimination
    on wrong length + non-accepting transcript).
-/

section Thm_Noun_Validation

/-- **[1.cite] `Noun_Validation`** — the genuine biconditional. -/
theorem noun_validation_cite (n : Noun) (lam : ℕ) :
    n.leaves = lam ↔
      ∃ T : Transcript, checkValidNoun n T = Result.accept ∧ T.length = 2 * lam - 1 :=
  Noun_Validation n lam

/-- The two concrete nouns: an atom (λ=1) and the small cell `⟦0 1⟧` (λ=2). -/
def b10_atom : Noun := Noun.atom 0
def b10_cell : Noun := Noun.cell (Noun.atom 0) (Noun.atom 1)

/-- **[1.a] Leaf counts compute** (`atom` ↦ 1, `⟦0 1⟧` ↦ 2). -/
theorem b10_atom_leaves : b10_atom.leaves = 1 := rfl
theorem b10_cell_leaves : b10_cell.leaves = 2 := rfl

/-- **[1.b] The canonical transcript ACCEPTS on the atom, with length `2·1−1 = 1`.** -/
theorem b10_atom_accept : checkValidNoun b10_atom (transcript b10_atom) = Result.accept := by
  rw [checkValidNoun_accept_iff]; exact run_transcript_accept b10_atom

theorem b10_atom_len : (transcript b10_atom).length = 2 * 1 - 1 := by
  rw [transcript_length]; rfl

/-- **[1.b'] The canonical transcript ACCEPTS on the cell `⟦0 1⟧`, with length `2·2−1 = 3`.** -/
theorem b10_cell_accept : checkValidNoun b10_cell (transcript b10_cell) = Result.accept := by
  rw [checkValidNoun_accept_iff]; exact run_transcript_accept b10_cell

theorem b10_cell_len : (transcript b10_cell).length = 2 * 2 - 1 := by
  rw [transcript_length]; rfl

/-- **[1.c] BOTH DIRECTIONS fire (atom).**  `⟹`: from `leaves = 1` obtain an accepting transcript
    of length `2·1−1`.  `⟸`: from the canonical accepting transcript (length `2·1−1`) recover
    `leaves = 1`. -/
theorem b10_atom_forward :
    ∃ T : Transcript, checkValidNoun b10_atom T = Result.accept ∧ T.length = 2 * 1 - 1 :=
  (Noun_Validation b10_atom 1).mp b10_atom_leaves

theorem b10_atom_backward : b10_atom.leaves = 1 :=
  (Noun_Validation b10_atom 1).mpr ⟨transcript b10_atom, b10_atom_accept, b10_atom_len⟩

/-- **[1.c'] BOTH DIRECTIONS fire (cell `⟦0 1⟧`).** -/
theorem b10_cell_forward :
    ∃ T : Transcript, checkValidNoun b10_cell T = Result.accept ∧ T.length = 2 * 2 - 1 :=
  (Noun_Validation b10_cell 2).mp b10_cell_leaves

theorem b10_cell_backward : b10_cell.leaves = 2 :=
  (Noun_Validation b10_cell 2).mpr ⟨transcript b10_cell, b10_cell_accept, b10_cell_len⟩

/-- **[1.d] DISCRIMINATION (wrong length): the cell `⟦0 1⟧` (λ=2) has NO accepting transcript of
    length `2·1−1 = 1`** — the biconditional would force `leaves = 1`, contradicting `leaves = 2`. -/
theorem b10_cell_wrong_lam :
    ¬ ∃ T : Transcript, checkValidNoun b10_cell T = Result.accept ∧ T.length = 2 * 1 - 1 := by
  intro h
  have hl : b10_cell.leaves = 1 := (Noun_Validation b10_cell 1).mpr h
  rw [b10_cell_leaves] at hl
  exact absurd hl (by decide)

/-- **[1.d'] DISCRIMINATION (non-accepting transcript): the EMPTY transcript does NOT accept** on
    the atom — the multiset `{atom 0}` never reaches `∅`. -/
theorem b10_empty_not_accept : checkValidNoun b10_atom [] ≠ Result.accept := by
  intro hacc
  rw [checkValidNoun_accept_iff] at hacc
  simp only [runMset] at hacc
  simp at hacc

/-- **[1.e] The `1 ≤ leaves` guard makes `2λ−1` sound**: `Noun.one_le_leaves` +
    `Noun.size_add_one` (`size + 1 = 2·leaves`), so `size = 2·leaves − 1 ≥ 1`. -/
theorem b10_one_le_leaves (n : Noun) : 1 ≤ n.leaves := n.one_le_leaves
theorem b10_size_add_one (n : Noun) : n.size + 1 = 2 * n.leaves := n.size_add_one

/-- **[1.doc]** -/
def noun_validation_doc : String :=
  "Thm:Noun_Validation (main.tex:1268) → Nock.Noun_Validation (NounValidation.lean:255). " ++
  "GENUINE biconditional n.leaves = lam ↔ ∃ T, checkValidNoun n T = accept ∧ |T| = 2*lam-1. " ++
  "NON-VACUITY on TWO nouns: atom 0 (λ=1, |transcript|=1=2·1-1) and cell ⟦0 1⟧ (λ=2, " ++
  "|transcript|=3=2·2-1); BOTH directions fire (b10_atom_forward/_backward, b10_cell_forward/" ++
  "_backward) via transcript/run_transcript_accept/checkValidNoun_accept_iff/transcript_length. " ++
  "DISCRIMINATION: cell has NO accepting transcript of length 2·1-1 (b10_cell_wrong_lam); empty " ++
  "transcript rejects (b10_empty_not_accept). GUARD: 1 ≤ leaves (Noun.one_le_leaves) + size+1 = " ++
  "2·leaves (Noun.size_add_one) make the 2λ-1 truncated subtraction sound. Verdict: 1-1. " ++
  "Disposition: PASSED."

end Thm_Noun_Validation


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Thm:IO_result` — `Nock.IO.io_result` + `Nock.IO.io_result_LIO`
    ══════════════════════════════════════════════════════════════════════════════════════

    Two GENUINE biconditionals (NOT `:= True`):
    • `io_result`: joint `RAP_prog-IO` + `RAP_mem-IO` satisfiability (with `requests = responses`,
      `out_mem = 0`) ↔ the two RLC record-image sets are equal.
    • `io_result_LIO`: same LHS over record LISTS `req/resp` ↔ `IO.LIO K req resp`
      (= `InRange K resp.length ∧ resp.Nodup ∧ req.Perm resp`).

    CORRESPONDENCE verdict: 1-1 (costs = no-Lean) — the biconditional is fully proved; only the
    paper's efficiency/cost figures are not mechanized.

    NON-VACUITY of the ENDPOINT language `IO.LIO` (over `ℕ` records): a single-record pair and a
    genuine permutation ARE in `LIO`; a length-mismatch pair and a `Nodup`-violating pair are NOT.

    Witness
    `req=[x,x], resp=[x,y]`: the repaired `LmIO` correctly REJECTS it (toFinset `{x} ≠ {x,y}`),
    while `req=[x,x], resp=[x]` (dedup) is correctly ACCEPTED.

    Disposition: PASSED.
-/

section Thm_IO_result

/-- **[2.cite.a] `io_result`** — the RLC-image-set biconditional. -/
noncomputable def io_result_cite := @Nock.IO.io_result

/-- **[2.cite.b] `io_result_LIO`** — the record-list `↔ IO.LIO` biconditional. -/
noncomputable def io_result_LIO_cite := @Nock.IO.io_result_LIO

/-- **[2.a] NON-VACUITY (`LIO`, single record): `LIO 1 [7] [7]` holds.** -/
theorem b10_LIO_single : IO.LIO 1 ([7] : List ℕ) [7] :=
  ⟨⟨le_refl _, le_refl _⟩, List.nodup_singleton _, List.Perm.refl _⟩

/-- **[2.a'] NON-VACUITY (`LIO`, genuine permutation): `LIO 2 [1,2] [2,1]` holds.** -/
theorem b10_LIO_perm : IO.LIO 2 ([1, 2] : List ℕ) [2, 1] :=
  ⟨⟨by norm_num, by norm_num⟩, by decide, by decide⟩

/-- **[2.b] DISCRIMINATION (length mismatch): `[1]` is NOT `LIO`-matched to `[1,2]`** — no
    permutation can change length. -/
theorem b10_not_LIO_len : ¬ IO.LIO 2 ([1] : List ℕ) [1, 2] := by
  rintro ⟨_, _, hperm⟩
  have := hperm.length_eq
  simp at this

/-- **[2.b'] DISCRIMINATION (`Nodup` violation): a response with a duplicate is NOT `LIO`.** -/
theorem b10_not_LIO_dup : ¬ IO.LIO 2 ([1, 1] : List ℕ) [1, 1] := by
  rintro ⟨_, hnd, _⟩
  simp at hnd


theorem b10_census6_not_LmIO : ¬ IO.LmIO 2 ([1, 1] : List ℕ) [1, 2] := by
  rw [IO.LmIO_iff]
  rintro ⟨_, _, _, hfin⟩
  exact absurd hfin (by decide)

/-- **[2.c'] …and the repaired `LmIO` ACCEPTS the dedup `req=[x,x], resp=[x]`** — multiplicities on
    the request side are collapsed to the distinct response set. -/
theorem b10_LmIO_multiset : IO.LmIO 2 ([1, 1] : List ℕ) [1] := by
  rw [IO.LmIO_iff]
  exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, by decide, by decide⟩

/-- **[2.doc]** -/
def io_result_doc : String :=
  "Thm:IO_result (main.tex:617) → Nock.IO.io_result (IO.lean:721) + Nock.IO.io_result_LIO " ++
  "(IO.lean:806). Two GENUINE biconditionals: joint RAP_prog-IO + RAP_mem-IO satisfiability " ++
  "(requests=responses, out_mem=0) ↔ RLC record-image sets equal (io_result); same over record " ++
  "lists ↔ IO.LIO K req resp = (InRange K resp.length ∧ resp.Nodup ∧ req.Perm resp) " ++
  "(io_result_LIO). NON-VACUITY of endpoint LIO (over ℕ): [7]/[7] and perm [1,2]/[2,1] IN " ++
  "(b10_LIO_single/_perm); length-mismatch [1]/[1,2] and Nodup-violating [1,1]/[1,1] NOT " ++
  "(b10_not_LIO_len/_dup). ⚠ CENSUS #6 (LOW) CONFIRMED: LmIO uses BIDIRECTIONAL membership " ++
  "(req.toFinset = resp.toFinset) — faithful REPAIR of the paper's one-directional cond-3 " ++
  "(main.tex:198, makes lem_mio_ldse FALSE). Witness [1,1]/[1,2] REJECTED (b10_census6_not_LmIO: " ++
  "{1}≠{1,2}), dedup [1,1]/[1] ACCEPTED (b10_LmIO_multiset). Side-conditions hreqnd/hrespnd/" ++
  "InRange legitimately ASSUMED (from cor_uni_req_uni_resp). Verdict: 1-1 (costs=no-Lean). " ++
  "Disposition: PASSED."

end Thm_IO_result


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3. `Thm:NockVMROM` — `Nock.NockVM.V_NockVMROM` + `_forest`  ⚠ CARRIES
    ══════════════════════════════════════════════════════════════════════════════════════

    THE FINAL CAPSTONE (synthetic identity).  `V_NockVMROM` is the witness-SHARED 2-chip
    integration proving a CONJUNCTION of 3 conjuncts:
      (1) compute-chip walk soundness bound `≤ hc/|K| + ε_RLC`;
      (2) memory-chip walk soundness bound `≤ hm/|K| + ε_RLC`;
      (3) an IO biconditional `(∃ … jointly RAP-satisfiable …) ↔ IO.LIO Ksz (reqRecs …) (respRecs …)`
          — fed the SHARED derived record lists `reqRecs`/`respRecs` (functions of the SAME walk
          data `lblc`/`lblm`), NOT fresh req/resp.

    CORRESPONDENCE verdict: **"carries"** — the delicate one.  DOCUMENTED, CONFIRMED status:
    • (a) The 3 conjuncts ARE proved at RAP-satisfiability level; conjunct (3) is a GENUINE
      biconditional over a genuinely witness-SHARED multiset (via `equiv_compute_sound`/
      `equiv_mem_sound`).  We do NOT prove `reqRecs = respRecs` as sets — that is exactly what the
      IO biconditional CERTIFIES (matching `cor_uni_req_uni_resp`).
    • (b) The compute↔memory coupling is **IO-MULTISET only** — it DROPS the `Def:MES` SEED-PIN
      (memory root = public `(subject,formula)`).  Documented deferred item; NOT a
      closed proof that NockVM is MES.
    • (c) Memory-chip scope: `V_NockVMROM` uses the SINGLE-ROOT walk (`kroots = 1`); the
      multi-root subject-mutating case is `V_NockVMROM_forest` (`Corr:forest`).
    • (d) The honest `+ ε_RLC` term is retained; `BFSValid`/tiling DERIVED from a
      `QGate`; cost figures are carried `def`s.
    • Note: "one-hot of size 10" = the 10 numeric opcodes OP_0..OP_9; `cons` (=op_11) is
      a SEPARATE selector — NOT a discrepancy.

    Disposition: STRUCTURE/conjuncts PASSED (real 3-conjunct ↔, witness-shared); (b) seed-pin,
    (c) single-root-vs-forest, (d) carried costs — all DOCUMENTED-carried, honestly stated here.
    We do NOT claim NockVM is MES, do NOT claim the seed-pin is discharged, do NOT claim the
    forest/batched-axis is closed.
-/

section Thm_NockVMROM

/-- **[3.cite.a] `V_NockVMROM`** — the real 3-conjunct witness-shared capstone.
    Naming the constant exhibits its FULL type (soundness ∧ soundness ∧ IO-↔), NOT `:= True`. -/
noncomputable def V_NockVMROM_cite := @Nock.NockVM.V_NockVMROM

/-- **[3.cite.b] `V_NockVMROM_forest`** — the multi-root `Corr:forest` capstone. -/
noncomputable def V_NockVMROM_forest_cite := @Nock.NockVM.V_NockVMROM_forest

/-! ### (A) `reqRecs`/`respRecs` are HONEST functions of the walk data (witness-sharing is real) -/

/-- A concrete compute-row request record (`root.size = 1 ≠ 0`, so genuinely non-`zero`). -/
def b10_reqRec : ComputeTable.MemRec (ZMod 7) := ⟨⟨1, 0, 0⟩, 0, 0, 0⟩

/-- A concrete memory-row served record `⟨root=(2,0,3), child=(1,0,0), axis=4, ts=5⟩`. -/
def b10_memRec : ComputeTable.MemRec (ZMod 7) := ⟨⟨2, 0, 3⟩, ⟨1, 0, 0⟩, 4, 5⟩

/-- A concrete one-request compute public row carrying `mr1 = b10_reqRec`,
    `mr2 = mr3 = zero` as inactive padding. -/
def b10_pubC : ComputeTable.Pub (ZMod 7) where
  state := .s1
  s := 0; f := 0; e := 0
  sf1_s := 0; sf1_f := 0; sf1_e := 0
  sf2_s := 0; sf2_f := 0; sf2_e := 0
  sf3_s := 0; sf3_f := 0; sf3_e := 0
  ln_prev := 0; ln := 0
  mr1 := b10_reqRec
  mr2 := ComputeTable.MemRec.zero
  mr3 := ComputeTable.MemRec.zero

def b10_inputsC : ComputeTable.Inputs (ZMod 7) := ⟨1, 1, 0, 0, 0⟩
def b10_dec : ComputeTable.Dec (ZMod 7) := ⟨0, 0, 0, 0, 0, 0⟩

/-- A constant compute walk-label carrying the row `b10_pubC`. -/
def b10_lblc : ℕ → State × DTcomp (ZMod 7) := fun _ => (State.s0, b10_inputsC, b10_pubC, b10_dec)

/-- A concrete memory public row in state `read_root` serving `b10_memRec`. -/
def b10_pubM : MemoryTable.Pub (ZMod 7) where
  st := .read_root
  pt := MemoryTable.Cell.zero
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := b10_memRec
  ipre := 0; icur := 0

/-- A concrete memory public row in state `halt` (serves NOTHING to the external IO column). -/
def b10_pubM_halt : MemoryTable.Pub (ZMod 7) where
  st := .halt
  pt := MemoryTable.Cell.zero
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := b10_memRec
  ipre := 0; icur := 0

def b10_inputsM : MemoryTable.Inputs (ZMod 7) := ⟨1, 0, 2⟩

/-- A constant memory walk-label in `read_root` (serves one record per row). -/
def b10_lblm : ℕ → MState × DTmem (ZMod 7) := fun _ => (MState.read_root, b10_inputsM, b10_pubM)

/-- A constant memory walk-label in `halt` (serves nothing). -/
def b10_lblm_halt : ℕ → MState × DTmem (ZMod 7) :=
  fun _ => (MState.halt, b10_inputsM, b10_pubM_halt)

/-- **[3.A.1] `respRecs` is an HONEST function of the walk data: one served record per `read_root`
    row.**  Over one row it yields exactly `[encRec b10_memRec]` — the row's OWN committed
    `mem_record`, so conjunct (3)'s multiset is the memory walk's own traffic (not cosmetic). -/
theorem b10_respRecs_row : respRecs b10_lblm 1 = [encRecC b10_memRec 1] := rfl

/-- **[3.A.1'] The served vector is the record's 9 field coordinates** (`RLC^γ`'s components
    plus form R `C'`) — a concrete NON-TRIVIAL list value. -/
theorem b10_respRecs_value :
    respRecs b10_lblm 1 = [![2, 0, 3, 1, 0, 0, 4, 5, 1]] := by rw [b10_respRecs_row]; rfl

/-- **[3.A.2] DISCRIMINATION: a non-`read_root` (`halt`) row serves NOTHING** — `respRecs` really
    reads the row's state, so it is a genuine function of the walk (not a constant). -/
theorem b10_respRecs_halt : respRecs b10_lblm_halt 1 = [] := rfl

/-- **[3.A.3] `reqRecs` is an HONEST function of the walk data: the row's opcode-active memory
    records.**  Over one one-request row carrying `mr1 = b10_reqRec` (and `mr2 = mr3 = zero` as
    inactive padding) it yields exactly `[encRec b10_reqRec]` — the compute walk's OWN emitted
    request. -/
theorem b10_reqRecs_row :
    reqRecs b10_lblc 1 MemoryTable.formRDefault = [encRecFormR b10_reqRec MemoryTable.formRDefault] := rfl

/-- **[3.A.4] DISCRIMINATION: no rows ⇒ no requests / no responses** — `reqRecs`/`respRecs` really
    depend on the walk length `hc`/`hm` (empty at `0`). -/
theorem b10_reqRecs_zero : reqRecs b10_lblc 0 MemoryTable.formRDefault = [] := rfl
theorem b10_respRecs_zero : respRecs b10_lblm 0 = [] := rfl

/-! ### (b) The `Def:MES` SEED-PIN is DROPPED — coupling is IO-MULTISET only -/

/-- **[3.b.1] Conjunct (3)'s content is a MULTISET (`Perm`) coupling** — `IO.LIO` gives only
    `req.Perm resp`, i.e. request/response multisets coincide. -/
theorem b10_LIO_is_multiset_perm {R : Type*} [DecidableEq R] (K : ℕ) (req resp : List R)
    (h : IO.LIO K req resp) : req.Perm resp := h.2.2

/-- **[3.b.2] Multiset equality is STRICTLY WEAKER than a forward, per-record identity** — a
    genuine permutation `[0,1]/[1,0]` has equal multisets but is NOT equal as an ordered list.
    So the seed pin (memory root = the SPECIFIC compute request) is genuinely MORE
    than what conjunct (3) delivers — it is DROPPED by the base capstone. -/
theorem b10_perm_weaker_than_eq :
    ([0, 1] : List ℕ).Perm [1, 0] ∧ ([0, 1] : List ℕ) ≠ [1, 0] :=
  ⟨by decide, by decide⟩

/-- **[3.b.3] The seed coupling is DELIVERED ONLY WITH extra data** (`seedCoupled_of_LIO`): it
    requires BOTH the IO endpoint `hLIO : IO.LIO …` AND the compute chip's closed-form request
    timestamps `hReqTs` — it is NOT free from the base 3-conjunct capstone.
    We PROVE the delivery to pin exactly what is carried (cf. CORRESPONDENCE §"Theorem 5.4"). -/
theorem b10_seedPin_needs_LIO_and_ts
    (lblc : ℕ → State × DTcomp (ZMod 7)) (hc : ℕ)
    (lblm : ℕ → MState × DTmem (ZMod 7)) (hm : ℕ) (lmb z : ZMod 7) {Ksz : ℕ}
    (hReqTs : ∀ v ∈ reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = z ^ e)
    (hLIO : IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm)) :
    SeedCoupled lmb lblc hc lblm hm z :=
  seedCoupled_of_LIO lblc hc lblm hm z hReqTs hLIO

/-- **[3.b.cite] The seed-coupling machinery** (`SeedCoupled`, `seedCoupled_of_LIO`,
    `V_NockVMROM_seedcoupled`) — cited to show it is a SEPARATE, gated object, not part of the
    base `V_NockVMROM` conjunction. -/
noncomputable def SeedCoupled_cite := @Nock.NockVM.SeedCoupled
noncomputable def seedCoupled_of_LIO_cite := @Nock.NockVM.seedCoupled_of_LIO
noncomputable def V_NockVMROM_seedcoupled_cite := @Nock.NockVM.V_NockVMROM_seedcoupled

/-! ### (c) SINGLE-ROOT (`V_NockVMROM`) vs FOREST (`V_NockVMROM_forest`) scope -/

/-- **[3.c.1] The single-root case IS the `kroots = 1` case of the forest goal**:
    `ForestReconGoal … 1 h ↔ ReconGoal … h`.  So `V_NockVMROM` (single-root) covers exactly the
    one-root memory table; the multi-root (`kroots ≥ 2`) subject-mutating case is covered ONLY by
    `V_NockVMROM_forest` — the two are proved independently (scope delta, documented, not a bug). -/
theorem b10_forestReconGoal_one
    {n : ℕ} {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : Walk.StateSep F) (lbl : ℕ → S × DT) (h : ℕ) :
    Walk.ForestReconGoal St lbl 1 h ↔ Walk.ReconGoal St lbl h :=
  Walk.ForestReconGoal_one St lbl h

/-! ### (d) The "one-hot of size 10" NON-DISCREPANCY: 10 numeric opcodes vs cons=op_11 -/

/-- **[3.d.1] `opcode_onehot_size = 10`** and **`mem_record_arity = 3`** — the documented
    structural constants. -/
theorem b10_opcode_onehot_size : opcode_onehot_size = 10 := rfl
theorem b10_mem_record_arity : mem_record_arity = 3 := rfl

/-- **[3.d.2] The one-hot of size 10 counts the 10 NUMERIC opcodes `OP_0..OP_9`** (`State.toNat`
    maps `s0..s9 ↦ 0..9`). -/
theorem b10_numeric_opcodes :
    (ComputeTable.State.s0.toNat, ComputeTable.State.s9.toNat) = (0, 9) := rfl

/-- **[3.d.3] `cons` (=op_11) is a SEPARATE, distinct selector** — NOT one of the 10 numeric
    opcodes.  So "one-hot size 10 vs 11 `State` constructors" is NOT a discrepancy. -/
theorem b10_cons_separate : ComputeTable.State.cons ≠ ComputeTable.State.s0 := by decide

/-- **[3.doc]** -/
def nockvmrom_doc : String :=
  "Thm:NockVMROM (main.tex:1450) → Nock.NockVM.V_NockVMROM (NockVM.lean:815) + V_NockVMROM_forest " ++
  "(NockVM.lean:996). Witness-SHARED 2-chip capstone: 3-conjunct ∧ [(1) compute soundness ≤ " ++
  "hc/|K|+ε_RLC, (2) memory soundness ≤ hm/|K|+ε_RLC, (3) IO ↔ over the SHARED reqRecs/respRecs] " ++
  "— NOT :=True (V_NockVMROM_cite/_forest_cite name the real types). WITNESS-SHARING REAL: " ++
  "reqRecs = compute walk's emitted opcode-active mem-records (b10_reqRecs_row: " ++
  "[encRec b10_reqRec]), " ++
  "respRecs = memory walk's read_root served records (b10_respRecs_row/_value: " ++
  "[![2,0,3,1,0,0,4,5]]); both HONEST functions of the walk (halt-row serves nothing " ++
  "b10_respRecs_halt; empty at 0 rows). CARRIED (documented, CONFIRMED): (b) SEED-PIN DROPPED — " ++
  "conjunct (3) is IO-MULTISET only (LIO ⇒ Perm, b10_LIO_is_multiset_perm), strictly weaker than " ++
  "a forward per-record identity (b10_perm_weaker_than_eq); the Def:MES seed pin (main.tex:391) " ++
  "is delivered ONLY via seedCoupled_of_LIO WITH extra hLIO + hReqTs (b10_seedPin_needs_LIO_and_ts) " ++
  "— NOT a closed 'NockVM is MES'. (c) SINGLE-ROOT vs FOREST — V_NockVMROM = kroots=1 case " ++
  "(b10_forestReconGoal_one: ForestReconGoal … 1 ↔ ReconGoal), multi-root = V_NockVMROM_forest " ++
  "(main.tex:1441), independent proofs. (d) ε_RLC retained (CENSUS #4), BFSValid from QGate " ++
  "(CENSUS #5), costs carried defs (CENSUS §D); one-hot size 10 = numeric OP_0..OP_9 " ++
  "(b10_numeric_opcodes), cons=op_11 SEPARATE (b10_cons_separate) — NOT a discrepancy. " ++
  "Disposition: conjuncts PASSED / (b)(c)(d) DOCUMENTED-carried (honestly stated, not overclaimed)."

end Thm_NockVMROM


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch10_drift_summary : String :=
  "BATCH 10 CAPSTONE THEOREMS DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Thm:Noun_Validation — PASSED (genuine ↔; atom λ=1 + cell ⟦0 1⟧ λ=2 both directions fire; " ++
     "wrong-length + empty-transcript discrimination; 1≤leaves guard sound)\n" ++
  "2. Thm:IO_result       — PASSED ⚠ CENSUS #6: io_result + io_result_LIO genuine biconditionals; " ++
     "LIO non-vacuous over ℕ (single/perm IN, length/Nodup OUT); LmIO bidirectional-membership " ++
     "repair load-bearing ([1,1]/[1,2] REJECTED, [1,1]/[1] ACCEPTED). costs=no-Lean.\n" ++
  "3. Thm:NockVMROM       — conjuncts PASSED ⚠ CARRIES (b)(c)(d): real 3-conjunct witness-shared " ++
     "↔ (V_NockVMROM/_forest); reqRecs/respRecs HONEST walk functions ([encRec …] values, " ++
     "halt-row empty). (b) seed-pin DROPPED (IO-multiset only; LIO⇒Perm ⊊ per-record; delivered " ++
     "only via seedCoupled_of_LIO + hReqTs). (c) single-root=kroots=1 vs forest independent. " ++
     "(d) ε_RLC/QGate/costs; one-hot 10=numeric, cons=op_11 separate (non-discrepancy).\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. Documented deltas CONFIRMED (not re-flagged as new drift):\n" ++
  "• CENSUS #6 (LOW): io_result_LIO/LmIO bidirectional membership repair (paper one-directional " ++
     "cond-3 false as written). Confirmed load-bearing; already in Batch 5/9.\n" ++
  "• Theorem 5.4 (b): compute↔memory coupling IO-MULTISET only; Def:MES SEED-PIN (main.tex:391) " ++
     "DROPPED — deferred, disclosed; NOT a closed 'NockVM is MES' (Batch 9 nock_MES.hcorrect " ++
     "carries).\n" ++
  "• Theorem 5.4 (c): V_NockVMROM single-root (kroots=1); multi-root subject-mutating = " ++
     "V_NockVMROM_forest (Corr:forest, main.tex:1441); proved independently. SCOPE, not a bug.\n" ++
  "• Theorem 5.4 (d): honest +ε_RLC retained (CENSUS #4); BFSValid/tiling DERIVED from QGate " ++
     "(CENSUS #5); cost figures carried defs (CENSUS §D). one-hot size 10 = 10 numeric opcodes " ++
     "OP_0..OP_9, cons=op_11 SEPARATE selector — NOT a discrepancy (CENSUS note).\n" ++
  "CAPSTONE VERDICT: the 3 conjuncts are genuinely proved/certified over a witness-SHARED " ++
  "multiset; (b) seed-pin, (c) forest/single-root scope, (d) costs are DOCUMENTED-carried and " ++
  "stated honestly IN THE ARTIFACT. NO claim that NockVM is MES / seed-pin discharged / forest " ++
  "closed.\n" ++
  "AXIOM HYGIENE: witnesses over ZMod 7 (Fact prime by norm_num) / ℕ / Noun / Bool; NO " ++
  "goldilocks_prime; no sorry/admit/native_decide/stop/axiom/@[extern]. Classical.choice appears " ++
  "only via the classical DecidableEq (MemRec K) baked into reqRecs (whitelisted)."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SELF-CERTIFICATION: `#print axioms` for every proof-carrying declaration
    (all must be ⊆ {propext, Classical.choice, Quot.sound}; NONE uses goldilocks_prime)
    ══════════════════════════════════════════════════════════════════════════════════════
-/

-- Object 1
#print axioms noun_validation_cite
#print axioms b10_atom_leaves
#print axioms b10_cell_leaves
#print axioms b10_atom_accept
#print axioms b10_atom_len
#print axioms b10_cell_accept
#print axioms b10_cell_len
#print axioms b10_atom_forward
#print axioms b10_atom_backward
#print axioms b10_cell_forward
#print axioms b10_cell_backward
#print axioms b10_cell_wrong_lam
#print axioms b10_empty_not_accept
#print axioms b10_one_le_leaves
#print axioms b10_size_add_one
-- Object 2
#print axioms io_result_cite
#print axioms io_result_LIO_cite
#print axioms b10_LIO_single
#print axioms b10_LIO_perm
#print axioms b10_not_LIO_len
#print axioms b10_not_LIO_dup
#print axioms b10_census6_not_LmIO
#print axioms b10_LmIO_multiset
-- Object 3
#print axioms V_NockVMROM_cite
#print axioms V_NockVMROM_forest_cite
#print axioms b10_respRecs_row
#print axioms b10_respRecs_value
#print axioms b10_respRecs_halt
#print axioms b10_reqRecs_row
#print axioms b10_reqRecs_zero
#print axioms b10_respRecs_zero
#print axioms b10_LIO_is_multiset_perm
#print axioms b10_perm_weaker_than_eq
#print axioms b10_seedPin_needs_LIO_and_ts
#print axioms SeedCoupled_cite
#print axioms seedCoupled_of_LIO_cite
#print axioms V_NockVMROM_seedcoupled_cite
#print axioms b10_forestReconGoal_one
#print axioms b10_opcode_onehot_size
#print axioms b10_mem_record_arity
#print axioms b10_numeric_opcodes
#print axioms b10_cons_separate

end Nock.RedTeam
