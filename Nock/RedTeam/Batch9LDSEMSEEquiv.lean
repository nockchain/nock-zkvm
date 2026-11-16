/-
  Nock/RedTeam/Batch9LDSEMSEEquiv.lean

  Independent verification of definitional faithfulness + non-vacuity/discrimination witnesses,
  and CONFIRMATION (not re-flagging) of the documented scoping deltas.

This artifact provides MACHINE-CHECKED evidence for:
  1. Lem:ldse_mse         — `Nock.SetEq.ldse_mse` (+ general `mse_ldse_general`)  (Lem)
  2. Lem:mse_ldse_equiv   — `Nock.SetEq.mse_ldse_equiv` (+ `MSEcond`/`LDSEcond`)  (Lem)

  4. Def:MEF              — `Nock.Framework.MEF` (+ `MEF.Rec`/`MEF.Seq`)          (Def)
  5. Def:MES              — `Nock.Framework.MES` (+ instance `nock_MES`)          (Def) ⚠ CARRIED hcorrect
  6. Def:RVT              — `Nock.Walk.RVT` (+ `Nock.Walk.ProperArity`)           (Def) ⚠ def⚠ arity gap

  HYGIENE: No `sorry`, `admit`, `native_decide`, `axiom`, or `@[extern]`.
  Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}.  Field-arithmetic non-vacuity is
  audited over the AXIOM-CLEAN finite prime field `ZMod 5` (`Fact (Nat.Prime 5)` via `norm_num`),
  so NOT EVEN the whitelisted `Nock.Field.goldilocks_prime` is needed anywhere in this batch.
-/
import Nock.SetEq
import Nock.IO
import Nock.Framework
import Nock.Walk
import Nock.NockVM
import Mathlib.Tactic.NormNum.Prime

namespace Nock.RedTeam

open Nock Nock.Walk Nock.Framework Nock.ComputeTable Nock.MemoryTable

/-- Axiom-clean primality fact for the small finite prime field used as concrete witness.
    (`Nat.Prime 5` via `norm_num`; NO `goldilocks_prime`.) -/
instance fact_prime_5_b9 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Lem:ldse_mse` — `Nock.SetEq.ldse_mse` + `mse_ldse_general`
    ══════════════════════════════════════════════════════════════════════════════════════

    Over a field `L` with `[CharP L p]` and `n < p`:
      `(∏ i, (X + C (a i)) = ∏ i, (X + C (b i)))  ↔  (∑ i, frac (a i) = ∑ i, frac (b i))`,
    with `frac c = 1/(X + c)` in `RatFunc L`.  `ldse_mse` is the paper's fixed-`n` (equal-length)
    corollary; `mse_ldse_general` is the general unequal-length form (via multiset factorization),
    which the equal-length `ldse_mse` is just a specialization of.

    NON-VACUITY: the reflexive case `a = b` makes the product equation hold by `rfl`, so the
    biconditional is inhabited with a REAL `hn : n < p` and a REAL char-`p` field — instantiated
    over `ZMod 5` (`p = 5`, `n = 1`, `a = b = ![0]`).

    NOTE (benign strengthening): `mse_ldse_general` allows `n₁ ≠ n₂`; equality of either side
    already forces the two root-multisets (hence the lengths) to coincide, so this is strictly
    STRONGER than the paper's fixed-`n` statement without being unsound.

    Disposition: PASSED (verdict 1-1; both forms cited; benign strengthening documented).
-/

section Lem_ldse_mse

/-- **[1.cite.eq] `ldse_mse`** — the paper's equal-length corollary. -/
noncomputable def ldse_mse_cite := @SetEq.ldse_mse

/-- **[1.cite.gen] `mse_ldse_general`** — the general (unequal-length `n₁,n₂`) form. -/
noncomputable def mse_ldse_general_cite := @SetEq.mse_ldse_general

/-- **[1.a] NON-VACUITY: the reflexive biconditional instantiates over `ZMod 5`** (`p=5`, `n=1`,
    `a=b=![0]`), with a genuine `hn : 1 < 5` — the hypotheses are all real. -/
theorem ldse_mse_reflexive_iff :
    (∏ i, (Polynomial.X + Polynomial.C ((![0] : Fin 1 → ZMod 5) i)))
        = (∏ i, (Polynomial.X + Polynomial.C ((![0] : Fin 1 → ZMod 5) i)))
      ↔ (∑ i, SetEq.frac ((![0] : Fin 1 → ZMod 5) i)
          = ∑ i, SetEq.frac ((![0] : Fin 1 → ZMod 5) i)) :=
  SetEq.ldse_mse (p := 5) (by norm_num) (![0] : Fin 1 → ZMod 5) (![0] : Fin 1 → ZMod 5)

/-- **[1.a'] The product side holds by `rfl` (`a = b`), so the biconditional is genuinely
    satisfiable — push it forward to obtain the log-derivative (sum) side. -/
theorem ldse_mse_reflexive_sum :
    (∑ i, SetEq.frac ((![0] : Fin 1 → ZMod 5) i))
      = ∑ i, SetEq.frac ((![0] : Fin 1 → ZMod 5) i) :=
  ldse_mse_reflexive_iff.mp rfl

/-- **[1.b] The general form specializes to the equal-length one** — feeding `n₁ = n₂ = n` and the
    same `hn` on both sides recovers `ldse_mse` (documents that `ldse_mse` is `mse_ldse_general`'s
    diagonal, so the general form is a true superset). -/
theorem ldse_mse_is_general_diagonal {L : Type*} [Field L] {p : ℕ} [CharP L p] {n : ℕ}
    (hn : n < p) (a b : Fin n → L) :
    (SetEq.ldse_mse hn a b) = SetEq.mse_ldse_general hn hn a b :=
  rfl

/-- **[1.doc]** -/
def ldse_mse_doc : String :=
  "Lem:ldse_mse (main.tex:234) → Nock.SetEq.ldse_mse (SetEq.lean:283) + general " ++
  "mse_ldse_general (SetEq.lean:241). (∏(X+C(aᵢ)) = ∏(X+C(bᵢ))) ↔ (∑ frac(aᵢ) = ∑ frac(bᵢ)) over " ++
  "field L, [CharP L p], n < p; frac c = 1/(X+c) in RatFunc L. NON-VACUITY: reflexive a=b=![0] " ++
  "over ZMod 5 (p=5,n=1) with real hn:1<5 (ldse_mse_reflexive_iff/_sum). BENIGN STRENGTHENING: " ++
  "mse_ldse_general allows n₁≠n₂ (equality forces the root-multisets to coincide anyway), a true " ++
  "superset of the paper's fixed-n; ldse_mse is its diagonal (ldse_mse_is_general_diagonal). " ++
  "Verdict: 1-1. Disposition: PASSED."

end Lem_ldse_mse


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Lem:mse_ldse_equiv` — `Nock.SetEq.mse_ldse_equiv`
    ══════════════════════════════════════════════════════════════════════════════════════

    `MSEcond req resp ↔ LDSEcond req resp` for `req : Fin k₁ → Fin m → 𝔽`,
    `resp : Fin k₂ → Fin m → 𝔽`, with `hk₁ : k₁ < p`, `hk₂ : k₂ < p`, over `[Field 𝔽][CharP 𝔽 p]`.
    `MSEcond` = `∏(X + C(RLC reqᵢ)) = ∏(X + C(RLC respⱼ))`; `LDSEcond` = `∑ frac(RLC reqᵢ) =
    ∑ frac(RLC respⱼ)`.

    NON-VACUITY: the reflexive `req = resp` (with `k₁ = k₂`) makes `MSEcond` hold by `rfl`, so the
    ↔ is inhabited; instantiated concretely over `ZMod 5` (`k₁=k₂=1`, `m=1`, `req=resp=fun _ _=>0`).

    DOCUMENTED SCOPING (CONFIRM — do NOT re-flag as new drift): the Lean proves the EQUATION-level
    biconditional `MSEcond ↔ LDSEcond` on FIXED `(k₁,k₂,m)`-indexed sequences.  The paper's
    LANGUAGE-level `≡` (`L^{Y,K}_{MSE} ≡ L^{Y,K}_{LDSE}`) additionally bundles the
    shared membership constraint `∃ k₁,k₂,m ∈ [K]`; that packaging is assembled DOWNSTREAM (via
    `IO.LSE`/`IO.LumLDSE` and `IO.mio_ldse`).  CORRESPONDENCE's "1-1" is accurate for the defining
    EQUATIONS; the language-level ≡ is an assembly step, not a same-lemma claim.

    Disposition: PASSED (verdict 1-1 at the EQUATION level; language-level ≡ is downstream assembly).
-/

section Lem_mse_ldse_equiv

/-- **[2.cite] `mse_ldse_equiv`** — the equation-level biconditional. -/
noncomputable def mse_ldse_equiv_cite := @SetEq.mse_ldse_equiv

/-- **[2.a] NON-VACUITY: `MSEcond` holds reflexively** (`req = resp`, `k₁=k₂=1`, `m=1`) over
    `ZMod 5` — `∏ = ∏` by `rfl`. -/
theorem mse_ldse_equiv_MSEcond_reflexive :
    SetEq.MSEcond (𝔽 := ZMod 5) (fun _ _ : Fin 1 => (0 : ZMod 5))
      (fun _ _ : Fin 1 => (0 : ZMod 5)) :=
  rfl

/-- **[2.a'] …push it through the biconditional to obtain the reflexive `LDSEcond`.**  This
    exercises the ↔ non-vacuously with real `hk₁, hk₂ : 1 < 5`. -/
theorem mse_ldse_equiv_LDSEcond_reflexive :
    SetEq.LDSEcond (𝔽 := ZMod 5) (fun _ _ : Fin 1 => (0 : ZMod 5))
      (fun _ _ : Fin 1 => (0 : ZMod 5)) :=
  (SetEq.mse_ldse_equiv (𝔽 := ZMod 5) (p := 5) (by norm_num) (by norm_num)
    (fun _ _ : Fin 1 => (0 : ZMod 5)) (fun _ _ : Fin 1 => (0 : ZMod 5))).mp
    mse_ldse_equiv_MSEcond_reflexive

/-- **[2.doc]** -/
def mse_ldse_equiv_doc : String :=
  "Lem:mse_ldse_equiv (main.tex:241) → Nock.SetEq.mse_ldse_equiv (SetEq.lean:541). " ++
  "MSEcond req resp ↔ LDSEcond req resp, req:Fin k₁→Fin m→𝔽, resp:Fin k₂→Fin m→𝔽, hk₁:k₁<p, " ++
  "hk₂:k₂<p, [Field 𝔽][CharP 𝔽 p] (defs MSEcond/LDSEcond at SetEq.lean:528-535). NON-VACUITY: " ++
  "reflexive req=resp (k₁=k₂=1,m=1) over ZMod 5 (mse_ldse_equiv_MSEcond_reflexive/_LDSEcond_). " ++
  "DOCUMENTED SCOPING (CONFIRMED, not new drift): Lean proves the EQUATION-level ↔ on FIXED " ++
  "(k₁,k₂,m); the paper's LANGUAGE-level ≡ (L_MSE ≡ L_LDSE) bundles ∃ k₁,k₂,m ∈ [K] + the " ++
  "equation, ASSEMBLED downstream via IO.LSE/IO.LumLDSE + IO.mio_ldse. CORRESPONDENCE '1-1' is " ++
  "accurate for the defining equations; language-level ≡ is an assembly step. " ++
  "Verdict: 1-1 (equation level). Disposition: PASSED."

end Lem_mse_ldse_equiv


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3.

    `mio_ldse (K) (hKp : K < p) (hM : InRange K M) (req resp : List (Fin M → 𝔽)) :
        LmIO K req resp ↔ LumLDSE K req resp`, over `[Field 𝔽][CharP 𝔽 p]`.

    NON-VACUITY: on a concrete satisfiable pair over `ZMod 5` (`M=1`, `K=1`, `req=resp=[![0]]`)
    both `hKp : 1 < 5` and `hM : InRange 1 1` hold; `LmIO 1 [![0]] [![0]]` is proved and pushed
    through the ↔ to `LumLDSE 1 [![0]] [![0]]`.

    As written one-directionally, only
    `set(requests) ⊆ set(responses)` follows, which makes `lem_mio_ldse` FALSE (witness
    `req=[x,x], resp=[x,y]`: passes the one-directional read but the RLC-value sets differ, so
    `LumLDSE` fails). `LmIO_iff` exhibits the repaired `toFinset` (set-EQUALITY, both directions)
    characterization that is load-bearing here.

    Disposition: PASSED.
-/

section Lem_mio_ldse

/-- **[3.cite] `mio_ldse`** — the record ↔ log-derivative biconditional. -/
noncomputable def mio_ldse_cite := @Nock.IO.mio_ldse

/-- **[3.cite.iff] `LmIO_iff`** — the repaired `toFinset` (bidirectional set-equality)
    characterization. -/
theorem LmIO_iff_cite (K : ℕ) (req resp : List (Fin 1 → ZMod 5)) :
    Nock.IO.LmIO K req resp ↔
      (Nock.IO.InRange K req.length ∧ resp.length ≤ req.length ∧ resp.Nodup
        ∧ req.toFinset = resp.toFinset) :=
  Nock.IO.LmIO_iff K req resp

/-- The concrete request/response record `x = ![0] : Fin 1 → ZMod 5`. -/
def xIO : Fin 1 → ZMod 5 := ![0]

/-- **[3.a] NON-VACUITY: `LmIO 1 [x] [x]` holds** — a genuine satisfiable pair (via the repaired
    `LmIO_iff`: distinct responses with equal request/response value-sets). -/
theorem mio_LmIO : Nock.IO.LmIO 1 [xIO] [xIO] := by
  rw [Nock.IO.LmIO_iff]
  exact ⟨⟨le_refl _, le_refl _⟩, le_refl _, List.nodup_singleton _, rfl⟩

/-- **[3.a'] …push `LmIO` through `mio_ldse` to obtain `LumLDSE 1 [x] [x]`** — the ↔ fires
    non-vacuously with real `hKp : 1 < 5` and `hM : InRange 1 1`. -/
theorem mio_LumLDSE : Nock.IO.LumLDSE 1 [xIO] [xIO] :=
  (Nock.IO.mio_ldse (𝔽 := ZMod 5) (p := 5) 1 (by norm_num) ⟨le_refl _, le_refl _⟩ [xIO] [xIO]).mp
    mio_LmIO

/-- Witnessed here by the toFinset inequality. -/
theorem census6_toFinset_differs :
    ([xIO, xIO].toFinset ≠ [xIO, (![1] : Fin 1 → ZMod 5)].toFinset) := by
  decide

/-- **[3.doc]** -/
def mio_ldse_doc : String :=
  "lem_mio_ldse (main.tex:279) → Nock.IO.mio_ldse (IO.lean:307). LmIO K req resp ↔ LumLDSE K req " ++
  "resp over [Field 𝔽][CharP 𝔽 p]; LmIO at IO.lean:68, LumLDSE at IO.lean:233, LmIO_iff at " ++
  "IO.lean:78. NON-VACUITY: on req=resp=[![0]] over ZMod 5 (M=1,K=1), LmIO holds (mio_LmIO) and " ++
  "pushes through to LumLDSE (mio_LumLDSE) with real hKp:1<5, hM:InRange 1 1. ⚠ CENSUS #6 (LOW) " ++
  "CONFIRMED: LmIO uses BIDIRECTIONAL membership ∀ x, x∈requests ↔ x∈uniq (a repair). The paper's " ++
  "one-directional cond-3 (main.tex:198) makes the lemma FALSE as written — witness req=[x,x], " ++
  "resp=[x,y] passes one-directionally but req.toFinset ≠ resp.toFinset (census6_toFinset_differs), " ++
  "so LumLDSE fails. LmIO_iff exhibits the load-bearing toFinset set-EQUALITY. Already witnessed " ++
  "in Batch 5 IO (not re-proved). Verdict: 1-1*. Disposition: PASSED."

end Lem_mio_ldse


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 4. `Def:MEF` — `Nock.Framework.MEF`
    ══════════════════════════════════════════════════════════════════════════════════════

    The memory encoding family `MEM = (𝒜, 𝒱𝒟, 𝒯)`: a GENUINE structure with fields `A VD T : Type`
    plus `Tord : LinearOrder T` (the formalization of "ordered set of timestamps"), abbreviations
    `MEF.Rec = A × VD × T` and `MEF.Seq k = Fin k → Rec`.

    FAITHFULNESS: `A/VD/T` are real type fields (NOT `:= True`); `Tord` a real `LinearOrder` field —
    a reasonable faithful choice for "ordered timestamps".  NON-VACUITY: a concrete `MEF` is built
    by hand (`A=VD=T=ℕ` with the natural `LinearOrder`).

    Disposition: def (PASSED — faithful, inhabited structure).
-/

section Def_MEF

/-- **[4.cite] `MEF` is a genuine `Type`-valued structure** (not `:= True`; it lives in `Type 1`
    because its `A/VD/T` fields are `Type`). -/
def MEF_cite : Type 1 := MEF

/-- **[4.a] NON-VACUITY: a concrete `MEF` built by hand** (`A=VD=T=ℕ`, natural `LinearOrder`). -/
def toyMEF : MEF where
  A := ℕ
  VD := ℕ
  T := ℕ
  Tord := inferInstance

/-- `toyMEF`'s record type `ℕ × ℕ × ℕ` has decidable equality (needed for the `L_mIO`/`MES`
    obligations below). -/
instance : DecidableEq toyMEF.Rec := inferInstanceAs (DecidableEq (ℕ × ℕ × ℕ))

/-- **[4.b] FAITHFULNESS: the abbreviation `MEF.Rec` is the record triple `A × VD × T`.** -/
theorem toyMEF_Rec : toyMEF.Rec = (ℕ × ℕ × ℕ) := rfl

/-- **[4.b'] FAITHFULNESS: `MEF.Seq k` is a length-`k` ordered tuple of records.** -/
theorem toyMEF_Seq : toyMEF.Seq 3 = (Fin 3 → ℕ × ℕ × ℕ) := rfl

/-- **[4.c] FAITHFULNESS: the type fields are REAL** (not `:= True`) — `A` and `T` are `ℕ`. -/
theorem toyMEF_A : toyMEF.A = ℕ := rfl
theorem toyMEF_T : toyMEF.T = ℕ := rfl

/-- **[4.c'] FAITHFULNESS: `Tord` is a genuine `LinearOrder` field** (the "ordered timestamps"). -/
noncomputable def toyMEF_Tord : LinearOrder toyMEF.T := toyMEF.Tord

/-- **[4.doc]** -/
def MEF_doc : String :=
  "Def:MEF (main.tex:172) → Nock.Framework.MEF (Framework.lean:52). GENUINE structure: fields " ++
  "A VD T : Type + Tord : LinearOrder T; abbrevs MEF.Rec = A×VD×T, MEF.Seq k = Fin k→Rec " ++
  "(Framework.lean:63). FAITHFUL: type fields real (toyMEF_A/_T), Tord a real LinearOrder " ++
  "(toyMEF_Tord) — the formalization of 'ordered set of timestamps' (a reasonable faithful " ++
  "choice). NON-VACUITY: toyMEF (A=VD=T=ℕ) inhabits MEF; Rec/Seq compute (toyMEF_Rec/_Seq). " ++
  "Verdict: def. Disposition: PASSED."

end Def_MEF


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 5. `Def:MES` — `Nock.Framework.MES` + instance `nock_MES`  ⚠ CARRIED
    ══════════════════════════════════════════════════════════════════════════════════════

    THIS IS A CONCERN OBJECT.  `MES X Tw M` is a GENUINE structure with real type/verifier fields
    (`Xprog…IOmem`, `LangVM`, `LangVMComputation`, `LangVMMemory`), bijections `splitX`/`splitT`,
    `K`, `ioRecords`, and crucially a REAL biconditional field
      `correct : ∀ x, (∃ T, LangVM x T) ↔ (∃ decomposition with LangVMComputation ∧ LangVMMemory ∧
                  IO.LmIO K …)`   — NOT `:= True`.

    FAITHFULNESS + NON-VACUITY: we build a TINY TOY `MES` instance by hand over trivial types
    (`X = Tw = Unit`, `M = toyMEF`, trivial `LangVM`) where `correct` is GENUINELY PROVED (the RHS
    `LmIO 1 [r] [r]` holds).  This is the cleanest non-vacuity witness — the DEFINITION is inhabited
    with a real, discharged biconditional.

    CONFIRM THE DOCUMENTED DELTA HONESTLY (CORRESPONDENCE Def 3.1 note + Framework.lean:1008-1029 +
    §141/§199): the NOCK instance `nock_MES` does NOT discharge `hcorrect` — it takes it as an
    EXPLICIT CARRIED HYPOTHESIS.  So the paper's claim "NockVM is MES" is NOT closed in `Framework`
    alone.  The docstring (Framework.lean:1010-1029) explains WHY it cannot be discharged from the
    §5 capstone:
      (i)  SHAPE mismatch — `MES.correct` is a DETERMINISTIC, EXACT biconditional, whereas
           `V_NockVMROM_forest` proves a PROBABILISTIC soundness bound (one-directional
           `equiv_compute_sound`/`equiv_mem_sound` wrapped in a probability bound); neither implies
           the other.
      (ii) NO concrete `LangVM` is defined at the capstone level (`nock_MES` is parametric over an
           abstract `LangVM`, `splitX`, etc.).

    HONEST VERDICT: the STRUCTURE/definition is FAITHFUL and SUBSTANTIVE (real biconditional,
    inhabited by a toy instance that DISCHARGES `correct`).  The Nock INSTANCE carries `hcorrect`
    as a DISCLOSED hypothesis — a genuine CONNECTIVE GAP, honestly flagged — which is NOT vacuity of
    the definition, but ALSO NOT a closed proof that NockVM is MES.

    Disposition: STRUCTURE PASSED (faithful, non-vacuous, real biconditional); INSTANCE CARRIES
    `hcorrect` (connective gap, disclosed — NOT vacuity, NOT a closed "NockVM is MES").
-/

section Def_MES

/-- **[5.cite] `MES` is a genuine dependent structure** (not `:= True`). -/
noncomputable def MES_cite := @Nock.Framework.MES


def rMES : toyMEF.Rec := ((0 : ℕ), (0 : ℕ), (0 : ℕ))

/-- **[5.a] The `L_mIO` obligation the toy `correct` must discharge holds**: `LmIO 1 [r] [r]`. -/
theorem toyMES_LmIO : Nock.IO.LmIO 1 [rMES] [rMES] := by
  rw [Nock.IO.LmIO_iff]
  exact ⟨⟨le_refl _, le_refl _⟩, le_refl _, List.nodup_singleton _, rfl⟩

/-- **[5.b] NON-VACUITY: a TOY `MES` instance built by hand over trivial types, with `correct`
    GENUINELY PROVED** — the definition is inhabited with a real, discharged biconditional. -/
noncomputable def toyMES : MES Unit Unit toyMEF where
  Xprog := Unit
  Xmem := PUnit
  Tprog := Unit
  Tmem := PUnit
  IOprog := Unit
  IOmem := Unit
  LangVM := fun _ _ => True
  LangVMComputation := fun _ _ _ => True
  LangVMMemory := fun _ _ _ => True
  splitX := (Equiv.prodPUnit Unit).symm
  splitT := (Equiv.prodPUnit Unit).symm
  K := 1
  ioRecords := fun _ _ => ([rMES], [rMES])
  correct := by
    intro _
    constructor
    · intro _; exact ⟨(), (), (), trivial, trivial, toyMES_LmIO⟩
    · intro _; exact ⟨(), trivial⟩

/-- **[5.c] FAITHFULNESS: `MES.correct` is a REAL biconditional field** (not `:= True`) — the toy
    instance's `correct` projection IS the paper's separation ↔ at `x`. -/
theorem toyMES_correct_is_iff :
    ∀ x : Unit, (∃ _T : Unit, toyMES.LangVM x _T) ↔
      ∃ (_T : Unit) (ioP : toyMES.IOprog) (ioM : toyMES.IOmem),
        toyMES.LangVMComputation (toyMES.splitX x).1 (toyMES.splitT _T).1 ioP
        ∧ toyMES.LangVMMemory (toyMES.splitX x).2 (toyMES.splitT _T).2 ioM
        ∧ Nock.IO.LmIO toyMES.K (toyMES.ioRecords ioP ioM).1 (toyMES.ioRecords ioP ioM).2 :=
  toyMES.correct

/-- **[5.d] DOCUMENTED DELTA (crisp): `nock_MES` CARRIES `hcorrect`.**  The Nock instance is a
    function that TAKES `hcorrect` (the separation ↔) as an explicit argument and installs it as
    `correct` — it does NOT prove it.  Cited by naming the constant (its type exhibits `hcorrect`
    as a required hypothesis). -/
noncomputable def nock_MES_cite := @Nock.Framework.nock_MES

/-- **[5.d'] The carried hypothesis IS installed verbatim as `correct`.**  For any supplied
    `hcorrect`, `(nock_MES …).correct = hcorrect` — pinning that the instance adds NO new proof
    content; `hcorrect` is the disclosed connective gap. -/
theorem nock_MES_correct_is_hcorrect
    (K : Type*) [Field K] (M : MEF) [DecidableEq M.Rec]
    (X Tw : Type*) (Ksz : ℕ) (LangVM : X → Tw → Prop)
    (splitX : X ≃ NTree (State × DTcomp K) × NTree (MState × DTmem K))
    (hcorrect : ∀ x : X, (∃ T, LangVM x T) ↔
      ∃ (_T : Tw) (ioP ioM : List M.Rec),
        RVT (Fcomp (K := K)) (splitX x).1 ∧ RVT (Fmem (K := K)) (splitX x).2
        ∧ Nock.IO.LmIO Ksz ioP ioM) :
    (Nock.Framework.nock_MES K M X Tw Ksz LangVM splitX hcorrect).correct = hcorrect :=
  rfl

/-- **[5.doc]** -/
def MES_doc : String :=
  "Def:MES (main.tex:391) → Nock.Framework.MES (Framework.lean:165) + instance nock_MES " ++
  "(Framework.lean:1035). STRUCTURE: GENUINE (fields Xprog..IOmem, LangVM/LangVMComputation/" ++
  "LangVMMemory, splitX/splitT, K, ioRecords, and a REAL biconditional field `correct`, NOT " ++
  ":=True — toyMES_correct_is_iff). FAITHFUL + NON-VACUOUS: toyMES : MES Unit Unit toyMEF built " ++
  "by hand over trivial types, `correct` GENUINELY PROVED (RHS LmIO 1 [r] [r] holds, toyMES_LmIO). " ++
  "DOCUMENTED DELTA (CORRESPONDENCE Def 3.1 + Framework.lean:1008-1029): nock_MES does NOT " ++
  "discharge hcorrect — it CARRIES it as an explicit hypothesis (nock_MES_correct_is_hcorrect: " ++
  "correct = hcorrect verbatim). Undischargeable from §5 capstone because (i) SHAPE mismatch — " ++
  "MES.correct is a deterministic EXACT ↔, V_NockVMROM_forest is a PROBABILISTIC soundness bound " ++
  "(one-directional equiv_compute_sound/equiv_mem_sound), neither implying the other; (ii) NO " ++
  "concrete LangVM at capstone level. HONEST VERDICT: STRUCTURE faithful + substantive (inhabited " ++
  "with a discharged ↔); INSTANCE carries hcorrect as a disclosed CONNECTIVE GAP — NOT vacuity of " ++
  "the definition, but NOT a closed proof that NockVM is MES. Disposition: STRUCTURE PASSED / " ++
  "INSTANCE CARRIES hcorrect."

end Def_MES


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 6. `Def:RVT` — `Nock.Walk.RVT` + `Nock.Walk.ProperArity`  ⚠ def⚠
    ══════════════════════════════════════════════════════════════════════════════════════

    THIS IS A def⚠ OBJECT.  `RVT F t` (for `F : LT → (Fin n → Option LT) → Prop`) recursively
    requires, at each `node l ch`:
      (1) `F l (fun i => t.childLabel i)`               — node label verifies against child labels;
      (2) `∀ s ∈ ch, RVT F s`                            — every child is itself `RVT`;
      (3) `t.isLeaf ↔ F l (fun _ => none)`               — leaf ⟺ label verifies with no children.

    CRUCIALLY `RVT` does NOT bound the number of children: clause (1) only constrains child slots
    `0..n-1` (via `childLabel : Fin n → …`) while clause (2) recurses into ALL children.  So a node
    with `> n` children can still satisfy `RVT F`.  `ProperArity n t := ∀ s, InTree t s →
    s.children.length ≤ n` supplies the missing `L_SLT^n` arity bound; the FAITHFUL language is
    `{t // RVT F t ∧ ProperArity n t}` (documented at Walk.lean:1096-1100).

    FAITHFULNESS: a type-checking unfolding shows `RVT` captures per-node verification (1) +
    recursion (2) + the leaf-iff clause (3).

    NON-VACUITY: a fresh `RVT` leaf witness (`rvt_leaf`), and the concrete Nock RVT languages are
    inhabited via `Fcomp_nonvacuous`/`Fmem_nonvacuous`.

    KEY DELTA (def⚠): a concrete tree that SATISFIES `RVT F` but VIOLATES `ProperArity 1` — a node
    with 2 children over a trivial `F` — witnessing `{t // RVT F t} ⊋ {t // RVT F t ∧ ProperArity n t}`,
    so `RVT` alone is STRICTLY LARGER than the paper's `L_RVT^{F,n}`.  This is a documented
    completeness/scoping under-specification, NOT unsoundness.

    Disposition: def⚠ (PASSED — faithful as-far-as-it-goes; arity gap confirmed; `ProperArity`
    supplies the missing bound).
-/

section Def_RVT

/-- **[6.a] FAITHFULNESS: `RVT` is EXACTLY "every node satisfies its per-row F-constraint"** —
    `RVT_iff_forall_InTree`: `RVT F root ↔ ∀ t, InTree root t → Fcon F t`, where `Fcon F t` bundles
    clause (1) `F (label t) childLabel` and clause (3) `isLeaf ↔ F (label t) (fun _ => none)`, and
    the `∀ t, InTree root t` quantifier realizes clause (2) recursion into every node.  So the
    Lean `RVT` faithfully encodes the paper's per-node verification + recursion + leaf-iff clause. -/
theorem rvt_node_faithful {S DT : Type*} {n : ℕ}
    (F : (S × DT) → (Fin n → Option (S × DT)) → Prop) (root : NTree (S × DT)) :
    RVT F root ↔ ∀ t, InTree root t → Fcon F t :=
  Nock.Walk.RVT_iff_forall_InTree F root

/-- **[6.a'] `Fcon` per-node constraint = clause (1) ∧ clause (3)** — a type-checking citation
    pinning what each node must satisfy. -/
theorem rvt_Fcon_shape {S DT : Type*} {n : ℕ}
    (F : (S × DT) → (Fin n → Option (S × DT)) → Prop) (t : NTree (S × DT)) :
    Fcon F t ↔
      (F (NTree.label t) (fun i => t.childLabel i)
        ∧ (t.isLeaf ↔ F (NTree.label t) (fun _ => none))) :=
  Iff.rfl

/-- **[6.b] Leaf-RVT builder (fresh): any label `lbl` with `F lbl (fun _ => none)` gives an RVT
    leaf.** -/
theorem rvt_leaf_b9 {LT : Type*} {n : ℕ} {F : LT → (Fin n → Option LT) → Prop} {lbl : LT}
    (h : F lbl (fun _ => none)) : RVT F (NTree.node lbl []) := by
  unfold RVT
  refine ⟨h, ?_, ?_⟩
  · intro s hs; simp at hs
  · exact ⟨fun _ => h, fun _ => rfl⟩

/-- **[6.b'] NON-VACUITY: the compute RVT-language `{t // RVT Fcomp t}` is inhabited** (from
    `Fcomp_nonvacuous`). -/
noncomputable def compRVT_inhabited_b9 :
    {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t} :=
  ⟨NTree.node (Fcomp_nonvacuous (K := ℚ)).choose [],
    rvt_leaf_b9 (Fcomp_nonvacuous (K := ℚ)).choose_spec⟩

/-- **[6.b''] NON-VACUITY: the memory RVT-language `{t // RVT Fmem t}` is inhabited** (from
    `Fmem_nonvacuous`). -/
noncomputable def memRVT_inhabited_b9 :
    {t : NTree (MState × DTmem ℚ) // RVT (Fmem (K := ℚ)) t} :=
  ⟨NTree.node (Fmem_nonvacuous (K := ℚ)).choose [],
    rvt_leaf_b9 (Fmem_nonvacuous (K := ℚ)).choose_spec⟩

/-- The arity-gap verifier: `F l cl` accepts a leaf label (`l = false`) unconditionally, and a
    non-leaf label (`l = true`) exactly when it actually has a (slot-0) child.  This makes the
    leaf-iff clause (3) genuinely constrain (so `RVT` is not trivially satisfied) while allowing an
    internal node. -/
abbrev Farity : Bool → (Fin 1 → Option Bool) → Prop := fun l cl => l = false ∨ cl 0 ≠ none

/-- A leaf tree (`node false []`) and the 2-child root (`node true [leaf, leaf]`). -/
def leafArity : NTree Bool := NTree.node false []
def rootArity : NTree Bool := NTree.node true [leafArity, leafArity]

/-- **[6.c] The 2-child tree SATISFIES `RVT Farity`** (with `n = 1`).  All three clauses hold:
    root label verifies against its slot-0 child, both children are RVT leaves, and the leaf-iff
    clause holds (root is not a leaf and its label does NOT verify with no children). -/
theorem rootArity_RVT : RVT Farity rootArity := by
  unfold RVT
  refine ⟨Or.inr ?_, ?_, ?_⟩
  · -- root.childLabel 0 = some false ≠ none
    decide
  · -- both children are RVT leaves
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact rvt_leaf_b9 (Or.inl rfl)
    · exact rvt_leaf_b9 (Or.inl rfl)
  · -- leaf-iff: both sides FALSE (root has children; Farity true (all none) is false)
    constructor
    · intro h
      exact absurd h (by simp [NTree.isLeaf, rootArity, leafArity])
    · rintro (h | h)
      · exact absurd h (by decide)
      · exact absurd h (by decide)

/-- **[6.d] …but the same tree VIOLATES `ProperArity 1`** — its root has 2 children `> 1`. -/
theorem rootArity_not_ProperArity : ¬ ProperArity 1 rootArity := by
  intro h
  exact absurd (h rootArity (InTree.here rootArity)) (by decide)

/-- **[6.e] KEY DELTA (def⚠, crisp): the concrete tree witnesses `{t // RVT F t} ⊋
    {t // RVT F t ∧ ProperArity n t}`** — `RVT Farity` alone is STRICTLY LARGER than the paper's
    `L_RVT^{Farity,1}`. -/
theorem rvt_strictly_larger_than_properArity :
    RVT Farity rootArity ∧ ¬ ProperArity 1 rootArity :=
  ⟨rootArity_RVT, rootArity_not_ProperArity⟩

/-- **[6.f] `ProperArity` cited**, and
    `fanout_eq_children_length_of_properArity` (the bridge that makes `ProperArity` the faithful
    `L_SLT^n` supplement). -/
noncomputable def properArity_cite := @Nock.Walk.ProperArity
noncomputable def fanout_eq_children_length_of_properArity_cite :=
  @Nock.Walk.fanout_eq_children_length_of_properArity

/-- **[6.doc]** -/
def RVT_doc : String :=
  "Def:RVT (main.tex:683) → Nock.Walk.RVT (Walk.lean:131) + Nock.Walk.ProperArity (Walk.lean:1104). " ++
  "RVT F (node l ch) ⟺ (1) F l childLabel ∧ (2) ∀ s∈ch, RVT F s ∧ (3) isLeaf ↔ F l (fun _=>none) " ++
  "(rvt_node_faithful). CRUCIALLY RVT does NOT bound #children (clause 1 constrains only slots " ++
  "0..n-1; clause 2 recurses into ALL children). NON-VACUITY: fresh rvt_leaf; concrete Nock RVT " ++
  "languages inhabited via Fcomp_nonvacuous/Fmem_nonvacuous (compRVT_inhabited_b9/memRVT_inhabited_b9). " ++
  "KEY DELTA (def⚠) CONFIRMED: rootArity = node true [leaf,leaf] with Farity, n=1, SATISFIES " ++
  "RVT (rootArity_RVT) but VIOLATES ProperArity 1 (rootArity_not_ProperArity) — so {t//RVT F t} ⊋ " ++
  "{t//RVT F t ∧ ProperArity n t} (rvt_strictly_larger_than_properArity), i.e. RVT alone is " ++
  "STRICTLY LARGER than the paper's L_RVT^{F,n}. ProperArity supplies the missing #children ≤ n; " ++
  "the faithful language is RVT ∧ ProperArity (Walk.lean:1096-1100; " ++
  "fanout_eq_children_length_of_properArity). Documented completeness/scoping, NOT unsoundness. " ++
  "Verdict: def⚠. Disposition: PASSED."

end Def_RVT


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch9_drift_summary : String :=
  "BATCH 9 LDSE/MSE & EQUIVALENCE DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Lem:ldse_mse         — PASSED (ldse_mse + mse_ldse_general; reflexive ZMod 5 witness; " ++
     "general n₁≠n₂ = benign strengthening, ldse_mse is its diagonal)\n" ++
  "2. Lem:mse_ldse_equiv   — PASSED (equation-level MSEcond ↔ LDSEcond; reflexive ZMod 5 witness; " ++
     "language-level ≡ assembled downstream via IO.LSE/IO.mio_ldse)\n" ++
  "3. lem_mio_ldse         — PASSED ⚠ CENSUS #6: LmIO bidirectional membership repair " ++
     "(paper one-directional cond-3 makes lemma FALSE, witness [x,x]/[x,y]); non-vacuous over " ++
     "ZMod 5; repair load-bearing (LmIO_iff toFinset)\n" ++
  "4. Def:MEF              — PASSED (genuine structure A/VD/T + LinearOrder Tord; toyMEF inhabits)\n" ++
  "5. Def:MES              — STRUCTURE PASSED ⚠ INSTANCE CARRIES hcorrect: real biconditional " ++
     "`correct` (toyMES discharges it); nock_MES CARRIES hcorrect (= hcorrect verbatim), " ++
     "undischargeable from §5 (shape mismatch + no concrete LangVM). Connective gap, disclosed.\n" ++
  "6. Def:RVT              — PASSED ⚠ def⚠: RVT omits #children ≤ n; rootArity satisfies RVT but " ++
     "violates ProperArity 1 ⇒ {t//RVT} ⊋ {t//RVT ∧ ProperArity}; faithful language = RVT ∧ " ++
     "ProperArity\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. Documented deltas CONFIRMED (not re-flagged as new drift):\n" ++
  "• CENSUS #6 (LOW): lem_mio_ldse LmIO bidirectional repair (paper one-directional cond-3 false " ++
     "as written). Already in Batch 5 IO.\n" ++
  "• Def:MES: nock_MES carries hcorrect (not discharged from §5 capstone; shape mismatch " ++
     "deterministic-↔ vs probabilistic-bound + no concrete LangVM). Connective gap, disclosed — " ++
     "NOT vacuity of the definition, NOT a closed 'NockVM is MES'.\n" ++
  "• Def:RVT (def⚠): RVT omits arity bound #children ≤ n; ProperArity supplies it; faithful " ++
     "language is RVT ∧ ProperArity. Completeness/scoping, NOT unsoundness.\n" ++
  "• Lem:mse_ldse_equiv: Lean proves equation-level MSEcond ↔ LDSEcond; language-level ≡ " ++
     "assembled downstream.\n" ++
  "• Lem:ldse_mse: general form allows n₁≠n₂ (benign strengthening).\n" ++
  "MES VERDICT: STRUCTURE faithful/substantive (real ↔, toy instance discharges it); INSTANCE " ++
  "carries hcorrect (disclosed connective gap).\n" ++
  "RVT VERDICT: faithful as-far-as-it-goes; arity gap real and confirmed (RVT ⊋ RVT ∧ ProperArity); " ++
  "def⚠ completeness, NOT unsoundness.\n" ++
  "AXIOM HYGIENE: all witnesses over ZMod 5 (Fact prime by norm_num) / ℚ / Unit / Bool; NO " ++
  "goldilocks_prime; no sorry/admit/native_decide/axiom/@[extern]."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SELF-CERTIFICATION: `#print axioms` for every proof-carrying declaration
    (all must be ⊆ {propext, Classical.choice, Quot.sound}; NONE uses goldilocks_prime)
    ══════════════════════════════════════════════════════════════════════════════════════
-/

-- Object 1
#print axioms ldse_mse_cite
#print axioms mse_ldse_general_cite
#print axioms ldse_mse_reflexive_iff
#print axioms ldse_mse_reflexive_sum
#print axioms ldse_mse_is_general_diagonal
-- Object 2
#print axioms mse_ldse_equiv_cite
#print axioms mse_ldse_equiv_MSEcond_reflexive
#print axioms mse_ldse_equiv_LDSEcond_reflexive
-- Object 3
#print axioms mio_ldse_cite
#print axioms LmIO_iff_cite
#print axioms mio_LmIO
#print axioms mio_LumLDSE
#print axioms census6_toFinset_differs
-- Object 4
#print axioms MEF_cite
#print axioms toyMEF
#print axioms toyMEF_Rec
#print axioms toyMEF_Seq
#print axioms toyMEF_A
#print axioms toyMEF_T
#print axioms toyMEF_Tord
-- Object 5
#print axioms MES_cite
#print axioms toyMES_LmIO
#print axioms toyMES
#print axioms toyMES_correct_is_iff
#print axioms nock_MES_cite
#print axioms nock_MES_correct_is_hcorrect
-- Object 6
#print axioms rvt_node_faithful
#print axioms rvt_Fcon_shape
#print axioms rvt_leaf_b9
#print axioms compRVT_inhabited_b9
#print axioms memRVT_inhabited_b9
#print axioms rootArity_RVT
#print axioms rootArity_not_ProperArity
#print axioms rvt_strictly_larger_than_properArity
#print axioms properArity_cite
#print axioms fanout_eq_children_length_of_properArity_cite

end Nock.RedTeam
