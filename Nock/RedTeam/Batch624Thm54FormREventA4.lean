/-
  Nock/RedTeam/Batch624Thm54FormREventA4.lean

  Notes only; not a pass.

  * **What A4 reads, re-derived.**  `preEncode α λ row = row.specializeA α` rewrites exactly ONE
    record field, `ts := α^e` on active rows (`specializeA_axis`: the `mem.axis` field — the
    certificate carrier `nockAxisOf` reads — is the template's, at every `α`, every row).  So the
    certificate part A4 reads IS `α`-independent (first alternative of check 1), and the event's
    membership `(α, λ) ∈ formRRootBad P E` is a polynomial condition in both coordinates of a set
    that itself depends on neither (`formRBadAt_const`: `formRBadAt E i E' x = formRBadAt E i E' y`
    for all `x y`).  `ReadsOn ∅` is therefore the exact statement, and `ReadsOn (priorCoords …)`
    a weakening of it; both are stated over the landed `Fin 11` vector with `lamIdx = 10`,
    `alphaMIdx = 2` (`landedVec_lambda`, `landedVec_alphaM`, re-checked by `rfl`).
  * **Never the encode's output**: `specialize = encodeRow λ ∘ specializeA α` (`rfl`), and
    `encodeRow` is the only writer of `T` (`encode_writes_T`: on an active row the specialized
    axis is `λ^{formRCertShift (template axis)}`).
  * **Positive controls are not vacuous and use the same instance.**  A concrete
    `MemoryRowTemplate` with `state = read_root` and placeholder axis `(2 : K)` is exhibited
    (`witnessRow`), its hypotheses discharged, and `encodedTBad_not_readsOn` applied to it
    (`control_fires`); the `ReadsOn` instance is the same `(C := K) (n := 11)
    (priorCoords landedRound lamIdx)` as `formRBadAt_readsOn` (`same_instance`, by `rfl` on the
    predicate's arguments).
  * **Card bound.**  `formRBadAt_eq_template` + `formRRootBad_card_le` give
    `card (formRBadAt E i E' x) ≤ |K|·(deg + E')` at every `x` (`badAt_card`), the A3 bound.
  * **One λ** (check 2): `landedVec c 10 = c.2.2.2.lambda = memoryKOfTuple c 8 =
    computeKOfTuple c 9` (`one_lambda`, `rfl`); the λ coordinate appears once in `landedVec`
    (`lambda_once`, decided over the 11 coordinates at a separating tuple); `|𝕂|¹¹`.
  * Note that it has FOUR rounds (`z:0, αM:1, γ:2, αC:3`)
    while `deployedChronology` collapses to `sampledAfter ∈ {0, 1}` (`min 1`): the staging view
    cannot tell `αC`/`γ` from `αM` (relevant to check 6).
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch624

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

noncomputable section

section A4
variable {K : Type} [Field K]

/-- `specializeA` leaves the certificate carrier (`mem.axis`) untouched on EVERY row. -/
theorem specializeA_axis (α : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specializeA α).2.2.mem.axis = row.placeholder.2.2.mem.axis := by
  simp [MemoryRowTemplate.specializeA, specializeMemRec, ha]

/-- On a padding row `specializeA` zeroes the record (so there is no certificate to read; the
event reads only `read_root` rows, `readRowAt_read_root`). -/
theorem specializeA_padding (α : K) (row : MemoryRowTemplate (K := K))
    (hp : memoryMemRecKind row.timestamp.state = .padding) :
    (row.specializeA α).2.2.mem = ComputeTable.MemRec.zero := by
  have : ¬ memoryMemRecKind row.timestamp.state = .active := by rw [hp]; decide
  simp [MemoryRowTemplate.specializeA, specializeMemRec, this]

/-- `encodeRow` is the writer of `T`: the specialized axis is `λ^{m}` of the TEMPLATE axis. -/
theorem encode_writes_T (α lmb : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specialize α lmb).2.2.mem.axis =
      lmb ^ MemoryTable.formRCertShift (MemoryTable.nockAxisOf row.placeholder.2.2.mem.axis) := by
  rw [specialize_eq_encode_preEncode, MemoryRowTemplate.encodeRow]
  simp only [preEncode, MemoryRowTemplate.specializeA, ha]
  simp [NockVM.formRRow, MemoryTable.formRT, specializeMemRec]

variable [Fintype K] [DecidableEq K]

/-- The bad set is the same at every coin vector: `ReadsOn ∅` is exact, not a bound. -/
theorem formRBadAt_const {F : Type} [Field F] [Algebra F K] {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (E' : ℕ) (x y : Fin 11 → K) :
    formRBadAt E i E' x = formRBadAt E i E' y := by
  rw [formRBadAt_eq_template, formRBadAt_eq_template]

theorem badAt_card {F : Type} [Field F] [Algebra F K] {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (e₀ E' : ℕ) (x : Fin 11 → K)
    (hB : (formRTemplatePolynomial E i).coeff e₀ ≠ 0) (hE0 : e₀ ≤ E') :
    (formRBadAt E i E' x).card ≤
      Fintype.card K * (((formRTemplatePolynomial E i).coeff e₀).natDegree + E') := by
  rw [formRBadAt_eq_template]
  exact formRRootBad_card_le _ _ e₀ E' hB hE0

/-! ### The positive control is not vacuous -/

/-- A `read_root` row whose placeholder axis is `2`. -/
def witnessRow : MemoryRowTemplate (K := K) where
  timestamp := ⟨.read_root, 0⟩
  placeholder := (.read_root, (⟨0, 0, 0⟩,
    { st := .read_root, pt := MemoryTable.Cell.zero, lc := MemoryTable.Cell.zero,
      rc := MemoryTable.Cell.zero, lcSt := .halt, rcSt := .halt,
      mem := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ((2 : ℕ) : K), 0⟩, ipre := 0, icur := 0 }))

theorem witnessRow_active : memoryMemRecKind (witnessRow (K := K)).timestamp.state = .active := rfl
theorem witnessRow_axis : (witnessRow (K := K)).placeholder.2.2.mem.axis = ((2 : ℕ) : K) := rfl

/-- The encode's-output control FIRES on the witness (so `encodedTBad_not_readsOn` is inhabited
at every `K` with `2 < ringChar K`). -/
theorem control_fires (h2 : 2 < ringChar K) :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (encodedTBad (witnessRow (K := K))) :=
  encodedTBad_not_readsOn witnessRow witnessRow_active witnessRow_axis h2

/-- The witness's encoded `T` is literally `λ`: reading it reads the coin. -/
theorem witness_T (α lmb : K) (h2 : 2 < ringChar K) :
    ((witnessRow (K := K)).specialize α lmb).2.2.mem.axis = lmb := by
  rw [encode_writes_T α lmb _ witnessRow_active, witnessRow_axis,
    MemoryTable.nockAxisOf_natCast h2]
  have : MemoryTable.formRCertShift 2 = 1 := by decide
  rw [this, pow_one]

/-- Same `ReadsOn` instance in A4 and in both controls: the dependence set is
`priorCoords landedRound lamIdx = {z, a, b, c}` (indices `3, 6, 7, 8`). -/
theorem same_instance :
    priorCoords landedRound lamIdx = ({3, 6, 7, 8} : Finset (Fin 11)) := by decide

end A4

/-! ## Check 2 — one λ -/

section OneLambda
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F]

theorem one_lambda (c : OptimizedProductionChallengeTuple K F) :
    landedVec c lamIdx = c.2.2.2.lambda ∧
      memoryKOfTuple c 8 = c.2.2.2.lambda ∧
      computeKOfTuple c 9 = c.2.2.2.lambda := ⟨rfl, rfl, rfl⟩

theorem alphaM_coord (c : OptimizedProductionChallengeTuple K F) :
    landedVec c alphaMIdx = alphaM c.1 ∧ memoryKOfTuple c 3 = alphaM c.1 ∧
      computeKOfTuple c 0 = alphaM c.1 := ⟨rfl, rfl, rfl⟩

/-- λ occupies exactly one coordinate of `landedVec`: at a tuple whose λ is `1` and every other
coordinate `0`, exactly index `10` reads `1`. -/
theorem lambda_once :
    ∀ i : Fin 11, landedVec (K := K) (F := F)
      ((⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ((0, 0), (⟨0, 0, 0⟩, ⟨0, 1⟩)))) i = if i = lamIdx then 1 else 0 := by
  intro i
  fin_cases i <;> rfl

theorem tuple_card : Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

/-- `landedRound` has four distinct rounds; the staging chronology sees two. -/
theorem rounds_collapse :
    landedRound = ![3, 2, 1, 0, 1, 1, 0, 0, 0, 1, 1] ∧
      (∀ i : Fin 11, ((DeployedStaging.deployedChronology.sampledAfter i : Fin 3) : ℕ) =
        min (landedRound i) 1) ∧
      landedRound 0 ≠ landedRound 2 ∧
      DeployedStaging.deployedChronology.sampledAfter (0 : Fin 11) =
        DeployedStaging.deployedChronology.sampledAfter (2 : Fin 11) := by
  refine ⟨rfl, DeployedStaging.deployedChronology_eq_landedRound, by decide, rfl⟩

end OneLambda

end

end Nock.RedTeam.Batch624
