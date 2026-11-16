/-
  Nock/NockVMROM/Thm54/FormRAxisEvent.lean

  Form R axis event at the strategy layer, over the LANDED objects.

  **What is landed and used here (no second λ, no wrapper).**
  * The sampled Form R coin is `ChallengeVector.lam` (`Config.lean`): the template carries no λ,
    `ChallengeVectorTemplate.specialize v α lmb` inserts it, and in the sampled tuple
    `OptimizedProductionChallengeTuple K F` it is `c.2.2.2.lambda`
    (`MemoryChallengeTuple.lambda`), read by the chips at memory `𝕂` slot `8`
    (`memoryKOfTuple c 8`) and compute `𝕂` slot `9` (`computeKOfTuple c 9`); the tuple has
    `|𝕂|¹¹` points (`card_optimizedProductionChallengeTuple`).
  * The memory row encode is `MemoryRowTemplate.specialize α lmb = encodeRow lmb ∘ specializeA α`
    (`SemanticTimestampStrategy.lean`).  `specializeA α` is timestamp-only (the a-bearing row);
    `encodeRow lmb` replaces an active row's axis by `T = λ^m` and sets `C' = Cpoly(λ)`, both from
    the certificate of `nockAxisOf` of the a-bearing axis (`NockVM.formRRow` / `formRCprime`,
    `MemoryTable.formRCertShift` / `formRCertBit` / `nockAxisOf`).
  * The certificate of a template row is therefore the template's own data: `m = formRCertShift a`,
    `c_{j+1} = formRCertBit a j`, `a = nockAxisOf (placeholder axis)`. The 10-07 wrapper `FormRCertificate` (and its
    premise "the template has no `(m_e, c_e)` field") is deleted: no field is missing.
  * `FormRJointCoins` / `formRJointChronology` (a new strategy-layer λ coordinate) are deleted.
    One round map remains, `landedRound`, over the eleven coordinates of the landed tuple: it is
    needed because no landed Lean chronology covers that tuple (`jointChronology` is `Fin 4`,
    `nockChronology` is the eight 102-column chip coins, neither has λ).

  Positive control
  (`encodedTBad_not_readsOn`): the same row read through the encode's OUTPUT (`T = λ^m`) fails the
  check.

  -- the paper
-/
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.RoundFibredSoundness
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.FormRTemplatePolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators Classical Polynomial

namespace Nock.NockVMROM.Thm54.FormRAxisEvent

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open SemanticTimestampStrategy
open OptimizedStrictPackage
open Nock.RedTeam.Batch554 (bitsOf rpaths vpaths Cpoly bit)
open Nock.RedTeam.Batch575
open Polynomial

/-! ## A1. The template's own Form R certificate -/

section Certificate

variable {K : Type} [Field K]

/-! `formRN`, `formRN_sub_one`, `templateRowCertAxis`, `readRowAt`, `readRowAt_read_root`,
`certAxisVia`, `templateCertAxis`, `certShiftOf`, `certBitsOf`, `formRPolyOfCert` and
`formRTemplatePolynomial` (A1) moved verbatim, same names, to
`Nock/NockVMROM/Thm54/FormRTemplatePolynomial.lean`: below
`ProductionP8Containment`, so `workload`'s module can name the template polynomial. -/

/-- The pre-encode stage of the landed memory encode: the a-bearing row `encodeRow lmb` consumes.
`lmb` is accepted and ignored, so that the read set is visibly stated against the pair. -/
def preEncode (α _lmb : K) (row : MemoryRowTemplate (K := K)) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  row.specializeA α

/-- `MemoryRowTemplate.specialize = encodeRow lmb ∘ preEncode α lmb` (the landed definition). -/
theorem specialize_eq_encode_preEncode (α lmb : K) (row : MemoryRowTemplate (K := K)) :
    row.specialize α lmb = MemoryRowTemplate.encodeRow lmb (preEncode α lmb row) := rfl

/-- The certificate axis of one row, read at the pre-encode stage. -/
noncomputable def certAxisAt (α lmb : K) (row : MemoryRowTemplate (K := K)) : ℕ :=
  MemoryTable.nockAxisOf (preEncode α lmb row).2.2.mem.axis

/-- On an active row the pre-encode certificate is the template's: `specializeA` moves only
`ts`. -/
theorem certAxisAt_active (α lmb : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    certAxisAt α lmb row = templateRowCertAxis row := by
  simp [certAxisAt, preEncode, templateRowCertAxis, MemoryRowTemplate.specializeA,
    specializeMemRec, ha]

/-- Reading through the landed pre-encode stage gives the template certificate, at every
`(α, λ)`: read rows are active. -/
theorem certAxisVia_preEncode (α lmb : K) (t : NTree (MemoryRowTemplate (K := K))) :
    certAxisVia (certAxisAt α lmb) t = templateCertAxis t := by
  funext e
  unfold templateCertAxis certAxisVia
  cases h : readRowAt t e with
  | none => rfl
  | some r =>
      have hr := (readRowAt_read_root h).1
      have ha : memoryMemRecKind r.timestamp.state = .active := by
        rw [hr]; rfl
      simp [certAxisAt_active α lmb r ha]


def CertInRange (K : Type) [Field K] (A : ℕ → ℕ) : Prop :=
  ∀ e, certShiftOf A e ≤ formRN K - 1

/-- A certificate below the characteristic is in range. -/
theorem certInRange_of_lt (A : ℕ → ℕ) (h : ∀ e, A e < ringChar K) : CertInRange K A := by
  intro e
  exact Nat.sub_le_sub_right (Nat.size_le_size (Nat.le_of_lt (h e))) 1

/-- The template polynomial's read coefficient at `λ` is the `T` the landed encode writes. -/
theorem encode_T_eq_Tpoly_eval (α lmb : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specialize α lmb).2.2.mem.axis =
      (Tpoly (K := K) (MemoryTable.formRCertShift (templateRowCertAxis row))).eval lmb := by
  rw [MemoryRowTemplate.specialize_mem_active row α lmb ha]
  simp [NockVM.formRRow, MemoryTable.formRT, Tpoly, Y, templateRowCertAxis, specializeMemRec]

private theorem finset_sum_range_eq_list (n : ℕ) (f : ℕ → K) :
    ∑ j ∈ Finset.range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
      simp

/-- The template polynomial's `C'` factor at `λ` is the `C'` the landed encode writes. -/
theorem encode_Cprime_eq_C'poly_eval (α lmb : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specialize α lmb).2.2.cprime =
      (C'poly (K := K) (formRN K)
        (certBitsOf (fun _ => templateRowCertAxis row) 0)).eval lmb := by
  rw [MemoryRowTemplate.specialize_cprime_active row α lmb ha]
  simp only [NockVM.formRCprime, MemoryTable.formRC, C'poly, Cpoly, formRN_sub_one,
    specializeMemRec, if_true, certBitsOf]
  rw [eval_add, eval_pow, eval_X, eval_finsetSum, finset_sum_range_eq_list]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [bit, templateRowCertAxis, Nat.add_sub_cancel]
  split <;> simp

end Certificate

/-! ## A2. Path equation, not `ReadVerifyNested` -/

section PathEquation

variable {K : Type} [Field K]

/-- The Form R root identity of a certificate and a tree. -/
def FormRRootIdentity (A : ℕ → ℕ) (t : MTree K) : Prop :=
  formRPolyOfCert A t = 0

/-- `ExactMemoryAxisValidity`-shaped conclusion: unique paired exponents, padding, and
`verify_path = read_path ++ bitsOf m c`.  No `Nested` conjunct. -/
def FormRPathValid (A : ℕ → ℕ) (t : MTree K) : Prop :=
  (∀ e, readCount e t = verifyCount e t) ∧
    ∀ e, Paired e t →
      Padding (formRN K) (certShiftOf A e) (certBitsOf A e) ∧
        ∃ r, rpaths e t = [r] ∧ vpaths e t = [r ++ bitsOf (certShiftOf A e) (certBitsOf A e)]

/-- **A2.**  The root identity is the path equation (`Batch575.formR_counts_zero_iff`). -/
theorem formR_identity_iff_path (A : ℕ → ℕ) (t : MTree K)
    (hU : UniqueExponents t) (hA : CertInRange K A) :
    FormRRootIdentity A t ↔ FormRPathValid A t :=
  formR_counts_zero_iff (formRN K) (certShiftOf A) (certBitsOf A) t hU hA

/-- A2 at a template root, with its own certificate. -/
theorem formRTemplate_identity_iff_path
    {F : Type} [Field F] [Algebra F K]
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem)
    (hU : UniqueExponents (templateAxisTree (templateMemoryTreeAt E i)))
    (hA : CertInRange K (templateCertAxis (templateMemoryTreeAt E i))) :
    formRTemplatePolynomial E i = 0 ↔
      FormRPathValid (templateCertAxis (templateMemoryTreeAt E i))
        (templateAxisTree (templateMemoryTreeAt E i)) :=
  formR_identity_iff_path _ _ hU hA

/-- Replaces `alphaFreeRootStructureCheck`'s `ancestry` conjunct. -/
def formRRootStructureCheck (A : ℕ → ℕ) (t : MTree K) : Prop :=
  UniqueExponents t ∧ FormRRootIdentity A t

end PathEquation

/-! ## A3. The `(α, λ)` root set -/

section RootSet

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Envelope `F_E(α, lmb) = Σ_{k≤E} α^k B_k(lmb)` of a Form R polynomial. -/
noncomputable def formREnvelope (P : Polynomial (Polynomial K)) (E : ℕ) (α lmb : K) : K :=
  Nock.RedTeam.Batch556.F (Finset.range (E + 1)) id (fun e => P.coeff e) α lmb

/-- Root set of the envelope on pairs `(α, λ)`. -/
noncomputable def formRRootBad (P : Polynomial (Polynomial K)) (E : ℕ) : Finset (K × K) :=
  Finset.univ.filter fun p : K × K => formREnvelope P E p.1 p.2 = 0

/-- **A3.**  `card ≤ |K| · (deg_Y + E)` (`Batch575.formR_event_card`). -/
theorem formRRootBad_card_le (A : ℕ → ℕ) (t : MTree K)
    (e₀ E : ℕ) (hB : (formRPolyOfCert A t).coeff e₀ ≠ 0) (hE0 : e₀ ≤ E) :
    (formRRootBad (formRPolyOfCert A t) E).card
      ≤ Fintype.card K * (((formRPolyOfCert A t).coeff e₀).natDegree + E) := by
  have h := formR_event_card (K := K) (formRN K) (certShiftOf A) (certBitsOf A) t e₀ hB E hE0
  refine le_trans (le_of_eq ?_) h
  unfold formRRootBad
  congr 1

/-- Numerator is `pwAccountingWork'`-shaped (`Batch575.formR_work_vs_majorant`). -/
theorem formR_event_numerator_le_work
    (n N M dQ E : ℕ)
    (hd : dQ ≤ 2 * (n - 1) + M) (hE : E ≤ 3 * N + 3) :
    dQ + E ≤ Nock.RedTeam.Batch557.pwAccountingWork' n N M :=
  (formR_work_vs_majorant n N M dQ E hd hE).1

end RootSet

/-! ## The landed tuple and its round map -/

section Landed

variable {K F : Type} [Fintype K] [Fintype F]

/-- The eleven coordinates of the landed tuple, in its own product order:
`(αC, γ, αM, z | IO γ, IO pole | a, b, c | interPole, λ)`. -/
def landedVec (c : OptimizedProductionChallengeTuple K F) : Fin 11 → K :=
  ![alphaC c.1, gamma c.1, alphaM c.1, nprSeed c.1, c.2.1.1, c.2.1.2,
    c.2.2.1.eqA, c.2.2.1.eqB, c.2.2.1.eqC, c.2.2.2.interPole, c.2.2.2.lambda]

/-- Index of `αM` (the timestamp `α` of the memory walk / `ChallengeVector.α`). -/
def alphaMIdx : Fin 11 := 2
/-- Index of `z`. -/
def seedIdx : Fin 11 := 3
/-- Index of `λ` (`MemoryChallengeTuple.lambda` = `ChallengeVector.lam`). -/
def lamIdx : Fin 11 := 10

/-- Round map of the landed tuple.  The four joint coins are `jointChronology` verbatim; the
equality coins `(a, b, c)` are sampled with `z` (`ComputeStagedTable.nockSampledAfter` slots
`2, 3, 4`); `λ` is in `αM`'s round; the IO pair and `interPole` have no landed round and are placed
in `αM`'s round, which only REMOVES them from every prior set below (a stronger `ReadsOn`). -/
def landedRound : Fin 11 → ℕ := ![3, 2, 1, 0, 1, 1, 0, 0, 0, 1, 1]

theorem landedRound_joint (i : Fin 4) :
    landedRound ⟨i, by omega⟩ = jointChronology i := by
  fin_cases i <;> rfl

theorem lambda_round_eq_alphaM : landedRound lamIdx = landedRound alphaMIdx := rfl

/-- The coordinates sampled strictly before the `(α, λ)` round: `z` and `(a, b, c)`. -/
theorem lambda_prior :
    priorCoords landedRound lamIdx = ({3, 6, 7, 8} : Finset (Fin 11)) := by
  decide

theorem alphaM_prior :
    priorCoords landedRound alphaMIdx = ({3, 6, 7, 8} : Finset (Fin 11)) := by
  decide

theorem lam_not_prior : lamIdx ∉ priorCoords landedRound lamIdx :=
  not_mem_priorCoords _ _

theorem alphaM_not_prior : alphaMIdx ∉ priorCoords landedRound lamIdx := by
  rw [lambda_prior]; decide

/-- `λ` of the landed tuple is the coordinate both chips read. -/
theorem landedVec_lambda {F' K' : Type} [Field F'] [Field K'] [Algebra F' K']
    [Fintype K'] [Fintype F'] [DecidableEq K'] [FiniteDimensional F' K']
    (c : OptimizedProductionChallengeTuple K' F') :
    landedVec c lamIdx = c.2.2.2.lambda ∧
      DeployedChipFamily.memoryKOfTuple c 8 = c.2.2.2.lambda ∧
      DeployedChipFamily.computeKOfTuple c 9 = c.2.2.2.lambda :=
  ⟨rfl, rfl, rfl⟩

theorem landedVec_alphaM (c : OptimizedProductionChallengeTuple K F) :
    landedVec c alphaMIdx = alphaM c.1 := rfl

/-- The template carries no λ; the sampled one enters at `specialize` (`ChallengeVector.lam`). -/
theorem template_lam_is_sampled {F' K' : Type} [Field F'] [Field K'] [Algebra F' K']
    (T : ExactConfigTemplate F' K') (α lmb : K') :
    (T.specialize α lmb).challenges.lam = lmb := rfl

theorem landed_card (K' F' : Type) [Fintype K'] [Fintype F'] :
    Fintype.card (OptimizedProductionChallengeTuple K' F') = Fintype.card K' ^ 11 :=
  card_optimizedProductionChallengeTuple K' F'

end Landed

/-! ## A4. The event's read set, against `encodeRow lmb ∘ specializeA α` -/

section ReadSet

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- The event's bad set at a coin vector `x`: the `(α, λ)` roots of the template polynomial whose
certificate is read through the landed pre-encode stage at the vector's own `(α, λ)`.  It reads
the template's shape and exponents (`templateAxisTree`) and the certificate of
`preEncode (x αM) (x λ)` (the argument of `encodeRow (x λ)`). -/
noncomputable def formRBadAt {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (Edeg : ℕ) (x : Fin 11 → K) : Finset (K × K) :=
  formRRootBad
    (formRPolyOfCert
      (certAxisVia (certAxisAt (x alphaMIdx) (x lamIdx)) (templateMemoryTreeAt E i))
      (templateAxisTree (templateMemoryTreeAt E i)))
    Edeg

theorem formRBadAt_eq_template {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (Edeg : ℕ) (x : Fin 11 → K) :
    formRBadAt E i Edeg x = formRRootBad (formRTemplatePolynomial E i) Edeg := by
  simp only [formRBadAt, certAxisVia_preEncode, formRTemplatePolynomial]

/-- **A4.**  The bad set reads only coordinates sampled before the `(α, λ)` round. -/
theorem formRBadAt_readsOn {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (Edeg : ℕ) :
    ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (formRBadAt E i Edeg) := by
  intro x y _
  rw [formRBadAt_eq_template, formRBadAt_eq_template]

/-- A4, sharper: the set reads no coin at all (it is a template quantity). -/
theorem formRBadAt_readsOn_empty {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (Edeg : ℕ) :
    ReadsOn (C := K) (n := 11) (∅ : Finset (Fin 11)) (formRBadAt E i Edeg) := by
  intro x y _
  rw [formRBadAt_eq_template, formRBadAt_eq_template]

/-- **Positive control.**  The same row read through the encode's OUTPUT (`T = λ^m`, the
executed row's axis field). -/
noncomputable def encodedTBad (row : MemoryRowTemplate (K := K)) (x : Fin 11 → K) : Finset K :=
  {(row.specialize (x alphaMIdx) (x lamIdx)).2.2.mem.axis}

/-- **Positive control, compiled.**  An active row whose certificate axis is `2` (`m = 1`, so
`T = λ`): the set reading its encoded `T` FAILS the A4 check. -/
theorem encodedTBad_not_readsOn (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active)
    (hax : row.placeholder.2.2.mem.axis = ((2 : ℕ) : K)) (h2 : 2 < ringChar K) :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (encodedTBad row) := by
  intro hR
  let x : Fin 11 → K := fun _ => 0
  let y : Fin 11 → K := Function.update x lamIdx 1
  have hxy : ∀ j ∈ priorCoords landedRound lamIdx, x j = y j := by
    intro j hj
    have hne : j ≠ lamIdx := fun h => lam_not_prior (h ▸ hj)
    simp [y, Function.update_of_ne hne]
  have hT : ∀ α lmb : K, (row.specialize α lmb).2.2.mem.axis = lmb := by
    intro α lmb
    rw [encode_T_eq_Tpoly_eval α lmb row ha]
    have hcert : templateRowCertAxis row = 2 := by
      rw [templateRowCertAxis, hax]
      exact MemoryTable.nockAxisOf_natCast h2
    rw [hcert]
    have hs : Nat.size 2 = 2 := by decide
    simp [Tpoly, Y, MemoryTable.formRCertShift, hs]
  have h := hR x y hxy
  simp only [encodedTBad, hT] at h
  have hx : x lamIdx = 0 := rfl
  have hy : y lamIdx = 1 := by simp [y]
  rw [hx, hy] at h
  have : (0 : K) = 1 := Finset.singleton_injective h
  exact zero_ne_one this

/-- Positive control, coordinate form: a set reading the landed `λ` coordinate fails. -/
theorem lambdaBad_not_readsOn :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx)
      (fun x : Fin 11 → K => ({x lamIdx} : Finset K)) := by
  intro hR
  let x : Fin 11 → K := fun _ => 0
  let y : Fin 11 → K := Function.update x lamIdx 1
  have hxy : ∀ j ∈ priorCoords landedRound lamIdx, x j = y j := by
    intro j hj
    have hne : j ≠ lamIdx := fun h => lam_not_prior (h ▸ hj)
    simp [y, Function.update_of_ne hne]
  have h := hR x y hxy
  have : (0 : K) = 1 := by
    simpa [x, y] using Finset.singleton_injective h
  exact zero_ne_one this

end ReadSet

/-! ## The event on the landed tuple -/

section Event

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F]

/-- The lifted event on the landed tuple: `(αM, λ)` in the root set. -/
noncomputable def formRGuardedAxisFailureEvent {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (Edeg : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    (landedVec c alphaMIdx, landedVec c lamIdx) ∈ formRBadAt E i Edeg (landedVec c)

/-- The nine coordinates other than `(αM, λ)`. -/
def restOf (c : OptimizedProductionChallengeTuple K F) :
    (K × K × K) × ((K × K) × (OptimizedComputeCollisionBound.FinalComputeChallengeTuple K × K)) :=
  ((alphaC c.1, gamma c.1, nprSeed c.1), (c.2.1, (c.2.2.1, c.2.2.2.interPole)))

/-- Card of the lifted event: the nine free coordinates times the pair set. -/
theorem formRGuardedAxisFailureEvent_card_le {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (i : Fin T.kMem) (Edeg : ℕ) :
    (formRGuardedAxisFailureEvent E i Edeg).card
      ≤ Fintype.card K ^ 9 * (formRRootBad (formRTemplatePolynomial E i) Edeg).card := by
  set B := formRRootBad (formRTemplatePolynomial E i) Edeg
  let iota : OptimizedProductionChallengeTuple K F →
      ((K × K × K) × ((K × K) × (OptimizedComputeCollisionBound.FinalComputeChallengeTuple K × K)))
        × (K × K) :=
    fun c => (restOf c, (alphaM c.1, c.2.2.2.lambda))
  have hinj : Function.Injective iota := by
    rintro ⟨⟨⟨αc, γ⟩, ⟨αm, z⟩⟩, ⟨io, ⟨eq, ⟨ip, l⟩⟩⟩⟩
      ⟨⟨⟨αc', γ'⟩, ⟨αm', z'⟩⟩, ⟨io', ⟨eq', ⟨ip', l'⟩⟩⟩⟩ h
    simp only [iota, restOf, alphaC, gamma, nprSeed, alphaM, Prod.mk.injEq] at h
    obtain ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
    rfl
  have himg : (formRGuardedAxisFailureEvent E i Edeg).image iota ⊆ Finset.univ ×ˢ B := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    have hc' := (Finset.mem_filter.mp hc).2
    rw [formRBadAt_eq_template] at hc'
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hc'⟩
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ] at hcard
  refine hcard.trans (le_of_eq ?_)
  congr 1
  simp only [Fintype.card_prod, OptimizedStrictPackage.card_finalComputeChallengeTuple]
  ring

end Event

/-! ## The guarded set

`formRGuardedAxisFailureEvent` alone is the zero set of the envelope; on a tree whose Form R
polynomial is `0` (every valid-path tree, A2, and every `halt` root) it is the whole tuple space
.  The approved form guards each tree by "some coefficient at an exponent `≤ E'` is
nonzero" — NOT `P ≠ 0` (`Batch641.pneq_guard_insufficient`).  The guard reads only the template
polynomial `formRTemplatePolynomial E i`. -/

section Guarded

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F]

/-- **The guard** of the approved form: some coefficient at an exponent `≤ E'` is nonzero. -/
def formRGuard (P : Polynomial (Polynomial K)) (E' : ℕ) : Prop :=
  ∃ k ≤ E', P.coeff k ≠ 0

/-- **The guarded per-tree event** (`Batch641.formRGuardedBad`, verbatim shape): the guard reads
only the template polynomial. -/
noncomputable def formRGuardedBad {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (E' : ℕ) : Finset (OptimizedProductionChallengeTuple K F) :=
  if formRGuard (formRTemplatePolynomial E i) E' then formRGuardedAxisFailureEvent E i E' else ∅

/-- The guarded union over one template's trees, `⋃_{i < kMem} formRGuardedBad E i E'`. -/
noncomputable def formRGuardedUnion {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (E' : ℕ) : Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.biUnion fun i : Fin T.kMem => formRGuardedBad E i E'

end Guarded

/-!

`⋃_{i < kMem_z} formRGuardedBad E_z i E'` with `E_z` the committed post-seed template
`committedTemplate T.verifier z hz = (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate`
at the tuple's own seed `z = nprSeed c.1`, and `E' = 3N + 3` (`N = |computeSkeletonRows|`), on the
production tuple (λ at `c.2.2.2.lambda`).  It enters `OptimizedHostileProductionFailureEvent` as its
last parameter and is instantiated in the pinned `optimizedFailureEvent`.  The per-seed union is
written out (`biUnion` of `formRGuardedBad`, no helper name) so the watched `formRGuardedBad` is
what the closure sees one ring further out. -/

section LambdaEvent

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [Fintype F] [CharP K (ringChar K)]

/-- **The Form R λ-event** of a production strategy, on the landed tuple. -/
noncomputable def formRLambdaEvent (T : ProductionP8Containment.ProductionStrategy F K) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    ∃ hz : nprSeed c.1 ≠ 0,
      c ∈ (Finset.univ : Finset
          (Fin (T.verifier.raw.timestamp.afterSeed ⟨nprSeed c.1, hz⟩).configTemplate.kMem)).biUnion
        fun i => formRGuardedBad
          (ProductionAxisStructureVerifier.committedTemplate T.verifier (nprSeed c.1) hz) i
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3)

/-- The tuple's eight coordinates other than `(z, αM, λ)`. -/
def restOf8 (c : OptimizedProductionChallengeTuple K F) :
    (K × K) × ((K × K) × (OptimizedComputeCollisionBound.FinalComputeChallengeTuple K × K)) :=
  ((alphaC c.1, gamma c.1), (c.2.1, (c.2.2.1, c.2.2.2.interPole)))

/-- **One seed's slice.**  At a fixed `z`, the tuples whose `(αM, λ)` lies in `B` number at most
`|𝕂|⁸ · |B|`. -/
theorem seedSlice_card_le (z : K) (B : Finset (K × K)) :
    (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ B).card ≤
      Fintype.card K ^ 8 * B.card := by
  let f : OptimizedProductionChallengeTuple K F →
      ((K × K) × ((K × K) × (OptimizedComputeCollisionBound.FinalComputeChallengeTuple K × K)))
        × (K × K) :=
    fun c => (restOf8 c, (alphaM c.1, c.2.2.2.lambda))
  have hmaps : ∀ c ∈ (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ B),
      f c ∈ (Finset.univ ×ˢ B) := by
    intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hc'.2⟩
  have hinj : Set.InjOn f (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ B) := by
    rintro ⟨⟨⟨αc, γ⟩, ⟨αm, z₁⟩⟩, ⟨io, ⟨eq, ⟨ip, l⟩⟩⟩⟩ h₁
      ⟨⟨⟨αc', γ'⟩, ⟨αm', z₂⟩⟩, ⟨io', ⟨eq', ⟨ip', l'⟩⟩⟩⟩ h₂ h
    have hz₁ := (Finset.mem_filter.mp h₁).2.1
    have hz₂ := (Finset.mem_filter.mp h₂).2.1
    simp only [nprSeed] at hz₁ hz₂
    simp only [f, restOf8, alphaC, gamma, alphaM, Prod.mk.injEq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
    subst hz₁; subst hz₂
    rfl
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_univ] at hcard
  refine hcard.trans (le_of_eq ?_)
  congr 1
  simp only [Fintype.card_prod, OptimizedStrictPackage.card_finalComputeChallengeTuple]
  ring

/-- **The λ-event's card is priced by `fixedFormRWorkload`:** `≤ |𝕂|¹⁰ · fixedFormRWorkload T`
(`|𝕂|` seeds, `|𝕂|⁸` free coordinates per seed, and per seed the guarded root sets, each
`≤ |𝕂| · (deg_Y B_{e₀} + E')` with `e₀` the guard's witness, `formRRootBad_card_le`). -/
theorem formRLambdaEvent_card_le (T : ProductionP8Containment.ProductionStrategy F K) :
    (formRLambdaEvent T).card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.fixedFormRWorkload T := by
  set E' := 3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3 with hE'
  -- the per-seed pair set
  let Bz : K → Finset (K × K) := fun z =>
    if hz : z ≠ 0 then
      (Finset.univ : Finset
          (Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem)).biUnion
        fun i =>
          if formRGuard (formRTemplatePolynomial
              (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i) E'
          then formRRootBad (formRTemplatePolynomial
              (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i) E'
          else ∅
    else ∅
  have hsub : formRLambdaEvent T ⊆ (Finset.univ : Finset K).biUnion fun z =>
      Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ Bz z := by
    intro c hc
    obtain ⟨hz, hmem⟩ := (Finset.mem_filter.mp hc).2
    refine Finset.mem_biUnion.mpr ⟨nprSeed c.1, Finset.mem_univ _, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
    simp only [Bz, dif_pos hz]
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    unfold formRGuardedBad at hi
    split_ifs at hi with hg
    · rw [if_pos hg]
      have hi' := (Finset.mem_filter.mp hi).2
      rw [formRBadAt_eq_template] at hi'
      exact hi'
    · simp at hi
  have hBz : ∀ z, (Bz z).card ≤ Fintype.card K * ProductionP8Containment.fixedFormRWorkload T := by
    intro z
    by_cases hz : z ≠ 0
    · simp only [Bz, dif_pos hz]
      refine Finset.card_biUnion_le.trans ?_
      refine le_trans ?_ (Nat.mul_le_mul_left _
        (ProductionP8Containment.formRSeedWorkload_le_fixedFormRWorkload T z hz))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hg
      · obtain ⟨e₀, he₀, hB⟩ := hg
        have h1 := formRRootBad_card_le
          (templateCertAxis (templateMemoryTreeAt
            (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i))
          (templateAxisTree (templateMemoryTreeAt
            (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i)) e₀ E' hB he₀
        refine h1.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ _))
        exact Finset.le_sup (f := fun k => ((formRTemplatePolynomial
            (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i).coeff k).natDegree)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le he₀))
      · simp
    · simp only [Bz, dif_neg hz, Finset.card_empty]
      exact Nat.zero_le _
  calc (formRLambdaEvent T).card
      ≤ ((Finset.univ : Finset K).biUnion fun z =>
          Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
            nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ Bz z).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ z : K, (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
            nprSeed c.1 = z ∧ (alphaM c.1, c.2.2.2.lambda) ∈ Bz z).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _z : K, Fintype.card K ^ 8 *
          (Fintype.card K * ProductionP8Containment.fixedFormRWorkload T) := by
        apply Finset.sum_le_sum
        intro z _
        exact (seedSlice_card_le z (Bz z)).trans (Nat.mul_le_mul_left _ (hBz z))
    _ = Fintype.card K ^ 10 * ProductionP8Containment.fixedFormRWorkload T := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

end LambdaEvent

end Nock.NockVMROM.Thm54.FormRAxisEvent

#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formR_identity_iff_path
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRTemplate_identity_iff_path
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRBadAt_readsOn
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.encodedTBad_not_readsOn
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.lambdaBad_not_readsOn
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRRootBad_card_le
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRGuardedAxisFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.seedSlice_card_le
#print axioms Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent_card_le
