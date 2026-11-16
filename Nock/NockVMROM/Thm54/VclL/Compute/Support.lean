import Nock.NockVMROM.Thm54.Unhosted309Chip

/-!
# V4 (b), part 1: the column-support facts for the gates `computeChipVCL` keeps

**  Additive.**  `computeChipVCL` drops the base columns `202..301` (Form R: the
certificate bits `202..295` and the `𝕂` helpers `296..301`) and shifts `S` (`302`) and the walk columns
(`303..308`) down by `100`.  That is sound as a *reindex-and-filter* of `allGates309` exactly when
every kept gate reads no column of `[202, 302)`.  This module proves it, generically in `F`, `K` and
the coordinate basis: the typed leaves `certBase` / `certExt` are the only readers of Form R, and
the support of a compiled expression is the support of its typed source (`mulVec` / `powVec` add
only constants).

Kept groups: `finalBaseTransitionGates`, `correctedCore309`, `correctedAux309`,
`compileList309 endpoint2_309`, `compileList309 endpoint4_309`, `finalEndpointEqualityChecks`.
Dropped groups (they ARE the readers): `formRCertificateGates` (97 gates), `formRLamPins`.
The fourth carrier gate pair `computeExpGates` is replaced by the arity-1 serial (`Gates.lean`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Framework Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. Trace-column support -/

/-- The trace columns (current and next row) an expression reads. -/
def colsOf {F : Type*} : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .traceCur i => [i]
  | .var .traceNext i => [i]
  | .var _ _ => []
  | .add a b => colsOf a ++ colsOf b
  | .sub a b => colsOf a ++ colsOf b
  | .mul a b => colsOf a ++ colsOf b
  | .neg a => colsOf a
  | .pow a _ => colsOf a

def ColsIn {F : Type*} (P : ℕ → Prop) (e : CoeffExpr F) : Prop := ∀ i ∈ colsOf e, P i

/-- A column outside Form R's `[202, 302)`. -/
def NoFormR (i : ℕ) : Prop := i < 202 ∨ 302 ≤ i

section lemmas
variable {F : Type*} {P : ℕ → Prop}

theorem colsIn_const (c : F) : ColsIn P (.const c) := by simp [ColsIn, colsOf]
theorem colsIn_var (k : VarKind) (i : ℕ) (h : P i) : ColsIn P (CoeffExpr.var (F := F) k i) := by
  cases k <;> simp_all [ColsIn, colsOf]
theorem colsIn_add {a b : CoeffExpr F} (ha : ColsIn P a) (hb : ColsIn P b) : ColsIn P (.add a b) := by
  intro i hi; simp only [colsOf, List.mem_append] at hi; exact hi.elim (ha i) (hb i)
theorem colsIn_sub {a b : CoeffExpr F} (ha : ColsIn P a) (hb : ColsIn P b) : ColsIn P (.sub a b) := by
  intro i hi; simp only [colsOf, List.mem_append] at hi; exact hi.elim (ha i) (hb i)
theorem colsIn_mul {a b : CoeffExpr F} (ha : ColsIn P a) (hb : ColsIn P b) : ColsIn P (.mul a b) := by
  intro i hi; simp only [colsOf, List.mem_append] at hi; exact hi.elim (ha i) (hb i)
theorem colsIn_neg {a : CoeffExpr F} (ha : ColsIn P a) : ColsIn P (.neg a) := ha
theorem colsIn_pow {a : CoeffExpr F} (n : ℕ) (ha : ColsIn P a) : ColsIn P (.pow a n) := ha

theorem colsIn_sumList [Field F] {ι : Type*} (l : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ l, ColsIn P (f i)) : ColsIn P (CoeffExpr.sumList l f) := by
  induction l with
  | nil => exact colsIn_const _
  | cons a l ih =>
      exact colsIn_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

end lemmas

section compile
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {P : ℕ → Prop}

theorem colsIn_mulVec (b : Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F)
    (hu : ∀ i, ColsIn P (u i)) (hv : ∀ i, ColsIn P (v i)) (k : Fin 3) :
    ColsIn P (mulVec b u v k) := by
  refine colsIn_sumList _ _ fun i _ => colsIn_sumList _ _ fun j _ => ?_
  exact colsIn_mul (colsIn_mul (hu i) (hv j)) (colsIn_const _)

theorem colsIn_powVec (b : Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F)
    (hu : ∀ i, ColsIn P (u i)) : ∀ (n : ℕ) (k : Fin 3), ColsIn P (powVec b u n k)
  | 0, k => colsIn_const _
  | n + 1, k => colsIn_mulVec b _ u (fun i => colsIn_powVec b u hu n i) hu k

end compile

/-! ## 2. The typed sources -/

/-- The typed expression reads no Form R leaf. -/
def tNoCert : CorrectedFinalTypedExpr → Bool
  | .certBase _ => false
  | .certExt _ => false
  | .add x y => tNoCert x && tNoCert y
  | .sub x y => tNoCert x && tNoCert y
  | .mul x y => tNoCert x && tNoCert y
  | .neg x => tNoCert x
  | .pow x _ => tNoCert x
  | _ => true

def wNoCert : WTyped → Bool
  | .leaf t => tNoCert t
  | .wCur _ => true
  | .wNext _ => true
  | .add x y => wNoCert x && wNoCert y
  | .sub x y => wNoCert x && wNoCert y
  | .mul x y => wNoCert x && wNoCert y
  | .neg x => wNoCert x
  | .pow x _ => wNoCert x

section typed
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem typedCompile_colsIn (b : Basis (Fin 3) F K) :
    ∀ (t : CorrectedFinalTypedExpr), tNoCert t = true → ∀ k : Fin 3,
      ColsIn NoFormR (correctedFinalTypedCompile b t k)
  | .baseCur i, _, k => colsIn_mul (colsIn_var _ _ (Or.inl (by have := i.isLt; omega))) (colsIn_const _)
  | .baseNext i, _, k => colsIn_mul (colsIn_var _ _ (Or.inl (by have := i.isLt; omega))) (colsIn_const _)
  | .extCur i, _, k => colsIn_var _ _ (Or.inl (by
      have := i.isLt; have := k.isLt; simp only [correctedFinalExtCoordIndex]; omega))
  | .extNext i, _, k => colsIn_var _ _ (Or.inl (by
      have := i.isLt; have := k.isLt; simp only [correctedFinalExtCoordIndex]; omega))
  | .challenge i, _, k => by simp [correctedFinalTypedCompile, ColsIn, colsOf]
  | .extensionPublic i, _, k => by simp [correctedFinalTypedCompile, ColsIn, colsOf]
  | .scalarPublic i, _, k => by
      simp only [correctedFinalTypedCompile]
      exact colsIn_mul (by simp [ColsIn, colsOf]) (colsIn_const _)
  | .const c, _, k => colsIn_const _
  | .add x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_add (typedCompile_colsIn b x h.1 k) (typedCompile_colsIn b y h.2 k)
  | .sub x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_sub (typedCompile_colsIn b x h.1 k) (typedCompile_colsIn b y h.2 k)
  | .neg x, h, k => colsIn_neg (typedCompile_colsIn b x h k)
  | .mul x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_mulVec b _ _ (fun i => typedCompile_colsIn b x h.1 i)
        (fun i => typedCompile_colsIn b y h.2 i) k
  | .pow x n, h, k => colsIn_powVec b _ (fun i => typedCompile_colsIn b x h i) n k
  | .certBase i, h, k => by simp [tNoCert] at h
  | .certExt i, h, k => by simp [tNoCert] at h
  | .lamPow d, _, k => by
      simp only [correctedFinalTypedCompile]
      split
      · exact colsIn_powVec b _ (fun i => by simp [ColsIn, colsOf]) _ k
      · exact colsIn_const _
  | .expCur, _, k => colsIn_mul (colsIn_var _ _ (Or.inr (by omega))) (colsIn_const _)

theorem compile309_colsIn (b : Basis (Fin 3) F K) :
    ∀ (t : WTyped), wNoCert t = true → ∀ k : Fin 3, ColsIn NoFormR (compile309 b t k)
  | .leaf t, h, k => typedCompile_colsIn b t h k
  | .wCur j, _, k => colsIn_var _ _ (Or.inr (by simp only [walkLimb]; omega))
  | .wNext j, _, k => colsIn_var _ _ (Or.inr (by simp only [walkLimb]; omega))
  | .add x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_add (compile309_colsIn b x h.1 k) (compile309_colsIn b y h.2 k)
  | .sub x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_sub (compile309_colsIn b x h.1 k) (compile309_colsIn b y h.2 k)
  | .neg x, h, k => colsIn_neg (compile309_colsIn b x h k)
  | .mul x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_mulVec b _ _ (fun i => compile309_colsIn b x h.1 i)
        (fun i => compile309_colsIn b y h.2 i) k
  | .pow x n, h, k => colsIn_powVec b _ (fun i => compile309_colsIn b x h i) n k

end typed


/-! ## 3. The typed sources of the kept gates carry no Form R leaf (computed) -/

/-- The two core gates that read Form R: the sampled-IO denominator pins of records `1` and `2`
(`sampledDenomPin _ 1`, `_ 2` = ids `79`, `80`; pin `0` = id `78` reads no certificate).  They are the
`intermediate`-facing record slots that `computeChipVCL` replaces by the lookup-inverse triples. -/
def formRCoreIds : List ℕ := [79, 80]

/-- The core ids `computeChipVCL` keeps. -/
def keptCoreIds : List CorrectedCoreExtGateId :=
  (List.finRange 82).filter fun i => i.val ∉ formRCoreIds

theorem ext_gates_noCert : ∀ i : CorrectedCoreExtGateId, i ∈ keptCoreIds →
    tNoCert (correctedFinalExtGate i) = true := by
  decide +kernel

/-- Positive control: the two dropped ids DO read Form R (so the filter is necessary). -/
theorem formR_core_reads_cert :
    tNoCert (correctedFinalExtGate ⟨79, by omega⟩) = false ∧
      tNoCert (correctedFinalExtGate ⟨80, by omega⟩) = false := by
  decide +kernel

theorem keptCoreIds_length : keptCoreIds.length = 80 := by decide +kernel

theorem accAfterChain_noCert : tNoCert accAfterChain = true := by decide +kernel
theorem accAfterStep_noCert : tNoCert correctedAccAfterStep = true := by decide +kernel
theorem queueNonEmpty309_noCert : wNoCert queueNonEmpty309 = true := by decide +kernel
theorem queueTiling309_noCert : wNoCert queueTiling309 = true := by decide +kernel
theorem residualSource309_noCert : ∀ j : Fin 2, wNoCert (residualSource309 j) = true := by
  decide +kernel
theorem endpoint2_noCert : ∀ t ∈ endpoint2_309, wNoCert t = true := by decide +kernel
theorem endpoint4_noCert : ∀ t ∈ endpoint4_309, wNoCert t = true := by decide +kernel

/-! ## 4. The kept groups read no column of `[202, 302)` -/

section groups
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem residualWitnessCoord_colsIn (j : ResidualWitnessId) (k : Fin 3) :
    ColsIn NoFormR (residualWitnessCoord (F := F) j k) := by
  refine colsIn_var _ _ (Or.inl ?_)
  have h1 := (OptimizedComputeFinal.finalExtCoordIndex (residualWitnessRole j) k).isLt
  have := j.isLt; have := k.isLt
  simp only [OptimizedComputeFinal.finalExtCoordIndex, OptimizedComputeFinal.residualWitnessRole]; omega

theorem notLastCoeff_colsIn : ColsIn NoFormR (notLastCoeff (F := F)) :=
  colsIn_sub (colsIn_const _) (colsIn_var _ _ (Or.inl (by omega)))

theorem correctedCoreCoord_colsIn (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId)
    (hi : i ∈ keptCoreIds) (k : Fin 3) :
    ColsIn NoFormR (correctedCoreCoord b i k) := by
  have hg := typedCompile_colsIn b _ (ext_gates_noCert i hi) k
  unfold correctedCoreCoord
  split
  · exact colsIn_mul notLastCoeff_colsIn (residualWitnessCoord_colsIn _ _)
  split
  · exact colsIn_mul notLastCoeff_colsIn (residualWitnessCoord_colsIn _ _)
  split
  · exact typedCompile_colsIn b _ accAfterChain_noCert k
  split
  · exact colsIn_mul notLastCoeff_colsIn hg
  · exact hg

theorem correctedCoreCoord309_colsIn (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId)
    (hi : i ∈ keptCoreIds) (k : Fin 3) :
    ColsIn NoFormR (correctedCoreCoord309 b i k) := by
  unfold correctedCoreCoord309
  split
  · exact compile309_colsIn b _ queueNonEmpty309_noCert k
  split
  · exact compile309_colsIn b _ queueTiling309_noCert k
  · exact correctedCoreCoord_colsIn b i hi k

theorem correctedAuxCoord309_colsIn (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId)
    (k : Fin 3) : ColsIn NoFormR (correctedAuxCoord309 b j k) := by
  unfold correctedAuxCoord309
  split
  · rename_i h
    unfold correctedAuxCoord
    simp only [h, if_true]
    exact typedCompile_colsIn b _ accAfterStep_noCert k
  · exact colsIn_sub (residualWitnessCoord_colsIn _ _)
      (compile309_colsIn b _ (residualSource309_noCert _) k)

/-- The kept core: `correctedCore309` without ids `79`, `80`. -/
def correctedCoreVCL (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (keptCoreIds.map fun i => List.ofFn fun k : Fin 3 => correctedCoreCoord309 b i k).flatten

theorem correctedCoreVCL_length (b : Basis (Fin 3) F K) : (correctedCoreVCL (F := F) b).length = 240 := by
  simp only [correctedCoreVCL, List.length_flatten, List.map_map]
  have : ∀ i : CorrectedCoreExtGateId,
      (List.ofFn fun k : Fin 3 => correctedCoreCoord309 (F := F) b i k).length = 3 := by simp
  simp [Function.comp_def, this, keptCoreIds_length]

theorem correctedCoreVCL_colsIn (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedCoreVCL (F := F) b, ColsIn NoFormR g := by
  intro g hg
  simp only [correctedCoreVCL, List.mem_flatten, List.mem_map] at hg
  obtain ⟨_, ⟨i, hi, rfl⟩, hg⟩ := hg
  rw [List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  exact correctedCoreCoord309_colsIn b i hi k

theorem correctedAux309_colsIn (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedAux309 (F := F) b, ColsIn NoFormR g := by
  intro g hg
  simp only [correctedAux309, List.mem_flatten, List.mem_ofFn] at hg
  obtain ⟨_, ⟨j, rfl⟩, hg⟩ := hg
  rw [List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  exact correctedAuxCoord309_colsIn b j k

theorem compileList309_colsIn (b : Basis (Fin 3) F K) (ts : List WTyped)
    (h : ∀ t ∈ ts, wNoCert t = true) : ∀ g ∈ compileList309 (F := F) b ts, ColsIn NoFormR g := by
  intro g hg
  simp only [compileList309, List.mem_flatMap, List.mem_ofFn] at hg
  obtain ⟨t, ht, ⟨k, rfl⟩⟩ := hg
  exact compile309_colsIn b t (h t ht) k

theorem finalBaseTransitionGates_colsIn (n : ℕ) :
    ∀ g ∈ finalBaseTransitionGates (F := F) n, ColsIn NoFormR g := by
  have hv : ∀ i, i < 202 → ColsIn NoFormR (bv (F := F) i) := fun i hi =>
    colsIn_var _ _ (Or.inl hi)
  have hsb : ∀ i, i < 202 → ColsIn NoFormR (selectorBool (F := F) i) := fun i hi =>
    colsIn_mul (hv i hi) (colsIn_sub (colsIn_const _) (hv i hi))
  have hf : ColsIn NoFormR (isFirstVar (F := F)) := hv 11 (by omega)
  have hl : ColsIn NoFormR (isLastVar (F := F)) := hv 12 (by omega)
  intro g hg
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl | rfl | rfl
  · exact hsb i (by omega)
  · exact colsIn_sub (colsIn_sumList _ _ fun i hi => hv i (by simp at hi; omega)) (colsIn_const _)
  · exact colsIn_mul hf (colsIn_sub (colsIn_const _) hf)
  · exact colsIn_mul hl (colsIn_sub (colsIn_const _) hl)
  · unfold endpointOverlapConsistency
    split
    · exact colsIn_sub (colsIn_mul hf hl) (colsIn_const _)
    · exact colsIn_mul hf hl

theorem finalEndpointEqualityChecks_colsIn :
    ∀ g ∈ finalEndpointEqualityChecks (F := F), ColsIn NoFormR g := by
  intro g hg
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range] at hg
  have hv : ∀ i, i < 202 → ColsIn NoFormR (CoeffExpr.var (F := F) .traceCur i) := fun i hi =>
    colsIn_var _ _ (Or.inl hi)
  rcases hg with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
  · refine colsIn_mul (hv _ (by omega)) (colsIn_sub (hv _ (by omega)) ?_)
    intro j hj; simp [colsOf] at hj

end groups

end

end VclL.Compute
end Nock.NockVMROM.Thm54
