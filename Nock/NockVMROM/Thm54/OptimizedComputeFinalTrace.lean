import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
import Nock.NockVMROM.Thm54.TraceEncoding
import Nock.ComputeTable
import Nock.Tree

/-!
# Canonical polynomial trace for the final compute compiler

The construction is deliberately two-stage. Base, normalized 58-role payload, the `acc_after`
role 60 and dedicated walk-line role 61 are interpolated first. Residual roles 58--59 are then
interpolated from the actual degree-four residual evaluations of that preliminary polynomial
trace. This makes the terminal-row auxiliary values agree with the compiler's real `traceNext`
evaluation without an out-of-range or cyclic row lookup.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeFinalTrace

open Classical
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open scoped Polynomial
open OptimizedComputeCodec
open OptimizedComputeSampledTrace
open OptimizedComputeFinal
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open OptimizedComputeRangeCertificate

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

def coreExtensionValue (row : OptimizedComputeCodec.Row F K) (i : Fin 58) : K :=
  if h36 : (i : ℕ) < 36 then
    row.extension (.inl
      (⟨(i : ℕ) / 3, by omega⟩, ⟨(i : ℕ) % 3, Nat.mod_lt _ (by omega)⟩))
  else if h54 : (i : ℕ) < 54 then
    row.extension (.inr (.inl
      (⟨((i : ℕ) - 36) / 3, by omega⟩,
        ⟨((i : ℕ) - 36) % 3, Nat.mod_lt _ (by omega)⟩)))
  else
    row.extension (.inr (.inr ⟨(i : ℕ) - 54, by omega⟩))

/-- `s0` reads role `41` and `s9` reads role `44`.  The flag is the axis-row test;
the stored limb is `coreExtensionValue`, not a constant. -/
def formRLeafDummy (row : OptimizedComputeCodec.Row F K) (role : Fin 58) : Bool :=
  (decide ((role : ℕ) = 41) && decide (decodeState row.base = .s0)) ||
    (decide ((role : ℕ) = 44) && decide (decodeState row.base = .s9))

/-- Core extension role.  Roles `41` and `44` are the encoded `f_t.leaf` / `f_th.leaf`,
the same value `coreExtensionValue` stores.  The axis equation reads those limbs
from the trace; this `K` is the encoded core the walk and the formula read. -/
noncomputable def formRLeafCore (b : Basis (Fin 3) F K)
    (row : OptimizedComputeCodec.Row F K) (role : Fin 58) : K :=
  coreExtensionValue row role

theorem formRLeafCore_eq_core (b : Basis (Fin 3) F K)
    (row : OptimizedComputeCodec.Row F K) (role : Fin 58)
    (h : (role : ℕ) ≠ 41 ∧ (role : ℕ) ≠ 44) :
    formRLeafCore b row role = coreExtensionValue row role := by
  have := h
  simp [formRLeafCore]

/-- Off the axis opcode the leaf role is the encoded core.  `s1` reads role `41`
and is not `s0`; nothing in `sourcePubAtR` reads role `44`. -/
theorem formRLeafCore_eq_core_of_row (b : Basis (Fin 3) F K)
    (row : OptimizedComputeCodec.Row F K) (role : Fin 58)
    (h : formRLeafDummy row role = false) :
    formRLeafCore b row role = coreExtensionValue row role := by
  have := h
  simp [formRLeafCore]

theorem formRLeafCore_eq_core_all (b : Basis (Fin 3) F K)
    (row : OptimizedComputeCodec.Row F K) (role : Fin 58) :
    formRLeafCore b row role = coreExtensionValue row role := by
  simp [formRLeafCore]

theorem coord_formRLeafCore (b : Basis (Fin 3) F K)
    (row : OptimizedComputeCodec.Row F K) (role : Fin 58) (k : Fin 3) :
    coord b (formRLeafCore b row role) k =
      coord b (coreExtensionValue row role) k := by
  simp [formRLeafCore]

def finalBaseCell (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (i : Fin R.problem.cfg.compRows) (j : Fin 13) : F :=
  if h11 : (j : ℕ) < 11 then
    (encodedRowAt A i).base (.inl ⟨j, h11⟩)
  else if (j : ℕ) = 11 then
    if (i : ℕ) = 0 then 1 else 0
  else
    if i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0

/-- Coordinate 0 of the axis leaf: `f_t.leaf` on `s0`, `f_th.leaf` on `s9`. -/
def axisLeafCoord (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (i : Fin R.problem.cfg.compRows) : Option F :=
  match decodeState (encodedRowAt A i).base with
  | .s0 => some (coord b (coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩) 0)
  | .s9 => some (coord b (coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩) 0)
  | _ => none

/-- The `𝕂`-valued axis leaf of an `s0` / `s9` row (the record axis roles `41` / `44`; the
`mr₂` / `mr₃` axis of `OptimizedComputeSubstitution.mr2Field` / `mr3Field`), `0` otherwise. -/
def axisLeafK (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : K :=
  match decodeState (encodedRowAt A i).base with
  | .s0 => coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩
  | .s9 => coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩
  | _ => 0

/-- Basis-free natural axis of an `s0` / `s9` row: the residue of the `𝕂` leaf
(`MemoryTable.nockAxisOf`, the axis the Form R encode `encRecFormR` reads), `0` otherwise. -/
noncomputable def axisNatK (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : ℕ :=
  match decodeState (encodedRowAt A i).base with
  | .s0 | .s9 => MemoryTable.nockAxisOf (axisLeafK A i)
  | _ => 0

/-- Formula-noun axis: `[0 a]` or `[9 a c]`.  Inactive / non-axis formulas are `none`. -/
def axisOfFormula : Noun → Option ℕ
  | .cell (.atom 0) (.atom a) => some a
  | .cell (.atom 9) (.cell (.atom a) _) => some a
  | _ => none

/-- Per-row axis from the formula noun and the row state.  `A` does not expose this
    noun: `SampledIOSameExecutionAssignment` stores fingerprints only.  The missing
    projection is `ComputeRowSemanticData.root.formula` on
    `E.semanticData.rows i`; `sampledAssignment E I` (`BuildableChips`) has `E`. -/
def axisAtomOf (st : ComputeTable.State) (formula : Noun) : Option ℕ :=
  match st with
  | .s0 | .s9 => axisOfFormula formula
  | _ => none

/-- `coord b 1 = (1,0,0)`.  Not a lemma of an arbitrary `Basis (Fin 3) F K`;
    named SAT hypothesis. -/
def FormRBasis (b : Basis (Fin 3) F K) : Prop :=
  coord b (1 : K) 0 = 1 ∧ coord b (1 : K) 1 = 0 ∧ coord b (1 : K) 2 = 0

/-- Chip width: `Nat.size (ringChar F) ≤ 64`, and the characteristic is live
    (`0 < formRN`).  Goldilocks is equality at 64.  Leftover-gt / dummy-T /
    leftover-match at `m = 0` are uninhabited under this plus `a < 2^64`.
    The second conjunct is the SAT-facing fragment of `hp : 25 ≤ p`. -/
def FormRWidth (F : Type*) [Field F] : Prop :=
  OptimizedComputeRangeCertificate.formRN F ≤ 64 ∧
    0 < OptimizedComputeRangeCertificate.formRN F ∧
    3 < ringChar F

/-- Every committed axis leaf is a positive nat-cast below the base-field
    characteristic and the Form R chip width `2^64`.  Replaces `FormRLeafCover`.
    Discharged at the carrier by `runAxesBoundedBy_of_hyps` (`0 < a < p`) plus
    `p < 2^64` (Goldilocks) or an explicit `a < 2^64`.  `A` stores no formula
    noun; the correspondence is `ComputeRowSemanticData.root.formula` on
    `sampledAssignment E I`. -/
def FormRAxisBound (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) : Prop :=
  ∀ (i : Fin R.problem.cfg.compRows) (L : F),
    axisLeafCoord A b i = some L →
      ∃ a : ℕ, 0 < a ∧ a < ringChar F ∧ a < 2 ^ 64 ∧ (a : F) = L ∧
        ((a : ℕ) : K) = axisLeafK A i

/-- No committed axis leaf (`s0`/`s9` absent) is vacuously Form R. -/
theorem FormRAxisBound_of_none {A : SampledIOSameExecutionAssignment R p}
    {b : Basis (Fin 3) F K} (h : ∀ i, axisLeafCoord A b i = none) :
    FormRAxisBound A b := fun i L hL => by
  rw [h i] at hL
  cases hL

/-- On `ZMod q`, every nonzero committed leaf is a positive residue `< q`.
    The `q < 2^64` half is `FormRWidth` / `Nat.size q ≤ 64`.  This is the
    fixture `of_root` discharge: `runAxesBoundedBy_of_hyps` supplies
    `0 < a < q` at the carrier; here the residue is `L.val`. -/
theorem FormRAxisBound_of_zmod
    {q : ℕ} [Fact q.Prime]
    {K' : Type} [Field K'] [Algebra (ZMod q) K'] [FiniteDimensional (ZMod q) K']
    [Fintype K'] [DecidableEq K'] [CharP K' q]
    {R' : PlusIOSegmentedFamily (ZMod q) K'}
    (A : SampledIOSameExecutionAssignment R' q)
    (b : Basis (Fin 3) (ZMod q) K')
    (hq64 : q < 2 ^ 64)
    (hpos : ∀ i L, axisLeafCoord A b i = some L → L ≠ 0)
    (hbase : ∀ i L, axisLeafCoord A b i = some L → algebraMap (ZMod q) K' L = axisLeafK A i) :
    FormRAxisBound A b := by
  intro i L hL
  have hc : ringChar (ZMod q) = q := ZMod.ringChar_zmod_n q
  have hne : L ≠ 0 := hpos i L hL
  have hval : L.val ≠ 0 := by
    intro hv
    apply hne
    rw [← ZMod.natCast_zmod_val L, hv, Nat.cast_zero]
  refine ⟨L.val, Nat.pos_iff_ne_zero.mpr hval, ?_,
    lt_trans (ZMod.val_lt L) hq64, ZMod.natCast_zmod_val L, ?_⟩
  · rw [hc]
    exact ZMod.val_lt L
  · rw [← hbase i L hL, ← map_natCast (algebraMap (ZMod q) K'), ZMod.natCast_zmod_val L]

/-- Unique positive residue of a committed leaf, else `0` (inactive / zero cert).
    `A` has no row noun, so the fill recovers the nat that `FormRAxisBound`
    says exists.  This is not a window classifier. -/
noncomputable def axisNat (leaf : Option F) : ℕ :=
  match leaf with
  | none => 0
  | some L =>
      if h : ∃ a : ℕ, 0 < a ∧ (a : F) = L then Nat.find h else 0

theorem axisNat_none : axisNat (F := F) none = 0 := rfl

theorem axisNat_of_mem (L : F) {a : ℕ} (ha0 : 0 < a) (he : (a : F) = L) :
    0 < axisNat (some L) ∧ axisNat (some L) ≤ a ∧
      ((axisNat (some L) : F) = L) := by
  have hex : ∃ n : ℕ, 0 < n ∧ (n : F) = L := ⟨a, ha0, he⟩
  have hpos : 0 < Nat.find hex := (Nat.find_spec hex).1
  have hcast : ((Nat.find hex : ℕ) : F) = L := (Nat.find_spec hex).2
  have hle : Nat.find hex ≤ a := Nat.find_le ⟨ha0, he⟩
  have haxis : axisNat (some L) = Nat.find hex := dif_pos hex
  rw [haxis]
  exact ⟨hpos, hle, hcast⟩

theorem axisNat_lt_64 (L : F) {a : ℕ} (ha0 : 0 < a) (h64 : a < 2 ^ 64)
    (he : (a : F) = L) : axisNat (some L) < 2 ^ 64 :=
  lt_of_le_of_lt (axisNat_of_mem L ha0 he).2.1 h64

/-- Two residues below the characteristic with equal casts are equal. -/
theorem natCast_inj_of_lt_ringChar {L : Type*} [Field L] {a c : ℕ}
    (ha : a < ringChar L) (hc : c < ringChar L) (h : (a : L) = (c : L)) : a = c := by
  have hmod : a ≡ c [MOD ringChar L] :=
    (CharP.natCast_eq_natCast (R := L) (p := ringChar L)).mp h
  exact Nat.ModEq.eq_of_lt_of_lt hmod ha hc

/-- Under `FormRAxisBound`, the coordinate-keyed certificate axis is the basis-free residue
of the `𝕂` record axis (`axisNatK`), the axis `encRecFormR` reads. -/
theorem axisNat_axisLeafCoord_eq (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (hax : FormRAxisBound A b) (i : Fin R.problem.cfg.compRows) :
    axisNat (axisLeafCoord A b i) = axisNatK A i := by
  have key : ∀ L : F, axisLeafCoord A b i = some L →
      axisNat (some L) = MemoryTable.nockAxisOf (axisLeafK A i) := by
    intro L hL
    obtain ⟨a, ha0, hap, _h64, haL, haK⟩ := hax i L hL
    have hmem := axisNat_of_mem L ha0 haL
    have hapK : a < ringChar K := by rwa [← Algebra.ringChar_eq F K]
    rw [← haK, MemoryTable.nockAxisOf_natCast hapK]
    exact natCast_inj_of_lt_ringChar (lt_of_le_of_lt hmem.2.1 hap) hap
      (hmem.2.2.trans haL.symm)
  have hdef : axisLeafCoord A b i =
      match decodeState (encodedRowAt A i).base with
      | .s0 => some (coord b (coreExtensionValue (encodedRowAt A i) ⟨41, by decide⟩) 0)
      | .s9 => some (coord b (coreExtensionValue (encodedRowAt A i) ⟨44, by decide⟩) 0)
      | _ => none := rfl
  unfold axisNatK
  cases hs : decodeState (encodedRowAt A i).base
  case s0 => simp only [hs] at hdef ⊢; exact (congrArg axisNat hdef).trans (key _ hdef)
  case s9 => simp only [hs] at hdef ⊢; exact (congrArg axisNat hdef).trans (key _ hdef)
  all_goals (simp only [hs] at hdef ⊢; rw [hdef]; rfl)

/-- Constructive `exists_cert` witness: `m = size a − 1`, bits of `a`. -/
def axisCertM (a : ℕ) : ℕ := OptimizedComputeRangeCertificate.certShift a

/-- One Form R certificate, indexed by the natural axis.  `none` and `L` with
    no positive residue take the zero certificate (`m = 0`, `c = 0`). -/
noncomputable def formROffNat (a : ℕ) (off : ℕ) : F :=
  let m := axisCertM a
  if off < 63 then
    bit01 (certCBit a off)
  else if off < 69 then
    bit01 ((rangeShiftExp (F := F) m).testBit (off - 63))
  else if off = 69 then
    powBits (2 : F) (rangeShiftExp (F := F) m) 3
  else if off = 70 then
    powBits (2 : F) (rangeShiftExp (F := F) m) 6
  else if off = 71 then
    matchedP (F := F) (rangeShiftExp (F := F) m)
  else if off = 72 then
    leftoverBitMatchedTop (F := F) m
  else if 73 ≤ off ∧ off < 94 then
    leftoverHelperMask (F := F) m * certEqRun a (3 * ((off - 73) + 1))
  else 0

/-- The leftover certificate of a committed leaf (`formROffNat` at `axisNat leaf`). -/
noncomputable def formROff (leaf : Option F) (off : ℕ) : F :=
  formROffNat (axisNat leaf) off

theorem formROff_c (leaf : Option F) (j : ℕ) (hj : j < 63) :
    formROff leaf j = bit01 (certCBit (axisNat leaf) j) := by
  simp only [formROff, formROffNat]
  rw [if_pos hj]

theorem formROff_c_bool (leaf : Option F) (j : ℕ) (hj : j < 63) :
    formROff leaf j * (formROff leaf j - 1) = 0 := by
  rw [formROff_c leaf j hj]
  exact bit01_mul_sub _

theorem formROff_m (leaf : Option F) (k : ℕ) (hk : k < 6) :
    formROff leaf (63 + k) =
      bit01 ((rangeShiftExp (F := F) (axisCertM (axisNat leaf))).testBit k) := by
  have h63 : ¬ 63 + k < 63 := by omega
  have h69 : 63 + k < 69 := by omega
  simp only [formROff, formROffNat]
  rw [if_neg h63, if_pos h69]
  simp [show 63 + k - 63 = k by omega]

theorem formROff_h (leaf : Option F) :
    formROff leaf 69 =
      powBits (2 : F) (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 3 := by
  simp only [formROff, formROffNat]
  rw [if_neg (by omega : ¬ (69 : ℕ) < 63), if_neg (by omega : ¬ (69 : ℕ) < 69)]
  simp

theorem formROff_t (leaf : Option F) :
    formROff leaf 70 =
      powBits (2 : F) (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 6 := by
  simp only [formROff, formROffNat]
  rw [if_neg (by omega : ¬ (70 : ℕ) < 63), if_neg (by omega : ¬ (70 : ℕ) < 69),
    if_neg (by omega : (70 : ℕ) ≠ 69)]
  simp

theorem formROff_p (leaf : Option F) :
    formROff leaf 71 =
      matchedP (F := F) (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) := by
  simp only [formROff, formROffNat]
  rw [if_neg (by decide : ¬ (71 : ℕ) < 63), if_neg (by decide : ¬ (71 : ℕ) < 69),
    if_neg (by decide : (71 : ℕ) ≠ 69), if_neg (by decide : (71 : ℕ) ≠ 70)]
  simp

theorem formROff_top (leaf : Option F) :
    formROff leaf 72 =
      leftoverBitMatchedTop (F := F) (axisCertM (axisNat leaf)) := by
  simp only [formROff, formROffNat]
  rw [if_neg (by decide : ¬ (72 : ℕ) < 63), if_neg (by decide : ¬ (72 : ℕ) < 69),
    if_neg (by decide : (72 : ℕ) ≠ 69), if_neg (by decide : (72 : ℕ) ≠ 70),
    if_neg (by decide : (72 : ℕ) ≠ 71)]
  simp

theorem formROff_helper (leaf : Option F) (k : ℕ) (hk : k < 21) :
    formROff leaf (73 + k) =
      leftoverHelperMask (F := F) (axisCertM (axisNat leaf)) *
        certEqRun (axisNat leaf) (3 * (k + 1)) := by
  simp only [formROff, formROffNat]
  simp [show ¬ (73 + k < 63) by omega, show ¬ (73 + k < 69) by omega,
    show 73 + k ≠ 69 by omega, show 73 + k ≠ 70 by omega,
    show 73 + k ≠ 71 by omega, show 73 + k ≠ 72 by omega,
    show 73 ≤ 73 + k ∧ 73 + k < 94 by omega,
    show 73 + k - 73 = k by omega]

/-- `λ`-power columns: `λ` to the axis shift, or `λ^0 = 1` on the zero certificate. -/
noncomputable def formRLamH (leaf : Option F) (lam : F) : F :=
  powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 3

noncomputable def formRLamT (leaf : Option F) (lam : F) : F :=
  powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 6

theorem formRLamH_eq (leaf : Option F) (lam : F) :
    formRLamH leaf lam =
      powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 3 := rfl

theorem formRLamT_eq (leaf : Option F) (lam : F) :
    formRLamT leaf lam =
      powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat leaf))) 6 := rfl

noncomputable def formRLamOfChal (b : Basis (Fin 3) F K) (chalVal : ℕ → F) : K :=
  ∑ k : Fin 3, chalVal (27 + (k : ℕ)) • b k

/-- `𝕂` helper `H = λ^{m mod 8}` of the leftover certificate of the natural axis `a`. -/
noncomputable def formRLamHNat (a : ℕ) (lam : K) : K :=
  powBits lam (rangeShiftExp (F := F) (axisCertM a)) 3

/-- `𝕂` helper `T = λ^m` of the leftover certificate of the natural axis `a`. -/
noncomputable def formRLamTNat (a : ℕ) (lam : K) : K :=
  powBits lam (rangeShiftExp (F := F) (axisCertM a)) 6

/-- `𝕂` helper `H = λ^{m mod 8}` of the leftover certificate (`λ ∈ 𝕂`). -/
noncomputable def formRLamHK (leaf : Option F) (lam : K) : K :=
  formRLamHNat (F := F) (axisNat leaf) lam

/-- `𝕂` helper `T = λ^m` of the leftover certificate (`λ ∈ 𝕂`). -/
noncomputable def formRLamTK (leaf : Option F) (lam : K) : K :=
  formRLamTNat (F := F) (axisNat leaf) lam

/-- Compatibility aliases used by the leftover SAT path. -/
theorem formROff_c_cert (L : F) (j : ℕ) (hj : j < 63) :
    formROff (some L) j = bit01 (certCBit (axisNat (some L)) j) :=
  formROff_c (some L) j hj

theorem formROff_m_cert (L : F) (k : ℕ) (hk : k < 6) :
    formROff (some L) (63 + k) =
      bit01 ((rangeShiftExp (F := F) (axisCertM (axisNat (some L)))).testBit k) :=
  formROff_m (some L) k hk

theorem formROff_pow_cert (L : F) :
    formROff (some L) 69 =
      powBits (2 : F) (rangeShiftExp (F := F) (axisCertM (axisNat (some L)))) 3 ∧
    formROff (some L) 70 =
      powBits (2 : F) (rangeShiftExp (F := F) (axisCertM (axisNat (some L)))) 6 :=
  ⟨formROff_h (some L), formROff_t (some L)⟩

theorem formROff_pins_cert (L : F) :
    formROff (some L) 71 =
      matchedP (F := F) (rangeShiftExp (F := F) (axisCertM (axisNat (some L)))) ∧
    formROff (some L) 72 =
      leftoverBitMatchedTop (F := F) (axisCertM (axisNat (some L))) :=
  ⟨formROff_p (some L), formROff_top (some L)⟩

theorem formROff_helper_cert (L : F) (k : ℕ) (hk : k < 21) :
    formROff (some L) (73 + k) =
      leftoverHelperMask (F := F) (axisCertM (axisNat (some L))) *
        certEqRun (axisNat (some L)) (3 * (k + 1)) :=
  formROff_helper (some L) k hk

theorem formRLamH_cert (L : F) (lam : F) :
    formRLamH (some L) lam =
      powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat (some L)))) 3 :=
  formRLamH_eq (some L) lam

theorem formRLamT_cert (L : F) (lam : F) :
    formRLamT (some L) lam =
      powBits lam (rangeShiftExp (F := F) (axisCertM (axisNat (some L)))) 6 :=
  formRLamT_eq (some L) lam

/-- DELETED window classifiers (`lowLimb` / `goodWide` / `certLeaf` / `limbVal` /
    `FormRCover`) lived here.  The fill is the natural-axis leftover certificate. -/
theorem formROff_zero_c (j : ℕ) (hj : j < 63) :
    formROff (F := F) none j = 0 := by
  rw [formROff_c none j hj]
  simp [axisNat_none, certCBit, certShift, Nat.size_zero, bit01]

def preliminaryCell (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (b : Basis (Fin 3) F K)
    (i : Fin R.problem.cfg.compRows) (j : Fin 302) : F :=
  if h13 : (j : ℕ) < 13 then
    finalBaseCell A hn i ⟨j, h13⟩
  else
    let role := ((j : ℕ) - 13) / 3
    let k : Fin 3 := ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩
    if h58 : role < 58 then
      coord b (coreExtensionValue (encodedRowAt A i) ⟨role, h58⟩) k
    else if role = 61 then
      coord b (A.exact.computeWalk.ln ((i : ℕ) + 1)) k
    else if role = 60 then
      -- `acc_after(i)`: the co-resident request accumulator at the boundary after row `i`.
      coord b (ComputeSampledIO.coResidentAccC A.compress10
        R.problem.cfg.challenges.lam R.problem.exec.computeRows ((i : ℕ) + 1)) k
    else if role = 62 then
      let c := A.exact.computeWalk.count ((i : ℕ) + 1)
      let l := A.exact.computeWalk.ln ((i : ℕ) + 1)
      coord b (if c = l then 0 else (c - l)⁻¹) k
    else if (j : ℕ) < 202 then
      0
    else
      -- Form R leftover certificate of the natural axis, or the zero certificate.
      formROff (axisLeafCoord A b i) ((j : ℕ) - 202)

/-- Form-R columns `202.. 301` skip every pre-form-R role branch. -/
theorem preliminaryCell_formR
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (b : Basis (Fin 3) F K)
    (i : Fin R.problem.cfg.compRows) (j : Fin 302)
    (hj : 202 ≤ (j : ℕ)) :
    preliminaryCell A hn b i j = formROff (axisLeafCoord A b i) ((j : ℕ) - 202) := by
  have h13 : ¬ (j : ℕ) < 13 := by omega
  have hrole : ¬ ((j : ℕ) - 13) / 3 < 58 := by omega
  have hn61 : ((j : ℕ) - 13) / 3 ≠ 61 := by omega
  have hn60 : ((j : ℕ) - 13) / 3 ≠ 60 := by omega
  have hn62 : ((j : ℕ) - 13) / 3 ≠ 62 := by omega
  have hn202 : ¬ (j : ℕ) < 202 := Nat.not_lt.mpr hj
  unfold preliminaryCell
  simp [h13, hrole, hn61, hn60, hn62, hn202]

def interpolateColumn {n w : ℕ} (nodes : Fin n → F)
    (cells : Fin n → Fin w → F) (j : Fin w) : F[X] :=
  Lagrange.interpolate Finset.univ nodes (fun i => cells i j)

theorem interpolateColumn_eval {n w : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (cells : Fin n → Fin w → F)
    (i : Fin n) (j : Fin w) :
    (interpolateColumn nodes cells j).eval (nodes i) = cells i j :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

/-- Stage-one trace. Slots 11/12 are definitionally the fixed preprocessing polynomials. -/
def preliminaryTrace (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) : Fin 302 → F[X] :=
  fun j =>
    if (j : ℕ) = 11 then firstRowMask nodes
    else if (j : ℕ) = 12 then lastRowMask hn nodes
    else interpolateColumn nodes (preliminaryCell A hn b) j

theorem preliminaryTrace_eval (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (i : Fin R.problem.cfg.compRows) (j : Fin 302) :
    (preliminaryTrace A hn nodes b j).eval (nodes i) =
      preliminaryCell A hn b i j := by
  by_cases h11 : (j : ℕ) = 11
  · have hj : j = ⟨11, by omega⟩ := Fin.ext h11
    rw [hj]
    rw [show preliminaryTrace A hn nodes b ⟨11, by omega⟩ = firstRowMask nodes by
      simp [preliminaryTrace]]
    rw [firstRowMask_eval nodes hnodes]
    simp [preliminaryCell, finalBaseCell]
  by_cases h12 : (j : ℕ) = 12
  · rw [preliminaryTrace, if_neg h11, if_pos h12, lastRowMask_eval hn nodes hnodes]
    simp [preliminaryCell, finalBaseCell, h12]
  · rw [preliminaryTrace, if_neg h11, if_neg h12,
      interpolateColumn_eval nodes hnodes]

def residualCell (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (r : ResidualWitnessId) (k : Fin 3) : F :=
  (finalTypedCompile b (finalResidualSource r) k).eval
    (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω (nodes i) chalVal pubVal)

def residualPolynomial (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (r : ResidualWitnessId) (k : Fin 3) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => (finalTypedCompile b (finalResidualSource r) k).eval
      (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω (nodes i) chalVal pubVal))

/-- Canonical 202-column, two-round final trace. Roles 58--60 are exact residuals and role 61 is
the dedicated walk line. -/
def canonicalFinalTrace (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Fin 302 → F[X] :=
  fun j =>
    let role := ((j : ℕ) - 13) / 3
    let k : Fin 3 := ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩
    if hj : 13 ≤ (j : ℕ) ∧ role < 61 ∧ 58 ≤ role then
      residualPolynomial A hn nodes b chalVal pubVal orbit
        ⟨role - 58, by omega⟩ k
    else
      preliminaryTrace A hn nodes b j

theorem canonicalFinalTrace_eval (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ}
    (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (j : Fin 302) :
    (canonicalFinalTrace A hn nodes b chalVal pubVal orbit j).eval (nodes i) =
      if hj : 13 ≤ (j : ℕ) ∧ ((j : ℕ) - 13) / 3 < 61 ∧
          58 ≤ ((j : ℕ) - 13) / 3 then
        (finalTypedCompile b
          (finalResidualSource ⟨((j : ℕ) - 13) / 3 - 58, by omega⟩)
          ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩).eval
          (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
            (nodes i) chalVal pubVal)
      else preliminaryCell A hn b i j := by
  simp only [canonicalFinalTrace]
  split
  · rw [residualPolynomial, Lagrange.eval_interpolate_at_node _ hnodes.injOn
      (Finset.mem_univ i)]
  · rw [preliminaryTrace_eval A hn nodes hnodes b i j]

theorem canonicalFinalTrace_binds_preprocessing
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) :
    (NamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing
      (canonicalFinalTrace A hn nodes b chalVal pubVal orbit) := by
  intro j
  fin_cases j
  · change canonicalFinalTrace A hn nodes b chalVal pubVal orbit
      ⟨11, by omega⟩ = firstRowMask nodes
    simp [canonicalFinalTrace, preliminaryTrace]
  · change canonicalFinalTrace A hn nodes b chalVal pubVal orbit
      ⟨12, by omega⟩ = lastRowMask hn nodes
    simp [canonicalFinalTrace, preliminaryTrace]


def correctedResidualPolynomial (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (r : ResidualWitnessId) (k : Fin 3) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => (correctedFinalTypedCompile b (correctedFinalResidualSource r) k).eval
      (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω (nodes i) chalVal pubVal))

def honestS (R : PlusIOSegmentedFamily F K) (i : ℕ) : ℕ :=
  ((R.problem.exec.computeRows.take i).map
    (fun row => (NockVM.activeRequestRecords row.2.2.1).length)).sum

/-- **The honest exponent of an active request is `S(i) + j + 1`**: the `j`-th active request of
row `i` is the record at position `honestS R i + j` of the duplicate-free derived request list. -/
theorem honestExp_activeRequest (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ)
    (hj : j < (NockVM.activeRequestRecords (R.problem.exec.computePubAt i)).length) :
    RecordCarrier.honestExp R.problem.exec.derivedRequestIO
        (NockVM.encRecFormR ((NockVM.activeRequestRecords (R.problem.exec.computePubAt i))[j])
          R.problem.cfg.challenges.lam) =
      honestS R i + j + 1 := by
  set f : ComputeTable.State × ComputeTable.DTcomp K → List (Fin 9 → K) :=
    fun row => (NockVM.activeRequestRecords row.2.2.1).map
      (fun r => NockVM.encRecFormR r R.problem.cfg.challenges.lam) with hf
  have hL : R.problem.exec.derivedRequestIO = R.problem.exec.computeRows.flatMap f := by
    rw [ExactExecution.derivedRequestIO_eq_computeRows, List.map_flatMap]
  have hnd : (R.problem.exec.computeRows.flatMap f).Nodup := by
    rw [← hL, ← A.requests_eq]; exact A.sampled.uniqueRequest
  have hi : (i : ℕ) < R.problem.exec.computeRows.length := by
    rw [R.problem.exec.computeRows_length]; exact i.isLt
  have hrow : R.problem.exec.computeRows[(i : ℕ)] = R.problem.exec.computeRowAt i := by
    simp [ExactExecution.computeRowAt, List.get_eq_getElem]
  have hj' : j < (f R.problem.exec.computeRows[(i : ℕ)]).length := by
    simpa [hf, hrow, ExactExecution.computePubAt] using hj
  have h := RecordCarrier.honestExp_flatMap R.problem.exec.computeRows f hnd i hi j hj'
  rw [hL]
  have hel : (f R.problem.exec.computeRows[(i : ℕ)])[j] =
      NockVM.encRecFormR ((NockVM.activeRequestRecords (R.problem.exec.computePubAt i))[j])
        R.problem.cfg.challenges.lam := by
    simp [hf, hrow, ExactExecution.computePubAt]
  rw [← hel, h]
  simp [honestS, hf, Function.comp_def]

/-- Consumed canonical trace. -/
def correctedCanonicalFinalTrace (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Fin 303 → F[X] :=
  fun j =>
    if hH : 296 ≤ (j : ℕ) ∧ (j : ℕ) < 299 then
      Lagrange.interpolate Finset.univ nodes
        (fun i => coord b (formRLamHK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
          ⟨(j : ℕ) - 296, by omega⟩)
    else if hT : 299 ≤ (j : ℕ) then
      if hS : (j : ℕ) = 302 then
        Lagrange.interpolate Finset.univ nodes (fun i => ((honestS R i : ℕ) : F))
      else
        Lagrange.interpolate Finset.univ nodes
          (fun i => coord b (formRLamTK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
            ⟨(j : ℕ) - 299, by omega⟩)
    else
      let role := ((j : ℕ) - 13) / 3
      let k : Fin 3 := ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩
      if hj : 13 ≤ (j : ℕ) ∧ role < 60 ∧ 58 ≤ role then
        correctedResidualPolynomial A hn nodes b chalVal pubVal orbit
          ⟨role - 58, by omega⟩ k
      else preliminaryTrace A hn nodes b ⟨j, by omega⟩

theorem correctedCanonicalFinalTrace_eval (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (j : Fin 303) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit j).eval (nodes i) =
      if hH : 296 ≤ (j : ℕ) ∧ (j : ℕ) < 299 then
        coord b (formRLamHK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
          ⟨(j : ℕ) - 296, by omega⟩
      else if hT : 299 ≤ (j : ℕ) then
        if hS : (j : ℕ) = 302 then ((honestS R i : ℕ) : F)
        else
          coord b (formRLamTK (axisLeafCoord A b i) (formRLamOfChal b chalVal))
            ⟨(j : ℕ) - 299, by omega⟩
      else if hj : 13 ≤ (j : ℕ) ∧ ((j : ℕ) - 13) / 3 < 60 ∧
          58 ≤ ((j : ℕ) - 13) / 3 then
        (correctedFinalTypedCompile b
          (correctedFinalResidualSource ⟨((j : ℕ) - 13) / 3 - 58, by omega⟩)
          ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩).eval
          (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
            (nodes i) chalVal pubVal)
      else preliminaryCell A hn b i ⟨j, by omega⟩ := by
  simp only [correctedCanonicalFinalTrace]
  split_ifs with hH hT hS hj
  · rw [Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)]
  · rw [Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)]
  · rw [Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)]
  · rw [correctedResidualPolynomial, Lagrange.eval_interpolate_at_node _ hnodes.injOn
      (Finset.mem_univ i)]
  · rw [preliminaryTrace_eval A hn nodes hnodes b i _]

/-- The carrier column. -/
theorem correctedCanonicalFinalTrace_eval_S (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit ⟨302, by omega⟩).eval
      (nodes i) = ((honestS R i : ℕ) : F) := by
  rw [correctedCanonicalFinalTrace_eval A hn nodes hnodes]
  simp

/-- Pre-form-R columns (`j < 202`) keep the residual-or-preliminary reduction. -/
theorem correctedCanonicalFinalTrace_eval_preFormR
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) (j : Fin 303) (hlt : (j : ℕ) < 202) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit j).eval (nodes i) =
      if hj : 13 ≤ (j : ℕ) ∧ ((j : ℕ) - 13) / 3 < 60 ∧
          58 ≤ ((j : ℕ) - 13) / 3 then
        (correctedFinalTypedCompile b
          (correctedFinalResidualSource ⟨((j : ℕ) - 13) / 3 - 58, by omega⟩)
          ⟨((j : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩).eval
          (envOfTrace (preliminaryTrace A hn nodes b) orbit.ω
            (nodes i) chalVal pubVal)
      else preliminaryCell A hn b i ⟨j, by omega⟩ := by
  rw [correctedCanonicalFinalTrace_eval A hn nodes hnodes]
  have h296 : ¬ (296 ≤ (j : ℕ) ∧ (j : ℕ) < 299) := by omega
  have h299 : ¬ 299 ≤ (j : ℕ) := by omega
  simp [h296, h299]

theorem correctedCanonicalFinalTrace_binds_preprocessing
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) :
    (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) := by
  intro j
  fin_cases j
  · change correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit
      ⟨11, by omega⟩ = firstRowMask nodes
    simp [correctedCanonicalFinalTrace, preliminaryTrace]
  · change correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit
      ⟨12, by omega⟩ = lastRowMask hn nodes
    simp [correctedCanonicalFinalTrace, preliminaryTrace]

#print axioms preliminaryTrace_eval
#print axioms canonicalFinalTrace_eval
#print axioms canonicalFinalTrace_binds_preprocessing
#print axioms correctedCanonicalFinalTrace_eval
#print axioms correctedCanonicalFinalTrace_binds_preprocessing

end

end OptimizedComputeFinalTrace
end Nock.NockVMROM.Thm54
