/-
  Nock/NockVMROM/Thm54/VclL/Handle/SplitChipJ9.lean

  A NEW template; no existing module is
  edited.

  **Split value.** The split chip has NO `v` column, NO `inv` column, NO gate `v − hi·B − lo`
  and NO g4 gate.  The split value is `splitVal s := hi.val·B + lo.val` in ℕ (`splitValN` below).  The provided
  records `(id, 2, 0, lo)`, `(id, 3, 0, hi)` are unchanged.
  **F2:** `pubNA` is a TEMPLATE PARAMETER `nA` (as `kroots` in `walkChipHQK`), never a prover
  column: the gate `id − pubNA − s` is `id − (nA : F) − s`.

  **Layout** (MEASURED `w = 90` by `rfl`): base `0 isFirstT`, `1 isLastT` (preprocessing), `2 s` (row counter),
  `3 id`, `4 hi`, `5 lo`, `6 .. 69` bits `b_0 .. b_63`, `70 invHi`, `71 m` (multiplicity); `𝕂`-roles (round 2) as
  `𝕂′` pairs: `inv2 0/1` (record `(id,2,0,lo)`), `inv3 2/3` (record `(id,3,0,hi)`), `acc 4/5`.
  `72 + 6·3 = 90`.  (An earlier estimate of "≈ 80" columns was too low; the extension block here is two provide inverses and one
  accumulator, the standard memory-side shape of `atomQ`, rather than one paired inverse.)

  **Gates** (minus the dropped value-column gates): 64 bit booleanities; `hi − Σ_{i<32} 2^i b_{32+i}`,
  `lo − Σ_{i<32} 2^i b_i`; `isFirstT·s`, `(1 − isLastT)·(next.s − s − 1)`; `id − pubNA − s`; `hi·invHi − 1`.
  `𝕂′`: the two inverse gates (handle coins `HQ.denKeyQ`) and the accumulator `acc` over `m·(inv2 + inv3)` with
  terminal `pubSPs = 0/1` (the RHS of the J-9 A `hGS`).  **The split chip provides no tagged key** (cond. 3).

  **Instrument.** Serial-capable columns: `s`, `id`.  Every gate except the three counter gates is serial-free;
  the counter class is exactly `isFirstT·s`, `(1 − isLastT)·(next.s − s − 1)`, `id − pubNA − s` (the serial's own
  definition, as the cell table's `isFirst·idx` / `(1 − isLast)(idx′ − idx − 1)`).  The `𝕂′` gates read `id` only as
  an RLC key entry.  Positive controls.
  **Provider filter.** `splitProvs` keeps rows with `m ≠ 0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Chips.RowModel
import Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Columns -/

def isFT : ℕ := 0
def isLT : ℕ := 1
def ctr : ℕ := 2
def sid : ℕ := 3
def hi : ℕ := 4
def lo : ℕ := 5
/-- Bit `b_i` sits at column `bit0 + i` (`lo` bits `b_0 .. b_31`, `hi` bits `b_32 .. b_63`). -/
def bit0 : ℕ := 6
def invHi : ℕ := 70
def mult : ℕ := 71

def baseW : ℕ := 72

def inv2 : ℕ := 0
def inv3 : ℕ := 2
def acc : ℕ := 4

/-- The `𝕂′` terminal public (net provides). -/
def pubSPs : ℕ := 0

def serialColsSp : List ℕ := [ctr, sid]

/-- **The split value**: `hi.val·B + lo.val` in ℕ, `B = 2^32` (`Nock.Atoms.B`), read off a row's `hi`, `lo` limbs. -/
def splitValN (hiN loN : ℕ) : ℕ := hiN * 2 ^ 32 + loN

theorem layout_tiles : bit0 + 64 = invHi ∧ invHi + 1 = mult ∧ mult + 1 = baseW ∧ lo + 1 = bit0 := by decide

/-! ## 2. Gates -/

section Gates
variable {F : Type} [Field F]

/-- The 64 bit booleanities. -/
def bitBool : List (CoeffExpr F) := (List.range 64).map fun i => boolE (cv (bit0 + i))

/-- The limb decodes `hi − Σ_{i<32} 2^i b_{32+i}`, `lo − Σ_{i<32} 2^i b_i`. -/
def decode : List (CoeffExpr F) :=
  [ .sub (cv hi) (bitSum (bit0 + 32) 32), .sub (cv lo) (bitSum bit0 32) ]

/-- **The counter class** (the only serial readers): `isFirstT·s`, `(1 − isLastT)·(next.s − s − 1)`,
`id − pubNA − s` with `pubNA := nA` a template parameter (F2). -/
def counter (nA : ℕ) : List (CoeffExpr F) :=
  [ .mul (cv isFT) (cv ctr),
    .mul (notE (cv isLT)) (.sub (.sub (nv ctr) (cv ctr)) (.const 1)),
    .sub (.sub (cv sid) (.const (nA : F))) (cv ctr) ]

/-- `hi·invHi − 1` (a nonzero top limb: the comb is canonical, `v ≥ 2^32`). -/
def hiNZ : List (CoeffExpr F) := [ .sub (.mul (cv hi) (cv invHi)) (.const 1) ]

/-- **The split chip's base gates** (`64 + 2 + 3 + 1 = 70`). -/
def baseGates (nA : ℕ) : List (CoeffExpr F) := bitBool ++ decode ++ counter nA ++ hiNZ

/-- The two provided records `(id, 2, 0, lo)`, `(id, 3, 0, hi)`. -/
def key2 : List (CoeffExpr F) := [cv sid, .const 2, .const 0, cv lo]
def key3 : List (CoeffExpr F) := [cv sid, .const 3, .const 0, cv hi]

def pTerm (cur : Bool) : QE F :=
  if cur then QE.scale (cv mult) (QE.add (QE.var inv2) (QE.var inv3))
  else QE.scale (nv mult) (QE.add (QE.next inv2) (QE.next inv3))

/-- **The split chip's `𝕂′` equations.** -/
def spQ (δF : F) : List (QE F) :=
  [ QE.sub (QE.mul δF (QE.var inv2) (HQ.denKeyQ δF key2)) QE.one,
    QE.sub (QE.mul δF (QE.var inv3) (HQ.denKeyQ δF key3)) QE.one,
    QE.scale (cv isFT) (QE.sub (QE.var acc) (pTerm true)),
    QE.scale (notE (cv isLT)) (QE.sub (QE.sub (QE.next acc) (QE.var acc)) (pTerm false)),
    QE.scale (cv isLT) (QE.sub (QE.var acc) (QE.pub pubSPs)) ]

def spMixed (δF : F) : List (MixedExpr F) := (spQ δF).flatMap QE.gates

theorem bitSum_deg (base n : ℕ) : (bitSum base n : CoeffExpr F).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ 1 fun i _ => by simp [CoeffExpr.degree]

theorem baseGates_deg_all (nA : ℕ) : (baseGates (F := F) nA).all (fun g => decide (g.degree ≤ 4)) = true := by
  have h1 := bitSum_deg (F := F) (bit0 + 32) 32
  have h2 := bitSum_deg (F := F) bit0 32
  simp [baseGates, bitBool, decode, counter, hiNZ, CoeffExpr.degree, List.all_eq_true]
  omega

theorem baseGates_deg (nA : ℕ) : ∀ g ∈ (baseGates (F := F) nA), g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp (baseGates_deg_all nA) g hg

theorem spMixed_deg_all (δF : F) : (spMixed δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [spMixed, spQ, pTerm, key2, key3, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ, QE.gates, QE.var,
    QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree,
    CoeffExpr.degree]

theorem spMixed_deg (δF : F) : ∀ g ∈ spMixed δF, g.degree ≤ 4 := by
  intro g hg; simpa using List.all_eq_true.mp (spMixed_deg_all δF) g hg

theorem baseGates_length (nA : ℕ) : (baseGates (F := F) nA).length = 70 := by
  simp [baseGates, bitBool, decode, counter, hiNZ]

theorem spMixed_length (δF : F) : (spMixed δF).length = 10 := by
  simp [spMixed, spQ, QE.gates]

/-- **The split chip template**, `pubNA := nA` a template parameter (F2). -/
def splitTemplateJ9 (δF : F) (nA : ℕ) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![72, 0, 0]
  extColsOf := ![0, 0, 6]
  baseTransition := baseGates nA
  extTransition := []
  mixedTransition := spMixed δF
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGates_deg nA
  extTransition_deg := by simp
  mixedTransition_deg := spMixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem splitTemplateJ9_baseCols (δF : F) (nA : ℕ) : (splitTemplateJ9 δF nA).baseCols = 72 := by
  show (∑ r : Fin 3, (![72, 0, 0] : Fin 3 → ℕ) r) = 72
  decide
theorem splitTemplateJ9_extCols (δF : F) (nA : ℕ) : (splitTemplateJ9 δF nA).extCols = 6 := by
  show (∑ r : Fin 3, (![0, 0, 6] : Fin 3 → ℕ) r) = 6
  decide

/-- **`gates_degree ≤ 4`.** -/
theorem gates_degree (δF : F) (nA : ℕ) :
    (∀ g ∈ (splitTemplateJ9 δF nA).baseTransition, g.degree ≤ 4) ∧
      (∀ g ∈ (splitTemplateJ9 δF nA).mixedTransition, g.degree ≤ 4) :=
  ⟨baseGates_deg nA, spMixed_deg δF⟩


/-- Every base gate reads only columns `≤ invHi`. -/
theorem baseGates_cols :
    (baseGates (F := ℚ) 5).all (fun g => (colsOfB g).all fun c => decide (c < invHi + 1)) = true := by
  decide +kernel

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`splitChipJ9`** (`nA` the verifier-written public `pubNA`, a template parameter; masks at `0`, `1`). -/
noncomputable def splitChipJ9 (δF : F) (nA : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (splitTemplateJ9 δF nA) b (slotVal b 72 chals) (slotVal b 72 pubs) orbit (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 72 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (nA : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **`width_eq`: `w = 90`** (`72 + 6·3`), by `rfl`. -/
theorem width_eq : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w = 90 := rfl

/-- **Fingerprint**: `w = 90`, `s = 70 + 10·3 = 100`, `d = 4`, `k = 3`. -/
theorem splitChipJ9_fingerprint :
    (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w = 90 ∧
      (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.s = 100 ∧
      (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.d = 4 ∧
      (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.k = 3 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  rw [show (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap =
      expandChip (splitTemplateJ9 δF nA) b _ _ orbit _ from rfl, expandChip_s]
  simp only [splitTemplateJ9, baseGates_length, spMixed_length, List.length_nil]

end Chip

/-! ## 3. The instrument -/

section Instrument
variable {F : Type} [Field F]

def serialFreeSp (g : CoeffExpr F) : Bool := (colsOfB g).all fun i => !serialColsSp.contains i

def coinOnlyS : MixedExpr F → Bool
  | .Var .challenge _ => true
  | .Const _ => true
  | .Scale (.const _) u => coinOnlyS u
  | .Add x y => coinOnlyS x && coinOnlyS y
  | .Sub x y => coinOnlyS x && coinOnlyS y
  | .Mul x y => coinOnlyS x && coinOnlyS y
  | .Neg x => coinOnlyS x
  | .Pow x _ => coinOnlyS x
  | _ => false

def keyOKSp : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => coinOnlyS x
  | .Var _ _ => true
  | .Lift g => serialFreeSp g
  | .Scale g u => serialFreeSp g && keyOKSp u
  | .Const _ => true
  | .Add x y => keyOKSp x && keyOKSp y
  | .Sub x y => keyOKSp x && keyOKSp y
  | .Mul x y => keyOKSp x && keyOKSp y
  | .Neg x => keyOKSp x
  | .Pow x _ => keyOKSp x


/-- The arithmetic gates (`bitBool`, `decode`, `hiNZ`) read no serial column. -/
theorem arith_serialFree : ((bitBool (F := ℚ)) ++ decode ++ hiNZ).all serialFreeSp = true := by decide +kernel

/-- **The counter class is the only serial reader**: each of its three gates reads a serial (at any `nA`, here
`nA = 5`). -/
theorem counter_reads_serial : (counter (F := ℚ) 5).all (fun g => !serialFreeSp g) = true := by decide +kernel


/-- Every mixed gate of the split chip passes the key check `keyOKSp`. -/
theorem spMixed_keyOK : (spMixed (F := ℚ) 7).all keyOKSp = true := by decide +kernel


/-- The mixed gates of the split chip read only the columns `sid, lo, hi, isFT, isLT, mult`. -/
theorem spMixed_reads :
    (spMixed (F := ℚ) 7).all (fun g => (liftCols g).all fun c => [sid, lo, hi, isFT, isLT, mult].contains c) = true := by
  decide +kernel

/-- **Positive control 1**: `serialFreeSp` flags arithmetic on `id`. -/
theorem serialFreeSp_flags : serialFreeSp (F := ℚ) (.mul (cv sid) (cv hi)) = false := by decide +kernel

/-- **Positive control 2**: the `𝕂′` instrument flags a denominator multiplied by `id`. -/
theorem keyOKSp_flags : ((QE.mul (7 : ℚ) (HQ.denKeyQ 7 key2) (QE.base (cv sid))).gates).all keyOKSp = false := by
  decide +kernel

/-- **Positive control 3**: the read-set instrument sees a bit column. -/
theorem spMixed_reads_control :
    ((spMixed (F := ℚ) 7 ++ (QE.mul (7 : ℚ) (QE.var inv2) (QE.base (cv bit0))).gates).all
      (fun g => (liftCols g).all fun c => [sid, lo, hi, isFT, isLT, mult].contains c)) = false := by decide +kernel

end Instrument

/-! ## 4. Row environments and the provider list -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (nA : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → F[X])

abbrev spEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 72 chals) (slotVal b 72 pubs)

abbrev spEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((splitTemplateJ9 δF nA).col0 3) (spEF b nodes orbit chals pubs Q' i)

theorem sp_base (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ g ∈ (baseGates nA : List (CoeffExpr F)), g.eval (spEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (splitTemplateJ9 δF nA) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact hl.1

theorem sp_qgates (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ spQ δF, e.ev δF (spEK δF nA b nodes orbit chals pubs Q i) (spEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (splitTemplateJ9 δF nA) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg => hl.2.2.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)

theorem sp_masks (hbind : (splitChipJ9 δF nA b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (spEF b nodes orbit chals pubs Q i).trace isFT = (if (i : ℕ) = 0 then 1 else 0) ∧
      (spEF b nodes orbit chals pubs Q i).trace isLT = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w = 90 := width_eq δF nA b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact TeleH.masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

/-- A key read off a base environment, lifted to `𝕂`, zero-padded to width `w'`. -/
def keyVecL (w' : ℕ) (key : List (CoeffExpr F)) (eF : Env F) : Fin w' → K :=
  fun c => algebraMap F K ((key.getD c (.const 0)).eval eF)

/-- **The split providers** (rows with `m ≠ 0`; two records per row, weight `m`). -/
def splitProvs [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 8 → K) × K) :=
  (List.finRange n).flatMap fun i =>
    if (spEF b nodes orbit chals pubs Q' i).trace mult = 0 then [] else
      [(keyVecL 8 key2 (spEF b nodes orbit chals pubs Q' i), algebraMap F K ((spEF b nodes orbit chals pubs Q' i).trace mult)),
       (keyVecL 8 key3 (spEF b nodes orbit chals pubs Q' i), algebraMap F K ((spEF b nodes orbit chals pubs Q' i).trace mult))]

end Rows


/-! ## 5. Row lemmas (the S2 steps: bits, counter, id, `hi ≠ 0`, the 2-limb comb) -/

section RowLemmas
variable {F : Type} [Field F]

/-- **Every base gate of the split chip, as a field equation at one row.** -/
structure SpRowEqs (nA : ℕ) (e : Env F) : Prop where
  bits : ∀ i < 64, e.trace (bit0 + i) * (e.trace (bit0 + i) - 1) = 0
  dhi : e.trace hi = ∑ i ∈ Finset.range 32, (2 : F) ^ i * e.trace (bit0 + 32 + i)
  dlo : e.trace lo = ∑ i ∈ Finset.range 32, (2 : F) ^ i * e.trace (bit0 + i)
  c0 : e.trace isFT * e.trace ctr = 0
  c1 : (1 - e.trace isLT) * (e.traceNext ctr - e.trace ctr - 1) = 0
  cid : e.trace sid = (nA : F) + e.trace ctr
  nz : e.trace hi * e.trace invHi = 1

theorem spRowEqs_of {nA : ℕ} {e : Env F} (hg : ∀ g ∈ (baseGates nA : List (CoeffExpr F)), g.eval e = 0) :
    SpRowEqs nA e := by
  have hb : ∀ g ∈ (bitBool : List (CoeffExpr F)), g.eval e = 0 := fun g h =>
    hg g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have hd : ∀ g ∈ (decode : List (CoeffExpr F)), g.eval e = 0 := fun g h =>
    hg g (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have hc : ∀ g ∈ (counter nA : List (CoeffExpr F)), g.eval e = 0 := fun g h =>
    hg g (List.mem_append_left _ (List.mem_append_right _ h))
  have hz : ∀ g ∈ (hiNZ : List (CoeffExpr F)), g.eval e = 0 := fun g h => hg g (List.mem_append_right _ h)
  simp only [decode, counter, hiNZ, List.forall_mem_cons, List.forall_mem_nil, List.mem_nil_iff, false_implies,
    implies_true, and_true] at hd hc hz
  obtain ⟨d1, d2⟩ := hd
  obtain ⟨k1, k2, k3⟩ := hc
  simp only [CoeffExpr.eval, eval_bitSum, cv, nv, notE] at d1 d2 k1 k2 k3 hz
  refine ⟨fun i hi => ?_, by linear_combination d1, by linear_combination d2, k1, k2,
    by linear_combination k3, by linear_combination hz⟩
  have := hb _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simpa only [boolE, CoeffExpr.eval, cv] using this

theorem sp_rowEqs {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] (δF : F) (nA : ℕ)
    (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K) (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    SpRowEqs nA (spEF b nodes orbit chals pubs Q i) := by
  have hl := (expandChip_satisfies_iff_language (splitTemplateJ9 δF nA) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact spRowEqs_of hl.1

/-- **The row counter**: under the masks and row adjacency, row `i` has `ctr = i` and `sid = nA + i`. -/
theorem sp_ctr {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] (δF : F)
    [Fact (¬ IsSquare (algebraMap F K δF))] (nA : ℕ)
    (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K) (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (splitChipJ9 δF nA b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (i : Fin n) :
    (spEF b nodes orbit chals pubs Q i).trace ctr = ((i : ℕ) : F) ∧
      (spEF b nodes orbit chals pubs Q i).trace sid = ((nA + (i : ℕ) : ℕ) : F) := by
  have H := sp_rowEqs δF nA b hn nodes orbit chals pubs Q hsat
  have hM := sp_masks δF nA b hn nodes orbit chals pubs Q hbind hinj
  have hc : ∀ k (hk : k < n), (spEF b nodes orbit chals pubs Q ⟨k, hk⟩).trace ctr = (k : F) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := (H ⟨0, hk⟩).c0
      rw [(hM ⟨0, hk⟩).1, if_pos rfl, one_mul] at h0
      simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have h1 := (H ⟨k, hk'⟩).c1
      rw [(hM ⟨k, hk'⟩).2, if_neg (show ¬ k = n - 1 by omega), sub_zero, one_mul,
        traceNext_eq nodes orbit Q _ _ hadj ⟨k, hk'⟩ hk ctr, ih hk'] at h1
      push_cast
      linear_combination h1
  have hci := hc i i.isLt
  refine ⟨hci, ?_⟩
  rw [(H i).cid, hci]; push_cast; ring

end RowLemmas

/-! ## 6. ℕ-level split facts at `ZMod p` (S2) -/

section Nat
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combL combN)
variable {p : ℕ} [Fact p.Prime]

theorem limb_val_lt (hp : 2 ^ 32 < p) {x : ZMod p} (bits : ℕ → ZMod p) (hb : ∀ i < 32, bits i * (bits i - 1) = 0)
    (hx : x = ∑ i ∈ Finset.range 32, (2 : ZMod p) ^ i * bits i) : x.val < 2 ^ 32 := by
  obtain ⟨s, hs, hsum⟩ := Chips.CertBound.bits_sum_nat bits 32 hb
  rw [hx, ← hsum, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  exact hs

/-- **S2 step 1**: both limbs are below `B = 2^32`, and the top limb is nonzero. -/
theorem sp_limbs (hp : 2 ^ 32 < p) {nA : ℕ} {e : Env (ZMod p)} (H : SpRowEqs nA e) :
    (e.trace hi).val < 2 ^ 32 ∧ (e.trace lo).val < 2 ^ 32 ∧ (e.trace hi).val ≠ 0 := by
  refine ⟨limb_val_lt hp (fun i => e.trace (bit0 + 32 + i)) (fun i hi => ?_) H.dhi,
    limb_val_lt hp (fun i => e.trace (bit0 + i)) (fun i hi => H.bits i (by omega)) H.dlo, ?_⟩
  · have := H.bits (32 + i) (by omega); rwa [← add_assoc] at this
  · intro h0
    have := H.nz
    rw [(ZMod.val_eq_zero _).mp h0, zero_mul] at this
    exact zero_ne_one this

/-- **S2 step 6**: the split value's canonical comb is the 2-limb cell `[lo hi]`: `slot 2 = lo`, `slot 3 = hi`. -/
theorem splitVal_comb {hiN loN : ℕ} (hhi : hiN < 2 ^ 32) (hlo : loN < 2 ^ 32) (hnz : hiN ≠ 0) :
    combN (splitValN hiN loN) = Noun.cell (.atom loN) (.atom hiN) ∧
      Noun.slot 2 (combN (splitValN hiN loN)) = some (.atom loN) ∧
      Noun.slot 3 (combN (splitValN hiN loN)) = some (.atom hiN) := by
  have hd : Nat.digits Nock.Atoms.B (splitValN hiN loN) = [loN, hiN] := by
    have hB : Nock.Atoms.B = 2 ^ 32 := rfl
    rw [splitValN, ← hB, show hiN * Nock.Atoms.B + loN = loN + Nock.Atoms.B * hiN by ring,
      Nat.digits_add _ Nock.Atoms.one_lt_B _ _ (by rw [hB]; exact hlo) (Or.inr hnz),
      Nat.digits_of_lt _ _ hnz (by rw [hB]; exact hhi)]
  have hc : combN (splitValN hiN loN) = Noun.cell (.atom loN) (.atom hiN) := by
    rw [combN, hd]; rfl
  refine ⟨hc, ?_, ?_⟩ <;> rw [hc] <;> simp [Noun.slot]

end Nat

end

end Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9
