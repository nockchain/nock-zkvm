/-
  Nock/NockVMROM/Thm54/VclL/Handle/ReaderR3bJ8.lean

  **The atom-table reader fields and `hrealA`.**

  * §1 **`hrealA`**: an atom formula never holds (`evalN` on an atom formula is `none`): **`holdsN_formula_cell`**.
    So the public check `isCellN c.formula = true` rejects no true claim, and under it `hrealA` is vacuous
    (`hrealA_of_check`).  (FINDING, argument only: WITHOUT that check `hrealA` is not implied — row 0 may be an
    `s10L` chain state, whose formula handle `(0, 2·v + β)` matches an atom formula `a ≠ 1`, `s10L_row`.)
  * §2 the canonical reader `LinkQ2J8.valReader` of the atom table: **`hidxA_valReader`** (the serial gate),
    **`hB_valReader`** (g1: both limbs are 32-bit sums of boolean bits).
  * §3 **S1, the restatement**: `SmallU` — what the chain lemmas READ: `idx, aL, wR, aR, inc, cout, kRO` on every
    row, `idR` on weighted rows, `idxO, lO, vRO` on inc rows (`chainOK_of_gates`, `oldGenuine_of_served`,
    `agree_atom`; the free cells Q2's `no_small_reader` exhibits — `vRO / lO` on non-inc rows, `idR` on
    unweighted rows — are not in it).  **`smallU_valReader`**: at the canonical reader every table row is
    `SmallU`, from the gates (g1, g70, the cell base gate), the serial gate (`nA ≤ 2^62`), the validity balance
    (`ValidityServed`: a weighted child serial is a row serial) and the export consume (`ConsumeServedQ`: an inc
    row's old copy is a row's export key).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServedAJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads atomChipHQ atomGates LimbsBounded ConsumeServedQ)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (restr_trace)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF atom_base)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader valReader_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (isCellN)
open Nock.Atoms (B)

noncomputable section

/-! ## 1. `hrealA` -/

/-- **An atom formula never holds**: `evalN _ s (atom a) = none`. -/
theorem holdsN_formula_cell (c : P8PublicClaim) (h : Nock.Jet.HoldsN c) : isCellN c.formula = true := by
  obtain ⟨fuel, hf⟩ := h
  cases hc : c.formula with
  | cell _ _ => rfl
  | atom a =>
    rw [hc] at hf
    cases fuel with
    | zero => simp [Nock.evalN] at hf
    | succ n => simp [Nock.evalN] at hf

/-- Under the public check `isCellN c.formula = true`, `LinkJ8'`'s `hrealA` holds vacuously. -/
theorem hrealA_of_check {c : P8PublicClaim} {X : Prop} (h : isCellN c.formula = true) :
    isCellN c.formula = false → X := by
  intro h'; rw [h] at h'; exact absurd h' (by decide)

/-! ## 2. The canonical reader: `hidxA`, `hB` -/

section Reader
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA
local notation "QR" => AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA
local notation "tA" => cellTableOf δ b nodesA orbitA chalsA pubsA QR

theorem natOf_eq_val (x : ZMod p) : natOf x = x.val := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have h := natOf_natCast hF (k := x.val) (by rw [ZMod.ringChar_zmod_n]; exact ZMod.val_lt x)
  rwa [ZMod.natCast_zmod_val] at h

/-- Row `k`'s cell-table row has serial `k` (`cellTable_serial`). -/
theorem tA_idx (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (k : Fin nA) : ((AE k).trace Cell.idx).val = k := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hs := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsat) hF
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbind) hinj hadj
    (by rw [hrc]; exact hnp)
  have hlen : (tA).length = nA := by simp [cellTableOf]
  have h1 := List.getElem_of_eq hs (i := k) (by simp [hlen])
  simp only [List.getElem_map, List.getElem_range, cellTableOf, List.getElem_ofFn, cellRowOf, cellB0Of,
    Fin.eta] at h1
  rw [restr_trace δ b hnA nodesA orbitA chalsA pubsA QA k (by decide), natOf_eq_val] at h1
  exact h1

/-- **L5 `hidxA`** at the canonical reader. -/
theorem hidxA_valReader (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) : ∀ k : Fin nA, (valReader AE k).idx = k := by
  intro k
  rw [valReader_lt]
  exact tA_idx hsat hbind hinj hadj hnp k

/-- g1: both limbs of a table row are below `B = 2^32`. -/
theorem limbs_lt_B (hp : 2 ^ 32 ≤ p) (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (k : Fin nA) : ((AE k).trace Cell.aL).val < B ∧ ((AE k).trace Cell.aR).val < B := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg := atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat k
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have gA := g (.sub (cv Cell.aL) (bitSum AtomChipHQ.bitA 32)) (by simp [atomGates, AtomChipHQ.g1])
  have gR := g (.sub (cv Cell.aR) (bitSum AtomChipHQ.bitR 32)) (by simp [atomGates, AtomChipHQ.g1])
  have hbit : ∀ i < 64, (AE k).trace (AtomChipHQ.bitA + i) * ((AE k).trace (AtomChipHQ.bitA + i) - 1) = 0 := by
    intro i hi
    have := g (boolE (cv (AtomChipHQ.bitA + i))) (by
      simp only [atomGates, AtomChipHQ.g1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))))))))
    simpa [boolE, cv, CoeffExpr.eval] using this
  simp only [CoeffExpr.eval, cv, sub_eq_zero] at gA gR
  have hBe : B = 2 ^ 32 := by rfl
  refine ⟨?_, ?_⟩
  · rw [← natOf_eq_val, gA, hBe]
    exact bitSum_nat hF _ 32 _ (fun i hi => hbit i (by omega)) (by rw [hrc]; exact hp)
  · rw [← natOf_eq_val, gR, hBe]
    refine bitSum_nat hF _ 32 _ (fun i hi => ?_) (by rw [hrc]; exact hp)
    have := hbit (32 + i) (by omega)
    rwa [show AtomChipHQ.bitA + (32 + i) = AtomChipHQ.bitR + i by simp [AtomChipHQ.bitA, AtomChipHQ.bitR]; omega]
      at this

/-- **L5 `hB`** at the canonical reader (padding rows `(0, 1)`). -/
theorem hB_valReader (hp : 2 ^ 32 ≤ p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA) : LimbsBounded (valReader AE) := by
  intro j
  by_cases hj : j < nA
  · have h := valReader_lt AE ⟨j, hj⟩
    simp only at h
    rw [h]
    exact limbs_lt_B hp hsat ⟨j, hj⟩
  · simp [valReader, hj, B]

end Reader

/-! ## 3. S1: the restated smallness and its derivation at the canonical reader -/

/-- **S1, restated**: the row values the chain lemmas read are small — `idx, aL, wR, aR, inc, cout, kRO` on every
row, `idR` on a weighted row, the old copy `idxO, lO, vRO` on an inc row. -/
def SmallU (a : ARow) : Prop :=
  a.idx < 2 ^ 62 ∧ a.aL < 2 ^ 62 ∧ a.wR < 2 ^ 62 ∧ a.aR < 2 ^ 62 ∧ a.inc < 2 ^ 62 ∧ a.cout < 2 ^ 62 ∧
    a.kRO < 2 ^ 62 ∧ (a.wR = 1 → a.idR < 2 ^ 62) ∧ (a.inc = 1 → a.idxO < 2 ^ 62 ∧ a.lO < 2 ^ 62 ∧ a.vRO < 2 ^ 62)

/-- `Small` (the old field) implies `SmallU`: the restatement only drops obligations. -/
theorem smallU_of_small {a : ARow} (h : a.Small) : SmallU a := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := h
  exact ⟨s1, s2, s3, s5, s6, s7, s10, fun _ => s4, fun _ => ⟨s8, s9, s11⟩⟩

section Small
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA
local notation "QR" => AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA
local notation "tA" => cellTableOf δ b nodesA orbitA chalsA pubsA QR

theorem val_le_one_of_bool {x : ZMod p} (h : x * (x - 1) = 0) : x.val ≤ 1 := by
  rcases mul_eq_zero.mp h with h0 | h1
  · simp [h0]
  · rw [sub_eq_zero.mp h1, ZMod.val_one]

/-- A g70 booleanity gate at a row. -/
theorem atom_bool (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA) (k : Fin nA)
    {c : ℕ} (hc : boolE (cv c) ∈ (atomGates : List (CoeffExpr (ZMod p)))) :
    ((AE k).trace c).val ≤ 1 := by
  have hg := atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat k
  have := hg _ (List.mem_append_right _ hc)
  exact val_le_one_of_bool (by simpa [boolE, cv, CoeffExpr.eval] using this)

/-- **A weighted child serial is a row serial** (`ValidityServed`): `wR = 1 ⇒ idR < nA`. -/
theorem idR_lt_of_served (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hserved : ValidityServed (tA)) (k : Fin nA) (hw : (AE k).trace Cell.wR = 1) :
    ((AE k).trace Cell.idR).val < nA := by
  have hmem : cellRowOf δ (cellEnvK δ b nodesA orbitA chalsA pubsA QR k)
      (cellEnvF b nodesA orbitA chalsA pubsA QR k) ∈ tA := List.mem_ofFn.mpr ⟨k, rfl⟩
  have hwb : (cellRowOf δ (cellEnvK δ b nodesA orbitA chalsA pubsA QR k)
      (cellEnvF b nodesA orbitA chalsA pubsA QR k)).b0.wR = true := by
    simp only [cellRowOf, cellB0Of, decide_eq_true_eq]
    rw [restr_trace δ b hnA nodesA orbitA chalsA pubsA QA k (by decide)]; exact hw
  obtain ⟨c', hc', -, -, -, hid⟩ := (hserved _ hmem).2 hwb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc'
  simp only [cellRowOf, cellB0Of] at hid
  rw [restr_trace δ b hnA nodesA orbitA chalsA pubsA QA k (by decide),
    restr_trace δ b hnA nodesA orbitA chalsA pubsA QA j (by decide), natOf_eq_val, natOf_eq_val,
    tA_idx hsat hbind hinj hadj hnp j] at hid
  rw [hid]; exact j.2

/-- **S1 derived**: at the canonical reader every table row is `SmallU`, from the gates, the serial gate
(`nA ≤ 2^62`), `ValidityServed` and the export consume `ConsumeServedQ`. -/
theorem smallU_valReader (hp : 2 ^ 63 < p) (hn62 : nA ≤ 2 ^ 62)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hserved : ValidityServed (tA))
    (hcs : ConsumeServedQ (AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA) nA) :
    ∀ k : Fin nA, SmallU (valReader AE k) := by
  have hnp : nA < p := by omega
  have hBe : B = 2 ^ 32 := rfl
  have env_lt := AtomServedQ.atomEnvN_lt b hnA nodesA orbitA chalsA pubsA QA
  have one_val : (1 : ZMod p).val = 1 := ZMod.val_one p
  have of_val1 : ∀ {x : ZMod p}, x.val = 1 → x = 1 := fun h => ZMod.val_injective p (h.trans one_val.symm)
  have hidR : ∀ k : Fin nA, ((AE k).trace Cell.wR).val = 1 → ((AE k).trace Cell.idR).val < 2 ^ 62 :=
    fun k h => lt_of_lt_of_le (idR_lt_of_served hsat hbind hinj hadj hnp hserved k (of_val1 h)) hn62
  have hbw : ∀ k : Fin nA, ((AE k).trace Cell.wR).val ≤ 1 := fun k =>
    val_le_one_of_bool (LinkQ2J8.atom_wR_bool hsat k)
  intro k
  rw [valReader_lt]
  unfold SmallU
  dsimp only
  have hl := limbs_lt_B (by omega) hsat k
  refine ⟨?_, by omega, by have := hbw k; omega, by omega, ?_, ?_, ?_, hidR k, ?_⟩
  · rw [tA_idx hsat hbind hinj hadj hnp k]; omega
  · have := atom_bool hsat k (c := AtomChipHQ.inc) (by simp [atomGates, AtomChipHQ.g70]); omega
  · have := atom_bool hsat k (c := AtomChipHQ.cout) (by simp [atomGates, AtomChipHQ.g70]); omega
  · have := atom_bool hsat k (c := AtomChipHQ.kRO) (by simp [atomGates, AtomChipHQ.g70]); omega
  · intro hinc
    obtain ⟨j, hj, hkey⟩ := hcs k k.2 (by rw [env_lt k]; exact of_val1 hinc)
    rw [show j = ((⟨j, hj⟩ : Fin nA) : ℕ) from rfl, env_lt ⟨j, hj⟩, env_lt k] at hkey
    have hwL := (AtomCombJ8.atom_g23 hsat ⟨j, hj⟩).1
    simp only [CellH.keyH, AtomChipHQ.oldKey, CellH.valE, List.map_cons, List.map_nil, CoeffExpr.eval, cv,
      notE, List.cons.injEq, and_true, hwL] at hkey
    obtain ⟨e1, -, e3, -, e5⟩ := hkey
    have hlj := limbs_lt_B (by omega) hsat ⟨j, hj⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← e1, tA_idx hsat hbind hinj hadj hnp ⟨j, hj⟩]; omega
    · rw [← e3]; simp only [zero_mul, sub_zero, one_mul, zero_add]; omega
    · rw [← e5]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hbw ⟨j, hj⟩) with h | h
      · have h0 : (AE ⟨j, hj⟩).trace Cell.wR = 0 := (ZMod.val_eq_zero _).mp h
        rw [h0]; simp only [zero_mul, sub_zero, one_mul, zero_add]; omega
      · have h1 := of_val1 h
        rw [h1]; simp only [one_mul, sub_self, zero_mul, add_zero]
        exact hidR ⟨j, hj⟩ h

end Small

end

end Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8
