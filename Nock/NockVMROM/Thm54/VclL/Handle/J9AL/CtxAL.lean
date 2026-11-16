/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/CtxAL.lean

  **The per-call semantics `hsem` of `AluShareAL.jetProv_ok`
  from `AluSZOps`'s `op_sound6`.**

  * `alR R`: the window's FULL readout (every column), so `Readout R (alR R)` holds (`readout_alR`).
  * **`AluSZOps` gap (i) workaround** (`AluBaseAL`): `op_sound6` is run at the CONSTANT readouts `fun _ => X.al`,
    `fun _ => X.t` (its own `arithSZ` instance at `Tr := Unit`); its event is the consumed one (`RR49AL.arithAL`,
    built on the coin-free base readout `aluAL`) because the two readouts agree on the base columns
    (`agree_alR`, `AluBaseAL.arithBadC_agree`): `event_of_arithAL`.
  * **`AluSZOps` gap (ii) workaround** (`AtomWalkAL`): `Ctx.r` is the padded reader `rStar rA nA`; its `HDen` facts move to
    the J-9 A denotation `denJ9A … rA V` by `HDen.denK` and `extB_rStar` (`hden_D`).
  * **`hsem_of_ctx`**: at an `AluSZOps` context `X` over the window `R` with `X.al = alR R`, `X.t = atomAL r Pb tr`,
    `X.r = rStar rA nA`, outside the consumed `arithAL`, every `hdr` row with op flag `op` has
    `D (kA, vA) = a`, `D (kB, vB) = b`, `D (kE, vE) = c` atoms with `primSem op a b = some c`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluShareAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluBaseAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AtomWalkAL
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZOpsMD
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.DenJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CtxAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (Rows Readout Ctx ALRow opColOf op_sound6 eFn eFn_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent (cl rowAt arithBadC)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.Jet.Prim (PrimOp primSem)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The full readout -/

section Readout
variable {K : Type} [Field K] [Algebra Fp K] {δ : Fp} [Fact (¬ IsSquare (algebraMap Fp K δ))]

/-- **The window's full readout**: row `i` is every column of `R.eF i`. -/
def alR (R : Rows δ K) : List ALRow := List.ofFn fun i : Fin R.n => fun j => R.v i j

theorem cl_alR (R : Rows δ K) {i : ℕ} (hi : i < R.n) (j : ℕ) : cl (alR R) i j = R.v i j := by
  simp only [cl, rowAt, alR]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem readout_alR (R : Rows δ K) : Readout R (alR R) :=
  ⟨by simp [alR], fun i hi j => cl_alR R hi j⟩

theorem len_alR (R : Rows δ K) : (alR R).length = R.n := by simp [alR]

end Readout

/-! ## 2. The consumed event is `op_sound6`'s (`AluSZOps` gap (i)) -/

section Event
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K] [Algebra Fp (Quad (algebraMap Fp K δ))]

/-- The window `R` of the ALU view `qAL … chals pubs` (`AluSZOps.rowsOf`) reads, on its base columns, what the
coin-free readout `RR49AL.aluAL` reads (`nL ≤ AL`: the `take` is the identity). -/
theorem agree_alR {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {r : RowsJ9AL}
    (R : Rows δ K) (hn : R.n = Pb.nL)
    (hv : ∀ i (hi : i < Pb.nL), ∀ j < 94, R.v i j = (alE0 (K := K) δ b Pb tr ⟨i, hi⟩).trace j)
    (hAL : Pb.nL ≤ r.AL) :
    AluBaseAL.Agree94 (alR R) (RR49AL.aluAL (K := K) δ b r Pb tr) := by
  have hF := GeneratedField.primeFieldElems_zmod Nock.Atoms.p
  have hlen : (RR49AL.aluAL (K := K) δ b r Pb tr).length = Pb.nL := by
    simp [RR49AL.aluAL, List.length_take, List.length_ofFn]; omega
  refine ⟨by rw [len_alR, hlen, hn], fun i j hj => ?_⟩
  by_cases hi : i < Pb.nL
  · rw [cl_alR R (by omega) j, hv i hi j hj]
    have e : (RR49AL.aluAL (K := K) δ b r Pb tr).getD i (fun _ => 0) = fun j =>
        if j < 94 then ((Chips.ChipRAP.natOf ((alE0 (K := K) δ b Pb tr ⟨i, hi⟩).trace j) : ℕ) : Fp) else 0 := by
      simp [RR49AL.aluAL, List.getD_eq_getElem?_getD, List.getElem?_take, show i < r.AL by omega, hi]
    show _ = ((RR49AL.aluAL (K := K) δ b r Pb tr).getD i (fun _ => 0)) j
    rw [e]; dsimp only; rw [if_pos hj]
    exact (Chips.ChipRAP.natOf_cast hF _).symm
  · simp only [cl, rowAt]
    rw [List.getD_eq_default _ _ (by rw [len_alR, hn]; omega), List.getD_eq_default _ _ (by omega)]

/-- **The consumed event `arithAL` is `op_sound6`'s at the constant readouts**: outside `arithAL`, the tower seed
`(χ_{cY1}, χ_{cY2})` avoids `arithBadC (alR R) (atomAL r Pb tr)`. -/
theorem event_of_arithAL {Pb : PubJ9AL Nock.Atoms.p} {r : RowsJ9AL} {tr : TrJ9AL Fp} {χ : Coins frameJ8 K}
    {al : List ALRow} (hag : AluBaseAL.Agree94 al (RR49AL.aluAL (K := K) δ b r Pb tr))
    (hχ : ¬ (RR49AL.arithAL δ b r Pb).mem tr χ) :
    Quad.mk (algebraMap Fp K δ) (χ cY1) (χ cY2) ∉
      arithBadC (Kq := Quad (algebraMap Fp K δ)) al (RR49AL.atomAL r Pb tr) := by
  rw [AluBaseAL.arithBadC_agree hag]
  intro hm
  exact hχ ((AluSZEvent.arithSZ_mem_iff _ _ _ _ _ _ _ _ _ _ _ tr χ).mpr hm)

end Event

/-! ## 3. `HDen` at the padded reader gives the J-9 A denotation (`AluSZOps` gap (ii)) -/

theorem hden_D {rA : ℕ → ARow} {nA : ℕ} {q : ℕ} (tC : List (CellRowB0 q)) (V : ℕ → Option ℕ)
    (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (hpad : ∀ k, nA ≤ k → ∀ l, AtomChipHQ.Denotes rA k l → Nock.Atoms.val l < Nock.Atoms.p)
    {k v : Fp} {n : ℕ} (hd : AluSZOps.Ctx.HDen (AtomWalkAL.rStar rA nA) k v n) :
    DenJ9A.denJ9A tC Nock.Atoms.p rA V (k.val, v.val) = some (.atom n) := by
  have h3 : k.val ≠ 3 := by
    rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp
    · rw [show (2 : Fp) = ((2 : ℕ) : Fp) by norm_num, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by norm_num [Nock.Atoms.p, Nock.Field.p])]; omega
  rw [DenJ9A.denJ9A_ne3 tC _ rA V (k := (k.val, v.val)) h3]
  have e : extB Nock.Atoms.p (AtomWalkAL.rStar rA nA) = extB Nock.Atoms.p rA :=
    funext (AtomWalkAL.extB_rStar hin hpad)
  have := AluSZOps.Ctx.HDen.denK hd tC
  rw [e] at this
  exact this

/-! ## 4. `hsem` from an `AluSZOps` context -/

section Sem
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K] [Algebra Fp (Quad (algebraMap Fp K δ))]

/-- **`hsem` of `jetProv_ok` from an `AluSZOps` context** (see the module header).  The window's rows are the ALU rows:
`hv` says `R.v i j` is the coin-free row's column `j` for every `j` read below (`hvAll`). -/
theorem hsem_of_ctx {Pb : PubJ9AL Nock.Atoms.p} {r : RowsJ9AL} {tr : TrJ9AL Fp} {χ : Coins frameJ8 K}
    {R : Rows δ K} (X : Ctx R) (hn : R.n = Pb.nL)
    (hvAll : ∀ i (hi : i < Pb.nL) (j : ℕ), R.v i j = (alE0 (K := K) δ b Pb tr ⟨i, hi⟩).trace j)
    (hAL : Pb.nL ≤ r.AL) (hal : X.al = alR R) (ht : X.t = RR49AL.atomAL r Pb tr)
    {rA : ℕ → ARow} {nA : ℕ} (hr : X.r = AtomWalkAL.rStar rA nA)
    (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (hpad : ∀ k, nA ≤ k → ∀ l, AtomChipHQ.Denotes rA k l → Nock.Atoms.val l < Nock.Atoms.p)
    (hy : R.y = Quad.mk (algebraMap Fp K δ) (χ cY1) (χ cY2))
    (hχ : ¬ (RR49AL.arithAL δ b r Pb).mem tr χ) {q : ℕ} (tC : List (CellRowB0 q)) (V : ℕ → Option ℕ) :
    ∀ i : Fin Pb.nL, (alE0 (K := K) δ b Pb tr i).trace sH = 1 → ∀ op : PrimOp, op ≠ .dec →
      (alE0 (K := K) δ b Pb tr i).trace (opColOf op) = 1 →
      ∃ na nb nc,
        DenJ9A.denJ9A tC Nock.Atoms.p rA V
          (((alE0 (K := K) δ b Pb tr i).trace kA).val, ((alE0 (K := K) δ b Pb tr i).trace vA).val) =
            some (.atom na) ∧
        DenJ9A.denJ9A tC Nock.Atoms.p rA V
          (((alE0 (K := K) δ b Pb tr i).trace kB).val, ((alE0 (K := K) δ b Pb tr i).trace vB).val) =
            some (.atom nb) ∧
        DenJ9A.denJ9A tC Nock.Atoms.p rA V
          (((alE0 (K := K) δ b Pb tr i).trace kE).val, ((alE0 (K := K) δ b Pb tr i).trace vE).val) =
            some (.atom nc) ∧
        primSem op na nb = some nc := by
  intro i hH op hdec hflag
  have hhn : (i : ℕ) < R.n := by rw [hn]; exact i.2
  have hvi : ∀ j, R.v i j = (alE0 (K := K) δ b Pb tr i).trace j := fun j => hvAll i i.2 j
  have hag : AluBaseAL.Agree94 X.al (RR49AL.aluAL (K := K) δ b r Pb tr) := by
    rw [hal]; exact agree_alR δ b R hn (fun i hi j _ => hvAll i hi j) hAL
  have hev := event_of_arithAL δ b hag hχ
  have hop6 : op = .add ∨ op = .sub ∨ op = .lt ∨ op = .mul ∨ op = .div ∨ op = .mod := by
    cases op <;> simp_all
  have hχ' : ¬ (AluSZEvent.arithSZ (algebraMap Fp K δ) (Tr := Unit) (fun _ => True) (fun _ => X.al) (fun _ => X.t)
      (AluSZEvent.hdrs X.al).length X.t.length X.al.length (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ _ _ _ => ⟨rfl, rfl⟩)).mem () χ := by
    rw [AluSZEvent.arithSZ_mem_iff, ht]
    exact hev
  obtain ⟨na, nb, nc, hA, hB, hE, hs⟩ := op_sound6 X op hop6 (h := (i : ℕ)) hhn (by rw [hvi]; exact hH)
    (by rw [hvi]; exact hflag) () χ rfl rfl hy hχ'
  rw [hvi, hvi] at hA hB hE
  rw [hr] at hA hB hE
  exact ⟨na, nb, nc, hden_D tC V hin hpad hA, hden_D tC V hin hpad hB, hden_D tC V hin hpad hE, hs⟩

end Sem

end

end Nock.NockVMROM.Thm54.VclL.Handle.CtxAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.CtxAL
#print axioms readout_alR
#print axioms agree_alR
#print axioms event_of_arithAL
#print axioms hden_D
#print axioms hsem_of_ctx
end Axioms
