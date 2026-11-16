/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComapJ9A.lean

* `crC9_oldCol`: the twin's old columns keep their J-8 rounds; `stJ8_toJ8`: `StJ9A Q → StJ8 (toJ8 ∘ Q)`;
    `st40_comap`: the same through `St40`.
  * `DataJ8.comap`, `Data40J8.comap`, `DataJ8C.comap`: any J-8 readout record precomposed with a staging-preserving
    `f : Tr' → Tr` (every field `R.x (f tr)`, every reads/const proof `R.x_reads (f ∘ Q) (hf Q hQ)`), and the
    `toJ8` instances `…comapA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (DataJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)

/-! ## 1. Staging along `toJ8` -/

theorem crC9_oldCol (j : Fin 123) : crC9 (oldCol j) = crC j := by
  have hj := j.isLt
  simp only [crC9, oldCol, crC, ChipHX9.permX9]
  split_ifs <;> omega

theorem stJ8_toJ8 {F K : Type} [Field F] {Q : Coins frameJ8 K → TrJ9A F} (hQ : StJ9A Q) :
    StJ8 (fun χ => (Q χ).toJ8) :=
  ⟨fun j χ χ' h => hQ.1 (oldCol j) χ χ' (fun i hi => h i (by rw [← crC9_oldCol]; exact hi)),
    hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2.1, hQ.2.2.2.2.2.1⟩

theorem st40_comap {K Tr Tr' : Type} {St : (Coins frameJ8 K → Tr) → Prop} {St' : (Coins frameJ8 K → Tr') → Prop}
    (f : Tr' → Tr) (hf : ∀ Q, St' Q → St fun χ => f (Q χ)) {Q : Coins frameVSQ K → Tr'} (hQ : St40 St' Q) :
    St40 St fun ψ => f (Q ψ) := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  exact ⟨fun χ => f (Q' χ), hf Q' hQ', y₁, y₂, rfl⟩

/-! ## 2. The readout records along a staging-preserving map -/

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr Tr' : Type} {St : (Coins frameJ8 K → Tr) → Prop} {St' : (Coins frameJ8 K → Tr') → Prop}
  {r : RowsJ8} {P g : ℕ}

/-- **`DataJ8` along `f`.** -/
def DataJ8.comap (R : DataJ8 (q := q) δ Tr St r P) (f : Tr' → Tr) (hf : ∀ Q, St' Q → St fun χ => f (Q χ)) :
    DataJ8 (q := q) δ Tr' St' r P where
  Tr40 := R.Tr40
  St40 := R.St40
  l40 := R.l40
  π40 := fun tr => R.π40 (f tr)
  hπ40 := fun Q' hQ' y₁ y₂ => R.hπ40 _ (hf Q' hQ') y₁ y₂
  eps40 := R.eps40
  valReqs := fun tr χ => R.valReqs (f tr) χ
  valProvs := fun tr χ => R.valProvs (f tr) χ
  val_reads := fun Q hQ => R.val_reads _ (hf Q hQ)
  avReqs := fun tr χ => R.avReqs (f tr) χ
  avProvs := fun tr χ => R.avProvs (f tr) χ
  av_reads := fun Q hQ => R.av_reads _ (hf Q hQ)
  axReqs := fun tr χ => R.axReqs (f tr) χ
  axProvs := fun tr χ => R.axProvs (f tr) χ
  ax_reads := fun Q hQ => R.ax_reads _ (hf Q hQ)
  cxReqs := fun tr χ => R.cxReqs (f tr) χ
  cxProvs := fun tr χ => R.cxProvs (f tr) χ
  cx_reads := fun Q hQ => R.cx_reads _ (hf Q hQ)
  svReqs := fun tr χ => R.svReqs (f tr) χ
  svProvs := fun tr χ => R.svProvs (f tr) χ
  sv_reads := fun Q hQ => R.sv_reads _ (hf Q hQ)
  rowsA := fun tr => R.rowsA (f tr)
  skelA := fun tr => R.skelA (f tr)
  rowsA_le := fun tr => R.rowsA_le (f tr)
  skelA_le := fun tr => R.skelA_le (f tr)
  rowsA_const := fun Q hQ => R.rowsA_const _ (hf Q hQ)
  wdA := fun tr χ => R.wdA (f tr) χ
  wdA_le := fun tr χ => R.wdA_le (f tr) χ
  wdA_reads := fun Q hQ => R.wdA_reads _ (hf Q hQ)
  prs := fun tr => R.prs (f tr)
  prs_le := fun tr => R.prs_le (f tr)
  prs_const := fun Q hQ => R.prs_const _ (hf Q hQ)

/-- **`DataJ8C` along `f`.** -/
def DataJ8C.comap (R : DataJ8C (q := q) δ Tr St r P g) (f : Tr' → Tr) (hf : ∀ Q, St' Q → St fun χ => f (Q χ)) :
    DataJ8C (q := q) δ Tr' St' r P g where
  D := DataJ8.comap R.D f hf
  wdC := fun tr χ => R.wdC (f tr) χ
  wdC_le := fun tr χ => R.wdC_le (f tr) χ
  wdC_reads := fun Q hQ => R.wdC_reads _ (hf Q hQ)

/-- **`Data40J8` along `f`** (staging through `St40`). -/
def Data40J8.comap (L : Data40J8 (q := q) δ Tr St r) (f : Tr' → Tr) (hf : ∀ Q, St' Q → St fun χ => f (Q χ)) :
    Data40J8 (q := q) δ Tr' St' r where
  cRows := fun tr => L.cRows (f tr)
  cH := fun tr => L.cH (f tr)
  cH_le := fun tr => L.cH_le (f tr)
  c_const := fun Q hQ => L.c_const _ (st40_comap f hf hQ)
  rowsD := fun tr => L.rowsD (f tr)
  skelD := fun tr => L.skelD (f tr)
  rowsD_le := fun tr => L.rowsD_le (f tr)
  skelD_le := fun tr => L.skelD_le (f tr)
  rowsD_const := fun Q hQ => L.rowsD_const _ (st40_comap f hf hQ)
  wdW := fun tr ψ => L.wdW (f tr) ψ
  wdW_le := fun tr ψ => L.wdW_le (f tr) ψ
  wdW_reads := fun Q hQ => L.wdW_reads _ (st40_comap f hf hQ)
  fxReqs := fun tr ψ => L.fxReqs (f tr) ψ
  fxProvs := fun tr ψ => L.fxProvs (f tr) ψ
  fx_reads := fun Q hQ => L.fx_reads _ (st40_comap f hf hQ)
  vReqs := fun tr ψ => L.vReqs (f tr) ψ
  vProvs := fun tr ψ => L.vProvs (f tr) ψ
  v_reads := fun Q hQ => L.v_reads _ (st40_comap f hf hQ)
  xReqs := fun tr ψ => L.xReqs (f tr) ψ
  xProvs := fun tr ψ => L.xProvs (f tr) ψ
  x_reads := fun Q hQ => L.x_reads _ (st40_comap f hf hQ)
  pReqs := fun tr ψ => L.pReqs (f tr) ψ
  pProvs := fun tr ψ => L.pProvs (f tr) ψ
  p_reads := fun Q hQ => L.p_reads _ (st40_comap f hf hQ)

end Data

/-! ## 3. The `toJ8` instances -/

section A
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {r : RowsJ8} {P g : ℕ}

abbrev DataJ8C.comapA (R : DataJ8C (q := q) δ (TrJ8 (ZMod p)) StJ8 r P g) :
    DataJ8C (q := q) δ (TrJ9A (ZMod p)) StJ9A r P g :=
  DataJ8C.comap R TrJ9A.toJ8 fun _ hQ => stJ8_toJ8 hQ

abbrev Data40J8.comapA (L : Data40J8 (q := q) δ (TrJ8 (ZMod p)) StJ8 r) :
    Data40J8 (q := q) δ (TrJ9A (ZMod p)) StJ9A r :=
  Data40J8.comap L TrJ9A.toJ8 fun _ hQ => stJ8_toJ8 hQ

end A

end Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A
#print axioms crC9_oldCol
#print axioms stJ8_toJ8
#print axioms st40_comap
#print axioms DataJ8.comap
#print axioms Data40J8.comap
#print axioms DataJ8C.comap
end Axioms
