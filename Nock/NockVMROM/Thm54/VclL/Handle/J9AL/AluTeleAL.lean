/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluTeleAL.lean

  **The three `𝕂′` LogUp telescopes of the ALU `aluSZChipJ9`.** The twin of `J9A/AxisTeleJ9.lean` for the ALU's `logupQ` (`AluSZChipJ9.lean:487-500`):
  * validity `accV`: init `isFT·(accV − aV·invV)`, step `(1 − isLT)·(accV′ − accV − aV′·invV′)`, terminal
    `isLT·(accV − pubALv)` ⇒ `alu_teleV : Σ_i aVᵢ·invVᵢ = pubALv`;
  * export `accX`: the same with `sH·invX` ⇒ `alu_teleX : Σ_i sHᵢ·invXᵢ = pubALx`;
  * service `accS`: the term `wS·invR + wS·invO − sH·mJ·invJ` (`wS = sH − sP·mP`) ⇒ `alu_teleS`.
  The ALU chip is over `Fp` (`Nock.Atoms.Fp`, as `AluSZOps`); the assembly reaches it at `p = Nock.Atoms.p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluTeleAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (aluEF aluEK alu_rowGates alu_width)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] {δ : Fp}
  [Fact (¬ IsSquare (algebraMap Fp K δ))]
  (b : Basis (Fin 3) Fp K) {hO n : ℕ} (hn : 0 < n) (nodes : Fin n → Fp) (orbit : StrictOrbitDomain Fp 3 hO)
  (chals pubs : ℕ → K) (pre : Fin 3 → Fp[X]) (Q : Fin (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w → Fp[X])

local notation "𝕂′" => Quad (algebraMap Fp K δ)

/-- The `𝕂′` value of role pair `r, r + 1` at row `i`. -/
abbrev qv (r : ℕ) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((aluEK b hn nodes orbit chals pubs pre Q i).trace r) ((aluEK b hn nodes orbit chals pubs pre Q i).trace (r + 1))

/-- A base column at row `i`. -/
abbrev fv (j : ℕ) (i : Fin n) : Fp := (aluEF b hn nodes orbit chals pubs pre Q i).trace j

theorem alu_qe (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q) (i : Fin n) {e : QE Fp}
    (he : e ∈ aluQ δ) : e.ev δ (aluEK b hn nodes orbit chals pubs pre Q i) (aluEF b hn nodes orbit chals pubs pre Q i) = 0 :=
  AluSZRead.qe_zero (alu_rowGates b hn nodes orbit chals pubs pre Q hsat i) he

theorem alu_masks (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    fv b hn nodes orbit chals pubs pre Q isFT i = (if (i : ℕ) = 0 then 1 else 0) ∧
      fv b hn nodes orbit chals pubs pre Q isLT i = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have h0 : Q ⟨0, by rw [alu_width]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 5; omega⟩
  have h1 : Q ⟨1, by rw [alu_width]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 5; omega⟩
  exact TeleH.masks_of hn nodes orbit Q _ _ h0 h1 hinj (slotVal b 94 chals) (slotVal b 94 pubs) i

theorem aluEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (aluEF b hn nodes orbit chals pubs pre Q i).traceNext j = (aluEF b hn nodes orbit chals pubs pre Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem aluEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (aluEK b hn nodes orbit chals pubs pre Q i).traceNext r = (aluEK b hn nodes orbit chals pubs pre Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  TeleH.gather_next_T b _ _ _ (aluEF_next b hn nodes orbit chals pubs pre Q hadj i hi) r

theorem aluEK_pub (i : Fin n) (j : ℕ) : (aluEK b hn nodes orbit chals pubs pre Q i).pub j = pubs j :=
  TeleH.gather_pub_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ pubs rfl j

theorem aluEK_chal (i : Fin n) (j : ℕ) : (aluEK b hn nodes orbit chals pubs pre Q i).chal j = chals j :=
  TeleH.gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl j

/-- **A one-column accumulator telescope** (`accG acc pubI (fun c => scale (rdC c s) (rdQ c inv))`):
`Σ_i sᵢ·invᵢ = pubI`. -/
theorem alu_tele1 (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q)
    (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (acc pubI s inv : ℕ)
    (hmem : ∀ e ∈ accG acc pubI (fun c => QE.scale (rdC c s) (rdQ c inv)), e ∈ (aluQ δ : List (QE Fp))) :
    ∑ i, liftQ δ (fv b hn nodes orbit chals pubs pre Q s i) * qv b hn nodes orbit chals pubs pre Q inv i =
      Quad.mk _ (pubs pubI) (pubs (pubI + 1)) := by
  have hg := alu_qe b hn nodes orbit chals pubs pre Q hsat
  refine TeleHQ.qTelescope δ hn (fun i => fv b hn nodes orbit chals pubs pre Q isFT i)
    (fun i => fv b hn nodes orbit chals pubs pre Q isLT i)
    (fun i => qv b hn nodes orbit chals pubs pre Q acc i) _ _
    (fun i => (alu_masks b hn nodes orbit chals pubs pre Q hbind hinj i).1)
    (fun i => (alu_masks b hn nodes orbit chals pubs pre Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (hmem _ (List.Mem.head _))
    simp only [rdC, rdQ, ite_true, ev_scale, ev_sub, ev_var] at g
    simpa only [qv, fv, cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i (hmem _ (List.Mem.tail _ (List.Mem.head _)))
    simp only [rdC, rdQ, Bool.false_eq_true, ite_false, ev_scale, ev_sub, ev_next, ev_var] at g
    simp only [notE, cv, nv, CoeffExpr.eval, aluEK_next b hn nodes orbit chals pubs pre Q hadj i hi,
      aluEF_next b hn nodes orbit chals pubs pre Q hadj i hi] at g
    simpa only [qv, fv, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i (hmem _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    rw [ev_scale, ev_sub, ev_var, ev_pub, aluEK_pub, aluEK_pub] at g
    simpa only [qv, fv, cv, CoeffExpr.eval] using g

/-- **The ALU validity telescope**: `Σ_i aVᵢ·invVᵢ = (pub₀, pub₁)`. -/
theorem alu_teleV (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q)
    (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, liftQ δ (fv b hn nodes orbit chals pubs pre Q aV i) * qv b hn nodes orbit chals pubs pre Q invV i =
      Quad.mk _ (pubs pubALv) (pubs (pubALv + 1)) :=
  alu_tele1 b hn nodes orbit chals pubs pre Q hsat hbind hinj hadj accV pubALv aV invV
    (fun e he => List.mem_append_right _ (by simp only [logupQ, List.mem_append]; tauto))

/-- **The ALU export telescope**: `Σ_i sHᵢ·invXᵢ = (pub₄, pub₅)`. -/
theorem alu_teleX (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q)
    (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, liftQ δ (fv b hn nodes orbit chals pubs pre Q sH i) * qv b hn nodes orbit chals pubs pre Q invX i =
      Quad.mk _ (pubs pubALx) (pubs (pubALx + 1)) :=
  alu_tele1 b hn nodes orbit chals pubs pre Q hsat hbind hinj hadj accX pubALx sH invX
    (fun e he => List.mem_append_right _ (by simp only [logupQ, List.mem_append]; tauto))

/-- The service weight `wS = sH − sP·mP` at row `i`. -/
abbrev wSv (i : Fin n) : Fp :=
  fv b hn nodes orbit chals pubs pre Q sH i - fv b hn nodes orbit chals pubs pre Q sP i * fv b hn nodes orbit chals pubs pre Q mP i

/-- **The ALU service telescope**: `Σ_i (wSᵢ·invRᵢ + wSᵢ·invOᵢ − sHᵢ·mJᵢ·invJᵢ) = (pub₂, pub₃)`. -/
theorem alu_teleS (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q)
    (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, (liftQ δ (wSv b hn nodes orbit chals pubs pre Q i) * qv b hn nodes orbit chals pubs pre Q invR i +
        liftQ δ (wSv b hn nodes orbit chals pubs pre Q i) * qv b hn nodes orbit chals pubs pre Q invO i -
        liftQ δ (fv b hn nodes orbit chals pubs pre Q sH i * fv b hn nodes orbit chals pubs pre Q mJ i) *
          qv b hn nodes orbit chals pubs pre Q invJ i) =
      Quad.mk _ (pubs pubALs) (pubs (pubALs + 1)) := by
  have hg := alu_qe b hn nodes orbit chals pubs pre Q hsat
  have hmem : ∀ e ∈ accG accS pubALs (fun c => QE.sub (QE.add (QE.scale (wS c) (rdQ c invR))
      (QE.scale (wS c) (rdQ c invO))) (QE.scale (.mul (rdC c sH) (rdC c mJ)) (rdQ c invJ))),
      e ∈ (aluQ δ : List (QE Fp)) :=
    fun e he => List.mem_append_right _ (by simp only [logupQ, List.mem_append]; tauto)
  refine TeleHQ.qTelescope δ hn (fun i => fv b hn nodes orbit chals pubs pre Q isFT i)
    (fun i => fv b hn nodes orbit chals pubs pre Q isLT i)
    (fun i => qv b hn nodes orbit chals pubs pre Q accS i) _ _
    (fun i => (alu_masks b hn nodes orbit chals pubs pre Q hbind hinj i).1)
    (fun i => (alu_masks b hn nodes orbit chals pubs pre Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (hmem _ (List.Mem.head _))
    simp only [wS, rdC, rdQ, ite_true, ev_scale, ev_sub, ev_add, ev_var] at g
    simpa only [qv, fv, wSv, cv, CoeffExpr.eval, liftQ, map_sub, map_mul] using g
  · intro i hi
    have g := hg i (hmem _ (List.Mem.tail _ (List.Mem.head _)))
    simp only [wS, rdC, rdQ, Bool.false_eq_true, ite_false, ev_scale, ev_sub, ev_add, ev_next, ev_var] at g
    simp only [notE, cv, nv, CoeffExpr.eval, aluEK_next b hn nodes orbit chals pubs pre Q hadj i hi,
      aluEF_next b hn nodes orbit chals pubs pre Q hadj i hi] at g
    simpa only [qv, fv, wSv, liftQ, map_sub, map_one, map_mul] using g
  · intro i
    have g := hg i (hmem _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    rw [ev_scale, ev_sub, ev_var, ev_pub, aluEK_pub, aluEK_pub] at g
    simpa only [qv, fv, cv, CoeffExpr.eval] using g

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluTeleAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluTeleAL
#print axioms alu_teleV
#print axioms alu_teleX
#print axioms alu_teleS
end Axioms
