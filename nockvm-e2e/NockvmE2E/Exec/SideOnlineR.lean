/-
 the `FixFailR` restatement of the online split.

`FixFail'` (SoundOnlineP.lean) does not bound the lengths of the main proof's roots, while `fixCtx π ζ` contains `π.roots[0..3]` as raw lists.
So the `hglue` of `exec_e2e_J8V''`/`'''` (first conjunct `decS (sideOf g o).1 = ⟨[], fixCtx π ζ, vF⟩` with `[Finite Stmt']`) can only hold if the
roots of every `FixFail'` output are bounded (`old_hglue_bounds_roots`, kernel).  The online verifier checks `π.roots.all dgOk` (first `ckE`
of `verifyOnlineE'`), so the event `FixFailR := FixFail' ∧ π.roots.all dgOk = true` has the same bound.

Contents (Generic part, no J-8 notation):
  `FixFailR`, `FixFailR.fixFail'`, `FixFailR.roots_len`, `fixCtx_length_ge`, `old_hglue_bounds_roots` (reduction, kernel),
  `verifyOnline_splitR'`, `exec_e2e_onlineP_R`.

LABELS.  Kernel-checked (once the build job is DONE): everything in this file.  ARGUED, NOT kernel-checked: that `FixFail'` really admits outputs
with unboundedly long `roots[0]` (needs a concrete accepting side proof -- not built); so `old_hglue_bounds_roots` is the kernel half of the
unsatisfiability argument (a reduction), not an unsatisfiability proof.
-/
import NockvmE2E.Exec.E2EOnlineP

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideOnlineR
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.E2EOnline NockvmE2E.Exec.E2EOnlineP

/-- `FixFail'` together with the canonicity of the main proof's roots (which `verifyOnline'` checks first) -/
def FixFailR (X0 : ExecInst) (vk : VK) (Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop :=
  FixFail' X0 vk Hf FS FSf z π πF ∧ π.roots.all dgOk = true

theorem FixFailR.fixFail' {X0 : ExecInst} {vk : VK} {Hf : HFn} {FS FSf : FSFn} {z : List Nat} {π : FlatProof} {πF : FixProof}
    (h : FixFailR X0 vk Hf FS FSf z π πF) : FixFail' X0 vk Hf FS FSf z π πF := h.1

/-- every root of a `FixFailR` output has exactly 5 limbs -/
theorem FixFailR.roots_len {X0 : ExecInst} {vk : VK} {Hf : HFn} {FS FSf : FSFn} {z : List Nat} {π : FlatProof} {πF : FixProof}
    (h : FixFailR X0 vk Hf FS FSf z π πF) : ∀ r ∈ π.roots, r.length = 5 := by
  intro r hr
  have := (Array.all_eq_true_iff_forall_mem.1 h.2) r hr
  simp only [dgOk, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

/-- accept implies the root canonicity -/
theorem verifyOnline'_roots_all {vk : VK} {H Hf : HFn} {FS FSf : FSFn} {z : List Nat} {π : FlatProof} {πF : FixProof}
    (hon : verifyOnline' vk H Hf FS FSf z π πF = true) : π.roots.all dgOk = true := by
  have hE : verifyOnlineE' vk H Hf FS FSf z π πF = .ok () := by
    unfold verifyOnline' at hon
    cases h : verifyOnlineE' vk H Hf FS FSf z π πF with
    | error _ => simp [h] at hon
    | ok u => cases u; rfl
  have h1 := ((verifyOnlineE'_ok_iff vk H Hf FS FSf z π πF).mp hE).1
  unfold allCanonOnline at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1.1.1.1.2

/-- **The split lemma over `FixFailR`**: accept implies the flat verifier accepts, or `FixFailR` -/
theorem verifyOnline_splitR' (X0 : ExecInst) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (vk : VK)
    (hvk : setup' X0 Hf = some vk) (hon : verifyOnline' vk H Hf FS FSf z π πF = true) :
    verifyFlat X0 H FS z π = true ∨ FixFailR X0 vk Hf FS FSf z π πF := by
  rcases verifyOnline_split' X0 H Hf FS FSf z π πF vk hvk hon with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, verifyOnline'_roots_all hon⟩

section Generic
variable {D : Type} {R : D → Type} [DecidableEq D] [SampleableType (∀ d, R d)]
  {DF : Type} {RF : DF → Type} [DecidableEq DF] [SampleableType (∀ d, RF d)] {O O' : Type}

variable (X0 : ExecInst) (HOf : (∀ d, R d) → HFn) (FSOf : (∀ d, R d) → FSFn)
  (HfOf : (∀ d, RF d) → HFn) (FSfOf : (∀ d, RF d) → FSFn) (vkOf : (∀ d, RF d) → VK) (rp : O → O')
  (zO : O → List Nat) (πO : O → FlatProof) (πFO : O → FixProof) (BadO : O → Prop)
  (zO' : O' → List Nat) (πO' : O' → FlatProof) (BadO' : O' → Prop)

/-- **`exec_e2e_onlineP_R`**: `exec_e2e_onlineP` with `hFix` over the event `FixFailR` (same bound: accepting outputs satisfy `FixFailR`). -/
theorem exec_e2e_onlineP_R (hvk : ∀ gF, setup' X0 (HfOf gF) = some (vkOf gF))
    (hz : ∀ o, zO' (rp o) = zO o) (hπ : ∀ o, πO' (rp o) = πO o) (hBad : ∀ o, BadO' (rp o) ↔ BadO o)
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O))
    (ε εfix : ℝ≥0∞)
    (hflat : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repackP rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] ≤ ε)
    (hFix : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => FixFailR X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] ≤ ε + εfix := by
  let M : ProbComp ((∀ d, R d) × (∀ d, RF d) × Option O) :=
    do let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A; pure (g, gF, o)
  let Pon : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyOnline' (vkOf x.2.1) (HOf x.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o) = true ∧ BadO o
  let Pfl : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyFlat X0 (HOf x.1) (FSOf x.1) (zO o) (πO o) = true ∧ BadO o
  let Pfx : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => FixFailR X0 (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o)
  have e0 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] =
      Pr{let x ← M}[Pon x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : ∀ d, RF d) (o : Option O) => match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o)
  have e1 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => FixFailR X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] =
      Pr{let x ← M}[Pfx x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : ∀ d, RF d) (o : Option O) => match o with
      | none => False
      | some o => FixFailR X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))
  have e2 : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repackP rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] = Pr{let x ← M}[Pfl x] := by
    simp only [sim_repackP, M, Pfl, prEvent_eq_evalDist_map]
    simp
    congr! 3
    congr 1
    funext a
    congr 1
    funext o
    rcases o with _ | o
    · rfl
    · show (verifyFlat X0 (HOf _) (FSOf _) (zO' (rp o)) (πO' (rp o)) = true ∧ BadO' (rp o)) = _
      rw [hz, hπ, propext (hBad o)]
  have hmono : Pr{let x ← M}[Pon x] ≤ Pr{let x ← M}[Pfl x ∨ Pfx x] := by
    refine prEvent_mono_of_support M Pon _ ?_
    rintro ⟨g, gF, o⟩ _ h
    rcases o with _ | o
    · exact absurd h id
    · obtain ⟨h1, h2⟩ := h
      rcases verifyOnline_splitR' X0 (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) (vkOf gF) (hvk gF) h1 with h3 | h3
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr h3
  rw [e0]
  rw [e2] at hflat
  rw [e1] at hFix
  exact hmono.trans ((prEvent_or_le M Pfl Pfx).trans (add_le_add hflat hFix))

end Generic

end NockvmE2E.Exec.SideOnlineR

#print axioms NockvmE2E.Exec.SideOnlineR.FixFailR.roots_len
#print axioms NockvmE2E.Exec.SideOnlineR.verifyOnline_splitR'
#print axioms NockvmE2E.Exec.SideOnlineR.exec_e2e_onlineP_R
