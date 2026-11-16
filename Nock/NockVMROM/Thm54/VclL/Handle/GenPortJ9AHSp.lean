/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHSp.lean

  Orbit-generic: for `q = chipOf (spGenE χe nA vS mS).1` (any admissible orbit with `q.n ≤ 3·2^q.h`)
  * `spGenE_size`: row count `= vS.length`;
  * `interpOf_spChip`: the exec interpolant `interpOf q c` is the honest `polyS` at the exec nodes (`nodesOf q`);
  * `spChipOK_exec`: `SPChipOK` (present disjunct) at `nodesOf q`, `mkOrbit q ho`, publics `K3.toK ∘ spGenE.2`;
  * `spChipOK_exec_absent`: the absent disjunct (`spOn = false`, zero publics);
  * `spChipOK_I`: the same for an input record `I` whose split fields are the generator's (the form `recJ9AX` has).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH (polyS polySC)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-! ## 1. Size -/

theorem spGenE_size (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) :
    (GenSpE.spGenE χe nA vS mS).1.size = vS.length := by
  simp [GenSpE.spGenE]

/-! ## 2. The interpolant -/

/-- **The exec split interpolant is the honest `polyS`** at the exec nodes (columns `< 90`). -/
theorem interpOf_spChip (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) (q : ChipIn)
    (hq : q = chipOf (GenSpE.spGenE χe nA vS mS).1) (w : ℕ) (hw : w ≤ 90) (c : Fin w) :
    interpOf q c =
      polyS deltaF nA powerBasis3 (VerJ8.chalsMJ8 deltaF (toχ χe))
        (fun i : Fin q.n => vS.getD i 0) (fun i : Fin q.n => mS.getD i 0) (nodesOf q) w c := by
  subst hq
  have hn : (chipOf (GenSpE.spGenE χe nA vS mS).1).n = vS.length := spGenE_size χe nA vS mS
  unfold interpOf polyS
  congr 1
  funext i
  have := spGenE_cols χe nA vS mS (n := (chipOf (GenSpE.spGenE χe nA vS mS).1).n) hn i c (by omega)
  exact this

/-! ## 3. `SPChipOK` -/

/-- **`SPChipOK`, present disjunct, at the exec orbit.**  `hv`/`hχ` are the honest hypotheses of
`spChipOK_honest` (field axis atoms in `[2^32, 2^64)`; coin outside `famSP`). -/
theorem spChipOK_exec (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) (q : ChipIn)
    (hq : q = chipOf (GenSpE.spGenE χe nA vS mS).1) (ho : OrbOK q) (hn0 : 0 < q.n)
    (hnq : q.n ≤ 3 * 2 ^ q.h) (hnp : q.n < p) (hp : 2 ^ 32 < p)
    (hv : ∀ i : Fin q.n, 2 ^ 32 ≤ vS.getD i 0 ∧ vS.getD i 0 < 2 ^ 64)
    (hχ : ∀ e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin q.n => vS.getD i 0) (K := KC),
      toχ χe ∉ e.ev) :
    SPChipOK deltaF powerBasis3 nA true hn0 (nodesOf q) (mkOrbit q ho)
      (VerJ8.chalsMJ8 deltaF (toχ χe)) (fun j => K3.toK ((GenSpE.spGenE χe nA vS mS).2 j))
      (fun j => interpOf q j) := by
  have hn : q.n = vS.length := by rw [hq]; exact spGenE_size χe nA vS mS
  have hpub : (fun j => K3.toK ((GenSpE.spGenE χe nA vS mS).2 j)) =
      ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) (toχ χe) := by
    funext j
    exact pubsSE_eq χe nA vS mS hn hn0 j
  have hinj := nodesOf_inj q ho hnq
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [nodesOf_adj q i hi]
    exact mul_comm _ _
  have key := ComplJ9AChipsOK.spChipOK_honest deltaF powerBasis3 nA (fun i : Fin q.n => vS.getD i 0)
    (fun i : Fin q.n => mS.getD i 0) hn0 (nodesOf q) (mkOrbit q ho) hp hv hinj hadj hnp (toχ χe) hχ
  have hQ : (fun j : Fin (SplitChipJ9.splitChipJ9 deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho)
      (VerJ8.chalsMJ8 deltaF (toχ χe)) (ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) (toχ χe))).rap.w => interpOf q j) =
      polySC deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF (toχ χe))
        (ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
          (fun i : Fin q.n => mS.getD i 0) (toχ χe)) (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) := by
    funext c
    exact interpOf_spChip χe nA vS mS q hq _ (Nat.le_of_eq rfl) c
  rw [hpub, hQ]
  exact key

/-- **`SPChipOK`, absent disjunct** (`spOn = false`, the generator's absent branch has zero publics). -/
theorem spChipOK_exec_absent (nA : ℕ) (q : ChipIn) (ho : OrbOK q) (hn0 : 0 < q.n) (chals : ℕ → KC)
    (QS : Fin (SplitChipJ9.splitChipJ9 deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals
      (fun j => K3.toK ((fun _ => (0 : K3)) j))).rap.w → Polynomial (ZMod p)) :
    SPChipOK deltaF powerBasis3 nA false hn0 (nodesOf q) (mkOrbit q ho) chals
      (fun j => K3.toK ((fun _ => (0 : K3)) j)) QS :=
  Or.inr ⟨rfl, K3.toK_zero, K3.toK_zero⟩

/-- **`SPChipOK` for an input record whose split fields are the generator's** (present branch): the form
`recJ9AX` has (`SP = chipOf sR`, `pubsS = sP`, `spOn = true`), with `nA = I.A.n`. -/
theorem spChipOK_I (I : InJ9A) (hv : ValidJ9A I) (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ)
    (hSP : I.SP = chipOf (GenSpE.spGenE χe nA vS mS).1) (hP : I.pubsS = (GenSpE.spGenE χe nA vS mS).2)
    (hon : I.spOn = true) (hA : I.A.n = nA) (hχ' : I.χ = χe)
    (hnq : I.SP.n ≤ 3 * 2 ^ I.SP.h) (hnp : I.SP.n < p) (hp : 2 ^ 32 < p)
    (hvv : ∀ i : Fin I.SP.n, 2 ^ 32 ≤ vS.getD i 0 ∧ vS.getD i 0 < 2 ^ 64)
    (hχ : ∀ e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin I.SP.n => vS.getD i 0) (K := KC),
      toχ χe ∉ e.ev) :
    SPChipOK deltaF powerBasis3 (mkPbA I hv).nA (mkPbA I hv).spOn (mkPbA I hv).hnS (mkPbA I hv).nodesS
      (mkPbA I hv).orbitS (VerJ8.chalsMJ8 deltaF (toχ I.χ)) (fun j => K3.toK (I.pubsS j))
      (fun j => interpOf I.SP j) := by
  have h := spChipOK_exec χe nA vS mS I.SP hSP hv.oSP hv.nSP hnq hnp hp hvv hχ
  subst hχ'
  have e1 : (mkPbA I hv).nA = nA := hA
  rw [hP]
  rw [e1]
  have e2 : (mkPbA I hv).spOn = true := hon
  rw [e2]
  exact h

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp
#print axioms spGenE_size
#print axioms interpOf_spChip
#print axioms spChipOK_exec
#print axioms spChipOK_exec_absent
#print axioms spChipOK_I
end Axioms
