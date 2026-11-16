/-
(**fallback form `run_hyps9`**): the runtime gates of the verifier exe discharge the
instance-side binders of `exec_e2e_J9A` at ANY loaded instance.

`exec_e2e_J9A XI0 ...` has these instance-side hypotheses: `hsh hshX hchips hmask hnumeralOk` (the five `famGates`), `hl` (`l = 170`), the
datum binders (`d hdk L R hT hσ hfree hS hlink hids hnum0 hpJ hpV hpX hpS`) and `hjet`.  `run_hyps9` shows: from the exe's runtime checks
`famGates famJ9A (XI170 XI0)`, `XI0.l = 170`, `linkGate9 (XI170 XI0) c` (all of which `verdict9` evaluates; `verdict9_run`), the five gates
hold and there IS a datum `d` (with `DatumOK9A`, `Link9`, `StmtP9A`, `InpLink9`, small ids, `hnum0`, the four layout conditions, the table
restriction `R` with `hT hσ hfree`) with `d.c = c`; no table is a jet table (`hjet` is then vacuous:
`fun t h => absurd h (hnj t)`).  Instantiating `exec_e2e_J9A` at that `d`, `L`, `R` therefore yields the bound
`Pr[AccF ∧ ¬ HoldsN d.c] ≤ 2⁻⁸²` for the claim `c` the exe prints.  The fully packaged ∃-form (restating the ~100-line notation block of
`E2EJ9A.lean` and all adversary binders) was NOT written: this is fallback, same content, readable in one pass.
-/
import NockvmE2E.J9A.RunGate9
set_option autoImplicit false
namespace NockvmE2E.J9A.E2EJ9ARun
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.E2EJ9AToyR NockvmE2E.J9A.RunGate9 NockvmE2E.J9A.LagrJ9A
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- **the runtime gates give the instance-side hypotheses of `exec_e2e_J9A`** (at `XI := XI170 XI0`, any `XI0`, any `c`) -/
theorem run_hyps9 (XI0 : ExecInst) (c : P8PublicClaim)
    (hG : NockvmE2E.Exec.FamGates.famGates famJ9A (XI170 XI0) = true) (hl : XI0.l = 170) (hg : linkGate9 (XI170 XI0) c = true) :
    shapeOkF famJ9A (XI170 XI0) = true ∧ shapeXOkF famJ9A (XI170 XI0) = true ∧ chipsOkF famJ9A (XI170 XI0) = true ∧
    maskOkF famJ9A (XI170 XI0) = true ∧ numeralOkF famJ9A (XI170 XI0) = true ∧ XI0.l = 170 ∧
    Wit9 (XI170 XI0) c (fun _ => True) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := NockvmE2E.Exec.FamGates.famGates_sound hG
  exact ⟨h1, h2, h3, h4, h5, hl, linkGate9_wit _ c h1 hg⟩

/-- the same, from the exe's verdict: whenever `verdict9 XI ... = .ok c`, `run_hyps9` applies at `XI0 := XI` with the printed claim `c` -/
theorem verdict9_run {XI : ExecInst} {H : HFn} {FS : FSFn} {z : List ℕ} {π : FlatProof} {c : P8PublicClaim}
    (h : verdict9 XI H FS z π = .ok c) :
    shapeOkF famJ9A (XI170 XI) = true ∧ shapeXOkF famJ9A (XI170 XI) = true ∧ chipsOkF famJ9A (XI170 XI) = true ∧
    maskOkF famJ9A (XI170 XI) = true ∧ numeralOkF famJ9A (XI170 XI) = true ∧ XI.l = 170 ∧
    Wit9 (XI170 XI) c (fun _ => True) := by
  obtain ⟨hG, hl, hg, _⟩ := verdict9_sound h
  have hx := xi170_of_l hl
  exact run_hyps9 XI c (by rw [hx]; exact hG) hl (by rw [hx]; exact hg)

end NockvmE2E.J9A.E2EJ9ARun

#print axioms NockvmE2E.J9A.E2EJ9ARun.run_hyps9
#print axioms NockvmE2E.J9A.E2EJ9ARun.verdict9_run
