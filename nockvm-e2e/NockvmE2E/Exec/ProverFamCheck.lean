/-
the prover's family data (`FP.FamP`, Mathlib-free) agrees with the verifier's `ShapeF.Fam` (`famJ8`, `famJ9A`), and a synthetic J-9 A table set (the toy
vector `toy9On`, 8 tables) run through the SAME layout builder / `pubMode` the prover uses (`FlatF.layoutOfTabsF famP9A.tabOf famP9A.tabLens`,
`pubMode := famP9A.pubMode`) yields an instance with `layOkF famJ9A = true`, `pubMode = 2` and an accepting `pubCheck`.  No real trace.
-/
import NockvmE2E.Exec.FlatProver
import NockvmE2E.Exec.FlatFam
import NockvmE2E.Exec.J9ALChipsFam

set_option autoImplicit false

namespace NockvmE2E.Exec.ProverFamCheck
open NockvmE2E.Exec NockvmE2E.Exec.FP NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.FlatFam NockvmE2E.Exec.FlatF NockvmE2E.Exec.V

/-- same id SET (the prover's order is its table order = the J-8 exe's, kept for byte-identical output; the verifier addresses tables by `tabOf`, not list order) -/
theorem famP8_ids : famP8.ids.all (famJ8.ids.contains ·) = true ∧ famJ8.ids.all (famP8.ids.contains ·) = true ∧ famP8.ids.length = famJ8.ids.length := by decide +kernel
theorem famP8_tabLens : famP8.tabLens = famJ8.tabLens := rfl
theorem famP8_mode : famP8.pubMode = famJ8.pubMode := rfl
theorem famP9A_ids : famP9A.ids.all (famJ9A.ids.contains ·) = true ∧ famJ9A.ids.all (famP9A.ids.contains ·) = true ∧ famP9A.ids.length = famJ9A.ids.length := by decide +kernel
theorem famP9A_tabLens : famP9A.tabLens = famJ9A.tabLens := rfl
theorem famP9A_mode : famP9A.pubMode = famJ9A.pubMode := rfl
/-- the table index agrees on every family id and on an unknown id -/
theorem famP9A_tabOf : (famJ9A.ids ++ ["bogus"]).all (fun id => famP9A.tabOf id == famJ9A.tabOf id) = true := by decide +kernel
theorem famP8_tabOf : (famJ8.ids ++ ["bogus"]).all (fun id => famP8.tabOf id == famJ8.tabOf id) = true := by decide +kernel
/-- the J-9 AL family (`famP9AL`, the prover's) agrees with `famJ9AL` (the verifier's) -/
theorem famP9AL_ids : famP9AL.ids.all (J9ALChips.famJ9AL.ids.contains ·) = true ∧ J9ALChips.famJ9AL.ids.all (famP9AL.ids.contains ·) = true ∧
    famP9AL.ids.length = J9ALChips.famJ9AL.ids.length := by decide +kernel
theorem famP9AL_tabLens : famP9AL.tabLens = J9ALChips.famJ9AL.tabLens := rfl
theorem famP9AL_mode : famP9AL.pubMode = J9ALChips.famJ9AL.pubMode := rfl
theorem famP9AL_tabOf : (J9ALChips.famJ9AL.ids ++ ["bogus"]).all (fun id => famP9AL.tabOf id == J9ALChips.famJ9AL.tabOf id) = true := by decide +kernel
/-- the prover's preprocessed-column map agrees with `famJ9AL`'s on every id (the ALU: columns 0..4) -/
theorem preIdxOf_J9AL : (J9ALChips.famJ9AL.ids ++ famJ8.ids).all (fun id => preIdxOf id == J9ALChips.famJ9AL.preIdx id) = true := by decide +kernel

/-- the preprocessed-column map the prover uses agrees with the verifier family's on every id (J-8 and J-9 A) -/
theorem preIdxOf_J9A : (famJ9A.ids ++ famJ8.ids).all (fun id => preIdxOf id == famJ9A.preIdx id) = true := by decide +kernel
theorem preIdxOf_J8 : famJ8.ids.all (fun id => preIdxOf id == famJ8.preIdx id) = true := by decide +kernel

/-- J-8 default: the prover's layout builder is `layoutOfTabs` (so the default-family instance is unchanged) -/
theorem layout_famP8 (tabs : Array TabInst) : layoutOfTabsF famP8.tabOf famP8.tabLens tabs = layoutOfTabs tabs := rfl

/-- the synthetic J-9 A instance: 8 dummy-chip tables carrying `toy9On`, layout from the prover's builder, pubMode from the prover's family -/
def synth : Option ExecInst :=
  match layoutOfTabsF famP9A.tabOf famP9A.tabLens (tab9 famJ9A PE.toy9On) with
  | .ok L => some { instOf9 PE.toy9On with pubLay := L, pubMode := famP9A.pubMode }
  | .error _ => none

def smoke : Bool :=
  match synth with
  | none => false
  | some XI =>
    XI.pubMode == 2 && layOkF famJ9A XI && XI.pubLay.present.size == 8 && XI.pubLay.present.all id &&
    XI.pubCheck PE.toy1Slots (PE.concatPubs PE.toy9On) &&
    !XI.pubCheck PE.toy1Slots (PE.concatPubs (PE.tweak9 PE.toy9On 6 1)) &&
    -- a J-8 family instance on the same tables is rejected (pubMode 0 layout has 6 tables)
    (match layoutOfTabsF famP8.tabOf famP8.tabLens (tab9 famJ9A PE.toy9On) with | Except.error _ => true | Except.ok _ => false)

theorem smoke_true : smoke = true := by decide +kernel

end NockvmE2E.Exec.ProverFamCheck

#print axioms NockvmE2E.Exec.ProverFamCheck.smoke_true
#print axioms NockvmE2E.Exec.ProverFamCheck.preIdxOf_J9A
#print axioms NockvmE2E.Exec.ProverFamCheck.famP9A_tabOf
#print axioms NockvmE2E.Exec.ProverFamCheck.famP9AL_ids
#print axioms NockvmE2E.Exec.ProverFamCheck.famP9AL_tabOf
#print axioms NockvmE2E.Exec.ProverFamCheck.preIdxOf_J9AL
