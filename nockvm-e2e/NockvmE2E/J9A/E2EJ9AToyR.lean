/-
J9A-LINK: **`toy9_witness` / `abs9_witness`**, the kernel witness of the DATUM hypotheses of `exec_e2e_J9A`
(and `_absent`) AT THE EXECUTED J-9 A INSTANCES `toy9R` / `abs9R` (Exec/Toy9R.lean, Exec/Abs9R.lean), and the claim = the real run of the program
(nockvm's generator `Nock.V1J8.Gen.runX`, kernel-evaluated).  The false-claim twins `*_false` (instances `toy9RF`, `abs9RF`) show the bound's bad
event `AccF ∧ ¬ HoldsN d.c` is not empty by its hypotheses.
Labels: `hsh : shapeOkF famJ9A (XI170 _) = true` is the executed gate (a hypothesis of each witness, not kernel-evaluated here).  Not witnessed here:
`AccJ9A`/`PubJ9A`, the executed gates `hshX hchips hmask hnumeralOk hl`, the TCB `hjet` (vacuous: no jet table), `R`'s `tp`.
No existing file edited.
-/
import NockvmE2E.Exec.Toy9R
import NockvmE2E.Exec.Abs9R
import NockvmE2E.J9A.DatX9Ok
import NockvmE2E.J9A.InstJ9AW
import NockvmE2E.J9A.LagrJ9A
import NockvmE2E.J9A.RVUJ9A
import Nock.V1J8.GenComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.J9A.E2EJ9AToyR

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9 NockvmE2E.J9A.DatX9Ok NockvmE2E.J9A.InstJ9AW
open NockvmE2E.J9A.LagrJ9A (numOf9)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)

noncomputable section

local instance : DecidableEq NockvmE2E.Exec.PE.Tok := fun a b =>
  match a, b with
  | .cell, .cell => isTrue rfl
  | .atom x, .atom y => if h : x = y then isTrue (by simp [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .cell, .atom _ => isFalse (by intro h; cases h)
  | .atom _, .cell => isFalse (by intro h; cases h)

local instance : DecidableEq NockvmE2E.Exec.PE.NounRec := fun a b =>
  match a, b with
  | ⟨k, n, i, h, l⟩, ⟨k', n', i', h', l'⟩ =>
    if h1 : k = k' ∧ n = n' ∧ i = i' ∧ h = h' ∧ l = l' then
      isTrue (by obtain ⟨e1, e2, e3, e4, e5⟩ := h1; subst e1 e2 e3 e4 e5; rfl)
    else isFalse (by intro e; cases e; exact h1 ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-! ## 1. the programs and their runs -/

def rspP : ℕ → Nock.Noun
  | 0 => .atom 0
  | n + 1 => .cell (.atom 0) (rspP n)

/-- toy: Batch4883 chips-on, `*[sA [[0 AB] [0 AF]]]`, `sA = [0 [0 … 0]]` (63 cells), `AB = 2^64-1`, `AF = 2^63-1` -/
def toyS : Nock.Noun := rspP 63
def toyF : Nock.Noun := .cell (.cell (.atom 0) (.atom (2 ^ 64 - 1))) (.cell (.atom 0) (.atom (2 ^ 63 - 1)))
/-- absent: `*[[(p+5) 0] [0 2]]` (NOT Batch4882's `*[(p+5) [0 1]]`) -/
def absS : Nock.Noun := .cell (.atom (Nock.Field.p + 5)) (.atom 0)
def absF : Nock.Noun := .cell (.atom 0) (.atom 2)

def cToy : P8PublicClaim := ⟨toyS, toyF, .cell (.atom 0) (.cell (.atom 0) (.atom 0))⟩
def cAbs : P8PublicClaim := ⟨absS, absF, .atom (Nock.Field.p + 5)⟩
/-- the false claims of the twin instances: result record changed (toy: `[0 [0 1]]`; absent: the big atom `p + 6`) -/
def cToyF : P8PublicClaim := ⟨toyS, toyF, .cell (.atom 0) (.cell (.atom 0) (.atom 1))⟩
def cAbsF : P8PublicClaim := ⟨absS, absF, .atom (Nock.Field.p + 6)⟩

/-- **[kernel] nockvm's generator run on the toy program** gives the result of the claim -/
theorem run_toy : (Nock.V1J8.Gen.runX (fun _ => none) 1000 toyS toyF).map (·.res) = some cToy.result := by decide +kernel
theorem run_abs : (Nock.V1J8.Gen.runX (fun _ => none) 1000 absS absF).map (·.res) = some cAbs.result := by decide +kernel

theorem holds_toy : Nock.Jet.HoldsN cToy := ⟨1000, by decide +kernel⟩
theorem holds_abs : Nock.Jet.HoldsN cAbs := ⟨1000, by decide +kernel⟩

theorem not_holds_toyF : ¬ Nock.Jet.HoldsN cToyF := by
  rintro ⟨f, h⟩
  have h1 : Nock.evalN 1000 toyS toyF = some (.cell (.atom 0) (.cell (.atom 0) (.atom 0))) := by decide +kernel
  have := Nock.evalN_deterministic h1 h
  simp [cToyF] at this

theorem not_holds_absF : ¬ Nock.Jet.HoldsN cAbsF := by
  rintro ⟨f, h⟩
  have h1 : Nock.evalN 1000 absS absF = some (.atom (Nock.Field.p + 5)) := by decide +kernel
  have := Nock.evalN_deterministic h1 h
  simp [cAbsF] at this

/-! ## 2. the executed gates are shared by the twins (the twin differs only in `pubIn`, which no gate reads) -/

theorem shape_toyF : shapeOkF famJ9A (XI170 Toy9R.toy9RF) = shapeOkF famJ9A (XI170 Toy9R.toy9R) := rfl
theorem shape_absF : shapeOkF famJ9A (XI170 Abs9R.abs9RF) = shapeOkF famJ9A (XI170 Abs9R.abs9R) := rfl

/-! ## 3. the generic witness over a loaded instance (proof-free closed premises) -/

/-- the numeral of table `s` of `DX9 XI _ _ k kV c`, without proofs -/
def numP (XI : ExecInst) (k kV : ℕ) (s : Fin 8) : ℕ :=
  if s = 2 then k else if s = 5 then (if (tabOf XI "walkChipHQK").isSome then kV else 0) else if s = 7 then hNof XI "atomChipHQL" else 0

/-- **`Wit9 XI c Q`**: there is a J-9 A datum `d` with `DatumOK9A d`, `Link9 XI d`, `StmtP9A d`, `InpLink9 d XI.pubIn`, small registry ids, the
numeral side condition `hnum0`, the four absent-table layout conditions, no jet table, the table restriction `R` with `hfree`, `d.c = c`, and `Q d`.
These are exactly the datum-side binders of `exec_e2e_J9A` / `exec_e2e_J9A_absent` (with `XI := XI170 XI0`). -/
def Wit9 (XI : ExecInst) (c : P8PublicClaim) (Q : Datum9A → Prop) : Prop :=
  ∃ (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d),
    StmtP9A d ∧ NockvmE2E.J9A.RVUJ9A.InpLink9 d XI.pubIn ∧ (∀ id ∈ d.Pb.regs, id < P) ∧
    (∀ t : Fin XI.tabs.size, (chipNumeralF famJ9A XI.tabs[t].chip).getD 0 = numOf9 d (sigma9 XI t)) ∧
    (d.Pb.nJ = 0 → XI.pubLay.present[3]! = false) ∧ (d.Pb.krootsV = 0 → XI.pubLay.present[5]! = false) ∧
    (d.Pb.axOn = false → XI.pubLay.present[6]! = false) ∧ (d.Pb.spOn = false → XI.pubLay.present[7]! = false) ∧
    (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "jetChipJ8") ∧
    (∃ (R : NockvmE2E.J8.TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size), (∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) ∧
      (J9A d hdk).AccOn R.q) ∧
    d.c = c ∧ Q d

theorem witness9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0) (k kV : ℕ)
    (hk1 : 1 ≤ k) (hkW : k ≤ hNof XI "walkChipJ8")
    (hV : (tabOf XI "walkChipHQK").isSome = true → 1 ≤ kV ∧ kV ≤ hNof XI "walkChipHQK")
    (hV0 : (tabOf XI "walkChipHQK").isSome = false → kV = 0)
    (c : P8PublicClaim) (hc : ClaimOK9 c (hNof XI "atomChipHQL"))
    (hcl : XI.pubIn.claimCells = (Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.claimCells c).map
        (NockvmE2E.J8.RVUJ8.claimRec (Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun c)) ++
      (Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9.claimBigs P c).map
        (NockvmE2E.J8.RVUJ8.claimRec (Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun c)))
    (hpin : XI.pubIn.pins = [])
    (hat : XI.pubIn.atoms = (List.finRange 3).filterMap (fun i => match Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun c i with
      | .atom v => if P ≤ v then none else some (i.val, v) | .cell _ _ => none))
    (hnum : ∀ t : Fin XI.tabs.size, (chipNumeralF famJ9A XI.tabs[t].chip).getD 0 = numP XI k kV (sigma9 XI t))
    (hpJ : hNof XI "jetChipJ8" = 0 → XI.pubLay.present[3]! = false)
    (hpV : (if (tabOf XI "walkChipHQK").isSome then kV else 0) = 0 → XI.pubLay.present[5]! = false)
    (hpX : (tabOf XI "axisChipJ9").isSome = false → XI.pubLay.present[6]! = false)
    (hpS : (tabOf XI "splitChipJ9").isSome = false → XI.pubLay.present[7]! = false)
    (hnj : ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "jetChipJ8")
    (Q : Datum9A → Prop) (hQ : Q (DX9 XI h hJ k kV c)) : Wit9 XI c Q := by
  obtain ⟨hdk, hS⟩ := datX9_ok XI h hJ k kV hk1 hkW hV hV0 c hc
  refine ⟨DX9 XI h hJ k kV c, hdk, link9_DX9 XI h hJ k kV c, hS, ⟨hcl, hpin, hat⟩, ?_, hnum, hpJ, hpV, hpX, hpS, hnj,
    ⟨RJ9A XI _ hdk, rfl, fun _ => rfl, hfree_J9A XI h k kV _ [] [] _ _ _ _ rfl hdk⟩, rfl, hQ⟩
  intro id hid
  exact absurd hid (by simp [DX9, PbOfX9])

/-! ## 4. the toy and absent witnesses -/


/-! ### toy -/
open Toy9R Abs9R in
theorem hJ_toy : hNof (XI170 toy9R) "jetChipJ8" = 0 := by decide +kernel
open Toy9R Abs9R in
theorem claimOK_toy : ClaimOK9 cToy (hNof (XI170 toy9R) "atomChipHQL") := by
  have : hNof (XI170 toy9R) "atomChipHQL" = 2 := by decide +kernel
  rw [this]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
open Toy9R Abs9R in
theorem wit_toy (hsh : shapeOkF famJ9A (XI170 toy9R) = true) :
    Wit9 (XI170 toy9R) cToy (fun d => d.Pb.axOn = true ∧ d.Pb.spOn = true ∧ d.Pb.kroots = 3 ∧ d.Pb.krootsV = 1) :=
  witness9 (XI170 toy9R) hsh hJ_toy 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cToy claimOK_toy (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) _ (by show (tabOf (XI170 toy9R) "axisChipJ9").isSome = true ∧ (tabOf (XI170 toy9R) "splitChipJ9").isSome = true ∧ 3 = 3 ∧ (if (tabOf (XI170 toy9R) "walkChipHQK").isSome then 1 else 0) = 1; decide +kernel)

/-! ### toyF -/
open Toy9R Abs9R in
theorem hJ_toyF : hNof (XI170 toy9RF) "jetChipJ8" = 0 := by decide +kernel
open Toy9R Abs9R in
theorem claimOK_toyF : ClaimOK9 cToyF (hNof (XI170 toy9RF) "atomChipHQL") := by
  have : hNof (XI170 toy9RF) "atomChipHQL" = 2 := by decide +kernel
  rw [this]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
open Toy9R Abs9R in
theorem wit_toyF (hsh : shapeOkF famJ9A (XI170 toy9RF) = true) :
    Wit9 (XI170 toy9RF) cToyF (fun d => d.Pb.axOn = true ∧ d.Pb.spOn = true ∧ d.Pb.kroots = 3 ∧ d.Pb.krootsV = 1) :=
  witness9 (XI170 toy9RF) hsh hJ_toyF 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cToyF claimOK_toyF (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) _ (by show (tabOf (XI170 toy9RF) "axisChipJ9").isSome = true ∧ (tabOf (XI170 toy9RF) "splitChipJ9").isSome = true ∧ 3 = 3 ∧ (if (tabOf (XI170 toy9RF) "walkChipHQK").isSome then 1 else 0) = 1; decide +kernel)

/-! ### abs -/
open Toy9R Abs9R in
theorem hJ_abs : hNof (XI170 abs9R) "jetChipJ8" = 0 := by decide +kernel
open Toy9R Abs9R in
theorem claimOK_abs : ClaimOK9 cAbs (hNof (XI170 abs9R) "atomChipHQL") := by
  have : hNof (XI170 abs9R) "atomChipHQL" = 2 := by decide +kernel
  rw [this]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
open Toy9R Abs9R in
theorem wit_abs (hsh : shapeOkF famJ9A (XI170 abs9R) = true) :
    Wit9 (XI170 abs9R) cAbs (fun d => d.Pb.axOn = false ∧ d.Pb.spOn = false ∧ d.Pb.kroots = 1 ∧ d.Pb.krootsV = 0) :=
  witness9 (XI170 abs9R) hsh hJ_abs 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cAbs claimOK_abs (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) _ (by show (tabOf (XI170 abs9R) "axisChipJ9").isSome = false ∧ (tabOf (XI170 abs9R) "splitChipJ9").isSome = false ∧ 1 = 1 ∧ (if (tabOf (XI170 abs9R) "walkChipHQK").isSome then 0 else 0) = 0; decide +kernel)

/-! ### absF -/
open Toy9R Abs9R in
theorem hJ_absF : hNof (XI170 abs9RF) "jetChipJ8" = 0 := by decide +kernel
open Toy9R Abs9R in
theorem claimOK_absF : ClaimOK9 cAbsF (hNof (XI170 abs9RF) "atomChipHQL") := by
  have : hNof (XI170 abs9RF) "atomChipHQL" = 2 := by decide +kernel
  rw [this]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
open Toy9R Abs9R in
theorem wit_absF (hsh : shapeOkF famJ9A (XI170 abs9RF) = true) :
    Wit9 (XI170 abs9RF) cAbsF (fun d => d.Pb.axOn = false ∧ d.Pb.spOn = false ∧ d.Pb.kroots = 1 ∧ d.Pb.krootsV = 0) :=
  witness9 (XI170 abs9RF) hsh hJ_absF 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cAbsF claimOK_absF (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) _ (by show (tabOf (XI170 abs9RF) "axisChipJ9").isSome = false ∧ (tabOf (XI170 abs9RF) "splitChipJ9").isSome = false ∧ 1 = 1 ∧ (if (tabOf (XI170 abs9RF) "walkChipHQK").isSome then 0 else 0) = 0; decide +kernel)

open Toy9R Abs9R in
/-- **`toy9_witness`** [kernel, modulo `hsh`]: at the executed toy instance (`toy9R`, claim = the run of `*[sA [[0 AB] [0 AF]]]`) every datum hypothesis of
`exec_e2e_J9A` holds together (`Wit9`), the claim is the result of nockvm's generator run (`run_toy`), and it holds (`holds_toy`).  `hsh` is the executed gate. -/
theorem toy9_witness (hsh : shapeOkF famJ9A (XI170 toy9R) = true) :
    Wit9 (XI170 toy9R) cToy (fun d => d.Pb.axOn = true ∧ d.Pb.spOn = true ∧ d.Pb.kroots = 3 ∧ d.Pb.krootsV = 1) ∧
    (Nock.V1J8.Gen.runX (fun _ => none) 1000 toyS toyF).map (·.res) = some cToy.result ∧ Nock.Jet.HoldsN cToy :=
  ⟨wit_toy hsh, run_toy, holds_toy⟩

open Toy9R Abs9R in
/-- **`abs9_witness`**: the same at the absent instance `abs9R` (`*[[(p+5) 0] [0 2]] = p+5`; axis / split / atom-walk / jet tables absent) -/
theorem abs9_witness (hsh : shapeOkF famJ9A (XI170 abs9R) = true) :
    Wit9 (XI170 abs9R) cAbs (fun d => d.Pb.axOn = false ∧ d.Pb.spOn = false ∧ d.Pb.kroots = 1 ∧ d.Pb.krootsV = 0) ∧
    (Nock.V1J8.Gen.runX (fun _ => none) 1000 absS absF).map (·.res) = some cAbs.result ∧ Nock.Jet.HoldsN cAbs :=
  ⟨wit_abs hsh, run_abs, holds_abs⟩

open Toy9R Abs9R in
/-- **`toy9_witness_false`**: at the false-claim twin `toy9RF` the same hypotheses hold and the claim is NOT the program's result: the bad event of the bound is
non-empty by its hypotheses -/
theorem toy9_witness_false (hsh : shapeOkF famJ9A (XI170 toy9RF) = true) :
    Wit9 (XI170 toy9RF) cToyF (fun d => d.Pb.axOn = true ∧ d.Pb.spOn = true ∧ d.Pb.kroots = 3 ∧ d.Pb.krootsV = 1) ∧
    (Nock.V1J8.Gen.runX (fun _ => none) 1000 toyS toyF).map (·.res) = some cToy.result ∧ cToyF.result ≠ cToy.result ∧
    ¬ Nock.Jet.HoldsN cToyF :=
  ⟨wit_toyF hsh, run_toy, by simp [cToyF, cToy], not_holds_toyF⟩

open Toy9R Abs9R in
theorem abs9_witness_false (hsh : shapeOkF famJ9A (XI170 abs9RF) = true) :
    Wit9 (XI170 abs9RF) cAbsF (fun d => d.Pb.axOn = false ∧ d.Pb.spOn = false ∧ d.Pb.kroots = 1 ∧ d.Pb.krootsV = 0) ∧
    (Nock.V1J8.Gen.runX (fun _ => none) 1000 absS absF).map (·.res) = some cAbs.result ∧ cAbsF.result ≠ cAbs.result ∧
    ¬ Nock.Jet.HoldsN cAbsF :=
  ⟨wit_absF hsh, run_abs, by simp [cAbsF, cAbs], not_holds_absF⟩

end

end NockvmE2E.J9A.E2EJ9AToyR

#print axioms NockvmE2E.J9A.E2EJ9AToyR.run_toy
#print axioms NockvmE2E.J9A.E2EJ9AToyR.run_abs
#print axioms NockvmE2E.J9A.E2EJ9AToyR.holds_toy
#print axioms NockvmE2E.J9A.E2EJ9AToyR.holds_abs
#print axioms NockvmE2E.J9A.E2EJ9AToyR.not_holds_toyF
#print axioms NockvmE2E.J9A.E2EJ9AToyR.not_holds_absF
#print axioms NockvmE2E.J9A.E2EJ9AToyR.witness9
#print axioms NockvmE2E.J9A.E2EJ9AToyR.toy9_witness
#print axioms NockvmE2E.J9A.E2EJ9AToyR.abs9_witness
#print axioms NockvmE2E.J9A.E2EJ9AToyR.toy9_witness_false
#print axioms NockvmE2E.J9A.E2EJ9AToyR.abs9_witness_false
