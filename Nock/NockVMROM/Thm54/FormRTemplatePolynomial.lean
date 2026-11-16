/-
  Nock/NockVMROM/Thm54/FormRTemplatePolynomial.lean

  The template's own Form R polynomial and exactly what it needs, moved VERBATIM and under the
  SAME fully qualified names (`Nock.NockVMROM.Thm54.FormRAxisEvent.*`) out of
  `FormRAxisEvent.lean`: `formRN`, `formRN_sub_one`, `templateRowCertAxis`, `readRowAt`,
  `readRowAt_read_root`, `certAxisVia`, `templateCertAxis`, `certShiftOf`, `certBitsOf`,
  `formRPolyOfCert`, `formRTemplatePolynomial`.  A pure module move: types and values are
  unchanged.

  Imports: `FormRCore` (the Form R polynomial core) and `TemplateAxisCounting`
  (`templateMemoryTreeAt`, `templateAxisTree`), both strictly below `OptimizedStrictPackage` and
  `ProductionP8Containment`, so a later `fixedFormRWorkload` can sit in `workload`'s
  module without a `workload` parameter.
-/
import Nock.NockVMROM.Thm54.FormRCore
import Nock.NockVMROM.Thm54.TemplateAxisCounting

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators Classical Polynomial

namespace Nock.NockVMROM.Thm54.FormRAxisEvent

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open SemanticTimestampStrategy
open Nock.RedTeam.Batch554 (bitsOf rpaths vpaths Cpoly bit)
open Nock.RedTeam.Batch575
open Polynomial

/-! ## A1. The template's own Form R certificate -/

section Certificate

variable {K : Type} [Field K]

noncomputable def formRN (K : Type) [Field K] : ℕ := Nat.size (ringChar K)

theorem formRN_sub_one : formRN K - 1 = MemoryTable.pwScaleExp K := rfl

/-- The same, read off the template itself. -/
noncomputable def templateRowCertAxis (row : MemoryRowTemplate (K := K)) : ℕ :=
  MemoryTable.nockAxisOf row.placeholder.2.2.mem.axis

/-- The read-root row of exponent `e` in a template tree (first in BFS order). -/
def readRowAt (t : NTree (MemoryRowTemplate (K := K))) (e : ℕ) :
    Option (MemoryRowTemplate (K := K)) :=
  ((bfsForest [t]).map NTree.label).find? fun r =>
    decide (r.timestamp.state = .read_root) && decide (r.timestamp.recordExponent = e)

theorem readRowAt_read_root {t : NTree (MemoryRowTemplate (K := K))} {e : ℕ}
    {r : MemoryRowTemplate (K := K)} (h : readRowAt t e = some r) :
    r.timestamp.state = .read_root ∧ r.timestamp.recordExponent = e := by
  have := List.find?_some h
  simpa using this

/-- Certificate axis of exponent `e`, through a row reader. -/
noncomputable def certAxisVia (read : MemoryRowTemplate (K := K) → ℕ)
    (t : NTree (MemoryRowTemplate (K := K))) (e : ℕ) : ℕ :=
  ((readRowAt t e).map read).getD 0

/-- The template certificate axis of exponent `e`. -/
noncomputable def templateCertAxis (t : NTree (MemoryRowTemplate (K := K))) : ℕ → ℕ :=
  certAxisVia templateRowCertAxis t

/-- `m_e` of a certificate-axis map. -/
def certShiftOf (A : ℕ → ℕ) : ℕ → ℕ := fun e => MemoryTable.formRCertShift (A e)

def certBitsOf (A : ℕ → ℕ) : ℕ → ℕ → Bool :=
  fun e k => MemoryTable.formRCertBit (A e) (k - 1)

noncomputable def formRPolyOfCert (A : ℕ → ℕ) (t : MTree K) : Polynomial (Polynomial K) :=
  formRCounts (formRN K) (certShiftOf A) (certBitsOf A) t

/-- **A1.**  Form R polynomial of one template root, certificate from the template's own rows. -/
noncomputable def formRTemplatePolynomial
    {F : Type} [Field F] [Algebra F K]
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) :
    Polynomial (Polynomial K) :=
  formRPolyOfCert (templateCertAxis (templateMemoryTreeAt E i))
    (templateAxisTree (templateMemoryTreeAt E i))

end Certificate

end Nock.NockVMROM.Thm54.FormRAxisEvent
