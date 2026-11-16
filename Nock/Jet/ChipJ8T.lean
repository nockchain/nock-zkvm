/-
  Nock/Jet/ChipJ8T.lean

  **The J chip as a RAP, with the in-chip tags LAST.**

  **Finding (why a variant).**  The J chip's ONE tagged accumulator carries the in-chip balances
  (`TAG_val`, `TAG_reg`) AND the service provide (`TAG_jet`) at the handle coins `γH′ρH′`; its
  terminal enters the SERVICE balance (SPEC §3.4: `acc_service = term_J + term_inc + term_AW`).  So
  the J in-chip keys share ONE rational identity with the inc and `walkRecA` keys.  With J-3b's
  tag-FIRST in-chip keys (`keyV = (1, cid, n, k, v)`, `keyRg = (2, id, k, v)`) they are NOT disjoint
  from those (`RapJetJ8.oldRegKey_recOK` / `oldValKey_recOK`: a registry key `(2, id, k, v)` IS a
  `walkRecA` record with `rootIdx = 2`, a node-value key `(1, cid, n, k, 4)` IS an inc record).  Then a J consume could be served
  by an atom-side provide (and a compute `walkRecA` / inc consume by a J in-chip provide), and
  `Accepted.bal` does not follow from the balance.

  **Fix (no coin, no column, width `71`):** the C-2 step 0 rule applied to the in-chip keys — every
  in-chip key is put in 8 entries with its tag LAST (`tagLast`): `(cid, n, k, v, 0, 0, 0, 1)` and
  `(id, k, v, 0, 0, 0, 0, 2)`.  Entry 7 is then `1` / `2` (in-chip), `3` (jet), `0` (inc and
  `walkRecA`, zero-padded), so the four classes are disjoint as VECTORS (`p > 3`).

  * `jetPre` / **`jetChipJ8`**: `expandChip jetTemplateJ8T` with the 18 verifier-fixed columns
    (`0..10` selectors, `11 / 12` masks, `13..17` the layout numbers) interpolated from a public layout
    `lay : Fin n → PRow`.
-/
import Nock.Jet.ChipJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.Reified Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open scoped Polynomial

/-! ## 2. Tag-last in-chip keys -/

/-- **Tag LAST, 8 entries**: `(t, x₁, …, x_k) ↦ (x₁, …, x_k, 0, …, 0, t)`. -/
def tagLast (l : List KE) : List KE := l.tail ++ List.replicate (8 - l.length) (.k 0) ++ l.take 1

def entsT (es : List (Kd × List KE)) : List (Kd × List KE) := es.map fun e => (e.1, tagLast e.2)

def ents0T : List (Kd × List KE) := entsT ents0
def ents1T : List (Kd × List KE) := entsT ents1
def ents2T : List (Kd × List KE) := entsT ents2

/-- The new in-chip keys are 8 long with tag `1` / `2` last. -/
theorem keyV_T (n k v : KE) : tagLast (keyV n k v) = [.col Col.cid, n, k, v, .k 0, .k 0, .k 0, .k 1] := rfl
theorem keyRg_T : tagLast keyRg = [.col Col.id, .col Col.kN, .col Col.vN, .k 0, .k 0, .k 0, .k 0, .k 2] := rfl

section Gates
variable {F : Type} [Field F]

def slotGatesT (δ : F) : List (QE F) :=
  [ slotGate δ gamT rhoT Col.inv0 ents0T, slotGate δ gamT rhoT Col.inv1 ents1T,
    slotGate δ gamT rhoT Col.inv2 ents2T, slotGate δ gamT rhoT Col.inv3 ents3,
    slotGate δ gamX rhoX Col.invX entsX ]

/-- **The `𝕂`-valued gates of the tag-last chip** (the accumulators are J-3b's: they read only the
selectors, which `entsT` keeps). -/
def gatesJT (δ : F) : List (MixedExpr F) := (slotGatesT δ ++ accGates).flatMap QE.gates

theorem gatesJT_deg_all (δ : F) : (gatesJT δ).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gatesJT, slotGatesT, accGates, slotGate, contribT, contribX, denJ, rlcJ, gpowJ, sumQE, selSum,
    CoeffExpr.sumList, ents0T, ents1T, ents2T, entsT, tagLast, ents0, ents1, ents2, ents3, entsX, keyV,
    keyRg, keyJet, keyX, KE.expr, gamT, rhoT, gamX, rhoX, Kd.sel, QE.gates, QE.var, QE.next, QE.chal,
    QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree,
    CoeffExpr.degree]

theorem gatesJT_degree (δ : F) : ∀ g ∈ gatesJT δ, g.degree ≤ 4 := by
  intro g hg
  simpa using List.all_eq_true.mp (gatesJT_deg_all δ) g hg

/-- **The tag-last J chip template** (base `29`, `𝕂`-roles `0 / 14`, as `jetTemplateJ8`). -/
def jetTemplateJ8T (δ : F) : ChipTemplate F where
  rounds := 2
  rounds_pos := by decide
  baseColsOf := ![29, 0]
  extColsOf := ![0, 14]
  baseTransition := baseGatesJ
  extTransition := []
  mixedTransition := gatesJT δ
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGatesJ_deg
  extTransition_deg := by simp
  mixedTransition_deg := gatesJT_degree δ
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

/-- **Width, MEASURED: `71`** (unchanged by the key fix). -/
theorem jetTemplateJ8T_width (δ : F) : (jetTemplateJ8T δ).width 3 = 71 := rfl

theorem jetTemplateJ8T_baseCols (δ : F) : (jetTemplateJ8T δ).baseCols = 29 := by
  show (∑ r : Fin 2, (![29, 0] : Fin 2 → ℕ) r) = 29
  decide

end Gates

theorem gatesJT_keyOK : (gatesJT (F := ℚ) 7).all keyOKJe = true := by decide +kernel

/-! ## 3. The RAP: verifier-fixed columns from the public layout -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The value of preprocessed column `j < 18` (`j ≠ 11, 12`) on a layout row (`= colOf`). -/
def preCol (q : PRow) (j : ℕ) : F :=
  if j < 11 then (if q.kd.sel = j then 1 else 0) else
  match j with
  | 13 => (q.id : F) | 14 => (q.cid : F) | 15 => (q.nid : F) | 16 => (q.n1 : F) | 17 => (q.n2 : F)
  | _ => 0

/-- The verifier-fixed column `j` at row `i`: the masks at `11 / 12`, the layout elsewhere. -/
def jetPre {n : ℕ} (lay : Fin n → PRow) (j : ℕ) (i : Fin n) : F :=
  if j = 11 then (if (i : ℕ) = 0 then 1 else 0) else
  if j = 12 then (if (i : ℕ) = n - 1 then 1 else 0) else preCol (lay i) j

/-- **The J chip RAP** (tag-last keys), with the 18 verifier-fixed columns interpolated from the
public layout `lay` (the registry rows, then one block per call). -/
noncomputable def jetChipJ8 (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (lay : Fin n → PRow) :
    FixedPreprocessingRAP F where
  rap := expandChip (jetTemplateJ8T δ) b (slotVal b 29 chals) (slotVal b 29 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 2; omega
  fixedCount := 18
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 29 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing j := Lagrange.interpolate Finset.univ nodes (fun i => jetPre lay (j : ℕ) i)

theorem jetChipJ8_width (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (lay : Fin n → PRow) :
    (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w = 71 := jetTemplateJ8T_width δ

end Chip

end Nock.Jet.ChipJ8
