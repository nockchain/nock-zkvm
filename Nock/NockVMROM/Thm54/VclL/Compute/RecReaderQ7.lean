import Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7

/-!
# The record readers over an interface

.

`RecReader G K` abstracts what the VCL node-records chain reads of a PHYSICAL row `e : Env F` besides
the gathered environment: the export / path request records (`recX11`, `recP`) and their activity
flags (`actX`, `actP`) at the gather's field `K'`, with exactly the laws the chain uses:
* the activity laws at one-hot rows,
* the records' roots / children are the DECODED fingerprints of the gathered pull-back
  `(G.env309 (pullEnv e)).base` (so the `fpAt` layer and `fpAt_pullEnv` are absorbed),
* the shared record view's key / axis clauses (`RV.exportKey`, `RV.exportAxis`, `RV.pathKey`, `RV.pathAxis`),
  whose serials are the `K`-lifts of the raw `F` columns (`K` the frame's field).
`recReaderOfBasis b` is the 3-limb instance (laws from `FormulaLookup`/`AccVCL`/`ChipQ7S`/`NodeRecQ7`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State DTcomp FP MemRec Vcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector oneHot_ofSubst)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.RecordCarrier (natLift)
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCodec (records_eq_expected_of_vcomp expectedMr1 expectedMr2
  expectedMr3)
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution (restoredPub_eval_of_oneHot)
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.SVWalk

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-- The serial column of export slot `s` (`fIdx`, `vIdx 0`, `vIdx 1`). -/
def xIdxCol : ℕ → ℕ
  | 0 => fIdxCol
  | 1 => vIdxCol 0
  | _ => vIdxCol 1

/-- The root-serial column of path slot `s`. -/
def pIdxCol : ℕ → ℕ
  | 0 => vIdxCol 0
  | _ => vIdxCol 1

section reader
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [Field K'] [Algebra F K'] [DecidableEq K']

/-- The gathered pull-back (`Env309.base`) of a physical row. -/
abbrev gatheredBase (G : CoordGather F K') (e : Env F) : CorrectedFinalTypedEnv F K' :=
  (G.env309 (pullEnv e)).base

/-- **The record readers over an interface** (see the module doc). -/
structure RecReader (G : CoordGather F K') (K : Type) [Field K] [Algebra F K] where
  recX11 : Env F → ℕ → Fin 11 → K'
  recP : Env F → ℕ → Fin 8 → K'
  actX : Env F → ℕ → K'
  actP : Env F → ℕ → K'
  actX_zero : ∀ e, actX e 0 = 1
  actX_one : ∀ e st, SelAt e st →
    (st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) → actX e 1 = 1
  actX_two : ∀ e, SelAt e .s6 → actX e 2 = 1
  /-- export slot 0 / 1 / 2 roots and children are the decoded fingerprints -/
  xroot0 : ∀ e st, RV.exportRoot (recX11 e 0) = (StrategyOfTracesLift.decodePub (gatheredBase G e) st).f
  xchild0 : ∀ e, RV.exportChild (recX11 e 0) = (StrategyOfTracesLift.decodeDec (gatheredBase G e)).f_t
  xroot1 : ∀ e, RV.exportRoot (recX11 e 1) = (StrategyOfTracesLift.decodeDec (gatheredBase G e)).f_t
  xchild1 : ∀ e, RV.exportChild (recX11 e 1) = (StrategyOfTracesLift.decodeDec (gatheredBase G e)).f_th
  xroot2 : ∀ e, RV.exportRoot (recX11 e 2) = (StrategyOfTracesLift.decodeDec (gatheredBase G e)).f_tt
  xchild2 : ∀ e, RV.exportChild (recX11 e 2) = (StrategyOfTracesLift.decodeDec (gatheredBase G e)).f_tth
  xaxis : ∀ e s, s < 3 → RV.exportAxis (recX11 e s) = if s = 0 then 3 else 2
  /-- export key: the serial column lifted through the frame's `K` -/
  xkey : ∀ e s, s < 3 → RV.exportKey (recX11 e s) =
    .export (natLift (algebraMap F K (e.trace (xIdxCol s)))) (decide (s = 0))
  proot0 : ∀ e st, RV.pathRoot (recP e 0) = (StrategyOfTracesLift.decodePub (gatheredBase G e) st).s
  pchild0 : ∀ e st st', OneHotSelector (gatheredBase G e).toSourceEnv st → st ≠ .s1 →
    RV.pathChild (recP e 0) = (StrategyOfTracesLift.decodePub (gatheredBase G e) st').e
  proot1 : ∀ e st, RV.pathRoot (recP e 1) = (StrategyOfTracesLift.decodePub (gatheredBase G e) st).sf1_e
  pchild1 : ∀ e st st', OneHotSelector (gatheredBase G e).toSourceEnv st → st ≠ .s3 ∧ st ≠ .s4 →
    RV.pathChild (recP e 1) = (StrategyOfTracesLift.decodePub (gatheredBase G e) st').sf2_f
  paxis : ∀ e s, s < 2 → RV.pathAxis (recP e s) = natLift (algebraMap F K (e.trace axCol))
  pkey : ∀ e s, s < 2 → RV.pathKey (recP e s) =
    .path (natLift (algebraMap F K (e.trace (pIdxCol s)))) (natLift (algebraMap F K (e.trace axCol)))

end reader

/-! ## Env-only lemmas, over any gathered environment (moved from `NodeRecQ7`, generalized) -/

namespace NodeRecQ7

section act
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem actX_one_of_sel (env : Env F) (st : State) (h : SelAt env st)
    (hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) :
    actX (K := K) env 1 = 1 := by
  have ht := selAt_trace h
  simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
    ht 8 (by norm_num), ht 9 (by norm_num)]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [selIdx]

theorem actX_two_s6 (env : Env F) (h : SelAt env .s6) : actX (K := K) env 2 = 1 := by
  simp only [actX]; rw [selAt_trace h 6 (by norm_num)]; simp [selIdx]

theorem actP_zero_s0 (env : Env F) (h : SelAt env .s0) : actP (K := K) env 0 = 1 := by
  simp only [actP]; rw [selAt_trace h 0 (by norm_num)]; simp [selIdx]

theorem actP_one_s9 (env : Env F) (h : SelAt env .s9) : actP (K := K) env 1 = 1 := by
  simp only [actP]; rw [selAt_trace h 9 (by norm_num)]; simp [selIdx]

end act

section decode
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- `Pub.e` (role 2, overlay-hosted only at `s1`) is the physical role at a one-hot row off `s1`,
at ANY gathered environment. -/
theorem decodePub_e_oneHotG (ge : CorrectedFinalTypedEnv F K) (st st' : State) (hst : st ≠ .s1)
    (h : OneHotSelector ge.toSourceEnv st) :
    (StrategyOfTracesLift.decodePub ge st').e =
      ⟨(pubFP .traceCur 2 0).eval ge.toSourceEnv, (pubFP .traceCur 2 1).eval ge.toSourceEnv,
        (pubFP .traceCur 2 2).eval ge.toSourceEnv⟩ := by
  have key : ∀ c : ℕ, c < 3 → (restoredPub .traceCur 2 c).eval ge.toSourceEnv =
      (pubFP .traceCur 2 c).eval ge.toSourceEnv := by
    intro c hc
    rw [restoredPub_eval_of_oneHot _ st h]
    cases st <;> simp_all [sourcePubAt, overlayANat, overlayBNat]
  have h0 : computeTraceSubst .traceCur 17 = restoredPub .traceCur 2 0 := rfl
  have h1 : computeTraceSubst .traceCur 18 = restoredPub .traceCur 2 1 := rfl
  have h2 : computeTraceSubst .traceCur 19 = restoredPub .traceCur 2 2 := rfl
  show (⟨(computeTraceSubst .traceCur 17).eval _, (computeTraceSubst .traceCur 18).eval _,
    (computeTraceSubst .traceCur 19).eval _⟩ : FP K) = _
  rw [h0, h1, h2, key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num)]

/-- `Pub.sf2_f` (role 7, overlay-hosted only at `s3`/`s4`) is the physical role off those states. -/
theorem decodePub_sf2f_oneHotG (ge : CorrectedFinalTypedEnv F K) (st st' : State)
    (hst : st ≠ .s3 ∧ st ≠ .s4) (h : OneHotSelector ge.toSourceEnv st) :
    (StrategyOfTracesLift.decodePub ge st').sf2_f =
      ⟨(pubFP .traceCur 7 0).eval ge.toSourceEnv, (pubFP .traceCur 7 1).eval ge.toSourceEnv,
        (pubFP .traceCur 7 2).eval ge.toSourceEnv⟩ := by
  have key : ∀ c : ℕ, c < 3 → (restoredPub .traceCur 7 c).eval ge.toSourceEnv =
      (pubFP .traceCur 7 c).eval ge.toSourceEnv := by
    intro c hc
    rw [restoredPub_eval_of_oneHot _ st h]
    obtain ⟨h3, h4⟩ := hst
    cases st <;> simp_all [sourcePubAt, overlayANat, overlayBNat]
  have h0 : computeTraceSubst .traceCur 32 = restoredPub .traceCur 7 0 := rfl
  have h1 : computeTraceSubst .traceCur 33 = restoredPub .traceCur 7 1 := rfl
  have h2 : computeTraceSubst .traceCur 34 = restoredPub .traceCur 7 2 := rfl
  show (⟨(computeTraceSubst .traceCur 32).eval _, (computeTraceSubst .traceCur 33).eval _,
    (computeTraceSubst .traceCur 34).eval _⟩ : FP K) = _
  rw [h0, h1, h2, key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num)]

end decode

end NodeRecQ7

/-! ## The 3-limb instance -/

section ofBasis
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K]

theorem recX11_lt (b : Basis (Fin 3) F K) (e : Env F) (s i : ℕ) (hi : i < 10) :
    recX11 b e s ⟨i, by omega⟩ = recX b e s ⟨i, hi⟩ := by
  simp [recX11, Fin.snoc, hi]

theorem recX11_ten (b : Basis (Fin 3) F K) (e : Env F) (s : ℕ) :
    recX11 b e s 10 = sideVal s := by
  unfold recX11; exact Fin.snoc_last (α := fun _ => K) _ _

theorem exportChild_recX11_zero (b : Basis (Fin 3) F K) (e : Env F) :
    RV.exportChild (recX11 b e 0) = ⟨recX b e 0 6, recX b e 0 7, recX b e 0 8⟩ := by
  have h1 : recX11 b e 0 10 = 1 := by rw [recX11_ten]; rfl
  simp only [RV.exportChild, RV.sideOf, h1, decide_true, if_true, RV.fpAt]
  rw [recX11_lt b e 0 6 (by omega), recX11_lt b e 0 7 (by omega), recX11_lt b e 0 8 (by omega)]
  rfl

theorem exportChild_recX11_ne (b : Basis (Fin 3) F K) (e : Env F) (s : ℕ) (hs : s ≠ 0) :
    RV.exportChild (recX11 b e s) = ⟨recX b e s 3, recX b e s 4, recX b e s 5⟩ := by
  have h1 : recX11 b e s 10 ≠ 1 := by rw [recX11_ten, sideVal_ne s hs]; exact zero_ne_one
  simp only [RV.exportChild, RV.sideOf, h1, decide_false, Bool.false_eq_true, if_false, RV.fpAt]
  rw [recX11_lt b e s 3 (by omega), recX11_lt b e s 4 (by omega), recX11_lt b e s 5 (by omega)]
  rfl

theorem exportKey_recX11 (b : Basis (Fin 3) F K) (e : Env F) (s : ℕ) :
    RV.exportKey (recX11 b e s) = .export (natLift (recX b e s 9)) (decide (s = 0)) := by
  have h9 : recX11 b e s 9 = recX b e s 9 := recX11_lt b e s 9 (by omega)
  have h10 : decide (recX11 b e s 10 = 1) = decide (s = 0) := by
    rw [recX11_ten]; unfold sideVal; by_cases h : s = 0 <;> simp [h]
  simp only [RV.exportKey, RV.sideOf, h10]
  rw [h9]

theorem exportAxis_recX11 (b : Basis (Fin 3) F K) (e : Env F) (s : ℕ) :
    RV.exportAxis (recX11 b e s) = if s = 0 then 3 else 2 := by
  simp only [RV.exportAxis, RV.sideOf, recX11_ten]
  unfold sideVal; by_cases h : s = 0 <;> simp [h]

/-- **The 3-limb record reader** (`recReaderOfBasis b`): the existing `recX11`/`recP`/`actX`/`actP`. -/
def recReaderOfBasis (b : Basis (Fin 3) F K) : RecReader (CoordGather.ofBasis b) K where
  recX11 := recX11 b
  recP := recP b
  actX := actX
  actP := actP
  actX_zero _ := rfl
  actX_one := NodeRecQ7.actX_one_of_sel
  actX_two e h := NodeRecQ7.actX_two_s6 e h
  xroot0 e st := (show RV.exportRoot (recX11 b e 0) = fpAt b e roleF from rfl).trans
    ((fpAt_pullEnv b e roleF (by decide)).symm.trans rfl)
  xchild0 e := by
    rw [exportChild_recX11_zero]
    exact (show (⟨recX b e 0 6, recX b e 0 7, recX b e 0 8⟩ : FP K) = fpAt b e roleFt from rfl).trans
      ((fpAt_pullEnv b e roleFt (by decide)).symm.trans rfl)
  xroot1 e := (show RV.exportRoot (recX11 b e 1) = fpAt b e roleFt from rfl).trans
    ((fpAt_pullEnv b e roleFt (by decide)).symm.trans rfl)
  xchild1 e := by
    rw [exportChild_recX11_ne b e 1 (by decide)]
    exact (show (⟨recX b e 1 3, recX b e 1 4, recX b e 1 5⟩ : FP K) = fpAt b e roleFth from rfl).trans
      ((fpAt_pullEnv b e roleFth (by decide)).symm.trans rfl)
  xroot2 e := (show RV.exportRoot (recX11 b e 2) = fpAt b e roleFtt from rfl).trans
    ((fpAt_pullEnv b e roleFtt (by decide)).symm.trans rfl)
  xchild2 e := by
    rw [exportChild_recX11_ne b e 2 (by decide)]
    exact (show (⟨recX b e 2 3, recX b e 2 4, recX b e 2 5⟩ : FP K) = fpAt b e roleFtth from rfl).trans
      ((fpAt_pullEnv b e roleFtth (by decide)).symm.trans rfl)
  xaxis e s _ := exportAxis_recX11 b e s
  xkey e s hs := by
    rw [exportKey_recX11]
    rcases s with _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · omega
  proot0 e st := (show RV.pathRoot (recP b e 0) = fpAt b e roleS from rfl).trans
    ((fpAt_pullEnv b e roleS (by decide)).symm.trans rfl)
  pchild0 e st st' h hne := (show RV.pathChild (recP b e 0) = fpAt b e roleE from rfl).trans
    ((fpAt_pullEnv b e roleE (by decide)).symm.trans
      (NodeRecQ7.decodePub_e_oneHotG _ st st' hne h).symm)
  proot1 e st := (show RV.pathRoot (recP b e 1) = fpAt b e roleSf1E from rfl).trans
    ((fpAt_pullEnv b e roleSf1E (by decide)).symm.trans rfl)
  pchild1 e st st' h hne := (show RV.pathChild (recP b e 1) = fpAt b e roleSf2F from rfl).trans
    ((fpAt_pullEnv b e roleSf2F (by decide)).symm.trans
      (NodeRecQ7.decodePub_sf2f_oneHotG _ st st' hne h).symm)
  paxis e s hs := by
    rcases s with _ | _ | s
    · rfl
    · rfl
    · omega
  pkey e s hs := by
    rcases s with _ | _ | s
    · rfl
    · rfl
    · omega

end ofBasis

/-! ## The key clauses over (gather, reader) -/

section keysG
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [Field K'] [Algebra F K'] [DecidableEq K']
  {G : CoordGather F K'} (R : RecReader G K) {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T]

/-- **The export key clause over a reader** (`export_key_clauseQ7'`). -/
theorem export_key_clauseQ7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (st : State) (s : ℕ) (hs : s = 0 ∨ (s = 1 ∧ st ≠ .s0) ∨ (s = 2 ∧ st ≠ .s9)) :
    RV.exportKey (R.recX11 (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7' V (b0 (T := T) Q) st (2 * i) s := by
  rw [recKeyQ7'_even]
  rcases hs with rfl | ⟨rfl, hst⟩ | ⟨rfl, hst⟩
  · rw [R.xkey _ 0 (by norm_num)]
    simp only [recKeyQ7, decide_true]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl
  · rw [R.xkey _ 1 (by norm_num)]
    simp only [recKeyQ7, if_neg hst]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl
  · rw [R.xkey _ 2 (by norm_num)]
    simp only [recKeyQ7, if_neg hst]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl

/-- **The path key clause over a reader** (`path_key_clauseQ7'`). -/
theorem path_key_clauseQ7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (s : ℕ) (hs : s < 2) :
    RV.pathKey (R.recP (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7' V (b0 (T := T) Q) (if s = 0 then .s0 else .s9) (2 * i) (s + 1) := by
  rw [recKeyQ7'_even, R.pkey _ s hs]
  interval_cases s
  · simp only [recKeyQ7, pIdxCol]
    rw [b0NatAt_row V chalV pubVal Q i, b0NatAt_row V chalV pubVal Q i]; rfl
  · simp only [recKeyQ7, pIdxCol, show (1 : ℕ) ≠ 0 by decide, if_false]
    rw [b0NatAt_row V chalV pubVal Q i, b0NatAt_row V chalV pubVal Q i]; rfl

end keysG

end

end VclL.Compute
end Nock.NockVMROM.Thm54
