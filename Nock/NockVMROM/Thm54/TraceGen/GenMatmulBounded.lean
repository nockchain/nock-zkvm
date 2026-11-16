/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulBounded.lean

  `SemanticSkeleton.BoundedBy 65537` on the generated F65537 matmul
  carrier, then `ExactExecutionNounRealization` and the cumulative
  language from the already-proved `BindsAt` / `TraversableChained`.

  Compute boundedness is fuel-induction on `genComputeSkeleton` (atoms
  grow by at most one per OP4, so `B + fuel` stays below `q`).  Memory
  boundedness is noun-walk / axis-descent induction on the annotated
  forest, not an 401-way BFS split.

  `ExactExecutionSemanticData` / `memoryTrace` are not claimed here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTopology
import Nock.NockVMROM.Thm54.TraceGen.GenTierABounded
import Nock.NockVMROM.Thm54.TraceGen.GenRowSemantic
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.FieldEmbedding

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Bound monotonicity -/

theorem BoundedBy_mono {q q' : ℕ} {n : Noun} (h : q ≤ q') :
    FieldEmbedding.BoundedBy q n → FieldEmbedding.BoundedBy q' n := by
  induction n with
  | atom a =>
    intro ha
    simp [FieldEmbedding.BoundedBy] at ha ⊢
    omega
  | cell l r ihl ihr =>
    intro hn
    exact ⟨ihl (FieldEmbedding.BoundedBy_cell.mp hn).1,
      ihr (FieldEmbedding.BoundedBy_cell.mp hn).2⟩

theorem atom0_boundedBy {q : ℕ} (h : 0 < q) :
    FieldEmbedding.BoundedBy q (.atom 0) := by
  simp [FieldEmbedding.BoundedBy, h]

theorem formulaHead_boundedBy {q : ℕ} {n : Noun} (h0 : 0 < q)
    (hn : FieldEmbedding.BoundedBy q n) :
    FieldEmbedding.BoundedBy q (formulaHead n) := by
  cases n with
  | atom _ => simpa [formulaHead]
  | cell h t => exact (FieldEmbedding.BoundedBy_cell.mp hn).1

theorem formulaTail_boundedBy {q : ℕ} {n : Noun} (h0 : 0 < q)
    (hn : FieldEmbedding.BoundedBy q n) :
    FieldEmbedding.BoundedBy q (formulaTail n) := by
  cases n with
  | atom _ => simpa [formulaTail]
  | cell h t => exact (FieldEmbedding.BoundedBy_cell.mp hn).2

theorem computeSkel_bounded_mono {q q' : ℕ} {s : ComputeRowSkeleton}
    (h : q ≤ q') (hb : s.BoundedBy q) : s.BoundedBy q' :=
  ⟨BoundedBy_mono h hb.1, BoundedBy_mono h hb.2.1, BoundedBy_mono h hb.2.2.1,
    fun slot hs => BoundedBy_mono h (hb.2.2.2.1 slot hs),
    fun i hi slot => BoundedBy_mono h (hb.2.2.2.2.1 i hi slot),
    fun i hi => ⟨BoundedBy_mono h (hb.2.2.2.2.2 i hi).1,
      BoundedBy_mono h (hb.2.2.2.2.2 i hi).2⟩⟩

/-! ## Remaining `genSkel*` bounds -/

theorem genSkelCons_bounded {q : ℕ}
    {subject leftF rightF leftR rightR : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hlf : FieldEmbedding.BoundedBy q leftF)
    (hrf : FieldEmbedding.BoundedBy q rightF)
    (hlr : FieldEmbedding.BoundedBy q leftR)
    (hrr : FieldEmbedding.BoundedBy q rightR) :
    (genSkelCons subject leftF rightF leftR rightR).BoundedBy q := by
  refine ⟨hs, FieldEmbedding.BoundedBy_cell.mpr ⟨hlf, hrf⟩,
    FieldEmbedding.BoundedBy_cell.mpr ⟨hlr, hrr⟩, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelCons] using hlf
    | f_t => simpa [genSkelCons] using hrf
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelCons, decActive, hasTailDecomposition] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelCons, ComputeTable.fanoutComp] at hi ⊢
    · exact hs
    · exact hlf
    · exact hlr
    · exact hs
    · exact hrf
    · exact hrr
  · intro i hi
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelCons, Nock.Framework.recordCount] using hi
      exact Fin.ext (by omega)
    subst i
    change FieldEmbedding.BoundedBy q (.cell leftF rightF) ∧
      FieldEmbedding.BoundedBy q rightF
    exact ⟨FieldEmbedding.BoundedBy_cell.mpr ⟨hlf, hrf⟩, hrf⟩

theorem genSkelOp0_bounded {q : ℕ}
    {subject formula head tail result : Noun} {axis : ℕ}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (ht : FieldEmbedding.BoundedBy q tail)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp0 subject formula head tail result axis).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp0] using hh
    | f_t => simpa [genSkelOp0] using ht
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp0, decActive, hasTailDecomposition] at hact
  · intro i hi slot
    simp [genSkelOp0, ComputeTable.fanoutComp] at hi
  · intro i hi
    fin_cases i <;> simp [genSkelOp0, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, ht⟩
    · exact ⟨hs, hr⟩

theorem genSkelOp3_bounded {q : ℕ}
    {subject formula head tail callSubject callFormula callResult result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (ht : FieldEmbedding.BoundedBy q tail)
    (hcs : FieldEmbedding.BoundedBy q callSubject)
    (hcf : FieldEmbedding.BoundedBy q callFormula)
    (hcr : FieldEmbedding.BoundedBy q callResult)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp3 subject formula head tail callSubject callFormula callResult
      result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp3] using hh
    | f_t => simpa [genSkelOp3] using ht
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp3, decActive, hasTailDecomposition] at hact
  · intro i hi slot
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelOp3, ComputeTable.fanoutComp] using hi
      exact Fin.ext (by omega)
    subst i
    cases slot <;> simp [genSkelOp3]
    · exact hcs
    · exact hcf
    · exact hcr
  · intro i hi
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelOp3, Nock.Framework.recordCount] using hi
      exact Fin.ext (by omega)
    subst i
    simp [genSkelOp3, MemRecSkeleton.BoundedBy]
    exact ⟨hf, ht⟩

theorem genSkelOp4_bounded {q : ℕ}
    {subject formula head tail callSubject callFormula callResult result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (ht : FieldEmbedding.BoundedBy q tail)
    (hcs : FieldEmbedding.BoundedBy q callSubject)
    (hcf : FieldEmbedding.BoundedBy q callFormula)
    (hcr : FieldEmbedding.BoundedBy q callResult)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp4 subject formula head tail callSubject callFormula callResult
      result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp4] using hh
    | f_t => simpa [genSkelOp4] using ht
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp4, decActive, hasTailDecomposition] at hact
  · intro i hi slot
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelOp4, ComputeTable.fanoutComp] using hi
      exact Fin.ext (by omega)
    subst i
    cases slot <;> simp [genSkelOp4]
    · exact hcs
    · exact hcf
    · exact hcr
  · intro i hi
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelOp4, Nock.Framework.recordCount] using hi
      exact Fin.ext (by omega)
    subst i
    simp [genSkelOp4, MemRecSkeleton.BoundedBy]
    exact ⟨hf, ht⟩

theorem genSkelOp5_bounded {q : ℕ}
    {subject formula head fTail fTh fTt sf1 sf2 result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (hs1 : FieldEmbedding.BoundedBy q sf1)
    (hs2 : FieldEmbedding.BoundedBy q sf2)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp5] using hh
    | f_t => simpa [genSkelOp5] using hft
    | f_th => simpa [genSkelOp5] using hth
    | f_tt => simpa [genSkelOp5] using htt
    | f_tth | f_ttt =>
      simp [genSkelOp5, decActive] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp5, ComputeTable.fanoutComp] at hi ⊢
    · exact hs
    · exact hth
    · exact hs1
    · exact hs
    · exact htt
    · exact hs2
  · intro i hi
    fin_cases i <;> simp [genSkelOp5, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩

theorem genSkelOp7_bounded {q : ℕ}
    {subject formula head fTail fTh fTt sb result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (hsb : FieldEmbedding.BoundedBy q sb)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp7 subject formula head fTail fTh fTt sb result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp7] using hh
    | f_t => simpa [genSkelOp7] using hft
    | f_th => simpa [genSkelOp7] using hth
    | f_tt => simpa [genSkelOp7] using htt
    | f_tth | f_ttt =>
      simp [genSkelOp7, decActive] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp7, ComputeTable.fanoutComp] at hi ⊢
    · exact hsb
    · exact htt
    · exact hr
    · exact hs
    · exact hth
    · exact hsb
  · intro i hi
    fin_cases i <;> simp [genSkelOp7, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩

theorem genSkelOp8_bounded {q : ℕ}
    {subject formula head fTail fTh fTt sb result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (hsb : FieldEmbedding.BoundedBy q sb)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp8 subject formula head fTail fTh fTt sb result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp8] using hh
    | f_t => simpa [genSkelOp8] using hft
    | f_th => simpa [genSkelOp8] using hth
    | f_tt => simpa [genSkelOp8] using htt
    | f_tth | f_ttt =>
      simp [genSkelOp8, decActive] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp8, ComputeTable.fanoutComp] at hi ⊢
    · exact FieldEmbedding.BoundedBy_cell.mpr ⟨hsb, hs⟩
    · exact htt
    · exact hr
    · exact hs
    · exact hth
    · exact hsb
  · intro i hi
    fin_cases i <;> simp [genSkelOp8, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩

/-! ## Generated compute trees -/

theorem reqs_bounded_cons {q : ℕ} {ts : K} {leftF rightF : Noun}
    (hlf : FieldEmbedding.BoundedBy q leftF)
    (hrf : FieldEmbedding.BoundedBy q rightF) :
    ∀ r : ServiceReq K,
      r ∈ [{ root := (.cell leftF rightF), child := rightF, axis := 3, ts := ts }] →
      FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child := by
  intro r hr
  simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
  subst r
  exact ⟨FieldEmbedding.BoundedBy_cell.mpr ⟨hlf, hrf⟩, hrf⟩

theorem genComputeSkeleton_evalN
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    Nock.evalN fuel subject formula = some result := by
  induction fuel generalizing subject formula t result with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ =>
          simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [Nock.evalN, ih hL, ih hR]
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · cases tl with
          | cell _ _ =>
            simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none =>
              simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [Nock.evalN, hslot]
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [Nock.evalN]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ =>
                  simp [genComputeSkeleton, hBcall, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hBcall, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp [Nock.evalN, ih hBcall, ih hC, ih hM]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [Nock.evalN, ih hcall]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none =>
              simp [genComputeSkeleton, hcall, hlus] at h
            | some lusR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [Nock.evalN, ih hcall, hlus]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [Nock.evalN, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ =>
              simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ =>
                simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ =>
                  simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp [Nock.evalN, ih hcond, hval, ih htaken]
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp [Nock.evalN, ih hcond, hval, ih htaken]
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [Nock.evalN, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [Nock.evalN, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ =>
              simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none =>
                  simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    simp [Nock.evalN, ih hcore, hslot, ih hinv]
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

theorem evalGBy_eq_of_evalN {q fuel : ℕ} {s f r r' : Noun} (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : FieldEmbedding.evalGBy q fuel s f = some r)
    (hN : Nock.evalN fuel s f = some r') : r = r' :=
  Option.some.inj
    ((FieldEmbedding.agreeBy q hq fuel s f r hs hf hG).1.symm.trans hN)

theorem evalGBy_result_of_gen {q fuel : ℕ} (hq : 1 < q)
    {s f : Noun} {t : NTree (GenComputeRow K)} {r rG : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : FieldEmbedding.evalGBy q fuel s f = some rG)
    (h : genComputeSkeleton (K := K) fuel s f = .ok (t, r)) :
    rG = r :=
  evalGBy_eq_of_evalN hq hs hf hG (genComputeSkeleton_evalN h)

theorem atom1_boundedBy {q : ℕ} (hq : 1 < q) :
    FieldEmbedding.BoundedBy q (.atom 1) := hq

theorem cell_boundedBy {q : ℕ} {l r : Noun}
    (hl : FieldEmbedding.BoundedBy q l) (hr : FieldEmbedding.BoundedBy q r) :
    FieldEmbedding.BoundedBy q (.cell l r) :=
  FieldEmbedding.BoundedBy_cell.mpr ⟨hl, hr⟩

/-! ## Guarded evaluator combinators -/

theorem evalGBy_s0_exact {q fuel axis : ℕ} {subject result : Noun}
    (hslot : Noun.slot axis subject = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject (.cell (.atom 0) (.atom axis)) =
      some result := by
  simpa only [FieldEmbedding.evalGBy] using hslot

theorem evalGBy_s1_exact (q fuel : ℕ) (subject result : Noun) :
    FieldEmbedding.evalGBy q (fuel + 1) subject (.cell (.atom 1) result) =
      some result := by
  rfl

theorem evalGBy_s4_exact {q fuel : ℕ} {subject tail value result : Noun}
    (hcall : FieldEmbedding.evalGBy q fuel subject tail = some value)
    (hinc : FieldEmbedding.lusGBy q value = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject (.cell (.atom 4) tail) =
      some result := by
  simp only [FieldEmbedding.evalGBy, hcall, Option.bind_some]
  exact hinc

theorem evalGBy_s5_exact {q fuel : ℕ} {subject left right leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalGBy q fuel subject left = some leftResult)
    (hright : FieldEmbedding.evalGBy q fuel subject right = some rightResult) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.atom 5) (.cell left right)) =
      some (Noun.tis leftResult rightResult) := by
  simp only [FieldEmbedding.evalGBy, hleft, hright]

theorem evalGBy_s6_zero_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : FieldEmbedding.evalGBy q fuel subject condition = some (.atom 0))
    (hbranch : FieldEmbedding.evalGBy q fuel subject yesBranch = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) =
      some result := by
  simp only [FieldEmbedding.evalGBy, hcondition]
  exact hbranch

theorem evalGBy_s6_one_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : FieldEmbedding.evalGBy q fuel subject condition = some (.atom 1))
    (hbranch : FieldEmbedding.evalGBy q fuel subject noBranch = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) =
      some result := by
  simp only [FieldEmbedding.evalGBy, hcondition]
  exact hbranch

theorem evalGBy_s7_exact {q fuel : ℕ}
    {subject first second intermediate result : Noun}
    (hfirst : FieldEmbedding.evalGBy q fuel subject first = some intermediate)
    (hsecond : FieldEmbedding.evalGBy q fuel intermediate second = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.atom 7) (.cell first second)) = some result := by
  simp only [FieldEmbedding.evalGBy, hfirst]
  exact hsecond

theorem evalGBy_s9_exact {q fuel axis : ℕ}
    {subject coreFormula core arm result : Noun}
    (hcore : FieldEmbedding.evalGBy q fuel subject coreFormula = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalGBy q fuel core arm = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) coreFormula)) = some result := by
  simp only [FieldEmbedding.evalGBy, hcore, hslot]
  exact harm

theorem evalGBy_cons_exact {q fuel : ℕ}
    {subject headLeft headRight tail leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalGBy q fuel subject (.cell headLeft headRight) =
      some leftResult)
    (hright : FieldEmbedding.evalGBy q fuel subject tail = some rightResult) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.cell headLeft headRight) tail) =
      some (.cell leftResult rightResult) := by
  simp only [FieldEmbedding.evalGBy, hleft, hright]

theorem evalGBy_succ {q fuel : ℕ} {subject formula result : Noun}
    (h : FieldEmbedding.evalGBy q fuel subject formula = some result) :
    FieldEmbedding.evalGBy q (fuel + 1) subject formula = some result := by
  induction fuel, subject, formula using FieldEmbedding.evalGBy.induct q
      generalizing result with
  | case11 fuel subject tail ih =>
      simp only [FieldEmbedding.evalGBy, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subject tail ih =>
      simp only [FieldEmbedding.evalGBy, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ => simp_all [FieldEmbedding.evalGBy]

theorem evalGBy_mono {q n m : ℕ} {subject formula result : Noun}
    (hnm : n ≤ m)
    (h : FieldEmbedding.evalGBy q n subject formula = some result) :
    FieldEmbedding.evalGBy q m subject formula = some result := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact evalGBy_succ ih

theorem lusGBy_mod_le {q q' : ℕ} {x m : Noun} (hqq : q ≤ q')
    (h : FieldEmbedding.lusGBy q x = some m) :
    FieldEmbedding.lusGBy q' x = some m := by
  cases x with
  | atom n =>
    simp only [FieldEmbedding.lusGBy] at h ⊢
    split at h
    · rename_i hlt
      simp only [Nat.lt_of_lt_of_le hlt hqq]
      exact h
    · simp at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

theorem evalGBy_mod_le {q q' : ℕ} (hqq : q ≤ q') :
    ∀ (fuel : ℕ) (s f r : Noun),
      FieldEmbedding.evalGBy q fuel s f = some r →
        FieldEmbedding.evalGBy q' fuel s f = some r := by
  intro fuel
  induction fuel with
  | zero => intro s f r h; simp [FieldEmbedding.evalGBy] at h
  | succ fuel ih =>
    intro s f r h
    match f with
    | .atom _ => simp [FieldEmbedding.evalGBy] at h
    | .cell (.cell b c) d =>
      simp only [FieldEmbedding.evalGBy] at h ⊢
      cases hbc : FieldEmbedding.evalGBy q fuel s (.cell b c) with
      | none => rw [hbc] at h; simp at h
      | some l =>
        cases hd : FieldEmbedding.evalGBy q fuel s d with
        | none => rw [hbc, hd] at h; simp at h
        | some r' =>
          rw [hbc, hd] at h
          rw [ih s (.cell b c) l hbc, ih s d r' hd]
          exact h
    | .cell (.atom op) tail =>
      match op with
      | 0 | 1 => simpa [FieldEmbedding.evalGBy] using h
      | 2 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell b c =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hb : FieldEmbedding.evalGBy q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            cases hc : FieldEmbedding.evalGBy q fuel s c with
            | none => rw [hb, hc] at h; simp at h
            | some sc =>
              rw [hb, hc] at h
              rw [ih s b sb hb, ih s c sc hc]
              exact ih sb sc r h
      | 3 =>
        simp only [FieldEmbedding.evalGBy] at h ⊢
        cases ht : FieldEmbedding.evalGBy q fuel s tail with
        | none => rw [ht] at h; simp at h
        | some v =>
          rw [ht] at h
          rw [ih s tail v ht]
          exact h
      | 4 =>
        simp only [FieldEmbedding.evalGBy] at h ⊢
        cases ht : FieldEmbedding.evalGBy q fuel s tail with
        | none => rw [ht] at h; simp at h
        | some v =>
          rw [ht] at h
          rw [ih s tail v ht]
          exact lusGBy_mod_le hqq h
      | 5 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell b c =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hb : FieldEmbedding.evalGBy q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            cases hc : FieldEmbedding.evalGBy q fuel s c with
            | none => rw [hb, hc] at h; simp at h
            | some sc =>
              rw [hb, hc] at h
              rw [ih s b sb hb, ih s c sc hc]
              exact h
      | 6 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell _ (.atom _) => simp [FieldEmbedding.evalGBy] at h
        | .cell b (.cell c d) =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hb : FieldEmbedding.evalGBy q fuel s b with
          | none => rw [hb] at h; simp at h
          | some vb =>
            rw [hb] at h
            rw [ih s b vb hb]
            match vb with
            | .atom 0 => exact ih s c r h
            | .atom 1 => exact ih s d r h
            | .atom (_ + 2) => simp at h
            | .cell _ _ => simp at h
      | 7 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell b c =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hb : FieldEmbedding.evalGBy q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            rw [hb] at h
            rw [ih s b sb hb]
            exact ih sb c r h
      | 8 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell b c =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hb : FieldEmbedding.evalGBy q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            rw [hb] at h
            rw [ih s b sb hb]
            exact ih (.cell sb s) c r h
      | 9 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.cell _ _) _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.atom ax) c =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hc : FieldEmbedding.evalGBy q fuel s c with
          | none => rw [hc] at h; simp at h
          | some core =>
            rw [hc] at h
            rw [ih s c core hc]
            cases hslot : Noun.slot ax core with
            | none => simp [hslot] at h
            | some arm =>
              simp [hslot] at h ⊢
              exact ih core arm r h
      | 10 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.atom _) _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.cell (.cell _ _) _) _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.cell (.atom ax) c) d =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hc : FieldEmbedding.evalGBy q fuel s c with
          | none => rw [hc] at h; simp at h
          | some new =>
            cases hd : FieldEmbedding.evalGBy q fuel s d with
            | none => rw [hc, hd] at h; simp at h
            | some old =>
              rw [hc, hd] at h
              rw [ih s c new hc, ih s d old hd]
              exact h
      | 11 =>
        match tail with
        | .atom _ => simp [FieldEmbedding.evalGBy] at h
        | .cell (.cell _ clue) body =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          cases hclue : FieldEmbedding.evalGBy q fuel s clue with
          | none => rw [hclue] at h; simp at h
          | some clueR =>
            rw [hclue] at h
            rw [ih s clue clueR hclue]
            exact ih s body r h
        | .cell (.atom _) body =>
          simp only [FieldEmbedding.evalGBy] at h ⊢
          exact ih s body r h
      | _ + 12 => simp [FieldEmbedding.evalGBy] at h

theorem lusG_succ {n : ℕ} (h : n + 1 < 97) :
    FieldEmbedding.lusGBy 97 (.atom n) = some (.atom (n + 1)) := by
  simp [FieldEmbedding.lusGBy, h]


theorem evalG_quote (q fuel : ℕ) (subject result : Noun) :
    FieldEmbedding.evalGBy q (fuel + 1) subject (quote result) = some result :=
  evalGBy_s1_exact q fuel subject result

theorem evalG_op1 (q fuel : ℕ) (subject : Noun) (k : ℕ) :
    FieldEmbedding.evalGBy q (fuel + 1) subject (op1 k) = some (.atom k) :=
  evalGBy_s1_exact q fuel subject (.atom k)

theorem evalG_op0 (q n axis : ℕ) {subject result : Noun}
    (h : Noun.slot axis subject = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject (op0 axis) = some result :=
  evalGBy_s0_exact h

theorem evalG_op4 (q n : ℕ) {subject tail value result : Noun}
    (hcall : FieldEmbedding.evalGBy q n subject tail = some value)
    (hinc : FieldEmbedding.lusGBy q value = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject (op4 tail) = some result :=
  evalGBy_s4_exact hcall hinc

theorem evalG_op5 (q n : ℕ) {subject b c rb rc : Noun}
    (hb : FieldEmbedding.evalGBy q n subject b = some rb)
    (hc : FieldEmbedding.evalGBy q n subject c = some rc) :
    FieldEmbedding.evalGBy q (n + 1) subject (op5 b c) = some (Noun.tis rb rc) :=
  evalGBy_s5_exact hb hc

theorem evalG_op6_zero (q n : ℕ) {subject b c d result : Noun}
    (hb : FieldEmbedding.evalGBy q n subject b = some (.atom 0))
    (hc : FieldEmbedding.evalGBy q n subject c = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject (op6 b c d) = some result :=
  evalGBy_s6_zero_exact hb hc

theorem evalG_op6_one (q n : ℕ) {subject b c d result : Noun}
    (hb : FieldEmbedding.evalGBy q n subject b = some (.atom 1))
    (hd : FieldEmbedding.evalGBy q n subject d = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject (op6 b c d) = some result :=
  evalGBy_s6_one_exact hb hd

theorem evalG_op7 (q n : ℕ) {subject b c sb result : Noun}
    (hb : FieldEmbedding.evalGBy q n subject b = some sb)
    (hc : FieldEmbedding.evalGBy q n sb c = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject (op7 b c) = some result :=
  evalGBy_s7_exact hb hc

theorem evalG_op9 (q n axis : ℕ) {subject c core arm result : Noun}
    (hc : FieldEmbedding.evalGBy q n subject c = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalGBy q n core arm = some result) :
    FieldEmbedding.evalGBy q (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = some result :=
  evalGBy_s9_exact hc hslot harm

theorem evalG_cons (q fuel : ℕ)
    {subject leftHead leftTail tail leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalGBy q fuel subject (.cell leftHead leftTail) =
      some leftResult)
    (hright : FieldEmbedding.evalGBy q fuel subject tail = some rightResult) :
    FieldEmbedding.evalGBy q (fuel + 1) subject
      (.cell (.cell leftHead leftTail) tail) =
      some (.cell leftResult rightResult) :=
  evalGBy_cons_exact hleft hright

theorem evalG_invokeAxis (q n axis : ℕ) {subject core arm result : Noun}
    (hslot1 : Noun.slot 1 subject = some core)
    (hslotA : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalGBy q (n + 2) core arm = some result) :
    FieldEmbedding.evalGBy q (n + 3) subject (invokeAxis axis) = some result := by
  have hcore : FieldEmbedding.evalGBy q (n + 2) subject (op0 1) = some core :=
    evalG_op0 q (n + 1) 1 hslot1
  exact evalGBy_s9_exact (fuel := n + 2) hcore hslotA harm

/-- `slam batteryF sampleF axis` against `subject`, when `batteryF` is a cell. -/
theorem evalG_slam (q fuel : ℕ)
    {subject bHead bTail sampleF battery sample arm result : Noun} {axis : ℕ}
    (hb : FieldEmbedding.evalGBy q (fuel + 3) subject (.cell bHead bTail) =
      some battery)
    (hs : FieldEmbedding.evalGBy q (fuel + 3) subject sampleF = some sample)
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : FieldEmbedding.evalGBy q (fuel + 3) (.cell battery sample) arm =
      some result) :
    FieldEmbedding.evalGBy q (fuel + 5) subject
      (slam (.cell bHead bTail) sampleF axis) = some result := by
  have hcons : FieldEmbedding.evalGBy q (fuel + 4) subject
      (.cell (.cell bHead bTail) sampleF) = some (.cell battery sample) :=
    evalG_cons q (fuel + 3) hb hs
  have hax : FieldEmbedding.evalGBy q (fuel + 4) (.cell battery sample)
      (invokeAxis axis) = some result :=
    evalG_invokeAxis (q := q) (n := fuel + 1) (axis := axis)
      (slot_1 _) hslot harm
  exact evalG_op7 q (fuel + 4) hcons hax

/-! ## Add-arm evaluation -/

theorem evalG_addArm_done (q n : ℕ) (acc m : Noun) :
    FieldEmbedding.evalGBy q (n + 6) (addCore acc m m) addArm = some acc := by
  have h14 := evalG_op0 q (n + 3) 14 (addCore_slot14 acc m m)
  have h15 := evalG_op0 q (n + 3) 15 (addCore_slot15 acc m m)
  have hcond := evalG_op5 q (n + 4) h14 h15
  have htis : Noun.tis m m = .atom 0 := tis_self m
  rw [htis] at hcond
  have hthen := evalG_op0 q (n + 4) 6 (addCore_slot6 acc m m)
  simpa [addArm] using evalG_op6_zero q (n + 5) hcond hthen

theorem evalG_addNewSample (n acc i m : ℕ) (hacc : acc + 1 < 97) (hi : i + 1 < 97) :
    FieldEmbedding.evalGBy 97 (n + 5) (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) := by
  have h6 := evalG_op0 97 (n + 2) 6 (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := evalG_op0 97 (n + 1) 14 (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := evalG_op0 97 (n + 2) 15 (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := evalG_op4 97 (n + 3) h6 (lusG_succ hacc)
  have hincI := evalG_op4 97 (n + 2) h14 (lusG_succ hi)
  have hinner := evalG_cons 97 (n + 3) hincI h15
  exact evalG_cons 97 (n + 4) hincA hinner

/-- One increment: `i = 0`, `m = 1`. -/
theorem evalG_addArm_one (n acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalGBy 97 (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      some (.atom (acc + 1)) := by
  have h14 := evalG_op0 97 (n + 13) 14
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := evalG_op0 97 (n + 13) 15
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := evalG_op5 97 (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalG_addNewSample (n + 8) acc 0 1 hacc (by decide)
  have hbatt := evalG_op0 97 (n + 12) 2
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  have hdone := evalG_addArm_done 97 (n + 7) (.atom (acc + 1)) (.atom 1)
  have hslam := evalG_slam (q := 97) (fuel := n + 10)
    (subject := addCore (.atom acc) (.atom 0) (.atom 1))
    (bHead := .atom 0) (bTail := .atom 2) (sampleF := addNewSample)
    (battery := addArm)
    (sample := .cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1)))
    (axis := 2) (arm := addArm) (result := .atom (acc + 1))
    hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1))
    hdone
  simpa [addArm, slam, op0] using evalG_op6_one 97 (n + 15) hcond hslam

theorem add_1_1_evalG :
    FieldEmbedding.evalGBy 97 32 (.atom 0) (addCall (.atom 1) (.atom 1))
      = some (.atom 2) := by
  have hqB := evalG_quote 97 29 (.atom 0) addArm
  have hqS := evalG_quote 97 29 (.atom 0) (addSample (.atom 1) (.atom 1))
  have hslot : Noun.slot 2
      (.cell addArm (addSample (.atom 1) (.atom 1))) = some addArm :=
    addCore_slot2 (.atom 1) (.atom 0) (.atom 1)
  have hdone := evalG_addArm_one 14 1 (by decide)
  have hslam := evalG_slam (q := 97) (fuel := 27)
    hqB hqS hslot hdone
  simpa [addCall, slam, quote] using hslam

/-! ## MAC-arm evaluation -/

theorem evalG_macArm_done (q fuel : ℕ) (acc n m : Noun) :
    FieldEmbedding.evalGBy q (fuel + 6) (macCoreAt acc n n m) macArm = some acc := by
  have h14 := evalG_op0 q (fuel + 3) 14 (macCoreAt_slot14 acc n n m)
  have h30 := evalG_op0 q (fuel + 3) 30 (macCoreAt_slot30 acc n n m)
  have hcond := evalG_op5 q (fuel + 4) h14 h30
  rw [tis_self n] at hcond
  have hthen := evalG_op0 q (fuel + 4) 6 (macCoreAt_slot6 acc n n m)
  simpa [macArm] using evalG_op6_zero q (fuel + 5) hcond hthen

theorem evalG_macArm_zero (q fuel : ℕ) (acc m : Noun) :
    FieldEmbedding.evalGBy q (fuel + 6) (macCore acc (.atom 0) m) macArm = some acc :=
  evalG_macArm_done q fuel acc (.atom 0) m

/-- Sample formula `[accF [0 [nF mF]]]` with cell-headed `accF`/`nF`. -/
theorem evalG_macSampleF (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m : Noun}
    (ha : FieldEmbedding.evalGBy q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : FieldEmbedding.evalGBy q fuel subject (.cell nH nT) = some n)
    (hm : FieldEmbedding.evalGBy q fuel subject mF = some m) :
    FieldEmbedding.evalGBy q (fuel + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      some (.cell acc (.cell (.atom 0) (.cell n m))) := by
  have hnm := evalG_cons q fuel hn hm
  have hz := evalG_op1 q fuel subject 0
  have hinner := evalG_cons q (fuel + 1) hz hnm
  exact evalG_cons q (fuel + 2) ha hinner

theorem evalG_invokeMac (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m result : Noun}
    (ha : FieldEmbedding.evalGBy q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : FieldEmbedding.evalGBy q fuel subject (.cell nH nT) = some n)
    (hm : FieldEmbedding.evalGBy q fuel subject mF = some m)
    (harm : FieldEmbedding.evalGBy q (fuel + 3) (macCore acc n m) macArm =
      some result) :
    FieldEmbedding.evalGBy q (fuel + 5) subject
      (invokeMac (.cell aH aT) (.cell nH nT) mF) = some result := by
  have hqB := evalG_quote q (fuel + 2) subject mmBattery
  have hsf := evalG_macSampleF q fuel ha hn hm
  have hslot := macCoreAt_slot4 acc (.atom 0) n m
  simpa [invokeMac, slam, quote, macCore, macCoreAt, macSample] using
    evalG_slam (q := q) (fuel := fuel)
      (bHead := .atom 1) (bTail := mmBattery)
      hqB hsf hslot harm

theorem mac_0_m_evalG (m : ℕ) :
    FieldEmbedding.evalGBy 97 16 (.atom 0)
        (invokeMac (op1 0) (op1 0) (op1 m))
      = some (.atom 0) := by
  have ha := evalG_op1 97 13 (.atom 0) 0
  have hn := evalG_op1 97 10 (.atom 0) 0
  have hm := evalG_op1 97 10 (.atom 0) m
  have harm := evalG_macArm_zero 97 8 (.atom 0) (.atom m)
  have h := evalG_invokeMac (q := 97) (fuel := 11)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 1) (nT := .atom 0)
    (mF := op1 m) ha hn hm
    (evalGBy_mono (q := 97) (show 8 + 6 ≤ 11 + 3 by omega) harm)
  simpa [op1] using
    evalGBy_mono (q := 97) (show 11 + 5 ≤ 16 by omega) h

/-- Inner add slammed from a MAC core: `m = 0` so `add` is immediately done. -/
theorem evalG_addFromMac_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = some (.atom acc) := by
  have h5 := evalG_op0 97 (fuel + 9) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := evalG_op0 97 (fuel + 8) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := evalG_op1 97 (fuel + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := evalG_op0 97 (fuel + 7) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := evalG_cons 97 (fuel + 8) hz hm
  have hsmpl := evalG_cons 97 (fuel + 9) hacc hinner
  have hadd := evalG_addArm_done 97 (fuel + 4) (.atom acc) (.atom 0)
  simpa [addFromMac, slam, op0, op1, macCore] using
    evalG_slam (q := 97) (fuel := fuel + 7)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 0))
      hadd

/-- Inner add slammed from a MAC core: `m = 1` so `add` takes one increment. -/
theorem evalG_addFromMac_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalGBy 97 (fuel + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      some (.atom (acc + 1)) := by
  have h5 := evalG_op0 97 (fuel + 18) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := evalG_op0 97 (fuel + 17) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := evalG_op1 97 (fuel + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := evalG_op0 97 (fuel + 16) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := evalG_cons 97 (fuel + 17) hz hm
  have hsmpl := evalG_cons 97 (fuel + 18) haccS hinner
  have hadd := evalG_addArm_one (fuel + 3) acc hacc
  simpa [addFromMac, slam, op0, op1, macCore] using
    evalG_slam (q := 97) (fuel := fuel + 16)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
      hadd

/-- `macNewSample` after one MAC trip with `m = 0`. -/
theorem evalG_macNewSample_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      some (.cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) := by
  have hadd := evalG_addFromMac_m0 fuel acc
  have h14 := evalG_op0 97 (fuel + 10) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := evalG_op4 97 (fuel + 11) h14 (lusG_succ (n := 0) (by decide))
  have hn := evalG_op0 97 (fuel + 10) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := evalG_op0 97 (fuel + 10) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := evalG_cons 97 (fuel + 11) hn hm
  have hrest := evalG_cons 97 (fuel + 12) hinc hnm
  exact evalG_cons 97 (fuel + 13)
    (evalGBy_mono (q := 97) (show fuel + 12 ≤ fuel + 13 by omega) hadd) hrest

theorem evalG_macArm_one_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = some (.atom acc) := by
  have h14 := evalG_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := evalG_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := evalG_op5 97 (fuel + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalG_macNewSample_m0 (fuel + 4) acc
  have hbatt := evalG_op0 97 (fuel + 18) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hdone := evalG_macArm_done 97 (fuel + 13) (.atom acc) (.atom 1) (.atom 0)
  have hslam := evalG_slam (q := 97) (fuel := fuel + 16)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalGBy_mono (q := 97) (show fuel + 4 + 14 ≤ fuel + 16 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0))
    (evalGBy_mono (q := 97) (show fuel + 13 + 6 ≤ fuel + 16 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    evalG_op6_one 97 (fuel + 21) hcond hslam

/-- `macNewSample` after one MAC trip with `m = 1`. -/
theorem evalG_macNewSample_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalGBy 97 (fuel + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) := by
  have hadd := evalG_addFromMac_m1 fuel acc hacc
  have h14 := evalG_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := evalG_op4 97 (fuel + 20) h14 (lusG_succ (n := 0) (by decide))
  have hn := evalG_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := evalG_op0 97 (fuel + 19) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := evalG_cons 97 (fuel + 20) hn hm
  have hrest := evalG_cons 97 (fuel + 21) hinc hnm
  exact evalG_cons 97 (fuel + 22)
    (evalGBy_mono (q := 97) (show fuel + 21 ≤ fuel + 22 by omega) hadd) hrest

theorem evalG_macArm_one_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalGBy 97 (fuel + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      some (.atom (acc + 1)) := by
  have h14 := evalG_op0 97 (fuel + 28) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := evalG_op0 97 (fuel + 28) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := evalG_op5 97 (fuel + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalG_macNewSample_m1 (fuel + 4) acc hacc
  have hbatt := evalG_op0 97 (fuel + 27) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hdone := evalG_macArm_done 97 (fuel + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have hslam := evalG_slam (q := 97) (fuel := fuel + 25)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalGBy_mono (q := 97) (show fuel + 4 + 23 ≤ fuel + 25 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1))
    (evalGBy_mono (q := 97) (show fuel + 22 + 6 ≤ fuel + 25 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    evalG_op6_one 97 (fuel + 30) hcond hslam

theorem mac_1_1_evalG :
    FieldEmbedding.evalGBy 97 48 (.atom 0)
        (invokeMac (op1 0) (op1 1) (op1 1))
      = some (.atom 1) := by
  have ha := evalG_op1 97 44 (.atom 0) 0
  have hn := evalG_op1 97 42 (.atom 0) 1
  have hm := evalG_op1 97 42 (.atom 0) 1
  have harm := evalG_macArm_one_m1 11 0 (by decide)
  have h := evalG_invokeMac (q := 97) (fuel := 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 1) (nT := .atom 1)
    (mF := op1 1) ha hn hm
    (evalGBy_mono (q := 97) (show 11 + 31 ≤ 43 + 3 by omega) harm)
  simpa [op1] using
    evalGBy_mono (q := 97) (show 43 + 5 ≤ 48 by omega) h

/-! ## 2×2 evaluation -/

/-- `c00 = 1·1 + 1·1 = 2`. -/
theorem evalG_mmC00 (fuel : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 56) mmSubject mmC00 = some (.atom 2) := by
  have ha0 := evalG_op1 97 (fuel + 44) mmSubject 0
  have a00 := evalG_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b00 := evalG_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := evalG_macArm_one_m1 (fuel + 11) 0 (by decide)
  have hinner := evalG_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00
    (evalGBy_mono (q := 97) (show fuel + 11 + 31 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := evalG_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b10 := evalG_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := evalG_macArm_one_m1 (fuel + 16) 1 (by decide)
  have houter := evalG_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b10
    (evalGBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c01 = 1·0 + 1·1 = 1`. -/
theorem evalG_mmC01 (fuel : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 56) mmSubject mmC01 = some (.atom 1) := by
  have ha0 := evalG_op1 97 (fuel + 44) mmSubject 0
  have a00 := evalG_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b01 := evalG_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := evalG_macArm_one_m0 (fuel + 20) 0
  have hinner := evalG_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01
    (evalGBy_mono (q := 97) (show fuel + 20 + 22 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := evalG_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b11 := evalG_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := evalG_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalG_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b11
    (evalGBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c10 = 0·1 + 1·1 = 1`. -/
theorem evalG_mmC10 (fuel : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 56) mmSubject mmC10 = some (.atom 1) := by
  have ha0 := evalG_op1 97 (fuel + 44) mmSubject 0
  have a10 := evalG_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b00 := evalG_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := evalG_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 1)
  have hinner := evalG_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00
    (evalGBy_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := evalG_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b10 := evalG_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := evalG_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalG_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b10
    (evalGBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c11 = 0·0 + 1·1 = 1`. -/
theorem evalG_mmC11 (fuel : ℕ) :
    FieldEmbedding.evalGBy 97 (fuel + 56) mmSubject mmC11 = some (.atom 1) := by
  have ha0 := evalG_op1 97 (fuel + 44) mmSubject 0
  have a10 := evalG_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b01 := evalG_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := evalG_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 0)
  have hinner := evalG_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01
    (evalGBy_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := evalG_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b11 := evalG_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := evalG_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalG_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b11
    (evalGBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

theorem mm_evalG :
    FieldEmbedding.evalGBy 97 64 mmSubject mmFormula = some mmC := by
  have h00 := evalG_mmC00 6
  have h01 := evalG_mmC01 6
  have h10 := evalG_mmC10 6
  have h11 := evalG_mmC11 6
  have hL := evalG_cons 97 62
    (evalGBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h00)
    (evalGBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h01)
  have hR := evalG_cons 97 62
    (evalGBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h10)
    (evalGBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h11)
  rw [mmFormula, mmC]
  exact evalG_cons 97 63 hL hR

theorem mm_evalN {K : Type} [Field K] :
    Nock.evalN 64 mmSubject mmFormula = some mmC :=
  genComputeSkeleton_evalN (mmTree_gen (K := K))

theorem mm_evalG_65537 :
    FieldEmbedding.evalGBy 65537 64 mmSubject mmFormula = some mmC :=
  evalGBy_mod_le (q := 97) (q' := 65537) (by omega) 64 mmSubject mmFormula mmC mm_evalG

theorem atom_boundedBy {q a : ℕ} (h : a < q) :
    FieldEmbedding.BoundedBy q (.atom a) := by
  simp [FieldEmbedding.BoundedBy, h]

theorem op0_bounded {q ax : ℕ} (h0 : 0 < q) (hax : ax < q) :
    FieldEmbedding.BoundedBy q (op0 ax) :=
  cell_boundedBy (atom_boundedBy h0) (atom_boundedBy hax)

theorem op1_bounded {q k : ℕ} (h1 : 1 < q) (hk : k < q) :
    FieldEmbedding.BoundedBy q (op1 k) :=
  cell_boundedBy (atom_boundedBy h1) (atom_boundedBy hk)

theorem op4_bounded {q : ℕ} {b : Noun} (h4 : 4 < q)
    (hb : FieldEmbedding.BoundedBy q b) :
    FieldEmbedding.BoundedBy q (op4 b) :=
  cell_boundedBy (atom_boundedBy h4) hb

theorem op5_bounded {q : ℕ} {b c : Noun} (h5 : 5 < q)
    (hb : FieldEmbedding.BoundedBy q b) (hc : FieldEmbedding.BoundedBy q c) :
    FieldEmbedding.BoundedBy q (op5 b c) :=
  cell_boundedBy (atom_boundedBy h5) (cell_boundedBy hb hc)

theorem op6_bounded {q : ℕ} {b c d : Noun} (h6 : 6 < q)
    (hb : FieldEmbedding.BoundedBy q b) (hc : FieldEmbedding.BoundedBy q c)
    (hd : FieldEmbedding.BoundedBy q d) :
    FieldEmbedding.BoundedBy q (op6 b c d) :=
  cell_boundedBy (atom_boundedBy h6)
    (cell_boundedBy hb (cell_boundedBy hc hd))

theorem op7_bounded {q : ℕ} {b c : Noun} (h7 : 7 < q)
    (hb : FieldEmbedding.BoundedBy q b) (hc : FieldEmbedding.BoundedBy q c) :
    FieldEmbedding.BoundedBy q (op7 b c) :=
  cell_boundedBy (atom_boundedBy h7) (cell_boundedBy hb hc)

theorem invokeAxis_bounded {q ax : ℕ} (h9 : 9 < q) (h0 : 0 < q)
    (h1 : 1 < q) (hax : ax < q) :
    FieldEmbedding.BoundedBy q (invokeAxis ax) :=
  cell_boundedBy (atom_boundedBy h9)
    (cell_boundedBy (atom_boundedBy hax)
      (cell_boundedBy (atom_boundedBy h0) (atom_boundedBy h1)))

theorem quote_bounded {q : ℕ} {n : Noun} (h1 : 1 < q)
    (hn : FieldEmbedding.BoundedBy q n) :
    FieldEmbedding.BoundedBy q (quote n) :=
  cell_boundedBy (atom_boundedBy h1) hn

theorem slam_bounded {q : ℕ} {batteryF sampleF : Noun} {axis : ℕ}
    (h7 : 7 < q) (h9 : 9 < q) (h0 : 0 < q) (h1 : 1 < q) (hax : axis < q)
    (hb : FieldEmbedding.BoundedBy q batteryF)
    (hs : FieldEmbedding.BoundedBy q sampleF) :
    FieldEmbedding.BoundedBy q (slam batteryF sampleF axis) :=
  op7_bounded h7 (cell_boundedBy hb hs) (invokeAxis_bounded h9 h0 h1 hax)

private theorem q32 : 32 < (65537 : ℕ) := by omega
private theorem q32_ops : 0 < 32 ∧ 1 < 32 ∧ 4 < 32 ∧ 5 < 32 ∧ 6 < 32 ∧
    7 < 32 ∧ 9 < 32 := by omega

theorem mmSubject_bounded32 : FieldEmbedding.BoundedBy 32 mmSubject := by
  simp [mmSubject, mmA, mmB, FieldEmbedding.BoundedBy]

theorem addNewSample_bounded32 : FieldEmbedding.BoundedBy 32 addNewSample :=
  cell_boundedBy
    (op4_bounded (by omega) (op0_bounded (by omega) (by omega)))
    (cell_boundedBy
      (op4_bounded (by omega) (op0_bounded (by omega) (by omega)))
      (op0_bounded (by omega) (by omega)))

theorem addArm_bounded32 : FieldEmbedding.BoundedBy 32 addArm :=
  op6_bounded (by omega)
    (op5_bounded (by omega) (op0_bounded (by omega) (by omega))
      (op0_bounded (by omega) (by omega)))
    (op0_bounded (by omega) (by omega))
    (slam_bounded (by omega) (by omega) (by omega) (by omega) (by omega)
      (op0_bounded (by omega) (by omega)) addNewSample_bounded32)

theorem addFromMac_bounded32 : FieldEmbedding.BoundedBy 32 addFromMac :=
  slam_bounded (by omega) (by omega) (by omega) (by omega) (by omega)
    (op0_bounded (by omega) (by omega))
    (cell_boundedBy (op0_bounded (by omega) (by omega))
      (cell_boundedBy (op1_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega))))

theorem macNewSample_bounded32 : FieldEmbedding.BoundedBy 32 macNewSample :=
  cell_boundedBy addFromMac_bounded32
    (cell_boundedBy
      (op4_bounded (by omega) (op0_bounded (by omega) (by omega)))
      (cell_boundedBy (op0_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega))))

theorem macArm_bounded32 : FieldEmbedding.BoundedBy 32 macArm :=
  op6_bounded (by omega)
    (op5_bounded (by omega) (op0_bounded (by omega) (by omega))
      (op0_bounded (by omega) (by omega)))
    (op0_bounded (by omega) (by omega))
    (slam_bounded (by omega) (by omega) (by omega) (by omega) (by omega)
      (op0_bounded (by omega) (by omega)) macNewSample_bounded32)

theorem mmBattery_bounded32 : FieldEmbedding.BoundedBy 32 mmBattery :=
  cell_boundedBy macArm_bounded32 addArm_bounded32

theorem invokeMac_bounded32 {accF nF mF : Noun}
    (ha : FieldEmbedding.BoundedBy 32 accF)
    (hn : FieldEmbedding.BoundedBy 32 nF)
    (hm : FieldEmbedding.BoundedBy 32 mF) :
    FieldEmbedding.BoundedBy 32 (invokeMac accF nF mF) :=
  slam_bounded (by omega) (by omega) (by omega) (by omega) (by omega)
    (quote_bounded (by omega) mmBattery_bounded32)
    (cell_boundedBy ha (cell_boundedBy (op1_bounded (by omega) (by omega))
      (cell_boundedBy hn hm)))

theorem mac2_bounded32 {accF nF mF nF' mF' : Noun}
    (ha : FieldEmbedding.BoundedBy 32 accF)
    (hn : FieldEmbedding.BoundedBy 32 nF)
    (hm : FieldEmbedding.BoundedBy 32 mF)
    (hn' : FieldEmbedding.BoundedBy 32 nF')
    (hm' : FieldEmbedding.BoundedBy 32 mF') :
    FieldEmbedding.BoundedBy 32 (mac2 accF nF mF nF' mF') :=
  invokeMac_bounded32 (invokeMac_bounded32 ha hn hm) hn' hm'

theorem mmFormula_bounded32 : FieldEmbedding.BoundedBy 32 mmFormula :=
  cell_boundedBy
    (cell_boundedBy
      (mac2_bounded32 (op1_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega)))
      (mac2_bounded32 (op1_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))))
    (cell_boundedBy
      (mac2_bounded32 (op1_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega)))
      (mac2_bounded32 (op1_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))
        (op0_bounded (by omega) (by omega)) (op0_bounded (by omega) (by omega))))

theorem mmSubject_bounded : FieldEmbedding.BoundedBy 65537 mmSubject :=
  BoundedBy_mono (by omega) mmSubject_bounded32

theorem mmFormula_bounded : FieldEmbedding.BoundedBy 65537 mmFormula :=
  BoundedBy_mono (by omega) mmFormula_bounded32

/-! ## Generated compute-tree `InTree` bounds -/

def computeNodeBounded (q : ℕ) (u : NTree (GenComputeRow K)) : Prop :=
  u.label.skel.BoundedBy q ∧
    ∀ r ∈ u.label.requests,
      FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child

theorem genComputeSkeleton_inTree_bounded
    {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u, InTree t u → computeNodeBounded q u := by
  induction fuel generalizing subject formula t result with
  | zero =>
    simp [FieldEmbedding.evalGBy] at hG
  | succ n ih =>
    have hRes : FieldEmbedding.BoundedBy q result :=
      (FieldEmbedding.agreeBy q hq (n + 1) subject formula result hs hf hG).2.2
    cases formula with
    | atom _ =>
      simp [FieldEmbedding.evalGBy] at hG
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        obtain ⟨hfL, hfR⟩ := FieldEmbedding.BoundedBy_cell.mp hf
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [FieldEmbedding.evalGBy] at hG
            cases hGL : FieldEmbedding.evalGBy q n subject (.cell lh lt) with
            | none => rw [hGL] at hG; simp at hG
            | some lG =>
              cases hGR : FieldEmbedding.evalGBy q n subject tl with
              | none => rw [hGL, hGR] at hG; simp at hG
              | some rG =>
                rw [hGL, hGR] at hG
                obtain ⟨rfl, rfl⟩ := Noun.cell.inj (Option.some.inj hG)
                have hBL := (FieldEmbedding.agreeBy q hq n subject (.cell lh lt)
                  pL.2 hs hfL hGL).2.2
                have hBR := (FieldEmbedding.agreeBy q hq n subject tl
                  pR.2 hs hfR hGR).2.2
                intro u hu
                cases hu with
                | here =>
                  simp only [computeNodeBounded, skelNode]
                  refine ⟨genSkelCons_bounded hs hfL hfR hBL hBR, ?_⟩
                  intro r hr
                  simp [List.mem_singleton, List.mem_cons, List.not_mem_nil] at hr; subst r
                  exact ⟨hf, hfR⟩
                | sub hch hu =>
                  simp [NTree.children_node, List.mem_cons, List.not_mem_nil,
                    List.mem_singleton] at hch
                  rcases hch with rfl | rfl
                  · exact ih hs hfL hGL hL u hu
                  · exact ih hs hfR hGR hR u hu
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP0
          cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              intro u hu
              cases hu with
              | here =>
                simp only [computeNodeBounded, skelNode]
                obtain ⟨hh, ht⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                refine ⟨genSkelOp0_bounded hs hf hh ht hRes, ?_⟩
                intro r hr
                simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                rcases hr with rfl | rfl
                · exact ⟨hf, ht⟩
                · exact ⟨hs, FieldEmbedding.slot_boundedBy q ax subject hs hslot⟩
              | sub hch _ =>
                simp [NTree.children_node] at hch
        · -- OP1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          intro u hu
          cases hu with
          | here =>
            simp only [computeNodeBounded, skelNode]
            obtain ⟨_, ht⟩ := FieldEmbedding.BoundedBy_cell.mp hf
            refine ⟨genSkelOp1_bounded hs hf hRes (atom1_boundedBy hq), ?_⟩
            intro r hr
            simp [List.mem_singleton, List.mem_cons, List.not_mem_nil] at hr; subst r
            exact ⟨hf, ht⟩
          | sub hch _ =>
            simp [NTree.children_node] at hch
        · -- OP2
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hb, hc⟩ := (FieldEmbedding.BoundedBy_cell.mp
              (FieldEmbedding.BoundedBy_cell.mp hf).2)
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp only [FieldEmbedding.evalGBy] at hG
                  cases hGB : FieldEmbedding.evalGBy q n subject b with
                  | none => rw [hGB] at hG; simp at hG
                  | some sbG =>
                    cases hGC : FieldEmbedding.evalGBy q n subject c with
                    | none => rw [hGB, hGC] at hG; simp at hG
                    | some scG =>
                      rw [hGB, hGC] at hG
                      have hBeq := evalGBy_result_of_gen hq hs hb hGB hB
                      have hCeq := evalGBy_result_of_gen hq hs hc hGC hC
                      cases hBeq; cases hCeq
                      have hBB := (FieldEmbedding.agreeBy q hq n subject b
                        pB.2 hs hb hGB).2.2
                      have hBC := (FieldEmbedding.agreeBy q hq n subject c
                        pC.2 hs hc hGC).2.2
                      have hMeq := evalGBy_result_of_gen hq hBB hBC hG hM
                      cases hMeq
                      intro u hu
                      cases hu with
                      | here =>
                        simp only [computeNodeBounded, skelNode]
                        obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                        refine ⟨genSkelOp2_bounded hs hf hh hft hb hc hBB hBC hRes, ?_⟩
                        intro r hr
                        simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                        rcases hr with rfl | rfl
                        · exact ⟨hf, hft⟩
                        · exact ⟨hft, hb⟩
                      | sub hch hu =>
                        simp [NTree.children_node, List.mem_cons,
                          List.not_mem_nil, List.mem_singleton] at hch
                        rcases hch with rfl | rfl | rfl
                        · exact ih hs hb hGB hB u hu
                        · exact ih hs hc hGC hC u hu
                        · exact ih hBB hBC hG hM u hu
        · -- OP3
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨_, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
            simp only [FieldEmbedding.evalGBy] at hG
            cases hGc : FieldEmbedding.evalGBy q n subject tl with
            | none => rw [hGc] at hG; simp at hG
            | some v =>
              rw [hGc] at hG
              have heq := evalGBy_result_of_gen hq hs hft hGc hcall
              cases heq
              have hBv := (FieldEmbedding.agreeBy q hq n subject tl p.2
                hs hft hGc).2.2
              intro u hu
              cases hu with
              | here =>
                simp only [computeNodeBounded, skelNode]
                obtain ⟨hh, _⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                refine ⟨genSkelOp3_bounded hs hf hh hft hs hft hBv hRes, ?_⟩
                intro r hr
                simp [List.mem_singleton, List.mem_cons, List.not_mem_nil] at hr; subst r
                exact ⟨hf, hft⟩
              | sub hch hu =>
                simp [NTree.children_node, List.mem_cons, List.not_mem_nil] at hch
                subst hch
                exact ih hs hft hGc hcall u hu
        · -- OP4
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some lusR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨_, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
              simp only [FieldEmbedding.evalGBy] at hG
              cases hGc : FieldEmbedding.evalGBy q n subject tl with
              | none => rw [hGc] at hG; simp at hG
              | some v =>
                rw [hGc] at hG
                have heq := evalGBy_result_of_gen hq hs hft hGc hcall
                cases heq
                have hBv := (FieldEmbedding.agreeBy q hq n subject tl p.2
                  hs hft hGc).2.2
                intro u hu
                cases hu with
                | here =>
                  simp only [computeNodeBounded, skelNode]
                  obtain ⟨hh, _⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                  refine ⟨genSkelOp4_bounded hs hf hh hft hs hft hBv hRes, ?_⟩
                  intro r hr
                  simp [List.mem_singleton, List.mem_cons, List.not_mem_nil] at hr; subst r
                  exact ⟨hf, hft⟩
                | sub hch hu =>
                  simp [NTree.children_node, List.mem_cons, List.not_mem_nil] at hch
                  subst hch
                  exact ih hs hft hGc hcall u hu
        · -- OP5
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hb, hc⟩ := (FieldEmbedding.BoundedBy_cell.mp
              (FieldEmbedding.BoundedBy_cell.mp hf).2)
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [FieldEmbedding.evalGBy] at hG
                cases hGB : FieldEmbedding.evalGBy q n subject b with
                | none => rw [hGB] at hG; simp at hG
                | some sbG =>
                  cases hGC : FieldEmbedding.evalGBy q n subject c with
                  | none => rw [hGB, hGC] at hG; simp at hG
                  | some scG =>
                    rw [hGB, hGC] at hG
                    have hBeq := evalGBy_result_of_gen hq hs hb hGB hB
                    have hCeq := evalGBy_result_of_gen hq hs hc hGC hC
                    cases hBeq; cases hCeq
                    have hBB := (FieldEmbedding.agreeBy q hq n subject b
                      pB.2 hs hb hGB).2.2
                    have hBC := (FieldEmbedding.agreeBy q hq n subject c
                      pC.2 hs hc hGC).2.2
                    intro u hu
                    cases hu with
                    | here =>
                      simp only [computeNodeBounded, skelNode]
                      obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                      refine ⟨genSkelOp5_bounded hs hf hh hft hb hc hBB hBC hRes, ?_⟩
                      intro r hr
                      simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                      rcases hr with rfl | rfl
                      · exact ⟨hf, hft⟩
                      · exact ⟨hft, hb⟩
                    | sub hch hu =>
                      simp [NTree.children_node, List.mem_cons,
                        List.not_mem_nil, List.mem_singleton] at hch
                      rcases hch with rfl | rfl
                      · exact ih hs hb hGB hB u hu
                      · exact ih hs hc hGC hC u hu
        · -- OP6
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              obtain ⟨hb, hrest⟩ := (FieldEmbedding.BoundedBy_cell.mp
                (FieldEmbedding.BoundedBy_cell.mp hf).2)
              obtain ⟨hc, hd⟩ := FieldEmbedding.BoundedBy_cell.mp hrest
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [FieldEmbedding.evalGBy] at hG
                      cases hGcond : FieldEmbedding.evalGBy q n subject b with
                      | none => rw [hGcond] at hG; simp at hG
                      | some vb =>
                        rw [hGcond] at hG
                        have hCeq := evalGBy_result_of_gen hq hs hb hGcond hcond
                        cases hCeq
                        simp [hval] at hG
                        have hBc := (FieldEmbedding.agreeBy q hq n subject b
                          pCond.2 hs hb hGcond).2.2
                        have hGteq := evalGBy_result_of_gen hq hs hc hG htaken
                        cases hGteq
                        intro u hu
                        cases hu with
                        | here =>
                          simp only [computeNodeBounded, skelNode]
                          obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                          have hBt := (FieldEmbedding.agreeBy q hq n subject c
                            pTaken.2 hs hc hG).2.2
                          refine ⟨genSkelOp6_bounded hs hf hh hft hb hrest hc hd
                            (by simpa [hval] using hBc) hc hRes, ?_⟩
                          intro r hr
                          simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                          rcases hr with rfl | rfl | rfl
                          · exact ⟨hf, hft⟩
                          · exact ⟨hft, hb⟩
                          · exact ⟨hrest, hc⟩
                        | sub hch hu =>
                          simp [NTree.children_node, List.mem_cons,
                            List.not_mem_nil, List.mem_singleton] at hch
                          rcases hch with rfl | rfl
                          · exact ih hs hb hGcond hcond u hu
                          · exact ih hs hc hG htaken u hu
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp only [FieldEmbedding.evalGBy] at hG
                        cases hGcond : FieldEmbedding.evalGBy q n subject b with
                        | none => rw [hGcond] at hG; simp at hG
                        | some vb =>
                          rw [hGcond] at hG
                          have hCeq := evalGBy_result_of_gen hq hs hb hGcond hcond
                          cases hCeq
                          simp [hval] at hG
                          have hBc := (FieldEmbedding.agreeBy q hq n subject b
                            pCond.2 hs hb hGcond).2.2
                          have hGteq := evalGBy_result_of_gen hq hs hd hG htaken
                          cases hGteq
                          intro u hu
                          cases hu with
                          | here =>
                            simp only [computeNodeBounded, skelNode]
                            obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                            have hBt := (FieldEmbedding.agreeBy q hq n subject d
                              pTaken.2 hs hd hG).2.2
                            refine ⟨genSkelOp6_bounded hs hf hh hft hb hrest hc hd
                              (by simpa [hval] using hBc) hd hRes, ?_⟩
                            intro r hr
                            simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                            rcases hr with rfl | rfl | rfl
                            · exact ⟨hf, hft⟩
                            · exact ⟨hft, hb⟩
                            · exact ⟨hrest, hc⟩
                          | sub hch hu =>
                            simp [NTree.children_node, List.mem_cons,
                              List.not_mem_nil, List.mem_singleton] at hch
                            rcases hch with rfl | rfl
                            · exact ih hs hb hGcond hcond u hu
                            · exact ih hs hd hG htaken u hu
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · -- OP7
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hb, hc⟩ := (FieldEmbedding.BoundedBy_cell.mp
              (FieldEmbedding.BoundedBy_cell.mp hf).2)
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [FieldEmbedding.evalGBy] at hG
                cases hGB : FieldEmbedding.evalGBy q n subject b with
                | none => rw [hGB] at hG; simp at hG
                | some sbG =>
                  rw [hGB] at hG
                  have hBeq := evalGBy_result_of_gen hq hs hb hGB hB
                  cases hBeq
                  have hBB := (FieldEmbedding.agreeBy q hq n subject b
                    pB.2 hs hb hGB).2.2
                  have hCeq := evalGBy_result_of_gen hq hBB hc hG hC
                  cases hCeq
                  intro u hu
                  cases hu with
                  | here =>
                    simp only [computeNodeBounded, skelNode]
                    obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                    refine ⟨genSkelOp7_bounded hs hf hh hft hb hc hBB hRes, ?_⟩
                    intro r hr
                    simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                    rcases hr with rfl | rfl
                    · exact ⟨hf, hft⟩
                    · exact ⟨hft, hb⟩
                  | sub hch hu =>
                    simp [NTree.children_node, List.mem_cons,
                      List.not_mem_nil, List.mem_singleton] at hch
                    rcases hch with rfl | rfl
                    · exact ih hs hb hGB hB u hu
                    · exact ih hBB hc hG hC u hu
        · -- OP8
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hb, hc⟩ := (FieldEmbedding.BoundedBy_cell.mp
              (FieldEmbedding.BoundedBy_cell.mp hf).2)
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [FieldEmbedding.evalGBy] at hG
                cases hGB : FieldEmbedding.evalGBy q n subject b with
                | none => rw [hGB] at hG; simp at hG
                | some sbG =>
                  rw [hGB] at hG
                  have hBeq := evalGBy_result_of_gen hq hs hb hGB hB
                  cases hBeq
                  have hBB := (FieldEmbedding.agreeBy q hq n subject b
                    pB.2 hs hb hGB).2.2
                  have hsub : FieldEmbedding.BoundedBy q (.cell pB.2 subject) :=
                    cell_boundedBy hBB hs
                  have hCeq := evalGBy_result_of_gen hq hsub hc hG hC
                  cases hCeq
                  intro u hu
                  cases hu with
                  | here =>
                    simp only [computeNodeBounded, skelNode]
                    obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                    refine ⟨genSkelOp8_bounded hs hf hh hft hb hc hBB hRes, ?_⟩
                    intro r hr
                    simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                    rcases hr with rfl | rfl
                    · exact ⟨hf, hft⟩
                    · exact ⟨hft, hb⟩
                  | sub hch hu =>
                    simp [NTree.children_node, List.mem_cons,
                      List.not_mem_nil, List.mem_singleton] at hch
                    rcases hch with rfl | rfl
                    · exact ih hs hb hGB hB u hu
                    · exact ih hsub hc hG hC u hu
        · -- OP9
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              obtain ⟨hax, hc⟩ := (FieldEmbedding.BoundedBy_cell.mp
                (FieldEmbedding.BoundedBy_cell.mp hf).2)
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    simp only [FieldEmbedding.evalGBy] at hG
                    cases hGc : FieldEmbedding.evalGBy q n subject c with
                    | none => rw [hGc] at hG; simp at hG
                    | some coreG =>
                      rw [hGc] at hG
                      have hCeq := evalGBy_result_of_gen hq hs hc hGc hcore
                      cases hCeq
                      have hBcore := (FieldEmbedding.agreeBy q hq n subject c
                        pCore.2 hs hc hGc).2.2
                      simp [hslot] at hG
                      have harmB := FieldEmbedding.slot_boundedBy q ax pCore.2
                        hBcore hslot
                      have hIeq := evalGBy_result_of_gen hq hBcore harmB hG hinv
                      cases hIeq
                      intro u hu
                      cases hu with
                      | here =>
                        simp only [computeNodeBounded, skelNode]
                        obtain ⟨hh, hft⟩ := FieldEmbedding.BoundedBy_cell.mp hf
                        refine ⟨genSkelOp9_bounded hs hf hh hft
                          (atom_boundedBy (by simpa [FieldEmbedding.BoundedBy]
                            using hax)) hc hBcore harmB hRes, ?_⟩
                        intro r hr
                        simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
                        rcases hr with rfl | rfl | rfl
                        · exact ⟨hf, hft⟩
                        · exact ⟨hft, atom_boundedBy (by
                            simpa [FieldEmbedding.BoundedBy] using hax)⟩
                        · exact ⟨hBcore, harmB⟩
                      | sub hch hu =>
                        simp [NTree.children_node, List.mem_cons,
                          List.not_mem_nil, List.mem_singleton] at hch
                        rcases hch with rfl | rfl
                        · exact ih hs hc hGc hcore u hu
                        · exact ih hBcore harmB hG hinv u hu
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

theorem mmTree_inTree_bounded (u : NTree (GenComputeRow K))
    (hu : InTree (mmTree (K := K)) u) :
    computeNodeBounded 65537 u :=
  genComputeSkeleton_inTree_bounded (by omega) mmSubject_bounded mmFormula_bounded
    mm_evalG_65537 (mmTree_gen (K := K)) u hu

theorem mmTreeAir_inTree_bounded (u : NTree (GenComputeRow K))
    (hu : InTree (mmTreeAir (K := K)) u) :
    computeNodeBounded 65537 u := by
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  have h := mmTree_inTree_bounded u0 hu0
  simp only [computeNodeBounded] at h ⊢
  rw [hl]
  exact h

/-! ## Assigned compute-node bound transport -/

theorem bfsAssign_inTree_computeNodeBounded {q : ℕ}
    {t : NTree (GenComputeRow K)}
    (H : ∀ u, InTree t u → computeNodeBounded q u)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign t) n) :
    computeNodeBounded q n := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hlab
  obtain ⟨i, hi, hni⟩ := List.mem_map.mp hlab
  have hi' := lt_bfsRows_of_mem_range' hi
  have hrow : (bfsRows t)[i - 1] ∈ bfsRows t := List.getElem_mem hi'
  unfold bfsRows at hrow
  obtain ⟨n0, hn0, hlab0⟩ := List.mem_map.mp hrow
  obtain ⟨u0, hu0, hin0⟩ := (mem_bfsForest _ n0).mp hn0
  simp only [List.mem_singleton] at hu0
  subst u0
  have hb := H n0 hin0
  simp only [computeNodeBounded] at hb ⊢
  rw [← hni, bfsLabelAt_skel t i hi', bfsLabelAt_requests t i hi']
  have hbeq : (bfsRows t)[i - 1] = n0.label := by
    unfold bfsRows
    exact hlab0.symm
  rw [hbeq]
  exact hb

/-! ## Memory-builder InTree bounds (generic modulus) -/

theorem boundedBy_nounWalk (E : Noun → ComputeTable.FP K) (z : K) {q : ℕ}
    (h0 : 0 < q) :
    ∀ n, FieldEmbedding.BoundedBy q n →
      ∀ t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
        t.label.skel.BoundedBy q
  | .atom a, hn, t, ht => by
      cases ht with
      | here =>
        simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
        exact memHaltSkel_bounded (by simpa [FieldEmbedding.BoundedBy] using hn)
      | sub hs _ =>
        simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, hn, t, ht => by
      have hh : FieldEmbedding.BoundedBy q h :=
        (FieldEmbedding.BoundedBy_cell.mp hn).1
      have htl : FieldEmbedding.BoundedBy q tl :=
        (FieldEmbedding.BoundedBy_cell.mp hn).2
      cases ht with
      | here =>
        simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
        exact memDecomposeSkel_bounded (by simpa using hn) hh htl
      | sub hs hu =>
        simp [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
          List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact boundedBy_nounWalk E z h0 h hh _ hu
        · exact boundedBy_nounWalk E z h0 tl htl _ hu

theorem boundedBy_verify (E : Noun → ComputeTable.FP K) (z : K) {q : ℕ}
    (h0 : 0 < q) (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (hr : FieldEmbedding.BoundedBy q root)
    (hc : FieldEmbedding.BoundedBy q child)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t) :
    t.label.skel.BoundedBy q := by
  cases ht with
  | here =>
    simp [genAnnotatedVerify, NTree.label, gMemRow9]
    exact memVerifySkelAx_bounded hr hc
  | sub hs hu =>
    simp [genAnnotatedVerify, NTree.children_node, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    subst hs
    exact boundedBy_nounWalk E z h0 child hc _ hu

theorem boundedBy_descent (E : Noun → ComputeTable.FP K) (z : K) {q : ℕ}
    (h0 : 0 < q) (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (hr : FieldEmbedding.BoundedBy q root)
    (hc : FieldEmbedding.BoundedBy q child)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    FieldEmbedding.BoundedBy q currentNoun →
    ∀ u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1,
      ∀ n, InTree u n → n.label.skel.BoundedBy q := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ ax ih =>
    intro hcur u hu n hn
    unfold genAnnotatedDescent at hu
    split at hu
    · simp [genAnnotatedVerify] at hu
      subst u
      exact boundedBy_verify E z h0 root child recAxis ts recordExp hr hc n hn
    · have hge : 2 ≤ ax := by omega
      have hrest := axisRest_lt hge
      have hhd := formulaHead_boundedBy h0 hcur
      have htl := formulaTail_boundedBy h0 hcur
      split at hu
      · simp at hu
        subst u
        cases hn with
        | here =>
          simp [NTree.label, gMemRow9]
          exact memDecomposeSkel_bounded hcur hhd htl
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_append, List.mem_cons,
            List.not_mem_nil] at hs
          rcases hs with rfl | hmem
          · exact boundedBy_nounWalk E z h0 (formulaHead currentNoun) hhd n hu'
          · exact ih (axisRest ax) hrest (formulaTail currentNoun) htl _ hmem n hu'
      · simp at hu
        subst u
        cases hn with
        | here =>
          simp [NTree.label, gMemRow9]
          exact memDecomposeSkel_bounded hcur hhd htl
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_append, List.mem_cons,
            List.not_mem_nil, List.mem_singleton] at hs
          rcases hs with hmem | rfl
          · exact ih (axisRest ax) hrest (formulaHead currentNoun) hhd _ hmem n hu'
          · exact boundedBy_nounWalk E z h0 (formulaTail currentNoun) htl n hu'

theorem boundedBy_record (E : Noun → ComputeTable.FP K) (z α : K) {q : ℕ}
    (h0 : 0 < q) (root child : Noun) (axis recordExp : ℕ)
    (hr : FieldEmbedding.BoundedBy q root)
    (hc : FieldEmbedding.BoundedBy q child)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedRecordTree E z α lmb root child axis recordExp) t) :
    t.label.skel.BoundedBy q := by
  rw [genAnnotatedRecordTree_eq] at ht
  cases ht with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memReadSkelAx_bounded hr hc (atom0_boundedBy h0)
  | sub hs hu =>
    simp [NTree.children_node] at hs
    exact boundedBy_descent E z h0 root child axis (α ^ recordExp) recordExp
      hr hc root axis hr _ hs t hu

theorem boundedBy_descentCont (E : Noun → ComputeTable.FP K) (z : K) {q : ℕ}
    (h0 : 0 < q) (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (hcs : ∀ u ∈ cont, ∀ n, InTree u n → n.label.skel.BoundedBy q)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    FieldEmbedding.BoundedBy q currentNoun →
    ∀ u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1,
      ∀ n, InTree u n → n.label.skel.BoundedBy q := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ ax ih =>
    intro hcur u hu n hn
    unfold genAnnotatedDescentCont at hu
    split at hu
    · exact hcs u hu n hn
    · have hge : 2 ≤ ax := by omega
      have hrest := axisRest_lt hge
      have hhd := formulaHead_boundedBy h0 hcur
      have htl := formulaTail_boundedBy h0 hcur
      split at hu
      · simp at hu
        subst u
        cases hn with
        | here =>
          simp [NTree.label, gMemRow9]
          exact memDecomposeSkel_bounded hcur hhd htl
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_append, List.mem_cons,
            List.not_mem_nil] at hs
          rcases hs with rfl | hmem
          · exact boundedBy_nounWalk E z h0 (formulaHead currentNoun) hhd n hu'
          · exact ih (axisRest ax) hrest (formulaTail currentNoun) htl _ hmem n hu'
      · simp at hu
        subst u
        cases hn with
        | here =>
          simp [NTree.label, gMemRow9]
          exact memDecomposeSkel_bounded hcur hhd htl
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_append, List.mem_cons,
            List.not_mem_nil, List.mem_singleton] at hs
          rcases hs with hmem | rfl
          · exact ih (axisRest ax) hrest (formulaHead currentNoun) hhd _ hmem n hu'
          · exact boundedBy_nounWalk E z h0 (formulaTail currentNoun) htl n hu'

theorem boundedBy_chainedInner (E : Noun → ComputeTable.FP K) (z α : K) {q : ℕ}
    (h0 : 0 < q) (prev : MemRecordReq) (more : List MemRecordReq)
    (hprev : FieldEmbedding.BoundedBy q prev.root ∧
      FieldEmbedding.BoundedBy q prev.child)
    (hmore : ∀ r ∈ more,
      FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child) :
    ∀ u ∈ (genAnnotatedChainedInner E z α lmb prev more).1,
      ∀ n, InTree u n → n.label.skel.BoundedBy q := by
  induction more generalizing prev with
  | nil =>
    intro u hu n hn
    rw [genAnnotatedChainedInner_nil] at hu
    simp at hu
    subst u
    exact boundedBy_verify E z h0 prev.root prev.child prev.axis
      (α ^ prev.recordExp) prev.recordExp hprev.1 hprev.2 n hn
  | cons r rest ih =>
    intro u hu n hn
    have hr : FieldEmbedding.BoundedBy q r.root ∧
        FieldEmbedding.BoundedBy q r.child :=
      hmore r (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ s ∈ rest,
        FieldEmbedding.BoundedBy q s.root ∧ FieldEmbedding.BoundedBy q s.child :=
      fun s hs => hmore s (List.mem_cons_of_mem _ hs)
    unfold genAnnotatedChainedInner at hu
    simp [chainedInnerRootState] at hu
    subst u
    cases hn with
    | here =>
      simp [NTree.label, gMemRow9]
      exact memReadSkelAx_bounded hr.1 hr.2 (atom0_boundedBy h0)
    | sub hs hu' =>
      simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases hu' with
      | here =>
        simp [NTree.label, gMemRow9]
        exact memVerifySkelAx_bounded hprev.1 hprev.2
      | sub hs' hu'' =>
        exact boundedBy_descentCont E z h0
          (genAnnotatedChainedInner E z α lmb r rest).1
          (genAnnotatedChainedInner E z α lmb r rest).2
          (chainedInnerRootState rest) (fun w hw m hm => ih r hr hrest w hw m hm)
          r.root r.axis hr.1 _ hs' n hu''

theorem boundedBy_chainedTree (E : Noun → ComputeTable.FP K) (z α : K) {q : ℕ}
    (h0 : 0 < q) (reqs : List MemRecordReq)
    (hreqs : ∀ r ∈ reqs,
      FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t)
    (n : NTree (GenMemoryRow K)) (hn : InTree t n) :
    n.label.skel.BoundedBy q := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at ht
  | [r] =>
    simp [genAnnotatedChainedTree] at ht
    subst t
    exact boundedBy_record E z α h0 r.root r.child r.axis r.recordExp
      (hreqs r (by simp)).1 (hreqs r (by simp)).2 n hn
  | r :: r2 :: rest =>
    have hr := hreqs r (by simp)
    have hmore : ∀ s ∈ r2 :: rest,
        FieldEmbedding.BoundedBy q s.root ∧ FieldEmbedding.BoundedBy q s.child :=
      fun s hs => hreqs s (List.mem_cons_of_mem _ hs)
    unfold genAnnotatedChainedTree at ht
    simp [chainedInnerRootState] at ht
    subst t
    cases hn with
    | here =>
      simp [NTree.label, gMemRow9]
      exact memReadSkelAx_bounded hr.1 hr.2 (atom0_boundedBy h0)
    | sub hs hu =>
      simp [NTree.children_node] at hs
      exact boundedBy_descentCont E z h0
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
        (chainedInnerRootState (r2 :: rest))
        (fun w hw m hm =>
          boundedBy_chainedInner E z α h0 r (r2 :: rest) hr hmore w hw m hm)
        r.root r.axis hr.1 _ hs n hu

theorem boundedBy_rowMemForest (E : Noun → ComputeTable.FP K) (z α : K) {q : ℕ}
    (h0 : 0 < q) (reqs : List MemRecordReq)
    (hreqs : ∀ r ∈ reqs,
      FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genRowMemForest E z α lmb reqs)
    (n : NTree (GenMemoryRow K)) (hn : InTree u n) :
    n.label.skel.BoundedBy q := by
  match reqs with
  | [] => simp [genRowMemForest] at hu
  | [r] =>
    simp [genRowMemForest_singleton] at hu
    subst u
    exact boundedBy_record E z α h0 r.root r.child r.axis r.recordExp
      (hreqs r (by simp)).1 (hreqs r (by simp)).2 n hn
  | [r1, r2] =>
    have h1 := hreqs r1 (by simp)
    have h2 := hreqs r2 (by simp)
    rw [genRowMemForest_two_eq] at hu
    split_ifs at hu with hc
    · split at hu
      · rename_i t ht
        simp at hu
        subst u
        exact boundedBy_chainedTree E z α h0 [r1, r2] hreqs t ht n hn
      · simp at hu
        rcases hu with rfl | rfl
        · exact boundedBy_record E z α h0 r1.root r1.child r1.axis r1.recordExp
            h1.1 h1.2 n hn
        · exact boundedBy_record E z α h0 r2.root r2.child r2.axis r2.recordExp
            h2.1 h2.2 n hn
    · simp at hu
      rcases hu with rfl | rfl
      · exact boundedBy_record E z α h0 r1.root r1.child r1.axis r1.recordExp
          h1.1 h1.2 n hn
      · exact boundedBy_record E z α h0 r2.root r2.child r2.axis r2.recordExp
          h2.1 h2.2 n hn
  | [r1, r2, r3] =>
    have h1 := hreqs r1 (by simp)
    have h2 := hreqs r2 (by simp)
    have h3 := hreqs r3 (by simp)
    have h12 : ∀ r ∈ [r1, r2],
        FieldEmbedding.BoundedBy q r.root ∧ FieldEmbedding.BoundedBy q r.child := by
      intro r hr
      simp [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2
    rw [genRowMemForest_three_eq, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | rfl
    · rw [genRowMemForest_two_eq] at hmem
      split_ifs at hmem with hc
      · split at hmem
        · rename_i t ht
          simp at hmem
          subst u
          exact boundedBy_chainedTree E z α h0 [r1, r2] h12 t ht n hn
        · simp at hmem
          rcases hmem with rfl | rfl
          · exact boundedBy_record E z α h0 r1.root r1.child r1.axis r1.recordExp
              h1.1 h1.2 n hn
          · exact boundedBy_record E z α h0 r2.root r2.child r2.axis r2.recordExp
              h2.1 h2.2 n hn
      · simp at hmem
        rcases hmem with rfl | rfl
        · exact boundedBy_record E z α h0 r1.root r1.child r1.axis r1.recordExp
            h1.1 h1.2 n hn
        · exact boundedBy_record E z α h0 r2.root r2.child r2.axis r2.recordExp
            h2.1 h2.2 n hn
    · exact boundedBy_record E z α h0 r3.root r3.child r3.axis r3.recordExp
        h3.1 h3.2 n hn
  | r1 :: r2 :: r3 :: r4 :: rest =>
    have hlong :
        genRowMemForest E z α lmb (r1 :: r2 :: r3 :: r4 :: rest) =
          (r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp :=
      rfl
    rw [hlong, List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    exact boundedBy_record E z α h0 r.root r.child r.axis r.recordExp
      (hreqs r hr).1 (hreqs r hr).2 n hn

theorem boundedBy_memForestFromTree (z α : K) {q : ℕ} (_h0 : 0 < q)
    (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        ∀ v, InTree u v → v.label.skel.BoundedBy q)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t)
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.skel.BoundedBy q := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
          ∀ v, InTree u v → v.label.skel.BoundedBy q) →
      ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
        ∀ v, InTree u v → v.label.skel.BoundedBy q from
    this (NTree.size t) t le_rfl H u hu v hv
  intro N
  induction N with
  | zero =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu v hv
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
                  ∀ v, InTree u v → v.label.skel.BoundedBy q) →
              ∀ u ∈ genMemForestFromList (encC z) z α lmb cs',
                ∀ v, InTree u v → v.label.skel.BoundedBy q := by
          intro cs' hsub hsz H' u' hu' v' hv'
          induction cs' generalizing u' v' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' v' hv'
            · refine ihcs ?_ ?_ ?_ u' hu' v' hv'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
          (fun t ht n hn => H n (InTree.sub ht hn)) u hu v hv
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum :=
          List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem mmAssigned_rowBounded (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.skel.BoundedBy 65537 := by
  have hb := bfsAssign_inTree_computeNodeBounded
    (t := mmTreeAir (K := K)) mmTreeAir_inTree_bounded n hn
  intro u hu v hv
  refine boundedBy_rowMemForest (encC z) z α (by omega) (extractNodeReqs n.label)
    ?_ u hu v hv
  intro r hr
  unfold extractNodeReqs at hr
  obtain ⟨req, hreq, hroot, hchild, _⟩ := extractNodeReqsAux_mem _ _ _ r hr
  have hreqb := hb.2 req hreq
  exact ⟨by rw [hroot]; exact hreqb.1, by rw [hchild]; exact hreqb.2⟩

theorem mmAssigned_inTree_bounded (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb
      (bfsAssign (mmTreeAir (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.skel.BoundedBy 65537 :=
  boundedBy_memForestFromTree z α (by omega) _
    (mmAssigned_rowBounded z α) u hu v hv

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

theorem semanticSkeleton_computeRows (z α : K) :
    computeSkeletonRows (semanticSkeleton z α) =
      (bfsForest [mmTreeAir (K := K)]).map (fun n => n.label.skel) := by
  rw [semanticSkeleton, computeSkeletonRows_genSemantic,
    computeSkeletonRows_genCompute, bfsAssign_skel_list]

theorem semanticSkeleton_computeRows_bounded (z α : K) :
    (computeSkeletonRows (semanticSkeleton z α)).Forall
      (ComputeRowSkeleton.BoundedBy 65537) := by
  rw [semanticSkeleton_computeRows]
  refine List.forall_iff_forall_mem.mpr ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hu
  subst u
  exact (mmTreeAir_inTree_bounded n hin).1

theorem semanticSkeleton_memoryRows (z α : K) :
    (memorySkeletonRows (semanticSkeleton z α)).Forall
      (MemoryRowSkeleton.BoundedBy 65537) := by
  rw [semanticSkeleton, memorySkeletonRows_genSemantic]
  refine List.forall_iff_forall_mem.mpr ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  unfold assignedForest at hu
  exact mmAssigned_inTree_bounded z α u hu n hin

theorem semanticSkeleton_bounded (z α : K) :
    (semanticSkeleton z α).BoundedBy 65537 := by
  refine ⟨semanticSkeleton_computeRows_bounded z α,
    semanticSkeleton_memoryRows z α, ?_⟩
  intro tree htree node hnode
  have hmem : node.label ∈ memorySkeletonRows (semanticSkeleton z α) := by
    refine List.mem_map.mpr ⟨node, ?_, rfl⟩
    exact (mem_bfsForest _ node).mpr ⟨tree, htree, hnode⟩
  exact List.forall_iff_forall_mem.mp (semanticSkeleton_memoryRows z α) _ hmem

theorem nounRealization_seed :
    ExactExecutionNounRealization 65537 (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) :=
  nounRealization_of_binds seedZ_ne_zero
    (semanticSkeleton_bounded seedZ alphaA) bindsAt_seed

theorem language_seed
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 65537
      (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  language_of_traversable_noun (traversable_seed hfirst) nounRealization_seed

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.mm_evalG_65537
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmTree_inTree_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmAssigned_inTree_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.semanticSkeleton_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.nounRealization_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.language_seed


