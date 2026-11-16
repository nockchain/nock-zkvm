/-
  Nock/NockVMROM/Thm54/VclL/Handle/AluProvJ9.lean

  **The ALU's `TAG_jet` providers are genuine.**

  `aluProvOK`: every record whose key is in `aluJetProvsOf` (the `keyJet (id, kc, vc, kS, vS, kE, vE, 3)` of every
  `hdr` row with `sH·mJ ≠ 0`) satisfies the jet clause of `RowSemChipX.RecOK` at `j = primSpec op`:
  `Rg id = some (primSpec op)`, `D (kc, vc) = some (primC op)`, the subject `S` (a cell `[A B]` by `Cell3`) and the
  result `E` with `(primTemplate op).rel S E` (`binT`: axes `2`, `3`, `primSem op`).

  The per-row input `hrow` is what the caller supplies for a `hdr` row:
  * `Rg id = some (primSpec op)`: the `AcceptsJ9AL.hPrim` field (the op comes from the consumed op record);
  * `D (kc, vc) = some (primC op)`: `hReg_of_pinP`'s conclusion (`denK … (1, idxP id) = some (primC op)`) transported
    along the consumed `keyRg` record `(2, id, kc, vc)` (the J-side `pinCons` for `(1, idxP id)`);
  * `Cell3 D (kS, vS) (kA, vA) (kB, vB)`: the consumed export record `keyX (vS, kA, vA, kB, vB)` (`RecOK .x`);
  * the three `HDen` facts and `primSem op na nb = some nc`: exactly the conclusion of `AluSZOps.op_sound6`;
  * `hDen`: the bridge from `HDen` (the atom table's reading) to the denotation `D` (`HDen.denK` at `D = denK …`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZOpsMD
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProvKindsX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluProvJ9

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX Cell3)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I recClass PreI9)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (PreI)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 (provP9I_of_pre clsKey_of_tag7)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (PubJ9AL TrJ9AL alE0 aluJetProvsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (cv)
open Nock.Jet.Prim (PrimOp primSem primC primSpec primTemplate)

noncomputable section

section Prov
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- The `binT` relation on a cell subject `[A B]` with atom arguments. -/
theorem binT_rel (op : PrimOp) (hop : op ≠ .dec) {na nb nc : ℕ}
    (hs : primSem op na nb = some nc) :
    (primTemplate op).rel (.cell (.atom na) (.atom nb)) (.atom nc) := by
  have hT : primTemplate op = Nock.Jet.Prim.binT op := by
    cases op <;> first | exact absurd rfl hop | rfl
  rw [hT]
  have ha : (Nock.Jet.Prim.binT op).args (.cell (.atom na) (.atom nb)) = some ![.atom na, .atom nb] := by
    refine (Nock.Jet.Template.args_eq_some (T := Nock.Jet.Prim.binT op)).mpr ?_
    intro i
    fin_cases i <;> simp [Nock.Jet.Prim.binT, Noun.slot]
  unfold Nock.Jet.Template.rel Nock.Jet.Template.semS
  rw [ha]
  simp [Nock.Jet.Prim.binT, hs]

theorem mem_jet [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p))
    {q : (Fin 8 → K) × K} (hq : q ∈ aluJetProvsOf (K := K) δ b Pb tr) :
    ∃ i : Fin Pb.nL, (alE0 (K := K) δ b Pb tr i).trace sH * (alE0 (K := K) δ b Pb tr i).trace mJ ≠ 0 ∧
      q.1 = AxisChipJ9.keyVecL 8 keyJetE (alE0 (K := K) δ b Pb tr i) := by
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  by_cases h : (alE0 (K := K) δ b Pb tr i).trace sH * (alE0 (K := K) δ b Pb tr i).trace mJ = 0
  · simp only [h, if_true] at hi; simp at hi
  · simp only [h, if_false] at hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨i, h, rfl⟩

/-- **`aluProvOK`**: every `keyJet` the ALU provides is a genuine jet record at `primSpec op`. -/
theorem aluProvOK (hp5 : 5 < p) [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p))
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hrow : ∀ i : Fin Pb.nL,
      (alE0 (K := K) δ b Pb tr i).trace sH * (alE0 (K := K) δ b Pb tr i).trace mJ ≠ 0 →
      ∃ op : PrimOp, op ≠ .dec ∧
        Rg ((alE0 (K := K) δ b Pb tr i).trace idc).val = some (primSpec op) ∧
        D (((alE0 (K := K) δ b Pb tr i).trace kc).val, ((alE0 (K := K) δ b Pb tr i).trace vc).val)
          = some (primC op) ∧
        Cell3 D (((alE0 (K := K) δ b Pb tr i).trace kS).val, ((alE0 (K := K) δ b Pb tr i).trace vS).val)
          (((alE0 (K := K) δ b Pb tr i).trace kA).val, ((alE0 (K := K) δ b Pb tr i).trace vA).val)
          (((alE0 (K := K) δ b Pb tr i).trace kB).val, ((alE0 (K := K) δ b Pb tr i).trace vB).val) ∧
        ∃ na nb nc,
          D (((alE0 (K := K) δ b Pb tr i).trace kA).val, ((alE0 (K := K) δ b Pb tr i).trace vA).val)
            = some (.atom na) ∧
          D (((alE0 (K := K) δ b Pb tr i).trace kB).val, ((alE0 (K := K) δ b Pb tr i).trace vB).val)
            = some (.atom nb) ∧
          D (((alE0 (K := K) δ b Pb tr i).trace kE).val, ((alE0 (K := K) δ b Pb tr i).trace vE).val)
            = some (.atom nc) ∧
          primSem op na nb = some nc) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg comb) .s (aluJetProvsOf (K := K) δ b Pb tr) := by
  have h3 : (3 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  have hcls : ∀ q ∈ aluJetProvsOf (K := K) δ b Pb tr, ProvKindsX9.ClsKey (p := p) q.1 := by
    intro q hq
    obtain ⟨i, -, hk⟩ := mem_jet δ b Pb tr hq
    rw [hk]
    exact clsKey_of_tag7 hp5 (t := 3) (by omega) (by norm_num) (by norm_num)
      (by simp [AxisChipJ9.keyVecL, keyJetE, keyJetRE, reE, CoeffExpr.eval])
  refine provP9I_of_pre hcls ?_
  intro q hq l hl hlt hnk _
  change l.length ≤ 8 at hl
  change Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8.natKey (p := p) (K := K) 8 l = q.1 at hnk
  obtain ⟨i, hw, hk⟩ := mem_jet δ b Pb tr hq
  rw [hk] at hnk
  · -- the row
    obtain ⟨op, hop, hRg, hc, hcell, na, nb, nc, hA, hB, hE, hsem⟩ := hrow i hw
    set e := alE0 (K := K) δ b Pb tr i with he
    have e8 : ∀ c (hc : c < 8), ((l.getD c 0 : ℕ) : ZMod p) =
        ((keyJetE : List (CoeffExpr (ZMod p))).getD c (.const 0)).eval e := fun c hc =>
      (algebraMap (ZMod p) K).injective (congrFun hnk ⟨c, hc⟩)
    have hlen : l.length = 8 := by
      by_contra hne
      have e7 := e8 7 (by norm_num)
      rw [List.getD_eq_default _ _ (by omega)] at e7
      simp [keyJetE, keyJetRE, reE, CoeffExpr.eval] at e7
      have : ((3 : ℕ) : ZMod p) ≠ ((0 : ℕ) : ZMod p) := Nock.Jet.RapJetJ8.ne_cast h3 h0 (by norm_num)
      exact this (by simpa using e7.symm)
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := Nock.Jet.RapJetJ8.eight l hlen
    have hlt' : ∀ x ∈ [x0, x1, x2, x3, x4, x5, x6, x7], x < p := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
    obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := hlt'
    have c0 := e8 0 (by norm_num); have c1 := e8 1 (by norm_num); have c2 := e8 2 (by norm_num)
    have c3 := e8 3 (by norm_num); have c4 := e8 4 (by norm_num); have c5 := e8 5 (by norm_num)
    have c6 := e8 6 (by norm_num); have c7 := e8 7 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero, keyJetE, keyJetRE, List.map_cons, List.map_nil, reE,
      CoeffExpr.eval, cv] at c0 c1 c2 c3 c4 c5 c6 c7
    have v0 := Nock.Jet.RapJetJ8.val_of_cast l0 c0
    have v1 := Nock.Jet.RapJetJ8.val_of_cast l1 c1
    have v2 := Nock.Jet.RapJetJ8.val_of_cast l2 c2
    have v3 := Nock.Jet.RapJetJ8.val_of_cast l3 c3
    have v4 := Nock.Jet.RapJetJ8.val_of_cast l4 c4
    have v5 := Nock.Jet.RapJetJ8.val_of_cast l5 c5
    have v6 := Nock.Jet.RapJetJ8.val_of_cast l6 c6
    have v7 := Nock.Jet.ChipJ8.natCast_inj_lt l7 h3 (by simpa using c7)
    subst v7 v0 v1 v2 v3 v4 v5 v6
    obtain ⟨A, B, hS, hAd, hBd⟩ := hcell
    have hAn := hA
    have hBn := hB
    have hEn := hE
    refine ⟨primSpec op, hRg, hc, .cell A B, .atom nc, hS, hEn, ?_⟩
    rw [hAd] at hAn; rw [hBd] at hBn
    obtain rfl := Option.some.inj hAn
    obtain rfl := Option.some.inj hBn
    exact binT_rel op hop hsem

end Prov

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluProvJ9

open Nock.NockVMROM.Thm54.VclL.Handle.AluProvJ9 in
#print axioms binT_rel
open Nock.NockVMROM.Thm54.VclL.Handle.AluProvJ9 in
#print axioms aluProvOK
