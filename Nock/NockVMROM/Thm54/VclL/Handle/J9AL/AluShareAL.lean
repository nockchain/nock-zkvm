/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluShareAL.lean

  **The ALU share of the service obligation.** The ALU's service provides `aluPL = aluRegProvsOf ++ aluJetProvsOf` meet `RecOK9I`:
  * `regProv_ok`: the `preg` provides (keyRg tag `7`, op record tag `6`) are class-`0` keys whose `RecOK` clause is
    `True` (no tag-`3` jet clause, no inc / path shape).
  * `op_of_code`: on a `hdr` row (`sH = 1`) the op code `opc = primCode op` (from `BindAL.hdr_binding`) makes
    `op ≠ dec` and the op flag `opColOf op` equal to `1` (the one-hot op flags, `gKind`, `gHdr`).
  * `jetProv_ok`: `AluProvJ9.aluProvOK`'s per-row input from (1) the `hdr ↔ preg` binding (`BindAL.hdr_binding`),
    (2) `hPrim`, (3) the cell-side pin `D (1, idxP id) = primC op` (`AcceptsJ9AL.hReg_of_pinP`), (4) the export
    `Cell3` (the consumed `keyX (vS, kA, vA, kB, vB)` with `kS = 1` by `gKS`) and (5) the per-call semantics on the
    hdr handles (`AluSZOps.op_sound6`, supplied by the caller at the `AluSZOps` context).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.BindAL
import Nock.NockVMROM.Thm54.VclL.Handle.AluProvJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluShareAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead (ag_zero mem_kind)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op keyVecL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (aluEF aluEK alu_rowGates opColOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX Cell3)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I recClass)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 (provP9I_of_pre clsKey_of_tag7)
open Nock.Jet.Prim (PrimOp primSem primC primSpec)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The `preg` provides -/

section Reg
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- **The `preg` provides meet `RecOK9I`** (class `0`, and `RecOK` of a tag-`7` / tag-`6` 8-entry record is
`True`). -/
theorem regProv_ok (hp7 : 7 < p) [DecidableEq (ZMod p)] (Pb : PubJ9AL p) (tr : TrJ9AL (ZMod p))
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun} :
    ProvP (p := p) (K := K) (RecOK9I D V Rg comb) .s (aluRegProvsOf (K := K) δ b Pb tr) := by
  have hmem : ∀ q ∈ aluRegProvsOf (K := K) δ b Pb tr, ∃ e : Env (ZMod p),
      q.1 = keyVecL 8 keyRgE e ∨ q.1 = keyVecL 8 opRecE e := by
    intro q hq
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq
    split_ifs at hj with hz
    · simp at hj
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inr rfl⟩
  have h7 : ∀ q ∈ aluRegProvsOf (K := K) δ b Pb tr,
      q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((7 : ℕ) : ZMod p) ∨
        q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((6 : ℕ) : ZMod p) := by
    intro q hq
    obtain ⟨e, he | he⟩ := hmem q hq <;> rw [he]
    · left; simp [keyVecL, keyRgE, keyRgRE, reE, CoeffExpr.eval, tagRgP]
    · right; simp [keyVecL, opRecE, opRecRE, reE, CoeffExpr.eval, tagOp]
  refine provP9I_of_pre (fun q hq => ?_) ?_
  · rcases h7 q hq with h | h
    · exact clsKey_of_tag7 (by omega) (t := 7) (by omega) (by norm_num) (by norm_num) h
    · exact clsKey_of_tag7 (by omega) (t := 6) (by omega) (by norm_num) (by norm_num) h
  · intro q hq l hl hlt hnk _
    change l.length ≤ 8 at hl
    change Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8.natKey (p := p) (K := K) 8 l = q.1 at hnk
    have e7 := congrFun hnk ⟨7, by norm_num⟩
    simp only [Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8.natKey] at e7
    have h76 : l.getD 7 0 = 7 ∨ l.getD 7 0 = 6 := by
      have hlt7 : l.getD 7 0 < p := by
        rcases Nat.lt_or_ge 7 l.length with hc | hc
        · rw [List.getD_eq_getElem _ _ hc]; exact hlt _ (List.getElem_mem hc)
        · rw [List.getD_eq_default _ _ hc]; omega
      rcases h7 q hq with h | h <;> rw [h] at e7 <;> have e := (algebraMap (ZMod p) K).injective e7
      · left; exact Nock.Jet.ChipJ8.natCast_inj_lt hlt7 (by omega) e
      · right; exact Nock.Jet.ChipJ8.natCast_inj_lt hlt7 (by omega) e
    have hlen : l.length = 8 := by
      by_contra hne
      rw [List.getD_eq_default _ _ (by omega)] at h76
      omega
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := Nock.Jet.RapJetJ8.eight l hlen
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h76
    rcases h76 with rfl | rfl <;> trivial

end Reg

/-! ## 2. The op flag of a `hdr` row (at the ALU's field) -/

section Flag
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {chals pubs : ℕ → K}

local notation "CH" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL
local notation "QL" => qAL δ b Pb tr chals pubs
local notation "E0" => alE0 (K := K) δ b Pb tr

theorem nat01 {x : Fp} (h : x = 0 ∨ x = 1) : ∃ n : ℕ, n ≤ 1 ∧ x = (n : Fp) := by
  rcases h with rfl | rfl
  · exact ⟨0, by omega, by simp⟩
  · exact ⟨1, le_rfl, by simp⟩

theorem opcol_bool (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) {j : ℕ} (hj : j ∈ opCols) :
    ∃ n : ℕ, n ≤ 1 ∧ (E0 i).trace j = (n : Fp) := by
  have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
    (mem_kind (a := ar (boolE (cv j))) (by
      unfold gKind
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩)))))))
  simp only [AG.gate, ar, boolE, cv, CoeffExpr.eval] at g
  exact nat01 (Chips.CertBound.bool_cases g)

theorem onehot6 {a1 a2 a3 a4 a5 a6 k : ℕ} (h1 : a1 ≤ 1) (h2 : a2 ≤ 1) (h3 : a3 ≤ 1) (h4 : a4 ≤ 1) (h5 : a5 ≤ 1)
    (h6 : a6 ≤ 1) (hs : a1 + a2 + a3 + a4 + a5 + a6 = 1)
    (hk : 1 * a1 + 2 * a2 + 3 * a3 + 4 * a4 + 5 * a5 + 6 * a6 = k) :
    (k = 1 → a1 = 1) ∧ (k = 2 → a2 = 1) ∧ (k = 3 → a3 = 1) ∧ (k = 4 → a4 = 1) ∧ (k = 5 → a5 = 1) ∧
      (k = 6 → a6 = 1) ∧ k ≠ 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h3 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h4 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h5 with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h6 with rfl | rfl <;> omega

/-- **The op flag of a `hdr` row**: `opc = primCode op` forces `op ≠ dec` and `opColOf op = 1`. -/
theorem op_of_code (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) (hH : (E0 i).trace sH = 1) {op : PrimOp}
    (hc : (E0 i).trace opc = ((primCode op : ℕ) : Fp)) :
    op ≠ .dec ∧ (E0 i).trace (opColOf op) = 1 := by
  have hG := alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i
  have g1 := ag_zero hG (AluSZOps.Rows.mem_hdr (a := ar (.mul (cv sH) (.sub (cv opc) opCode))) (by simp [gHdr]))
  have g2 := ag_zero hG (mem_kind (a := ar (.mul (cv sH) (.sub (sumC opCols) (.const 1)))) (by simp [gKind]))
  simp only [AG.gate, ar, opCode, sumC, opCols, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] at g1 g2
  have hT : ∀ j, (aluEF b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL i).trace j = (E0 i).trace j :=
    fun _ => rfl
  simp only [hT] at g1 g2
  rw [hH, one_mul, sub_eq_zero] at g1 g2
  obtain ⟨a1, ha1, e1⟩ := opcol_bool δ b hsat i (j := oAdd) (by simp [opCols])
  obtain ⟨a2, ha2, e2⟩ := opcol_bool δ b hsat i (j := oSub) (by simp [opCols])
  obtain ⟨a3, ha3, e3⟩ := opcol_bool δ b hsat i (j := oLt) (by simp [opCols])
  obtain ⟨a4, ha4, e4⟩ := opcol_bool δ b hsat i (j := oMul) (by simp [opCols])
  obtain ⟨a5, ha5, e5⟩ := opcol_bool δ b hsat i (j := oDiv) (by simp [opCols])
  obtain ⟨a6, ha6, e6⟩ := opcol_bool δ b hsat i (j := oMod) (by simp [opCols])
  rw [e1, e2, e3, e4, e5, e6] at g1 g2
  rw [hc] at g1
  have hp : 40 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  have hcast : ∀ {x y : ℕ}, x < 40 → y < 40 → (x : Fp) = (y : Fp) → x = y := fun hx hy h => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; exact h
  have hs : a1 + a2 + a3 + a4 + a5 + a6 = 1 := by
    refine hcast (by omega) (by omega) ?_
    push_cast; linear_combination g2
  have hpc : primCode op < 7 := by cases op <;> simp [primCode]
  have hk : 1 * a1 + 2 * a2 + 3 * a3 + 4 * a4 + 5 * a5 + 6 * a6 = primCode op := by
    refine hcast (by omega) (by omega) ?_
    push_cast; linear_combination -g1
  obtain ⟨o1, o2, o3, o4, o5, o6, o0⟩ := onehot6 ha1 ha2 ha3 ha4 ha5 ha6 hs hk
  rcases op with _ | _ | _ | _ | _ | _ | _
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oAdd = 1; rw [e1, o1 rfl]; simp
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oSub = 1; rw [e2, o2 rfl]; simp
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oLt = 1; rw [e3, o3 rfl]; simp
  · exact absurd rfl o0
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oMul = 1; rw [e4, o4 rfl]; simp
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oDiv = 1; rw [e5, o5 rfl]; simp
  · refine ⟨by simp, ?_⟩; show (E0 i).trace oMod = 1; rw [e6, o6 rfl]; simp

/-- `kS = 1` on a `hdr` row (`gKS`). -/
theorem kS_one (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) (hH : (E0 i).trace sH = 1) : (E0 i).trace kS = 1 := by
  have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
    (AluSZOps.Rows.mem_hdr (a := ar gKS) (by simp [gHdr]))
  simp only [AG.gate, ar, gKS, CoeffExpr.eval, cv] at g
  change (E0 i).trace sH * ((E0 i).trace kS - 1) = 0 at g
  rw [hH, one_mul, sub_eq_zero] at g
  exact g

/-! ## 3. The jet provides -/

theorem val_cast {n : ℕ} (h : n < Nock.Atoms.p) : ((n : ℕ) : Fp).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-- **The ALU's jet provides meet `RecOK9I`** (`AluProvJ9.aluProvOK` with its per-row input assembled from the
binding, `hPrim`, the cell-side pin, the export `Cell3` and the per-call semantics). -/
theorem jetProv_ok (hsat : (CH).rap.Satisfies QL)
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hlt : ∀ q ∈ Pb.prims, q.1 < Nock.Atoms.p ∧ Pb.idxP q.1 < Nock.Atoms.p)
    (hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (primSpec q.2))
    (hpin : ∀ q ∈ Pb.prims, D (1, Pb.idxP q.1) = some (primC q.2))
    (hbindR : ∀ i : Fin Pb.nL, (E0 i).trace sH ≠ 0 → ∃ q ∈ Pb.prims, (E0 i).trace idc = (q.1 : Fp) ∧
      (E0 i).trace kc = 1 ∧ (E0 i).trace vc = (Pb.idxP q.1 : Fp) ∧ (E0 i).trace opc = ((primCode q.2 : ℕ) : Fp))
    (hcell : ∀ i : Fin Pb.nL, (E0 i).trace sH = 1 →
      Cell3 D (1, ((E0 i).trace vS).val) (((E0 i).trace kA).val, ((E0 i).trace vA).val)
        (((E0 i).trace kB).val, ((E0 i).trace vB).val))
    (hsem : ∀ i : Fin Pb.nL, (E0 i).trace sH = 1 → ∀ op : PrimOp, op ≠ .dec → (E0 i).trace (opColOf op) = 1 →
      ∃ na nb nc, D (((E0 i).trace kA).val, ((E0 i).trace vA).val) = some (.atom na) ∧
        D (((E0 i).trace kB).val, ((E0 i).trace vB).val) = some (.atom nb) ∧
        D (((E0 i).trace kE).val, ((E0 i).trace vE).val) = some (.atom nc) ∧ primSem op na nb = some nc) :
    ProvP (p := Nock.Atoms.p) (K := K) (RecOK9I D V Rg comb) .s (aluJetProvsOf (K := K) δ b Pb tr) := by
  refine AluProvJ9.aluProvOK δ b (by norm_num [Nock.Atoms.p, Nock.Field.p]) Pb tr (fun i hw => ?_)
  have hH0 : (E0 i).trace sH ≠ 0 := left_ne_zero_of_mul hw
  have hH : (E0 i).trace sH = 1 :=
    (AluSumAL.sH_bool δ b Pb tr chals pubs hsat i).resolve_left hH0
  obtain ⟨q, hq, hid, hk, hv, hop⟩ := hbindR i hH0
  obtain ⟨hdec, hflag⟩ := op_of_code δ b hsat i hH hop
  obtain ⟨na, nb, nc, hA, hB, hE, hs⟩ := hsem i hH q.2 hdec hflag
  refine ⟨q.2, hdec, ?_, ?_, ?_, na, nb, nc, hA, hB, hE, hs⟩
  · rw [hid, val_cast (hlt q hq).1]; exact hPrim q hq
  · rw [hk, hv, ZMod.val_one, val_cast (hlt q hq).2]; exact hpin q hq
  · rw [kS_one δ b hsat i hH, ZMod.val_one]; exact hcell i hH

end Flag

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluShareAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluShareAL
#print axioms regProv_ok
#print axioms op_of_code
#print axioms jetProv_ok
end Axioms
