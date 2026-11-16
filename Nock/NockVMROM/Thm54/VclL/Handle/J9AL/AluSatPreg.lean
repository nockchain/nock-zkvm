/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatPreg.lean

  **The preg layout.**

  * `pregsP ps vcOf mOf`: the preg rows of a primitive table `ps` (`AluHonestTable.pregsOf` is
    `pregsP (primsC prims ids) (idxPOf cs prims) (fun id => ids.count id + 1)`, by `rfl`).
  * `preLOf tb k`: the honest preprocessing, the Lagrange interpolant of the table's column `k + 2`
    (`sP / pId / pOp`) over the row nodes; `preLOf_hpre`: it is the `hpre` of `AluSatRows.aluSZChipJ9_honest_sat`.
  * `pregOK_tblP`: at the honest table `tblP` with preg rows `pregsP ps …`, the preprocessing `preLOf` meets the
    accepted predicate's `AcceptsJ9AL.PregOK nodes ps`, under `hnoDec : ∀ q ∈ ps, q.2 ≠ .dec` (the disclosed
    registry restriction: the ALU has no `dec` block, and `primCode .dec = 0 ≠ opIx .dec + 1`).
  * `aluSZChipJ9_honest_sat_preg`: honest acceptance of `aluSZChipJ9` at `preLOf` with `PregOK`, the block gates
    still the hypothesis `hblk`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRows
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.Jet.Prim (PrimOp)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The preg rows -/

section Rows
variable {F : Type} [Field F]

/-- **The preg rows of a primitive table** `ps` (registry index `vcOf`, multiplicity `mOf`). -/
def pregsP (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) : List (BRow F) :=
  ps.map fun q => pregRow q.1 (opIx q.2 + 1) (vcOf q.1) (mOf q.1)

theorem pregsP_preg (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) :
    ∀ r ∈ (pregsP ps vcOf mOf : List (BRow F)), ∃ a b c d : ℕ, r = pregRow a b c d := by
  intro r hr
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
  exact ⟨_, _, _, _, rfl⟩

theorem pregsP_length (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) :
    (pregsP ps vcOf mOf : List (BRow F)).length = ps.length := by
  simp [pregsP]

/-- `opIx o + 1` is the accepted predicate's `primCode o` off `dec`. -/
theorem opIx_succ (o : PrimOp) (h : o ≠ .dec) : opIx o + 1 = RealIOJ9AL.primCode o := by
  cases o <;> first | rfl | exact absurd rfl h

end Rows

/-- A property of every element and of the default holds of `getD`. -/
theorem getD_prop {α : Type} (l : List α) (d : α) (P : α → Prop) (hl : ∀ x ∈ l, P x) (hd : P d) (j : ℕ) :
    P (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => simpa using hd
  | some x => exact hl x (List.mem_of_getElem? h)

/-! ## 2. The preg columns of the honest table -/

section Table
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

/-- Block rows have no preg columns. -/
theorem blocks_noPreg (pN : ℕ) (y : Quad (algebraMap F K δ)) (cls : List CallL) :
    ∀ x : BRow F × QRow (Quad (algebraMap F K δ)), x ∈ cls.flatMap (zipB δ pN y) →
      x.1.sP = 0 ∧ x.1.pId = 0 ∧ x.1.pOp = 0 := by
  intro x hx
  obtain ⟨cl, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨xb, xq⟩ := x
  have hb := (List.of_mem_zip hx).1
  simp only [blockB, List.mem_cons, List.mem_flatMap, slotRows, List.mem_map] at hb
  rcases hb with rfl | ⟨s, -, i, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

theorem rowAt_tblP_lt (pN : ℕ) (y : Quad (algebraMap F K δ)) (pregs : List (BRow F)) (cls : List CallL) (i : ℕ)
    (hi : i < pregs.length) : rowAt δ (tblP δ pN y pregs cls) i = (pregs[i], QRow.zero) := by
  have hl : i < (tblP δ pN y pregs cls).length := by simp [tblP]; omega
  unfold rowAt
  rw [List.getD_eq_getElem _ _ hl]
  simp only [tblP, List.append_assoc]
  rw [List.getElem_append_left (by simpa using hi)]
  simp

theorem rowAt_tblP_ge (pN : ℕ) (y : Quad (algebraMap F K δ)) (pregs : List (BRow F)) (cls : List CallL) (i : ℕ)
    (hi : pregs.length ≤ i) :
    (rowAt δ (tblP δ pN y pregs cls) i).1.sP = 0 ∧ (rowAt δ (tblP δ pN y pregs cls) i).1.pId = 0 ∧
      (rowAt δ (tblP δ pN y pregs cls) i).1.pOp = 0 := by
  unfold rowAt
  simp only [tblP, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  refine getD_prop _ _ (fun x : BRow F × QRow (Quad (algebraMap F K δ)) => x.1.sP = 0 ∧ x.1.pId = 0 ∧ x.1.pOp = 0) (fun x hx => ?_) ⟨rfl, rfl, rfl⟩ _
  rcases List.mem_append.mp hx with hx | hx
  · exact blocks_noPreg δ pN y cls x hx
  · rw [List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl, rfl⟩

theorem rowAt_tblP_preg (pN : ℕ) (y : Quad (algebraMap F K δ)) (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ)
    (cls : List CallL) (i : ℕ) (hi : i < ps.length) :
    (rowAt δ (tblP δ pN y (pregsP ps vcOf mOf) cls) i).1 =
      pregRow ps[i].1 (opIx ps[i].2 + 1) (vcOf ps[i].1) (mOf ps[i].1) := by
  rw [rowAt_tblP_lt δ pN y _ cls i (by rw [pregsP_length]; exact hi)]
  simp [pregsP]

end Table

/-! ## 3. The honest preprocessing -/

section Pre
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)

/-- **The honest preprocessing**: column `k + 2` (`sP / pId / pOp`) of the table, interpolated over the row
nodes. -/
def preLOf (tb : List (BRow F × QRow (Quad (algebraMap F K δ)))) (k : Fin 3) : F[X] :=
  Lagrange.interpolate Finset.univ nodes (fun i => (rowAt δ tb i).1.col ((k : ℕ) + 2))

theorem preLOf_eval (hinj : Function.Injective nodes) (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))
    (k : Fin 3) (i : Fin n) : (preLOf δ nodes tb k).eval (nodes i) = (rowAt δ tb i).1.col ((k : ℕ) + 2) :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

/-- **`preLOf` is the `hpre` of the honest acceptance theorem.** -/
theorem preLOf_hpre (hinj : Function.Injective nodes) (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))
    (r2 : ℕ → Fin n → K) (k : Fin 3) (i : Fin n) :
    (preLOf δ nodes tb k).eval (nodes i) = colAL δ b tb r2 ((k : ℕ) + 2) i := by
  rw [preLOf_eval δ nodes hinj tb k i, colAL, if_pos (by have := k.isLt; omega)]

end Pre

/-! ## 4. `PregOK` -/

section PregOK
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] {n : ℕ} (nodes : Fin n → ZMod p)

/-- **`PregOK` at the honest table** (stage 3): rows `0 .. |ps| − 1` are the preg rows of `ps` in order, every other
row has `sP = pId = pOp = 0`; so `preLOf` evaluates at the row nodes to the accepted predicate's layout.  `hnoDec`:
the primitive table has no `dec` (disclosed registry restriction). -/
theorem pregOK_tblP (hinj : Function.Injective nodes) (pN : ℕ) (y : Quad (algebraMap (ZMod p) K δ))
    (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (cls : List CallL)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec) (hlen : (tblP δ pN y (pregsP ps vcOf mOf) cls).length ≤ n) :
    AcceptsJ9AL.PregOK nodes ps (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls)) := by
  have hpl := pregsP_length (F := ZMod p) ps vcOf mOf
  have hge := rowAt_tblP_ge δ pN y (pregsP ps vcOf mOf) cls
  refine ⟨?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · have : ps.length ≤ (tblP δ pN y (pregsP ps vcOf mOf) cls).length := by
      simp only [tblP, List.length_append, List.length_map, hpl, List.length_singleton]; omega
    omega
  · rw [preLOf_eval δ nodes hinj]
    show (rowAt δ _ i).1.sP = _
    by_cases hi : (i : ℕ) < ps.length
    · rw [rowAt_tblP_preg δ pN y ps vcOf mOf cls i hi, if_pos hi]; rfl
    · rw [if_neg hi]; exact (hge i (by rw [hpl]; omega)).1
  · rw [preLOf_eval δ nodes hinj]
    show (rowAt δ _ i).1.pId = _
    by_cases hi : (i : ℕ) < ps.length
    · rw [rowAt_tblP_preg δ pN y ps vcOf mOf cls i hi, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map]
      rfl
    · rw [List.getD_eq_default _ _ (by simp; omega)]; exact (hge i (by rw [hpl]; omega)).2.1
  · rw [preLOf_eval δ nodes hinj]
    show (rowAt δ _ i).1.pOp = _
    by_cases hi : (i : ℕ) < ps.length
    · rw [rowAt_tblP_preg δ pN y ps vcOf mOf cls i hi, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, ← opIx_succ _ (hnoDec _ (List.getElem_mem hi))]
      rfl
    · rw [List.getD_eq_default _ _ (by simp; omega)]; exact (hge i (by rw [hpl]; omega)).2.2

end PregOK

/-! ## 5. Honest acceptance at the honest preprocessing -/

section Sat
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)

/-- **Stage 1–3: the ALU chip accepts the honest trace at the honest preprocessing**, which meets `PregOK`; the block
gates are the hypothesis `hblk`, the primitive table excludes `dec` (`hnoDec`). -/
theorem aluSZChipJ9_honest_sat_preg (pN : ℕ) (y : Quad (algebraMap (ZMod p) K δ)) (ps : List (ℕ × PrimOp))
    (vcOf mOf : ℕ → ℕ) (cls : List CallL)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hblk : ∀ cl ∈ cls, BlockBaseSat (F := ZMod p) pN cl ∧ BlockIdentSat (K := K) δ pN cl)
    (hy : Quad.mk _ (chals 2) (chals 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk _ (chals (40 + 2 * t)) (chals (41 + 2 * t)) = y ^ t)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hlen : (tblP δ pN y (pregsP ps vcOf mOf) cls).length ≤ n)
    (hden : ∀ i : Fin n,
      ((rowAt δ (tblP δ pN y (pregsP ps vcOf mOf) cls) i).1.aV ≠ 0 →
        dV δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i ≠ 0) ∧
      ((rowAt δ (tblP δ pN y (pregsP ps vcOf mOf) cls) i).1.sH +
          (rowAt δ (tblP δ pN y (pregsP ps vcOf mOf) cls) i).1.sP ≠ 0 →
        dR δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i ≠ 0 ∧
          dO δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i ≠ 0) ∧
      ((rowAt δ (tblP δ pN y (pregsP ps vcOf mOf) cls) i).1.sH ≠ 0 →
        dJ δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i ≠ 0 ∧
          dX δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i ≠ 0))
    (hpV : Quad.mk _ (pubs AluSZChipJ9.pubALv) (pubs (AluSZChipJ9.pubALv + 1)) =
      ∑ i : Fin n, tV δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i)
    (hpS : Quad.mk _ (pubs AluSZChipJ9.pubALs) (pubs (AluSZChipJ9.pubALs + 1)) =
      ∑ i : Fin n, tS δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i)
    (hpX : Quad.mk _ (pubs AluSZChipJ9.pubALx) (pubs (AluSZChipJ9.pubALx + 1)) =
      ∑ i : Fin n, tX δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls) i) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs
        (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls))).rap.Satisfies
        (polyAL δ b hn nodes orbit chals pubs (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls))
          (tblP δ pN y (pregsP ps vcOf mOf) cls) (r2AL δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls))) ∧
      (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit chals pubs
        (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls))).BindsPreprocessing
        (polyAL δ b hn nodes orbit chals pubs (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls))
          (tblP δ pN y (pregsP ps vcOf mOf) cls) (r2AL δ chals (tblP δ pN y (pregsP ps vcOf mOf) cls))) ∧
      AcceptsJ9AL.PregOK nodes ps (preLOf δ nodes (tblP δ pN y (pregsP ps vcOf mOf) cls)) :=
  ⟨(aluSZChipJ9_honest_sat_tblP δ b hn nodes orbit chals pubs _ pN y _ cls (pregsP_preg ps vcOf mOf) hblk hy hyp
      hinj hadj (preLOf_hpre δ b nodes hinj _ _) hlen hden hpV hpS hpX).1,
    (aluSZChipJ9_honest_sat_tblP δ b hn nodes orbit chals pubs _ pN y _ cls (pregsP_preg ps vcOf mOf) hblk hy hyp
      hinj hadj (preLOf_hpre δ b nodes hinj _ _) hlen hden hpV hpS hpX).2,
    pregOK_tblP δ nodes hinj pN y ps vcOf mOf cls hnoDec hlen⟩

end Sat

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg
#print axioms pregOK_tblP
#print axioms aluSZChipJ9_honest_sat_preg
end Axioms
