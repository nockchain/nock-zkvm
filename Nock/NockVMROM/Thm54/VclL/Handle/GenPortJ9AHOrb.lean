/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrb.lean

-/
import Nock.V1J9A.GenJ9AX
import Nock.V1J9A.CheckJ9AIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A

/-! ## 1. `hOf` -/

theorem hOf_go_ge (n : ℕ) : ∀ k h, n ≤ 3 * 2 ^ (h + k) → h ≤ hOf.go n k h ∧ n ≤ 3 * 2 ^ hOf.go n k h := by
  intro k
  induction k with
  | zero => intro h hn; exact ⟨le_refl _, by simpa [hOf.go] using hn⟩
  | succ k ih =>
    intro h hn
    unfold hOf.go
    by_cases hc : n ≤ 3 * 2 ^ h
    · rw [if_pos hc]; exact ⟨le_refl _, hc⟩
    · rw [if_neg hc]
      have := ih (h + 1) (by rw [show h + 1 + k = h + (k + 1) by omega]; exact hn)
      exact ⟨by omega, this.2⟩

theorem hOf_go_le (n B : ℕ) (hB : n ≤ 3 * 2 ^ B) : ∀ k h, h ≤ B → hOf.go n k h ≤ B := by
  intro k
  induction k with
  | zero => intro h hh; simpa [hOf.go] using hh
  | succ k ih =>
    intro h hh
    unfold hOf.go
    by_cases hc : n ≤ 3 * 2 ^ h
    · rw [if_pos hc]; exact hh
    · rw [if_neg hc]
      have : h < B := by
        by_contra hlt
        have : h = B := by omega
        subst this; exact hc hB
      exact ih (h + 1) (by omega)

/-- `hOf`: at least `1`, covers `n` (for `n ≤ 2^31`), and stays `≤ 32`. -/
theorem hOf_spec (n : ℕ) (hn : n ≤ 2 ^ 31) :
    1 ≤ hOf n ∧ n ≤ 3 * 2 ^ hOf n ∧ hOf n ≤ 32 := by
  have h32 : n ≤ 3 * 2 ^ 32 := by
    have : (2 : ℕ) ^ 31 ≤ 3 * 2 ^ 32 := by norm_num
    omega
  have h65 : n ≤ 3 * 2 ^ (1 + 64) := by
    have : (3 * 2 ^ 32 : ℕ) ≤ 3 * 2 ^ (1 + 64) := by
      apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have a := hOf_go_ge n 64 1 h65
  exact ⟨a.1, a.2, hOf_go_le n 32 h32 64 1 (by norm_num)⟩

/-! ## 2. The generator's order -/

/-- **One kernel evaluation**: `ωOf h` has exact order `3·2^h` (checked by repeated squaring) for `h = 1 … 32`. -/
theorem ordOK_ωOf_all : (List.range 32).all (fun i => ordOK (ωOf (i + 1)) (i + 1)) = true := by
  decide +kernel

theorem ordOK_ωOf (h : ℕ) (h1 : 1 ≤ h) (h32 : h ≤ 32) : ordOK (ωOf h) h = true := by
  have := List.all_eq_true.mp ordOK_ωOf_all (h - 1) (List.mem_range.mpr (by omega))
  have e : h - 1 + 1 = h := by omega
  rwa [e] at this

/-! ## 3. `chipOf` -/

theorem orbOK_chipOf (tbl : Array (Array (ZMod P))) (hs : tbl.size ≤ 2 ^ 31) : OrbOK (chipOf tbl) := by
  obtain ⟨h1, -, h32⟩ := hOf_spec tbl.size hs
  rw [← orbB_iff]
  unfold orbB
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h1, ordOK_ωOf _ h1 h32⟩

theorem chipOf_n_le (tbl : Array (Array (ZMod P))) (hs : tbl.size ≤ 2 ^ 31) :
    (chipOf tbl).n ≤ 3 * 2 ^ (chipOf tbl).h :=
  (hOf_spec tbl.size hs).2.1

/-! ## 4. Nodes -/

/-- Row nodes of an admissible chip with `n ≤ 3·2^h` rows are pairwise distinct. -/
theorem nodesOf_inj (q : ChipIn) (ho : OrbOK q) (hn : q.n ≤ 3 * 2 ^ q.h) : Function.Injective (nodesOf q) := by
  intro i j hij
  rw [nodesOf_eq, nodesOf_eq] at hij
  have hi := pow_injOn_Iio_orderOf (x := q.ω.toZ)
  have h := hi (Set.mem_Iio.mpr (by rw [ho.ord]; exact lt_of_lt_of_le i.2 hn))
    (Set.mem_Iio.mpr (by rw [ho.ord]; exact lt_of_lt_of_le j.2 hn)) hij
  exact Fin.ext h

theorem nodesOf_adj (q : ChipIn) :
    ∀ i : Fin q.n, ∀ hi : (i : ℕ) + 1 < q.n, nodesOf q ⟨i + 1, hi⟩ = q.ω.toZ * nodesOf q i := by
  intro i hi
  rw [nodesOf_eq, nodesOf_eq]; simp [pow_succ, mul_comm]

theorem nodesOf_chipOf_inj (tbl : Array (Array (ZMod P))) (hs : tbl.size ≤ 2 ^ 31) :
    Function.Injective (nodesOf (chipOf tbl)) :=
  nodesOf_inj _ (orbOK_chipOf tbl hs) (chipOf_n_le tbl hs)

/-! ## 5. `ValidJ9A` -/

/-- The absent J chip `⟨1, 0, ω6g, _⟩` is admissible. -/
theorem orbOK_J0 (f : ℕ → Fin 0 → ZMod p) : OrbOK (⟨1, 0, Example.ω6g, f⟩ : ChipIn) := by
  have := ordOK_ωOf 1 le_rfl (by norm_num)
  rw [show ωOf 1 = Example.ω6g from rfl] at this
  exact ⟨le_rfl, (ordOK_iff _ _ le_rfl).mp this⟩

/-- **`ValidJ9A`** for an input whose chips are `chipOf` tables (all non-empty, `≤ 2^31` rows), J absent. -/
theorem validJ9A_of_chips (I : InJ9A)
    (tX tC tW tA tV tAX tSP : Array (Array (ZMod P)))
    (hX : I.X = chipOf tX) (hC : I.C = chipOf tC) (hW : I.W = chipOf tW) (hA : I.A = chipOf tA)
    (hV : I.V = chipOf tV) (hAX : I.AX = chipOf tAX) (hSP : I.SP = chipOf tSP)
    (hJ : I.J = ⟨1, 0, Example.ω6g, fun _ => Fin.elim0⟩)
    (nX : 0 < tX.size) (nC : 0 < tC.size) (nW : 0 < tW.size) (nA : 0 < tA.size) (nV : 0 < tV.size)
    (nAX : 0 < tAX.size) (nSP : 0 < tSP.size)
    (sX : tX.size ≤ 2 ^ 31) (sC : tC.size ≤ 2 ^ 31) (sW : tW.size ≤ 2 ^ 31) (sA : tA.size ≤ 2 ^ 31)
    (sV : tV.size ≤ 2 ^ 31) (sAX : tAX.size ≤ 2 ^ 31) (sSP : tSP.size ≤ 2 ^ 31) :
    ValidJ9A I := by
  have e : ∀ t : Array (Array (ZMod P)), (chipOf t).n = t.size := fun _ => rfl
  refine ValidJ9A.mk' I ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
  · show 0 < I.X.n; rw [hX, e]; exact nX
  · show 0 < I.C.n; rw [hC, e]; exact nC
  · show 0 < I.W.n; rw [hW, e]; exact nW
  · show 0 < I.A.n; rw [hA, e]; exact nA
  · show 0 < I.V.n; rw [hV, e]; exact nV
  · show OrbOK I.X; rw [hX]; exact orbOK_chipOf _ sX
  · show OrbOK I.C; rw [hC]; exact orbOK_chipOf _ sC
  · show OrbOK I.W; rw [hW]; exact orbOK_chipOf _ sW
  · show OrbOK I.J; rw [hJ]; exact orbOK_J0 _
  · show OrbOK I.A; rw [hA]; exact orbOK_chipOf _ sA
  · show OrbOK I.V; rw [hV]; exact orbOK_chipOf _ sV
  · show 0 < I.AX.n; rw [hAX, e]; exact nAX
  · show OrbOK I.AX; rw [hAX]; exact orbOK_chipOf _ sAX
  · show 0 < I.SP.n; rw [hSP, e]; exact nSP
  · show OrbOK I.SP; rw [hSP]; exact orbOK_chipOf _ sSP

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms hOf_spec
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms ordOK_ωOf
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms orbOK_chipOf
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms nodesOf_inj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms nodesOf_adj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb in
#print axioms validJ9A_of_chips
