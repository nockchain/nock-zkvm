/-
  NockvmE2E/Emit/TieR.lean

  A memory-linear form of the list decoder.  `decTableL` appends `l ++ [v]` at every step; the kernel `decide` of
  `decodeDagL` on an emitted chip was OOM-killed at 20 GB.  `decTableR` conses onto a
  reversed table with a counter instead (lookup `i` is `lr[n-1-i]`); `decodeDagR_eq` proves it equal to `decodeDagL` generically,
  so `decodeDagR d = some g` (by `decide +kernel`) gives the hypothesis of `evalDagK_toEx_of_decodeDag`.
-/
import NockvmE2E.Emit.Tie

set_option autoImplicit false

namespace NockvmE2E.Emit
open Nock.Emit

def stepL (l : List Val) (j : JExpr) : Option (List Val) :=
  (decStepG (fun i => l[i]?) j).map fun v => l ++ [v]

theorem decTableL_eq (defs : List JExpr) : decTableL defs = defs.foldlM stepL [] := rfl

def lkR (lr : List Val) (n : ℕ) (i : ℕ) : Option Val := if i < n then lr[n - 1 - i]? else none

def stepR (st : List Val × ℕ) (j : JExpr) : Option (List Val × ℕ) :=
  (decStepG (lkR st.1 st.2) j).map fun v => (v :: st.1, st.2 + 1)

def decTableR (defs : List JExpr) : Option (List Val × ℕ) := defs.foldlM stepR ([], 0)

theorem lkR_eq (lr : List Val) (i : ℕ) : lkR lr lr.length i = lr.reverse[i]? := by
  unfold lkR
  by_cases h : i < lr.length
  · rw [if_pos h, List.getElem?_reverse h]
  · rw [if_neg h]
    symm
    exact List.getElem?_eq_none (by simpa using (not_lt.mp h))

theorem decTableR_eq (defs : List JExpr) : ∀ lr : List Val,
    (defs.foldlM stepR (lr, lr.length)).map (fun s => s.1.reverse) = defs.foldlM stepL lr.reverse := by
  induction defs with
  | nil => intro lr; simp
  | cons j rest ih =>
    intro lr
    rw [List.foldlM_cons, List.foldlM_cons]
    have hs : decStepG (lkR lr lr.length) j = decStepG (fun i => lr.reverse[i]?) j := by
      congr 1; funext i; exact lkR_eq lr i
    cases hd : decStepG (fun i => lr.reverse[i]?) j with
    | none => simp [stepR, stepL, hs, hd]
    | some v =>
      simp only [stepR, stepL, hs, hd, Option.map_some, Option.bind_some]
      have := ih (v :: lr)
      simpa [List.reverse_cons] using this

def decodeRoots (d : DagGates) (tab : List Val) : Option DGatesDec :=
  match d.base.mapM (decBL tab), d.ext.mapM (decML tab), d.mixed.mapM (decML tab),
        d.ext1.mapM (decML tab), d.ext3.mapM (decML tab), d.eqc.mapM (decBL tab) with
  | some a, some b, some c, some e, some f, some g => some ⟨a, b, c, e, f, g⟩
  | _, _, _, _, _, _ => none

theorem decodeDagL_eq (d : DagGates) : decodeDagL d = (decTableL d.defs).bind (decodeRoots d) := by
  unfold decodeDagL decodeRoots
  cases decTableL d.defs <;> rfl

def decodeDagR (d : DagGates) : Option DGatesDec :=
  (decTableR d.defs).bind fun s => decodeRoots d s.1.reverse

theorem decodeDagR_eq (d : DagGates) : decodeDagR d = decodeDagL d := by
  rw [decodeDagL_eq, decTableL_eq]
  have h := decTableR_eq d.defs []
  simp only [List.length_nil, List.reverse_nil] at h
  unfold decodeDagR decTableR
  cases hr : d.defs.foldlM stepR ([], 0) with
  | none => simp [hr] at h; simp [← h]
  | some s => simp [hr] at h; simp [← h]

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.decodeDagR_eq
