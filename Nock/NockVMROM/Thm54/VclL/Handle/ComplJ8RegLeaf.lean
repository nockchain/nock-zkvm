import Nock.Jet.Autogen
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet

/-!
# ComplJ8RegLeaf: every leaf atom of a compiled template is `< p`

`compile p T` emits only: opcodes 0..9, the fixed library axes (at most 55), `A (p-1)`, `A 0`, `A 1`,
the template axes `T.ax i` and the template constants (`< p` by `HasTy.const`).  So for
`56 ≤ p` and `∀ i, T.ax i < p`, all leaves are `< p`.  Neither hypothesis can be dropped:
`p = 2` fails (axis 12 appears), and `WellTyped` does not bound `T.ax`.
-/
set_option autoImplicit false
namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8RegLeaf
open Nock Nock.Noun Nock.Jet.Autogen

/-- All leaves `< p`. -/
def Lt (p : ℕ) (n : Noun) : Prop := ∀ v ∈ n.leafList, v < p

theorem Lt_atom {p k : ℕ} (h : k < p) : Lt p (.atom k) := by
  intro v hv; simp [Noun.leafList] at hv; omega
theorem Lt_cell {p : ℕ} {a b : Noun} (ha : Lt p a) (hb : Lt p b) : Lt p (.cell a b) := by
  intro v hv; simp only [Noun.leafList, List.mem_append] at hv; rcases hv with h | h
  exacts [ha v h, hb v h]

section
variable {p : ℕ} (hp : 56 ≤ p)
include hp

theorem Lt_op0 {ax : ℕ} (h : ax < p) : Lt p (op0 ax) := Lt_cell (Lt_atom (by omega)) (Lt_atom h)
theorem Lt_op1 {c : Noun} (h : Lt p c) : Lt p (op1 c) := Lt_cell (Lt_atom (by omega)) h
theorem Lt_op6 {b c d : Noun} (hb : Lt p b) (hc : Lt p c) (hd : Lt p d) : Lt p (op6 b c d) :=
  Lt_cell (Lt_atom (by omega)) (Lt_cell hb (Lt_cell hc hd))
theorem Lt_op8 {c d : Noun} (h : Lt p c) (h' : Lt p d) : Lt p (op8 c d) :=
  Lt_cell (Lt_atom (by omega)) (Lt_cell h h')
theorem Lt_A {c : ℕ} (h : c < p) : Lt p (A c) := Lt_atom h

theorem Lt_LIB : Lt p (LIB p) := by
  intro v hv
  simp [LIB, isfArm, fadlArm, subcArm, fmllArm, call, A, op0, op1, op3, op4, op5, op6, op7, op8, op9,
    Noun.leafList] at hv
  omega

theorem Lt_tailF {f : Noun} (h : Lt p f) : ∀ j, Lt p (tailF j f)
  | 0 => h
  | j + 1 => Lt_cell (Lt_atom (by omega)) (Lt_cell (Lt_tailF h j) (Lt_cell (Lt_atom (by omega)) (Lt_atom (by omega))))

theorem Lt_cEx {k : ℕ} (ax : Fin k → ℕ) (hax : ∀ i, ax i < p) {inTy : Fin k → Ty} {e : Ex k} {t : Ty}
    (h : HasTy p inTy e t) : Lt p (cEx ax e) := by
  induction h with
  | var i =>
    intro v hv
    simp [cEx, op0, op7, Noun.leafList] at hv
    have := hax i
    omega
  | const hc =>
    intro v hv
    simp [cEx, op1, A, Noun.leafList] at hv
    omega
  | nil τ =>
    intro v hv
    simp [cEx, op1, A, Noun.leafList] at hv
    omega
  | weakN _ ih => exact ih
  | add _ _ ih1 ih2 =>
    intro v hv
    simp [cEx, call, A, op0, op1, op9, Noun.leafList] at hv
    rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> first | omega | exact ih1 v h | exact ih2 v h
  | mul _ _ ih1 ih2 =>
    intro v hv
    simp [cEx, call, A, op0, op1, op9, Noun.leafList] at hv
    rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> first | omega | exact ih1 v h | exact ih2 v h
  | nth _ _ ih =>
    intro v hv
    simp only [cEx, op0, op7] at hv
    exact Lt_cell (Lt_atom (by omega)) (Lt_cell (Lt_tailF hp ih _) (Lt_cell (Lt_atom (by omega)) (Lt_atom (by omega)))) v hv
  | pair _ _ ih1 ih2 => exact Lt_cell ih1 ih2

theorem Lt_gL {g : Noun → Noun} (hg : ∀ f, Lt p f → Lt p (g f)) :
    ∀ (n : ℕ) (f : Noun), Lt p f → Lt p (gL g n f)
  | 0, f, h => by
    intro v hv; simp [gL, op5, op1, A, Noun.leafList] at hv
    rcases hv with hv|hv|hv|hv <;> first | omega | exact h v hv
  | n + 1, f, h => by
    have ih := Lt_gL hg n (op7 f (op0 3)) (by
      intro v hv; simp [op7, op0, Noun.leafList] at hv
      rcases hv with hv|hv|hv|hv <;> first | omega | exact h v hv)
    have hg' := hg (op7 f (op0 2)) (by
      intro v hv; simp [op7, op0, Noun.leafList] at hv
      rcases hv with hv|hv|hv|hv <;> first | omega | exact h v hv)
    have hf : Lt p (op3 f) := by
      intro v hv; simp [op3, Noun.leafList] at hv
      rcases hv with hv|hv <;> first | omega | exact h v hv
    have a1 : Lt p (op1 (A 1)) := Lt_op1 hp (Lt_A hp (by omega))
    exact Lt_op6 hp hf (Lt_op6 hp hg' ih a1) a1

theorem Lt_gTy (T : Ty) : ∀ f, Lt p f → Lt p (gTy p T f) := by
  induction T with
  | F =>
    intro f h v hv
    simp [gTy, call, A, op0, op1, op3, op4, op6, op9, Noun.leafList] at hv
    rcases hv with hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv <;> first | omega | exact h v hv
  | L n τ ih => intro f h; exact Lt_gL hp ih n f h
  | N =>
    intro f h
    have hf : Lt p (op3 f) := by
      intro v hv; simp [op3, Noun.leafList] at hv
      rcases hv with hv|hv <;> first | omega | exact h v hv
    have a0 : Lt p (op1 (A 0)) := Lt_op1 hp (Lt_A hp (by omega))
    exact Lt_op6 hp hf a0 a0

theorem Lt_compile (T : Tpl) (hax : ∀ i, T.ax i < p) (hT : T.WellTyped p) :
    Lt p (compile p T) := by
  have hb := Lt_cEx hp T.ax hax hT
  have hg : ∀ l : List (Fin T.k), Lt p (guardAll p T l) := by
    intro l
    induction l with
    | nil => exact Lt_op1 hp (Lt_A hp (by omega))
    | cons i l ih =>
      have hi := Lt_gTy hp (T.inTy i) _ (Lt_cEx hp T.ax hax (inTy := T.inTy) (HasTy.var i))
      cases l with
      | nil => simpa [guardAll] using hi
      | cons j l =>
        simp only [guardAll]
        exact Lt_op6 hp hi ih (Lt_op1 hp (Lt_A hp (by omega)))
  unfold compile
  exact Lt_op8 hp (Lt_op1 hp (Lt_LIB hp))
    (Lt_op6 hp (hg _) hb (Lt_op0 hp (by omega)))

end

/-- **`compile_leaves_lt`**: every leaf of a compiled well-typed template is `< p`. -/
theorem compile_leaves_lt {p : ℕ} (hp : 56 ≤ p) (T : Tpl) (hT : T.WellTyped p)
    (hax : ∀ i, T.ax i < p) : ∀ v ∈ (compile p T).leafList, v < p :=
  Lt_compile hp T hax hT

/-- Registry form. -/
theorem compile_leaves_lt_reg {p : ℕ} (hp : 56 ≤ p) (Rt : ℕ → Tpl) (regs : List ℕ)
    (hT : ∀ id ∈ regs, (Rt id).WellTyped p) (hax : ∀ id ∈ regs, ∀ i, (Rt id).ax i < p) :
    ∀ id ∈ regs, ∀ v ∈ (compile p (Rt id)).leafList, v < p :=
  fun id hid => compile_leaves_lt hp (Rt id) (hT id hid) (hax id hid)

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8RegLeaf
