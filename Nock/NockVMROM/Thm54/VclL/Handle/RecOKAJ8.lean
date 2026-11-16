/-
  Nock/NockVMROM/Thm54/VclL/Handle/RecOKAJ8.lean

  New module, additive (twins only; `RowSemChipX`, `WalkBridgeJ8`, `AcceptJ8` are not edited).

  The twin obligation here:

  * **`WalkAOK D comb`**: a `walkRecA` record `(rv, ax, lk, lv)` (`.s`, 4 entries) is genuine when
    `D (2, rv) = atom n`, `lk = 0 → /[ax] (comb n) = atom lv` (a limb child, a function of `n`) and
    `lk = 1 → /[ax] (comb n)` is a cell (a comb node: only its shape, never its row); other kinds are never
    consumed (the compute's `xL1.k`, `xL2.k` are boolean).  `comb` is the
    canonical limb comb (instantiated in `AtomCombJ8`).
  * **`RecOKA D R comb`**: `WalkAOK` on `walkRecA`-shaped records, `RecOK` (any `limbA`) elsewhere
    (`recOK_congr`: off that shape `RecOK` does not read `limbA`).
  * **The mixed `differ_leaves` cases, re-proved** (`walkA_consistent`): on a row, the two `walkRecA` records
    (the op 5 α pair, the only `walkRecA`-shaped consumes, `walkA_mem`; boolean kinds) at a common value `n`
    and common axis are both limbs (then equal), or one limb and one node (`atom ≠ cell`: impossible), or both nodes
    (excluded by the gate `pr2·k₁·k₂ = 0`, `pr2_gate`).  Hence a per-row `limbA` exists
    (`exists_limbA_row`) and the row semantics apply unchanged: **`rowSemX_of_chipA`**, `differ_leavesA`.
  * Re-threading: `RowsAccXA`, `halving_of_treeA`, `holdsN_of_walkJ8A`, `acceptsJ8_holdsN_computeA` (the
    proofs of the originals, the per-row step through `rowSemX_of_chipA`); provider transfer
    `provPA_of_provOK` / `provOK_of_provPA` (`.x`, `.p`) and `provPA_of_forall` (a provider whose obligation
    holds at EVERY `limbA`: its keys never take the `walkRecA` shape).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8

open Nock Nock.Reified Nock.Edit Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC prodL)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The twin obligation -/

def WalkAOK (D : HX → Option Noun) (comb : ℕ → Noun) : List ℕ → Prop
  | [rv, ax, lk, lv] => ∃ n, D (2, rv) = some (.atom n) ∧
      (lk = 0 → Noun.slot ax (comb n) = some (.atom lv)) ∧
        (lk = 1 → ∃ a c, Noun.slot ax (comb n) = some (.cell a c))
  | _ => True

/-- The `walkRecA` shape: a 4-entry record of the service balance. -/
def IsWalkA (r : List ℕ × Bal) : Prop := r.2 = .s ∧ r.1.length = 4

instance (r : List ℕ × Bal) : Decidable (IsWalkA r) := by unfold IsWalkA; infer_instance

/-- **The twin of `RecOK`**: `WalkAOK` on `walkRecA`-shaped records, `RecOK` elsewhere. -/
def RecOKA (D : HX → Option Noun) (R : Nock.Jet.Registry) (comb : ℕ → Noun) (r : List ℕ × Bal) : Prop :=
  if IsWalkA r then WalkAOK D comb r.1 else RecOK D R (fun _ _ => (0, 0)) r

/-- Off the `walkRecA` shape, `RecOK` does not read `limbA`. -/
theorem recOK_congr {D : HX → Option Noun} {R : Nock.Jet.Registry} {l1 l2 : ℕ → ℕ → HX} {r : List ℕ × Bal}
    (h : ¬ IsWalkA r) (hr : RecOK D R l1 r) : RecOK D R l2 r := by
  obtain ⟨l, bl⟩ := r
  unfold IsWalkA at h
  unfold RecOK at hr ⊢
  split at hr <;> simp_all

theorem recOKA_iff_off {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    {limbA : ℕ → ℕ → HX} {r : List ℕ × Bal} (h : ¬ IsWalkA r) : RecOKA D R comb r ↔ RecOK D R limbA r := by
  unfold RecOKA; rw [if_neg h]
  exact ⟨recOK_congr h, recOK_congr h⟩

theorem recOKA_walk {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun} {r : List ℕ × Bal}
    (h : IsWalkA r) : RecOKA D R comb r ↔ WalkAOK D comb r.1 := by
  unfold RecOKA; rw [if_pos h]

section Prov
variable {K : Type} [Field K] [Algebra (ZMod p) K]
  {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}

/-- **Provider transfer off the service balance** (`.x`, `.p`: no `walkRecA` shape). -/
theorem provPA_of_provOK {limbA : ℕ → ℕ → HX} {bl : Bal} (hbl : bl ≠ .s)
    {provs : List ((Fin (mOf bl) → K) × K)} (h : ProvOK (p := p) (K := K) D R limbA bl provs) :
    ProvP (p := p) (K := K) (RecOKA D R comb) bl provs := by
  intro q hq l hl hlt hk
  have hw : ¬ IsWalkA (l, bl) := fun hw => hbl hw.1
  exact (recOKA_iff_off hw).mpr (h q hq l hl hlt hk)

theorem provOK_of_provPA {limbA : ℕ → ℕ → HX} {bl : Bal} (hbl : bl ≠ .s)
    {provs : List ((Fin (mOf bl) → K) × K)} (h : ProvP (p := p) (K := K) (RecOKA D R comb) bl provs) :
    ProvOK (p := p) (K := K) D R limbA bl provs := by
  intro q hq l hl hlt hk
  have hw : ¬ IsWalkA (l, bl) := fun hw => hbl hw.1
  exact (recOKA_iff_off hw).mp (h q hq l hl hlt hk)

/-- **A provider whose `RecOK` obligation holds at EVERY `limbA`** meets `RecOKA`: a `walkRecA`-shaped key
`[a, b, c, d]` would give `limbA n b = (c, d)` at `limbA := fun _ _ => (c + 1, d)`. -/
theorem provPA_of_forall {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ∀ limbA : ℕ → ℕ → HX, ProvOK (p := p) (K := K) D R limbA bl provs) :
    ProvP (p := p) (K := K) (RecOKA D R comb) bl provs := by
  intro q hq l hl hlt hk
  by_cases hw : IsWalkA (l, bl)
  · exfalso
    obtain ⟨hs, h4⟩ := hw
    simp only at hs h4
    subst hs
    match l, h4 with
    | [a, b, c, d], _ =>
      have := h (fun _ _ => (c + 1, d)) q hq [a, b, c, d] hl hlt hk
      simp only [RecOK, Prod.mk.injEq] at this
      obtain ⟨_, _, h1, _⟩ := this
      omega
  · exact (recOKA_iff_off hw).mpr (h (fun _ _ => (0, 0)) q hq l hl hlt hk)

end Prov

/-! ## 2. One row: the only `walkRecA` consumes are the α pair; the mixed cases -/

section Row
variable {env : Env (ZMod p)} {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}

theorem ents_not_walkA :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ x ∈ S.ents, ¬ (x.bal = Bal.s ∧ x.rcd.length = 4) := by
  simp [ChipHX.slotsX, slot0X, slot1X, slot2X, slot3X, cellRecX, walkRecX, incRecX, jetRecX, recOf,
    ChipH.cellRec, ChipH.walkRec]

/-- **The `walkRecA`-shaped records a row consumes are the α pair** (slot 3's pair under `pr2`). -/
theorem walkA_mem {r : List ℕ × Bal} (hr : r ∈ activeX env) (hw : IsWalkA r) :
    env.trace pr2X = 1 ∧ (r = ((walkRecAX xFtth xL1).map (reVal env), .s) ∨
      r = ((walkRecAX xFttt xL2).map (reVal env), .s)) := by
  obtain ⟨hs, hl⟩ := hw
  obtain ⟨S, hS, hr⟩ := List.mem_flatMap.mp hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact absurd ⟨hs, by simpa using hl⟩ (ents_not_walkA S hS x (List.mem_filter.mp hx).1)
  · simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl
    · simp [pairRecsX, slot0X] at h
    · simp [pairRecsX, slot1X] at h
    · simp only [pairRecsX, slot2X] at h
      split_ifs at h
      · exfalso; rcases List.mem_pair.mp h with rfl | rfl <;> simp at hs
      · simp at h
    · simp only [pairRecsX, slot3X] at h
      split_ifs at h with h2
      · exact ⟨h2, by simpa using h⟩
      · simp at h

/-- The α pair gate `pr2·k₁·k₂ = 0` (every row). -/
theorem pr2_gate (hB : BaseHoldsX env) : env.trace pr2X * env.trace xL1.k * env.trace xL2.k = 0 := by
  have aK := arith_of_base hB (op5G_sub _ (by simp [op5G] :
    (prodL [cc pr2X, cc xL1.k, cc xL2.k] : CoeffExpr ℚ) ∈ op5G))
  simpa [prodL, cc, evalQX, mul_assoc] using aK

/-- **The mixed cases of `differ_leaves`, re-proved at the weakened clause**: two `walkRecA` records reading
the same comb position `X`, not both nodes, carry the same child (both limbs: the comb's limb; limb vs node:
`atom ≠ cell`). -/
theorem walkA_consistent {X : Option Noun} {k1 v1 k2 v2 : ℕ} (hk1 : k1 = 0 ∨ k1 = 1) (hk2 : k2 = 0 ∨ k2 = 1)
    (hkk : ¬ (k1 = 1 ∧ k2 = 1))
    (h1 : (k1 = 0 → X = some (.atom v1)) ∧ (k1 = 1 → ∃ a c, X = some (.cell a c)))
    (h2 : (k2 = 0 → X = some (.atom v2)) ∧ (k2 = 1 → ∃ a c, X = some (.cell a c))) :
    (k1, v1) = (k2, v2) := by
  rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl
  · rw [h1.1 rfl] at h2; have e2 := h2.1 rfl; simp only [Option.some.injEq, Noun.atom.injEq] at e2; rw [e2]
  · obtain ⟨a, c, e2⟩ := h2.2 rfl; rw [h1.1 rfl] at e2; simp at e2
  · obtain ⟨a, c, e1⟩ := h1.2 rfl; rw [h2.1 rfl] at e1; simp at e1
  · exact absurd ⟨rfl, rfl⟩ hkk

/-- **A per-row `limbA`**: at a row whose consumed records meet `RecOKA`, some `limbA` makes every consumed
record meet `RecOK` (the two pair records agree when their roots denote the same value, by
`walkA_consistent` and the gate). -/
theorem exists_limbA_row (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOKA D R comb r) :
    ∃ limbA : ℕ → ℕ → HX, ∀ r ∈ activeX env, RecOK D R limbA r := by
  classical
  let limbA : ℕ → ℕ → HX := fun n _ =>
    if D (2, (env.trace xFtth.v).val) = some (.atom n) then ((env.trace xL1.k).val, (env.trace xL1.v).val)
    else ((env.trace xL2.k).val, (env.trace xL2.v).val)
  refine ⟨limbA, fun r hr => ?_⟩
  by_cases hw : IsWalkA r
  · obtain ⟨h2, hr12⟩ := walkA_mem hr hw
    have hpm := pair_mem (env := env) (S := slot3X) (fl := pr2X) (a := walkRecAX xFtth xL1)
      (b := walkRecAX xFttt xL2) (bl := .s) (by simp [ChipHX.slotsX]) rfl h2
    have w1 := (recOKA_walk (D := D) (R := R) (comb := comb) (show IsWalkA
      ((walkRecAX xFtth xL1).map (reVal env), .s) from ⟨rfl, rfl⟩)).mp (hOK _ hpm.1)
    have w2 := (recOKA_walk (D := D) (R := R) (comb := comb) (show IsWalkA
      ((walkRecAX xFttt xL2).map (reVal env), .s) from ⟨rfl, rfl⟩)).mp (hOK _ hpm.2)
    simp only [walkRecAX, List.map_cons, List.map_nil, reVal, WalkAOK] at w1 w2
    obtain ⟨n1, hn1, c1⟩ := w1
    obtain ⟨n2, hn2, c2⟩ := w2
    rcases hr12 with rfl | rfl
    · simp only [walkRecAX, List.map_cons, List.map_nil, reVal, RecOK]
      exact ⟨n1, hn1, by simp only [limbA, if_pos hn1]⟩
    · simp only [walkRecAX, List.map_cons, List.map_nil, reVal, RecOK]
      refine ⟨n2, hn2, ?_⟩
      simp only [limbA]
      split_ifs with hc
      · rw [hc] at hn1
        have hn : n2 = n1 := by simpa using hn1
        subst hn
        have hkk : ¬ ((env.trace xL1.k).val = 1 ∧ (env.trace xL2.k).val = 1) := by
          rintro ⟨e1, e2⟩
          have g := pr2_gate hB
          rw [h2, ZMod.val_injective p (e1.trans val_one'.symm),
            ZMod.val_injective p (e2.trans val_one'.symm)] at g
          simp at g
        have kb : ∀ x : ZMod p, (x = 0 ∨ x = 1) → (x.val = 0 ∨ x.val = 1) := by
          rintro x (rfl | rfl)
          · left; simp
          · right; exact val_one'
        exact walkA_consistent (kb _ (col_bool hB (i := xL1.k) (by simp [oneHotG])))
          (kb _ (col_bool hB (i := xL2.k) (by simp [oneHotG]))) hkk c1 c2
      · rfl
  · exact (recOKA_iff_off hw).mp (hOK r hr)

theorem rowSemX_of_chipA (hD : DenOKX p D) (hp : 17 < p) (hB : BaseHoldsX env) (st : StateX)
    (hOH : OneHotAt env (stIdx st)) (hOK : ∀ r ∈ activeX env, RecOKA D R comb r)
    (hv : HalvingOK env st) : RowSemX p D R (rowOfX env st) := by
  obtain ⟨limbA, h⟩ := exists_limbA_row hB hOK
  exact rowSemX_of_chip hD hp hB st hOH h hv

/-- **`differ_leaves` at the twin obligation** (the op 5 "≠" first-difference leaves differ). -/
theorem differ_leavesA (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOKA D R comb r)
    (hp : 17 < p) (h5 : env.trace 5 = 1) (hβ : env.trace betaX = 1) :
    DifferX p D (hdV env xFtth) (hdV env xFttt) := by
  obtain ⟨limbA, h⟩ := exists_limbA_row hB hOK
  exact differ_leaves hB h hp h5 hβ

end Row

/-! ## 3. The tree and the compute half, re-threaded -/

section Tree
open Nock.Walk Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8 (halvingOK_of_child)
variable {K : Type} [Field K]

structure RowsAccXA (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (D : HX → Option Noun)
    (R : Nock.Jet.Registry) (comb : ℕ → Noun) : Prop where
  base : ∀ r < n, BaseHoldsX (E r)
  oh : ∀ r < n, OneHotAt (E r) (stIdx (st r))
  served : ∀ r < n, ∀ x ∈ activeX (E r), RecOKA D R comb x
  ax : ∀ r < n, st r = .s10L → 2 ≤ ((E r).trace xM.v).val ∧ ((E r).trace xM.v).val < 2 ^ 62

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun}
  {R : Nock.Jet.Registry} {comb : ℕ → Noun}

/-- **`HalvingOK` at every `s10L` node of the walk tree**: the node's one child carries the chip
child label `(s, (0, v), e)`, the child is some row (label link `xF = (0, v)`), and
`halvingOK_of_child` applies. -/
theorem halving_of_treeA (hp : 2 ^ 63 + 1 < p) (A : RowsAccXA n E st D R comb)
    {t : NTree (StateX × RowVSX)}
    (hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i)
    (hlink : ∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX u.label.2)
    {u : NTree (StateX × RowVSX)} (hu : InTree t u) {i : ℕ} (hui : u.label = lblOf (rowsWX E st) i)
    (hs : st (i - 1) = .s10L) : HalvingOK (E (i - 1)) .s10L := by
  have hl := hlink u hu
  rw [hui] at hl
  simp only [lblOf, rowsWX, hs, kidsX_rowW_s10L] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_map, List.length_cons, List.length_nil] at hlen
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  rw [hc] at hl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  have hcin : InTree t c := inTree_trans hu (InTree.sub (by rw [hc]; simp) (InTree.here _))
  obtain ⟨j, hj1, hjn, hcj⟩ := hrow c hcin
  rw [hcj] at hl
  simp only [lblOf, rowsWX] at hl
  rw [rowW_trip] at hl
  simp only [rowOfX, RowVSX.trip, hdV, Prod.mk.injEq] at hl
  obtain ⟨-, ⟨hk, hv⟩, -⟩ := hl
  exact halvingOK_of_child hp (A.base _ (by omega)) (A.oh _ (by omega)) (ZMod.val_eq_zero _ |>.mp hk)
    (ZMod.val_injective _ hv) (A.ax _ (by omega))

/-- **J-8a step 1 + step 3 (halving part) composed**: an accepted compute walk (`ForestReconGoal` over
the walk-decoded rows `rowsWX`, i.e. outside `cwEvent` with `cwalkX_sat`'s facts) whose rows satisfy
`RowsAccX` and whose root is a real row denoting the claim proves `HoldsN` of the claim.  No
`HalvingOK` hypothesis: it is derived from the tree (`halving_of_tree`). -/
theorem holdsN_of_walkJ8A [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D)
    (hn : 1 ≤ n) (A : RowsAccXA n E st D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hreal : (st 0).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨t, hroot, hrow, hlink⟩ :=
    tree_of_goal (K := K) p hp0 (rowsWX E st) hn (fun i _ _ => smallR_rowW _ _) hG
  let rw : StateX × RowVSX → RowVSX := fun l =>
    if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf (rowsWX E st) i then
      rowOfX (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      rw u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    have h := hrow u hu
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [rw, dif_pos h]⟩
  have hrt : rw t.label = rowOfX (E 0) (st 0) := by
    have h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t.label = lblOf (rowsWX E st) i := ⟨1, le_rfl, hn, hroot⟩
    have h1 : Nat.find h = 1 := le_antisymm (Nat.find_min' h ⟨le_rfl, hn, hroot⟩) (Nat.find_spec h).1
    simp only [rw, dif_pos h, h1]
  have hok : RowsOKX rw p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      rw [hrw]
      exact rowSemX_of_chipA hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
        (A.served _ (by omega)) (fun hs => halving_of_treeA hp A hrow hlink hu hui hs rfl)
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (rw c.label).trip) = u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_treeA hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]
  exact holdsN_of_rowsVSX rw hR hD t hok (by rw [hrt]; exact hreal) x (by rw [hrt]; exact hs)
    (by rw [hrt]; exact hf) (by rw [hrt]; exact he)

end Tree


section Accept
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8 (bctx_of_xctx goalJ8)
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P
local notation "CV" => coinsCV b δ chalV

/-- **`AcceptJ8.acceptsJ8_holdsN_compute` at the twin obligation**: the same composition, with the provider
obligation `hprov : ProvP (RecOKA D R comb)` in place of `ProvOK D R limbA`. -/
theorem acceptsJ8_holdsN_computeA [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hR : R.Faithful) (hD : DenOKX p D)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (hprov : ∀ bl, ProvP (p := p) (K := K) (RecOKA D R comb) bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX (EN 0)).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN 0) xS) = some x.subject) (hf : D (hdV (EN 0) xF) = some x.formula)
    (he : D (hdV (EN 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  have hp4 : 4 < p := by omega
  have B := bctx_of_xctx C
  have hOK := servedP_of_balancesJ8 B hp4 hbal hout hcount hprov
  have hAx := servedP_of_balancesJ8 B hp4 hbal hout hcount haxP
  obtain ⟨hbase, hoh⟩ := base_oh_of_sat C
  have A : RowsAccXA n (fun r => EN r) (fun r => stX (EN r)) D R comb :=
    { base := hbase
      oh := hoh
      served := hOK
      ax := fun r hr hst => by
        have h12 := hoh r hr
        rw [hst] at h12
        exact ax_of_axOK (hbase r hr) h12 (hAx r hr) }
  exact holdsN_of_walkJ8A (K := K) hp hR hD hn A (goalJ8 C hseed hα hw) hreal x hs hf he

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
