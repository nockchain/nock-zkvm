/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/ClaimSizesP1.lean

 **The statement side of `UniqueCloseP1.trace_unique_closed`: the run, `noPathReads` and the sizes as functions of
 the claim.**

 * §1 registry independence (`genX_reg_indep`): on the fragment `P1Frag` (no op 11) `genX R fuel s f` does not
 read `R`. Fuel stability (`genX_fuel`): a run of a fragment formula at any fuel is the run at every fuel
 `≥ fz f` (the formula size). `runP1 c` is the run at the empty registry and fuel `fz c.formula`; every run of
 `c` (any registry, any fuel) is `runP1 c` (`runP1_of_run`); `hrun_of_fragC` gives the run at the acceptance
 registry from `P1FragC.run` (registry `R0`).
 * §2 `noPathReads c` (decidable): the run's path reads (`V1J8.Gen.pathReads (rowsOfT t)`, axis `≥ 2`) are empty.
 `noPathReads_iff`: it is the E10 case split `walkRoots (j8DataCanon …).reads = []` of `CanonWalkP1`;
 `nW_one_of_noPath`: then the canonical walk has one row.
 * §3 `P1SizeOK c` (`Rows31 ∧ RootsLeafOK` of the canonical data of `runP1 c`), `szOfClaim`, `szOfClaim_eq`
 (= `szCanon` under `P1SizeOK`), and the statement-side `hsz` (`hsz_of`) and `hnW1` (`hnW1_of`) at
 `canonPb hpG (szOfClaim p) c`.
 * §4 the walk size as a read closure: a read trie has one node per proper prefix of its targets
 (`trie_size_eq`), and `closure_card`: `|readClosure (RdOf σ reads)| = |walkRows cells reads|` when the
 serial `σ` separates the roots, every path read is a defined slot and there is a path read.
 * §5 `RdP1 c` (keys `(cells.idxOf root, axis)` of the canonical reads) and `hszW_of`: the statement-side `hszW`
 at `Rd = RdP1 p c`, `noPath = noPathReads c`.
 `P1SizeOK` is an explicit hypothesis everywhere.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1

open Nock Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.VclL (isPathAx axisBits axisBits_of_two_le)
open Nock.NockVMROM.Thm54.VclL.GenWalk (walkRoots pathKind walkRows walkForest krW trie)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1 (j8DataCanon szCanon szOf ord8Canon ordRS trie_nil_size)

/-! ## 1. Registry independence and fuel stability -/

/-- The formula size (bounds the recursion depth of `genX` on the fragment). -/
def fz : Noun → ℕ
  | .atom _ => 1
  | .cell a b => fz a + fz b + 1

section Reg
variable (R R' : Registry)

/-- **`genX_reg_indep`**: on the fragment `{0, 7, 10, autocons}` the generator does not read the registry. -/
theorem genX_reg_indep {f : Noun} (hf : P1Frag f) : ∀ (fuel : ℕ) (s : Noun), genX R fuel s f = genX R' fuel s f := by
  induction hf with
  | op0 ax =>
    intro fuel s
    cases fuel with
    | zero => rfl
    | succ n => simp only [genX, genComputeSkeletonX]
  | @op7 b c _ _ ihb ihc =>
    intro fuel s
    cases fuel with
    | zero => rfl
    | succ n =>
      simp only [genX] at ihb ihc
      simp only [genX, genComputeSkeletonX, ihb n s]
      cases genComputeSkeletonX R' n s b with
      | none => rfl
      | some x => obtain ⟨tH, sb⟩ := x; simp only [ihc n sb]
  | @op10 ax c d _ _ ihc ihd =>
    intro fuel s
    cases fuel with
    | zero => rfl
    | succ n =>
      simp only [genX] at ihc ihd
      simp only [genX, genComputeSkeletonX, ihc n s, ihd n s]
  | @cons b c d _ _ ihbc ihd =>
    intro fuel s
    cases fuel with
    | zero => rfl
    | succ n =>
      simp only [genX] at ihbc ihd
      simp only [genX, genComputeSkeletonX, ihbc n s, ihd n s]

/-- **Fuel stability on the fragment**: a run at some fuel is the run at every fuel `≥ fz f`. -/
theorem genX_fuel {f : Noun} (hf : P1Frag f) :
    ∀ {n m : ℕ} {s : Noun} {x : NTree SkelX × Noun}, genX R n s f = some x → fz f ≤ m → genX R m s f = some x := by
  induction hf with
  | op0 ax =>
    intro n m s x h hm
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by cases n <;> simp_all [genX, genComputeSkeletonX]⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [fz] at hm; omega⟩
    simp only [genX, genComputeSkeletonX] at h ⊢
    exact h
  | @op7 b c _ _ ihb ihc =>
    intro n m s x h hm
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by cases n <;> simp_all [genX, genComputeSkeletonX]⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [fz] at hm; omega⟩
    simp only [fz] at hm
    simp only [genX, genComputeSkeletonX] at h ⊢
    cases hb : genComputeSkeletonX R k s b with
    | none => simp [hb] at h
    | some y =>
      obtain ⟨tH, sb⟩ := y
      cases hc : genComputeSkeletonX R k sb c with
      | none => simp [hb, hc] at h
      | some z =>
        obtain ⟨tM, r⟩ := z
        simp only [hb, hc] at h
        simp only [ihb (m := m') hb (by omega), ihc (m := m') hc (by omega)]
        exact h
  | @op10 ax c d _ _ ihc ihd =>
    intro n m s x h hm
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by cases n <;> simp_all [genX, genComputeSkeletonX]⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [fz] at hm; omega⟩
    simp only [fz] at hm
    simp only [genX, genComputeSkeletonX] at h ⊢
    cases hc : genComputeSkeletonX R k s c with
    | none => simp [hc] at h
    | some y =>
      cases hd : genComputeSkeletonX R k s d with
      | none => simp [hc, hd] at h
      | some z =>
        simp only [hc, hd] at h
        simp only [ihc (m := m') hc (by omega), ihd (m := m') hd (by omega)]
        exact h
  | @cons b c d _ _ ihbc ihd =>
    intro n m s x h hm
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by cases n <;> simp_all [genX, genComputeSkeletonX]⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp only [fz] at hm; omega⟩
    simp only [fz] at hm
    simp only [genX, genComputeSkeletonX] at h ⊢
    cases hc : genComputeSkeletonX R k s (.cell b c) with
    | none => simp [hc] at h
    | some y =>
      cases hd : genComputeSkeletonX R k s d with
      | none => simp [hc, hd] at h
      | some z =>
        simp only [hc, hd] at h
        simp only [ihbc (m := m') hc (by simp only [fz]; omega), ihd (m := m') hd (by omega)]
        exact h

end Reg

/-- **The P1 run of a claim**: the generator at the empty registry and fuel `fz c.formula`. -/
def runP1 (c : P8PublicClaim) : Option (NTree SkelX × Noun) :=
  genX VerifiedRegistry.empty.R (fz c.formula) c.subject c.formula

/-- **Every run of a fragment claim is `runP1 c`** (any registry, any fuel). -/
theorem runP1_of_run {c : P8PublicClaim} (hf : P1Frag c.formula) {R : Registry} {fuel : ℕ}
    {x : NTree SkelX × Noun} (h : genX R fuel c.subject c.formula = some x) : runP1 c = some x := by
  rw [genX_reg_indep R VerifiedRegistry.empty.R hf] at h
  exact genX_fuel _ hf h le_rfl

/-- `runP1 c` is a run at every registry. -/
theorem run_of_runP1 {c : P8PublicClaim} (hf : P1Frag c.formula) (R : Registry) {x : NTree SkelX × Noun}
    (h : runP1 c = some x) : genX R (fz c.formula) c.subject c.formula = some x := by
  rw [genX_reg_indep R VerifiedRegistry.empty.R hf]; exact h

/-- **`hrun` at the acceptance registry from `P1FragC.run`** (stated at `InhabJ8Base.R0`): the run of `runP1 c`,
with result `c.result`, at fuel `fz c.formula`, at every registry. -/
theorem hrun_of_fragC {c : P8PublicClaim} (hc : P1FragC c) :
    ∃ t, runP1 c = some (t, c.result) ∧ ∀ Rg : Registry, genX Rg (fz c.formula) c.subject c.formula = some (t, c.result) := by
  obtain ⟨fuel, t, ht⟩ := hc.run
  have h := runP1_of_run (AsmRowsP1.P1FragC.p1Frag hc) ht
  exact ⟨t, h, fun Rg => run_of_runP1 (AsmRowsP1.P1FragC.p1Frag hc) Rg h⟩

/-- **The run at the acceptance registry is the canonical run**: any `hrun : genX Rg fuel … = some (tg, res)` has
`(tg, res) = (t, c.result)` with `t` the tree of `runP1 c`. -/
theorem hrun_eq {c : P8PublicClaim} (hc : P1FragC c) {Rg : Registry} {fuel : ℕ} {tg : NTree SkelX} {res : Noun}
    (hrun : genX Rg fuel c.subject c.formula = some (tg, res)) : runP1 c = some (tg, c.result) ∧ res = c.result := by
  obtain ⟨t, h, -⟩ := hrun_of_fragC hc
  have h' := runP1_of_run (AsmRowsP1.P1FragC.p1Frag hc) hrun
  rw [h] at h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact ⟨h, rfl⟩

/-! ## 2. `noPathReads` -/

/-- **`noPathReads c`**: the P1 run has no path read at axis `≥ 2` (`true` when there is no run). -/
def noPathReads (c : P8PublicClaim) : Prop :=
  match runP1 c with
  | some (t, _) => Nock.V1J8.Gen.pathReads (rowsOfT t) = []
  | none => True

instance (c : P8PublicClaim) : Decidable (noPathReads c) := by
  unfold noPathReads
  split <;> infer_instance

theorem isPathAx_of_two_le {a : ℕ} (h : 2 ≤ a) : isPathAx a = true := by
  unfold isPathAx
  simp only [decide_eq_true_eq, VclL.depthOf]
  rw [axisBits_of_two_le h]
  simp

/-- On reads at axes `≥ 2`, no walk root iff no read. -/
theorem walkRoots_nil_iff {l : List (Noun × ℕ)} (hl : ∀ x ∈ l, 2 ≤ x.2) : walkRoots l = [] ↔ l = [] := by
  unfold walkRoots pathKind
  rw [List.dedup_eq_nil, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons x xs => exact absurd (isPathAx_of_two_le (hl x (by simp))) (h x (by simp))
  · rintro rfl; simp

theorem pathReads_two_le (rows : Array Nock.Edit.GenX.RowNX) : ∀ x ∈ Nock.V1J8.Gen.pathReads rows, 2 ≤ x.2 := by
  intro x hx
  unfold Nock.V1J8.Gen.pathReads at hx
  exact of_decide_eq_true (List.mem_filter.mp hx).2

section Canon
variable (p : ℕ) [Fact p.Prime] (Rg : VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)

/-- **`noPathReads` is the E10 case split** of `CanonWalkP1` (`walkRoots reads = []` at the canonical data), for
every run of the claim. -/
theorem noPathReads_iff {c : P8PublicClaim} (hf : P1Frag c.formula) {fuel : ℕ} {t : NTree SkelX} {r : Noun}
    (hgen : genX Rg.R fuel c.subject c.formula = some (t, r)) :
    noPathReads c ↔ walkRoots (j8DataCanon p Rg Rt hgen).reads = [] := by
  have hrun := runP1_of_run hf hgen
  have e : noPathReads c ↔ Nock.V1J8.Gen.pathReads (rowsOfT t) = [] := by
    unfold noPathReads; rw [hrun]
  rw [e]
  have hp : (j8DataCanon p Rg Rt hgen).reads.Perm (Nock.V1J8.Gen.pathReads (rowsOfT t)) :=
    ord8Canon.permR _ _
  rw [walkRoots_nil_iff (fun x hx => pathReads_two_le _ x (hp.mem_iff.mp hx))]
  constructor
  · intro h; rw [h] at hp; exact hp.eq_nil
  · intro h; rw [h] at hp; exact hp.symm.eq_nil

/-- **The canonical walk of a claim with no path read has one row** (the dummy). -/
theorem walkRows_one_of_noPath {c : P8PublicClaim} (hf : P1Frag c.formula) {fuel : ℕ} {t : NTree SkelX} {r : Noun}
    (hgen : genX Rg.R fuel c.subject c.formula = some (t, r)) (h : noPathReads c) :
    (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length = 1 := by
  have h0 := (noPathReads_iff p Rg Rt hf hgen).mp h
  unfold walkRows walkForest
  rw [if_pos h0, bfsForest_length]
  simp [totalSize, trie_nil_size]

end Canon

/-! ## 3. Claim-level sizes -/

noncomputable section Sizes
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data jNounsP)
open Nock.V1J8.Gen (cellsOfRoots rootsOf callsOf)

/-- The run equation of `runP1`, at the empty verified registry. -/
theorem runP1_gen {c : P8PublicClaim} {x : NTree SkelX × Noun} (h : runP1 c = some x) :
    genX VerifiedRegistry.empty.R (fz c.formula) c.subject c.formula = some x := h

/-- **A P1 run makes no jet call.** -/
theorem callsOf_nil {R : Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hf : P1Frag f)
    (h : genX R fuel s f = some (t, r)) : callsOf (rowsOfT t) = [] := by
  unfold callsOf
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨c0, hc0, hcu⟩ := (mem_bfsForest [t] u).mp hu
  rw [List.mem_singleton] at hc0; subst hc0
  rcases NounSetCloseP1.genX_frag hf h u hcu with e | e | e | e | e | e <;> simp [rowOfSkelX, e]

/-- **The canonical cell count of a P1 run** is the cell count of the claim's demand roots (no J nouns). -/
theorem canon_cells_length (p : ℕ) [Fact p.Prime] (Rg : VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {c : P8PublicClaim} (hf : P1Frag c.formula) {fuel : ℕ} {t : NTree SkelX}
    (hgen : genX Rg.R fuel c.subject c.formula = some (t, c.result)) :
    (j8DataCanon p Rg Rt hgen).cells.length = (cellsOfRoots (rootsOf c (rowsOfT t))).length := by
  have e1 : (j8DataCanon p Rg Rt hgen).cells.length = (cellsOfRoots (j8DataCanon p Rg Rt hgen).roots).length :=
    (ord8Canon.permC _).length_eq
  have ejn : (j8DataCanon p Rg Rt hgen).jn = [] := by
    show jNounsP p Rt ((callsOf (rowsOfT t)).map Prod.fst).dedup (callsOf (rowsOfT t)) = []
    rw [callsOf_nil hf hgen]; rfl
  have e2 : (j8DataCanon p Rg Rt hgen).roots = rootsOf c (rowsOfT t) ++ (j8DataCanon p Rg Rt hgen).jn := rfl
  rw [e1, e2, ejn, List.append_nil]

variable (p : ℕ) [Fact p.Prime]

theorem fact_rc : Fact (ringChar (ZMod p)).Prime := ⟨(ZMod.ringChar_zmod_n p).symm ▸ Fact.out⟩

attribute [local instance] fact_rc

/-- The template table used for the canonical sizes (unread on P1: no calls). -/
def Rt0 : ℕ → Nock.Jet.Autogen.Tpl := fun _ => tpl0

/-- The default sizes (outside `P1SizeOK`). -/
def sz1 : SizesP1 := ⟨1, 1, 1, 1, one_pos, one_pos, one_pos, by norm_num⟩

/-- **The canonical data of the P1 run** `runP1 c = some (t, r)` (empty registry, `Rt0`). -/
abbrev DC {c : P8PublicClaim} {t : NTree SkelX} {r : Noun} (h : runP1 c = some (t, r)) :
    J8Data p VerifiedRegistry.empty (fz c.formula) c.subject c.formula r :=
  j8DataCanon p VerifiedRegistry.empty Rt0 (runP1_gen h)

/-- The fit inequality `SizesP1.hfit` of a datum. -/
abbrev FitP1 {Rg : VerifiedRegistry} {fuel : ℕ} {s f r : Noun} (D : J8Data p Rg fuel s f r) : Prop :=
  max (bfsForest [D.t]).length (max D.cells.length (walkRows D.cells D.reads).length) ≤ 2 ^ 32

/-- **`P1SizeOK c`**: the size premise, `Rows31 ∧ RootsLeafOK` of the canonical data of the P1 run (`False` when
there is no run). -/
def P1SizeOK (c : P8PublicClaim) : Prop :=
  match h : runP1 c with
  | some (_, _) => ComplJ8Of.Rows31 (DC p h) ∧ ComplJ8Walk.RootsLeafOK (DC p h).roots
  | none => False

/-- **`szOfClaim`**: the canonical sizes of the claim's P1 run (`sz1` when there is no run or it does not fit). -/
def szOfClaim (c : P8PublicClaim) : SizesP1 :=
  match h : runP1 c with
  | some (_, _) =>
    if hfit : FitP1 p (DC p h) then
      szOf (DC p h) (J8Gen.cells_posG Rt0 (runP1_gen h) ord8Canon) hfit
    else sz1
  | none => sz1

theorem szOfClaim_of {c : P8PublicClaim} {t : NTree SkelX} {r : Noun} (h : runP1 c = some (t, r)) :
    szOfClaim p c = if hfit : FitP1 p (DC p h) then
      szOf (DC p h) (J8Gen.cells_posG Rt0 (runP1_gen h) ord8Canon) hfit else sz1 := by
  unfold szOfClaim
  split
  · next t' r' h' =>
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  · next h' => rw [h] at h'; cases h'

theorem P1SizeOK_of {c : P8PublicClaim} {t : NTree SkelX} {r : Noun} (h : runP1 c = some (t, r)) :
    P1SizeOK p c ↔ ComplJ8Of.Rows31 (DC p h) ∧ ComplJ8Walk.RootsLeafOK (DC p h).roots := by
  unfold P1SizeOK
  split
  · next t' r' h' =>
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  · next h' => rw [h] at h'; cases h'

/-- `Rows31` gives the fit (`CanonRunP1.canon_fit_of_rows31`). -/
theorem fit_of_rows31 {Rg : VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {D : J8Data p Rg fuel s f r}
    (h31 : ComplJ8Of.Rows31 D) : FitP1 p D := by
  have hn := h31 (bfsForest [D.t]).length (by simp [ComplJ8Of.sizesJ8])
  have hC : D.cells.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ8Of.sizesJ8])
  have hW := h31 (walkRows D.cells D.reads).length (by simp [ComplJ8Of.sizesJ8])
  have : (2 : ℕ) ^ 31 ≤ 2 ^ 32 := by norm_num
  exact max_le (hn.trans this) (max_le (hC.trans this) (hW.trans this))

/-- **Under `P1SizeOK`, `szOfClaim` is the canonical generator's sizes** (`szOf` form). -/
theorem szOfClaim_eq_szOf {c : P8PublicClaim} {t : NTree SkelX} {r : Noun} (h : runP1 c = some (t, r))
    (hok : P1SizeOK p c) : ∃ hfit, szOfClaim p c = szOf (DC p h) (J8Gen.cells_posG Rt0 (runP1_gen h) ord8Canon) hfit :=
  have hfit := fit_of_rows31 p ((P1SizeOK_of p h).mp hok).1
  ⟨hfit, by rw [szOfClaim_of p h]; exact dif_pos hfit⟩

/-- **`szOfClaim c = szCanon …` under `P1SizeOK`.** -/
theorem szOfClaim_eq [Fact (ringChar (ZMod p)).Prime] {c : P8PublicClaim} {t : NTree SkelX} {r : Noun}
    (h : runP1 c = some (t, r)) (hok : P1SizeOK p c) :
    ∃ hfit, szOfClaim p c = szCanon p VerifiedRegistry.empty Rt0 (runP1_gen h) hfit :=
  szOfClaim_eq_szOf p h hok

/-- **`hsz` of `trace_unique_closed`** at `Pb = canonPb hpG (szOfClaim p) c`, for the run `hrun` at the acceptance
registry. -/
theorem hsz_of {hpG : p = Nock.Atoms.p} {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {Rg : Registry} {fuel : ℕ} {tg : NTree SkelX} {res : Noun}
    (hrun : genX Rg fuel c.subject c.formula = some (tg, res)) :
    (canonPb hpG (szOfClaim p) c).nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length := by
  obtain ⟨h, -⟩ := hrun_eq hc hrun
  obtain ⟨hfit, e⟩ := szOfClaim_eq_szOf p h hok
  show (szOfClaim p c).nC = _
  rw [e]
  exact canon_cells_length p VerifiedRegistry.empty Rt0 (AsmRowsP1.P1FragC.p1Frag hc) (runP1_gen h)

/-- **`hnW1` of `trace_unique_closed`**: with no path read the canonical walk has one row. -/
theorem hnW1_of {hpG : p = Nock.Atoms.p} {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    (hno : noPathReads c) : (canonPb hpG (szOfClaim p) c).nW = 1 := by
  obtain ⟨t, h, -⟩ := hrun_of_fragC hc
  obtain ⟨hfit, e⟩ := szOfClaim_eq_szOf p h hok
  show (szOfClaim p c).nW = 1
  rw [e]
  exact walkRows_one_of_noPath p VerifiedRegistry.empty Rt0 (AsmRowsP1.P1FragC.p1Frag hc) (runP1_gen h) hno

end Sizes

/-! ## 4. The walk size as a read closure (`hszW`) -/

section WalkSize
open Nock.NockVMROM.Thm54.VclL (chainWalk axisFold axisFold_append axisFold_lt axisFold_axisBits slot_eq_chainWalk)
open Nock.NockVMROM.Thm54.VclL.GenWalk (sideTails contT cont mem_contT contT_ne_nil targetsOf targetsOf_ne
  targetsOf_ne_nil mem_pathKind mem_sideTails_iff size_node' two_le_of_path)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (pref readClosure)

/-- The proper prefixes of a target list. -/
def PP (T : List (List Bool)) : Finset (List Bool) :=
  T.toFinset.biUnion fun s => (Finset.range s.length).image fun k => s.take k

theorem mem_PP {T : List (List Bool)} {q : List Bool} : q ∈ PP T ↔ ∃ s ∈ T, ∃ k < s.length, s.take k = q := by
  simp only [PP, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image, Finset.mem_range]

theorem mem_PP_split {T : List (List Bool)} (hT : ∀ s ∈ T, s ≠ []) (hne : T ≠ []) (q : List Bool) :
    q ∈ PP T ↔ q = [] ∨ ∃ b q', q = b :: q' ∧ q' ∈ PP (contT b T) := by
  rw [mem_PP]
  constructor
  · rintro ⟨s, hs, k, hk, rfl⟩
    obtain ⟨b, s', rfl⟩ := List.exists_cons_of_ne_nil (hT _ hs)
    cases k with
    | zero => left; rfl
    | succ k =>
      right
      have hk' : k < s'.length := by simpa using hk
      refine ⟨b, s'.take k, rfl, mem_PP.mpr ⟨s', ?_, k, hk', rfl⟩⟩
      unfold contT
      refine List.mem_filter.mpr ⟨mem_sideTails_iff.mpr hs, ?_⟩
      cases s' with
      | nil => simp at hk'
      | cons _ _ => rfl
  · rintro (rfl | ⟨b, q', rfl, hq⟩)
    · obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil T hne
      refine ⟨s, hs, 0, ?_, rfl⟩
      cases s with
      | nil => exact absurd rfl (hT _ hs)
      | cons _ _ => simp
    · obtain ⟨s', hs', k, hk, rfl⟩ := mem_PP.mp hq
      exact ⟨b :: s', (mem_contT hs').1, k + 1, by simpa using hk, rfl⟩

/-- `cons b` as an embedding. -/
def consE (b : Bool) : List Bool ↪ List Bool := ⟨List.cons b, List.cons_injective⟩

theorem card_PP {T : List (List Bool)} (hT : ∀ s ∈ T, s ≠ []) (hne : T ≠ []) :
    (PP T).card = 1 + (PP (contT false T)).card + (PP (contT true T)).card := by
  have e : PP T = insert [] ((PP (contT false T)).map (consE false) ∪ (PP (contT true T)).map (consE true)) := by
    ext q
    rw [mem_PP_split hT hne, Finset.mem_insert, Finset.mem_union, Finset.mem_map, Finset.mem_map]
    constructor
    · rintro (h | ⟨b, q', rfl, hq⟩)
      · exact Or.inl h
      · cases b
        · exact Or.inr (Or.inl ⟨q', hq, rfl⟩)
        · exact Or.inr (Or.inr ⟨q', hq, rfl⟩)
    · rintro (h | ⟨q', hq, rfl⟩ | ⟨q', hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨false, q', rfl, hq⟩
      · exact Or.inr ⟨true, q', rfl, hq⟩
  have hdis : Disjoint ((PP (contT false T)).map (consE false)) ((PP (contT true T)).map (consE true)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_map.mp hb
    simp [consE] at hy
  have hnot : [] ∉ (PP (contT false T)).map (consE false) ∪ (PP (contT true T)).map (consE true) := by
    intro h
    rcases Finset.mem_union.mp h with h | h <;>
    · obtain ⟨x, -, hx⟩ := Finset.mem_map.mp h
      simp [consE] at hx
  rw [e, Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis, Finset.card_map, Finset.card_map]
  omega

theorem contT_nil_of {b : Bool} {T : List (List Bool)} (hc : ¬ cont b T = true) : contT b T = [] := by
  unfold cont at hc
  cases h : contT b T with
  | nil => rfl
  | cons _ _ => rw [h] at hc; simp at hc

/-- **The read trie has one node per proper prefix of its targets** (non-empty targets, defined paths). -/
theorem trie_size_eq (root : Noun) : ∀ (n : Noun) (bs : List Bool) (T : List (List Bool)),
    T ≠ [] → (∀ s ∈ T, s ≠ [] ∧ (chainWalk n s).isSome) → (trie root n bs T).size = (PP T).card
  | .atom a, bs, T, hne, hT => by
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil T hne
    obtain ⟨h1, h2⟩ := hT s hs
    obtain ⟨b, s', rfl⟩ := List.exists_cons_of_ne_nil h1
    simp [chainWalk] at h2
  | .cell l r, bs, T, hne, hT => by
    have hT' : ∀ s ∈ T, s ≠ [] := fun s hs => (hT s hs).1
    rw [card_PP hT' hne]
    have hL : ((if cont false T = true then [trie root l (bs ++ [false]) (contT false T)] else []).map
        NTree.size).sum = (PP (contT false T)).card := by
      by_cases hc : cont false T = true
      · rw [if_pos hc]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        refine trie_size_eq root l _ _ (contT_ne_nil hc) fun s hs => ⟨(mem_contT hs).2, ?_⟩
        have := (hT _ (mem_contT hs).1).2
        simpa [chainWalk] using this
      · rw [if_neg hc, contT_nil_of hc]; rfl
    have hR : ((if cont true T = true then [trie root r (bs ++ [true]) (contT true T)] else []).map
        NTree.size).sum = (PP (contT true T)).card := by
      by_cases hc : cont true T = true
      · rw [if_pos hc]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        refine trie_size_eq root r _ _ (contT_ne_nil hc) fun s hs => ⟨(mem_contT hs).2, ?_⟩
        have := (hT _ (mem_contT hs).1).2
        simpa [chainWalk] using this
      · rw [if_neg hc, contT_nil_of hc]; rfl
    simp only [trie, size_node', List.map_append, List.sum_append, hL, hR]
    omega

/-- **The walk rows, counted by proper prefixes** (at least one path read; every path read a defined slot). -/
theorem walkRows_length_eq (cells : List Noun) (reads : List (Noun × ℕ))
    (hslot : ∀ x ∈ pathKind reads, (Noun.slot x.2 x.1).isSome) (hne : walkRoots reads ≠ []) :
    (walkRows cells reads).length = ((walkRoots reads).map fun r => (PP (targetsOf reads r)).card).sum := by
  unfold walkRows walkForest
  rw [if_neg hne, bfsForest_length]
  unfold totalSize
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  simp only [Function.comp]
  refine trie_size_eq r r [] _ (targetsOf_ne_nil hr) fun s hs => ⟨targetsOf_ne reads r s hs, ?_⟩
  unfold targetsOf at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
  have e : x.1 = r := of_decide_eq_true hx2
  have h2 := two_le_of_path (mem_pathKind.mp hx1).2
  rw [← e, ← slot_eq_chainWalk x.2 (by omega)]
  exact hslot x hx1

theorem two_pow_le_axisFold (bs : List Bool) : 2 ^ bs.length ≤ axisFold bs := by
  induction bs using List.reverseRecOn with
  | nil => simp [axisFold]
  | append_singleton bs b ih =>
    rw [axisFold_append, List.length_append, List.length_singleton, pow_succ]
    split <;> omega

theorem axisFold_take (bs : List Bool) : ∀ j ≤ bs.length, axisFold (bs.take j) = axisFold bs / 2 ^ (bs.length - j) := by
  induction bs using List.reverseRecOn with
  | nil => intro j hj; simp at hj; subst hj; simp
  | append_singleton bs b ih =>
    intro j hj
    rw [List.length_append, List.length_singleton] at hj ⊢
    by_cases hjl : j = bs.length + 1
    · subst hjl; rw [Nat.sub_self, pow_zero, Nat.div_one, List.take_of_length_le (by simp)]
    · have hj' : j ≤ bs.length := by omega
      rw [List.take_append_of_le_length hj', ih j hj', axisFold_append,
        show bs.length + 1 - j = (bs.length - j) + 1 by omega, pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      split <;> omega

theorem mem_pref_iff (σ0 a : ℕ) (ha : 1 ≤ a) (y : ℕ × ℕ) :
    y ∈ pref (σ0, a) ↔ ∃ j < (axisBits a).length, y = (σ0, axisFold ((axisBits a).take j)) := by
  set L := (axisBits a).length with hL
  have hfa := axisFold_axisBits a ha
  have hlo : 2 ^ L ≤ a := hfa ▸ two_pow_le_axisFold (axisBits a)
  have hhi : a < 2 ^ (L + 1) := hfa ▸ axisFold_lt (axisBits a)
  unfold pref
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨hk, h1⟩, rfl⟩
    have h2 : 2 ^ (k + 1) ≤ a := by
      have := (Nat.le_div_iff_mul_le (by positivity)).mp h1; omega
    have hkL : k + 1 ≤ L := by
      by_contra hc
      have : 2 ^ (L + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨L - (k + 1), by omega, ?_⟩
    rw [axisFold_take _ _ (by omega), hfa, show L - (L - (k + 1)) = k + 1 by omega]
  · rintro ⟨j, hj, rfl⟩
    have hLa : L < a := lt_of_lt_of_le Nat.lt_two_pow_self hlo
    refine ⟨L - j - 1, ⟨by omega, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le (by positivity), one_mul]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlo
    · rw [axisFold_take _ _ (by omega), hfa, show L - j - 1 + 1 = L - j by omega]

/-- **The walk reads as `(root serial, axis)` keys**, serial `σ`. -/
def RdOf (σ : Noun → ℕ) (reads : List (Noun × ℕ)) : Finset (ℕ × ℕ) :=
  ((pathKind reads).map fun x => (σ x.1, x.2)).toFinset

theorem axisFold_inj : Function.Injective axisFold := fun q q' h => by
  have := congrArg axisBits h
  rwa [Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.axisBits_axisFold,
    Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.axisBits_axisFold] at this

/-- **The read closure has one key per walk row** (distinct roots have distinct serials; at least one path read;
every path read a defined slot). -/
theorem closure_card (cells : List Noun) (reads : List (Noun × ℕ)) (σ : Noun → ℕ)
    (hσ : ∀ r ∈ walkRoots reads, ∀ r' ∈ walkRoots reads, σ r = σ r' → r = r')
    (hslot : ∀ x ∈ pathKind reads, (Noun.slot x.2 x.1).isSome) (hne : walkRoots reads ≠ []) :
    (readClosure (RdOf σ reads)).card = (walkRows cells reads).length := by
  have e : readClosure (RdOf σ reads) = (walkRoots reads).toFinset.biUnion
      fun r => (PP (targetsOf reads r)).image fun q => (σ r, axisFold q) := by
    ext y
    simp only [readClosure, RdOf, Finset.mem_biUnion, List.mem_toFinset, List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
      have h2 := two_le_of_path (mem_pathKind.mp hx).2
      obtain ⟨j, hj, rfl⟩ := (mem_pref_iff _ _ (by omega) y).mp hy
      refine ⟨x.1, ?_, (axisBits x.2).take j, mem_PP.mpr ⟨axisBits x.2, ?_, j, hj, rfl⟩, rfl⟩
      · unfold walkRoots; exact List.mem_dedup.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
      · unfold targetsOf; exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
    · rintro ⟨r, hr, q, hq, rfl⟩
      obtain ⟨s, hs, k, hk, rfl⟩ := mem_PP.mp hq
      unfold targetsOf at hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
      have e1 : x.1 = r := of_decide_eq_true hx2
      subst e1
      have h2 := two_le_of_path (mem_pathKind.mp hx1).2
      exact ⟨_, ⟨x, hx1, rfl⟩, (mem_pref_iff _ _ (by omega) _).mpr ⟨k, hk, rfl⟩⟩
  rw [e, Finset.card_biUnion]
  · have hnd : (walkRoots reads).Nodup := List.nodup_dedup _
    rw [List.sum_toFinset _ hnd, walkRows_length_eq cells reads hslot hne]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    exact Finset.card_image_of_injective _ fun q q' h => axisFold_inj (Prod.mk.inj h).2
  · intro r hr r' hr' hne'
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hb
    exact hne' (hσ r (List.mem_toFinset.mp hr) r' (List.mem_toFinset.mp hr') (Prod.mk.inj hq').1.symm)

end WalkSize

/-! ## 5. `hszW` at the canonical layout -/

noncomputable section WalkCanon
open Nock.NockVMROM.Thm54.VclL.GenWalk (mem_pathKind)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (readClosure)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen (j8DataGen Ord8)
variable (p : ℕ) [Fact p.Prime]
attribute [local instance] fact_rc

/-- **Every walk read's root is a cell of the table** (a defined slot at axis `≥ 2` reads a cell; handle nouns that
are cells are in the cell list). -/
theorem reads_root_mem {Rg : VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    ∀ x ∈ (j8DataGen p Rg Rt hgen O).reads, x.1 ∈ (j8DataGen p Rg Rt hgen O).cells := by
  intro x hx
  have hsl := J8Gen.reads_slotG Rt hgen O x hx
  have hx' := (O.permR _ _).mem_iff.mp hx
  have h2 := pathReads_two_le _ x hx'
  obtain ⟨row, hrow, hn⟩ := ComplJ8Data.pathReads_root _ x hx'
  rcases J8Gen.handle_noun_casesG p Rg Rt hgen O hrow hn with ⟨-, hm⟩ | ⟨v, ev, -⟩ | ⟨v, ev, -⟩
  · exact hm
  · rw [ev, ComplJ8OfBalG.slot_atom_two h2] at hsl; cases hsl
  · rw [ev, ComplJ8OfBalG.slot_atom_two h2] at hsl; cases hsl

/-- **The honest read keys of a claim** `(cells.idxOf root, axis)` of the canonical data of its P1 run (`∅` when
there is no run). -/
def RdP1 (c : P8PublicClaim) : Finset (ℕ × ℕ) :=
  match h : runP1 c with
  | some (_, _) => RdOf (fun x => (DC p h).cells.idxOf x) (DC p h).reads
  | none => ∅

theorem RdP1_of {c : P8PublicClaim} {t : NTree SkelX} {r : Noun} (h : runP1 c = some (t, r)) :
    RdP1 p c = RdOf (fun x => (DC p h).cells.idxOf x) (DC p h).reads := by
  unfold RdP1
  split
  · next t' r' h' =>
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  · next h' => rw [h] at h'; cases h'

/-- **`hszW` of `trace_unique_closed`** at `Pb = canonPb hpG (szOfClaim p) c`, `Rd = RdP1 p c`,
`noPath = noPathReads c`. -/
theorem hszW_of {hpG : p = Nock.Atoms.p} {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c) :
    ¬ noPathReads c → (readClosure (RdP1 p c)).card = (canonPb hpG (szOfClaim p) c).nW := by
  intro hno
  obtain ⟨t, h, -⟩ := hrun_of_fragC hc
  obtain ⟨hfit, e⟩ := szOfClaim_eq_szOf p h hok
  show _ = (szOfClaim p c).nW
  rw [e, RdP1_of p h]
  show _ = (walkRows (DC p h).cells (DC p h).reads).length
  have hf := AsmRowsP1.P1FragC.p1Frag hc
  have hne : walkRoots (DC p h).reads ≠ [] := fun h0 =>
    hno ((noPathReads_iff p VerifiedRegistry.empty Rt0 hf (runP1_gen h)).mpr h0)
  have hm : ∀ r ∈ walkRoots (DC p h).reads, r ∈ (DC p h).cells := by
    intro r hr
    unfold walkRoots at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hr)
    exact reads_root_mem p Rt0 (runP1_gen h) ord8Canon x (mem_pathKind.mp hx).1
  refine closure_card _ _ _ (fun r hr r' hr' hσ => (List.idxOf_inj (hm r hr)).mp hσ) (fun x hx => ?_) hne
  exact J8Gen.reads_slotG Rt0 (runP1_gen h) ord8Canon x (mem_pathKind.mp hx).1

end WalkCanon

end Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.genX_reg_indep
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.genX_fuel
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.runP1_of_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.run_of_runP1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.hrun_of_fragC
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.hrun_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.noPathReads_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.walkRows_one_of_noPath
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.callsOf_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.canon_cells_length
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.szOfClaim_eq_szOf
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.szOfClaim_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.hsz_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.hnW1_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.trie_size_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.walkRows_length_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.closure_card
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.reads_root_mem
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1.hszW_of
