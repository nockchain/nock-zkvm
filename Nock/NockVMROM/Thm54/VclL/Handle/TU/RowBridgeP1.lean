/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RowBridgeP1.lean

 **The positional decode-to-run bridge on the fragment `{0, 7, 10, autocons}`.**

 Setting: the compute walk's row accumulator `RowsAccXI n E st D R comb` and its forest goal
 `ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n` (both exposed by the extraction twins
 `TwinRowSemIJ8.acceptsJ8_holdsN_computeI_ex`, `TwinFinalJ8IGA.acceptsJ8_holdsN_EIGA_ex` and
 `TwinHokLJ8GA.acceptsJ8_holdsN_finalLGA_ex`), a root whose subject and formula handles denote the claim's,
 `P1Frag` of the claim formula, `R.Faithful`, and `genX R fuel x.subject x.formula = some (tg, r)`.

 * `goal_tree` — the goal's own tree `t` with the positional clause kept: `(bfsForest [t]).map label` is the
 list of row labels `1..n` (`tree_of_goal` drops it).
 * `sem_at` — EVERY compute row `j < n` satisfies the guarded row semantics `RowSemX0I` (not only the first row
 carrying its label): the halving premise of an `s10L` row comes from the BFS node at position `j`.
 * `state_eq_of_lbl` — two rows with the same walk label have the same state. The walk label rewrites an
 `s10L` state to `s3`, so the only collision is `s10L` against `s3`; it is excluded by the formula handle
 (shared by the label): an `s10L` row's formula handle has kind `0`, an `s3` row's is a cell (`cell3_kind`).
 * **`rowBridge`** — the bridge: the BFS list of `tg` has length `n` and for every `j < n` the decoded row
 `rowOfX (E j) (st j)` agrees with BFS node `j` of `tg` (`RowAgreeX`): the state; the subject, formula and
 evaluation nouns; for every child position `i`, the nouns of the `i`-th child triple of `kidsX` against the
 honest `i`-th kid row (subject, formula, evaluation); and the per-state local handles `ActiveX` against
 `rowOfSkelX` (`s0`: `fh ft`; `s7`: `fh ft fth ftt sf1`; `cons`: `fh ft sf1 sf2`; `s10`: `fh ft fth ftt
 ftth fttt`). Through the child triples this also fixes `sf2` of `s7` and `sf1 sf2` of `s10`.
 * `rowBridge_rowsOfT` — the same against `ComplJ8Data.rowsOfT tg`.
 * `rowBridge_of_twin` — the bridge from the twins' conclusion shape `RowsAccXI ∧ ForestReconGoal ∧ TreeFacts ∧
 HoldsN`.

 Handle serials are not compared here (nouns and states only). Every comparison is field-wise over an
 abstract `env`; no two concrete row records are compared head-to-head.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.GenXDetRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1

open Nock Nock.Reified Nock.Edit Nock.Walk
open Nock.Edit.GenX (P1Frag genX skelOfT skelOfT_node RowNX rowOfSkelX kidE inTree_rowSem)
open Nock.NockVMROM.Thm54 (mapNTree mapNTree_label mapNTree_children bfsForest_mapNTree)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8 (relabX TreeFacts)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.Jet (Registry)

noncomputable section

/-! ## 1. The walk label of a row -/

/-- The state the walk label carries: `s10L` is read as `s3`. -/
def wSt : StateX → StateX
  | .s10L => .s3
  | s => s

section Lbl
variable {p : ℕ} [Fact p.Prime]

theorem rowW_st (env : Env (ZMod p)) (st : StateX) : (rowW env st).st = wSt st := by
  cases st <;> rfl

theorem rowW_s (env : Env (ZMod p)) (st : StateX) : (rowW env st).s = hdV env xS := by
  cases st <;> rfl

theorem rowW_f (env : Env (ZMod p)) (st : StateX) : (rowW env st).f = hdV env xF := by
  cases st <;> rfl

theorem rowW_e (env : Env (ZMod p)) (st : StateX) : (rowW env st).e = hdV env xE := by
  cases st <;> rfl

theorem wSt_eq {a b : StateX} (h : wSt a = wSt b) :
    a = b ∨ (a = .s10L ∧ b = .s3) ∨ (a = .s3 ∧ b = .s10L) := by
  cases a <;> cases b <;> simp_all [wSt]

/-- The `s10L` decoded row's formula handle is a small atom. -/
theorem f_kind_s10L {D : HX → Option Noun} {R : Registry} {env : Env (ZMod p)}
    (h : RowSemX0 p D R (rowOfX env .s10L)) : (hdV env xF).1 = 0 := by
  obtain ⟨a, ha, -⟩ := h
  have : (rowOfX env .s10L).f = hdV env xF := rfl
  rw [← this, ha]

/-- The `s3` decoded row's formula handle is not a small atom. -/
theorem f_kind_s3 {D : HX → Option Noun} {R : Registry} (hD : DenOKX p D) {env : Env (ZMod p)}
    (h : RowSemX0 p D R (rowOfX env .s3)) : (hdV env xF).1 ≠ 0 :=
  cell3_kind hD h.1

end Lbl

/-! ## 2. The goal's tree, with the positional clause -/

section Goal
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX}

/-- **The goal's tree**: as `tree_of_goal`, with the positional clause (BFS node `j` carries row label `j+1`). -/
theorem goal_tree [CharP K p] (hn : 1 ≤ n) (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n) :
    ∃ t : NTree (StateX × RowVSX),
      (bfsForest [t]).map NTree.label = (List.range' 1 n).map (lblOf (rowsWX E st)) ∧
      t.label = lblOf (rowsWX E st) 1 ∧
      (∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i) ∧
      (∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX u.label.2) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hsmall : ∀ i, 1 ≤ i → i ≤ n → SmallR p (rowsWX E st i) := fun i _ _ => smallR_rowW _ _
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    match ts, hlen with
    | [t], _ => exact ⟨t, rfl⟩
  have hmem : ∀ u, InTree t u → u ∈ bfsForest [t] := fun u hu =>
    (mem_bfsForest [t] u).mpr ⟨t, List.mem_singleton_self _, hu⟩
  have hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i := by
    intro u hu
    have hl : u.label ∈ (bfsForest [t]).map NTree.label := List.mem_map_of_mem (hmem u hu)
    rw [hlab] at hl
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hl
    rw [List.mem_range'_1] at hi
    exact ⟨i, hi.1, by omega, hie.symm⟩
  refine ⟨t, hlab, ?_, hrow, ?_⟩
  · have hb : bfsForest [t] = [t] ++ bfsForest ([t].flatMap NTree.children) :=
      bfsForest_cons_eq [t] (List.cons_ne_nil _ _)
    have hr : List.range' 1 n = 1 :: List.range' 2 (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [List.range'_succ]; rfl
    have hlab' := hlab
    rw [hb, hr] at hlab'
    simp only [List.singleton_append, List.map_cons, List.cons.injEq] at hlab'
    exact hlab'.1
  · intro u hu
    have hR : RVT (FV (K := K)) u := rvt_sub (hrvt t (List.mem_singleton_self _)) hu
    obtain ⟨i, hi1, hih, hui⟩ := hrow u hu
    have hfo : fanS u.label.1 = u.children.length := hfan u (hmem u hu)
    obtain ⟨l, ch⟩ := u
    simp only [RVT] at hR
    obtain ⟨hF, -, -⟩ := hR
    simp only [NTree.label, NTree.children] at hfo hui ⊢
    have hst : l.1 = l.2.st := hF.1
    have hlen : ch.length = (kidsX l.2).length := by rw [kidsX_length, ← hst, hfo]
    have hsl : SmallR p l.2 := by rw [hui]; exact hsmall i hi1 hih
    refine List.ext_getElem (by rw [List.length_map, hlen]) ?_
    intro j hj1 hj2
    rw [List.length_map] at hj1
    have hj3 : j < 3 := by have := fanS_le l.1; omega
    have hc := (hF.2 ⟨j, hj3⟩).2 (ch[j]).label (by
      simp [NTree.childLabel, NTree.childOpt, NTree.children, hj1])
    have hcin : InTree (NTree.node l ch) ch[j] := InTree.sub (List.getElem_mem hj1) (InTree.here _)
    obtain ⟨i', hi1', hih', hci⟩ := hrow _ (inTree_trans hu hcin)
    have hcs : SmallR p (ch[j]).label.2 := by rw [hci]; exact hsmall i' hi1' hih'
    have hk : (kidsX l.2).getD j trip0 = (kidsX l.2)[j] := by
      rw [List.getD_eq_getElem]
    rw [hk] at hc
    simp only [List.getElem_map]
    exact encT_inj (smallT_trip hcs) (smallT_kids hp0 hsl _ (List.getElem_mem _)) hc

/-- The BFS list of the goal's tree has length `n`, and its `j`-th node carries row label `j + 1`. -/
theorem bfs_at {t : NTree (StateX × RowVSX)}
    (hlab : (bfsForest [t]).map NTree.label = (List.range' 1 n).map (lblOf (rowsWX E st))) :
    (bfsForest [t]).length = n ∧ ∀ j (hj : j < (bfsForest [t]).length),
      ((bfsForest [t])[j]'hj).label = lblOf (rowsWX E st) (j + 1) := by
  have hl := congrArg List.length hlab
  simp only [List.length_map, List.length_range'] at hl
  refine ⟨hl, fun j hj => ?_⟩
  have h2 : j < ((List.range' 1 n).map (lblOf (rowsWX E st))).length := by
    simp only [List.length_map, List.length_range']; omega
  have := List.getElem_of_eq hlab (by simpa using hj)
  rw [List.getElem_map, List.getElem_map, List.getElem_range'] at this
  rw [this]; congr 1; omega

end Goal

/-! ## 3. The honest side -/

section Honest
open Nock.Edit.GenX (SkelX)

theorem rowOfSkelX_core (sk : SkelX) :
    (rowOfSkelX sk).st = sk.state ∧ (rowOfSkelX sk).s = sk.subject ∧ (rowOfSkelX sk).f = sk.formula ∧
      (rowOfSkelX sk).e = sk.evaluation := by
  cases h : sk.state <;> simp [rowOfSkelX, h]

theorem skelOfT_label_row (T : NTree RowX) : (skelOfT T).label.row = T.label := by
  cases T; simp [skelOfT, SkelX.row, NTree.label]

/-- Every node of a `SkelX` lift has its children's rows as its `kids`. -/
theorem skelOfT_kids : ∀ (T : NTree RowX) (v : NTree SkelX), InTree (skelOfT T) v →
    v.label.kids = v.children.map (fun c => c.label.row)
  | .node r cs, v, hv => by
    rw [skelOfT_node] at hv
    cases hv with
    | here =>
      show cs.map NTree.label = (cs.map skelOfT).map (fun c => c.label.row)
      rw [List.map_map]
      exact List.map_congr_left (fun a _ => (skelOfT_label_row a).symm)
    | sub hc hu =>
      simp only [NTree.children] at hc
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hc
      exact skelOfT_kids c v hu

theorem mapT_eq_mapNTree {α β : Type} (g : α → β) (t : NTree α) : mapT g t = mapNTree g t := by
  rw [← GenXDetRows.relabelT_eq_mapT, GenX.relabelT_eq_mapNTree]

end Honest

/-! ## 4. The agreement predicates -/

/-- The handles that the row's own semantics fixes, per fragment state, against the honest noun row. -/
def ActiveX (D : HX → Option Noun) (d : RowVSX) (h : RowNX) : Prop :=
  match d.st with
  | .s0 => nd D d.fh = h.fh ∧ nd D d.ft = h.ft
  | .s7 => nd D d.fh = h.fh ∧ nd D d.ft = h.ft ∧ nd D d.fth = h.fth ∧ nd D d.ftt = h.ftt ∧
      nd D d.sf1 = h.sf1
  | .cons => nd D d.fh = h.fh ∧ nd D d.ft = h.ft ∧ nd D d.sf1 = h.sf1 ∧ nd D d.sf2 = h.sf2
  | .s10 => nd D d.fh = h.fh ∧ nd D d.ft = h.ft ∧ nd D d.fth = h.fth ∧ nd D d.ftt = h.ftt ∧
      nd D d.ftth = h.ftth ∧ nd D d.fttt = h.fttt
  | _ => True

/-- Every child triple of the decoded row denotes the honest kid row's `(subject, formula, evaluation)`. -/
def KidsAgree (D : HX → Option Noun) (d : RowVSX) (sk : GenX.SkelX) : Prop :=
  (kidsX d).length = sk.kids.length ∧ ∀ i (h1 : i < (kidsX d).length) (h2 : i < sk.kids.length),
    nd D ((kidsX d)[i]'h1).1 = (sk.kids[i]'h2).subject ∧ nd D ((kidsX d)[i]'h1).2.1 = (sk.kids[i]'h2).formula ∧
      nd D ((kidsX d)[i]'h1).2.2 = (sk.kids[i]'h2).evaluation

/-- **The decoded row agrees with the honest row**: state, the three nouns, every child triple, and the
locally fixed handles. -/
def RowAgreeX (D : HX → Option Noun) (d : RowVSX) (sk : GenX.SkelX) : Prop :=
  d.st = sk.state ∧ nd D d.s = sk.subject ∧ nd D d.f = sk.formula ∧ nd D d.e = sk.evaluation ∧
    KidsAgree D d sk ∧ ActiveX D d (rowOfSkelX sk)

section Active
variable {p : ℕ} {D : HX → Option Noun} {R : Registry}

theorem active_of {d : RowVSX} {h : RowNX} (hsem : RowSemX0 p D R d) (hsn : h.SemN R)
    (hst : d.st = h.st) (hf : nd D d.f = h.f) (he : nd D d.e = h.e) : ActiveX D d h := by
  unfold ActiveX
  unfold RowSemX0 at hsem
  unfold RowNX.SemN at hsn
  rw [← hst] at hsn
  generalize d.st = S at hsem hsn ⊢
  cases S <;> simp only at hsem hsn ⊢
  · obtain ⟨⟨A, B, hA, hB, hC⟩, -⟩ := hsem
    obtain ⟨-, hfc, -⟩ := hsn
    rw [nd_of hA, hfc] at hf
    obtain ⟨h1, h2⟩ := Noun.cell.inj hf
    exact ⟨by rw [nd_of hB, h1], by rw [nd_of hC, h2]⟩
  · obtain ⟨⟨A, B, hA, hB, hC⟩, -, ⟨A', B', hA', hB', hC'⟩, hes⟩ := hsem
    obtain ⟨-, hfc, htc, hes'⟩ := hsn
    rw [nd_of hA, hfc] at hf
    obtain ⟨h1, h2⟩ := Noun.cell.inj hf
    have hft : nd D d.ft = h.ft := by rw [nd_of hC, h2]
    rw [nd_of hA', htc] at hft
    obtain ⟨h3, h4⟩ := Noun.cell.inj hft
    exact ⟨by rw [nd_of hB, h1], by rw [nd_of hC, h2], by rw [nd_of hB', h3], by rw [nd_of hC', h4],
      by rw [← hes, he, hes']⟩
  · obtain ⟨⟨A, B, hA, hB, hC⟩, -, ⟨A', B', hA', hB', hC'⟩⟩ := hsem
    obtain ⟨-, hfc, hec⟩ := hsn
    rw [nd_of hA, hfc] at hf
    obtain ⟨h1, h2⟩ := Noun.cell.inj hf
    rw [nd_of hA', hec] at he
    obtain ⟨h3, h4⟩ := Noun.cell.inj he
    exact ⟨by rw [nd_of hB, h1], by rw [nd_of hC, h2], by rw [nd_of hB', h3], by rw [nd_of hC', h4]⟩
  · obtain ⟨⟨A, B, hA, hB, hC⟩, -, ⟨A', B', hA', hB', hC'⟩, ⟨A'', B'', hA'', hB'', hC''⟩, -⟩ := hsem
    obtain ⟨-, hfc, htc, hthc, -⟩ := hsn
    rw [nd_of hA, hfc] at hf
    obtain ⟨h1, h2⟩ := Noun.cell.inj hf
    have hft : nd D d.ft = h.ft := by rw [nd_of hC, h2]
    rw [nd_of hA', htc] at hft
    obtain ⟨h3, h4⟩ := Noun.cell.inj hft
    have hfth : nd D d.fth = h.fth := by rw [nd_of hB', h3]
    rw [nd_of hA'', hthc] at hfth
    obtain ⟨h5, h6⟩ := Noun.cell.inj hfth
    exact ⟨by rw [nd_of hB, h1], by rw [nd_of hC, h2], by rw [nd_of hB', h3], by rw [nd_of hC', h4],
      by rw [nd_of hB'', h5], by rw [nd_of hC'', h6]⟩

end Active

/-! ## 5. Rows with one walk label -/

section Same
variable {p : ℕ} [Fact p.Prime] {D : HX → Option Noun} {R : Registry}
variable {E : ℕ → Env (ZMod p)} {st : ℕ → StateX}

theorem sem0 {env : Env (ZMod p)} {s : StateX} (h : RowSemX0I p D R (rowOfX env s))
    (h4 : s ≠ .s4) (h5 : s ≠ .s5) (h11 : s ≠ .s11j) : RowSemX0 p D R (rowOfX env s) :=
  h.1 (preRow_triv h4 h5 h11)

/-- **Two rows with one walk label agree**: the same state (an `s10L` / `s3` collision is excluded by the
shared formula handle), the same subject, formula and evaluation handles, and, off `s10L`, the same decoded
row. -/
theorem agree_of_lbl (hD : DenOKX p D) {i k : ℕ}
    (hsi : RowSemX0I p D R (rowOfX (E (i - 1)) (st (i - 1))))
    (hsk : RowSemX0I p D R (rowOfX (E (k - 1)) (st (k - 1))))
    (hl : lblOf (rowsWX E st) i = lblOf (rowsWX E st) k) :
    st (i - 1) = st (k - 1) ∧ hdV (E (i - 1)) xS = hdV (E (k - 1)) xS ∧
      hdV (E (i - 1)) xF = hdV (E (k - 1)) xF ∧ hdV (E (i - 1)) xE = hdV (E (k - 1)) xE ∧
      (st (i - 1) ≠ .s10L → rowOfX (E (i - 1)) (st (i - 1)) = rowOfX (E (k - 1)) (st (k - 1))) := by
  have hw : rowW (E (i - 1)) (st (i - 1)) = rowW (E (k - 1)) (st (k - 1)) := congrArg Prod.snd hl
  have hS := congrArg RowVSX.s hw
  have hF := congrArg RowVSX.f hw
  have hE := congrArg RowVSX.e hw
  have hT := congrArg RowVSX.st hw
  rw [rowW_s, rowW_s] at hS
  rw [rowW_f, rowW_f] at hF
  rw [rowW_e, rowW_e] at hE
  rw [rowW_st, rowW_st] at hT
  have hst : st (i - 1) = st (k - 1) := by
    rcases wSt_eq hT with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h
    · rw [ha] at hsi; rw [hb] at hsk
      have a := f_kind_s10L (sem0 hsi (by decide) (by decide) (by decide))
      have b := f_kind_s3 hD (sem0 hsk (by decide) (by decide) (by decide))
      rw [hF] at a
      exact absurd a b
    · rw [ha] at hsi; rw [hb] at hsk
      have a := f_kind_s10L (sem0 hsk (by decide) (by decide) (by decide))
      have b := f_kind_s3 hD (sem0 hsi (by decide) (by decide) (by decide))
      rw [← hF] at a
      exact absurd a b
  refine ⟨hst, hS, hF, hE, fun hne => ?_⟩
  have h2 := hw
  rw [rowW_of_ne _ hne, rowW_of_ne _ (by rw [← hst]; exact hne)] at h2
  exact h2

theorem kidsX_congr {d d' : RowVSX} (hst : d.st = d'.st) (hs : d.s = d'.s) (hf : d.f = d'.f)
    (he : d.e = d'.e) (hfull : d.st ≠ .s10L → d = d') : kidsX d = kidsX d' := by
  by_cases h : d.st = .s10L
  · have h' : d'.st = .s10L := hst ▸ h
    simp only [kidsX, h, h', hs, hf, he]
  · rw [hfull h]

theorem getElem_map_eq {α β : Type} {f : α → β} {l : List α} {l' : List β} (h : l.map f = l') {i : ℕ}
    (hi : i < l'.length) : l'[i] = f (l[i]'(by rw [← h] at hi; simpa using hi)) := by
  subst h; simp

theorem active_ofI {d : RowVSX} {h : RowNX} (hsem : RowSemX0I p D R d) (hsn : h.SemN R)
    (hst : d.st = h.st) (hf : nd D d.f = h.f) (he : nd D d.e = h.e) : ActiveX D d h := by
  by_cases h4 : d.st = .s4
  · unfold ActiveX; rw [h4]; exact trivial
  by_cases h5 : d.st = .s5
  · unfold ActiveX; rw [h5]; exact trivial
  by_cases h11 : d.st = .s11j
  · unfold ActiveX; rw [h11]; exact trivial
  exact active_of (hsem.1 (preRow_triv h4 h5 h11)) hsn hst hf he

end Same

/-! ## 6. The bridge -/

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun} {R : Registry}
  {comb : ℕ → Noun}

/-- **The positional decode-to-run bridge.** For every compute row `j < n`, the decoded row
`rowOfX (E j) (st j)` agrees with BFS node `j` of the generated tree `tg` of the claim (`RowAgreeX`): state,
subject / formula / evaluation nouns, every child triple's nouns, and the locally fixed handles. The BFS list
of `tg` has exactly `n` nodes. -/
theorem rowBridge [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D) (hn : 1 ≤ n)
    (A : RowsAccXI n E st D R comb) (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (x : P8PublicClaim) (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r)) :
    (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX D (rowOfX (E j) (st j)) ((bfsForest [tg])[j]'hj).label := by
  classical
  obtain ⟨t, hlab, hroot, hrow, hlink⟩ := goal_tree (K := K) hn hG
  obtain ⟨hlen, hlbl⟩ := bfs_at hlab
  have node : ∀ j (hj : j < (bfsForest [t]).length), InTree t ((bfsForest [t])[j]'hj) := by
    intro j hj
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [t] _).mp (List.getElem_mem hj)
    rw [List.mem_singleton] at hc; subst hc; exact hcu
  have semI : ∀ i, 1 ≤ i → i ≤ n →
      RowSemX0I p D R (rowOfX (E (i - 1)) (st (i - 1))) ∧ KidKinds (rowOfX (E (i - 1)) (st (i - 1))) := by
    intro i hi1 hin
    have hj : i - 1 < (bfsForest [t]).length := by omega
    have hui := hlbl (i - 1) hj
    rw [show i - 1 + 1 = i by omega] at hui
    exact rowSemXI_of_chip hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
      (A.served _ (by omega)) (fun hs => halving_of_treeI hp A hrow hlink (node _ hj) hui hs rfl)
  -- the first-occurrence relabelling, row by row
  have spec : ∀ i, 1 ≤ i → i ≤ n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ lblOf (rowsWX E st) i = lblOf (rowsWX E st) k ∧
      relabX n E st (lblOf (rowsWX E st) i) = rowOfX (E (k - 1)) (st (k - 1)) := fun i hi1 hin => by
    have h : ∃ k, 1 ≤ k ∧ k ≤ n ∧ lblOf (rowsWX E st) i = lblOf (rowsWX E st) k := ⟨i, hi1, hin, rfl⟩
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [relabX, dif_pos h]⟩
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      relabX n E st u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    obtain ⟨i, hi1, hin, hui⟩ := hrow u hu
    obtain ⟨k, hk1, hkn, hik, hrk⟩ := spec i hi1 hin
    exact ⟨k, hk1, hkn, hui.trans hik, by rw [hui]; exact hrk⟩
  have hok : RowsOKXI (relabX n E st) p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, -, hrw⟩ := rw_spec u hu
      rw [hrw]; exact semI i hi1 hin
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (relabX n E st c.label).trip) =
          u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_treeI hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]
  -- the root denotes the claim
  obtain ⟨k0, hk01, hk0n, h1k, hr0⟩ := spec 1 le_rfl hn
  have hroot' : relabX n E st t.label = rowOfX (E (k0 - 1)) (st (k0 - 1)) := by rw [hroot]; exact hr0
  obtain ⟨-, hS0, hF0, -, -⟩ :=
    agree_of_lbl (E := E) (st := st) hD (semI 1 le_rfl hn).1 (semI k0 hk01 hk0n).1 h1k
  simp only [Nat.sub_self] at hS0 hF0
  have hsR : D (relabX n E st t.label).s = some x.subject := by
    rw [hroot']; show D (hdV _ xS) = _; rw [← hS0]; exact hs
  have hfR : D (relabX n E st t.label).f = some x.formula := by
    rw [hroot']; show D (hdV _ xF) = _; rw [← hF0]; exact hf
  have hsR' : D (relabX n E st t.label).s ≠ none := by rw [hsR]; exact Option.some_ne_none _
  have hrowOK : RowsOKX (relabX n E st) p D R t := rowsOKX_of_I (relabX n E st) hD t hok hsR'
  have hT := genuineNX_of_rowsX (relabX n E st) hD t hrowOK hsR'
  have hTs : (mapT (fun l => rx D (relabX n E st l)) t).label.subject = x.subject := by
    rw [mapT_label]; exact nd_of hsR
  have hTf : (mapT (fun l => rx D (relabX n E st l)) t).label.formula = x.formula := by
    rw [mapT_label]; exact nd_of hfR
  -- P1 fragment
  obtain ⟨hTe, hsk⟩ := GenX.genuineNX_eq_genX hR hfrag hg hT hTs hTf
  rw [GenX.relabelT_eq_mapNTree, mapT_eq_mapNTree] at hTe
  have hB : (bfsForest [t]).map (mapNTree (fun l => rx D (relabX n E st l))) =
      (bfsForest [tg]).map (mapNTree GenX.SkelX.row) := by
    have h1 := bfsForest_mapNTree (fun l => rx D (relabX n E st l)) [t]
    have h2 := bfsForest_mapNTree GenX.SkelX.row [tg]
    simp only [List.map_cons, List.map_nil] at h1 h2
    rw [← h1, ← h2, hTe]
  have hlenB : (bfsForest [tg]).length = n := by
    have := congrArg List.length hB; simp only [List.length_map] at this; omega
  refine ⟨hlenB, fun j hj => ?_⟩
  have hjt : j < (bfsForest [t]).length := by omega
  have hnode : mapNTree (fun l => rx D (relabX n E st l)) ((bfsForest [t])[j]'hjt) =
      mapNTree GenX.SkelX.row ((bfsForest [tg])[j]'hj) := by
    have := List.getElem_of_eq hB (by simpa using hjt)
    simp only [List.getElem_map] at this
    exact this
  have hvin : InTree tg ((bfsForest [tg])[j]'hj) := by
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [tg] _).mp (List.getElem_mem hj)
    rw [List.mem_singleton] at hc; subst hc; exact hcu
  have hsn := inTree_rowSem hg hvin
  have hkidsAll : ∀ w, InTree tg w → w.label.kids = w.children.map (fun c => c.label.row) := by
    rw [← hsk]; exact skelOfT_kids _
  have hkids := hkidsAll _ hvin
  have hui := hlbl j hjt
  have hlinku := hok.link _ (node j hjt)
  generalize (bfsForest [t])[j]'hjt = u at hnode hui hlinku
  generalize (bfsForest [tg])[j]'hj = v at hnode hsn hkids ⊢
  have hlabel : rx D (relabX n E st u.label) = v.label.row := by
    have := congrArg NTree.label hnode; simpa only [mapNTree_label] using this
  have hch : u.children.map (fun c => rx D (relabX n E st c.label)) = v.children.map (fun c => c.label.row) := by
    have := congrArg (fun T => T.children.map NTree.label) hnode
    simpa only [mapNTree_children, List.map_map, Function.comp_def, mapNTree_label] using this
  obtain ⟨k, hk1, hkn, hjk, hrk⟩ := spec (j + 1) (by omega) (by omega)
  have ag := agree_of_lbl (E := E) (st := st) hD (semI (j + 1) (by omega) (by omega)).1
    (semI k hk1 hkn).1 hjk
  simp only [Nat.add_sub_cancel] at ag
  obtain ⟨hst, hS, hF, hE, hfull⟩ := ag
  have hrel : relabX n E st u.label = rowOfX (E (k - 1)) (st (k - 1)) := by rw [hui]; exact hrk
  rw [hrel] at hlabel hlinku
  have hstate : (rowOfX (E j) (st j)).st = v.label.state := by
    show st j = _; rw [hst]; exact congrArg RowX.state hlabel
  have hsub : nd D (rowOfX (E j) (st j)).s = v.label.subject := by
    show nd D (hdV (E j) xS) = _; rw [hS]; exact congrArg RowX.subject hlabel
  have hfor : nd D (rowOfX (E j) (st j)).f = v.label.formula := by
    show nd D (hdV (E j) xF) = _; rw [hF]; exact congrArg RowX.formula hlabel
  have hev : nd D (rowOfX (E j) (st j)).e = v.label.evaluation := by
    show nd D (hdV (E j) xE) = _; rw [hE]; exact congrArg RowX.evaluation hlabel
  -- the child triples
  have hkx : kidsX (rowOfX (E j) (st j)) = kidsX (rowOfX (E (k - 1)) (st (k - 1))) :=
    kidsX_congr hst hS hF hE hfull
  rw [← hkx] at hlinku
  have hL2 : u.children.map (fun c => rx D (relabX n E st c.label)) = v.label.kids := by
    rw [hkids, hch]
  have hkid : KidsAgree D (rowOfX (E j) (st j)) v.label := by
    refine ⟨?_, fun i h1 h2 => ?_⟩
    · rw [← hlinku, ← hL2, List.length_map, List.length_map]
    · rw [getElem_map_eq hlinku h1, getElem_map_eq hL2 h2]
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨c1, c2, c3, c4⟩ := rowOfSkelX_core v.label
  refine ⟨hstate, hsub, hfor, hev, hkid, ?_⟩
  exact active_ofI (semI (j + 1) (by omega) (by omega)).1 hsn (by rw [c1]; exact hstate)
    (by rw [c3]; exact hfor) (by rw [c4]; exact hev)

/-- **The bridge against `rowsOfT`**: the honest row array has `n` rows, and row `j` is `rowOfSkelX` of a
`SkelX` row with which the decoded row `j` agrees. -/
theorem rowBridge_rowsOfT [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D) (hn : 1 ≤ n)
    (A : RowsAccXI n E st D R comb) (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (x : P8PublicClaim) (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r)) :
    (rowsOfT tg).size = n ∧ ∀ j, j < n → ∃ sk : GenX.SkelX, (rowsOfT tg)[j]? = some (rowOfSkelX sk) ∧
      RowAgreeX D (rowOfX (E j) (st j)) sk := by
  obtain ⟨hlen, hrow⟩ := rowBridge (K := K) hp hR hD hn A hG x hs hf hfrag hg
  refine ⟨by simp [rowsOfT, hlen], fun j hj => ⟨_, ?_, hrow j (by omega)⟩⟩
  simp [rowsOfT, List.getElem?_eq_getElem (by omega : j < (bfsForest [tg]).length)]

/-- **The bridge from the twins' conclusion** (`RowsAccXI ∧ ForestReconGoal ∧ TreeFacts ∧ HoldsN`, as returned by
`acceptsJ8_holdsN_computeI_ex`, `acceptsJ8_holdsN_EIGA_ex`, `acceptsJ8_holdsN_finalLGA_ex`). -/
theorem rowBridge_of_twin [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D) (hn : 1 ≤ n)
    (x : P8PublicClaim)
    (H : RowsAccXI n E st D R comb ∧ ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n ∧
      TreeFacts K n E st D R ∧ Nock.Jet.HoldsN x)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r)) :
    (rowsOfT tg).size = n ∧ ∀ j, j < n → ∃ sk : GenX.SkelX, (rowsOfT tg)[j]? = some (rowOfSkelX sk) ∧
      RowAgreeX D (rowOfX (E j) (st j)) sk :=
  rowBridge_rowsOfT (K := K) hp hR hD hn H.1 H.2.1 x hs hf hfrag hg

end Bridge

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1.agree_of_lbl
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1.rowBridge
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1.rowBridge_rowsOfT
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1.rowBridge_of_twin
