/-
  Nock/RedTeam/Batch4872Thm54JSibRetire.lean

  This file records

  * (i)   `jrowsH_eq_of_sib` (F1): under `JSibOK`, `JSubjOK` and the run's registry binder `hRt` (WellTyped ∧ `sem = some`
          for every call, `calls_of_hregC`), the new rows ARE the old audited rows
          (`honestJ8G (hJd …) = honestJ8 cs`, hence `D.jrows` is the old `mvFixP … (honestJ8 …)`);
  * (ii)  non-vacuity at a jet call on a big sibling subject `[[3 0] (p + 5)]`, argument axis `2`: the new J export key of
          the `sl` row equals the cell table's key `[idx, H(l), H(r)]` (`(2, rootIdxP)` for the big tail);
  * (iii) negative control: at the same run the OLD key (`honestJ8 cs`, handle `hOf`) differs from the cell key;
  * (iv)  atom-subject twin: a jet called on the big atom subject `.atom (p + 7)`: the new call key carries
          `(2, rootIdxP)`, the old key `(0, 7)`.

  Labels: all theorems below are kernel-checked (`#print axioms` at the end).  The closed `complJ8_closed` on a
  jet-bearing generated run is NOT constructed here (OPEN, not kernel-checked): (ii)/(iii)/(iv) are at the level of
  the honest J rows of the run's `(cs, acs)` for an arbitrary prime `p`, `cs`, `acs` (stated for all of them, which
  is stronger than a `decide` at one instance).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4872

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Jet.ChipJ8 Nock.Jet.Interp
open Nock.Jet.Autogen (nhd ntl)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf hJd GoodN ClP goodN_nhd goodN_ntl mvFixP pinsOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (JSibOK ChainSibsOK Small)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ (JSubjOK)

noncomputable section

/-! ## (i) Conservativity: `JSibOK ∧ JSubjOK` ⟹ the new rows are the old rows -/

section Cons
variable {p : ℕ} [Fact p.Prime] {cs : List Noun} {acs : List Noun}

theorem agree_of {y : Noun} (hs : ∀ v, y = .atom v → v < p) (hg : GoodN cs y) :
    hOf (p := p) cs y = hJd p cs acs y :=
  ComplJ8OfBalG.hOf_hdlP (p := p) (cs := cs) acs y hs (fun hc => by
    cases y with
    | atom v => simp [Noun.isCell] at hc
    | cell a b => exact hg a b rfl)

theorem small_atoms {y : Noun} (h : Small p y) : ∀ v, y = .atom v → v < p := by
  intro v e; subst e; exact h

theorem chainWG_agree (hcl : ClP cs []) (c dst : ℕ) :
    ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun), GoodN cs x → (∀ v, x = .atom v → v < p) → ChainSibsOK p bs x →
      chainWG (p := p) (hJd p cs acs) c dst src ctr bs x = chainWG (p := p) (hOf cs) c dst src ctr bs x
  | [], src, ctr, x, hg, hs, _ => by
    simp only [chainWG]
    rw [agree_of (acs := acs) hs hg]
  | b :: bs, src, ctr, x, hg, hs, hsib => by
    have hgl := goodN_nhd hcl hg
    have hgr := goodN_ntl hcl hg
    simp only [chainWG]
    rw [agree_of (acs := acs) hs hg, agree_of (acs := acs) hsib.1 hgl, agree_of (acs := acs) hsib.2.1 hgr]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact chainWG_agree hcl c _ bs ctr (ctr + 1) _ hgl hsib.1 hsib.2.2
    · simp only [↓reduceIte]
      exact chainWG_agree hcl c _ bs ctr (ctr + 1) _ hgr hsib.2.1 hsib.2.2

theorem nodeWG_agree (hcl : ClP cs []) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode)
    (hs : GoodN cs s) (hsa : ∀ v, s = .atom v → v < p) (hlk : ∀ n, GoodN cs (lk n)) (hsm : ∀ n, Small p (lk n))
    (hvar : ∀ i ax, nd.op = .var i ax → ChainSibsOK p (axPath ax) s)
    (hpair : nd.op = .pair → lk nd.id = .cell (lk nd.a) (lk nd.b)) :
    nodeWG (p := p) (hJd p cs acs) c S ctr lk s nd = nodeWG (p := p) (hOf cs) c S ctr lk s nd := by
  unfold nodeWG
  cases hop : nd.op with
  | var i ax => dsimp only; exact chainWG_agree hcl _ _ _ _ _ _ hs hsa (hvar i ax hop)
  | nth j =>
    dsimp only
    exact chainWG_agree hcl _ _ _ _ _ _ (hlk _) (small_atoms (hsm _)) (ComplJ8OfBalG.chainSibs_of_small _ (hsm _))
  | tlN n =>
    dsimp only
    exact chainWG_agree hcl _ _ _ _ _ _ (hlk _) (small_atoms (hsm _)) (ComplJ8OfBalG.chainSibs_of_small _ (hsm _))
  | pair =>
    dsimp only
    rw [agree_of (acs := acs) (small_atoms (hsm nd.id)) (hlk nd.id),
      agree_of (acs := acs) (small_atoms (hsm nd.a)) (hlk nd.a),
      agree_of (acs := acs) (small_atoms (hsm nd.b)) (hlk nd.b)]
  | const k => rfl
  | add => rfl
  | mul => rfl
  | isF => rfl
  | isNil => rfl

theorem nodesWG_agree (hcl : ClP cs []) (c S : ℕ) (lk : ℕ → Noun) (s : Noun)
    (hs : GoodN cs s) (hsa : ∀ v, s = .atom v → v < p) (hlk : ∀ n, GoodN cs (lk n)) (hsm : ∀ n, Small p (lk n)) :
    ∀ (nds : List JNode) (ctr : ℕ),
      (∀ nd ∈ nds, (∀ i ax, nd.op = .var i ax → ChainSibsOK p (axPath ax) s) ∧
        (nd.op = .pair → lk nd.id = .cell (lk nd.a) (lk nd.b))) →
      nodesWG (p := p) (hJd p cs acs) c S lk s ctr nds = nodesWG (p := p) (hOf cs) c S lk s ctr nds
  | [], _, _ => rfl
  | nd :: nds, ctr, hnd => by
    simp only [nodesWG]
    rw [nodeWG_agree hcl c S ctr lk s nd hs hsa hlk hsm (hnd nd (by simp)).1 (hnd nd (by simp)).2,
      nodesWG_agree hcl c S lk s hs hsa hlk hsm nds _ (fun nd' h => hnd nd' (by simp [h]))]

theorem blockWG_agree (hcl : ClP cs []) (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) (s : Noun)
    (hs : GoodN cs s) (hsa : ∀ v, s = .atom v → v < p)
    (hv : ∀ y ∈ (honestRows p (R i) s c).map JRow.val, GoodN cs y)
    (hc : GoodN cs (Nock.Jet.Autogen.compile p (R i)))
    (hT : (R i).WellTyped p) (hN : ∀ j, ComplJ8OfBalG.NFree ((R i).inTy j)) (hsem : ∃ r, (R i).sem p s = some r)
    (hsib : ∀ j : Fin (R i).k, ChainSibsOK p (axPath ((R i).ax j)) s) :
    blockWG (p := p) (hJd p cs acs) R c i s = blockWG (p := p) (hOf cs) R c i s := by
  have hlk : ∀ n, GoodN cs (honestLook (p := p) (R i) s c n) := by
    intro n
    unfold honestLook
    cases hn : (honestRows p (R i) s c)[n]? with
    | none => intro a b e; simp [z0] at e
    | some row =>
      simp only [Option.map_some, Option.getD_some]
      exact hv _ (List.mem_map.mpr ⟨row, List.mem_of_getElem? hn, rfl⟩)
  have hsm := ComplJ8OfBalG.look_small (R i) hT hN s hsem c
  have hnodes : ∀ nd ∈ nodesOf (R i), (∀ i' ax, nd.op = .var i' ax → ChainSibsOK p (axPath ax) s) ∧
      (nd.op = .pair → honestLook (p := p) (R i) s c nd.id =
        .cell (honestLook (p := p) (R i) s c nd.a) (honestLook (p := p) (R i) s c nd.b)) := by
    intro nd hnd
    refine ⟨fun i' ax hop => ?_, ComplJ8OfBalG.pair_look (R i) hT s hsem c nd hnd⟩
    obtain ⟨j, rfl⟩ := ComplJ8OfBalG.nodesOf_var (R i) nd hnd i' ax hop
    exact hsib j
  simp only [blockWG]
  have hlk0 := hlk 0
  rw [agree_of (acs := acs) (small_atoms (ComplJ8OfBalG.look_small (R i) hT hN s hsem c 0)) hlk0,
    agree_of (acs := acs) hsa hs,
    agree_of (acs := acs) (by intro v e; rw [Nock.Jet.Autogen.compile] at e; cases e) hc,
    nodesWG_agree hcl c _ _ s hs hsa hlk hsm _ _ hnodes]

end Cons

section Run
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  [Fact (ringChar (ZMod p)).Prime] (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX}
  (hgen : Nock.Edit.GenX.genX Rg.R fuel s f = some (t, r))

/-- **(i) F1: the new honest J rows are the old audited rows under the old binders** (and the registry binder). -/
theorem jrowsH_eq_of_sib
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hN : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ j, ComplJ8OfBalG.NFree ((Rt id).inTy j))
    (hsib : JSibOK Rt (j8DataOf p Rg Rt hgen)) (hsubj : JSubjOK (j8DataOf p Rg Rt hgen)) :
    honestJ8G (p := p) (hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs) Rt
        (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).calls =
      honestJ8 (p := p) (j8DataOf p Rg Rt hgen).cells Rt (j8DataOf p Rg Rt hgen).regs
        (j8DataOf p Rg Rt hgen).calls := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hcl : ClP D.cells [] := ComplJ8Data.cells_closed _
  have hjn := ComplJ8Data.jn_good p Rg Rt hgen
  have hok := ComplJ8OfBalJ.calls_ok Rt hgen hRt
  rw [← honestJ8G_hOf]
  unfold honestJ8G
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hm := ComplJ8OfBalJ.compile_mem Rt hgen i hi
    obtain ⟨a, c', hac⟩ := ComplJ8Data.compile_isCell p (Rt i)
    have hg : GoodN D.cells (Nock.Jet.Autogen.compile p (Rt i)) := fun a' b' _ => hm
    rw [agree_of (acs := D.acs) (by intro v e; rw [hac] at e; cases e) hg]
  · refine List.flatMap_congr fun ⟨⟨i, s0⟩, c⟩ hq => ?_
    have hc1 : (i, s0) ∈ D.calls := List.fst_mem_of_mem_zipIdx hq
    obtain ⟨hT, -, hsem, hreg⟩ := hok _ hc1
    have hs0 : GoodN D.cells s0 := hjn _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq, List.mem_cons_self⟩))
    have hsa : ∀ v, s0 = .atom v → v < p := fun v e => hsubj _ hc1 v e
    exact blockWG_agree hcl Rt c i s0 hs0 hsa
      (fun y hy => hjn _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq, List.mem_cons_of_mem _ hy⟩)))
      (fun a' b' _ => ComplJ8OfBalJ.compile_mem Rt hgen i hreg) hT (hN i (ComplJ8Of.regs_called (p := p) Rt hgen i hreg)) hsem (hsib _ hc1)

theorem jrowsH_eq_old
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hN : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ j, ComplJ8OfBalG.NFree ((Rt id).inTy j))
    (hsib : JSibOK Rt (j8DataOf p Rg Rt hgen)) (hsubj : JSubjOK (j8DataOf p Rg Rt hgen)) :
    (j8DataOf p Rg Rt hgen).jrows =
      mvFixP p (honestJ8 (p := p) (j8DataOf p Rg Rt hgen).cells Rt (j8DataOf p Rg Rt hgen).regs
        (j8DataOf p Rg Rt hgen).calls) (pinsOfP p (j8DataOf p Rg Rt hgen).regs (j8DataOf p Rg Rt hgen).idx) := by
  rw [ComplJ8Jet.j8DataOf_jrows Rt hgen, jrowsH_eq_of_sib Rt hgen hRt hN hsib hsubj]

end Run

/-! ## (ii)/(iii) A jet call on a big sibling: the J export key against the cell key -/

section BigSib
variable {p : ℕ} [Fact p.Prime] (cs acs : List Noun)

/-- The subject `[[3 0] (p + 5)]`: argument axis `2` is the list `[3]`, the off-path sibling is the big atom `p + 5`. -/
def sBig (p : ℕ) : Noun := .cell (.cell (.atom 3) (.atom 0)) (.atom (p + 5))

/-- The cell table's key of the subject `(idx, H l, H r)` (`hdlP` cast). -/
def cellKey (p : ℕ) [Fact p.Prime] (cs acs : List Noun) (x : Noun) : List (ZMod p) :=
  [(((ComplJ8Data.hdlP p cs acs x).2 : ℕ) : ZMod p),
   (((ComplJ8Data.hdlP p cs acs (nhd x)).1 : ℕ) : ZMod p), (((ComplJ8Data.hdlP p cs acs (nhd x)).2 : ℕ) : ZMod p),
   (((ComplJ8Data.hdlP p cs acs (ntl x)).1 : ℕ) : ZMod p), (((ComplJ8Data.hdlP p cs acs (ntl x)).2 : ℕ) : ZMod p)]

/-- The first read row of the call on `sBig` at axis `2`, at the handle `hd`. -/
def slRow (hd : Noun → ZMod p × ZMod p) (c ctr src : ℕ) : CRow (ZMod p) :=
  ⟨⟨.sl, 0, c, ctr, src, 0⟩, mkW 0 1 0 0 0 (hd (sBig p)) (hd (nhd (sBig p))) (hd (ntl (sBig p)))⟩

theorem axPath_two : axPath 2 = [false] := by decide

theorem chain_two (hd : Noun → ZMod p × ZMod p) (c dst src ctr : ℕ) :
    chainWG hd c dst src ctr (axPath 2) (sBig p) =
      [slRow hd c ctr src, ⟨⟨.cp, 0, c, dst, ctr, 0⟩, mkW 0 1 0 0 0 (0, 0) (hd (nhd (sBig p))) (0, 0)⟩] := by
  rw [axPath_two]
  simp only [chainWG, slRow, nhd, ntl, sBig, Bool.false_eq_true, ↓reduceIte]

/-- **(ii) The J export key of the first read row is the cell table's key** (new rows, handle `hJd`): the big
tail is `(2, rootIdxP)` on both sides. -/
theorem key_new (c ctr src : ℕ) :
    keysOf entsX (slRow (hJd p cs acs) c ctr src) = [cellKey p cs acs (sBig p)] := by
  have h := keysOf_entsX_chain (hJd p cs acs) c ctr src false (sBig p)
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  unfold slRow
  rw [h]
  simp only [List.cons.injEq, and_true]
  simp [cellKey, hJd, nhd, ntl, sBig, ComplJ8Data.hdlP]

theorem tail_kind_new : ((hJd p cs acs (ntl (sBig p))).1) = 2 := by
  have h : ¬ (p + 5 < p) := by omega
  simp [hJd, ntl, sBig, ComplJ8Data.hdlP, h]

/-- **(iii) Negative control: the OLD key differs from the cell key** (old handle `hOf cs`, the `honestJ8 cs`
generator at the same run): the big tail has kind `0` there, kind `2` in the cell table. -/
theorem key_old_ne (c ctr src : ℕ) (hp3 : 2 < p) :
    keysOf entsX (slRow (hOf (p := p) cs) c ctr src) ≠ [cellKey p cs acs (sBig p)] := by
  have h0 := keysOf_entsX_chain (hOf (p := p) cs) c ctr src false (sBig p)
  simp only [Bool.false_eq_true, ↓reduceIte] at h0
  unfold slRow
  rw [h0]
  intro h
  simp only [List.cons.injEq, and_true] at h
  have h4 := congrArg (fun l => l.getD 3 0) h
  have h2 : ¬ (p + 5 < p) := by omega
  simp [cellKey, hOf, nhd, ntl, sBig, ComplJ8Data.hdlP, h2] at h4
  have h2' : (2 : ZMod p) = 0 := by exact_mod_cast h4.symm
  have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2')
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-! ## (iv) Atom-subject twin: a jet called on the big atom `p + 7` -/

/-- The call row of a block at the handle `hd`: it carries the handles of `compile T`, the subject `s` and the result. -/
theorem call_key_subject (hd : Noun → ZMod p × ZMod p) (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) (s : Noun) :
    ((blockWG (p := p) hd R c i s).head?.map fun r => (r.w.kL, r.w.vL)) = some ((hd s).1, (hd s).2) := by
  simp [blockWG, mkW]

theorem subject_new : hJd p cs acs (.atom (p + 7)) = (2, (ComplJ8Data.rootIdxP p acs (p + 7) : ZMod p)) := by
  have h : ¬ (p + 7 < p) := by omega
  simp [hJd, ComplJ8Data.hdlP, h]

theorem subject_old : hOf (p := p) cs (.atom (p + 7)) = (0, ((p + 7 : ℕ) : ZMod p)) := by
  simp [hOf]

theorem subject_old_vs_new (hp3 : 2 < p) :
    hOf (p := p) cs (.atom (p + 7)) ≠ hJd p cs acs (.atom (p + 7)) := by
  intro h
  rw [subject_old, subject_new] at h
  have h1 := congrArg Prod.fst h
  simp only at h1
  have h2' : (2 : ZMod p) = 0 := by exact_mod_cast h1.symm
  have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2')
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

end BigSib

end

end Nock.RedTeam.Batch4872

#print axioms Nock.RedTeam.Batch4872.jrowsH_eq_of_sib
#print axioms Nock.RedTeam.Batch4872.jrowsH_eq_old
#print axioms Nock.RedTeam.Batch4872.key_new
#print axioms Nock.RedTeam.Batch4872.tail_kind_new
#print axioms Nock.RedTeam.Batch4872.key_old_ne
#print axioms Nock.RedTeam.Batch4872.subject_new
#print axioms Nock.RedTeam.Batch4872.subject_old
#print axioms Nock.RedTeam.Batch4872.subject_old_vs_new
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed.complJ9B_closed
