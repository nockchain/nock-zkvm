/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CellUniqP1.lean

 **Serial uniqueness of the P1 cell table.**

 * §1 (generic) a two-provider accepted cell table `tC` (`TableAccepts2`, external leaves at the empty atom
 denotation) whose rows are read off row values `v` (`hb0`: `b0` of row `i` is `cellB0Of (envAt v i)`), with the
 sorted-table hypotheses `TableM v n`, carries the noun link `NounLink v n N` at `N i` = the decoded noun of serial
 `i` (`nounLink_of_table`, from `row_genuine2` and the validity service); then `CellOrderP1.TableM.nouns_inj` gives
 **one serial per decoded noun** (`serial_inj_table`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.AtomPadP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1

noncomputable section

/-! ## 1. One table -/

section Table
variable {p : ℕ} [Fact p.Prime]

theorem natOf_val (x : ZMod p) : natOf x = x.val := by
  have h := natOf_spec (GeneratedField.primeFieldElems_zmod p) x
  rw [ZMod.ringChar_zmod_n] at h
  have e := congrArg ZMod.val h.2
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h.1] at e
  exact e

theorem cast_val_rc (x : ZMod p) : ((x.val : ZMod (ringChar (ZMod p)))).val = x.val := by
  rw [ZMod.val_natCast, ZMod.ringChar_zmod_n, Nat.mod_eq_of_lt (ZMod.val_lt x)]

theorem lt_of_decode {q : ℕ} {t : List (CellRowB0 q)} {leaf : CellRowB0 q → Side → Option (Option Noun)}
    {f i : ℕ} {X : Noun} (h : decodeTree t leaf f i = some X) : i < t.length := by
  cases f with
  | zero => simp [decodeTree] at h
  | succ f =>
    by_contra hc
    rw [decodeTree, List.getElem?_eq_none (by omega)] at h
    simp at h

theorem idx_of_serial {q : ℕ} {t : List (CellRowB0 q)} (h : SerialOK t) {j : ℕ} (hj : j < t.length) :
    (t[j]'hj).idx = j := by
  have := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at this
  rw [List.getElem?_range hj] at this
  exact Option.some.inj this

variable {Kfp : Type} [Field Kfp] [Algebra (ZMod (ringChar (ZMod p))) Kfp] [Fact (ringChar (ZMod p)).Prime]

/-- The decoded noun of serial `i` (atom `0` off the table). -/
def nounAt (t : List (CellRowB0 (ringChar (ZMod p)))) (i : ℕ) : Noun :=
  (preZNounOfTable2 t (fun _ => none) i).getD (.atom 0)

/-- **One linked side.** -/
theorem side_of {v : ℕ → ℕ → ZMod p} {n : ℕ} {tC : List (CellRow (ringChar (ZMod p)) Kfp)} {vp : List (VKey Kfp)}
    (hlen : tC.length = n) (hserial : SerialOK (tC.map (·.b0)))
    (hb0 : ∀ i (hi : i < tC.length), (tC[i]'hi).b0 = cellB0Of (envAt v i))
    (hserved : ValidityServed2 tC vp)
    {i : ℕ} (hi : i < tC.length) (s : Side) {w id a lo hi' : ℕ} {X : Noun}
    (hw01 : v i w = 0 ∨ v i w = 1)
    (hwS : (tC[i]'hi).b0.wS s = decide (v i w = 1)) (hidS : (tC[i]'hi).b0.idS s = natOf (v i id))
    (haS : (tC[i]'hi).b0.aS s = (natOf (v i a) : ZMod (ringChar (ZMod p))))
    (hloS : (tC[i]'hi).b0.loS s = natOf (v i lo)) (hhiS : (tC[i]'hi).b0.hiS s = natOf (v i hi'))
    (hatom : (tC[i]'hi).b0.wS s = false → X = .atom ((tC[i]'hi).b0.aS s).val)
    (hbig : (tC[i]'hi).b0.wS s = true → (tC[i]'hi).b0.hiS s = 0 ∧ (tC[i]'hi).b0.loS s = 0 → False)
    (hcellch : (tC[i]'hi).b0.wS s = true → ¬ ((tC[i]'hi).b0.hiS s = 0 ∧ (tC[i]'hi).b0.loS s = 0) →
      preZNounOfTable2 (tC.map (·.b0)) (fun _ => none) ((tC[i]'hi).b0.idS s) = some X)
    (hvpN : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0) :
    SideLink v n (nounAt (tC.map (·.b0))) i w id a lo hi' X := by
  rcases hw01 with h0 | h1
  · left
    refine ⟨h0, ?_⟩
    have hf : (tC[i]'hi).b0.wS s = false := by rw [hwS]; simp [h0]
    rw [hatom hf, haS, natOf_val, cast_val_rc]
  · right
    have ht : (tC[i]'hi).b0.wS s = true := by rw [hwS]; simp [h1]
    refine ⟨h1, ?_⟩
    have hnb : ¬ ((tC[i]'hi).b0.hiS s = 0 ∧ (tC[i]'hi).b0.loS s = 0) := hbig ht
    rcases hserved _ (List.getElem_mem hi) s ht with ⟨c', hc', -, hhi2, hlo2, hid2⟩ | hv
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc'
      have hidx : (tC[j]'hj).b0.idx = j := by
        have := idx_of_serial hserial (j := j) (by simpa using hj)
        simpa using this
      have hbj := hb0 j hj
      refine ⟨j, hlen ▸ hj, ?_, ?_, ?_, ?_⟩
      · apply ZMod.val_injective
        have e1 : (tC[j]'hj).b0.idx = natOf (v j Cell.idx) := by rw [hbj]; rfl
        rw [← natOf_val, ← natOf_val, ← e1, ← hidS, hid2]
      · have hd := hcellch ht hnb
        rw [hid2, hidx] at hd
        simp only [nounAt, hd, Option.getD_some]
      · apply ZMod.val_injective
        have e1 : (tC[j]'hj).b0.lo = natOf (v j Cell.lo) := by rw [hbj]; rfl
        rw [← natOf_val, ← natOf_val, ← e1, ← hloS, hlo2]
      · apply ZMod.val_injective
        have e1 : (tC[j]'hj).b0.hi = natOf (v j Cell.hi) := by rw [hbj]; rfl
        rw [← natOf_val, ← natOf_val, ← e1, ← hhiS, hhi2]
    · exact absurd ⟨(hvpN _ hv).1, (hvpN _ hv).2⟩ hnb

/-- **The noun link of an accepted table** at its decoded nouns. -/
theorem nounLink_of_table (hq : 2 ^ 63 < ringChar (ZMod p)) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms (ringChar (ZMod p)) z E)
    {tC : List (CellRow (ringChar (ZMod p)) Kfp)} {vp : List (VKey Kfp)} (htab : TableAccepts2 z tC vp)
    (hvp : AtomLeaves E vp (fun _ => none)) {v : ℕ → ℕ → ZMod p} {n : ℕ} (hlen : tC.length = n)
    (hb0 : ∀ i (hi : i < tC.length), (tC[i]'hi).b0 = cellB0Of (envAt v i)) (T : TableM v n) :
    NounLink v n (nounAt (tC.map (·.b0))) := by
  refine ⟨fun i hi => ?_⟩
  have hiC : i < tC.length := by omega
  have hc := List.getElem_mem hiC
  obtain ⟨L, R, hd, -, -, -, hbig, hcellch, haL, haR⟩ := row_genuine2 hq hcons hE htab hvp hc
  have hidx : (tC[i]'hiC).b0.idx = i := by
    have := idx_of_serial htab.serial (j := i) (by simpa using hiC)
    simpa using this
  have hbi := hb0 i hiC
  have hvpN : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 := fun k hk => ⟨(hvp k hk).1, (hvp k hk).2.1⟩
  have hnone : ∀ s, (tC[i]'hiC).b0.wS s = true →
      (tC[i]'hiC).b0.hiS s = 0 ∧ (tC[i]'hiC).b0.loS s = 0 → False := by
    intro s hw h0
    obtain ⟨hv', -⟩ := hbig s hw h0
    simp at hv'
  refine ⟨L, R, ?_, ?_, ?_⟩
  · simp only [nounAt]; rw [← hidx, hd]; rfl
  · exact side_of hlen htab.serial hb0 htab.served hiC .L (T.cell hi).wL (by rw [hbi]; rfl)
      (by rw [hbi]; rfl) (by rw [hbi]; rfl) (by rw [hbi]; rfl) (by rw [hbi]; rfl) (fun h => haL h)
      (hnone .L) (fun hw hn => by have := hcellch .L hw hn; rwa [if_pos rfl] at this) hvpN
  · exact side_of hlen htab.serial hb0 htab.served hiC .R (T.cell hi).wR (by rw [hbi]; rfl)
      (by rw [hbi]; rfl) (by rw [hbi]; rfl) (by rw [hbi]; rfl) (by rw [hbi]; rfl) (fun h => haR h)
      (hnone .R) (fun hw hn => by have := hcellch .R hw hn; rwa [if_neg (by decide)] at this) hvpN

/-- **One serial per decoded noun** on an accepted sorted table. -/
theorem serial_inj_table (hpG : p = Nock.Atoms.p) (hq : 2 ^ 63 < ringChar (ZMod p)) {z : Kfp}
    {E : Noun → FP Kfp} (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) z E)
    {tC : List (CellRow (ringChar (ZMod p)) Kfp)} {vp : List (VKey Kfp)} (htab : TableAccepts2 z tC vp)
    (hvp : AtomLeaves E vp (fun _ => none)) {v : ℕ → ℕ → ZMod p} {n : ℕ} (hlen : tC.length = n)
    (hb0 : ∀ i (hi : i < tC.length), (tC[i]'hi).b0 = cellB0Of (envAt v i)) (T : TableM v n) (hnp : n ≤ p) :
    ∀ i i' X, preZNounOfTable2 (tC.map (·.b0)) (fun _ => none) i = some X →
      preZNounOfTable2 (tC.map (·.b0)) (fun _ => none) i' = some X → i = i' := by
  intro i i' X h1 h2
  have L := nounLink_of_table hq hcons hE htab hvp hlen hb0 T
  have hi : i < n := by
    have := lt_of_decode (show decodeTree _ _ _ _ = _ from h1); simpa [hlen] using this
  have hi' : i' < n := by
    have := lt_of_decode (show decodeTree _ _ _ _ = _ from h2); simpa [hlen] using this
  exact T.nouns_inj L hpG hnp hi hi' (by simp only [nounAt, h1, h2])

end Table

/-! ## 2. The P1 cell table -/

section Inst
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ (hqkEF)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

theorem cellB0Of_congr {e e' : Env (ZMod p)} (h : ∀ j < 129, e.trace j = e'.trace j) :
    cellB0Of e = cellB0Of e' := by
  simp only [cellB0Of, h Cell.idx (by decide), h Cell.idL (by decide), h Cell.idR (by decide),
    h Cell.wL (by decide), h Cell.wR (by decide), h Cell.aL (by decide), h Cell.aR (by decide),
    h Cell.lo (by decide), h Cell.hi (by decide), h Cell.loL (by decide), h Cell.hiL (by decide),
    h Cell.loR (by decide), h Cell.hiR (by decide), h Cell.carry (by decide), h Cell.mv (by decide),
    h Cell.mx (by decide)]

/-- The restricted cell environment of row `i` reads the trace's round-0 cell columns. -/
theorem restr_trace (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (i : Fin Pb.nC) {j : ℕ}
    (hj : j < 129) :
    (Reify.envOfTrace (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs))
        Pb.orbitC.ω (Pb.nodesC i) (slotVal b 129 chals) (slotVal b 129 pubs)).trace j =
      (tr.M ⟨j, by omega⟩).eval (Pb.nodesC i) ∧
    (Reify.envOfTrace (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs))
        Pb.orbitC.ω (Pb.nodesC i) (slotVal b 129 chals) (slotVal b 129 pubs)).traceNext j =
      (tr.M ⟨j, by omega⟩).eval (Pb.orbitC.ω * Pb.nodesC i) := by
  have hw : (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs).1
  have h0 : j < (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs).rap.w := by rw [hw]; omega
  simp only [Reify.envOfTrace, dif_pos h0, restrictHQKWCell, restrictQ, qM]
  constructor <;> congr 2 <;> apply Fin.ext <;> simp [shiftCol, hj]

/-- **The sorted-table hypotheses at the canonical layout**, from `canonM` and the cell chip. -/
theorem tableM_of {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {c : P8PublicClaim}
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)} {chals pubs : ℕ → K}
    (hM : (canonM b (canonPb hpG sz c)).Satisfies (sideMQ tr ax))
    (hsat : (cellChipHQKW δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals
      pubs).rap.Satisfies (qM δ b (canonPb hpG sz c) tr chals pubs))
    (hbind : (cellChipHQKW δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals
      pubs).BindsPreprocessing (qM δ b (canonPb hpG sz c) tr chals pubs))
    (hinj : Function.Injective (canonPb hpG sz c).nodesC) :
    TableM (vM tr ax (canonPb hpG sz c).orbitC.ω) (canonPb hpG sz c).nC := by
  set Pb := canonPb hpG sz c with hPb
  have hnode : ∀ i : Fin Pb.nC, Pb.nodesC i = Pb.orbitC.ω ^ (i : ℕ) := fun i => rfl
  have hsat0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs _ hsat
  refine ⟨rows_of_canonM b hM, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have hbase := (cellChip_rowLocal δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs _ hsat0 ⟨i, hi⟩).1
    refine cellBase_transfer (fun j hj => ?_) (fun j hj => ?_) hbase
    · show vM tr ax Pb.orbitC.ω i j = _
      rw [vM_base tr ax _ i (by omega), (restr_trace δ b Pb tr chals pubs ⟨i, hi⟩ hj).1, hnode]
    · show vM tr ax Pb.orbitC.ω (i + 1) j = _
      rw [vM_base tr ax _ (i + 1) (by omega), (restr_trace δ b Pb tr chals pubs ⟨i, hi⟩ hj).2, hnode, pow_succ']
  · have hm := (CellTwinKW.cellHQKW_masks δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs _ hbind hinj ⟨i, hi⟩).1
    have e : (hqkEF b Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs) ⟨i, hi⟩).trace Cell.isF =
        vM tr ax Pb.orbitC.ω i Cell.isF := by
      rw [vM_base tr ax _ i (by decide), ← hnode ⟨i, hi⟩]
      simp only [hqkEF, Reify.envOfTrace]
      rw [dif_pos (by rw [CellTwinKW.cellChipHQKW_width]; decide)]
      rfl
    rw [← e, hm]
  · have hm := (CellTwinKW.cellHQKW_masks δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs _ hbind hinj ⟨i, hi⟩).2
    have e : (hqkEF b Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs) ⟨i, hi⟩).trace Cell.isL =
        vM tr ax Pb.orbitC.ω i Cell.isL := by
      rw [vM_base tr ax _ i (by decide), ← hnode ⟨i, hi⟩]
      simp only [hqkEF, Reify.envOfTrace]
      rw [dif_pos (by rw [CellTwinKW.cellChipHQKW_width]; decide)]
      rfl
    rw [← e, hm]
    simp only
    congr 1
    apply propext; omega

/-- The rows of the cell table are read off the row values `vM`. -/
theorem b0_of_canon {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {c : P8PublicClaim}
    {tr : TrJ8 (ZMod p)} (ax : AuxP1 (ZMod p)) (chals pubs : ℕ → K) :
    ∀ i (hi : i < (cellTableOf δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals pubs
      (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals pubs
        (qM δ b (canonPb hpG sz c) tr chals pubs))).length),
      ((cellTableOf δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals pubs
        (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC chals
          pubs (qM δ b (canonPb hpG sz c) tr chals pubs)))[i]'hi).b0 =
        cellB0Of (envAt (vM tr ax (canonPb hpG sz c).orbitC.ω) i) := by
  set Pb := canonPb hpG sz c with hPb
  intro i hi
  have hi' : i < Pb.nC := by simpa [cellTableOf] using hi
  simp only [cellTableOf, List.getElem_ofFn]
  refine cellB0Of_congr (fun j hj => ?_)
  show (cellEnvF b Pb.nodesC Pb.orbitC chals pubs _ ⟨i, hi'⟩).trace j = vM tr ax Pb.orbitC.ω i j
  rw [vM_base tr ax _ i (by omega)]
  exact (restr_trace δ b Pb tr chals pubs ⟨i, hi'⟩ hj).1

/-- Two traces with equal round-0 cell columns have equal cell rows. -/
theorem b0_eq_of_r0M (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)} (chals pubs chals' pubs' : ℕ → K)
    (hr : ∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    (cellTableOf δ b Pb.nodesC Pb.orbitC chals pubs
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs))).map (·.b0) =
    (cellTableOf δ b Pb.nodesC Pb.orbitC chals' pubs'
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals' pubs' (qM δ b Pb tr' chals' pubs'))).map (·.b0) := by
  simp only [cellTableOf, List.map_ofFn]
  congr 1
  funext i
  refine cellB0Of_congr (fun j hj => ?_)
  show (cellEnvF b Pb.nodesC Pb.orbitC chals pubs _ i).trace j = (cellEnvF b Pb.nodesC Pb.orbitC chals' pubs' _ i).trace j
  rw [(restr_trace δ b Pb tr chals pubs i hj).1, (restr_trace δ b Pb tr' chals' pubs' i hj).1]
  exact hr ⟨j, by omega⟩ (by simp; omega) i

end Inst

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1.nounLink_of_table
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1.serial_inj_table
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1.tableM_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1.b0_of_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1.b0_eq_of_r0M
