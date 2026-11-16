/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomRun.lean

* `atomRun_args`: the arguments `genJ9AX` feeds to `atomGenE` are `ptrP P DA.acs DA.rows`, `DA.acs`, `DA.info`,
    `DA.mb`, `DA.mxA`, `DA.mhA` (`DA := j9aDataOf P Rg Rt hgen`);
  * `recJ9AX_A`, `recJ9AX_pubsA`, `recJ9AX_A_eq`: `I.A = chipOf (atomGenE …).1`, `I.M.pubsA = (atomGenE …).2`;
  * **`genJ9AX_atom_n`**: `I.A.n = DA.acs.length`;
  * **`genJ9AX_atom_cols`**: at any orbit `o` with `Injective (powN o |acs|)`, `I.A.cols c i = fullCol hA (colA …) c i`;
  * **`genJ9AX_atom_pubs`**: `K3.toK (I.M.pubsA j) = pubsAOf … DA hA o (toχ χe) j`;
  * **`genJ9AX_atom_interp`** (generic chip `q` with `q.cols = I.A.cols` up to `Fin.cast`; `q := I.A` is the plain form):
    `interpOf q j = trAOf deltaF powerBasis3 DA hA (mkOrbit q ho) (toχ χe) ⟨j, hj⟩`.

  Statement note: the three lemmas that use `GenHyp` carry the binder `hN : DA.rows.size ≤ 2 ^ 31`
  (`ComplJ9ATables.rows_leA` derives it from `Rows31 DA`), as `ComplJ9ATables.genHyp_mbXA` needs.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow (nodesOf_powN)
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.V1J9A.GenJ9AX (recJ9AX recJ9AXRn)
open Nock.V1J9.Gen9 (mbCounts9)

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRun

/-! ## 1. The executable arguments of `atomGenE` in `recJ9AX` -/

/-- The cell list of the run. -/
abbrev csR (s f r : Noun) (t : NTree SkelX) : List Noun :=
  cellsOfRoots (rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t))

/-- The executable pointer. -/
abbrev ptR (s f r : Noun) (t : NTree SkelX) : Noun → ℕ :=
  ptrE (GenPortJ9.acsRun s f r t) (stopEdges (ComplJ8Data.rowsOfT t))

/-- The executable root-index function. -/
abbrev rIAR (acsL : List Noun) : Noun → ℕ :=
  fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n

/-- The executable atom-walk rows `vs`. -/
abbrev vsR (s f r : Noun) (t : NTree SkelX) : List WRow :=
  (let reads := pairReads (hdlB (csR s f r t) (GenPortJ9.acsRun s f r t))
      (HonestPairX.pdX (sxE (ptR s f r t))) (ComplJ8Data.rowsOfT t) ++
      ComplJ9AChainsRun.axReadsK9 P (ComplJ9AGen.rowsOfT9 t)
    if reads.isEmpty then ([], 0) else walkGen padN reads).1

/-- The atom table's arguments, written out over the run. -/
abbrev agR (s f r : Noun) (t : NTree SkelX) (χe : CoinsE) : Array (Array (ZMod P)) × (ℕ → K3) :=
  atomGenE (ptR s f r t) χe (GenPortJ9.acsRun s f r t)
    (infoOfE (GenPortJ9.acsRun s f r t) (ptR s f r t) (ComplJ8Data.rowsOfT t))
    (mbCounts9 (GenPortJ9.acsRun s f r t) (csR s f r t) ⟨s, f, r⟩)
    (wCounts (rIAR (GenPortJ9.acsRun s f r t)) (GenPortJ9.acsRun s f r t) (vsR s f r t))
    (wCounts (rIAR (GenPortJ9.acsRun s f r t)) (GenPortJ9.acsRun s f r t) (vsR s f r t))

theorem recJ9AX_A (s f r : Noun) (t : NTree SkelX) (χe : CoinsE) :
    (recJ9AX s f χe t r).A = chipOf (agR s f r t χe).1 := rfl

theorem recJ9AX_pubsA (s f r : Noun) (t : NTree SkelX) (χe : CoinsE) :
    (recJ9AX s f χe t r).M.pubsA = (agR s f r t χe).2 := rfl

section Run
variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => ComplJ9ADataRec.j9aDataOf P Rg Rt hgen
local notation "DD" => ComplJ8Data.j8DataOf P Rg Rt hgen

/-- **The arguments are `DA`'s.** -/
theorem atomRun_args (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) :
    agR s f r t χe =
      atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := GenPortJ9A.genJ9AX_data (p := P) Rt hgen rfl hnc χe
  have h6' : wCounts (rIAR (GenPortJ9.acsRun s f r t)) (GenPortJ9.acsRun s f r t) (vsR s f r t) = (DA).mxA := h6
  have h7' : wCounts (rIAR (GenPortJ9.acsRun s f r t)) (GenPortJ9.acsRun s f r t) (vsR s f r t) = (DA).mhA := h7
  obtain ⟨hpt, hinfo, -⟩ := GenPortJ9.genJ9A_pointer_data (p := P) Rt hgen rfl hnc
  have hacs : GenPortJ9.acsRun s f r t = (DA).acs :=
    (ComplJ9BClosed.genJ9A_data (p := P) Rt hgen rfl hnc).2.2
  have hcs : csR s f r t = (DA).cells :=
    (ComplJ9BClosed.genJ9A_data (p := P) Rt hgen rfl hnc).2.1
  have hmb : mbCounts9 (GenPortJ9.acsRun s f r t) (csR s f r t) ⟨s, f, r⟩ = (DA).mb := by
    rw [hacs, hcs, ← ComplJ9BOf.mbCountsP9_gen]
    exact (ComplJ9BOf.j9_mb_eq (p := P) Rg Rt hgen).symm
  have hpt' : ptR s f r t = ComplJ8Data.ptrP P (DA).acs (DA).rows := funext hpt
  have hmh : (DA).mhA = (DA).mxA := h7'.symm.trans h6'
  have e : (DD).info = (DA).info := rfl
  unfold agR
  rw [hinfo, hmb, h6', hpt', hacs, e, hmh]

theorem atom_chip (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) :
    (recJ9AX s f χe t r).A =
      chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1 := by
  rw [recJ9AX_A, atomRun_args Rt hgen hnc]

/-- **`genJ9AX_atom_n`**: the executable atom chip has one row per atom cell. -/
theorem genJ9AX_atom_n (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) :
    (recJ9AX s f χe t r).A.n = (DA).acs.length := by
  rw [atom_chip Rt hgen hnc χe]
  exact atomGenE_size (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA

theorem chipOf_cols (tbl : Array (Array (ZMod P))) (q : ChipIn) (hq : q = chipOf tbl) (c : ℕ) (i : Fin q.n) :
    q.cols c i = (tbl.getD i #[]).getD c 0 := by
  subst hq
  rfl

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [instFR : Fact (ringChar (ZMod P)).Prime] [instAR : Algebra (ZMod (ringChar (ZMod P))) KC]

/-- The honest atom columns (`fullCol` of `colA`) at `DA`, orbit `o`, coin `χe`. -/
noncomputable abbrev colAF (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) (χe : CoinsE) :
    ℕ → Fin (DA).acs.length → ZMod P :=
  fun c i => fullCol hA (HonestA8.colA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o
    (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (ComplJ8Of.pubsAOf deltaF powerBasis3 (DA) hA o (toχ χe))
    (ComplJ8Of.colAH deltaF powerBasis3 (DA) hA o (toχ χe) (ComplJ8Of.pubsAOf deltaF powerBasis3 (DA) hA o (toχ χe)))
    (ComplJ8Of.newBA (DA))) c i

/-- **`genJ9AX_atom_cols`**: the executable atom table is the honest `fullCol` at every orbit `o` with injective
nodes (all `349` columns). -/
theorem genJ9AX_atom_cols (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DA).acs.length))
    (i : Fin (recJ9AX s f χe t r).A.n) (c : ℕ) (hc : c < 349) :
    (recJ9AX s f χe t r).A.cols c i = colAF Rt hgen hA o χe c (Fin.cast (genJ9AX_atom_n Rt hgen hnc χe) i) := by
  have hacs : (DA).acs = ComplJ8Data.acsP P (DA).bigs (DA).dupP := rfl
  have hinfo : (DA).info = ComplJ8Data.infoOfP P (DA).acs (DA).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DA).bigs (DA).dupP (DA).rows (DA).mb := ComplJ9ATables.genHyp_mbXA Rg Rt hgen hN
  have key := atomGenE_cols (DA) hacs hinfo hg χe hA o hinj (Fin.cast (genJ9AX_atom_n Rt hgen hnc χe) i) c hc
  refine Eq.trans ?_ key
  exact chipOf_cols _ _ (atom_chip Rt hgen hnc χe) c i

/-- **`genJ9AX_atom_pubs`**: the executable atom publics are the honest `pubsAOf` at every orbit `o` with
injective nodes. -/
theorem genJ9AX_atom_pubs (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DA).acs.length)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsA j) = ComplJ8Of.pubsAOf deltaF powerBasis3 (DA) hA o (toχ χe) j := by
  have hacs : (DA).acs = ComplJ8Data.acsP P (DA).bigs (DA).dupP := rfl
  have hinfo : (DA).info = ComplJ8Data.infoOfP P (DA).acs (DA).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DA).bigs (DA).dupP (DA).rows (DA).mb := ComplJ9ATables.genHyp_mbXA Rg Rt hgen hN
  rw [recJ9AX_pubsA, atomRun_args Rt hgen hnc]
  exact atomGenE_pubs (DA) hacs hinfo hg χe hA o hinj j

/-- **`genJ9AX_atom_interp`** (corrected form, generic chip): a chip `q` with the columns of `I.A` (up to
`Fin.cast`) interpolates, at its own orbit `mkOrbit q ho`, to the honest atom trace `trAOf` re-instantiated there.
`q := I.A` (`hqn = rfl`, `hqc = fun _ _ => rfl`) is the plain statement. -/
theorem genJ9AX_atom_interp (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length)
    (q : ChipIn) (hqn : q.n = (recJ9AX s f χe t r).A.n)
    (hqc : ∀ c i, q.cols c i = (recJ9AX s f χe t r).A.cols c (Fin.cast hqn i))
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (DA) hA (mkOrbit q ho) (toχ χe) ⟨j, hj⟩ := by
  have e : q.n = (DA).acs.length := hqn.trans (genJ9AX_atom_n Rt hgen hnc χe)
  have hinj' : Function.Injective (ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length) := by
    intro a b hab
    have h1 : nodesOf q (Fin.cast e.symm a) = nodesOf q (Fin.cast e.symm b) := by
      rw [nodesOf_powN q ho]
      exact hab
    have h2 := hinj h1
    have h3 : ((Fin.cast e.symm a : Fin q.n) : ℕ) = ((Fin.cast e.symm b : Fin q.n) : ℕ) := congrArg Fin.val h2
    exact Fin.ext h3
  obtain ⟨gG, hgG⟩ : ∃ g : Fin (DA).acs.length → ZMod P, g = colAF Rt hgen hA (mkOrbit q ho) χe j :=
    ⟨_, rfl⟩
  have hcols : ∀ i : Fin q.n, q.cols j i = gG (Fin.cast e i) := by
    intro i
    rw [hqc, hgG]
    exact genJ9AX_atom_cols Rt hgen hnc χe hN hA (mkOrbit q ho) hinj' (Fin.cast hqn i) j hj
  have hn : nodesOf q = fun i : Fin q.n => ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length (Fin.cast e i) :=
    funext fun i => (congrFun (nodesOf_powN q ho) i).trans rfl
  show Lagrange.interpolate Finset.univ (nodesOf q) (fun i => q.cols j i) = _
  rw [hn, show (fun i => q.cols j i) = fun i : Fin q.n => gG (Fin.cast e i) from funext hcols]
  refine (interp_cast e (ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length) gG).trans ?_
  subst hgG
  rfl

end Run

#print axioms recJ9AX_A
#print axioms recJ9AX_pubsA
#print axioms atomRun_args
#print axioms atom_chip
#print axioms genJ9AX_atom_n
#print axioms chipOf_cols
#print axioms genJ9AX_atom_cols
#print axioms genJ9AX_atom_pubs
#print axioms genJ9AX_atom_interp

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRun
