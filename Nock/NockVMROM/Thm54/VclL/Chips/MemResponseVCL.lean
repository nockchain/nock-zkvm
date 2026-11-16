/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemResponseVCL.lean

  **1829, 1837–1839): `response_sound` of `vclMemFamily`.**
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Nock.NockVMROM.Thm54.RecordCarrier
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. `natLift` of a lifted base-field value is `natOf` -/

section NatLiftQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem ringChar_quad_eq : ringChar (Quad (algebraMap F K δF)) = ringChar F := by
  rw [← Algebra.ringChar_eq F (Quad (algebraMap F K δF))]

/-- **`natLift (liftQ x) = natOf x`** (under `PrimeFieldElems`): the record's integer entries
(`idx`, `acc`, `rootIdx`) read back as the chip's serials. -/
theorem natLift_liftQ (hF : GeneratedField.PrimeFieldElems F) (x : F) :
    natLift (liftQ (K := K) δF x) = natOf x := by
  obtain ⟨hlt, hc⟩ := natOf_spec hF x
  have : liftQ (K := K) δF x = ((natOf x : ℕ) : Quad (algebraMap F K δF)) := by
    conv_lhs => rw [← hc]
    simp [liftQ]
  rw [this, natLift_natCast (by rw [ringChar_quad_eq]; exact hlt)]

end NatLiftQ

/-! ## 2. The record entries -/

section Entries
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (eK : Env K) (eF : Env F)

theorem vKeyP_fp : RV.fpAt (keyVec δF 5 Cell.vKeyP eK eF) 0 (by omega) = (QFP.var Cell.pR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Cell.vKeyP, QFP.var, QFP.entries, QFP.ev]

theorem vKeyP_idx : keyVec δF 5 Cell.vKeyP eK eF 4 = liftQ (K := K) δF (eF.trace Cell.idx) := by
  simp [keyVec, Cell.vKeyP, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]

theorem xKeyS_p (s : F) : RV.fpAt (keyVec δF 11 (Cell.xKeyS s) eK eF) 0 (by omega) =
    (QFP.var Cell.pR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries, QFP.ev]

theorem xKeyS_l (s : F) : RV.fpAt (keyVec δF 11 (Cell.xKeyS s) eK eF) 3 (by omega) =
    (QFP.var Cell.lR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries, QFP.ev]

theorem xKeyS_r (s : F) : RV.fpAt (keyVec δF 11 (Cell.xKeyS s) eK eF) 6 (by omega) =
    (QFP.var Cell.rR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries, QFP.ev]

theorem xKeyS_idx (s : F) : keyVec δF 11 (Cell.xKeyS s) eK eF 9 = liftQ (K := K) δF (eF.trace Cell.idx) := by
  simp [keyVec, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]

theorem xKeyS_side (s : F) : keyVec δF 11 (Cell.xKeyS s) eK eF 10 = liftQ (K := K) δF s := by
  simp [keyVec, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cst]

theorem pRec_root : RV.fpAt (keyVec δF 8 Path.pRec eK eF) 0 (by omega) = (QFP.var Path.rootR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Path.pRec, QFP.var, QFP.entries, QFP.ev]

theorem pRec_child : RV.fpAt (keyVec δF 8 Path.pRec eK eF) 3 (by omega) = (Path.child (F := F)).ev δF eK eF := by
  simp [RV.fpAt, keyVec, Path.pRec, QFP.var, QFP.entries, QFP.ev]

theorem pRec_acc : keyVec δF 8 Path.pRec eK eF 6 = liftQ (K := K) δF (eF.trace Path.acc) := by
  simp [keyVec, Path.pRec, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]

theorem pRec_rootIdx : keyVec δF 8 Path.pRec eK eF 7 = liftQ (K := K) δF (eF.trace Path.rootIdx) := by
  simp [keyVec, Path.pRec, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]

end Entries

/-! ## 3. The provider keys read B0 entries only -/

section KeyCongr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs chals' pubs' : ℕ → K)
  {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X])

theorem cellEnvF_trace_congr {B : ℕ} (hB : B ≤ w) (hB' : B ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < B), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) (i : Fin n) :
    ∀ j < B, (cellEnvF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals' pubs' Q' i).trace j := by
  intro j hj
  rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
    hQ j hj]

theorem pathEnvF_trace_congr {B : ℕ} (hB : B ≤ w) (hB' : B ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < B), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) (i : ℕ) :
    ∀ j < B, (pathEnvF b hn nodes orbit chals pubs Q i).trace j =
      (pathEnvF b hn nodes orbit chals' pubs' Q' i).trace j := by
  intro j hj
  unfold pathEnvF
  rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
    hQ j hj]

section Cell129
variable (hw : 129 ≤ w) (hw' : 129 ≤ w')
  (hQ : ∀ (j : ℕ) (hj : j < 129), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
include hw hw' hQ

theorem cVRec_keys_congr :
    (cVRec δF b nodes orbit chals pubs Q).map (fun r => RV.validKey r.1) =
      (cVRec δF b nodes orbit chals' pubs' Q').map (fun r => RV.validKey r.1) := by
  unfold cVRec
  simp only [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, RV.validKey]
  have e : (4 : Fin 5) = 4 := rfl
  rw [vKeyP_idx, vKeyP_idx, cellEnvF_trace_congr b nodes orbit chals pubs chals' pubs' Q Q' hw hw' hQ i
    Cell.idx (by decide)]

theorem cXRec_keys_congr :
    (cXRec δF b nodes orbit chals pubs Q).map (fun r => RV.exportKey r.1) =
      (cXRec δF b nodes orbit chals' pubs' Q').map (fun r => RV.exportKey r.1) := by
  unfold cXRec
  simp only [List.map_flatMap, List.map_cons, List.map_nil]
  refine List.flatMap_congr fun i _ => ?_
  simp only [RV.exportKey, xKeyS_idx, xKeyS_side, RV.sideOf]
  rw [cellEnvF_trace_congr b nodes orbit chals pubs chals' pubs' Q Q' hw hw' hQ i Cell.idx (by decide)]

end Cell129

theorem pPRec_keys_congr (hw16 : 16 ≤ w) (hw16' : 16 ≤ w')
    (hQ16 : ∀ (j : ℕ) (hj : j < 16), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    (pPRec δF b hn nodes orbit chals pubs Q).map (fun r => RV.pathKey r.1) =
      (pPRec δF b hn nodes orbit chals' pubs' Q').map (fun r => RV.pathKey r.1) := by
  have hE := fun j => pathEnvF_trace_congr b hn nodes orbit chals pubs chals' pubs' Q Q' hw16 hw16' hQ16 j
  unfold pPRec
  rw [List.filter_congr (fun j _ => by rw [hE j Path.last (by decide)])]
  simp only [List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, RV.pathKey, pRec_acc, pRec_rootIdx]
  rw [hE j Path.acc (by decide), hE j Path.rootIdx (by decide)]

end KeyCongr

/-! ## 4. The genuine rows of an accepted cell table -/

section CellRows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → F[X])

/-- **Every row of an accepted cell table is genuine**: its serial decodes (through any `dn` that
agrees with the B0 decode on bounded nouns) to a cell `[L R]` whose fingerprints are the row's
`p`, `l`, `r`. -/
theorem cell_rows_genuine (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    {vl : List (VKey (Quad (algebraMap F K δF)))}
    (hacc : TableAccepts (Quad.mk (algebraMap F K δF) (chals 2) (chals 3))
      (cellTableOf δF b nodes orbit chals pubs Q) vl)
    (dn : ℕ → Noun)
    (hdn : ∀ idx m, preZNounOfTable ((cellTableOf δF b nodes orbit chals pubs Q).map (·.b0)) idx = some m →
      m.leaves ≤ fuelChip → dn idx = m) (i : Fin n) :
    ∃ L R, dn (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) = .cell L R ∧
      (QFP.var Cell.pR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) =
        GlobalCarryRecognizer.enc (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) (.cell L R) ∧
      (QFP.var Cell.lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) =
        GlobalCarryRecognizer.enc (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) L ∧
      (QFP.var Cell.rR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) =
        GlobalCarryRecognizer.enc (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) R := by
  have hmem : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i) ∈
      cellTableOf δF b nodes orbit chals pubs Q := List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨L, R, hd, hp, hl, hr, -⟩ := row_genuine hq hz hacc hmem
  obtain ⟨m, hm, hpm, -, hlv, -⟩ := preZNounOfTable_sound hq hz hacc _ hmem
  have hmc : m = .cell L R := by
    rw [hd] at hm; exact (Option.some.inj hm).symm
  subst hmc
  exact ⟨L, R, hdn _ _ hd hlv, hp, hl, hr⟩

end CellRows

/-! ## 5. A path record is genuine -/

section PathGenuine
variable {q : ℕ} {F : Type} [Field F] [DecidableEq F] {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp]
  [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- **One accepted row, through `dn`**: the serial of any row of an accepted table decodes to a cell
`[L R]` with the row's fingerprints. -/
theorem row_dn (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {c : CellRow q Kfp} (hc : c ∈ t) (dn : ℕ → Noun)
    (hdn : ∀ idx m, preZNounOfTable (t.map (·.b0)) idx = some m → m.leaves ≤ fuelChip → dn idx = m) :
    ∃ L R, preZNounOfTable (t.map (·.b0)) c.b0.idx = some (.cell L R) ∧ dn c.b0.idx = .cell L R ∧
      c.p = GlobalCarryRecognizer.enc z (.cell L R) ∧
      c.l = GlobalCarryRecognizer.enc z L ∧ c.r = GlobalCarryRecognizer.enc z R := by
  obtain ⟨L, R, hd, hp, hl, hr, -⟩ := row_genuine hq hz h hc
  obtain ⟨m, hm, -, -, hlv, -⟩ := preZNounOfTable_sound hq hz h _ hc
  have hmc : m = .cell L R := by
    rw [hd] at hm; exact (Option.some.inj hm).symm
  subst hmc
  exact ⟨L, R, hd, hdn _ _ hd hlv, hp, hl, hr⟩

/-- **A path record row is genuine** (T3 at the path chip): given every path row's edge exported by
the cell table (`hexp`) and the chain facts of `path_records_of_chip` at the record row `e`, outside
the census and dyck-root events, the root serial decodes to `rt` with the record's root fingerprint
`enc rt`, and the record's child is the fingerprint of `rt`'s subtree at the record's axis. -/
theorem path_record_genuine (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (t.map (·.b0)))
    (dn : ℕ → Noun)
    (hdn : ∀ idx m, preZNounOfTable (t.map (·.b0)) idx = some m → m.leaves ≤ fuelChip → dn idx = m)
    (rows : ℕ → PathRow F Kfp) (cidx : F → ℕ) (nP : ℕ)
    (hexp : ∀ j < nP, EdgeExported t
      ⟨(rows j).p, (rows j).l, (rows j).r, (rows j).sideB, cidx (rows j).cellIdx⟩)
    (e s k : ℕ) (hesk : e = s + k) (hen : e < nP)
    (hroot : (rows e).root = (rows s).p) (hidx : (rows e).rootIdx = (rows s).cellIdx)
    (hend : chainEnd (rows s).p (edges rows cidx s k) = some (rows e).child) :
    ∃ rt nn, dn (cidx (rows e).rootIdx) = rt ∧ (rows e).root = GlobalCarryRecognizer.enc z rt ∧
      (rows e).child = GlobalCarryRecognizer.enc z nn ∧
      Noun.slot (axisFold (sides rows s k)) rt = some nn := by
  have hexpE : ∀ ed ∈ edges rows cidx s k, EdgeExported t ed := by
    intro ed hed
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hed
    exact hexp (s + j) (by have := List.mem_range.mp hj; omega)
  obtain ⟨c, hc, hci, hcp, -, -⟩ := hexp s (by omega)
  obtain ⟨L, R, hdec, hdcn, hp, -, -⟩ := row_dn hq hz h hc dn hdn
  have hpe : (rows s).p = GlobalCarryRecognizer.enc z (.cell L R) := by
    have : c.p = (rows s).p := hcp
    rw [← this]; exact hp
  rw [hpe] at hend
  obtain ⟨nn, hnn, hslot⟩ := chain_sound_outside hq hz h [] hT2 hdy hdec _ hexpE hend
  have hsd : (edges rows cidx s k).map Edge.side = sides rows s k := by
    simp [edges, sides, List.map_map, Function.comp_def]
  rw [hsd] at hslot
  have hci' : c.b0.idx = cidx (rows s).cellIdx := hci
  refine ⟨.cell L R, nn, ?_, by rw [hroot, hpe], hnn.symm ▸ ?_, hslot⟩
  · rw [hidx, ← hci']; exact hdcn
  · exact rfl
  
end PathGenuine

/-! ## 6. The three accumulators' providers are genuine -/

section Providers
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → F[X])
  (z : Quad (algebraMap F K δF)) (dnn : ℕ → Noun) (hF : GeneratedField.PrimeFieldElems F)
  (SR SD : RV.KeyVCL → Noun) (SK : List RV.KeyVCL)
include hF

/-- **Validity providers** (`a = 0`): key `valid idx`, root = child = `enc z (dnn idx)`, axis `1`. -/
theorem valid_records_sound
    (G : ∀ i : Fin n, ∃ L R, dnn (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) = .cell L R ∧
      (QFP.var Cell.pR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) = GlobalCarryRecognizer.enc z (.cell L R))
    (hSR : ∀ i, SR (.valid i) = dnn i) (hSD : ∀ i, SD (.valid i) = dnn i)
    (hSK : ∀ r ∈ cVRec δF b nodes orbit chals pubs Q, RV.validKey r.1 ∈ SK) :
    ∀ r ∈ cVRec δF b nodes orbit chals pubs Q,
      RV.validKey r.1 ∈ SK ∧ RV.validRoot r.1 = GlobalCarryRecognizer.enc z (SR (RV.validKey r.1)) ∧
      RV.validRoot r.1 = GlobalCarryRecognizer.enc z (SD (RV.validKey r.1)) ∧
      Noun.slot 1 (SR (RV.validKey r.1)) = some (SD (RV.validKey r.1)) := by
  intro r hr
  refine ⟨hSK r hr, ?_⟩
  unfold cVRec at hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  obtain ⟨L, R, hd, hp⟩ := G i
  have hk : RV.validKey (keyVec δF 5 Cell.vKeyP (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i)) =
      .valid (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) := by
    simp only [RV.validKey, vKeyP_idx, natLift_liftQ δF hF]
  have hr0 : RV.validRoot (keyVec δF 5 Cell.vKeyP (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i)) = GlobalCarryRecognizer.enc z (.cell L R) := by
    rw [RV.validRoot, vKeyP_fp]; exact hp
  simp only [hk, hSR, hSD, hd, hr0]
  exact ⟨trivial, trivial, by simp [Noun.slot]⟩

/-- **Export providers** (`a = 1`): two per row; key `export idx side`, root `enc (dnn idx)`, child the
side's subtree, axis `2 / 3`. -/
theorem export_records_sound
    (G : ∀ i : Fin n, ∃ L R, dnn (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) = .cell L R ∧
      (QFP.var Cell.pR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) = GlobalCarryRecognizer.enc z (.cell L R) ∧
      (QFP.var Cell.lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) = GlobalCarryRecognizer.enc z L ∧
      (QFP.var Cell.rR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
          (cellEnvF b nodes orbit chals pubs Q i) = GlobalCarryRecognizer.enc z R)
    (hSR : ∀ i s, SR (.export i s) = dnn i) (hSD : ∀ i s, SD (.export i s) = sideChild s (dnn i))
    (hSK : ∀ r ∈ cXRec δF b nodes orbit chals pubs Q, RV.exportKey r.1 ∈ SK) :
    ∀ r ∈ cXRec δF b nodes orbit chals pubs Q,
      RV.exportKey r.1 ∈ SK ∧ RV.exportRoot r.1 = GlobalCarryRecognizer.enc z (SR (RV.exportKey r.1)) ∧
      RV.exportChild r.1 = GlobalCarryRecognizer.enc z (SD (RV.exportKey r.1)) ∧
      Noun.slot (RV.exportAxis r.1) (SR (RV.exportKey r.1)) = some (SD (RV.exportKey r.1)) := by
  intro r hr
  refine ⟨hSK r hr, ?_⟩
  unfold cXRec at hr
  obtain ⟨i, -, hri⟩ := List.mem_flatMap.mp hr
  obtain ⟨L, R, hd, hp, hl, hrr⟩ := G i
  have h0 : (0 : Quad (algebraMap F K δF)) ≠ 1 := zero_ne_one
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hri
  rcases hri with rfl | rfl
  · have hsd : RV.sideOf (keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) = false := by
      simp [RV.sideOf, xKeyS_side, liftQ, h0]
    have hk : RV.exportKey (keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) =
        .export (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) false := by
      simp only [RV.exportKey, xKeyS_idx, natLift_liftQ δF hF, hsd]
    simp only [hk, hSR, hSD, hd, RV.exportRoot, RV.exportChild, RV.exportAxis, hsd, xKeyS_p, xKeyS_l, hp, hl,
      sideChild, if_false, Bool.false_eq_true]
    exact ⟨trivial, trivial, by simp [Noun.slot]⟩
  · have hsd : RV.sideOf (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) = true := by
      simp [RV.sideOf, xKeyS_side, liftQ]
    have hk : RV.exportKey (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) =
        .export (natOf ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.idx)) true := by
      simp only [RV.exportKey, xKeyS_idx, natLift_liftQ δF hF, hsd]
    simp only [hk, hSR, hSD, hd, RV.exportRoot, RV.exportChild, RV.exportAxis, hsd, xKeyS_p, xKeyS_r, hp, hrr,
      sideChild, if_true]
    exact ⟨trivial, trivial, by simp [Noun.slot]⟩

/-- **Path providers** (`a = 2`): the `last` rows; key `path rootIdx acc`, root `enc (dnn rootIdx)`, child
the subtree at the axis `acc`. -/
theorem path_records_sound (hnn : 0 < n)
    (G : ∀ e < n, (pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.last = 1 →
      ∃ rt nn, dnn (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.rootIdx)) = rt ∧
        (QFP.var Path.rootR : QFP F).ev δF (pathEnvK δF b hnn nodes orbit chals pubs Q e)
          (pathEnvF b hnn nodes orbit chals pubs Q e) = GlobalCarryRecognizer.enc z rt ∧
        (Path.child : QFP F).ev δF (pathEnvK δF b hnn nodes orbit chals pubs Q e)
          (pathEnvF b hnn nodes orbit chals pubs Q e) = GlobalCarryRecognizer.enc z nn ∧
        Noun.slot (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.acc)) rt = some nn)
    (hSR : ∀ ri ax, SR (.path ri ax) = dnn ri)
    (hSD : ∀ ri ax, SD (.path ri ax) = (Noun.slot ax (dnn ri)).getD (.atom 0))
    (hSK : ∀ r ∈ pPRec δF b hnn nodes orbit chals pubs Q, RV.pathKey r.1 ∈ SK) :
    ∀ r ∈ pPRec δF b hnn nodes orbit chals pubs Q,
      RV.pathKey r.1 ∈ SK ∧ RV.pathRoot r.1 = GlobalCarryRecognizer.enc z (SR (RV.pathKey r.1)) ∧
      RV.pathChild r.1 = GlobalCarryRecognizer.enc z (SD (RV.pathKey r.1)) ∧
      Noun.slot (RV.pathAxis r.1) (SR (RV.pathKey r.1)) = some (SD (RV.pathKey r.1)) := by
  intro r hr
  refine ⟨hSK r hr, ?_⟩
  unfold pPRec at hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hen, hlast⟩ := List.mem_filter.mp he
  have hen' := List.mem_range.mp hen
  obtain ⟨rt, nn, hd, hroot, hchild, hslot⟩ := G e hen' (by simpa using hlast)
  have hk : RV.pathKey (keyVec δF 8 Path.pRec (pathEnvK δF b hnn nodes orbit chals pubs Q e)
      (pathEnvF b hnn nodes orbit chals pubs Q e)) =
      .path (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.rootIdx))
        (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.acc)) := by
    simp only [RV.pathKey, pRec_acc, pRec_rootIdx, natLift_liftQ δF hF]
  have hax : RV.pathAxis (keyVec δF 8 Path.pRec (pathEnvK δF b hnn nodes orbit chals pubs Q e)
      (pathEnvF b hnn nodes orbit chals pubs Q e)) =
      natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.acc) := by
    simp only [RV.pathAxis, pRec_acc, natLift_liftQ δF hF]
  have hsl : (Noun.slot (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.acc))
      (dnn (natOf ((pathEnvF b hnn nodes orbit chals pubs Q e).trace Path.rootIdx)))).getD (.atom 0) = nn := by
    rw [hd, hslot]; rfl
  rw [hk, hax, hSR, hSD, hsl, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [RV.pathRoot, pRec_root]; exact hroot
  · rw [RV.pathChild, pRec_child]; exact hchild
  · exact hslot

end Providers

/-! ## 7. `response_sound` -/

theorem round_path0 (hT hP j : ℕ) (hj : j < 16) :
    ((shapeV hT hP).table (tP hT hP)).colRound ⟨j, by show j < 112; omega⟩ = 0 := by
  show Chips.Path.colRoundT ⟨j, _⟩ = 0
  simp only [Chips.Path.colRoundT, show Chips.Path.b0Count = 16 from rfl]
  rw [if_pos hj]

section Response
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ} {C : TableSpec}
  (V : VerifierData F K hC (shapeV hT hP))

/-- **`response_sound` of `vclMemFamily`** (the four conjuncts at every committed provider record of
every accumulator).  Hypotheses are the field's: the request lists with their LogUp sums, the joint
weighted IO exclusion, the consumer count, and the summand exclusion. -/
theorem vcl_response_sound (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (χ : Coins frameVCL K) (Q : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X])
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j)))
    (Qc : Fin C.width → F[X])
    (reqs : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF)))
    (hsum : ∀ a, ((reqs a).map fun r =>
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum = ρ a)
    (hne : ∀ a, ∀ r ∈ reqs a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0)
    (hio : ∀ a, (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternal δF hT hP V Q a) (liftWts (vclResp δF hT hP V Q a)))
    (hcount : ∀ a, (reqs a ++ vclInternal δF hT hP V Q a).length < ringChar (Quad (algebraMap F K δF)))
    (hsumm : ∀ s ∈ vclSummands δF hT hP V (C := C) (), ¬ s.mem (Qc, Q) χ) :
    ∀ a, ∀ r ∈ (vclIoFacts h a).records,
      RV.keyVCL a r.1 ∈ vclServedKeys δF hT hP V (fun t => b0 (Q t)) ∧
      RV.rootVCL a r.1 = GlobalCarryRecognizer.enc ((seedSpecVCL (algebraMap F K δF)).seed χ)
        (vclServedRoot hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) ∧
      RV.childVCL a r.1 = GlobalCarryRecognizer.enc ((seedSpecVCL (algebraMap F K δF)).seed χ)
        (vclServed hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) ∧
      Noun.slot (RV.axisVCL a r.1) (vclServedRoot hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) =
        some (vclServed hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) := by
  obtain ⟨⟨hgC, hsC⟩, ⟨hgP, hsP⟩⟩ := vcl_accepted h
  have hadjC := hgC.adj
  have hinjC := hgC.2.1
  have hF := hgC.2.2.1
  have hq := hgC.2.2.2.1
  have hnC := hgC.2.2.2.2
  have hadjP := hgP.adj
  have hinjP := hgP.2.1
  have hnP := hgP.2.2.2.2
  -- the characteristic, the Algebra instance, primality
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar F := ringChar_quad_eq δF
  haveI hcp : CharP (Quad (algebraMap F K δF)) (ringChar F) := by
    rw [← hchar]; exact ringChar.charP _
  haveI : Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF)) := ZMod.algebra _ _
  haveI : Fact (ringChar F).Prime :=
    ⟨(CharP.char_is_prime_or_zero F (ringChar F)).resolve_right (by omega)⟩
  -- the seed outside the summands
  obtain ⟨hz0, hT2, hdy⟩ := vclSummands_good δF hT hP V () (Qc, Q) χ hsumm
  have hrows := rowsOfTr_eq δF hT hP V Qc Q ρ y χ
  rw [hrows] at hT2 hdy
  have hseed : (seedSpecVCL (algebraMap F K δF)).seed χ =
      Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3) := by
    simp [seedSpecVCL, chalsVCL, c2, c3]; rfl
  rw [hseed] at hz0 hT2 hdy
  simp only [hseed]
  -- the cell table accepts (the validity lookup, a = 0)
  have hhio0 := hio 0
  have hhio1 := hio 1
  have hacc : TableAccepts (Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3))
      (cellTableOf δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (QC δF hT hP ρ y V χ Q)) [] := by
    refine cellTable_accepts_of_lookup δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP))
      (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) hF hq hz0 hsC.1 hsC.2
      hinjC hadjC (by omega) _ _ (chalsVCL_ok δF χ 11) (reqs 0) ?_ (hne 0) ?_ ?_ ?_ []
    · rw [pubsC_01]; exact hsum 0
    · rw [cellVInternal_eq, cellVRecords_eq]
      exact fun hc => hhio0 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc))
    · rw [cellVInternal_eq, cellVRecords_eq]
      exact fun hc => hhio0 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))
    · rw [cellVInternal_eq, ← hchar]; exact hcount 0
  -- the B0 decode through `decodedNoun`
  have hrows' : cellRowsB0 hT hP V (fun t => b0 (Q t)) =
      (cellTableOf δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (QC δF hT hP ρ y V χ Q)).map (·.b0) := hrows
  have hdn : ∀ idx m, preZNounOfTable ((cellTableOf δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q)).map (·.b0)) idx = some m →
      m.leaves ≤ fuelChip → decodedNoun hT hP V (fun t => b0 (Q t)) idx = m := by
    intro idx m hm hl
    simp only [decodedNoun, hrows', hm, capN_of_le hl]
  have G0 := fun i => cell_rows_genuine δF V.basis (V.memNodes (tC hT hP))
    (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) hq hz0 hacc
    (decodedNoun hT hP V (fun t => b0 (Q t))) hdn i
  -- the path edges are exported (the export lookup, a = 1)
  have hexp := path_edges_exported δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
    (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
    (pubsP δF ρ y) (QC δF hT hP ρ y V χ Q) (QP δF hT hP ρ y V χ Q) hsC.1 hsC.2 hinjC hadjC hsP.1 hsP.2
    hinjP hadjP _ _ (chalsVCL_ok δF χ 11) (ρ 1) (by rw [pubsC_23, pubsP_01]) (reqs 1) (hsum 1) (hne 1)
    (by
      rw [pathXInternal_eq, cellXRecords_eq]
      exact fun hc => hhio1 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (by
      rw [pathXInternal_eq, cellXRecords_eq]
      exact fun hc => hhio1 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc))))
    (by rw [pathXInternal_eq, ← hchar]; exact hcount 1)
  -- every path record row is genuine
  have G2 : ∀ e < V.memRows (tP hT hP),
      (pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
        (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e).trace Path.last = 1 →
      ∃ rt nn, decodedNoun hT hP V (fun t => b0 (Q t))
          (natOf ((pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
            (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e).trace Path.rootIdx)) = rt ∧
        (QFP.var Path.rootR : QFP F).ev δF (pathEnvK δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP))
          (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e)
          (pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
            (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e) =
          GlobalCarryRecognizer.enc (Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3)) rt ∧
        (Path.child : QFP F).ev δF (pathEnvK δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP))
          (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e)
          (pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
            (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e) =
          GlobalCarryRecognizer.enc (Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3)) nn ∧
        Noun.slot (natOf ((pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
          (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e).trace Path.acc)) rt = some nn := by
    intro e he hl
    obtain ⟨s, k, hesk, -, hax, hroot, hidx, hend⟩ := path_records_of_chip δF V.basis (V.hM (tP hT hP))
      (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y)
      (QP δF hT hP ρ y V χ Q) hsP.1 hsP.2 hinjP hadjP hF hq (by omega) natOf e he hl
    obtain ⟨rt, nn, hd, hr, hc, hs⟩ := path_record_genuine hq hz0 hacc hT2 hdy
      (decodedNoun hT hP V (fun t => b0 (Q t))) hdn
      (pathRows δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q)) natOf (V.memRows (tP hT hP)) hexp
      e s k hesk he hroot hidx hend
    have hside := (pathLocal_of_chip δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP))
      (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) hsP.1 e he).side_bool
    refine ⟨rt, nn, hd, hr, ?_, ?_⟩
    · rw [child_ev δF _ _ hside]; exact hc
    · have hax' := hax
      change natOf ((pathEnvF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) e).trace Path.acc) = _ at hax'
      rw [hax']; exact hs
  -- the served keys contain the providers' keys (they read B0 entries only)
  have hbQ : ∀ (t : Fin (shapeV hT hP).k) (j : ℕ) (hj : j < ((shapeV hT hP).table t).width),
      ((shapeV hT hP).table t).colRound ⟨j, hj⟩ = 0 →
      Q t ⟨j, hj⟩ = bTr hT hP (fun t => b0 (Q t)) t ⟨j, hj⟩ :=
    fun t j hj h0 => (b0Trace_b0 (Q t) ⟨j, hj⟩ h0).symm
  intro a r hr
  rw [vclIoFacts_records h a] at hr
  match a with
  | 0 =>
    have hr' : r ∈ cVRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) := by
      rw [← cellVRecords_eq δF hT hP ρ y V χ Q] at hr; exact hr
    refine valid_records_sound δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) _ (decodedNoun hT hP V (fun t => b0 (Q t))) hF
      (vclServedRoot hT hP V (fun t => b0 (Q t))) (vclServed hT hP V (fun t => b0 (Q t)))
      (vclServedKeys δF hT hP V (fun t => b0 (Q t)))
      (fun i => by obtain ⟨L, R, hd, hp, -⟩ := G0 i; exact ⟨L, R, hd, hp⟩)
      (fun i => rfl) (fun i => rfl) ?_ r hr'
    intro r' hr''
    have hk : RV.validKey r'.1 ∈ (cVRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q)).map (fun r => RV.validKey r.1) :=
      List.mem_map_of_mem hr''
    rw [cVRec_keys_congr δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) 0 0 (QC δF hT hP ρ y V χ Q) (bTr hT hP (fun t => b0 (Q t)) (tC hT hP))
      (by rw [cellOk_w' δF hT hP ρ y V χ]; show 129 ≤ 225; omega) (show 129 ≤ 225 by omega)
      (fun j hj => hbQ (tC hT hP) j (by show j < 225; omega) (round_cell0 hT hP j hj))] at hk
    exact List.mem_append_left _ (List.mem_append_left _ hk)
  | 1 =>
    have hr' : r ∈ cXRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) := by
      rw [← cellXRecords_eq δF hT hP ρ y V χ Q] at hr; exact hr
    have hSKx : ∀ r' ∈ cXRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q), RV.exportKey r'.1 ∈
        vclServedKeys δF hT hP V (fun t => b0 (Q t)) := by
      intro r' hr''
      have hk : RV.exportKey r'.1 ∈ (cXRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
          (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q)).map (fun r => RV.exportKey r.1) :=
        List.mem_map_of_mem hr''
      rw [cXRec_keys_congr δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) 0 0 (QC δF hT hP ρ y V χ Q) (bTr hT hP (fun t => b0 (Q t)) (tC hT hP))
        (by rw [cellOk_w' δF hT hP ρ y V χ]; show 129 ≤ 225; omega) (show 129 ≤ 225 by omega)
        (fun j hj => hbQ (tC hT hP) j (by show j < 225; omega) (round_cell0 hT hP j hj))] at hk
      exact List.mem_append_left _ (List.mem_append_right _ hk)
    have hres := export_records_sound δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) _ (decodedNoun hT hP V (fun t => b0 (Q t))) hF
      (vclServedRoot hT hP V (fun t => b0 (Q t))) (vclServed hT hP V (fun t => b0 (Q t)))
      (vclServedKeys δF hT hP V (fun t => b0 (Q t))) G0 (fun i s => rfl) (fun i s => rfl) hSKx r hr'
    exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2⟩
  | 2 =>
    have hr' : r ∈ pPRec δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) := by
      rw [← pathPRecords_eq δF hT hP ρ y V χ Q] at hr; exact hr
    refine path_records_sound δF V.basis (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
      (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) _ (decodedNoun hT hP V (fun t => b0 (Q t))) hF
      (vclServedRoot hT hP V (fun t => b0 (Q t))) (vclServed hT hP V (fun t => b0 (Q t)))
      (vclServedKeys δF hT hP V (fun t => b0 (Q t))) (V.hM (tP hT hP)) G2 (fun ri ax => rfl)
      (fun ri ax => rfl) ?_ r hr'
    intro r' hr''
    have hk : RV.pathKey r'.1 ∈ (pPRec δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP))
        (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q)).map
        (fun r => RV.pathKey r.1) := List.mem_map_of_mem hr''
    rw [pPRec_keys_congr δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) 0 0 (QP δF hT hP ρ y V χ Q) (bTr hT hP (fun t => b0 (Q t)) (tP hT hP))
      (by rw [pathOk_w' δF hT hP ρ y V χ]; show 16 ≤ 112; omega) (show 16 ≤ 112 by omega)
      (fun j hj => hbQ (tP hT hP) j (by show j < 112; omega) (round_path0 hT hP j hj))] at hk
    exact List.mem_append_right _ hk

end Response

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
