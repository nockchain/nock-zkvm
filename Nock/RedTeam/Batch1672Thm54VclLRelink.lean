/-
  Nock/RedTeam/Batch1672Thm54VclLRelink.lean

  **The relinking NC at the chip model, ported to the real
  `FP` / `FP.cons` (T8).**

  The fixture tables are
  `CellRow 113 (ZMod 113)` checked against the PRODUCTION predicates `RowOK` / `SerialOK` /
  `ValidityBalanced` / `TableAccepts` of `P8Core/VclL/Table.lean`.

  * `honest_accepted` (the honest `x` table, serials `X 0, A 1, B 2, Dx 3, [0 0] 4`);
  * `forged_same_b0` / `relink_rejected`: the forgery re-links the post-seed fingerprints on the SAME
    round-0 table and is REJECTED (serial 1 provides `(fp A, 2, 1)`, row 0 consumes `(fp B, 2, 1)`);
  * NCs, each re-admitting the forgery with the same B0 and a different fingerprint served at one
    serial (so `served_of_b0`'s conclusion fails): `nc_zero_step_relink_accepted` (serial step
    `+1 → +0`), `nc_no_child_key_relink_accepted` (child serials out of the validity key),
    `nc_dup_serial_relink_accepted` (duplicated serials, threading gate off).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Table
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1672

open Nock Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)

abbrev F := ZMod 113
instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

def zz : F := 16
def zi : F := 106

theorem zinv : zz⁻¹ = zi := inv_eq_of_mul_eq_one_right (by decide)

/-- `FP.cons` at `zz` with the inverse as a literal (computable). -/
def consFix (l r : FP F) : FP F :=
  ⟨l.size * r.size, zz * l.dyck + l.size * l.size * zi + l.size * l.size * r.dyck,
    l.leaf + l.size * r.leaf⟩

theorem consFix_eq (l r : FP F) : consFix l r = FP.cons zz l r := by
  simp only [consFix, FP.cons, zinv]

/-- The fingerprint by `consFix` (= `enc zz` by `enc_cons`/`enc_atom`, `zz ≠ 0`). -/
def fpc : Noun → FP F
  | .atom a => FP.atomFP zz (a : F)
  | .cell l r => consFix (fpc l) (fpc r)

theorem fpc_eq_enc : ∀ n, fpc n = GlobalCarryRecognizer.enc zz n
  | .atom a => by rw [GlobalCarryRecognizer.enc_atom]; rfl
  | .cell l r => by
    rw [fpc, consFix_eq, fpc_eq_enc l, fpc_eq_enc r, GlobalCarryRecognizer.enc_cons (by decide)]

/-! ## The Bool row check and its soundness against `RowOK` -/

def rowOKb (c : CellRow 113 F) : Bool :=
  decide (c.p = consFix c.l c.r) && decide (c.b0.lo < 2 ^ 62) && decide (c.b0.loL < 2 ^ 62) &&
  decide (c.b0.loR < 2 ^ 62) && decide (c.b0.hi < 2 ^ 48) && decide (c.b0.hiL < 2 ^ 48) &&
  decide (c.b0.hiR < 2 ^ 48) && decide (c.b0.carry ≤ 1) &&
  decide ((c.b0.lo : F) + (c.b0.carry : F) * 2 ^ 62 = (c.b0.loL : F) + (c.b0.loR : F) + 1) &&
  decide ((c.b0.hi : F) = (c.b0.hiL : F) + (c.b0.hiR : F) + (c.b0.carry : F)) &&
  (c.b0.wL || decide (c.l = FP.atomFP zz c.b0.aL ∧ c.b0.loL = 0 ∧ c.b0.hiL = 0)) &&
  (c.b0.wR || decide (c.r = FP.atomFP zz c.b0.aR ∧ c.b0.loR = 0 ∧ c.b0.hiR = 0))

theorem rowOKb_sound {c : CellRow 113 F} (h : rowOKb c = true) : RowOK zz c := by
  simp only [rowOKb, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, hL⟩, hR⟩ := h
  refine ⟨by rw [hc, consFix_eq], h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, ?_⟩
  · intro hw
    rcases hL with hL | hL
    · rw [hw] at hL; exact absurd hL (by decide)
    · have e : algebraMap F F c.b0.aL = c.b0.aL := rfl
      rw [e]; exact hL
  · intro hw
    rcases hR with hR | hR
    · rw [hw] at hR; exact absurd hR (by decide)
    · have e : algebraMap F F c.b0.aR = c.b0.aR := rfl
      rw [e]; exact hR

theorem tableAccepts_of {t : List (CellRow 113 F)} {vl : List (VKey F)}
    (hs : SerialOK (t.map (·.b0))) (hr : t.all rowOKb = true) (hv : ValidityBalanced t vl) :
    TableAccepts zz t vl :=
  ⟨hs, fun c hc => rowOKb_sound (List.all_eq_true.mp hr c hc), hv.served⟩

/-! ## The fixture -/

def n0 : Noun := .atom 0
def n00 : Noun := .cell n0 n0
def nA : Noun := .cell n0 n00
def nB : Noun := .cell n00 n0
def nDx : Noun := .cell n0 nB
def nDy : Noun := .cell n0 nA
def nX : Noun := .cell nA nDx
def nY : Noun := .cell nB nDy

theorem relink_fp_collision : fpc nX = fpc nY := by decide
theorem relink_distinct : nX ≠ nY := by decide
theorem relink_enc_collision : GlobalCarryRecognizer.enc zz nX = GlobalCarryRecognizer.enc zz nY := by
  rw [← fpc_eq_enc, ← fpc_eq_enc, relink_fp_collision]

def a0 : FP F := FP.atomFP zz 0

/-- A row with `hi = 0` limbs, carry `0`. -/
def mkRow (idx idL idR : ℕ) (wL wR : Bool) (mu muL muR mv mx : ℕ) (p l r : FP F) : CellRow 113 F :=
  ⟨⟨idx, idL, idR, wL, wR, 0, 0, mu, 0, muL, 0, muR, 0, 0, mv, mx⟩, p, l, r⟩

def rowX : CellRow 113 F := mkRow 0 1 3 true true 6 2 3 1 1 (fpc nX) (fpc nA) (fpc nDx)
def rowA : CellRow 113 F := mkRow 1 0 4 false true 2 0 1 1 0 (fpc nA) a0 (fpc n00)
def rowB : CellRow 113 F := mkRow 2 4 0 true false 2 1 0 1 0 (fpc nB) (fpc n00) a0
def rowDx : CellRow 113 F := mkRow 3 0 2 false true 3 0 2 1 0 (fpc nDx) a0 (fpc nB)
def row00 : CellRow 113 F := mkRow 4 0 0 false false 1 0 0 2 0 (fpc n00) a0 a0

def honestT : List (CellRow 113 F) := [rowX, rowA, rowB, rowDx, row00]
def rootKey : VKey F := (fpc nX, 0, 6, 0)

theorem honest_accepted : TableAccepts zz honestT [rootKey] :=
  tableAccepts_of (by unfold SerialOK; decide) (by decide) (by unfold ValidityBalanced; decide)

/-- The forgery: the SAME round-0 rows, the post-seed fingerprints re-linked as `y`. -/
def forgedT : List (CellRow 113 F) :=
  [{ rowX with p := fpc nY, l := fpc nB, r := fpc nDy }, rowA, rowB,
   { rowDx with p := fpc nDy, r := fpc nA }, row00]

theorem forged_same_b0 : forgedT.map (·.b0) = honestT.map (·.b0) := by decide
theorem forged_rows_ok : forgedT.all rowOKb = true := by decide

/-- **REJECTED** at the production acceptance. -/
theorem relink_rejected : ¬ TableAccepts zz forgedT [rootKey] := fun h =>
  absurd h.served (by unfold ValidityServed; decide)

/-- The forgery is rejected already by the multiset form too (kept). -/
theorem relink_rejected_balanced : ¬ ValidityBalanced forgedT [rootKey] := by
  unfold ValidityBalanced; decide

/-- What the forgery would serve: row 0's left child `fp B` where the B0 decode says `A`. -/
theorem relink_serves_wrong_noun : (forgedT.head?.map (·.l)) = some (fpc nB) ∧ fpc nB ≠ fpc nA ∧
    (honestT.head?.map (·.l)) = some (fpc nA) := ⟨rfl, by decide, rfl⟩

/-! ## NC (a): the serial step `+1 → +0` -/

def zeroSer (c : CellRow 113 F) : CellRow 113 F :=
  { c with b0 := { c.b0 with idx := 0, idL := 0, idR := 0 } }

def AcceptsZeroStep (t : List (CellRow 113 F)) (vl : List (VKey F)) : Prop :=
  (∀ c ∈ t, c.b0.idx = 0) ∧ (∀ c ∈ t, RowOK zz c) ∧ ValidityBalanced t vl

def rootKey0 : VKey F := (fpc nX, 0, 6, 0)

theorem nc_zero_step_honest_accepted : AcceptsZeroStep (honestT.map zeroSer) [rootKey0] :=
  ⟨by decide, fun c hc => rowOKb_sound (List.all_eq_true.mp (by decide) c hc),
    by unfold ValidityBalanced; decide⟩

/-- The forgery is ACCEPTED again under NC (a), on the same B0, serving a different fingerprint at
serial `0` (row position 3: `fp Dx` vs `fp Dy`). -/
theorem nc_zero_step_relink_accepted :
    AcceptsZeroStep (forgedT.map zeroSer) [rootKey0] ∧
    (forgedT.map zeroSer).map (·.b0) = (honestT.map zeroSer).map (·.b0) ∧
    ∃ c ∈ honestT.map zeroSer, ∃ c' ∈ forgedT.map zeroSer, c.b0.idx = c'.b0.idx ∧ c.p ≠ c'.p :=
  ⟨⟨by decide, fun c hc => rowOKb_sound (List.all_eq_true.mp (by decide) c hc),
    by unfold ValidityBalanced; decide⟩, by decide,
   ⟨zeroSer rowDx, List.mem_map_of_mem (by simp [honestT]),
     zeroSer { rowDx with p := fpc nDy, r := fpc nA }, List.mem_map_of_mem (by simp [forgedT]), rfl,
     by decide⟩⟩

/-! ## NC (b): child serials out of the validity key -/

def vProv2 (t : List (CellRow 113 F)) : List ((FP F × ℕ × ℕ) × ℕ) :=
  t.map fun c => ((c.p, c.b0.hi, c.b0.lo), c.b0.mv)
def vCons2 (t : List (CellRow 113 F)) : List ((FP F × ℕ × ℕ) × ℕ) :=
  t.flatMap fun c =>
    [((c.l, c.b0.hiL, c.b0.loL), if c.b0.wL then 1 else 0),
     ((c.r, c.b0.hiR, c.b0.loR), if c.b0.wR then 1 else 0)]

def AcceptsNoChildKey (t : List (CellRow 113 F)) (vl : List (FP F × ℕ × ℕ)) : Prop :=
  SerialOK (t.map (·.b0)) ∧ (∀ c ∈ t, RowOK zz c) ∧
    (expand (vProv2 t)).Perm (expand (vCons2 t ++ vl.map (·, 1)))

theorem nc_no_child_key_honest_accepted : AcceptsNoChildKey honestT [(fpc nX, 0, 6)] :=
  ⟨by unfold SerialOK; decide, fun c hc => rowOKb_sound (List.all_eq_true.mp (by decide) c hc), by decide⟩

theorem nc_no_child_key_relink_accepted :
    AcceptsNoChildKey forgedT [(fpc nX, 0, 6)] ∧ forgedT.map (·.b0) = honestT.map (·.b0) ∧
    ∃ c ∈ honestT, ∃ c' ∈ forgedT, c.b0.idx = c'.b0.idx ∧ c.p ≠ c'.p :=
  ⟨⟨by unfold SerialOK; decide, fun c hc => rowOKb_sound (List.all_eq_true.mp forged_rows_ok c hc),
    by decide⟩,
   forged_same_b0, ⟨rowDx, by simp [honestT], { rowDx with p := fpc nDy, r := fpc nA }, by simp [forgedT], rfl,
     by decide⟩⟩

/-! ## NC (c): duplicated serials with the threading gate OFF -/

def setIdx (c : CellRow 113 F) (idx idL idR mv : ℕ) : CellRow 113 F :=
  { c with b0 := { c.b0 with idx := idx, idL := idL, idR := idR, mv := mv } }

def rowXp : CellRow 113 F := mkRow 4 1 2 true true 6 2 3 0 0 (fpc nY) (fpc nB) (fpc nDy)
def rowDy : CellRow 113 F := mkRow 2 0 1 false true 3 0 2 1 0 (fpc nDy) a0 (fpc nA)

def dupHonest : List (CellRow 113 F) :=
  [setIdx rowX 0 1 2 1, rowXp, setIdx rowA 1 0 3 2, setIdx rowB 1 3 0 2, setIdx rowDx 2 0 1 1, rowDy,
   setIdx row00 3 0 0 2]

def dupForged : List (CellRow 113 F) :=
  [{ setIdx rowX 0 1 2 1 with p := fpc nY, l := fpc nB, r := fpc nDy },
   { rowXp with p := fpc nX, l := fpc nA, r := fpc nDx },
   setIdx rowA 1 0 3 2, setIdx rowB 1 3 0 2,
   { setIdx rowDx 2 0 1 1 with p := fpc nDy, r := fpc nA },
   { rowDy with p := fpc nDx, r := fpc nB },
   setIdx row00 3 0 0 2]

def AcceptsFreeSerial (t : List (CellRow 113 F)) (vl : List (VKey F)) : Prop :=
  (∀ c ∈ t, RowOK zz c) ∧ ValidityBalanced t vl

theorem dup_same_b0 : dupForged.map (·.b0) = dupHonest.map (·.b0) := by decide

theorem nc_dup_serial_honest_accepted : AcceptsFreeSerial dupHonest [rootKey] :=
  ⟨fun c hc => rowOKb_sound (List.all_eq_true.mp (by decide) c hc), by unfold ValidityBalanced; decide⟩

theorem nc_dup_serial_relink_accepted :
    AcceptsFreeSerial dupForged [rootKey] ∧
    ∃ c ∈ dupHonest, ∃ c' ∈ dupForged, c.b0.idx = c'.b0.idx ∧ c.b0 = c'.b0 ∧ c.p ≠ c'.p :=
  ⟨⟨fun c hc => rowOKb_sound (List.all_eq_true.mp (by decide) c hc), by unfold ValidityBalanced; decide⟩,
   ⟨setIdx rowDx 2 0 1 1, by simp [dupHonest], { setIdx rowDx 2 0 1 1 with p := fpc nDy, r := fpc nA },
     by simp [dupForged],
     rfl, rfl, by decide⟩⟩

/-- The threading gate is what rejects it. -/
theorem dup_serial_gate_rejects : ¬ SerialOK (dupForged.map (·.b0)) := by
  unfold SerialOK; decide

end Nock.RedTeam.Batch1672

#print axioms Nock.RedTeam.Batch1672.fpc_eq_enc
#print axioms Nock.RedTeam.Batch1672.relink_enc_collision
#print axioms Nock.RedTeam.Batch1672.honest_accepted
#print axioms Nock.RedTeam.Batch1672.forged_same_b0
#print axioms Nock.RedTeam.Batch1672.relink_rejected
#print axioms Nock.RedTeam.Batch1672.relink_serves_wrong_noun
#print axioms Nock.RedTeam.Batch1672.nc_zero_step_honest_accepted
#print axioms Nock.RedTeam.Batch1672.nc_zero_step_relink_accepted
#print axioms Nock.RedTeam.Batch1672.nc_no_child_key_honest_accepted
#print axioms Nock.RedTeam.Batch1672.nc_no_child_key_relink_accepted
#print axioms Nock.RedTeam.Batch1672.nc_dup_serial_honest_accepted
#print axioms Nock.RedTeam.Batch1672.nc_dup_serial_relink_accepted
#print axioms Nock.RedTeam.Batch1672.dup_serial_gate_rejects
