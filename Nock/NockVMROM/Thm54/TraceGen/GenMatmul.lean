/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmul.lean

  2×2 matmul inhabitant (generic-matmul plan, item 7).  Design rules:

  * Count **up**, never down — the only arithmetic primitive is OP4.
  * Fuse multiply-accumulate into **one** recursive arm so the running
    sum never leaves the sample.
  * Entries in `{0,1}` so every inner add / outer MAC trip count is
    `0` or `1` (small increment loops, still genuine OP6/OP9 recursion).
  * No OP10: the generator classifies it `.notROM`.  Recursion rebuilds
    the core with OP7 + autocons (`[[0 2] newSample]`) and OP9.

  Matrices (subject `[A B]`):

      A = [[1 1] [0 1]]     B = [[1 0] [1 1]]
      C = [[2 1] [1 1]]

  Slot map of the subject: `/[8]=a00 /[9]=a01 /[10]=a10 /[11]=a11`,
  `/[12]=b00 /[13]=b01 /[14]=b10 /[15]=b11`.

  Two arms share a battery `[macArm addArm]`:

  * `addArm` on sample `[acc [i m]]` — increment `acc` until `i = m`.
  * `macArm` on sample `[acc [i [n m]]]` — `acc += m`, `n` times, by
    slamming `addArm`.

  Each output entry is `mac(mac(0, a_ik, b_kj), a_i,k', b_k'j)`.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.GenSound
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.GlobalOpcodeScheduling
import Nock.FieldEmbedding

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OpcodeSemantics
open Nock.NockVMROM.Thm54.GlobalOpcodeScheduling
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## Formula fragments -/

/-- `[9 [axis [0 1]]]` — invoke the arm at `axis` against `*[subj [0 1]]`. -/
def invokeAxis (axis : ℕ) : Noun :=
  .cell (.atom 9) (.cell (.atom axis) (.cell (.atom 0) (.atom 1)))

/-- `[7 [b c]]`. -/
def op7 (b c : Noun) : Noun :=
  .cell (.atom 7) (.cell b c)

/-- `[6 [b [c d]]]`. -/
def op6 (b c d : Noun) : Noun :=
  .cell (.atom 6) (.cell b (.cell c d))

/-- `[5 [b c]]`. -/
def op5 (b c : Noun) : Noun :=
  .cell (.atom 5) (.cell b c)

/-- `[4 b]`. -/
def op4 (b : Noun) : Noun :=
  .cell (.atom 4) b

/-- `[0 axis]`. -/
def op0 (axis : ℕ) : Noun :=
  .cell (.atom 0) (.atom axis)

/-- `[1 n]`. -/
def op1 (n : ℕ) : Noun :=
  .cell (.atom 1) (.atom n)

/-- Quote a noun as an OP1 constant. -/
def quote (n : Noun) : Noun :=
  .cell (.atom 1) n

/-- Rebuild `[battery sample]` from `batteryF`/`sampleF` and invoke `axis`. -/
def slam (batteryF sampleF : Noun) (axis : ℕ) : Noun :=
  op7 (.cell batteryF sampleF) (invokeAxis axis)

/-! ## Add arm — sample `[acc [i m]]`, count `i` up to `m`

    `/[6]=acc /[14]=i /[15]=m`.  Recurses via `/[2]` (this arm). -/

def addNewSample : Noun :=
  .cell (op4 (op0 6)) (.cell (op4 (op0 14)) (op0 15))

def addArm : Noun :=
  op6 (op5 (op0 14) (op0 15))
    (op0 6)
    (slam (op0 2) addNewSample 2)

def addSample (acc m : Noun) : Noun :=
  .cell acc (.cell (.atom 0) m)

/-- Slam `addArm` on dummy subject `0`. -/
def addCall (acc m : Noun) : Noun :=
  slam (quote addArm) (quote (addSample acc m)) 2

def addCore (acc i m : Noun) : Noun :=
  .cell addArm (.cell acc (.cell i m))

/-! ## MAC arm — sample `[acc [i [n m]]]`, `acc += m` exactly `n` times

    `/[6]=acc /[14]=i /[30]=n /[31]=m`.  Inner add slams `/[5]`. -/

def addFromMac : Noun :=
  slam (op0 5) (.cell (op0 6) (.cell (op1 0) (op0 31))) 2

def macNewSample : Noun :=
  .cell addFromMac (.cell (op4 (op0 14)) (.cell (op0 30) (op0 31)))

def macArm : Noun :=
  op6 (op5 (op0 14) (op0 30))
    (op0 6)
    (slam (op0 2) macNewSample 4)

/-- Battery `[macArm addArm]`.  Slot 4 = mac, slot 5 = add. -/
def mmBattery : Noun :=
  .cell macArm addArm

def macSample (acc n m : Noun) : Noun :=
  .cell acc (.cell (.atom 0) (.cell n m))

def macCoreAt (acc i n m : Noun) : Noun :=
  .cell mmBattery (.cell acc (.cell i (.cell n m)))

def macCore (acc n m : Noun) : Noun :=
  macCoreAt acc (.atom 0) n m

/-- Slam the MAC arm; `accF`/`nF`/`mF` are formulas against the row subject. -/
def invokeMac (accF nF mF : Noun) : Noun :=
  slam (quote mmBattery)
    (.cell accF (.cell (op1 0) (.cell nF mF)))
    4

/-- Nested MAC: `acc + n*m + n'*m'`. -/
def mac2 (accF nF mF nF' mF' : Noun) : Noun :=
  invokeMac (invokeMac accF nF mF) nF' mF'

/-! ## 2×2 matrices -/

def mmA : Noun :=
  .cell (.cell (.atom 1) (.atom 1)) (.cell (.atom 0) (.atom 1))
def mmB : Noun :=
  .cell (.cell (.atom 1) (.atom 0)) (.cell (.atom 1) (.atom 1))
/-- `A B = [[2 1] [1 1]]`. -/
def mmC : Noun :=
  .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1))
def mmSubject : Noun :=
  .cell mmA mmB

/-- `c00 = a00·b00 + a01·b10`. -/
def mmC00 : Noun := mac2 (op1 0) (op0 8) (op0 12) (op0 9) (op0 14)
/-- `c01 = a00·b01 + a01·b11`. -/
def mmC01 : Noun := mac2 (op1 0) (op0 8) (op0 13) (op0 9) (op0 15)
/-- `c10 = a10·b00 + a11·b10`. -/
def mmC10 : Noun := mac2 (op1 0) (op0 10) (op0 12) (op0 11) (op0 14)
/-- `c11 = a10·b01 + a11·b11`. -/
def mmC11 : Noun := mac2 (op1 0) (op0 10) (op0 13) (op0 11) (op0 15)

/-- Autocons of the four fused MACs. -/
def mmFormula : Noun :=
  .cell (.cell mmC00 mmC01) (.cell mmC10 mmC11)

/-! ## Slot lemmas (subject only; do not unfold arms) -/

theorem slot_1 (n : Noun) : Noun.slot 1 n = some n := by
  simp [Noun.slot]

theorem addCore_slot2 (acc i m : Noun) :
    Noun.slot 2 (addCore acc i m) = some addArm := by
  simp [addCore, Noun.slot]

theorem addCore_slot6 (acc i m : Noun) :
    Noun.slot 6 (addCore acc i m) = some acc := by
  simp [addCore, Noun.slot]

theorem addCore_slot14 (acc i m : Noun) :
    Noun.slot 14 (addCore acc i m) = some i := by
  simp [addCore, Noun.slot]

theorem addCore_slot15 (acc i m : Noun) :
    Noun.slot 15 (addCore acc i m) = some m := by
  simp [addCore, Noun.slot]

theorem macCoreAt_slot2 (acc i n m : Noun) :
    Noun.slot 2 (macCoreAt acc i n m) = some mmBattery := by
  simp [macCoreAt, Noun.slot]

theorem macCoreAt_slot4 (acc i n m : Noun) :
    Noun.slot 4 (macCoreAt acc i n m) = some macArm := by
  simp [macCoreAt, mmBattery, Noun.slot]

theorem macCoreAt_slot5 (acc i n m : Noun) :
    Noun.slot 5 (macCoreAt acc i n m) = some addArm := by
  simp [macCoreAt, mmBattery, Noun.slot]

theorem macCoreAt_slot6 (acc i n m : Noun) :
    Noun.slot 6 (macCoreAt acc i n m) = some acc := by
  simp [macCoreAt, Noun.slot]

theorem macCoreAt_slot14 (acc i n m : Noun) :
    Noun.slot 14 (macCoreAt acc i n m) = some i := by
  simp [macCoreAt, Noun.slot]

theorem macCoreAt_slot30 (acc i n m : Noun) :
    Noun.slot 30 (macCoreAt acc i n m) = some n := by
  simp [macCoreAt, Noun.slot]

theorem macCoreAt_slot31 (acc i n m : Noun) :
    Noun.slot 31 (macCoreAt acc i n m) = some m := by
  simp [macCoreAt, Noun.slot]

theorem tis_self (n : Noun) : Noun.tis n n = .atom 0 := by
  simp [Noun.tis]

theorem tis_atom_ne {a b : ℕ} (h : a ≠ b) :
    Noun.tis (.atom a) (.atom b) = .atom 1 := by
  simp [Noun.tis, h]

theorem lus_succ {n : ℕ} (h : n + 1 < 97) :
    FieldEmbedding.lusFBy 97 (.atom n) = some (.atom (n + 1)) := by
  simp [FieldEmbedding.lusFBy, Nat.mod_eq_of_lt h]

theorem lus_nat (n : ℕ) :
    Noun.lus (.atom n) = some (.atom (n + 1)) :=
  rfl

/-! ## Eval wrappers -/

theorem eval_quote (q fuel : ℕ) (subject result : Noun) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (quote result) = some result :=
  evalFBy_s1_exact q fuel subject result

theorem eval_op1 (q fuel : ℕ) (subject : Noun) (k : ℕ) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (op1 k) = some (.atom k) :=
  evalFBy_s1_exact q fuel subject (.atom k)

theorem eval_op0 (q n axis : ℕ) {subject result : Noun}
    (h : Noun.slot axis subject = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject (op0 axis) = some result :=
  evalFBy_s0_exact h

theorem eval_op4 (q n : ℕ) {subject tail value result : Noun}
    (hcall : FieldEmbedding.evalFBy q n subject tail = some value)
    (hinc : FieldEmbedding.lusFBy q value = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject (op4 tail) = some result :=
  evalFBy_s4_exact hcall hinc

theorem eval_op5 (q n : ℕ) {subject b c rb rc : Noun}
    (hb : FieldEmbedding.evalFBy q n subject b = some rb)
    (hc : FieldEmbedding.evalFBy q n subject c = some rc) :
    FieldEmbedding.evalFBy q (n + 1) subject (op5 b c) = some (Noun.tis rb rc) :=
  evalFBy_s5_exact hb hc

theorem eval_op6_zero (q n : ℕ) {subject b c d result : Noun}
    (hb : FieldEmbedding.evalFBy q n subject b = some (.atom 0))
    (hc : FieldEmbedding.evalFBy q n subject c = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject (op6 b c d) = some result :=
  evalFBy_s6_zero_exact hb hc

theorem eval_op6_one (q n : ℕ) {subject b c d result : Noun}
    (hb : FieldEmbedding.evalFBy q n subject b = some (.atom 1))
    (hd : FieldEmbedding.evalFBy q n subject d = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject (op6 b c d) = some result :=
  evalFBy_s6_one_exact hb hd

theorem eval_op7 (q n : ℕ) {subject b c sb result : Noun}
    (hb : FieldEmbedding.evalFBy q n subject b = some sb)
    (hc : FieldEmbedding.evalFBy q n sb c = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject (op7 b c) = some result :=
  evalFBy_s7_exact hb hc

theorem eval_op9 (q n axis : ℕ) {subject c core arm result : Noun}
    (hc : FieldEmbedding.evalFBy q n subject c = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalFBy q n core arm = some result) :
    FieldEmbedding.evalFBy q (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = some result :=
  evalFBy_s9_exact hc hslot harm

theorem eval_cons (q fuel : ℕ)
    {subject leftHead leftTail tail leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalFBy q fuel subject (.cell leftHead leftTail) =
      some leftResult)
    (hright : FieldEmbedding.evalFBy q fuel subject tail = some rightResult) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.cell leftHead leftTail) tail) =
      some (.cell leftResult rightResult) :=
  evalFBy_cons_exact hleft hright

theorem eval_invokeAxis (q n axis : ℕ) {subject core arm result : Noun}
    (hslot1 : Noun.slot 1 subject = some core)
    (hslotA : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalFBy q (n + 2) core arm = some result) :
    FieldEmbedding.evalFBy q (n + 3) subject (invokeAxis axis) = some result := by
  have hcore : FieldEmbedding.evalFBy q (n + 2) subject (op0 1) = some core :=
    eval_op0 q (n + 1) 1 hslot1
  exact evalFBy_s9_exact (fuel := n + 2) hcore hslotA harm

/-- `slam batteryF sampleF axis` against `subject`, when `batteryF` is a cell. -/
theorem eval_slam (q fuel : ℕ)
    {subject bHead bTail sampleF battery sample arm result : Noun} {axis : ℕ}
    (hb : FieldEmbedding.evalFBy q (fuel + 3) subject (.cell bHead bTail) =
      some battery)
    (hs : FieldEmbedding.evalFBy q (fuel + 3) subject sampleF = some sample)
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : FieldEmbedding.evalFBy q (fuel + 3) (.cell battery sample) arm =
      some result) :
    FieldEmbedding.evalFBy q (fuel + 5) subject
      (slam (.cell bHead bTail) sampleF axis) = some result := by
  have hcons : FieldEmbedding.evalFBy q (fuel + 4) subject
      (.cell (.cell bHead bTail) sampleF) = some (.cell battery sample) :=
    eval_cons q (fuel + 3) hb hs
  have hax : FieldEmbedding.evalFBy q (fuel + 4) (.cell battery sample)
      (invokeAxis axis) = some result :=
    eval_invokeAxis (q := q) (n := fuel + 1) (axis := axis)
      (slot_1 _) hslot harm
  exact eval_op7 q (fuel + 4) hcons hax

/-! ## Add-arm evaluation -/

theorem eval_addArm_done (q n : ℕ) (acc m : Noun) :
    FieldEmbedding.evalFBy q (n + 6) (addCore acc m m) addArm = some acc := by
  have h14 := eval_op0 q (n + 3) 14 (addCore_slot14 acc m m)
  have h15 := eval_op0 q (n + 3) 15 (addCore_slot15 acc m m)
  have hcond := eval_op5 q (n + 4) h14 h15
  have htis : Noun.tis m m = .atom 0 := tis_self m
  rw [htis] at hcond
  have hthen := eval_op0 q (n + 4) 6 (addCore_slot6 acc m m)
  simpa [addArm] using eval_op6_zero q (n + 5) hcond hthen

theorem eval_addNewSample (n acc i m : ℕ) (hacc : acc + 1 < 97) (hi : i + 1 < 97) :
    FieldEmbedding.evalFBy 97 (n + 5) (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) := by
  have h6 := eval_op0 97 (n + 2) 6 (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := eval_op0 97 (n + 1) 14 (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := eval_op0 97 (n + 2) 15 (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := eval_op4 97 (n + 3) h6 (lus_succ hacc)
  have hincI := eval_op4 97 (n + 2) h14 (lus_succ hi)
  have hinner := eval_cons 97 (n + 3) hincI h15
  exact eval_cons 97 (n + 4) hincA hinner

/-- One increment: `i = 0`, `m = 1`. -/
theorem eval_addArm_one (n acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalFBy 97 (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      some (.atom (acc + 1)) := by
  have h14 := eval_op0 97 (n + 13) 14
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := eval_op0 97 (n + 13) 15
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := eval_op5 97 (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := eval_addNewSample (n + 8) acc 0 1 hacc (by decide)
  have hbatt := eval_op0 97 (n + 12) 2
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  have hdone := eval_addArm_done 97 (n + 7) (.atom (acc + 1)) (.atom 1)
  have hslam := eval_slam (q := 97) (fuel := n + 10)
    (subject := addCore (.atom acc) (.atom 0) (.atom 1))
    (bHead := .atom 0) (bTail := .atom 2) (sampleF := addNewSample)
    (battery := addArm)
    (sample := .cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1)))
    (axis := 2) (arm := addArm) (result := .atom (acc + 1))
    hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1))
    hdone
  simpa [addArm, slam, op0] using eval_op6_one 97 (n + 15) hcond hslam

theorem add_1_1_eval :
    FieldEmbedding.evalFBy 97 32 (.atom 0) (addCall (.atom 1) (.atom 1))
      = some (.atom 2) := by
  have hqB := eval_quote 97 29 (.atom 0) addArm
  have hqS := eval_quote 97 29 (.atom 0) (addSample (.atom 1) (.atom 1))
  have hslot : Noun.slot 2
      (.cell addArm (addSample (.atom 1) (.atom 1))) = some addArm :=
    addCore_slot2 (.atom 1) (.atom 0) (.atom 1)
  have hdone := eval_addArm_one 14 1 (by decide)
  have hslam := eval_slam (q := 97) (fuel := 27)
    hqB hqS hslot hdone
  simpa [addCall, slam, quote] using hslam

/-! ## MAC-arm evaluation -/

theorem eval_macArm_done (q fuel : ℕ) (acc n m : Noun) :
    FieldEmbedding.evalFBy q (fuel + 6) (macCoreAt acc n n m) macArm = some acc := by
  have h14 := eval_op0 q (fuel + 3) 14 (macCoreAt_slot14 acc n n m)
  have h30 := eval_op0 q (fuel + 3) 30 (macCoreAt_slot30 acc n n m)
  have hcond := eval_op5 q (fuel + 4) h14 h30
  rw [tis_self n] at hcond
  have hthen := eval_op0 q (fuel + 4) 6 (macCoreAt_slot6 acc n n m)
  simpa [macArm] using eval_op6_zero q (fuel + 5) hcond hthen

theorem eval_macArm_zero (q fuel : ℕ) (acc m : Noun) :
    FieldEmbedding.evalFBy q (fuel + 6) (macCore acc (.atom 0) m) macArm = some acc :=
  eval_macArm_done q fuel acc (.atom 0) m

/-- Sample formula `[accF [0 [nF mF]]]` with cell-headed `accF`/`nF`. -/
theorem eval_macSampleF (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m : Noun}
    (ha : FieldEmbedding.evalFBy q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : FieldEmbedding.evalFBy q fuel subject (.cell nH nT) = some n)
    (hm : FieldEmbedding.evalFBy q fuel subject mF = some m) :
    FieldEmbedding.evalFBy q (fuel + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      some (.cell acc (.cell (.atom 0) (.cell n m))) := by
  have hnm := eval_cons q fuel hn hm
  have hz := eval_op1 q fuel subject 0
  have hinner := eval_cons q (fuel + 1) hz hnm
  exact eval_cons q (fuel + 2) ha hinner

theorem eval_invokeMac (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m result : Noun}
    (ha : FieldEmbedding.evalFBy q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : FieldEmbedding.evalFBy q fuel subject (.cell nH nT) = some n)
    (hm : FieldEmbedding.evalFBy q fuel subject mF = some m)
    (harm : FieldEmbedding.evalFBy q (fuel + 3) (macCore acc n m) macArm =
      some result) :
    FieldEmbedding.evalFBy q (fuel + 5) subject
      (invokeMac (.cell aH aT) (.cell nH nT) mF) = some result := by
  have hqB := eval_quote q (fuel + 2) subject mmBattery
  have hsf := eval_macSampleF q fuel ha hn hm
  have hslot := macCoreAt_slot4 acc (.atom 0) n m
  simpa [invokeMac, slam, quote, macCore, macCoreAt, macSample] using
    eval_slam (q := q) (fuel := fuel)
      (bHead := .atom 1) (bTail := mmBattery)
      hqB hsf hslot harm

theorem mac_0_m_eval (m : ℕ) :
    FieldEmbedding.evalFBy 97 16 (.atom 0)
        (invokeMac (op1 0) (op1 0) (op1 m))
      = some (.atom 0) := by
  have ha := eval_op1 97 13 (.atom 0) 0
  have hn := eval_op1 97 10 (.atom 0) 0
  have hm := eval_op1 97 10 (.atom 0) m
  have harm := eval_macArm_zero 97 8 (.atom 0) (.atom m)
  have h := eval_invokeMac (q := 97) (fuel := 11)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 1) (nT := .atom 0)
    (mF := op1 m) ha hn hm
    (evalFBy_mono (q := 97) (show 8 + 6 ≤ 11 + 3 by omega) harm)
  simpa [op1] using
    evalFBy_mono (q := 97) (show 11 + 5 ≤ 16 by omega) h

/-- Inner add slammed from a MAC core: `m = 0` so `add` is immediately done. -/
theorem eval_addFromMac_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = some (.atom acc) := by
  have h5 := eval_op0 97 (fuel + 9) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := eval_op0 97 (fuel + 8) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := eval_op1 97 (fuel + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := eval_op0 97 (fuel + 7) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := eval_cons 97 (fuel + 8) hz hm
  have hsmpl := eval_cons 97 (fuel + 9) hacc hinner
  have hadd := eval_addArm_done 97 (fuel + 4) (.atom acc) (.atom 0)
  simpa [addFromMac, slam, op0, op1, macCore] using
    eval_slam (q := 97) (fuel := fuel + 7)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 0))
      hadd

/-- Inner add slammed from a MAC core: `m = 1` so `add` takes one increment. -/
theorem eval_addFromMac_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalFBy 97 (fuel + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      some (.atom (acc + 1)) := by
  have h5 := eval_op0 97 (fuel + 18) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := eval_op0 97 (fuel + 17) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := eval_op1 97 (fuel + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := eval_op0 97 (fuel + 16) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := eval_cons 97 (fuel + 17) hz hm
  have hsmpl := eval_cons 97 (fuel + 18) haccS hinner
  have hadd := eval_addArm_one (fuel + 3) acc hacc
  simpa [addFromMac, slam, op0, op1, macCore] using
    eval_slam (q := 97) (fuel := fuel + 16)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
      hadd

/-- `macNewSample` after one MAC trip with `m = 0`. -/
theorem eval_macNewSample_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      some (.cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) := by
  have hadd := eval_addFromMac_m0 fuel acc
  have h14 := eval_op0 97 (fuel + 10) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := eval_op4 97 (fuel + 11) h14 (lus_succ (n := 0) (by decide))
  have hn := eval_op0 97 (fuel + 10) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := eval_op0 97 (fuel + 10) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := eval_cons 97 (fuel + 11) hn hm
  have hrest := eval_cons 97 (fuel + 12) hinc hnm
  exact eval_cons 97 (fuel + 13)
    (evalFBy_mono (q := 97) (show fuel + 12 ≤ fuel + 13 by omega) hadd) hrest

theorem eval_macArm_one_m0 (fuel acc : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = some (.atom acc) := by
  have h14 := eval_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := eval_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := eval_op5 97 (fuel + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := eval_macNewSample_m0 (fuel + 4) acc
  have hbatt := eval_op0 97 (fuel + 18) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hdone := eval_macArm_done 97 (fuel + 13) (.atom acc) (.atom 1) (.atom 0)
  have hslam := eval_slam (q := 97) (fuel := fuel + 16)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalFBy_mono (q := 97) (show fuel + 4 + 14 ≤ fuel + 16 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0))
    (evalFBy_mono (q := 97) (show fuel + 13 + 6 ≤ fuel + 16 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    eval_op6_one 97 (fuel + 21) hcond hslam

/-- `macNewSample` after one MAC trip with `m = 1`. -/
theorem eval_macNewSample_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalFBy 97 (fuel + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) := by
  have hadd := eval_addFromMac_m1 fuel acc hacc
  have h14 := eval_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := eval_op4 97 (fuel + 20) h14 (lus_succ (n := 0) (by decide))
  have hn := eval_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := eval_op0 97 (fuel + 19) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := eval_cons 97 (fuel + 20) hn hm
  have hrest := eval_cons 97 (fuel + 21) hinc hnm
  exact eval_cons 97 (fuel + 22)
    (evalFBy_mono (q := 97) (show fuel + 21 ≤ fuel + 22 by omega) hadd) hrest

theorem eval_macArm_one_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    FieldEmbedding.evalFBy 97 (fuel + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      some (.atom (acc + 1)) := by
  have h14 := eval_op0 97 (fuel + 28) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := eval_op0 97 (fuel + 28) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := eval_op5 97 (fuel + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := eval_macNewSample_m1 (fuel + 4) acc hacc
  have hbatt := eval_op0 97 (fuel + 27) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hdone := eval_macArm_done 97 (fuel + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have hslam := eval_slam (q := 97) (fuel := fuel + 25)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalFBy_mono (q := 97) (show fuel + 4 + 23 ≤ fuel + 25 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1))
    (evalFBy_mono (q := 97) (show fuel + 22 + 6 ≤ fuel + 25 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    eval_op6_one 97 (fuel + 30) hcond hslam

theorem mac_1_1_eval :
    FieldEmbedding.evalFBy 97 48 (.atom 0)
        (invokeMac (op1 0) (op1 1) (op1 1))
      = some (.atom 1) := by
  have ha := eval_op1 97 44 (.atom 0) 0
  have hn := eval_op1 97 42 (.atom 0) 1
  have hm := eval_op1 97 42 (.atom 0) 1
  have harm := eval_macArm_one_m1 11 0 (by decide)
  have h := eval_invokeMac (q := 97) (fuel := 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 1) (nT := .atom 1)
    (mF := op1 1) ha hn hm
    (evalFBy_mono (q := 97) (show 11 + 31 ≤ 43 + 3 by omega) harm)
  simpa [op1] using
    evalFBy_mono (q := 97) (show 43 + 5 ≤ 48 by omega) h

/-! ## 2×2 evaluation -/

theorem mmSubject_slot8 : Noun.slot 8 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot9 : Noun.slot 9 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot10 : Noun.slot 10 mmSubject = some (.atom 0) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot11 : Noun.slot 11 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot12 : Noun.slot 12 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot13 : Noun.slot 13 mmSubject = some (.atom 0) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot14 : Noun.slot 14 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]
theorem mmSubject_slot15 : Noun.slot 15 mmSubject = some (.atom 1) := by
  simp [mmSubject, mmA, mmB, Noun.slot]

private theorem invokeMac_is_op7 (accF nF mF : Noun) :
    invokeMac accF nF mF =
      op7 (.cell (quote mmBattery) (.cell accF (.cell (op1 0) (.cell nF mF))))
        (invokeAxis 4) :=
  rfl

/-- `c00 = 1·1 + 1·1 = 2`. -/
theorem eval_mmC00 (fuel : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 56) mmSubject mmC00 = some (.atom 2) := by
  have ha0 := eval_op1 97 (fuel + 44) mmSubject 0
  have a00 := eval_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b00 := eval_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := eval_macArm_one_m1 (fuel + 11) 0 (by decide)
  have hinner := eval_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00
    (evalFBy_mono (q := 97) (show fuel + 11 + 31 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := eval_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b10 := eval_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := eval_macArm_one_m1 (fuel + 16) 1 (by decide)
  have houter := eval_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalFBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b10
    (evalFBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalFBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c01 = 1·0 + 1·1 = 1`. -/
theorem eval_mmC01 (fuel : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 56) mmSubject mmC01 = some (.atom 1) := by
  have ha0 := eval_op1 97 (fuel + 44) mmSubject 0
  have a00 := eval_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b01 := eval_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := eval_macArm_one_m0 (fuel + 20) 0
  have hinner := eval_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01
    (evalFBy_mono (q := 97) (show fuel + 20 + 22 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := eval_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b11 := eval_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := eval_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := eval_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalFBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b11
    (evalFBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalFBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c10 = 0·1 + 1·1 = 1`. -/
theorem eval_mmC10 (fuel : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 56) mmSubject mmC10 = some (.atom 1) := by
  have ha0 := eval_op1 97 (fuel + 44) mmSubject 0
  have a10 := eval_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b00 := eval_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := eval_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 1)
  have hinner := eval_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00
    (evalFBy_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := eval_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b10 := eval_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := eval_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := eval_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalFBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b10
    (evalFBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalFBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c11 = 0·0 + 1·1 = 1`. -/
theorem eval_mmC11 (fuel : ℕ) :
    FieldEmbedding.evalFBy 97 (fuel + 56) mmSubject mmC11 = some (.atom 1) := by
  have ha0 := eval_op1 97 (fuel + 44) mmSubject 0
  have a10 := eval_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b01 := eval_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := eval_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 0)
  have hinner := eval_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01
    (evalFBy_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := eval_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b11 := eval_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := eval_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := eval_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalFBy_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b11
    (evalFBy_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalFBy_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

theorem mm_eval :
    FieldEmbedding.evalFBy 97 64 mmSubject mmFormula = some mmC := by
  have h00 := eval_mmC00 6
  have h01 := eval_mmC01 6
  have h10 := eval_mmC10 6
  have h11 := eval_mmC11 6
  have hL := eval_cons 97 62
    (evalFBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h00)
    (evalFBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h01)
  have hR := eval_cons 97 62
    (evalFBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h10)
    (evalFBy_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h11)
  rw [mmFormula, mmC]
  exact eval_cons 97 63 hL hR

/-! ## Generator emission -/

theorem gen_quote (n : ℕ) (subject result : Noun) :
    genComputeSkeleton (K := K) (n + 1) subject (quote result) =
      .ok (.node (skelNode (genSkelOp1 subject (quote result) result (.atom 1))
            [⟨quote result, result, 3, 0⟩]) [], result) := by
  simp only [quote, genComputeSkeleton]

theorem gen_op1 (n : ℕ) (subject : Noun) (k : ℕ) :
    genComputeSkeleton (K := K) (n + 1) subject (op1 k) =
      .ok (.node (skelNode (genSkelOp1 subject (op1 k) (.atom k) (.atom 1))
            [⟨op1 k, .atom k, 3, 0⟩]) [], .atom k) := by
  simpa [op1, quote] using gen_quote (K := K) n subject (.atom k)

theorem gen_op0 (n : ℕ) {subject : Noun} {axis : ℕ} {result : Noun}
    (h : Noun.slot axis subject = some result) :
    genComputeSkeleton (K := K) (n + 1) subject (op0 axis) =
      .ok (.node (skelNode
            (genSkelOp0 subject (op0 axis) (.atom 0) (.atom axis) result axis)
            [⟨op0 axis, .atom axis, 3, 0⟩, ⟨subject, result, axis, 0⟩]) [],
          result) := by
  simp only [op0, genComputeSkeleton, h]

theorem gen_op4 (n : ℕ) {subject tail callResult result : Noun}
    {callTree : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result) :
    genComputeSkeleton (K := K) (n + 1) subject (op4 tail) =
      .ok (.node (skelNode
            (genSkelOp4 subject (op4 tail) (.atom 4) tail subject tail callResult result)
            [⟨op4 tail, tail, 3, 0⟩]) [callTree], result) := by
  simp only [op4, genComputeSkeleton, h, hinc]

theorem gen_op5 (n : ℕ) {subject b c sf1 sf2 : Noun}
    {bTree cTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2)) :
    genComputeSkeleton (K := K) (n + 1) subject (op5 b c) =
      .ok (.node (skelNode
            (genSkelOp5 subject (op5 b c) (.atom 5) (.cell b c) b c sf1 sf2
              (Noun.tis sf1 sf2))
            [⟨op5 b c, .cell b c, 3, 0⟩, ⟨.cell b c, b, 2, 0⟩])
            [bTree, cTree], Noun.tis sf1 sf2) := by
  simp only [op5, genComputeSkeleton, hb, hc]

theorem gen_op6_zero (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (takenTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) =
      .ok (.node (skelNode
            (genSkelOp6 subject (op6 b c d) (.atom 6) (.cell b (.cell c d))
              b (.cell c d) c d (.atom 0) c result)
            [⟨op6 b c d, .cell b (.cell c d), 3, 0⟩,
             ⟨.cell b (.cell c d), b, 2, 0⟩,
             ⟨.cell c d, c, 2, 0⟩])
            [condTree, takenTree], result) := by
  simp only [op6, genComputeSkeleton, hb, hc]

theorem gen_op6_one (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n subject d = .ok (takenTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) =
      .ok (.node (skelNode
            (genSkelOp6 subject (op6 b c d) (.atom 6) (.cell b (.cell c d))
              b (.cell c d) c d (.atom 1) d result)
            [⟨op6 b c d, .cell b (.cell c d), 3, 0⟩,
             ⟨.cell b (.cell c d), b, 2, 0⟩,
             ⟨.cell c d, c, 2, 0⟩])
            [condTree, takenTree], result) := by
  simp only [op6, genComputeSkeleton, hb, hd]

theorem gen_op7 (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject (op7 b c) =
      .ok (.node (skelNode
            (genSkelOp7 subject (op7 b c) (.atom 7) (.cell b c) b c sb result)
            [⟨op7 b c, .cell b c, 3, 0⟩, ⟨.cell b c, b, 2, 0⟩])
            [bTree, cTree], result) := by
  simp only [op7, genComputeSkeleton, hb, hc]

theorem gen_op9 (n : ℕ) {subject c core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree : NTree (GenComputeRow K)}
    (hc : genComputeSkeleton (K := K) n subject c = .ok (coreTree, core))
    (hslot : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) n core arm = .ok (invokeTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) =
      .ok (.node (skelNode
            (genSkelOp9 subject
              (.cell (.atom 9) (.cell (.atom axis) c))
              (.atom 9) (.cell (.atom axis) c) (.atom axis) c core arm result axis)
            [⟨.cell (.atom 9) (.cell (.atom axis) c), .cell (.atom axis) c, 3, 0⟩,
             ⟨.cell (.atom axis) c, .atom axis, 2, 0⟩,
             ⟨core, arm, axis, 0⟩])
            [coreTree, invokeTree], result) := by
  simp only [genComputeSkeleton, hc, hslot, harm]

theorem gen_cons (n : ℕ)
    {subject leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree : NTree (GenComputeRow K)}
    (hl : genComputeSkeleton (K := K) n subject (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n subject tail = .ok (rTree, rRes)) :
    genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.cell leftHead leftTail) tail) =
      .ok (.node (skelNode (genSkelCons subject (.cell leftHead leftTail) tail lRes rRes)
            [⟨.cell (.cell leftHead leftTail) tail, tail, 3, 0⟩])
            [lTree, rTree], .cell lRes rRes) := by
  simp only [genComputeSkeleton, hl, hr]

theorem gen_invokeAxis (n : ℕ) {subject core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree : NTree (GenComputeRow K)}
    (hcore : genComputeSkeleton (K := K) (n + 2) subject (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm = .ok (invokeTree, result)) :
    genComputeSkeleton (K := K) (n + 3) subject (invokeAxis axis) =
      .ok (.node (skelNode
            (genSkelOp9 subject (invokeAxis axis) (.atom 9)
              (.cell (.atom axis) (op0 1)) (.atom axis) (op0 1)
              core arm result axis)
            [⟨invokeAxis axis, .cell (.atom axis) (op0 1), 3, 0⟩,
             ⟨.cell (.atom axis) (op0 1), .atom axis, 2, 0⟩,
             ⟨core, arm, axis, 0⟩])
            [coreTree, invokeTree], result) := by
  simpa [invokeAxis, op0] using gen_op9 (n + 2) hcore hslotA harm

theorem gen_slam (n : ℕ) {axis : ℕ}
    {subject bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) (n + 3) subject (.cell bHead bTail) =
      .ok (battTree, battery))
    (hs : genComputeSkeleton (K := K) (n + 3) subject sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (.cell battery sample) arm =
      .ok (invokeTree, result)) :
    ∃ t l r, genComputeSkeleton (K := K) (n + 5) subject
        (slam (.cell bHead bTail) sampleF axis) = .ok (t, result) ∧
      t.children = [l, r] ∧ ¬ l.isLeaf ∧
      t.label.skel.state = State.s7 ∧ r.label.skel.state = State.s9 ∧
      invokeTree ∈ r.children := by
  have hpair :=
    gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore :=
    gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  have hop := gen_op7 (K := K) (n + 4) hpair hax
  refine ⟨_, _, _, by simpa [slam] using hop, rfl, ?_, rfl, rfl, ?_⟩
  · simp [NTree.isLeaf]
  · simp [NTree.children]

theorem gen_addArm_done (n : ℕ) (acc m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc) := by
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h15
  rw [tis_self m] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  exact ⟨_, by simpa [addArm] using gen_op6_zero (K := K) (n + 5) hcond hthen⟩

theorem gen_addNewSample (n acc i m : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) := by
  have h6 := gen_op0 (K := K) (n + 2) (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := gen_op0 (K := K) (n + 1) (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := gen_op0 (K := K) (n + 2) (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := gen_op4 (K := K) (n + 3) h6 (lus_nat acc)
  have hincI := gen_op4 (K := K) (n + 2) h14 (lus_nat i)
  have hinner := gen_cons (K := K) (n + 3) hincI h15
  exact ⟨_, gen_cons (K := K) (n + 4) hincA hinner⟩

theorem gen_addArm_one (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1)) := by
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_addNewSample (K := K) (n + 8) acc 0 1
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone⟩ := gen_addArm_done (K := K) (n + 7) (.atom (acc + 1)) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  exact ⟨_, by simpa [addArm, slam, op0] using hop6⟩

theorem gen_add_1_1 :
    ∃ t l r, genComputeSkeleton (K := K) 32 (.atom 0) (addCall (.atom 1) (.atom 1)) =
      .ok (t, .atom 2) ∧ t.children = [l, r] ∧ ¬ l.isLeaf ∧
      t.label.skel.state = State.s7 ∧ r.label.skel.state = State.s9 := by
  have hqB := gen_quote (K := K) 29 (.atom 0) addArm
  have hqS := gen_quote (K := K) 29 (.atom 0) (addSample (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone⟩ := gen_addArm_one (K := K) 14 1
  obtain ⟨t, l, r, ht, hch, hnl, hs7, hs9, _⟩ := gen_slam (K := K) 27 (axis := 2)
    (bHead := .atom 1) (bTail := addArm) hqB hqS
    (addCore_slot2 (.atom 1) (.atom 0) (.atom 1)) hdone
  exact ⟨t, l, r, by simpa [addCall, slam, quote] using ht, hch, hnl, hs7, hs9⟩

theorem gen_add_1_1_ok :
    ∃ t, genComputeSkeleton (K := K) 32 (.atom 0) (addCall (.atom 1) (.atom 1)) =
      .ok (t, .atom 2) := by
  obtain ⟨t, _, _, ht, _, _, _, _⟩ := gen_add_1_1 (K := K)
  exact ⟨t, ht⟩

noncomputable def addTree : NTree (GenComputeRow K) :=
  (gen_add_1_1_ok (K := K)).choose

theorem addTree_gen :
    genComputeSkeleton (K := K) 32 (.atom 0) (addCall (.atom 1) (.atom 1)) =
      .ok (addTree, .atom 2) :=
  (gen_add_1_1_ok (K := K)).choose_spec

theorem addTree_eq_of_gen {t : NTree (GenComputeRow K)}
    (ht : genComputeSkeleton (K := K) 32 (.atom 0) (addCall (.atom 1) (.atom 1)) =
      .ok (t, .atom 2)) :
    addTree (K := K) = t := by
  have h := addTree_gen (K := K)
  rw [ht] at h
  injection h with h'
  exact (Prod.mk.inj h').1.symm

theorem addTree_not_isPathTree :
    ¬ isPathTree (addTree (K := K)) := by
  obtain ⟨t, _, _, ht, hch, _, _, _⟩ := gen_add_1_1 (K := K)
  have heq := addTree_eq_of_gen ht
  intro hp
  rw [heq] at hp
  have hlen : t.children.length = 2 := by rw [hch]; simp
  cases t with
  | node _lab cs =>
    rw [isPathTree_iff] at hp
    simp [NTree.children] at hlen
    omega

theorem addTree_not_childrenAreLeaves :
    ¬ childrenAreLeaves (addTree (K := K)) := by
  obtain ⟨t, l, _, ht, hch, hnl, _, _⟩ := gen_add_1_1 (K := K)
  have heq := addTree_eq_of_gen ht
  intro hc
  have hlmem : l ∈ (addTree (K := K)).children := by
    rw [heq, hch]; exact List.mem_cons.mpr (Or.inl rfl)
  exact hnl (hc l hlmem)

noncomputable def addTimestampSkeleton :
    SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (addTree (K := K)))) :=
  genComputeTimestampSkeleton K addTree

theorem addTimestampSkeleton_nonvacuous :
    Nonempty (SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (addTree (K := K))))) :=
  ⟨addTimestampSkeleton⟩

theorem addTree_root_s7 :
    (addTree (K := K)).label.skel.state = State.s7 := by
  obtain ⟨t, _, _, ht, _, _, hs7, _⟩ := gen_add_1_1 (K := K)
  have heq := addTree_eq_of_gen ht
  simpa [heq] using hs7

theorem addTree_has_s9 :
    ∃ u ∈ (addTree (K := K)).children, u.label.skel.state = State.s9 := by
  obtain ⟨t, _, r, ht, hch, _, _, hs9⟩ := gen_add_1_1 (K := K)
  have heq := addTree_eq_of_gen ht
  refine ⟨r, ?_, hs9⟩
  rw [heq, hch]
  exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-! ## MAC generator -- same fuels as the eval lemmas -/

theorem gen_macArm_done (n : ℕ) (acc k m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc) := by
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h30
  rw [tis_self k] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  exact ⟨_, by simpa [macArm] using gen_op6_zero (K := K) (n + 5) hcond hthen⟩

theorem gen_macArm_zero (n : ℕ) (acc m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (macCore acc (.atom 0) m) macArm =
      .ok (t, acc) :=
  gen_macArm_done n acc (.atom 0) m

theorem gen_macSampleF (n : ℕ)
    {subject aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree : NTree (GenComputeRow K)}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m)) :
    ∃ t, genComputeSkeleton (K := K) (n + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      .ok (t, .cell acc (.cell (.atom 0) (.cell k m))) := by
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n subject 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  exact ⟨_, gen_cons (K := K) (n + 2) ha hinner⟩

theorem gen_invokeMac (n : ℕ)
    {subject aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree : NTree (GenComputeRow K)}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result)) :
    ∃ t l r, genComputeSkeleton (K := K) (n + 5) subject
        (invokeMac (.cell aH aT) (.cell nH nT) mF) = .ok (t, result) ∧
      t.children = [l, r] ∧ ¬ l.isLeaf ∧
      t.label.skel.state = State.s7 ∧ r.label.skel.state = State.s9 := by
  have hqB := gen_quote (K := K) (n + 2) subject mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  obtain ⟨t, l, r, ht, hch, hnl, hs7, hs9, _⟩ := gen_slam (K := K) n (axis := 4)
    (bHead := .atom 1) (bTail := mmBattery) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm
  exact ⟨t, l, r, by simpa [invokeMac, slam, quote, macCore, macCoreAt] using ht,
    hch, hnl, hs7, hs9⟩

theorem gen_addFromMac_m0 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc) := by
  have h5 := gen_op0 (K := K) (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := gen_op0 (K := K) (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := gen_op1 (K := K) (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := gen_op0 (K := K) (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := gen_cons (K := K) (n + 8) hz hm
  have hsmpl := gen_cons (K := K) (n + 9) hacc hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_done (K := K) (n + 4) (.atom acc) (.atom 0)
  obtain ⟨t, _, _, ht, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  exact ⟨t, by simpa [addFromMac, slam, op0, op1, macCore] using ht⟩

theorem gen_addFromMac_m1 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1)) := by
  have h5 := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := gen_op0 (K := K) (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := gen_op1 (K := K) (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := gen_op0 (K := K) (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := gen_cons (K := K) (n + 17) hz hm
  have hsmpl := gen_cons (K := K) (n + 18) haccS hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_one (K := K) (n + 3) acc
  obtain ⟨t, _, _, ht, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  exact ⟨t, by simpa [addFromMac, slam, op0, op1, macCore] using ht⟩

theorem gen_macNewSample_m0 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m0 (K := K) (n + 1) acc
  have h14 := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := gen_op4 (K := K) (n + 11) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := gen_cons (K := K) (n + 11) hn hm
  have hrest := gen_cons (K := K) (n + 12) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 13)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom acc) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 13) hadd' hrest
  simpa [macNewSample, addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using
    (⟨_, hcell⟩ : ∃ t, genComputeSkeleton (K := K) (n + 14)
      (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0))
      (.cell
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2)))
        (.cell (op4 (op0 14)) (.cell (op0 30) (op0 31)))) =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))))

theorem gen_macArm_one_m0 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc) := by
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m0 (K := K) (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 13) (.atom acc) (.atom 1) (.atom 0)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  exact ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6⟩

theorem gen_macNewSample_m1 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m1 (K := K) (n + 1) acc
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := gen_op4 (K := K) (n + 20) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := gen_cons (K := K) (n + 20) hn hm
  have hrest := gen_cons (K := K) (n + 21) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 22)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom (acc + 1)) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 22) hadd' hrest
  simpa [macNewSample, addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using
    (⟨_, hcell⟩ : ∃ t, genComputeSkeleton (K := K) (n + 23)
      (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1))
      (.cell
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2)))
        (.cell (op4 (op0 14)) (.cell (op0 30) (op0 31)))) =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))))

theorem gen_macArm_one_m1 (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)) := by
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m1 (K := K) (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  exact ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6⟩

/-! ## 2×2 generator -/

theorem gen_mmC00 (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 = .ok (t, .atom 2) := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m1 (K := K) (n + 20) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 1
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b10 outerA
  exact ⟨houterT, by simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using houter⟩

theorem gen_mmC01 (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 = .ok (t, .atom 1) := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m0 (K := K) (n + 29) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b11 outerA
  exact ⟨houterT, by simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] using houter⟩

theorem gen_mmC10 (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 = .ok (t, .atom 1) := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 1)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b10 outerA
  exact ⟨houterT, by simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using houter⟩

theorem gen_mmC11 (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 = .ok (t, .atom 1) := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 0)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b11 outerA
  exact ⟨houterT, by simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] using houter⟩

theorem gen_mm :
    ∃ t l r, genComputeSkeleton (K := K) 64 mmSubject mmFormula =
      .ok (t, mmC) ∧ t.children = [l, r] ∧ ¬ l.isLeaf ∧ ¬ r.isLeaf ∧
        t.label.requests.length = 1 := by
  obtain ⟨t00, h00⟩ := gen_mmC00 (K := K) 6
  obtain ⟨t01, h01⟩ := gen_mmC01 (K := K) 6
  obtain ⟨t10, h10⟩ := gen_mmC10 (K := K) 6
  obtain ⟨t11, h11⟩ := gen_mmC11 (K := K) 6
  have h00c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 12))
              (.cell (op1 0) (.cell (op0 9) (op0 14)))))
            (invokeAxis 4))) = .ok (t00, .atom 2) := by
    simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1] using h00
  have h01c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 13))
              (.cell (op1 0) (.cell (op0 9) (op0 15)))))
            (invokeAxis 4))) = .ok (t01, .atom 1) := by
    simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1] using h01
  have h10c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 12))
              (.cell (op1 0) (.cell (op0 11) (op0 14)))))
            (invokeAxis 4))) = .ok (t10, .atom 1) := by
    simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1] using h10
  have h11c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 13))
              (.cell (op1 0) (.cell (op0 11) (op0 15)))))
            (invokeAxis 4))) = .ok (t11, .atom 1) := by
    simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1] using h11
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have hshape :
      ∃ t l r,
        genComputeSkeleton (K := K) 64 mmSubject
          (.cell
            (.cell
              (.cell (.atom 7)
                (.cell (.cell (quote mmBattery)
                  (.cell (invokeMac (op1 0) (op0 8) (op0 12))
                    (.cell (op1 0) (.cell (op0 9) (op0 14)))))
                  (invokeAxis 4)))
              (.cell (.atom 7)
                (.cell (.cell (quote mmBattery)
                  (.cell (invokeMac (op1 0) (op0 8) (op0 13))
                    (.cell (op1 0) (.cell (op0 9) (op0 15)))))
                  (invokeAxis 4))))
            (.cell
              (.cell (.atom 7)
                (.cell (.cell (quote mmBattery)
                  (.cell (invokeMac (op1 0) (op0 10) (op0 12))
                    (.cell (op1 0) (.cell (op0 11) (op0 14)))))
                  (invokeAxis 4)))
              (.cell (.atom 7)
                (.cell (.cell (quote mmBattery)
                  (.cell (invokeMac (op1 0) (op0 10) (op0 13))
                    (.cell (op1 0) (.cell (op0 11) (op0 15)))))
                  (invokeAxis 4))))) =
          .ok (t, mmC) ∧ t.children = [l, r] ∧ ¬ l.isLeaf ∧ ¬ r.isLeaf ∧
            t.label.requests.length = 1 :=
    ⟨_, _, _, by simpa [mmC] using hop, rfl, by simp [NTree.isLeaf],
      by simp [NTree.isLeaf], by simp [skelNode]⟩
  simpa [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] using hshape

theorem gen_mm_ok :
    ∃ t, genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC) := by
  obtain ⟨t, _, _, ht, _, _, _, _⟩ := gen_mm (K := K)
  exact ⟨t, ht⟩

noncomputable def mmTree : NTree (GenComputeRow K) :=
  (gen_mm_ok (K := K)).choose

theorem mmTree_gen :
    genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (mmTree, mmC) :=
  (gen_mm_ok (K := K)).choose_spec

/-- AIR child-order twin of the generated DFS tree. -/
noncomputable def mmTreeAir : NTree (GenComputeRow K) :=
  airReorder (mmTree (K := K))

theorem mmTreeAir_label :
    (mmTreeAir (K := K)).label = (mmTree (K := K)).label :=
  airReorder_label _

theorem mmTree_eq_of_gen {t : NTree (GenComputeRow K)}
    (ht : genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC)) :
    mmTree (K := K) = t := by
  have h := mmTree_gen (K := K)
  rw [ht] at h
  injection h with h'
  exact (Prod.mk.inj h').1.symm

theorem mmTree_root_requests_length :
    (mmTree (K := K)).label.requests.length = 1 := by
  obtain ⟨t, _, _, ht, _, _, _, hreq⟩ := gen_mm (K := K)
  have heq := mmTree_eq_of_gen ht
  rw [heq]
  exact hreq

theorem mmTree_not_isPathTree :
    ¬ isPathTree (mmTree (K := K)) := by
  obtain ⟨t, _, _, ht, hch, _, _, _⟩ := gen_mm (K := K)
  have heq := mmTree_eq_of_gen ht
  intro hp
  rw [heq] at hp
  have hlen : t.children.length = 2 := by rw [hch]; simp
  cases t with
  | node _lab cs =>
    rw [isPathTree_iff] at hp
    simp [NTree.children] at hlen
    omega

theorem mmTree_not_childrenAreLeaves :
    ¬ childrenAreLeaves (mmTree (K := K)) := by
  obtain ⟨t, l, _, ht, hch, hnl, _, _⟩ := gen_mm (K := K)
  have heq := mmTree_eq_of_gen ht
  intro hc
  have hlmem : l ∈ (mmTree (K := K)).children := by
    rw [heq, hch]; exact List.mem_cons.mpr (Or.inl rfl)
  exact hnl (hc l hlmem)

noncomputable def mmTimestampSkeleton :
    SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (mmTree (K := K)))) :=
  genComputeTimestampSkeleton K mmTree

theorem mmTimestampSkeleton_nonvacuous :
    Nonempty (SemanticTimestampSkeleton K K
      (genComputeSemanticSkeleton (bfsAssign (mmTree (K := K))))) :=
  ⟨mmTimestampSkeleton⟩

#print axioms mm_eval
#print axioms add_1_1_eval
#print axioms gen_add_1_1
#print axioms gen_mm
#print axioms addTimestampSkeleton
#print axioms mmTimestampSkeleton

end Nock.NockVMROM.Thm54.TraceGen
