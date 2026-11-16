/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomCombJ8.lean

* **`combL`** (the right comb of a limb list: `[a, b] ↦ [a b]`, `a :: l ↦ [a (combL l)]`) and **`combN n`**
    (the comb of `n`'s base-`B` digits): the `comb` of `RecOKAJ8.RecOKA`.
  * **`combN_of_denotes`**: a denoted limb list is canonical (`Nat.digits B (val l) = l`) when the limbs are
    `< B` (g1, `LimbsBounded`) and every top row's limb is nonzero (g3, `TopNZ`); so `combN (val l) = combL l`.
  * **`decode_denotes`**: on a table whose rows agree with the ℕ reading `r` (`AgreeRow`: `wL = 0` (g2), the
    left limb, the right child as serial `idR` with `wR = 1` or limb `aR` with `wR = 0`), every successful
    decode of serial `i` is `combL l` for some `l` with `Denotes r i l`.  `denH_denotes`: the same for
    `denH t (true, i)` under `SerialOK`.
  * **`hold_of_rows`**: `FinalJ8`'s `hold` (an inc row's old handle denotes) from `ConsumeServedQ` (the old
    export is some row `j < n` with `idx = idxO`), the rows' decode (`row_genuine`-shaped `hdec`), and
    `decode_denotes`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads LimbsBounded ConsumeServedQ)
open Nock.Atoms (val B)

noncomputable section

/-! ## 1. The canonical comb -/

/-- **The right comb of a limb list**: `[a, b] ↦ [a b]`, `a :: l ↦ [a (combL l)]`. -/
def combL : List ℕ → Noun
  | [] => .atom 0
  | [a] => .atom a
  | a :: b :: l => .cell (.atom a) (combL (b :: l))

/-- **The canonical comb of a value**: the comb of its base-`B` digits. -/
def combN (n : ℕ) : Noun := combL (Nat.digits B n)

/-- g3: every top row (`wR = 0`) has a nonzero top limb. -/
def TopNZ (r : ℕ → ARow) : Prop := ∀ j, (r j).wR = 0 → (r j).aR ≠ 0

theorem denotes_len {r : ℕ → ARow} {i : ℕ} {l : List ℕ} (h : Denotes r i l) : 2 ≤ l.length := by
  induction h with
  | top _ => simp
  | step _ _ ih => simp; omega

theorem denotes_last_ne {r : ℕ → ARow} (hT : TopNZ r) {i : ℕ} {l : List ℕ} (h : Denotes r i l) :
    ∀ hl : l ≠ [], l.getLast hl ≠ 0 := by
  induction h with
  | @top j hw => intro _; simpa using hT j hw
  | @step j l' _ hd ih =>
    intro _
    have h2 := denotes_len hd
    have hne : l' ≠ [] := by intro e; rw [e] at h2; simp at h2
    rw [List.getLast_cons hne]
    exact ih hne

/-- **A denoted limb list is canonical.** -/
theorem digits_val_of_denotes {r : ℕ → ARow} (hB : LimbsBounded r) (hT : TopNZ r) {i : ℕ} {l : List ℕ}
    (h : Denotes r i l) : Nat.digits B (val l) = l :=
  Nat.digits_ofDigits B Nock.Atoms.one_lt_B l (Denotes.bounded hB h) (denotes_last_ne hT h)

theorem combN_of_denotes {r : ℕ → ARow} (hB : LimbsBounded r) (hT : TopNZ r) {i : ℕ} {l : List ℕ}
    (h : Denotes r i l) : combN (val l) = combL l := by
  rw [combN, digits_val_of_denotes hB hT h]

/-! ## 2. The decode of an agreeing table is the canonical comb of a denoted limb list -/

section Decode
variable {q : ℕ}

/-- **A table row agrees with the ℕ reading** of its serial: `wL = 0` (g2), the left limb (`< B`, g1), the
right child as the serial `idR` (`wR = 1`) or as the top limb `aR` (`wR = 0`; `< B` and nonzero, g1 / g3). -/
structure AgreeRow (c : CellRowB0 q) (a : ARow) : Prop where
  wL : c.wL = false
  aL : c.aL.val = a.aL
  aLB : a.aL < B
  wR1 : c.wR = true → a.wR = 1 ∧ c.idR = a.idR
  wR0 : c.wR = false → a.wR = 0 ∧ c.aR.val = a.aR ∧ a.aR < B ∧ a.aR ≠ 0

/-- A limb list is canonical: limbs `< B`, last limb nonzero. -/
def Canon (l : List ℕ) : Prop := (∀ x ∈ l, x < B) ∧ ∀ h : l ≠ [], l.getLast h ≠ 0

theorem combN_of_canon {l : List ℕ} (h : Canon l) : combN (val l) = combL l := by
  rw [combN, val, Nat.digits_ofDigits B Nock.Atoms.one_lt_B l h.1 h.2]

theorem decode_denotes {t : List (CellRowB0 q)} {r : ℕ → ARow} (hag : ∀ c ∈ t, AgreeRow c (r c.idx)) :
    ∀ f i T, decodeKey t f i = some T → ∃ l, Denotes r i l ∧ T = combL l ∧ Canon l := by
  intro f
  induction f with
  | zero => intro i T h; simp [decodeKey] at h
  | succ f ih =>
    intro i T h
    simp only [decodeKey, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, a, ha, b, hb, hT⟩ := h
    simp only [Option.some.injEq] at hT
    subst hT
    obtain ⟨hmem, hidx⟩ := rowByKey_spec hc
    have A := hag c hmem
    rw [hidx] at A
    rw [A.wL] at ha
    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ha
    subst ha
    cases hw : c.wR
    · rw [hw] at hb
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hb
      subst hb
      obtain ⟨h0, haR, hRB, hR0⟩ := A.wR0 hw
      refine ⟨[(r i).aL, (r i).aR], Denotes.top h0, by rw [A.aL, haR]; rfl, ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | rfl; exact A.aLB; exact hRB
      · intro _; simpa using hR0
    · rw [hw] at hb
      simp only [↓reduceIte] at hb
      obtain ⟨h1, hidR⟩ := A.wR1 hw
      obtain ⟨l, hl, rfl, hcB, hcL⟩ := ih _ _ hb
      rw [hidR] at hl
      have h2 := denotes_len hl
      have hne : l ≠ [] := by intro e; rw [e] at h2; simp at h2
      refine ⟨(r i).aL :: l, Denotes.step h1 hl, ?_, ?_, ?_⟩
      · match l, h2 with
        | x :: y :: l'', _ => rw [A.aL]; rfl
      · intro x hx; simp at hx; rcases hx with rfl | hx; exact A.aLB; exact hcB x hx
      · intro _; rw [List.getLast_cons hne]; exact hcL hne

/-- **`denH` of a serial on an agreeing table is the canonical comb of a denoted limb list.** -/
theorem denH_denotes {t : List (CellRowB0 q)} {r : ℕ → ARow} (hs : SerialOK t)
    (hag : ∀ c ∈ t, AgreeRow c (r c.idx)) {i : ℕ} {T : Noun} (h : denH t (true, i) = some T) :
    ∃ l, Denotes r i l ∧ T = combL l ∧ combN (val l) = combL l := by
  rw [denH_cell, preZNounOfTable, decodeB0_eq_decodeKey hs] at h
  obtain ⟨l, hl, hT, hc⟩ := decode_denotes hag _ _ _ h
  exact ⟨l, hl, hT, combN_of_canon hc⟩

/-- A decoded serial is a row of the table. -/
theorem denH_true_lt {t : List (CellRowB0 q)} {i : ℕ} {T : Noun}
    (h : denH t (true, i) = some T) : i < t.length := by
  rw [denH_cell, preZNounOfTable, show fuelChip = (fuelChip - 1) + 1 by unfold fuelChip; norm_num] at h
  simp only [decodeB0, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- A decoded serial is a cell. -/
theorem denH_true_cell {t : List (CellRowB0 q)} {i : ℕ} {T : Noun} (h : denH t (true, i) = some T) :
    ∃ a c, T = .cell a c := by
  rw [denH_cell, preZNounOfTable, show fuelChip = (fuelChip - 1) + 1 by unfold fuelChip; norm_num] at h
  simp only [decodeB0, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, a, _, c, _, hT⟩ := h
  exact ⟨a, c, (Option.some.inj hT).symm⟩

end Decode

/-! ## 3. The atom table: its rows agree with the ℕ reading -/

section Atom
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF atom_base)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
  (chalsA pubsA : ℕ → K)
  (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])

/-- The cell-table rows of the restricted atom trace read the atom trace's base columns. -/
theorem restr_trace (i : Fin nA) {c : ℕ} (hc : c < 129) :
    (cellEnvF b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)
      i).trace c = (aEF b nodesA orbitA chalsA pubsA QA i).trace c := by
  have hw : (cellChip δ b hnA nodesA orbitA chalsA pubsA).rap.w = 225 :=
    (cellChip_fingerprint δ b hnA nodesA orbitA chalsA pubsA).1
  erw [cellEnvF, AtomChipHQ.restrictAtomCell,
    envOfTrace_restrict_trace (cv' := slotVal b 205 chalsA) (pv' := slotVal b 205 pubsA) _ _ _ _ _ _ _ _
      (by rw [hw]; omega)]
  simp only [shiftCol, if_pos (show c < 129 by omega)]
  rfl

variable {δ b hnA nodesA orbitA chalsA pubsA QA} in
/-- The atom gates g2 / g3 at a row, read in ℕ: `wL = 0`, and a top row's limb is nonzero. -/
theorem atom_g23 (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (i : Fin nA) :
    (aEF b nodesA orbitA chalsA pubsA QA i).trace Cell.wL = 0 ∧
      ((aEF b nodesA orbitA chalsA pubsA QA i).trace Cell.wR = 0 →
        (aEF b nodesA orbitA chalsA pubsA QA i).trace Cell.aR ≠ 0) := by
  have hg := atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat i
  have g2 := hg (cv Cell.wL) (List.mem_append_right _ (by simp [AtomChipHQ.atomGates, AtomChipHQ.g23]))
  have g3 := hg (.mul (notE (cv Cell.wR)) (.sub (.mul (cv Cell.aR) (cv AtomChipHQ.invT)) (.const 1)))
    (List.mem_append_right _ (by simp [AtomChipHQ.atomGates, AtomChipHQ.g23]))
  simp only [CoeffExpr.eval, cv, notE] at g2 g3
  refine ⟨g2, fun h0 hR => ?_⟩
  rw [h0, hR] at g3
  simp at g3

variable {δ b hnA nodesA orbitA chalsA pubsA QA} in
/-- **The atom table's rows agree with the ℕ reading `rA`** (`Reads`, `Small`, `idx = k`, `LimbsBounded`,
boolean `wR`; g2 / g3 from the gates). -/
theorem agree_atom (hq : 2 ^ 63 < p)
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {rA : ℕ → ARow} (hRA : ∀ k : Fin nA, Reads (aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, (rA k).Small) (hidxA : ∀ k : Fin nA, (rA k).idx = k) (hB : LimbsBounded rA)
    (hwR : ∀ k : Fin nA, (rA k).wR ≤ 1) :
    ∀ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA
        (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).map (·.b0),
      c.idx < nA ∧ AgreeRow c (rA c.idx) := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  intro c hc
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  have R := hRA i
  obtain ⟨s1, s2, s3, s4, s5, -⟩ := hsA i
  obtain ⟨g2, g3⟩ := atom_g23 hsat i
  have tr : ∀ {c : ℕ}, c < 129 → (cellEnvF b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i).trace c =
      (aEF b nodesA orbitA chalsA pubsA QA i).trace c := fun hc => restr_trace δ b hnA nodesA orbitA chalsA
        pubsA QA i hc
  have nc : ∀ {x : ℕ}, x < 2 ^ 62 → natOf ((x : ℕ) : ZMod p) = x := fun hx =>
    natOf_natCast hF (by rw [hrc]; omega)
  have vc : ∀ {x : ℕ}, x < 2 ^ 62 → (((x : ℕ) : ZMod (ringChar (ZMod p)))).val = x := fun hx => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [hrc]; omega)]
  have ce : ∀ {x y : ℕ}, x < 2 ^ 62 → y < 2 ^ 62 → (x : ZMod p) = y → x = y := fun hx hy h =>
    AtomChipHQ.cast_inj (F := ZMod p) (by rw [hrc]; exact hq) (by omega) (by omega) h
  have hidx : (cellB0Of (cellEnvF b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i)).idx = i := by
    simp only [cellB0Of]
    rw [tr (by decide), R.idx, nc s1, hidxA i]
  simp only [cellTableOf, cellRowOf]
  refine ⟨by rw [hidx]; exact i.2, ?_⟩
  rw [hidx]
  refine ⟨?_, ?_, (hB i).1, ?_, ?_⟩
  · simp only [cellB0Of]; rw [tr (by decide), g2]; simp
  · simp only [cellB0Of]; rw [tr (by decide), R.aL, nc s2, vc s2]
  · intro hw
    simp only [cellB0Of, decide_eq_true_eq] at hw
    rw [tr (by decide), R.wR] at hw
    have h1 : (rA i).wR = 1 := ce s3 (by norm_num) (by simpa using hw)
    refine ⟨h1, ?_⟩
    simp only [cellB0Of]; rw [tr (by decide), R.idR, nc s4]
  · intro hw
    simp only [cellB0Of, decide_eq_false_iff_not] at hw
    rw [tr (by decide), R.wR] at hw
    have h0 : (rA i).wR = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hwR i) with h | h
      · exact h
      · exact absurd (by rw [h]; simp) hw
    refine ⟨h0, ?_, (hB i).2, ?_⟩
    · simp only [cellB0Of]; rw [tr (by decide), R.aR, nc s5, vc s5]
    · intro hz
      apply g3 (by rw [R.wR, h0]; simp)
      rw [R.aR, hz]; simp

variable {δ b hnA nodesA orbitA chalsA pubsA QA} in
/-- **`hold`** (`FinalJ8`): every inc row's old handle denotes.  The consume (`ConsumeServedQ`, from the atom
export balance by `consumeServedQ_of_balance`) names a row `j < n` with `idx = idxO`; that row decodes
(`row_genuine` on `atomTable_accepts`); the decode is a denoted limb list (`denH_denotes`, `agree_atom`). -/
theorem hold_of_served (hq : 2 ^ 63 < p)
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {rA : ℕ → ARow} (hRA : ∀ k : Fin nA, Reads (aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, (rA k).Small) (hidxA : ∀ k : Fin nA, (rA k).idx = k) (hB : LimbsBounded rA)
    (hwR : ∀ k : Fin nA, (rA k).wR ≤ 1)
    (hcs : ConsumeServedQ (AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA) nA) :
    ∀ k : Fin nA, (rA k).inc = 1 → ∃ l, Denotes rA (rA k).idxO l := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  intro k hinc
  have env_lt : ∀ i : Fin nA, AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA i =
      aEF b nodesA orbitA chalsA pubsA QA i := AtomServedQ.atomEnvN_lt b hnA nodesA orbitA chalsA pubsA QA
  have Rk := hRA k
  obtain ⟨j, hj, hkey⟩ := hcs k k.2 (by rw [env_lt k, Rk.inc, hinc, Nat.cast_one])
  have Rj := hRA ⟨j, hj⟩
  rw [show j = ((⟨j, hj⟩ : Fin nA) : ℕ) from rfl, env_lt ⟨j, hj⟩, env_lt k] at hkey
  have hwLj := (atom_g23 hsat ⟨j, hj⟩).1
  simp only [CellH.keyH, AtomChipHQ.oldKey, CellH.valE, List.map_cons, List.map_nil, CoeffExpr.eval,
    List.cons.injEq] at hkey
  have e1 := hkey.1
  rw [Rj.idx, Rk.idxO] at e1
  have s1 := (hsA ⟨j, hj⟩).1
  have t8 := (hsA k).2.2.2.2.2.2.2.1
  have hjo : j = (rA k).idxO := by
    refine (hidxA ⟨j, hj⟩).symm.trans ?_
    exact AtomChipHQ.cast_inj (F := ZMod p) (by rw [hrc]; exact hq) (by omega) (by omega) e1
  -- the row `j` decodes
  set tA := (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA))
  have hT := AtomChipHQ.atomTable_accepts δ b hnA nodesA orbitA chalsA pubsA hF (by rw [hrc]; exact hq) hz QA
    hsat hbind hinj hadj (by rw [hrc]; exact hnp) hserved []
  have hlen : tA.length = nA := by simp [tA, cellTableOf]
  have hjt : j < tA.length := by rw [hlen]; exact hj
  have hcm : tA[j] ∈ tA := List.getElem_mem hjt
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  obtain ⟨L, R, hd, -⟩ := Nock.NockVMROM.Thm54.VclL.row_genuine (by rw [hrc]; exact hq) hz hT hcm
  have hag := agree_atom hq hsat hRA hsA hidxA hB hwR
  obtain ⟨hlt, -⟩ := hag _ (List.mem_map_of_mem hcm)
  have hs := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsat) hF
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbind) hinj hadj
    (by rw [hrc]; exact hnp)
  have hidx : tA[j].b0.idx = j := by
    have h1 := List.getElem_of_eq hs (i := j) (by simpa using hjt)
    simpa using h1
  rw [hidx] at hd
  obtain ⟨l, hl, -⟩ := denH_denotes hs (fun c hc => (hag c hc).2) (i := j) (by rw [denH_cell]; exact hd)
  exact ⟨l, hjo ▸ hl⟩

end Atom

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
