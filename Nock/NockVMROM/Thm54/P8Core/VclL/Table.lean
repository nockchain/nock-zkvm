/-
  Nock/NockVMROM/Thm54/P8Core/VclL/Table.lean

  **1679; receipt `Batch1670`): the VCL-L cell table, abstractly, and T1 / T7 at the
  real NPR.**

  Here: the validity key is `(fp, hi, lo, idx)`; the serial gate `idx(i) = i` is
  `SerialOK`; `decodeB0` follows serials (a function of the committed round-0 data, read by the
  ANALYSIS, never by a gate); its recursion is on the certified rank (T7).

  * `CellRowB0` — the round-0 columns; `CellRow` — `b0` plus the B1 fingerprints `p l r`;
  * `RowOK` (cons gate = `FP.cons` at the seed, limb gates, range/booleanity as hypotheses, the
    atom gate), `SerialOK`, `ValidityBalanced` (`List.Perm` of expanded keys), `TableAccepts`;
  * `decodeB0` (reads `List CellRowB0` only — BY TYPE), `preZNounOfTable` (fuel `2^110`);
  * `mu_limbs_exact`, `rowOK_mu`, `rowOK_mu_lt` (the limb certificate is exact);
  * **T1** `decode_sound`, `preZNounOfTable_sound` (every row's `p` is `enc z` of the noun its
    round-0 columns decode to, leaves `= μ + 1 ≤ 2^110`), `row_genuine` (the children too),
    `decodeB0_strip`, `served_of_b0`;
  * **T7** `child_mu_lt`, `childRel_wf` (`mu_rank_wf` at the decode recursion).
-/
import Nock.GlobalCarryRecognizer
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. The table -/

/-- **A VCL-L cell row, round 0 (B0).**  Serial `idx`, child serials `idL idR`, weights `wL wR`
(`false` = atom child), atom values `aL aR` (base field), the rank limbs `lo hi` of the row and
`loL hiL loR hiR` of its children, the limb carry, the validity multiplicity `mv` and the export
multiplicity `mx`.  Everything here is committed before the seed. -/
structure CellRowB0 (q : ℕ) where
  idx : ℕ
  idL : ℕ
  idR : ℕ
  wL : Bool
  wR : Bool
  aL : ZMod q
  aR : ZMod q
  lo : ℕ
  hi : ℕ
  loL : ℕ
  hiL : ℕ
  loR : ℕ
  hiR : ℕ
  carry : ℕ
  mv : ℕ
  mx : ℕ
deriving DecidableEq

/-- **A VCL-L cell row**: the round-0 part and the B1 fingerprints (after the seed). -/
structure CellRow (q : ℕ) (Kfp : Type*) where
  b0 : CellRowB0 q
  p : FP Kfp
  l : FP Kfp
  r : FP Kfp

namespace CellRowB0
variable {q : ℕ}
/-- The certified rank `μ = hi·2^62 + lo` (`= λ − 1`). -/
def mu (c : CellRowB0 q) : ℕ := c.hi * 2 ^ 62 + c.lo
def muL (c : CellRowB0 q) : ℕ := c.hiL * 2 ^ 62 + c.loL
def muR (c : CellRowB0 q) : ℕ := c.hiR * 2 ^ 62 + c.loR
end CellRowB0

section Gates
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **The row predicate** (gates as hypotheses): the cons gate is `FP.cons` at the seed; the range certificates `lo < 2^62`, `hi < 2^48` on all three limb pairs and
carry booleanity; the two limb gates in `ZMod q`; the atom gate (a zero-weight child is the atom
named by its round-0 value, of rank `0`). -/
structure RowOK (z : Kfp) (c : CellRow q Kfp) : Prop where
  cons : c.p = FP.cons z c.l c.r
  lo_lt : c.b0.lo < 2 ^ 62
  loL_lt : c.b0.loL < 2 ^ 62
  loR_lt : c.b0.loR < 2 ^ 62
  hi_lt : c.b0.hi < 2 ^ 48
  hiL_lt : c.b0.hiL < 2 ^ 48
  hiR_lt : c.b0.hiR < 2 ^ 48
  carry_le : c.b0.carry ≤ 1
  limbLo : ((c.b0.lo : ZMod q) + (c.b0.carry : ZMod q) * 2 ^ 62 =
      (c.b0.loL : ZMod q) + (c.b0.loR : ZMod q) + 1)
  limbHi : ((c.b0.hi : ZMod q) = (c.b0.hiL : ZMod q) + (c.b0.hiR : ZMod q) + (c.b0.carry : ZMod q))
  atomL : c.b0.wL = false →
    c.l = FP.atomFP z (algebraMap (ZMod q) Kfp c.b0.aL) ∧ c.b0.loL = 0 ∧ c.b0.hiL = 0
  atomR : c.b0.wR = false →
    c.r = FP.atomFP z (algebraMap (ZMod q) Kfp c.b0.aR) ∧ c.b0.loR = 0 ∧ c.b0.hiR = 0

/-- **The serial threading gate** `idx(0) = 0`, `idx(i+1) = idx(i) + 1`, as its consequence. -/
def SerialOK (t : List (CellRowB0 q)) : Prop := t.map (·.idx) = List.range t.length

/-- Validity keys `(fp, hi, lo, idx)`: content, certified rank and round-0 serial. -/
abbrev VKey (Kfp : Type*) := FP Kfp × ℕ × ℕ × ℕ

/-- Expand a multiplicity list into the multiset it denotes. -/
def expand {α : Type*} (l : List (α × ℕ)) : List α := l.flatMap fun kc => List.replicate kc.2 kc.1

/-- Validity provides: each row provides its own key `mv` times. -/
def vProv (t : List (CellRow q Kfp)) : List (VKey Kfp × ℕ) :=
  t.map fun c => ((c.p, c.b0.hi, c.b0.lo, c.b0.idx), c.b0.mv)

/-- Validity consumes: each weighted child is consumed once, keyed by the child serial. -/
def vCons (t : List (CellRow q Kfp)) : List (VKey Kfp × ℕ) :=
  t.flatMap fun c =>
    [((c.l, c.b0.hiL, c.b0.loL, c.b0.idL), if c.b0.wL then 1 else 0),
     ((c.r, c.b0.hiR, c.b0.loR, c.b0.idR), if c.b0.wR then 1 else 0)]

/-- **The validity multiset balance** (LogUp as a multiset equality): provides = the table's own
consumes plus the external lookups `vl` (the root bindings). -/
def ValidityBalanced (t : List (CellRow q Kfp)) (vl : List (VKey Kfp)) : Prop :=
  (expand (vProv t)).Perm (expand (vCons t ++ vl.map (·, 1)))

def ValidityServed (t : List (CellRow q Kfp)) : Prop :=
  ∀ c ∈ t,
    (c.b0.wL = true → ∃ c' ∈ t, c.l = c'.p ∧ c.b0.hiL = c'.b0.hi ∧ c.b0.loL = c'.b0.lo ∧
      c.b0.idL = c'.b0.idx) ∧
    (c.b0.wR = true → ∃ c' ∈ t, c.r = c'.p ∧ c.b0.hiR = c'.b0.hi ∧ c.b0.loR = c'.b0.lo ∧
      c.b0.idR = c'.b0.idx)

structure TableAccepts (z : Kfp) (t : List (CellRow q Kfp)) (vl : List (VKey Kfp)) : Prop where
  serial : SerialOK (t.map (·.b0))
  rows : ∀ c ∈ t, RowOK z c
  served : ValidityServed t

end Gates

/-! ## 2. The B0 decoder -/

section Decode
variable {q : ℕ}

/-- **The served noun of a serial, from round-0 columns only** (its argument is a list of
`CellRowB0`: it cannot read a fingerprint). -/
def decodeB0 (t : List (CellRowB0 q)) : ℕ → ℕ → Option Noun
  | 0, _ => none
  | fuel + 1, i =>
    (t[i]?).bind fun c =>
      (if c.wL then decodeB0 t fuel c.idL else some (.atom c.aL.val)).bind fun a =>
        (if c.wR then decodeB0 t fuel c.idR else some (.atom c.aR.val)).bind fun b =>
          some (.cell a b)

/-- The certified fuel: `μ < 2^110` on every accepted row (`lambda_chip`). -/
def fuelChip : ℕ := 2 ^ 110

/-- **`preZNounOfTable`**: the noun at serial `i`, decoded from the round-0 table. -/
def preZNounOfTable (t : List (CellRowB0 q)) (i : ℕ) : Option Noun := decodeB0 t fuelChip i

/-- More fuel decodes the same noun. -/
theorem decodeB0_mono (t : List (CellRowB0 q)) :
    ∀ f f' i n, f ≤ f' → decodeB0 t f i = some n → decodeB0 t f' i = some n
  | 0, _, _, _, _, h => by simp [decodeB0] at h
  | f + 1, f', i, n, hle, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    have hfg : f ≤ g := by omega
    simp only [decodeB0, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨c, hc, a, ha, b, hb, hn⟩ := h
    refine ⟨c, hc, a, ?_, b, ?_, hn⟩
    · split_ifs at ha ⊢
      · exact decodeB0_mono t f g _ a hfg ha
      · exact ha
    · split_ifs at hb ⊢
      · exact decodeB0_mono t f g _ b hfg hb
      · exact hb

/-- Decoded nouns are cells. -/
theorem decodeB0_isCell (t : List (CellRowB0 q)) :
    ∀ f i n, decodeB0 t f i = some n → ∃ a b, n = .cell a b
  | 0, _, _, h => by simp [decodeB0] at h
  | f + 1, i, n, h => by
    simp only [decodeB0, Option.bind_eq_some_iff] at h
    obtain ⟨c, -, a, -, b, -, hn⟩ := h
    exact ⟨a, b, (Option.some.inj hn).symm⟩

/-- Decoded atoms lie below `q` (they are `ZMod q` values read through `.val`). -/
theorem decodeB0_leafList_lt [NeZero q] (t : List (CellRowB0 q)) :
    ∀ f i n, decodeB0 t f i = some n → ∀ k ∈ n.leafList, k < q
  | 0, _, _, h => by simp [decodeB0] at h
  | f + 1, i, n, h => by
    simp only [decodeB0, Option.bind_eq_some_iff] at h
    obtain ⟨c, -, a, ha, b, hb, hn⟩ := h
    rw [Option.some.injEq] at hn
    subst hn
    have hA : ∀ k ∈ a.leafList, k < q := by
      split_ifs at ha
      · exact decodeB0_leafList_lt t f _ a ha
      · rw [Option.some.injEq] at ha; subst ha
        intro k hk; simp only [Noun.leafList, List.mem_singleton] at hk; subst hk
        exact ZMod.val_lt _
    have hB : ∀ k ∈ b.leafList, k < q := by
      split_ifs at hb
      · exact decodeB0_leafList_lt t f _ b hb
      · rw [Option.some.injEq] at hb; subst hb
        intro k hk; simp only [Noun.leafList, List.mem_singleton] at hk; subst hk
        exact ZMod.val_lt _
    intro k hk
    simp only [Noun.leafList, List.mem_append] at hk
    rcases hk with hk | hk
    · exact hA k hk
    · exact hB k hk

end Decode

/-! ## 3. The limb certificate is exact (`Pregreen38Probes.mu_limbs_exact`, `lambda_chip`) -/

section Limbs

theorem mu_limbs_exact {q : ℕ} [Fact q.Prime] (hq : 2 ^ 63 < q)
    (loL loR loC hiL hiR hiC c : ℕ)
    (hloL : loL < 2 ^ 62) (hloR : loR < 2 ^ 62) (hloC : loC < 2 ^ 62)
    (hhiL : hiL < 2 ^ 48) (hhiR : hiR < 2 ^ 48) (hhiC : hiC < 2 ^ 48) (hc : c ≤ 1)
    (h1 : (loC : ZMod q) + c * 2 ^ 62 = loL + loR + 1)
    (h2 : (hiC : ZMod q) = hiL + hiR + c) :
    hiC * 2 ^ 62 + loC = (hiL * 2 ^ 62 + loL) + (hiR * 2 ^ 62 + loR) + 1 := by
  have e1 : ((loC + c * 2 ^ 62 : ℕ) : ZMod q) = ((loL + loR + 1 : ℕ) : ZMod q) := by
    push_cast; linear_combination h1
  have e2 : ((hiC : ℕ) : ZMod q) = ((hiL + hiR + c : ℕ) : ZMod q) := by
    push_cast; linear_combination h2
  rw [ZMod.natCast_eq_natCast_iff'] at e1 e2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e2
  omega

theorem lambda_chip (lo hi : ℕ) (hlo : lo < 2 ^ 62) (hhi : hi < 2 ^ 48) :
    hi * 2 ^ 62 + lo + 1 ≤ 2 ^ 110 := by
  have h1 : hi * 2 ^ 62 ≤ (2 ^ 48 - 1) * 2 ^ 62 :=
    Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hhi)
  have h2 : lo + 1 ≤ 2 ^ 62 := hlo
  calc hi * 2 ^ 62 + lo + 1 = hi * 2 ^ 62 + (lo + 1) := by ring
    _ ≤ (2 ^ 48 - 1) * 2 ^ 62 + 2 ^ 62 := Nat.add_le_add h1 h2
    _ = 2 ^ 110 := by norm_num

variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **The rank gate is exact over `ℕ`**: `μ = μ_L + μ_R + 1` on every accepted row. -/
theorem rowOK_mu [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {c : CellRow q Kfp} (h : RowOK z c) :
    c.b0.mu = c.b0.muL + c.b0.muR + 1 :=
  mu_limbs_exact hq _ _ _ _ _ _ _ h.loL_lt h.loR_lt h.lo_lt h.hiL_lt h.hiR_lt h.hi_lt h.carry_le
    h.limbLo h.limbHi

/-- **`Λ_chip`**: the certified rank of an accepted row is `< 2^110`. -/
theorem rowOK_mu_lt {z : Kfp} {c : CellRow q Kfp} (h : RowOK z c) : c.b0.mu < fuelChip := by
  have := lambda_chip c.b0.lo c.b0.hi h.lo_lt h.hi_lt
  unfold CellRowB0.mu fuelChip; omega

end Limbs

/-! ## 4. T1: on an accepted table every fingerprint is the NPR of the B0-decoded noun -/

section T1
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

theorem mem_expand {α : Type*} {l : List (α × ℕ)} {k : α} :
    k ∈ expand l ↔ ∃ kc ∈ l, kc.2 ≠ 0 ∧ k = kc.1 := by
  simp [expand, List.mem_flatMap, List.mem_replicate]

theorem serial_lookup {t : List (CellRowB0 q)} (hs : SerialOK t) {c : CellRowB0 q} (hc : c ∈ t) :
    t[c.idx]? = some c := by
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have h1 : (t.map (·.idx))[i]? = (List.range t.length)[i]? := by rw [hs]
  rw [List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hi, hci] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  rw [h1, List.getElem?_eq_getElem hi, hci]

/-- A weighted left child's key is provided by a row of the table (from the ℕ multiset balance). -/
theorem consumed_left_of_balanced {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (hbal : ValidityBalanced t vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wL = true) :
    ∃ c' ∈ t, c.l = c'.p ∧ c.b0.hiL = c'.b0.hi ∧ c.b0.loL = c'.b0.lo ∧ c.b0.idL = c'.b0.idx := by
  have hmem : (c.l, c.b0.hiL, c.b0.loL, c.b0.idL) ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    refine ⟨((c.l, c.b0.hiL, c.b0.loL, c.b0.idL), 1), ?_, one_ne_zero, rfl⟩
    apply List.mem_append_left
    simp only [vCons, List.mem_flatMap]
    exact ⟨c, hc, by simp [hw]⟩
  have hprov := hbal.mem_iff.mpr hmem
  rw [mem_expand] at hprov
  obtain ⟨kc, hkc, -, hk⟩ := hprov
  simp only [vProv, List.mem_map] at hkc
  obtain ⟨c', hc', rfl⟩ := hkc
  simp only [Prod.mk.injEq] at hk
  exact ⟨c', hc', hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩

theorem consumed_right_of_balanced {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (hbal : ValidityBalanced t vl) {c : CellRow q Kfp} (hc : c ∈ t) (hw : c.b0.wR = true) :
    ∃ c' ∈ t, c.r = c'.p ∧ c.b0.hiR = c'.b0.hi ∧ c.b0.loR = c'.b0.lo ∧ c.b0.idR = c'.b0.idx := by
  have hmem : (c.r, c.b0.hiR, c.b0.loR, c.b0.idR) ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    refine ⟨((c.r, c.b0.hiR, c.b0.loR, c.b0.idR), 1), ?_, one_ne_zero, rfl⟩
    apply List.mem_append_left
    simp only [vCons, List.mem_flatMap]
    exact ⟨c, hc, by simp [hw]⟩
  have hprov := hbal.mem_iff.mpr hmem
  rw [mem_expand] at hprov
  obtain ⟨kc, hkc, -, hk⟩ := hprov
  simp only [vProv, List.mem_map] at hkc
  obtain ⟨c', hc', rfl⟩ := hkc
  simp only [Prod.mk.injEq] at hk
  exact ⟨c', hc', hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩

/-- The ℕ multiset balance implies the existence form. -/
theorem ValidityBalanced.served {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (hbal : ValidityBalanced t vl) : ValidityServed t :=
  fun _ hc => ⟨consumed_left_of_balanced hbal hc, consumed_right_of_balanced hbal hc⟩

/-- A weighted left child's key is provided by a row of the table (existence form). -/
theorem consumed_left {t : List (CellRow q Kfp)} (hs : ValidityServed t) {c : CellRow q Kfp}
    (hc : c ∈ t) (hw : c.b0.wL = true) :
    ∃ c' ∈ t, c.l = c'.p ∧ c.b0.hiL = c'.b0.hi ∧ c.b0.loL = c'.b0.lo ∧ c.b0.idL = c'.b0.idx :=
  (hs c hc).1 hw

theorem consumed_right {t : List (CellRow q Kfp)} (hs : ValidityServed t) {c : CellRow q Kfp}
    (hc : c ∈ t) (hw : c.b0.wR = true) :
    ∃ c' ∈ t, c.r = c'.p ∧ c.b0.hiR = c'.b0.hi ∧ c.b0.loR = c'.b0.lo ∧ c.b0.idR = c'.b0.idx :=
  (hs c hc).2 hw

theorem atom_enc [NeZero q] (z : Kfp) (a : ZMod q) :
    FP.atomFP z (algebraMap (ZMod q) Kfp a) = GlobalCarryRecognizer.enc z (.atom a.val) := by
  rw [GlobalCarryRecognizer.enc_atom]
  congr 1
  rw [← map_natCast (algebraMap (ZMod q) Kfp), ZMod.natCast_zmod_val]

/-- The child noun a row's round-0 columns name on the left (`decodeB0`'s left branch). -/
def childL (t : List (CellRowB0 q)) (f : ℕ) (c : CellRowB0 q) : Option Noun :=
  if c.wL then decodeB0 t f c.idL else some (.atom c.aL.val)

def childR (t : List (CellRowB0 q)) (f : ℕ) (c : CellRowB0 q) : Option Noun :=
  if c.wR then decodeB0 t f c.idR else some (.atom c.aR.val)

theorem decodeB0_succ (t : List (CellRowB0 q)) (f i : ℕ) :
    decodeB0 t (f + 1) i =
      (t[i]?).bind fun c => (childL t f c).bind fun a => (childR t f c).bind fun b =>
        some (.cell a b) := rfl

/-- **T1, the induction (`decode_sound` at the real NPR).**  On an accepted table, every row of
rank `n` decodes (at any fuel `> n`) from its round-0 columns to a cell `[L R]` with `c.l = enc L`,
`c.r = enc R`, `c.p = enc [L R]` and `|[L R]| = n + 1` leaves.  Strong induction on the certified
rank (`rowOK_mu`). -/
theorem decode_sound [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    ∀ n, ∀ c ∈ t, c.b0.mu = n → ∀ fuel, n < fuel →
      ∃ L R, decodeB0 (t.map (·.b0)) fuel c.b0.idx = some (.cell L R) ∧
        childL (t.map (·.b0)) (fuel - 1) c.b0 = some L ∧
        childR (t.map (·.b0)) (fuel - 1) c.b0 = some R ∧
        c.l = GlobalCarryRecognizer.enc z L ∧ c.r = GlobalCarryRecognizer.enc z R ∧
        c.p = GlobalCarryRecognizer.enc z (.cell L R) ∧ (Noun.cell L R).leaves = n + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc hn fuel hf
  obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hok := h.rows c hc
  have hrank := rowOK_mu hq hok
  have hleft : ∃ a, childL (t.map (·.b0)) fuel c.b0 = some a ∧
      c.l = GlobalCarryRecognizer.enc z a ∧ a.leaves = c.b0.muL + 1 := by
    cases hw : c.b0.wL with
    | false =>
      obtain ⟨hla, hlo, hhi⟩ := hok.atomL hw
      refine ⟨.atom c.b0.aL.val, by simp [childL, hw], by rw [hla, atom_enc], ?_⟩
      simp [Noun.leaves, CellRowB0.muL, hlo, hhi]
    | true =>
      obtain ⟨c', hc', hl, hhiL, hloL, hidL⟩ := consumed_left h.served hc hw
      have hmu : c'.b0.mu = c.b0.muL := by simp [CellRowB0.mu, CellRowB0.muL, hhiL, hloL]
      have hval : c'.b0.mu < n := by rw [hmu, ← hn, hrank]; omega
      obtain ⟨L, R, hd, -, -, -, -, hp, hlv⟩ := ih _ hval c' hc' rfl fuel (by omega)
      refine ⟨.cell L R, by simp [childL, hw, hidL, hd], by rw [hl, hp], by rw [hlv, hmu]⟩
  have hright : ∃ b, childR (t.map (·.b0)) fuel c.b0 = some b ∧
      c.r = GlobalCarryRecognizer.enc z b ∧ b.leaves = c.b0.muR + 1 := by
    cases hw : c.b0.wR with
    | false =>
      obtain ⟨hra, hlo, hhi⟩ := hok.atomR hw
      refine ⟨.atom c.b0.aR.val, by simp [childR, hw], by rw [hra, atom_enc], ?_⟩
      simp [Noun.leaves, CellRowB0.muR, hlo, hhi]
    | true =>
      obtain ⟨c', hc', hr, hhiR, hloR, hidR⟩ := consumed_right h.served hc hw
      have hmu : c'.b0.mu = c.b0.muR := by simp [CellRowB0.mu, CellRowB0.muR, hhiR, hloR]
      have hval : c'.b0.mu < n := by rw [hmu, ← hn, hrank]; omega
      obtain ⟨L, R, hd, -, -, -, -, hp, hlv⟩ := ih _ hval c' hc' rfl fuel (by omega)
      refine ⟨.cell L R, by simp [childR, hw, hidR, hd], by rw [hr, hp], by rw [hlv, hmu]⟩
  obtain ⟨a, hda, hpa, hla⟩ := hleft
  obtain ⟨b, hdb, hpb, hlb⟩ := hright
  have hmem : c.b0 ∈ t.map (·.b0) := List.mem_map_of_mem hc
  refine ⟨a, b, ?_, by simpa using hda, by simpa using hdb, hpa, hpb, ?_, ?_⟩
  · rw [decodeB0_succ, serial_lookup h.serial hmem, Option.bind_some, hda, Option.bind_some, hdb,
      Option.bind_some]
  · rw [hok.cons, hpa, hpb, GlobalCarryRecognizer.enc_cons hz]
  · simp only [Noun.leaves] at hla hlb ⊢; rw [hla, hlb, ← hn, hrank]; ring

/-- **T1 (`preZNounOfTable`)**: on an accepted table, every row's serial decodes, from round-0
columns alone, to a noun whose fingerprint at the seed is the row's `p`, with `μ + 1 ≤ 2^110`
leaves and atoms below `q`. -/
theorem preZNounOfTable_sound [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    ∀ c ∈ t, ∃ n, preZNounOfTable (t.map (·.b0)) c.b0.idx = some n ∧
      c.p = GlobalCarryRecognizer.enc z n ∧ n.leaves = c.b0.mu + 1 ∧ n.leaves ≤ fuelChip ∧
      ∀ k ∈ n.leafList, k < q := by
  intro c hc
  have hlt := rowOK_mu_lt (h.rows c hc)
  obtain ⟨L, R, hd, -, -, -, -, hp, hlv⟩ := decode_sound hq hz h _ c hc rfl fuelChip hlt
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine ⟨.cell L R, hd, hp, hlv, by omega, decodeB0_leafList_lt _ _ _ _ hd⟩

/-- **T1, the children (`row_genuine`)**: an accepted row's decoded noun is `[L R]`, its `l`/`r`
columns are `enc L`/`enc R`, a weighted child is the decoded noun of its child serial (a row of
the table), and a zero-weight child is the atom named by the round-0 value. -/
theorem row_genuine [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, preZNounOfTable (t.map (·.b0)) c.b0.idx = some (.cell L R) ∧
      c.p = GlobalCarryRecognizer.enc z (.cell L R) ∧
      c.l = GlobalCarryRecognizer.enc z L ∧ c.r = GlobalCarryRecognizer.enc z R ∧
      (c.b0.wL = true → preZNounOfTable (t.map (·.b0)) c.b0.idL = some L) ∧
      (c.b0.wL = false → L = .atom c.b0.aL.val) ∧
      (c.b0.wR = true → preZNounOfTable (t.map (·.b0)) c.b0.idR = some R) ∧
      (c.b0.wR = false → R = .atom c.b0.aR.val) := by
  have hlt := rowOK_mu_lt (h.rows c hc)
  obtain ⟨L, R, hd, hL, hR, hl, hr, hp, -⟩ := decode_sound hq hz h _ c hc rfl fuelChip hlt
  refine ⟨L, R, hd, hp, hl, hr, ?_, ?_, ?_, ?_⟩
  · intro hw
    simp only [childL, hw, if_true] at hL
    exact decodeB0_mono _ _ _ _ _ (Nat.sub_le _ _) hL
  · intro hw
    simp only [childL, hw] at hL
    exact (Option.some.inj hL).symm
  · intro hw
    simp only [childR, hw, if_true] at hR
    exact decodeB0_mono _ _ _ _ _ (Nat.sub_le _ _) hR
  · intro hw
    simp only [childR, hw] at hR
    exact (Option.some.inj hR).symm

/-! ### The receipts: B0 only, and no relinking -/

/-- The round-0 projection of a row (fingerprints zeroed). -/
def strip (c : CellRow q Kfp) : CellRow q Kfp := ⟨c.b0, 0, 0, 0⟩

/-- **`decodeB0` reads round-0 columns only**: stripping every fingerprint leaves every decode
unchanged (by type: `decodeB0` takes `List CellRowB0`). -/
theorem decodeB0_strip (t : List (CellRow q Kfp)) (fuel i : ℕ) :
    decodeB0 ((t.map strip).map (·.b0)) fuel i = decodeB0 (t.map (·.b0)) fuel i := by
  simp [strip, List.map_map, Function.comp_def]

/-- **No relinking (`served_of_b0`)**: two accepted tables with the same round-0 columns, at any
two nonzero seeds, serve at every serial the fingerprint of ONE noun (the B0 decode). -/
theorem served_of_b0 [Fact q.Prime] (hq : 2 ^ 63 < q) {z z' : Kfp} (hz : z ≠ 0) (hz' : z' ≠ 0)
    {t t' : List (CellRow q Kfp)} {vl vl' : List (VKey Kfp)}
    (h : TableAccepts z t vl) (h' : TableAccepts z' t' vl')
    (hb0 : t.map (·.b0) = t'.map (·.b0)) :
    ∀ c ∈ t, ∀ c' ∈ t', c.b0.idx = c'.b0.idx →
      ∃ n, c.p = GlobalCarryRecognizer.enc z n ∧ c'.p = GlobalCarryRecognizer.enc z' n := by
  intro c hc c' hc' hidx
  obtain ⟨n, hd, hp, -⟩ := preZNounOfTable_sound hq hz h c hc
  obtain ⟨n', hd', hp', -⟩ := preZNounOfTable_sound hq hz' h' c' hc'
  rw [← hb0, ← hidx, hd, Option.some.injEq] at hd'
  exact ⟨n, hp, hd' ▸ hp'⟩

/-- At ONE seed: the same B0 serves the same fingerprint at every serial. -/
theorem served_of_b0_same_seed [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t t' : List (CellRow q Kfp)} {vl vl' : List (VKey Kfp)}
    (h : TableAccepts z t vl) (h' : TableAccepts z t' vl')
    (hb0 : t.map (·.b0) = t'.map (·.b0)) :
    ∀ c ∈ t, ∀ c' ∈ t', c.b0.idx = c'.b0.idx → c.p = c'.p := by
  intro c hc c' hc' hidx
  obtain ⟨n, hp, hp'⟩ := served_of_b0 hq hz hz h h' hb0 c hc c' hc' hidx
  rw [hp, hp']

end T1

/-! ## 5. T7: the decode recursion is well-founded on the certified rank (`mu_rank_wf`) -/

section T7
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

theorem mu_rank_wf {V : Type*} (mu : V → ℕ) (E : V → V → Prop)
    (hE : ∀ u v, E u v → mu v < mu u) : WellFounded (fun v u => E u v) :=
  Subrelation.wf (fun {v u} h => hE u v h) (measure mu).wf

/-- The edge relation the decode follows: `c'` provides the key of a weighted child of `c`. -/
def ChildOf (t : List (CellRow q Kfp)) (c c' : CellRow q Kfp) : Prop :=
  c ∈ t ∧ c' ∈ t ∧
    ((c.b0.wL = true ∧ c.l = c'.p ∧ c.b0.hiL = c'.b0.hi ∧ c.b0.loL = c'.b0.lo ∧
        c.b0.idL = c'.b0.idx) ∨
     (c.b0.wR = true ∧ c.r = c'.p ∧ c.b0.hiR = c'.b0.hi ∧ c.b0.loR = c'.b0.lo ∧
        c.b0.idR = c'.b0.idx))

/-- On an accepted table a child's certified rank is strictly smaller. -/
theorem child_mu_lt [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {c c' : CellRow q Kfp}
    (hcc : ChildOf t c c') : c'.b0.mu < c.b0.mu := by
  obtain ⟨hc, -, hk⟩ := hcc
  have hr := rowOK_mu hq (h.rows c hc)
  rcases hk with ⟨-, -, hhi, hlo, -⟩ | ⟨-, -, hhi, hlo, -⟩
  · have : c'.b0.mu = c.b0.muL := by simp [CellRowB0.mu, CellRowB0.muL, hhi, hlo]
    omega
  · have : c'.b0.mu = c.b0.muR := by simp [CellRowB0.mu, CellRowB0.muR, hhi, hlo]
    omega

/-- **T7**: the child relation of an accepted table is well-founded (no cycle, no phantom, no
back-reference survives the `+1`); this is the recursion `decode_sound` inducts along. -/
theorem childRel_wf [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    WellFounded (fun c' c => ChildOf t c c') :=
  mu_rank_wf (fun c : CellRow q Kfp => c.b0.mu) (ChildOf t) (fun _ _ hcc => child_mu_lt hq h hcc)

end T7

end Nock.NockVMROM.Thm54.VclL
