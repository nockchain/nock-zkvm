/-
  Nock/RedTeam/Batch557Thm54RangeGadget.lean

  * **A. Bit lists and lexicographic order.**  `val` (MSB first), `ltL`, `ltL_iff`
    (`ltL as bs ↔ val as < val bs` at equal length), `val_inj`.
  * **B. The gadget on committed columns.**
  * **C. The certificate bridge.**  `cert_eq_val`, `pbits` / `val_pbits`, `size_spec`;
    `gadget_sound` (accepted ⇒ `cert < p`, NO hypothesis on `p` beyond `0 < p`),
    `gadget_complete` (`cert < p` ⇒ accepted), `exists_cert` (every `1 ≤ a < p` is certified
    with `m ≤ n − 1`), `cert_mod_unique_of_lt` / `accepted_row_axis` (the alias is closed:
    `cert = axis.val`).
  * **D. BROKEN AS BRIEFED.**
  * **E. The repair, compiled.**  `top` bit-matched against `n − 1` (`topK`) and ONE added gate
    `ltm + top = 1` on the shift bits (`rangeK`): `range_gate_iff` (`= 1 ↔ m ≤ n − 1`),
    `top_eq_one_iff`, `range_gate_vacuous_pow2` (at `n = 2^b` — Goldilocks — the gate is the
    boolean identity and may be dropped).  With it, `gadget_sound` closes every alias.
  * **F. `hax` is derivable.**  `evalGAxRom` (the ROM evaluator with the OP0 tail atom and the
    OP9 axis atom guarded `< q`), `evalGRom_boundedBy_axes` (a guarded ROM run on `BoundedBy q`
    subject and formula is an axis-guarded run with a `BoundedBy q` result),
    `runAxesBoundedBy_of_hyps` (`hbound`, `hs`, `hf`, `hp` ⇒ `RunAxesBoundedBy p`).
  * **G. Degrees and widths.**  Every gate of the repaired design has `CoeffExpr.degree ≤ 4`
    (`termExpr_degree_le`, `ltGate_degree_le`, `helperPin_degree`, `topPin_degrees`);
    `rangeColumns e n` with `100` at `n = 64`, `26` at `n = 10`, `36` at `n = 17`;
    `compute_width_64 : 202 + 100 = 302`.
  * **H. The memory side moves by one exponent.**  The bracket theorems are parametric in the
    scale (`Batch554.bracket_zero_iff` at `N = n − 1`), but the deployed constant `λ^{62}`
    becomes `λ^{n−1} = λ^{63}` and the event majorant `M + 3N + 128 → M + 3N + 130`
    (`pwAccountingWork'`, `figures_unmoved_31'`, `figures_unmoved_32'`).
-/
import Nock.RedTeam.Batch555Thm54PwCertificate
import Nock.RedTeam.Batch556Thm54PwEvent
import Nock.NockVMROM.Thm54.FormRCore.Majorant
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch557

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.RedTeam.Batch554 (bitsOf bit)
open Nock.RedTeam.Batch555 (cert cert_bounds cert_inj c34 cert_c34)

/-! ## A. Bit lists (most significant bit first), values, lexicographic order -/

/-- The integer a MSB-first bit list denotes. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat * 2 ^ bs.length + val bs

theorem val_lt (bs : List Bool) : val bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [val]
  | cons b bs ih =>
      simp only [val, List.length_cons, pow_succ]
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Lexicographic strict order on equal-length MSB-first lists: the first differing position
has a `0` on the left and a `1` on the right. -/
def ltL : List Bool → List Bool → Bool
  | a :: as, b :: bs => (!a && b) || (a == b && ltL as bs)
  | _, _ => false

theorem ltL_iff (as : List Bool) : ∀ bs : List Bool, as.length = bs.length →
    (ltL as bs = true ↔ val as < val bs) := by
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => simp [ltL, val]
      | cons => simp at h
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          have h1 := val_lt as
          have h2 := val_lt bs
          rw [h] at h1
          simp only [ltL, val, h]
          cases a <;> cases b <;> simp [ih bs h] <;> omega

theorem val_inj (as : List Bool) : ∀ bs : List Bool, as.length = bs.length →
    val as = val bs → as = bs := by
  induction as with
  | nil =>
      intro bs h _
      cases bs with
      | nil => rfl
      | cons => simp at h
  | cons a as ih =>
      intro bs h hv
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          have h1 := val_lt as
          have h2 := val_lt bs
          rw [h] at h1
          simp only [val, h] at hv
          have hab : a = b := by
            cases a <;> cases b <;> simp at hv ⊢ <;> omega
          subst hab
          have : val as = val bs := by omega
          rw [ih bs h this]

/-! ## B. The comparison gadget on committed columns -/

section Gadget

variable {K : Type*} [Field K]

/-- `lin_i`: the column `c` when the constant bit `p_i = 1`, `1 − c` when `p_i = 0`. -/
def lin (a : K) (p : Bool) : K := if p then a else 1 - a

/-- The prefix-equality flag `eq`: the product of the `lin`s (MSB first). -/
def eqK : List K → List Bool → K
  | a :: as, p :: ps => lin a p * eqK as ps
  | _, _ => 1

/-- The gadget's `lt`, recursive form: at the top position either `p_i = 1 ∧ c_i = 0` fires, or
the bits agree and the comparison continues below. -/
def ltK : List K → List Bool → K
  | a :: as, p :: ps => (if p then 1 - a else 0) + lin a p * ltK as ps
  | _, _ => 0

def term (as : List K) (ps : List Bool) (k : ℕ) : K :=
  eqK (as.take k) (ps.take k) * (1 - as.getD k 0) * (if ps.getD k false then 1 else 0)

/-- **The brief's sum form is the recursive form** (distributivity; the `eq` helper columns are
names for the partial products). -/
theorem ltK_expand (as : List K) : ∀ ps : List Bool, as.length = ps.length →
    ltK as ps = ∑ k ∈ Finset.range as.length, term as ps k := by
  induction as with
  | nil => intro ps _; simp [ltK]
  | cons a as ih =>
      intro ps h
      cases ps with
      | nil => simp at h
      | cons p ps =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          rw [List.length_cons, Finset.sum_range_succ']
          have h0 : term (a :: as) (p :: ps) 0 = if p then 1 - a else 0 := by
            simp [term, eqK]
          have hs : ∀ k, term (a :: as) (p :: ps) (k + 1) = lin a p * term as ps k := by
            intro k
            simp only [term, List.take_succ_cons, eqK, List.getD_cons_succ]
            ring
          rw [h0, Finset.sum_congr rfl (fun k _ => hs k), ← Finset.mul_sum, ← ih ps h]
          simp only [ltK]
          ring

theorem lin_bit (a p : Bool) : lin (bit (K := K) a) p = if a = p then 1 else 0 := by
  cases a <;> cases p <;> simp [lin, bit]

/-- On boolean columns the prefix flag is `[prefix equal]`. -/
theorem eqK_bool (as : List Bool) : ∀ ps : List Bool, as.length = ps.length →
    eqK (as.map (bit (K := K))) ps = if as = ps then 1 else 0 := by
  induction as with
  | nil =>
      intro ps h
      cases ps with
      | nil => simp [eqK]
      | cons => simp at h
  | cons a as ih =>
      intro ps h
      cases ps with
      | nil => simp at h
      | cons p ps =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.map_cons, eqK, lin_bit, ih ps h, List.cons.injEq]
          by_cases hap : a = p <;> by_cases hasps : as = ps <;> simp [hap, hasps]

/-- **On boolean columns `lt ∈ {0, 1}` and `lt = 1 ↔ lexicographic `<`.** -/
theorem ltK_bool (as : List Bool) : ∀ ps : List Bool, as.length = ps.length →
    ltK (as.map (bit (K := K))) ps = if ltL as ps then 1 else 0 := by
  induction as with
  | nil =>
      intro ps h
      cases ps with
      | nil => simp [ltK, ltL]
      | cons => simp at h
  | cons a as ih =>
      intro ps h
      cases ps with
      | nil => simp at h
      | cons p ps =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [List.map_cons, ltK, ltL, lin_bit, ih ps h]
          cases a <;> cases p <;> simp [bit]

/-- A summand of the sum form is nonzero exactly when the prefix above `k` agrees, `c_k = 0`
and `p_k = 1`. -/
theorem term_ne_zero_iff (as ps : List Bool) (h : as.length = ps.length) (k : ℕ) :
    term (as.map (bit (K := K))) ps k ≠ 0
      ↔ as.take k = ps.take k ∧ as.getD k false = false ∧ ps.getD k false = true := by
  have hlen : (as.take k).length = (ps.take k).length := by simp [List.length_take, h]
  have hget : (as.map (bit (K := K))).getD k 0 = bit (as.getD k false) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases as[k]? <;> simp [bit]
  simp only [term, ← List.map_take, eqK_bool _ _ hlen, hget]
  cases hpk : ps.getD k false <;> cases hak : as.getD k false
    <;> by_cases hpre : as.take k = ps.take k <;> simp [hpre, bit]

/-- **At most one summand fires**: two firing positions `k < k'` are contradictory, because
`k'` firing needs `c_k = p_k` while `k` firing needs `c_k = 0 ≠ 1 = p_k`. -/
theorem at_most_one_term (as ps : List Bool) (h : as.length = ps.length) (k k' : ℕ)
    (hkk' : k < k') (hk : term (as.map (bit (K := K))) ps k ≠ 0) :
    term (as.map (bit (K := K))) ps k' = 0 := by
  by_contra hk'
  have hk'' : term (as.map (bit (K := K))) ps k' ≠ 0 := hk'
  rw [term_ne_zero_iff as ps h] at hk hk''
  obtain ⟨hpre, hak, hpk⟩ := hk
  obtain ⟨hpre', _, _⟩ := hk''
  have : as.getD k false = ps.getD k false := by
    have := congrArg (fun l : List Bool => l.getD k false) hpre'
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hkk'] using this
  rw [hak, hpk] at this
  exact Bool.false_ne_true this

end Gadget

/-! ## C. The certificate bridge: `cert`, the bits of `p`, `bitLength = Nat.size` -/

theorem bitsOf_succ (m : ℕ) (c : ℕ → Bool) :
    bitsOf (m + 1) c = c 1 :: bitsOf m (fun j => c (j + 1)) := by
  simp only [bitsOf, List.ofFn_succ, Fin.val_zero, zero_add, Fin.val_succ]

theorem val_bitsOf (m : ℕ) : ∀ c : ℕ → Bool,
    val (bitsOf m c) = ∑ j ∈ Finset.range m, (c (j + 1)).toNat * 2 ^ (m - (j + 1)) := by
  induction m with
  | zero => intro c; simp [bitsOf, val]
  | succ m ih =>
      intro c
      rw [bitsOf_succ, Finset.sum_range_succ']
      simp only [val, Batch554.bitsOf_length, ih (fun j => c (j + 1)), Nat.add_sub_cancel]
      have : ∀ j ∈ Finset.range m,
          (c (j + 1 + 1)).toNat * 2 ^ (m - (j + 1)) = (c (j + 1 + 1)).toNat * 2 ^ (m + 1 - (j + 1 + 1)) := by
        intro j _
        rw [show m + 1 - (j + 1 + 1) = m - (j + 1) by omega]
      rw [Finset.sum_congr rfl this, zero_add, add_comm]

/-- **The certificate is the value of the MSB-first list `1 :: c_1 :: … :: c_m`.** -/
theorem cert_eq_val (m : ℕ) (c : ℕ → Bool) : cert m c = val (true :: bitsOf m c) := by
  simp [cert, val, Batch554.bitsOf_length, val_bitsOf]

/-- The constant bits of `p` on `n` positions, MSB first: `p_{n−1}, …, p_0`. -/
def pbits (n p : ℕ) : List Bool := List.ofFn fun i : Fin n => p.testBit (n - 1 - i)

theorem pbits_length (n p : ℕ) : (pbits n p).length = n := by simp [pbits]

theorem pbits_succ (n p : ℕ) : pbits (n + 1) p = p.testBit n :: pbits n p := by
  simp only [pbits, List.ofFn_succ, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ]
  congr 1
  exact congrArg List.ofFn (funext fun i => by congr 1; omega)

theorem val_pbits (n p : ℕ) : val (pbits n p) = p % 2 ^ n := by
  induction n with
  | zero => simp [pbits, val, Nat.mod_one]
  | succ n ih =>
      rw [pbits_succ, val, pbits_length, ih, Nat.toNat_testBit, Nat.mod_pow_succ]
      ring

/-- `n := Nat.size p` is the bit length: `2^{n−1} ≤ p < 2^n`. -/
theorem size_spec (p : ℕ) (hp : 0 < p) : 2 ^ (Nat.size p - 1) ≤ p ∧ p < 2 ^ Nat.size p :=
  ⟨Nat.lt_size.mp (Nat.sub_lt (Nat.size_pos.mpr hp) Nat.one_pos), Nat.lt_size_self p⟩

section Certificate

variable {K : Type*} [Field K]

/-- The range gate's comparison value: the certificate's absolute bits (`c_0 = 1` on top) against
the bits of `p` on `n` positions.  Meaningful at `m + 1 = n`. -/
def ltCert (n p m : ℕ) (c : ℕ → Bool) : K :=
  ltK ((true :: bitsOf m c).map (bit (K := K))) (pbits n p)

theorem ltCert_eq (n p m : ℕ) (c : ℕ → Bool) (hm : m + 1 = n) :
    ltCert (K := K) n p m c = if cert m c < p % 2 ^ n then 1 else 0 := by
  have hlen : (true :: bitsOf m c).length = (pbits n p).length := by
    simp [Batch554.bitsOf_length, pbits_length, hm]
  rw [ltCert, ltK_bool _ _ hlen, cert_eq_val, ← val_pbits]
  by_cases h : val (true :: bitsOf m c) < val (pbits n p)
  · rw [if_pos h, if_pos ((ltL_iff _ _ hlen).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((ltL_iff _ _ hlen).mp h'))]

/-- **Soundness of the repaired gadget** — with `m ≤ n − 1` (the range gate, section E) and the
comparison gate at `m = n − 1`, the certificate is `< p`.  No hypothesis on `p` beyond `0 < p`. -/
theorem gadget_sound (p : ℕ) (hp : 0 < p) (m : ℕ) (c : ℕ → Bool) (hm : m ≤ Nat.size p - 1)
    (hgate : m = Nat.size p - 1 → ltCert (K := K) (Nat.size p) p m c = 1) :
    cert m c < p := by
  obtain ⟨hlo, hhi⟩ := size_spec p hp
  have hn : 1 ≤ Nat.size p := Nat.size_pos.mpr hp
  rcases Nat.lt_or_eq_of_le hm with hlt | heq
  · have h1 := (cert_bounds m c).2
    have h2 : 2 ^ (m + 1) ≤ 2 ^ (Nat.size p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h := hgate heq
    rw [ltCert_eq _ _ _ _ (by omega), Nat.mod_eq_of_lt hhi] at h
    split_ifs at h with hc
    · exact hc
    · exact absurd h zero_ne_one

/-- **Completeness**: a certificate `< p` has `m ≤ n − 1` and passes the comparison gate. -/
theorem gadget_complete (p : ℕ) (hp : 0 < p) (m : ℕ) (c : ℕ → Bool) (h : cert m c < p) :
    m ≤ Nat.size p - 1 ∧ (m = Nat.size p - 1 → ltCert (K := K) (Nat.size p) p m c = 1) := by
  obtain ⟨_, hhi⟩ := size_spec p hp
  have hn : 1 ≤ Nat.size p := Nat.size_pos.mpr hp
  have hm : m < Nat.size p := by
    have := (cert_bounds m c).1
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
  refine ⟨by omega, fun heq => ?_⟩
  rw [ltCert_eq _ _ _ _ (by omega), Nat.mod_eq_of_lt hhi, if_pos h]

theorem toNat_eq_one {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> simp at h ⊢

/-- **Every axis `1 ≤ a < p` is certified with `m ≤ n − 1`** (`m = size a − 1`, the bits of
`a`): the completeness side condition `hax` costs no hypothesis once `n = Nat.size p`. -/
theorem exists_cert (p a : ℕ) (ha : 0 < a) (hap : a < p) :
    ∃ m c, m ≤ Nat.size p - 1 ∧ cert m c = a := by
  obtain ⟨hlo, hhi⟩ := size_spec a ha
  have hn : 1 ≤ Nat.size a := Nat.size_pos.mpr ha
  refine ⟨Nat.size a - 1, fun j => a.testBit (Nat.size a - 1 - j), ?_, ?_⟩
  · have := Nat.size_le_size (le_of_lt hap)
    omega
  · set m := Nat.size a - 1 with hm
    have htop : a.testBit m = true := by
      apply toNat_eq_one
      rw [Nat.toNat_testBit]
      have h2 : (1 + 1) * 2 ^ m = 2 ^ Nat.size a := by
        rw [show 1 + 1 = 2 by rfl, ← pow_succ', show m + 1 = Nat.size a by omega]
      have hdiv : a / 2 ^ m = 1 :=
        Nat.div_eq_of_lt_le (by rw [one_mul]; exact hlo) (by rw [h2]; exact hhi)
      rw [hdiv]
    have hlist : true :: bitsOf m (fun j => a.testBit (m - j)) = pbits (m + 1) a := by
      rw [pbits_succ, htop]
      congr 1
      simp only [bitsOf, pbits]
      exact congrArg List.ofFn (funext fun i => by congr 1; omega)
    rw [cert_eq_val, hlist, val_pbits, show m + 1 = Nat.size a by omega, Nat.mod_eq_of_lt hhi]

/-- **The alias is closed**: two certificates below `p` with the same residue are the same
certificate — `Batch555.cert_mod_unique`'s `2^63 < p` premise replaced by the gate's `cert < p`. -/
theorem cert_mod_unique_of_lt (p : ℕ) [NeZero p] (m m' : ℕ) (c c' : ℕ → Bool)
    (h1 : cert m c < p) (h2 : cert m' c' < p)
    (h : ((cert m c : ℕ) : ZMod p) = ((cert m' c' : ℕ) : ZMod p)) :
    m = m' ∧ ∀ j, 1 ≤ j → j ≤ m → c j = c' j := by
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  exact cert_inj m m' c c' this

/-- **Accepted row ⇒ `cert = axis` as integers**: the committed axis atom `a : ZMod p` equal (in
the field) to the certificate, with the range gadget accepting, has `a.val = cert m c`. -/
theorem accepted_row_axis (p : ℕ) [NeZero p] (a : ZMod p) (m : ℕ) (c : ℕ → Bool)
    (hm : m ≤ Nat.size p - 1)
    (hgate : m = Nat.size p - 1 → ltCert (K := K) (Nat.size p) p m c = 1)
    (haxis : a = ((cert m c : ℕ) : ZMod p)) : a.val = cert m c := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [haxis, ZMod.val_natCast, Nat.mod_eq_of_lt (gadget_sound (K := K) p hp m c hm hgate)]

end Certificate

/-! ## D. BROKEN AS BRIEFED: `top := Π_k m_k` is `[m = 2^b − 1]`, not `[m = n − 1]` -/

section Brief

variable {K : Type*} [Field K]

/-- The brief's `top`: the product of the `b` shift bits of `m` — `eqK` against all-ones, i.e.
`[m = 2^b − 1]`. -/
def topBrief (b m : ℕ) : K := eqK ((pbits b m).map (bit (K := K))) (List.replicate b true)

theorem size_31 : Nat.size 31 = 5 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

theorem size_769 : Nat.size 769 = 10 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

theorem size_65537 : Nat.size 65537 = 17 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))

theorem size_goldilocks : Nat.size Nock.Field.p = 64 :=
  le_antisymm (Nat.size_le.mpr (by norm_num [Nock.Field.p]))
    (Nat.lt_size.mpr (by norm_num [Nock.Field.p]))

theorem clog_5 : Nat.clog 2 5 = 3 :=
  le_antisymm (Nat.clog_le_of_le_pow (by norm_num))
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num))

theorem clog_10 : Nat.clog 2 10 = 4 :=
  le_antisymm (Nat.clog_le_of_le_pow (by norm_num))
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num))

theorem clog_17 : Nat.clog 2 17 = 5 :=
  le_antisymm (Nat.clog_le_of_le_pow (by norm_num))
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num))

theorem clog_64 : Nat.clog 2 64 = 6 := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.clog_pow _ _ (by norm_num)]

theorem pbits_3_5 : pbits 3 5 = [true, false, true] := by decide
theorem pbits_4_10 : pbits 4 10 = [true, false, true, false] := by decide

/-- **The brief's own regression test FAILS as briefed.**  `p = 31`: `n = Nat.size 31 = 5`,
`b = ⌈log₂ 5⌉ = 3` shift bits, so `m = 5 = 101₂` is a committable shift with `top = 0`; the gate
`top · (lt − 1) = 0` holds for every `lt`; `cert 5 c34 = 34 ≡ 3 (mod 31)`. -/
theorem brief_gadget_accepts_34_at_31 :
    Nat.size 31 = 5 ∧ Nat.clog 2 5 = 3 ∧ 5 < 2 ^ 3 ∧ Nat.size 31 - 1 < 5
    ∧ topBrief (K := K) 3 5 = 0
    ∧ topBrief (K := K) 3 5 * (ltCert (K := K) 5 31 5 c34 - 1) = 0
    ∧ cert 5 c34 = 34 ∧ ((34 : ℕ) : ZMod 31) = 3 := by
  have htop : topBrief (K := K) 3 5 = 0 := by
    simp [topBrief, pbits_3_5, eqK, lin, bit]
  refine ⟨size_31, clog_5, by norm_num, by rw [size_31]; norm_num, htop, by rw [htop, zero_mul],
    cert_c34, by decide⟩

/-- **The Tier A fixture (`p = 769`) is broken the same way**: `n = 10`, `b = 4`, `m = 10 = 1010₂`
has `top = 0`; `cert 10 0 = 2^10 = 1024 ≡ 255 (mod 769)`, a legitimate residue of a different
axis. -/
theorem brief_gadget_accepts_1024_at_769 :
    Nat.size 769 = 10 ∧ Nat.clog 2 10 = 4 ∧ 10 < 2 ^ 4 ∧ Nat.size 769 - 1 < 10
    ∧ topBrief (K := K) 4 10 = 0
    ∧ cert 10 (fun _ => false) = 1024 ∧ ((1024 : ℕ) : ZMod 769) = 255 ∧ 255 < 769 := by
  have htop : topBrief (K := K) 4 10 = 0 := by
    simp [topBrief, pbits_4_10, eqK, lin, bit]
  refine ⟨size_769, clog_10, by norm_num, by rw [size_769]; norm_num, htop, ?_, by decide, by norm_num⟩
  simp [cert]

theorem brief_top_correct_at_goldilocks : 2 ^ Nat.clog 2 64 - 1 = 64 - 1 := by
  rw [clog_64]; norm_num

end Brief

/-! ## E. The repair: `top` bit-matched against `n − 1`, plus the range gate `ltm + top = 1` -/

section Repair

variable {K : Type*} [Field K]

/-- `top := [m = n − 1]`: the full-equality flag of the `b` shift bits against the constant bits
of `n − 1` (`m_k` where `(n−1)_k = 1`, `1 − m_k` where it is `0`). -/
def topK (b n m : ℕ) : K := eqK ((pbits b m).map (bit (K := K))) (pbits b (n - 1))

/-- The range gate's left-hand side on the shift bits: `ltm + top`. -/
def rangeK (b n m : ℕ) : K :=
  ltK ((pbits b m).map (bit (K := K))) (pbits b (n - 1)) + topK b n m

theorem pbits_inj (b x y : ℕ) (hx : x < 2 ^ b) (hy : y < 2 ^ b) (h : pbits b x = pbits b y) :
    x = y := by
  have := congrArg val h
  rwa [val_pbits, val_pbits, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem top_eq_one_iff (b n m : ℕ) (hm : m < 2 ^ b) (hn : n - 1 < 2 ^ b) :
    topK (K := K) b n m = 1 ↔ m = n - 1 := by
  have hlen : (pbits b m).length = (pbits b (n - 1)).length := by simp [pbits_length]
  rw [topK, eqK_bool _ _ hlen]
  constructor
  · intro h
    split_ifs at h with heq
    · exact pbits_inj b m (n - 1) hm hn heq
    · exact absurd h zero_ne_one
  · intro h; subst h; simp

theorem top_eq_zero_of_ne (b n m : ℕ) (hm : m < 2 ^ b) (hn : n - 1 < 2 ^ b) (h : m ≠ n - 1) :
    topK (K := K) b n m = 0 := by
  have hlen : (pbits b m).length = (pbits b (n - 1)).length := by simp [pbits_length]
  rw [topK, eqK_bool _ _ hlen, if_neg]
  intro heq
  exact h (pbits_inj b m (n - 1) hm hn heq)

/-- **The range gate**: on boolean shift bits, `ltm + top = 1 ↔ m ≤ n − 1`. -/
theorem range_gate_iff (b n m : ℕ) (hm : m < 2 ^ b) (hn : n - 1 < 2 ^ b) :
    rangeK (K := K) b n m = 1 ↔ m ≤ n - 1 := by
  have hlen : (pbits b m).length = (pbits b (n - 1)).length := by simp [pbits_length]
  have hv : val (pbits b m) < val (pbits b (n - 1)) ↔ m < n - 1 := by
    rw [val_pbits, val_pbits, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]
  rw [rangeK, topK, ltK_bool _ _ hlen, eqK_bool _ _ hlen]
  by_cases hlt : ltL (pbits b m) (pbits b (n - 1)) = true
  · have h1 : m < n - 1 := hv.mp ((ltL_iff _ _ hlen).mp hlt)
    have h2 : pbits b m ≠ pbits b (n - 1) := fun h => by
      have := pbits_inj b m (n - 1) hm hn h; omega
    rw [if_pos hlt, if_neg h2, add_zero]
    exact ⟨fun _ => le_of_lt h1, fun _ => rfl⟩
  · have h1 : ¬ m < n - 1 := fun h => hlt ((ltL_iff _ _ hlen).mpr (hv.mpr h))
    rw [if_neg hlt, zero_add]
    by_cases heq : pbits b m = pbits b (n - 1)
    · have := pbits_inj b m (n - 1) hm hn heq
      rw [if_pos heq]
      exact ⟨fun _ => le_of_eq this, fun _ => rfl⟩
    · have h3 : m ≠ n - 1 := fun h => heq (by rw [h])
      rw [if_neg heq]
      exact ⟨fun h => absurd h zero_ne_one, fun h => absurd (lt_of_le_of_ne h h3) h1⟩

/-- **At `n = 2^b` (Goldilocks: `n = 64`, `b = 6`) the range gate is vacuous** — `n − 1 = 2^b − 1`
is every shift bit `1`, and `ltm + top = 1` is the boolean telescoping identity
`Σ_k eqm_{k+1}(1 − m_k) + Π_k m_k = 1`; it may be dropped there.  At `n = 10` and `n = 17` it is
load-bearing (section D). -/
theorem range_gate_vacuous_pow2 (b m : ℕ) (hm : m < 2 ^ b) : rangeK (K := K) b (2 ^ b) m = 1 :=
  (range_gate_iff b (2 ^ b) m hm (Nat.sub_lt (Nat.two_pow_pos b) Nat.one_pos)).mpr (by omega)

end Repair

/-! ## F. `hax` is derivable: the axis-guarded ROM evaluator and the bounded-run invariant

`GenGuardedRom.evalGAxRom`, `evalGRom_boundedBy_axes`, `RunAxesBoundedBy`,
`runAxesBoundedBy_of_hyps`, `result_boundedBy_of_hyps`, `exists_cert`. -/

section Axes

open Nock.NockVMROM.Thm54.TraceGen (evalGRom RunBoundedBy)
open Nock.FieldEmbedding (BoundedBy)

/-- **`evalGRom q` with the OP0 tail atom and the OP9 axis atom guarded `< q`** — the
`Option`-guard shape of `GenGuardedRom.evalGRom`, applied to the two axis reads.
Every other arm is character-for-character `evalGRom`'s. -/
def evalGAxRom (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGAxRom q fuel subj (.cell b c), evalGAxRom q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => if ax < q then Noun.slot ax subj else none
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b, evalGAxRom q fuel subj c with
             | some sb, some sc => evalGAxRom q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGAxRom q fuel subj tail).map Noun.wut
    | 4 => (evalGAxRom q fuel subj tail).bind (FieldEmbedding.lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b, evalGAxRom q fuel subj c with
             | some sb, some sc => some (Noun.tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGAxRom q fuel subj b with
             | some (.atom 0) => evalGAxRom q fuel subj c
             | some (.atom 1) => evalGAxRom q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b with
             | some sb => evalGAxRom q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGAxRom q fuel subj b with
             | some sb => evalGAxRom q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             if ax < q then
               match evalGAxRom q fuel subj c with
               | some core =>
                 match Noun.slot ax core with
                 | some arm => evalGAxRom q fuel core arm
                 | none => none
               | none => none
             else none
           | _ => none
    | _ => none

/-- A successful guarded increment yields an atom `< q`. -/
theorem lusGBy_boundedBy {q : ℕ} {x m : Noun} (h : FieldEmbedding.lusGBy q x = some m) :
    BoundedBy q m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        rw [← h]; exact hlt
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-- **The invariant `hbound`, `hs`, `hf` carry**: a guarded ROM run on a `BoundedBy q` subject and
formula (`1 < q`) never reaches an OP0/OP9 axis atom `≥ q` — it is an axis-guarded run — and its
result is `BoundedBy q`.  The axis atom is an atom of the formula of some nested call, and every
nested call's subject and formula are built from sub-nouns of bounded nouns, `0`/`1`, guarded
increments and results of earlier calls. -/
theorem evalGRom_boundedBy_axes (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : ℕ) (s f : Noun), ∀ r : Noun, BoundedBy q s → BoundedBy q f →
      evalGRom q fuel s f = some r → BoundedBy q r ∧ evalGAxRom q fuel s f = some r := by
  intro fuel s f
  induction fuel, s, f using evalGRom.induct q <;> intro r hs hf h <;>
    simp only [evalGRom, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] at h <;>
    simp only [evalGAxRom, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq] <;>
    grind [FieldEmbedding.slot_boundedBy, FieldEmbedding.wut_boundedBy,
      FieldEmbedding.tis_boundedBy, lusGBy_boundedBy, FieldEmbedding.BoundedBy_cell,
      FieldEmbedding.BoundedBy_atom]

def RunAxesBoundedBy (q fuel : ℕ) (subject formula : Noun) : Prop :=
  ∃ result, evalGAxRom q fuel subject formula = some result

/-- **`hax` is a theorem of the tree's hypotheses**: `hbound : RunBoundedBy p`, `hs`, `hf` and
`hp : 25 ≤ p` give `RunAxesBoundedBy p` — every OP0 tail atom and OP9 axis atom the run reads
is `< p`, hence (`exists_cert`) certified with `m ≤ Nat.size p − 1`.  No new hypothesis. -/
theorem runAxesBoundedBy_of_hyps {p fuel : ℕ} {subject formula : Noun} (hp : 25 ≤ p)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : BoundedBy p subject) (hf : BoundedBy p formula) :
    RunAxesBoundedBy p fuel subject formula := by
  obtain ⟨r, hr⟩ := hbound
  exact ⟨r, (evalGRom_boundedBy_axes p (by omega) fuel subject formula r hs hf hr).2⟩

/-- The same run's result is `BoundedBy p` (the invariant's other half). -/
theorem result_boundedBy_of_hyps {p fuel : ℕ} {subject formula result : Noun} (hp : 25 ≤ p)
    (hr : evalGRom p fuel subject formula = some result)
    (hs : BoundedBy p subject) (hf : BoundedBy p formula) : BoundedBy p result :=
  (evalGRom_boundedBy_axes p (by omega) fuel subject formula result hs hf hr).1

/-- **Negative control — `hf` is what carries it.**  Without the bound on the formula,
`evalGRom 31` serves `[0 34]` on any subject (`Batch556.evalGRom_op0_unguarded`) while the
axis-guarded evaluator rejects it: the derivation is not a tautology of the guard. -/
theorem axis_guard_bites (S : Noun) :
    evalGAxRom 31 1 S (.cell (.atom 0) (.atom 34)) = none
    ∧ evalGRom 31 1 S (.cell (.atom 0) (.atom 34)) = Noun.slot 34 S
    ∧ ¬ BoundedBy 31 (Noun.cell (.atom 0) (.atom 34)) := by
  refine ⟨by simp [evalGAxRom], Batch556.evalGRom_op0_unguarded 31 0 S 34, ?_⟩
  simp

end Axes

/-! ## G. Degrees and widths of the repaired design -/

section Degrees

variable {F : Type} [Field F]

open OptimizedMemoryGateBasis (bcur bbool)

/-- Placeholder columns: an `eq` helper `E`, the `top` column, the certificate bits `c_j`, the
shift bits `m_k`, the `p := Π_{k<3} lin_k` helper. -/
def colE : CoeffExpr F := bcur 300
def colTop : CoeffExpr F := bcur 301
def colP : CoeffExpr F := bcur 182
def colC (j : ℕ) : CoeffExpr F := bcur (100 + j)
def colM (k : ℕ) : CoeffExpr F := bcur (170 + k)

/-- `lin_i` as an expression: the column where the constant bit is `1`, `1 − column` where it is
`0`.  The bit pattern of `p` (or of `n − 1`) is written as `0/1` constants — `CoeffExpr.const : F`
and `Expr.Const : ℤ` both accept it.  Degree `1` either way. -/
def linExpr (c : CoeffExpr F) (b : Bool) : CoeffExpr F := if b then c else .sub (.const 1) c

theorem linExpr_degree (c : CoeffExpr F) (b : Bool) (h : c.degree = 1) :
    (linExpr c b).degree = 1 := by
  cases b <;> simp [linExpr, CoeffExpr.degree, h]

theorem foldl_mul_degree (lins : List (CoeffExpr F)) :
    ∀ (E : CoeffExpr F) (d : ℕ), E.degree = d → (∀ l ∈ lins, l.degree = 1) →
      (lins.foldl .mul E).degree = d + lins.length := by
  induction lins with
  | nil => intro E d hE _; simp [hE]
  | cons l ls ih =>
      intro E d hE hl
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (.mul E l) (d + 1) (by simp [CoeffExpr.degree, hE, hl l (by simp)])
        (fun x hx => hl x (by simp [hx]))]
      ring

/-- One summand of the comparison gate: a helper (or `top`) times at most two in-gate `lin`s
times `(1 − c_i)`, for a position with `p_i = 1` (positions with `p_i = 0` contribute nothing). -/
def termExpr (E : CoeffExpr F) (lins : List (CoeffExpr F)) (c : CoeffExpr F) : CoeffExpr F :=
  .mul (lins.foldl .mul E) (.sub (.const 1) c)

theorem termExpr_degree (E : CoeffExpr F) (lins : List (CoeffExpr F)) (c : CoeffExpr F)
    (hE : E.degree = 1) (hl : ∀ l ∈ lins, l.degree = 1) (hc : c.degree = 1) :
    (termExpr E lins c).degree = 2 + lins.length := by
  simp only [termExpr, CoeffExpr.degree, foldl_mul_degree lins E 1 hE hl, hc]
  simp
  ring

/-- **Every summand has degree ≤ 4** when at most two `lin`s sit in-gate between helpers — so
a helper every three factors (`⌊(n−1)/3⌋` of them) suffices for any `n`, multiple of `3` or not. -/
theorem termExpr_degree_le (E : CoeffExpr F) (lins : List (CoeffExpr F)) (c : CoeffExpr F)
    (hE : E.degree = 1) (hl : ∀ l ∈ lins, l.degree = 1) (hc : c.degree = 1)
    (hlen : lins.length ≤ 2) : (termExpr E lins c).degree ≤ 4 := by
  rw [termExpr_degree E lins c hE hl hc]; omega

def sumExpr : List (CoeffExpr F) → CoeffExpr F
  | [] => .const 0
  | t :: ts => .add t (sumExpr ts)

theorem sumExpr_degree_le (L : List (CoeffExpr F)) (d : ℕ) (h : ∀ t ∈ L, t.degree ≤ d) :
    (sumExpr L).degree ≤ d := by
  induction L with
  | nil => simp [sumExpr, CoeffExpr.degree]
  | cons t ts ih =>
      simp only [sumExpr, CoeffExpr.degree]
      exact max_le (h t (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- The comparison gate, `top`-seeded form: `Σ_i eq'_{i+1}·(1 − c_{n−1−i})·p_i − top = 0`
(`eq'_{n−1} := top`, so `lt' = top · lt` and the gate is `top · (lt − 1) = 0` at degree ≤ 4
without a `top · (degree-4)` product). -/
def ltGate (terms : List (CoeffExpr F)) : CoeffExpr F := .sub (sumExpr terms) colTop

theorem ltGate_degree_le (terms : List (CoeffExpr F)) (h : ∀ t ∈ terms, t.degree ≤ 4) :
    (ltGate terms).degree ≤ 4 := by
  simp only [ltGate, CoeffExpr.degree]
  exact max_le (sumExpr_degree_le terms 4 h) (by simp [colTop, bcur, CoeffExpr.degree])

/-- The range gate on the shift bits: `Σ_k eqm_{k+1}·(1 − m_k)·(n−1)_k + top − 1 = 0`. -/
def mRangeGate (terms : List (CoeffExpr F)) : CoeffExpr F :=
  .sub (.add (sumExpr terms) colTop) (.const 1)

theorem mRangeGate_degree_le (terms : List (CoeffExpr F)) (h : ∀ t ∈ terms, t.degree ≤ 4) :
    (mRangeGate terms).degree ≤ 4 := by
  simp only [mRangeGate, CoeffExpr.degree]
  exact max_le (max_le (sumExpr_degree_le terms 4 h) (by simp [colTop, bcur, CoeffExpr.degree]))
    (by simp)

/-- An `eq` helper pin `E' − E·l₁·l₂·l₃ = 0` — degree exactly `4`. -/
def helperPin (E' E l1 l2 l3 : CoeffExpr F) : CoeffExpr F :=
  .sub E' (.mul (.mul (.mul E l1) l2) l3)

theorem helperPin_degree (E' E l1 l2 l3 : CoeffExpr F) (h0 : E'.degree = 1) (h1 : E.degree = 1)
    (h2 : l1.degree = 1) (h3 : l2.degree = 1) (h4 : l3.degree = 1) :
    (helperPin E' E l1 l2 l3).degree = 4 := by
  simp [helperPin, CoeffExpr.degree, h0, h1, h2, h3, h4]

def pPin (bits : ℕ → Bool) : CoeffExpr F :=
  .sub colP (.mul (.mul (linExpr (colM 5) (bits 5)) (linExpr (colM 4) (bits 4)))
    (linExpr (colM 3) (bits 3)))
def topPin (bits : ℕ → Bool) : CoeffExpr F :=
  .sub colTop (.mul (.mul (.mul colP (linExpr (colM 2) (bits 2))) (linExpr (colM 1) (bits 1)))
    (linExpr (colM 0) (bits 0)))

theorem topPin_degrees (bits : ℕ → Bool) :
    (pPin (F := F) bits).degree = 3 ∧ (topPin (F := F) bits).degree = 4 := by
  have hl : ∀ k b, (linExpr (colM (F := F) k) b).degree = 1 :=
    fun k b => linExpr_degree _ _ (by simp [colM, bcur, CoeffExpr.degree])
  constructor
  · simp [pPin, CoeffExpr.degree, hl, colP, bcur]
  · simp [topPin, CoeffExpr.degree, hl, colP, colTop, bcur]

theorem boolean_degree (j : ℕ) : (bbool (colC (F := F) j)).degree = 2 := rfl

/-- The concrete `n = 64` comparison gate: 63 summands over the bit pattern of Goldilocks
(`p_i = 1` for `i ∈ [32, 63]` and `i = 0`; `p_i = 0` for `i ∈ [1, 31]`), the `top`-seeded chain
with a helper every three factors.  Position `i` (absolute) is summand index `k = 63 − i`
(MSB first); the number of factors above `k` is `k` (`top` counted) so the helper index is
`k / 3` and `k % 3` `lin`s sit in-gate. -/
def goldilocksBit (i : ℕ) : Bool := decide (32 ≤ i ∧ i ≤ 63) || decide (i = 0)

def helperAt (k : ℕ) : CoeffExpr F := if k = 0 then colTop else bcur (300 + k)

def termAt (k : ℕ) : CoeffExpr F :=
  termExpr (helperAt (k / 3))
    ((List.range (k % 3)).map fun j => linExpr (colC (k - (k % 3) + j)) (goldilocksBit (63 - (k - (k % 3) + j))))
    (colC k)

/-- The summands at positions with `p_i = 1`: `k = 63 − i` for `i ∈ [32, 62]` and `i = 0`. -/
def goldilocksTerms : List (CoeffExpr F) :=
  ((List.range 63).filter fun k => goldilocksBit (63 - (k + 1))).map fun k => termAt (k + 1)

theorem helperAt_degree (k : ℕ) : (helperAt (F := F) k).degree = 1 := by
  unfold helperAt; split_ifs <;> simp [colTop, bcur, CoeffExpr.degree]

theorem termAt_degree_le (k : ℕ) : (termAt (F := F) k).degree ≤ 4 := by
  apply termExpr_degree_le
  · exact helperAt_degree _
  · intro l hl
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨j, _, rfl⟩ := hl
    exact linExpr_degree _ _ (by simp [colC, bcur, CoeffExpr.degree])
  · simp [colC, bcur, CoeffExpr.degree]
  · simp only [List.length_map, List.length_range]
    omega

/-- **The Goldilocks comparison gate has degree ≤ 4**, and has `32` summands (`i ∈ [32, 62]`
and `i = 0`). -/
theorem goldilocks_ltGate_degree_le : (ltGate (goldilocksTerms (F := F))).degree ≤ 4 := by
  apply ltGate_degree_le
  intro t ht
  simp only [goldilocksTerms, List.mem_map] at ht
  obtain ⟨k, _, rfl⟩ := ht
  exact termAt_degree_le _

theorem goldilocksTerms_length : (goldilocksTerms (F := F)).length = 32 := by
  simp only [goldilocksTerms, List.length_map]
  decide

end Degrees

/-! ### Widths and gate counts as functions of `n = Nat.size p` -/

/-- Shift bits `b := ⌈log₂ n⌉` (`Nat.clog 2 n`): `m ∈ [0, 2^b)` covers `m ≤ n − 1`. -/
def shiftBits (n : ℕ) : ℕ := Nat.clog 2 n

theorem shiftBits_covers (n : ℕ) : n - 1 < 2 ^ shiftBits n := by
  have := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have := Nat.two_pow_pos (Nat.clog 2 n)
  unfold shiftBits; omega

def ceil3 (b : ℕ) : ℕ := (b + 2) / 3

/-- **New compute columns**: `c_1..c_{n−1}`; `m_0..m_{b−1}`; the power-gadget helpers
`⌈b/3⌉` base (`h`, `t`) and `⌈b/3⌉` 𝕂 (`H`, `T`, each `e` coordinates); the `top` chain
`⌈b/3⌉` (`p`, `top`); the `eq` helpers `⌊(n−1)/3⌋`. -/
def rangeColumns (e n : ℕ) : ℕ :=
  (n - 1) + shiftBits n + ceil3 (shiftBits n) * (1 + e) + ceil3 (shiftBits n) + (n - 1) / 3

/-- **New compute gates**: booleanity `(n−1) + b`; power pins `2⌈b/3⌉`; `top` chain pins
`⌈b/3⌉`; `eq` helper pins `⌊(n−1)/3⌋`; the comparison gate; the range gate; the axis equation. -/
def rangeGates (n : ℕ) : ℕ :=
  (n - 1) + shiftBits n + 2 * ceil3 (shiftBits n) + ceil3 (shiftBits n) + (n - 1) / 3 + 3

theorem rangeColumns_64 : rangeColumns 3 64 = 100 := by
  simp [rangeColumns, shiftBits, clog_64, ceil3]
theorem rangeColumns_10 : rangeColumns 3 10 = 26 := by
  simp [rangeColumns, shiftBits, clog_10, ceil3]
theorem rangeColumns_17 : rangeColumns 3 17 = 36 := by
  simp [rangeColumns, shiftBits, clog_17, ceil3]

theorem compute_width_64 : 202 + rangeColumns 3 64 = 302 := by rw [rangeColumns_64]
theorem compute_width_vs_28th : rangeColumns 3 64 = Batch555.certificateColumns 3 + 23 := by
  rw [rangeColumns_64, Batch555.certificateColumns_eq]

theorem rangeGates_64 : rangeGates 64 = 99 := by simp [rangeGates, shiftBits, clog_64, ceil3]
theorem rangeGates_10 : rangeGates 10 = 25 := by simp [rangeGates, shiftBits, clog_10, ceil3]
theorem rangeGates_17 : rangeGates 17 = 35 := by simp [rangeGates, shiftBits, clog_17, ceil3]

/-- `C.rap.s`: `313 → 412` at `n = 64` (`411` if the vacuous range gate is dropped). -/
theorem compute_gates_64 : 313 + rangeGates 64 = 412 := by rw [rangeGates_64]

/-- Fixture widths: Tier A (`p = 769`, `n = 10`) `228`; matmul (`p = 65537`, `n = 17`) `238`. -/
theorem fixture_widths : 202 + rangeColumns 3 10 = 228 ∧ 202 + rangeColumns 3 17 = 238 := by
  rw [rangeColumns_10, rangeColumns_17]; exact ⟨rfl, rfl⟩

/-! ## H. The memory side moves by one exponent; the event majorant by two -/

section Memory

variable {K : Type*} [Field K]

open Polynomial

/-- Nothing on the memory side is re-proved — but the deployed constant
`λ^{62}` becomes `λ^{n−1}`. -/
theorem bracket_zero_iff_at_bitLength (p : ℕ) (m : ℕ) (c : ℕ → Bool) (v r : List Bool)
    (hm : m ≤ Nat.size p - 1) :
    Batch554.bracket (K := K) (Nat.size p - 1) m c v r = 0
      ↔ (∀ j, m < j → j ≤ Nat.size p - 1 → c j = false) ∧ v = r ++ bitsOf m c :=
  Batch554.bracket_zero_iff _ m c v r hm

/-- At Goldilocks the scale exponent is `63`, not the second pass's `62`: verify weight
`λ^{63}`, read weight `λ^{63}·T·ts`, constant records `(λ, λ^{63})`, `(λ, λ^{63} + λ^{62})`,
`C' = λ^{63} + Σ_{j=1}^{63} c_j λ^{63−j}`. -/
theorem goldilocks_scale : Nat.size Nock.Field.p - 1 = 63 := by rw [size_goldilocks]


theorem pwAccountingWork'_64 (N M : ℕ) :
    pwAccountingWork' 64 N M = Batch556.pwAccountingWork N M + 2 := by
  simp [pwAccountingWork', Batch556.pwAccountingWork]

open Nock.NockVMROM.Thm54.GoldilocksParameters in
theorem figures_unmoved_31' :
    (367 * 2 ^ 62 + 144 * 2 ^ 31 + 28 + 2 * pwAccountingWork' 64 (2 ^ 31) (2 ^ 31)) * 2 ^ 122
      < 2 * cardKGold := by
  norm_num [pwAccountingWork']

open Nock.NockVMROM.Thm54.GoldilocksParameters in
theorem figures_unmoved_32' :
    (367 * 2 ^ 64 + 144 * 2 ^ 32 + 28 + 2 * pwAccountingWork' 64 (2 ^ 32) (2 ^ 32)) * 2 ^ 120
      < 2 * cardKGold := by
  norm_num [pwAccountingWork']

/-- **Item 6**: `m = n − 1` with all lower bits `0` certifies `2^{n−1}`, which is `< p` for every
odd `p ≥ 3` (a power of two is never an odd prime), and the gadget accepts it. -/
theorem top_shift_zero_bits_accepted (p : ℕ) (hp : 3 ≤ p) (hodd : p % 2 = 1) :
    cert (Nat.size p - 1) (fun _ => false) = 2 ^ (Nat.size p - 1)
    ∧ 2 ^ (Nat.size p - 1) < p
    ∧ ltCert (K := K) (Nat.size p) p (Nat.size p - 1) (fun _ => false) = 1 := by
  have hc : cert (Nat.size p - 1) (fun _ => false) = 2 ^ (Nat.size p - 1) := by simp [cert]
  obtain ⟨hlo, _⟩ := size_spec p (by omega)
  have hn : 2 ≤ Nat.size p := Nat.lt_size.mpr (by omega)
  have hlt : 2 ^ (Nat.size p - 1) < p := by
    rcases Nat.lt_or_eq_of_le hlo with h | h
    · exact h
    · exfalso
      have : 2 ^ (Nat.size p - 1) % 2 = 0 := by
        rw [show Nat.size p - 1 = (Nat.size p - 2) + 1 by omega, pow_succ]; simp
      omega
  exact ⟨hc, hlt, (gadget_complete (K := K) p (by omega) _ _ (by rw [hc]; exact hlt)).2 rfl⟩

/-- Goldilocks: `2^63 < p` (`Batch555.goldilocks_window`), so the `m = 63`, all-zero row is honest
there too; the second pass's `hp63` is a theorem at Goldilocks and a hypothesis nowhere. -/
theorem goldilocks_top_shift :
    cert 63 (fun _ => false) = 2 ^ 63 ∧ 2 ^ 63 < Nock.Field.p := by
  exact ⟨by simp [cert], Batch555.goldilocks_window⟩

end Memory

end Nock.RedTeam.Batch557

#print axioms Nock.RedTeam.Batch557.ltK_expand
#print axioms Nock.RedTeam.Batch557.ltK_bool
#print axioms Nock.RedTeam.Batch557.at_most_one_term
#print axioms Nock.RedTeam.Batch557.gadget_sound
#print axioms Nock.RedTeam.Batch557.gadget_complete
#print axioms Nock.RedTeam.Batch557.exists_cert
#print axioms Nock.RedTeam.Batch557.cert_mod_unique_of_lt
#print axioms Nock.RedTeam.Batch557.accepted_row_axis
#print axioms Nock.RedTeam.Batch557.brief_gadget_accepts_34_at_31
#print axioms Nock.RedTeam.Batch557.brief_gadget_accepts_1024_at_769
#print axioms Nock.RedTeam.Batch557.range_gate_iff
#print axioms Nock.RedTeam.Batch557.top_eq_one_iff
#print axioms Nock.RedTeam.Batch557.evalGRom_boundedBy_axes
#print axioms Nock.RedTeam.Batch557.runAxesBoundedBy_of_hyps
#print axioms Nock.RedTeam.Batch557.axis_guard_bites
#print axioms Nock.RedTeam.Batch557.goldilocks_ltGate_degree_le
#print axioms Nock.RedTeam.Batch557.topPin_degrees
#print axioms Nock.RedTeam.Batch557.compute_width_64
#print axioms Nock.RedTeam.Batch557.figures_unmoved_31'
#print axioms Nock.RedTeam.Batch557.top_shift_zero_bits_accepted
