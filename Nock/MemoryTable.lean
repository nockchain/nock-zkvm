/-
  Nock/MemoryTable.lean

  The **Memory Table** of NockVM (paper Appendix B.2), modeled as a full, degree-tracked AIR constraint object (`RAPmem`),
  together with the algorithmic verifier `Vmem`,
  and the proof of **`Lem:equiv_mem`**: the RAP admits a satisfying assignment
  for `(x^mem, x_out^mem, W_mem)` iff the algorithmic verifier accepts.

  The AIR is modeled as concrete polynomial-constraint `Prop`s over the
  extension field `K`, not as abstract predicates.  The fingerprint triples `FP` and memory
  records `MemRec` of `Nock/ComputeTable.lean` are reused.  Everything is generic over an
  arbitrary field `K`; `goldilocks_prime` is not used.

  This is the exact analogue of `Nock/ComputeTable.lean` for the memory side.  The compute table
  is per-*opcode* (11 states, one big evaluation block with several non-linear gates); the memory
  table is much simpler — FOUR states,
  all equality constraints being linear/`cons`, with the single non-linearity being the LogUp
  `intermediate` accumulator, handled by the same inverse-witness gate
  technique as `equiv_compute`.

  ─────────────────────────────────────────────────────────────────────────────────────────
  MODELING NOTES

  * **Columns.**  `pt`/`lc`/`rc : K^5` each = a fingerprint triple
    (`.noun : FP K`) + `.indicator` (`axis_indicator`) + `.counts` (`axis_counts`); we bundle
    these as `Cell`.  The child labels `lc`/`rc` also carry a state, held on `Pub` as `lcSt`/`rcSt`.  `mem_record ∈ (K³)²×F×K` is the reused `MemRec`.  The LogUp accumulator is the pair
    `(intermediate_i, intermediate_{i+1}) = (ipre, icur)`.

  * **State = one-hot.**  `op_j`, `j∈{0,1,2,3}` for `{decompose, halt, read_root, verify_child}`.  We take `op := opSel p.st`, the one-hot encoding; booleanity and
    `Σop_j=1` then hold automatically (`SVsat_holds`), exactly as in `ComputeTable`.

  * **The LogUp / `intermediate` step.**  The constraint-spec form is
    the multiplicative `(RLC^γ(mem_record) − β)·(intermediate(i) − intermediate(i−1)) = op₃ − op₂`.
    The algorithm uses the inverse form `intermediate_{i+1} − intermediate_i =
    (RLC(mem_record) + X)^{-1}` (read_root, add) resp. `intermediate_i − intermediate_{i+1} =
    (…)^{-1}` (verify_child, remove).  We realize the RAP with an explicit inverse-witness column
    `g` (mirroring `equiv_compute`'s inverse gates): `pole·g = 1 ∧ Δ = ±g`, and prove it
    `⟺` the algorithm's `Δ = ±pole⁻¹` under the genericity condition `pole ≠ 0` (`WF`, the random
    `β` — cf. the compute table's `WF` RLC-nondegeneracy).  See the notes on `pole` and
    `interR` for the sign /
    `+X` vs `−β` reconciliation, taken identically on both RAP and V sides as in `equiv_compute`.
  ─────────────────────────────────────────────────────────────────────────────────────────
-/
import Mathlib.Data.Nat.Size
import Nock.ComputeTable

namespace Nock
namespace MemoryTable

open Classical ComputeTable
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

/-! ## The four memory-table states -/

/-- The memory-table state `𝒮 := {decompose, halt, read_root, verify_child}`.
    Table `tab:v_mem` labels the 4th column `check_child`; the algorithm and
    the label set call it `verify_child`; it is the same state. -/
inductive MState
  | decompose | halt | read_root | verify_child
deriving DecidableEq, Repr

namespace MState
/-- The opcode index `j ∈ {0,1,2,3}`. -/
def toIdx : MState → ℕ
  | decompose => 0 | halt => 1 | read_root => 2 | verify_child => 3
end MState

/-! ## Columns: `pt`/`lc`/`rc : K⁵` -/

/-- One label cell `∈ K⁵`: a fingerprint triple `.noun` (`size,dyck,leaf`)
    denoting the noun, plus `.indicator` (`axis_indicator`) and `.counts` (`axis_counts`). -/
structure Cell (K : Type*) where
  noun      : FP K
  indicator : K
  counts    : K

namespace Cell
/-- The null cell `((0,0,0), 0, 0)` — the `⊥` / `(0,0,0)` table entries. -/
def zero : Cell K := ⟨0, 0, 0⟩
end Cell

/-! ## RAP inputs and the memory-record RLC / LogUp pole -/

/-- The RAP's initial inputs: `z` (atom-fingerprint seed, as in the paper's `(z,0,⊥)`), and the LogUp
    challenges `β, γ` (as in the paper's `RLC^γ(·) − β`).  `Pub.lambda?` is the
    row copy (`none` reads `formRDefault`, see `Pub.lambda`). -/
structure Inputs (K : Type*) where
  z : K
  β : K
  γ : K

/-- `n − 1` at `n = Nat.size (ringChar K)`. Goldilocks is `63`. -/
noncomputable def pwScaleExp (K : Type*) [Field K] : ℕ := Nat.size (ringChar K) - 1

/-- `exists_cert` / `certShift`: `m = Nat.size a − 1`. -/
def formRCertShift (a : ℕ) : ℕ := Nat.size a - 1

/-- MSB-first certificate bits (`OptimizedComputeRangeCertificate.certCBit`).
    `c_{j+1} = formRCertBit a j` is the `Cpoly` coefficient sequence. -/
def formRCertBit (a j : ℕ) : Bool :=
  if j < formRCertShift a then a.testBit (formRCertShift a - 1 - j) else false

/-- `m = Nat.size ax − 1` (`exists_cert` / `certShift`); `T = 1` at `ax = 0`. -/
def formRT (lmb : K) (ax : ℕ) : K :=
  lmb ^ formRCertShift ax

/-- Honest Form R `C' = (Cpoly (n−1) c).eval λ`
    `= λ^{n−1} + Σ_j c_{j+1} λ^{n−1−(j+1)}` (`Cpoly`). -/
noncomputable def formRC (lmb : K) (ax : ℕ) : K :=
  let n := pwScaleExp K
  lmb ^ n +
    ((List.range n).map (fun j =>
      (if formRCertBit ax j then (1 : K) else 0) * lmb ^ (n - (j + 1)))).sum

@[simp] theorem formRT_one (ax : ℕ) : formRT (1 : K) ax = 1 := by
  simp [formRT]

theorem formRT_eq_pow_shift (lmb : K) (ax : ℕ) :
    formRT lmb ax = lmb ^ formRCertShift ax :=
  rfl

/-- Recover a residue `a < ringChar K` with `(a : K) = x`.
    Honest compute records store the Nock axis as this nat-cast (`a < p`). -/
noncomputable def nockAxisOf (x : K) : ℕ :=
  Classical.epsilon (fun a : ℕ => a < ringChar K ∧ (a : K) = x)

theorem nockAxisOf_spec {a : ℕ} (ha : a < ringChar K) :
    nockAxisOf (a : K) < ringChar K ∧ (nockAxisOf (a : K) : K) = (a : K) :=
  Classical.epsilon_spec (p := fun b : ℕ => b < ringChar K ∧ (b : K) = (a : K))
    ⟨a, ha, rfl⟩

/-- Residues below `ringChar K` are unique, so `nockAxisOf` recovers the witness. -/
theorem nockAxisOf_natCast {a : ℕ} (ha : a < ringChar K) :
    nockAxisOf (a : K) = a := by
  have h := nockAxisOf_spec (K := K) ha
  have hmod : nockAxisOf (a : K) ≡ a [MOD ringChar K] :=
    (CharP.natCast_eq_natCast (R := K) (p := ringChar K)).mp h.2
  exact Nat.ModEq.eq_of_lt_of_lt hmod h.1 ha

theorem pwScaleExp_zmod (p : ℕ) [Fact p.Prime] :
    pwScaleExp (ZMod p) = Nat.size p - 1 := by
  simp [pwScaleExp, ZMod.ringChar_zmod_n]

theorem formRC_one (ax : ℕ) :
    formRC (1 : K) ax =
      1 + ((List.range (pwScaleExp K)).map
        (fun j => (if formRCertBit ax j then (1 : K) else 0))).sum := by
  unfold formRC
  simp [one_pow]

theorem formRCertShift_three : formRCertShift 3 = 1 := by decide

theorem formRCertBit_three_zero : formRCertBit 3 0 = true := by
  simp [formRCertBit, formRCertShift_three]

theorem formRCertBit_three_succ {j : ℕ} (hj : 0 < j) : formRCertBit 3 j = false := by
  simp [formRCertBit, formRCertShift_three]
  omega

/-- Form R leftover weights from an a-bearing record (Nock-axis nat-cast in
    `r.axis`).  `(T, C')` are not stored on the record. -/
noncomputable def formRReadPw (lmb : K) (r : ComputeTable.MemRec K) : K :=
  lmb ^ pwScaleExp K * formRT lmb (nockAxisOf r.axis) * r.ts

noncomputable def formRReadCounts (lmb : K) (r : ComputeTable.MemRec K) : K :=
  formRT lmb (nockAxisOf r.axis) * formRC lmb (nockAxisOf r.axis) * r.ts

/-- At `λ = 2`, the verify leftover addend is the paper's `ts` times `2^{n−1}`. -/
theorem formR_at_two_verify (ts : K) :
    (2 : K) ^ pwScaleExp K * ts = ts * (2 : K) ^ pwScaleExp K := by
  ring

/-- At `λ = 2`, the read pw leftover addend is the Form R axis-role weight
    `T·ts` times `2^{n−1}` (`T = λ^m`). -/
theorem formR_at_two_read (ax : ℕ) (ts : K) :
    (2 : K) ^ pwScaleExp K * formRT (2 : K) ax * ts =
      formRT (2 : K) ax * ts * (2 : K) ^ pwScaleExp K := by
  ring

theorem formR_at_two (ax : ℕ) (ts : K) :
    (2 : K) ^ pwScaleExp K * ts = ts * (2 : K) ^ pwScaleExp K ∧
      (2 : K) ^ pwScaleExp K * formRT (2 : K) ax * ts =
        formRT (2 : K) ax * ts * (2 : K) ^ pwScaleExp K :=
  ⟨formR_at_two_verify (K := K) ts, formR_at_two_read ax ts⟩

/-- `formRCertShift` is `Nat.log2`. -/
theorem formRCertShift_eq_log2 (a : ℕ) : formRCertShift a = a.log2 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [formRCertShift, Nat.size_zero]
  have hs : 0 < Nat.size a := Nat.size_pos.mpr ha
  have hlo : 2 ^ (Nat.size a - 1) ≤ a := by
    by_contra h
    have := (Nat.size_le).mpr (Nat.lt_of_not_le h)
    omega
  have hhi : a < 2 ^ (Nat.size a - 1 + 1) := by
    rw [Nat.sub_add_cancel hs]; exact Nat.lt_size_self a
  rw [formRCertShift, Nat.log2_eq_log_two]
  exact (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi).symm

/-- Natural certificate weight `Σ_j c_{j+1} 2^{n−(j+1)}`. -/
def certSum (a n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if formRCertBit a j then 2 ^ (n - (j + 1)) else 0

theorem log2_div_two {a : ℕ} (h : 2 ≤ a) : (a / 2).log2 = a.log2 - 1 := by
  conv_rhs => rw [Nat.log2_def]
  rw [if_pos h]; omega

theorem certBit_div_two {a : ℕ} (h : 2 ≤ a) (j : ℕ) :
    formRCertBit a j =
      (formRCertBit (a / 2) j || (decide (j = a.log2 - 1) && a.testBit 0)) := by
  have hk : 1 ≤ a.log2 := by
    rw [Nat.log2_def, if_pos h]; omega
  simp only [formRCertBit, formRCertShift_eq_log2, log2_div_two h]
  by_cases hj : j < a.log2 - 1
  · have hne : j ≠ a.log2 - 1 := by omega
    have e : a.log2 - 1 - j = (a.log2 - 1 - 1 - j) + 1 := by omega
    simp [hj, show j < a.log2 by omega, hne, e, Nat.testBit_succ]
  · by_cases hj' : j = a.log2 - 1
    · subst hj'
      simp [show a.log2 - 1 < a.log2 by omega]
    · simp [hj, hj', show ¬ j < a.log2 by omega]

theorem certSum_div_two {a n : ℕ} (h : 2 ≤ a) (hn : a.log2 ≤ n) :
    certSum a n = certSum (a / 2) n + (if a.testBit 0 then 2 ^ (n - a.log2) else 0) := by
  have hk : 1 ≤ a.log2 := by
    rw [Nat.log2_def, if_pos h]; omega
  unfold certSum
  have hpt : ∀ j, (if formRCertBit a j then 2 ^ (n - (j + 1)) else 0) =
      (if formRCertBit (a / 2) j then 2 ^ (n - (j + 1)) else 0) +
        (if j = a.log2 - 1 then (if a.testBit 0 then 2 ^ (n - a.log2) else 0) else 0) := by
    intro j
    rw [certBit_div_two h j]
    by_cases hj : j = a.log2 - 1
    · subst hj
      have hb : formRCertBit (a / 2) (a.log2 - 1) = false := by
        simp [formRCertBit, formRCertShift_eq_log2, log2_div_two h]
      rw [hb, show a.log2 - 1 + 1 = a.log2 by omega]
      cases a.testBit 0 <;> simp
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (by omega))]

/-- **Honest certificate at base 2:** `2^m · (2^n + Σ c_{j+1} 2^{n−(j+1)}) = 2^n · a`. -/
theorem cert_two_identity : ∀ (a n : ℕ), 1 ≤ a → a.log2 ≤ n →
    2 ^ a.log2 * (2 ^ n + certSum a n) = 2 ^ n * a := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro n ha hn
    by_cases h2 : 2 ≤ a
    · have hk : 1 ≤ a.log2 := by rw [Nat.log2_def, if_pos h2]; omega
      have hd := ih (a / 2) (by omega) n (by omega) (by rw [log2_div_two h2]; omega)
      rw [log2_div_two h2] at hd
      rw [certSum_div_two h2 hn]
      have hpow : 2 ^ a.log2 = 2 * 2 ^ (a.log2 - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hsplit : 2 ^ a.log2 * 2 ^ (n - a.log2) = 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      have ha2 : a = 2 * (a / 2) + (if a.testBit 0 then 1 else 0) := by
        have := Nat.div_add_mod a 2
        rcases Nat.mod_two_eq_zero_or_one a with hm | hm <;>
          simp [Nat.testBit_zero, hm] <;> omega
      have hmain : 2 ^ a.log2 * (2 ^ n + certSum (a / 2) n) = 2 ^ n * (2 * (a / 2)) := by
        rw [hpow, mul_assoc, hd]; ring
      conv_rhs => rw [ha2]
      split_ifs with hb
      · rw [show 2 ^ n + (certSum (a / 2) n + 2 ^ (n - a.log2)) =
            (2 ^ n + certSum (a / 2) n) + 2 ^ (n - a.log2) by ring, mul_add, hmain, hsplit]
        ring
      · rw [add_zero, add_zero, hmain]
    · have : a = 1 := by omega
      subst this
      simp [certSum, formRCertBit, formRCertShift, Nat.size_one,
        show Nat.log2 1 = 0 by decide]

theorem list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, list_range_map_sum f n,
        Finset.sum_range_succ]
      simp


/-- `formRC` at base `2` is the nat-cast of `2^n + certSum`. -/
theorem formRC_two_eq (a : ℕ) :
    formRC (2 : K) a = ((2 ^ pwScaleExp K + certSum a (pwScaleExp K) : ℕ) : K) := by
  simp only [formRC, certSum, list_range_map_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Honest `(T, C')` at `λ = 2`:** `T · C' = 2^{n−1} · a` whenever the axis fits the
    certificate window (`m ≤ n − 1`). -/
theorem formRT_mul_formRC_two (a : ℕ) (ha : 1 ≤ a) (hp : a.log2 ≤ pwScaleExp K) :
    formRT (2 : K) a * formRC (2 : K) a = (2 : K) ^ pwScaleExp K * (a : K) := by
  have h := cert_two_identity a (pwScaleExp K) ha hp
  rw [formRC_two_eq, formRT, formRCertShift_eq_log2]
  have h' := congrArg (fun x : ℕ => (x : K)) h
  push_cast at h' ⊢
  exact h'

theorem formRT_two_eq (a : ℕ) : formRT (2 : K) a = (2 : K) ^ a.log2 := by
  rw [formRT, formRCertShift_eq_log2]

/-- The certificate window: an axis below `ringChar K` has `m ≤ n − 1`. -/
theorem log2_le_pwScaleExp {a : ℕ} (ha : a < ringChar K) : a.log2 ≤ pwScaleExp K := by
  rw [pwScaleExp, ← formRCertShift, formRCertShift_eq_log2, Nat.log2_eq_log_two,
    Nat.log2_eq_log_two]
  exact Nat.log_mono_right ha.le

/-- **Honest Form R read weights at `λ = 2`.**  For a Nock axis `1 ≤ a < ringChar K` stored as
    its nat-cast, `formRReadPw = 2^{n−1}·2^m·ts` and `formRReadCounts = 2^{n−1}·a·ts`. -/
theorem formRRead_two (r : ComputeTable.MemRec K) {a : ℕ} (hax : r.axis = (a : K))
    (ha1 : 1 ≤ a) (ha : a < ringChar K) :
    formRReadPw (2 : K) r = (2 : K) ^ pwScaleExp K * (2 : K) ^ a.log2 * r.ts ∧
      formRReadCounts (2 : K) r = (2 : K) ^ pwScaleExp K * (a : K) * r.ts := by
  have hna : nockAxisOf r.axis = a := by rw [hax]; exact nockAxisOf_natCast ha
  constructor
  · rw [formRReadPw, hna, formRT_two_eq]
  · rw [formRReadCounts, hna, formRT_mul_formRC_two a ha1 (log2_le_pwScaleExp ha)]

/-- `RLC^γ(mem_record)`: the random linear combination `Σ γ^{i-1}·rec(i)` of
    the record's `K`-components `(root.size, root.dyck, root.leaf, child.size, child.dyck,
    child.leaf, axis, ts)` plus form R's extra coordinate `C'` at `γ^8`.  Default `cprime = 0`
    recovers the eight-wide combination. -/
def recRLC (γ : K) (r : MemRec K) (cprime : K := 0) : K :=
  r.root.size + γ * r.root.dyck + γ ^ 2 * r.root.leaf
    + γ ^ 3 * r.child.size + γ ^ 4 * r.child.dyck + γ ^ 5 * r.child.leaf
    + γ ^ 6 * r.axis + γ ^ 7 * r.ts + γ ^ 8 * cprime

/-- The LogUp **pole** `RLC^γ(mem_record) − β`.  In the algorithm this
    is written `RLC(mem_record) + X`; the formal LogUp variable is instantiated as `X ↦ −β`. -/
def pole (inp : Inputs K) (r : MemRec K) (cprime : K := 0) : K := recRLC inp.γ r cprime - inp.β

/-! ## The row's public label + witness (`x^mem`, `x_out^mem`, `W_mem`) -/

/-- One memory row.  `st` is the parent state; `pt` the parent cell;
    `lc`/`rc` the two child cells with their states `lcSt`/`rcSt`;
    `mem` the single `mem_record`; `(ipre, icur) = (intermediate_i, intermediate_{i+1})` the LogUp
    accumulator pair; `ver` the paper's prover-chosen boolean column selecting which rows contribute to `IO_mem`.  The default is the
    honest generator's assignment `ver := (st = read_root)`; decoding a committed trace reads role 39. -/
structure Pub (K : Type*) where
  st   : MState
  pt   : Cell K
  lc   : Cell K
  rc   : Cell K
  lcSt : MState
  rcSt : MState
  mem  : MemRec K
  ipre : K
  icur : K
  /-- Paper `ver ∈ {0,1}^{h₂}`; `Bool` so booleanity is definitional.  The honest default matches `st = read_root`. -/
  ver  : Bool := decide (st = MState.read_root)
  /-- Form R `C'` override; `none` reads the default `1` (`Pub.cprime`).  `mem.axis` is `T`. -/
  cprime? : Option K := none
  /-- Form R accounting base `λ`.  `none` reads `formRDefault = 2` (`Pub.lambda`).  The challenge is
   copied onto every row. -/
  lambda? : Option K := none

/-- Form R `C'`.  Production decode writes `some (env.trace 57)`
    (`decodeMemPub_cprime`); gates read `recC'` at 𝕂-role 57. -/
def Pub.cprime (p : Pub K) : K := p.cprime?.getD 1

/-- ExactConfig AIR table-constant `λ = formRDefault = 2` when `lambda? = none`.
    Production samples `λ` on `MemoryChallengeTuple` (`|K|¹¹`); family fill
    writes that coin at chal 8 (`memoryKOfTuple_lambda`) and decode sets
    `lambda? := some (env.chal 8)` (`decodeMemPub_lambda`). -/
def Pub.lambda (p : Pub K) : K := p.lambda?.getD 2

/-- The default `λ = 2` is never read in production: the capstone samples `λ` (memory slot 8 / compute slot 9) and the
    honest package is specialized at the sampled `λ`; `formR_at_two` is the `λ = 2` receipt.
    `λ = 1` is a bad-set point (`StrengtheningScope`). -/
def formRDefault : K := 2

/-- A set `lambda?` is the sampled coin, not the ExactConfig default `formRDefault = 2`. -/
@[simp] theorem Pub.lambda_some (p : Pub K) (lam : K) (h : p.lambda? = some lam) :
    p.lambda = lam := by
  simp [Pub.lambda, h]

/-- A set `cprime?` is role 57 / `recC'`, not the ExactConfig default `1`. -/
@[simp] theorem Pub.cprime_some (p : Pub K) (c' : K) (h : p.cprime? = some c') :
    p.cprime = c' := by
  simp [Pub.cprime, h]

/-! ## Authoritative external-memory responses -/

/-- The raw external-memory response served by one memory row: the paper's `ver`-selected
    record. -/
@[reducible] def responseRecords (pub : Pub K) : List (MemRec K) :=
  if pub.ver then [pub.mem] else []

omit [Field K] in
/-- Unfolding of the `ver`-selected response list. -/
@[simp]
theorem responseRecords_spec (pub : Pub K) :
    responseRecords pub = if pub.ver then [pub.mem] else [] :=
  rfl

omit [Field K] in
/-- A row with `ver = true` emits exactly its `mem` record to the external response column. -/
@[simp]
theorem responseRecords_eq_singleton_of_ver (pub : Pub K) (h : pub.ver = true) :
    responseRecords pub = [pub.mem] := by
  simp [responseRecords, h]

omit [Field K] in
/-- A row with `ver = false` emits no external response. -/
@[simp]
theorem responseRecords_eq_nil_of_not_ver (pub : Pub K) (h : pub.ver = false) :
    responseRecords pub = [] := by
  simp [responseRecords, h]

omit [Field K] in
/-- Honest default: a `read_root` row with `ver = true` emits its `mem` record. -/
theorem responseRecords_eq_singleton_of_read_root (pub : Pub K)
    (_h : pub.st = MState.read_root) (hver : pub.ver = true) :
    responseRecords pub = [pub.mem] := by
  simp [responseRecords, hver]

omit [Field K] in
/-- Honest default: a `verify_child` row with `ver = false` emits nothing. -/
theorem responseRecords_eq_nil_of_verify_child (pub : Pub K)
    (_h : pub.st = MState.verify_child) (hver : pub.ver = false) :
    responseRecords pub = [] := by
  simp [responseRecords, hver]

omit [Field K] in
theorem responseRecords_of_honest_ver (pub : Pub K)
    (h : pub.ver = decide (pub.st = MState.read_root)) :
    responseRecords pub =
      match pub.st with
      | .read_root => [pub.mem]
      | .decompose | .halt | .verify_child => [] := by
  cases hst : pub.st <;> simp [responseRecords, h, hst]


/-! ## State-Variables block -/

/-- One-hot encoding of a state. -/
def opSel (st : MState) : MState → K := fun s => if s = st then 1 else 0

/-- `Σ_{j=0}^{3} g j` over the four states. -/
def sum4 (g : MState → K) : K :=
  g MState.decompose + g MState.halt + g MState.read_root + g MState.verify_child

/-- **State-Variables constraints**, with `op := opSel p.st`:
    booleanity and one-hot sum. -/
def SVsat (p : Pub K) : Prop :=
  (∀ j : MState, opSel (K := K) p.st j * (1 - opSel (K := K) p.st j) = 0)
    ∧ sum4 (opSel (K := K) p.st) = 1

/-- The State-Variables block holds automatically for the one-hot encoding. -/
theorem SVsat_holds (p : Pub K) : SVsat (K := K) p := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [opSel]; by_cases h : j = p.st <;> simp [h]
  · cases p.st <;> simp [sum4, opSel]

/-! ## Equality constraints — Table `tab:v_mem`

    Shared verbatim between `RAPmem` and `Vmem` (they differ only in the `intermediate` block),
    so `equiv_mem` passes it through unchanged.  `⊥` (no constraint) rows are simply omitted. -/

/-- Per-state equality block.

    * `decompose`: `pt.noun = cons(lc.noun, rc.noun)`;
      `pt.indicator = lc.indicator + rc.indicator`;
      `2·pt.counts = lc.counts + rc.counts − rc.indicator` (at `λ = 1`; the table's
      `(1/2)·(…)` form is equal over `char ≠ 2`); `mem_record = 0`.  In the Lean statement the
      indicator and counts are scaled by `λ` (Form R).
    * `halt`: `pt.noun` has size `z` and dyck `0` (an atom; leaf free);
      `pt.indicator = pt.counts = 0`; both children null (`x_out = ⊥`); `mem_record = 0`.
    * `read_root`/`verify_child`: `pt.noun = lc.noun`, `lcSt = st`, the right child is null, and
      the indicator/counts are updated by the record's timestamp (and, for `read_root`, axis) weighted by `λ^{n−1}`
      (`pwScaleExp`); `mem.root` (resp. `mem.child`) is `pt.noun`.
      Goldilocks has `n = 64`, so the scale is `λ^{63}`.  `indicator` hosts `pw`. -/
def eqBlk (inp : Inputs K) (p : Pub K) : Prop :=
  match p.st with
  | .decompose =>
      p.pt.noun = FP.cons inp.z p.lc.noun p.rc.noun
        ∧ p.pt.indicator = p.lambda * (p.lc.indicator + p.rc.indicator)
        ∧ p.pt.counts = p.lc.counts + p.rc.counts
            + (p.lambda - 1) * (p.lc.indicator + p.rc.indicator) + p.rc.indicator
        ∧ p.mem = MemRec.zero
  | .halt =>
      p.pt.noun.size = inp.z ∧ p.pt.noun.dyck = 0
        ∧ p.pt.indicator = 0 ∧ p.pt.counts = 0
        ∧ p.lc = Cell.zero ∧ p.rc = Cell.zero
        ∧ p.mem = MemRec.zero
  | .read_root =>
      p.pt.noun = p.lc.noun ∧ p.lcSt = p.st
        ∧ p.pt.indicator =
            p.lc.indicator - p.lambda ^ pwScaleExp K * p.mem.axis * p.mem.ts
        ∧ p.pt.counts = p.lc.counts - p.mem.axis * p.cprime * p.mem.ts
        ∧ p.mem.root = p.pt.noun
        ∧ p.rc = Cell.zero
  | .verify_child =>
      p.pt.noun = p.lc.noun ∧ p.lcSt = p.st
        ∧ p.pt.indicator = p.lc.indicator + p.lambda ^ pwScaleExp K * p.mem.ts
        ∧ p.pt.counts = p.lc.counts + p.lambda ^ pwScaleExp K * p.mem.ts
        ∧ p.mem.child = p.pt.noun
        ∧ p.rc = Cell.zero

/-! ## The `intermediate` LogUp block -/

/-- **RAP form** of the `intermediate` accumulator, with the inverse-witness column `g`.

    * `decompose`/`halt`: `intermediate` is unchanged (`icur = ipre`) — no record is
      added/removed (`op₂ = op₃ = 0` in the constraint-spec form).  The algorithm is
      silent here; the "unchanged" reading is taken identically on both sides.
    * `read_root` ("add"): `pole·g = 1 ∧ icur − ipre = g`  (so `icur − ipre = pole⁻¹`).
    * `verify_child` ("remove"): `pole·g = 1 ∧ icur − ipre = −g`  (so `ipre − icur = pole⁻¹`).

    Multiplying through by `pole`, this is exactly the constraint-spec form
    `pole·(icur − ipre) = op₂ − op₃` (see `logup_spec`).  The spec as printed writes `op₃ − op₂`;
    the sign is reconciled by the algorithm's add/remove semantics. -/
noncomputable def interR (inp : Inputs K) (p : Pub K) (g : K) : Prop :=
  match p.st with
  | .decompose | .halt => p.icur = p.ipre
  | .read_root => pole inp p.mem p.cprime * g = 1 ∧ p.icur - p.ipre = g
  | .verify_child => pole inp p.mem p.cprime * g = 1 ∧ p.icur - p.ipre = -g

/-- **Verifier form** of the `intermediate` accumulator (the algorithm's add/remove step), using the honest
    field inverse `pole⁻¹` (the algorithm's `(RLC(mem_record)+X)^{-1}`). -/
noncomputable def interV (inp : Inputs K) (p : Pub K) : Prop :=
  match p.st with
  | .decompose | .halt => p.icur = p.ipre
  | .read_root => p.icur - p.ipre = (pole inp p.mem p.cprime)⁻¹
  | .verify_child => p.ipre - p.icur = (pole inp p.mem p.cprime)⁻¹

/-! ## The RAP and the algorithmic verifier -/

/-- **The memory RAP `RAP_mem`**: the full degree-tracked constraint
    conjunction for one row, over the auxiliary LogUp inverse column `g`. -/
noncomputable def RAPmem (inp : Inputs K) (p : Pub K) (g : K) : Prop :=
  SVsat p ∧ eqBlk inp p ∧ interR inp p g

/-- **Booleanity of the paper's `ver` column**: `ver·(ver−1)=0`.
    With `ver : Bool` the field embedding is always boolean; stated so `Vmem` carries the
    paper's constraint shape. -/
def verBool (p : Pub K) : Prop :=
  (if p.ver then (1 : K) else 0) * ((if p.ver then (1 : K) else 0) - 1) = 0

/-- `ver : Bool` is definitionally boolean in `K`. -/
theorem verBool_holds (p : Pub K) : verBool (K := K) p := by
  cases hv : p.ver <;> simp [verBool, hv]

/-- **The algorithmic verifier `V_mem`**,
    plus the paper's IO-side `ver` booleanity on the K-side row. -/
noncomputable def Vmem (inp : Inputs K) (p : Pub K) : Prop :=
  verBool p ∧ eqBlk inp p ∧ interV inp p

/-- **Well-formedness** — the paper's implicit genericity condition:
    in the two states that touch a live memory record, the LogUp pole is non-vanishing.  This is
    the exact analogue of the compute table's `WF` (RLC-nondegeneracy / nonzero sizes). -/
structure WF (inp : Inputs K) (p : Pub K) : Prop where
  pole_ne : (p.st = MState.read_root ∨ p.st = MState.verify_child) → pole inp p.mem p.cprime ≠ 0

/-! ### The LogUp inverse-witness gate -/

/-- **`(∃ g, interR) ↔ interV`** — the RAP `intermediate` block (with its inverse-witness column)
    is satisfiable iff the algorithm's honest `pole⁻¹` check passes.  Forward is unconditional
    (`pole·g = 1 ⟹ pole ≠ 0`); backward needs `WF` (the random-`β` non-vanishing). -/
theorem inter_iff (inp : Inputs K) (p : Pub K) (wf : WF inp p) :
    (∃ g, interR inp p g) ↔ interV inp p := by
  cases hst : p.st
  case decompose =>
    simp only [interR, interV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case halt =>
    simp only [interR, interV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case read_root =>
    simp only [interR, interV, hst]
    constructor
    · rintro ⟨g, h1, h2⟩
      have hP : pole inp p.mem p.cprime ≠ 0 := by
        intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
      have hg : g = (pole inp p.mem p.cprime)⁻¹ := by
        calc g = (pole inp p.mem p.cprime)⁻¹ * (pole inp p.mem p.cprime * g) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]
          _ = (pole inp p.mem p.cprime)⁻¹ := by rw [h1, mul_one]
      rw [h2, hg]
    · intro hv
      have hP := wf.pole_ne (Or.inl hst)
      exact ⟨(pole inp p.mem p.cprime)⁻¹, mul_inv_cancel₀ hP, hv⟩
  case verify_child =>
    simp only [interR, interV, hst]
    constructor
    · rintro ⟨g, h1, h2⟩
      have hP : pole inp p.mem p.cprime ≠ 0 := by
        intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
      have hg : g = (pole inp p.mem p.cprime)⁻¹ := by
        calc g = (pole inp p.mem p.cprime)⁻¹ * (pole inp p.mem p.cprime * g) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]
          _ = (pole inp p.mem p.cprime)⁻¹ := by rw [h1, mul_one]
      rw [hg] at h2; linear_combination -h2
    · intro hv
      have hP := wf.pole_ne (Or.inr hst)
      exact ⟨(pole inp p.mem p.cprime)⁻¹, mul_inv_cancel₀ hP, by linear_combination -hv⟩

/-- **`Lem:equiv_mem`.**  `RAP_mem` admits a satisfying assignment for
    `(x^mem, x_out^mem, W_mem)` (over the auxiliary LogUp inverse column `g`) iff the algorithmic
    verifier `V_mem` accepts.  Proved over all four states (the paper gives only a one-line
    sketch: "follow the approach of `Lem:equiv_compute`").

    Structure mirrors `equiv_compute`: the State-Variables block is discharged automatically
    (`SVsat_holds`), the equality block `eqBlk` is shared verbatim between the two sides, and the
    only non-linear step — the `intermediate` LogUp accumulator — is handled by the inverse-witness
    gate `inter_iff` under the genericity hypothesis `WF`. -/
theorem equiv_mem (inp : Inputs K) (p : Pub K) (wf : WF inp p) :
    (∃ g, RAPmem inp p g) ↔ Vmem inp p := by
  unfold RAPmem Vmem
  refine ⟨?_, ?_⟩
  · rintro ⟨g, _hsv, heq, hint⟩
    exact ⟨verBool_holds p, heq, (inter_iff inp p wf).mp ⟨g, hint⟩⟩
  · rintro ⟨_hver, heq, hintv⟩
    obtain ⟨g, hint⟩ := (inter_iff inp p wf).mpr hintv
    exact ⟨g, SVsat_holds p, heq, hint⟩

/-! ### Bridge to the literal constraint-spec form

    The RAP's inverse-witness `intermediate` block realizes exactly the
    multiplicative constraint-spec form `pole·(icur − ipre) = op₂ − op₃`. -/

/-- `op₂ − op₃` (read_root minus verify_child selector) at the row's state. -/
def opDiff (st : MState) : K := opSel st MState.read_root - opSel st MState.verify_child

/-- **The RAP `intermediate` block implies the constraint-spec identity.**  For any witness
    `g` satisfying `interR`, the multiplicative form `pole·(icur − ipre) = op₂ − op₃` holds. -/
theorem logup_spec (inp : Inputs K) (p : Pub K) (g : K) (h : interR inp p g) :
    pole inp p.mem p.cprime * (p.icur - p.ipre) = opDiff p.st := by
  cases hst : p.st <;> simp only [interR, hst] at h
  · -- decompose: op₂ − op₃ = 0, icur = ipre
    rw [show opDiff (K := K) MState.decompose = 0 by simp [opDiff, opSel]]
    linear_combination pole inp p.mem p.cprime * h
  · -- halt
    rw [show opDiff (K := K) MState.halt = 0 by simp [opDiff, opSel]]
    linear_combination pole inp p.mem p.cprime * h
  · -- read_root: op₂ − op₃ = 1, pole·(icur−ipre) = pole·g = 1
    obtain ⟨h1, h2⟩ := h
    rw [show opDiff (K := K) MState.read_root = 1 by simp [opDiff, opSel]]
    linear_combination pole inp p.mem p.cprime * h2 + h1
  · -- verify_child: op₂ − op₃ = −1, pole·(icur−ipre) = pole·(−g) = −1
    obtain ⟨h1, h2⟩ := h
    rw [show opDiff (K := K) MState.verify_child = -1 by simp [opDiff, opSel]]
    linear_combination pole inp p.mem p.cprime * h2 - h1

/-! ## Adversarial selector pinning: a FREE one-hot `MState` selector is forced to `opSel s`

  Mirrors `ComputeTable.oneHot_of_bool_sum` / `SV_pins_head` for the four-state memory selector.
  Unlike the compute table there is NO head-shape block, so the pinning lemma is exactly `oneHot_of_bool_sum` at
  `numStates = 4`: a boolean selector whose four entries sum to `1` is a one-hot `opSel s`.

  FIELD SUBTLETY (same as the compute table).  "Booleanity + sum = 1 ⟹ one-hot" is FALSE in small
  characteristic (three ones sum to `1` in char 2).  We take as hypothesis
  `hchar : ∀ n ≤ 4, (n : K) = 1 → n = 1` (satisfied by char `0` or `> 4`, in particular Goldilocks
  and its extension). -/

/-- `MState` is a `Fintype` (the four memory-table states), used to count a free selector's support. -/
instance : Fintype MState :=
  ⟨⟨[MState.decompose, MState.halt, MState.read_root, MState.verify_child], by decide⟩,
   by intro x; cases x <;> decide⟩

/-- The four-term selector sum as a `Finset.univ` sum. -/
theorem sum_univ_eq (g : MState → K) : (∑ j : MState, g j) = sum4 g := by
  have h : (∑ j : MState, g j)
    = g MState.decompose + (g MState.halt + (g MState.read_root + (g MState.verify_child + 0))) :=
    rfl
  rw [h]; simp only [sum4]; ring

/-- **State-Variables block over a FREE selector**.
    Identical to `SVsat` but with `op` an explicit free argument rather than `opSel p.st`. -/
def SVsatFree (op : MState → K) : Prop :=
  (∀ j : MState, op j * (1 - op j) = 0) ∧ sum4 op = 1

/-- `SVsat` is exactly `SVsatFree` at the honest one-hot selector (`rfl`). -/
theorem SVsat_eq_free (p : Pub K) : SVsat (K := K) p = SVsatFree (opSel (K := K) p.st) := rfl

/-- **MState one-hot pinning.**  A boolean selector summing to `1` over the four states is forced
    to be a one-hot `opSel s`.  Needs `hchar` (the support cardinality `≤ 4` casts injectively). -/
theorem oneHot_of_bool_sum (op : MState → K)
    (hchar : ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1)
    (hb : ∀ j, op j = 0 ∨ op j = 1)
    (hsum : sum4 op = 1) :
    ∃ s, op = opSel s := by
  classical
  set S := Finset.univ.filter (fun j => op j = 1) with hS
  have hcast : (S.card : K) = sum4 op := by
    rw [← sum_univ_eq]
    have hcong : (∑ j : MState, op j) = ∑ j : MState, (if op j = 1 then (1 : K) else 0) :=
      Finset.sum_congr rfl (fun j _ => by rcases hb j with h | h <;> simp [h])
    rw [hcong, Finset.sum_boole]
  rw [hsum] at hcast
  have hle : S.card ≤ 4 := by
    have := Finset.card_filter_le (Finset.univ : Finset MState) (fun j => op j = 1)
    rwa [Finset.card_univ, (by decide : Fintype.card MState = 4)] at this
  have hc1 : S.card = 1 := hchar S.card hle hcast
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
  refine ⟨a, funext fun j => ?_⟩
  simp only [opSel]
  by_cases hja : j = a
  · subst hja
    have haS : j ∈ S := by rw [ha]; exact Finset.mem_singleton_self j
    have : op j = 1 := (Finset.mem_filter.mp haS).2
    simp [this]
  · have hnotin : j ∉ S := by rw [ha, Finset.mem_singleton]; exact hja
    have hne : op j ≠ 1 := fun hc => hnotin (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)
    rcases hb j with h | h
    · simp [hja, h]
    · exact absurd h hne

/-- **`SV_pins` (mechanized).**  Over a FREE selector `op`, the State-Variables block `SVsatFree`
    forces `op = opSel s` for a unique state `s` (via `oneHot_of_bool_sum`).  This is the memory
    analogue of `ComputeTable.SV_pins_head`; there is no head-shape conclusion because the memory SV
    block carries no SV4–6. -/
theorem SV_pins (op : MState → K)
    (hchar : ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1)
    (h : SVsatFree op) : ∃ s : MState, op = opSel s :=
  oneHot_of_bool_sum op hchar (fun j => (bool_iff (op j)).mp (h.1 j)) h.2

/-- Cell-vanishing characterization: a cell is null iff all three of its `K⁵` slots vanish. -/
theorem Cell.zero_iff (c : Cell K) :
    c = Cell.zero ↔ c.noun = 0 ∧ c.indicator = 0 ∧ c.counts = 0 := by
  cases c; simp [Cell.zero, Cell.mk.injEq]

/-- One-hot column reading: the `read_root` slot of `opSel s` is `1` iff `s = read_root`. -/
theorem opSel_read_root_eq_one_iff (s : MState) :
    opSel (K := K) s MState.read_root = 1 ↔ s = MState.read_root := by
  cases s <;> simp [opSel]

/-- One-hot column reading: the `verify_child` slot of `opSel s` is `1` iff `s = verify_child`. -/
theorem opSel_verify_child_eq_one_iff (s : MState) :
    opSel (K := K) s MState.verify_child = 1 ↔ s = MState.verify_child := by
  cases s <;> simp [opSel]

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
  ## MATERIALIZING the `intermediate` accumulator as an ORDERED record list
  ═══════════════════════════════════════════════════════════════════════════════════════════

  The per-row `interR`/`interV` blocks above pin, WITHIN a row, `icur − ipre = ±pole⁻¹` (or
  `icur = ipre`).  What makes the accumulator a genuine `intermediate` "record list" is the
  CROSS-ROW hand-off `icur(i) = ipre(i+1)` plus the terminal/initial boundary `intermediate = 0`.
  Threaded across the BFS-flattened rows in the WALK VISITATION ORDER, the accumulator TELESCOPES: its terminal value is
  `Σ_{read} pole⁻¹ − Σ_{verify} pole⁻¹`, so the terminal-zero constraint FORCES the ordered read/
  verify record lists into the LogUp balance `Σ_{read} pole⁻¹ = Σ_{verify} pole⁻¹` — the field-level
  content of the constraint-spec identity.  This is the memory-side analogue of the
  walk's `qgate ↔ BFSValid` (`Walk.qgate_of_bfsValid`/`bfsValid_of_qgate`): the per-row accumulator
  gates, once chained, FORCE the ordered-list matching. -/

/-- **`interDelta` — the signed per-row contribution to the `intermediate` accumulator**: `+pole⁻¹` when the row ADDS a record (`read_root`), `−pole⁻¹` when it
    REMOVES one (`verify_child`), `0` otherwise (`decompose`/`halt`, the accumulator is unchanged). -/
noncomputable def interDelta (inp : Inputs K) (p : Pub K) : K :=
  match p.st with
  | .read_root => (pole inp p.mem p.cprime)⁻¹
  | .verify_child => -(pole inp p.mem p.cprime)⁻¹
  | .decompose | .halt => 0

/-- **`interV` is exactly the per-row accumulator STEP `icur − ipre = interDelta`.**  This recasts
    the verifier's `intermediate` block as a single signed increment, the
    form the telescope consumes. -/
theorem interV_iff_delta (inp : Inputs K) (p : Pub K) :
    interV inp p ↔ p.icur - p.ipre = interDelta inp p := by
  cases hst : p.st
  case decompose =>
    simp only [interV, interDelta, hst]
    exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  case halt =>
    simp only [interV, interDelta, hst]
    exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  case read_root => simp only [interV, interDelta, hst]
  case verify_child =>
    simp only [interV, interDelta, hst]
    exact ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- **`InterChain` — the ordered `intermediate` accumulator over a walk-ordered row list**.  Each row's `interV` holds; the head's `ipre` is the running `seed`; the
    cross-row hand-off `icur(i) = ipre(i+1)` (`AIR.icurChainExpr`) threads the accumulator to the
    next row; and `term` is the accumulator's value after the last row.  This materializes the
    `intermediate` column as the ordered record list the paper describes. -/
def InterChain (inp : Inputs K) : K → K → List (Pub K) → Prop
  | seed, term, [] => seed = term
  | seed, term, p :: rest => p.ipre = seed ∧ interV inp p ∧ InterChain inp p.icur term rest

/-- **`sumDelta` — the net LogUp mass of the ordered record list**: `Σ_{read} pole⁻¹ −
    Σ_{verify} pole⁻¹`, i.e. the algebraic sum of the signed per-row contributions. -/
noncomputable def sumDelta (inp : Inputs K) (rows : List (Pub K)) : K :=
  (rows.map (interDelta inp)).sum

/-- **THE TELESCOPE (the `qgate → BFSValid` analogue).**  A chained `intermediate` accumulator's
    terminal value is its seed plus the net signed record mass: `term = seed + sumDelta`.  Proven by
    induction on the ordered row list, consuming each row's `interV` as the step `icur − ipre =
    interDelta` (`interV_iff_delta`) and the hand-off `icur(i) = ipre(i+1)`. -/
theorem interChain_telescope (inp : Inputs K) :
    ∀ (rows : List (Pub K)) (seed term : K),
      InterChain inp seed term rows → term = seed + sumDelta inp rows := by
  intro rows
  induction rows with
  | nil => intro seed term h; simp only [sumDelta, List.map_nil, List.sum_nil, add_zero]; exact h.symm
  | cons p rest ih =>
      intro seed term h
      obtain ⟨hseed, hV, hrest⟩ := h
      have hstep : p.icur - p.ipre = interDelta inp p := (interV_iff_delta inp p).mp hV
      have hrec := ih p.icur term hrest
      simp only [sumDelta, List.map_cons, List.sum_cons] at hrec ⊢
      rw [hrec]
      -- term = p.icur + Σrest;  p.icur = p.ipre + interDelta = seed + interDelta
      have hic : p.icur = seed + interDelta inp p := by rw [← hseed]; linear_combination hstep
      rw [hic]; ring

/-- **`sumDelta` splits into the read/verify LogUp sums.**  `sumDelta = Σ_{read_root rows} pole⁻¹ −
    Σ_{verify_child rows} pole⁻¹`: the ordered record list's net mass is the read record mass minus
    the verify record mass. -/
theorem sumDelta_split (inp : Inputs K) (rows : List (Pub K)) :
    sumDelta inp rows
      = ((rows.filter (fun p => decide (p.st = MState.read_root))).map
            (fun p => (pole inp p.mem p.cprime)⁻¹)).sum
        - ((rows.filter (fun p => decide (p.st = MState.verify_child))).map
            (fun p => (pole inp p.mem p.cprime)⁻¹)).sum := by
  induction rows with
  | nil => simp [sumDelta]
  | cons p rest ih =>
      have ihr : (List.map (interDelta inp) rest).sum
          = ((rest.filter (fun p => decide (p.st = MState.read_root))).map
                (fun p => (pole inp p.mem p.cprime)⁻¹)).sum
            - ((rest.filter (fun p => decide (p.st = MState.verify_child))).map
                (fun p => (pole inp p.mem p.cprime)⁻¹)).sum := ih
      cases hst : p.st <;>
        simp only [sumDelta, List.map_cons, List.sum_cons, List.filter_cons, interDelta, hst,
          decide_true, decide_false, reduceCtorEq, if_true, if_false] <;>
        rw [ihr] <;> ring

/-- **THE BALANCE (terminal-zero forces the ordered-list matching).**  If the `intermediate`
    accumulator is chained with initial seed `0` and terminal value `0`, then the ordered read and verify record lists carry EQUAL LogUp
    mass: `Σ_{read_root} pole⁻¹ = Σ_{verify_child} pole⁻¹`.  This is the field-level content of the
    constraint-spec identity — the per-row accumulator gates, once chained, FORCE
    the read/verify record lists to match (in LogUp mass).  Its upgrade to a perfect multiset
    matching is `Thm:IO_result`. -/
theorem interChain_balance (inp : Inputs K) (rows : List (Pub K))
    (h : InterChain inp 0 0 rows) :
    ((rows.filter (fun p => decide (p.st = MState.read_root))).map
        (fun p => (pole inp p.mem p.cprime)⁻¹)).sum
      = ((rows.filter (fun p => decide (p.st = MState.verify_child))).map
          (fun p => (pole inp p.mem p.cprime)⁻¹)).sum := by
  have ht := interChain_telescope inp rows 0 0 h
  rw [zero_add] at ht
  have hsplit := sumDelta_split inp rows
  rw [← ht] at hsplit
  exact sub_eq_zero.mp hsplit.symm

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
  ## The language `L_mem` as a literal set
  ═══════════════════════════════════════════════════════════════════════════════════════════

  The paper defines the memory transition-function language as the SET:
    `L_mem = { (x^mem, x_out^mem) ∈ LT_mem × (LT_mem ∪ {⊥})² | ∃ W, V_mem((x,x_out),W) = 0 }`
  and, in the appendix, as this set UNIONED with the fully-padded terminal `{⊥}³`.
  We build this set object LITERALLY on top of the existing algorithmic verifier `Vmem`, exactly
  mirroring `ComputeTable.Lcomp`.

  * `LTmem` is the memory label `x^mem = (state, (parent, (axis_counts_P, axis_indicator_P)))`: a parent state `st` together with the parent cell `pt : Cell` (its noun
    fingerprint + `axis_indicator`/`axis_counts`).
  * `LT_mem ∪ {⊥}` is `Option (LTmem K)` (`none = ⊥`); the OUTPUT space `(LT_mem ∪ {⊥})²` is
    `OutMem = (Option (LTmem K))²` — the two child slots `(left_child, right_child)`, each a full label or `⊥`.
  * Arithmetization convention `⊥ ↦ (0,0,0)` cell: a `⊥` child slot is the
    null cell `Cell.zero`.  A `⊥` slot carries no state; the reconstruction supplies a placeholder
    (`MState.halt`), which `Vmem` NEVER reads — `eqBlk` reads a child STATE only for a PRESENT
    child (`read_root`/`verify_child` require `left_state = state`, and never read the null right
    child's state).
  * `V_mem((x,x_out),W) = 0` is `Vmem inp pub`; SET membership existentially closes the paper's
    witness `W_mem = (intermediate_i, intermediate_{i+1}, mem_record)`. -/

/-- The memory label `x^mem = (state, (parent, (axis_counts_P, axis_indicator_P)))`: parent state `st` and parent cell `cell : Cell` (noun fingerprint +
    `axis_indicator`/`axis_counts`). -/
structure LTmem (K : Type*) where
  st   : MState
  cell : Cell K

/-- The memory OUTPUT space `(LT_mem ∪ {⊥})²`: the two child slots
    `(left_child, right_child)`, each a full label or `⊥` (`none`). -/
abbrev OutMem (K : Type*) := Option (LTmem K) × Option (LTmem K)

/-- One output slot `LT_mem ∪ {⊥}` as its `(state, cell)`, with the arithmetization convention
    `⊥ = none ↦ (halt, Cell.zero)`.  The placeholder state `halt` is never
    read by `Vmem` on a `⊥` slot (see the section header). -/
def slotCell (o : Option (LTmem K)) : MState × Cell K :=
  match o with
  | none => (MState.halt, Cell.zero)
  | some l => (l.st, l.cell)

/-- Reconstruct the row `Pub` from an input label `x`, an output pair `xout`, and the paper's
    witness `W_mem = (intermediate_i, intermediate_{i+1}, mem_record)`. -/
def toPubMem (x : LTmem K) (xout : OutMem K) (ipre icur : K) (mem : MemRec K) : Pub K where
  st   := x.st
  pt   := x.cell
  lc   := (slotCell xout.1).2
  rc   := (slotCell xout.2).2
  lcSt := (slotCell xout.1).1
  rcSt := (slotCell xout.2).1
  mem  := mem
  ipre := ipre
  icur := icur

/-- **`L_mem`.**  The memory transition-function language as a literal set:
    `{ (x, x_out) ∈ LT_mem × (LT_mem ∪ {⊥})² | ∃ W_mem, V_mem((x,x_out), W_mem) = 0 }`, with
    `V_mem(...) = 0` given by `Vmem` and the witness `W_mem` existentially quantified. -/
noncomputable def Lmem (inp : Inputs K) : Set (LTmem K × OutMem K) :=
  { p | ∃ (ipre icur : K) (mem : MemRec K), Vmem inp (toPubMem p.1 p.2 ipre icur mem) }

/-- **`L_mem`.**  The main-body set `Lmem`, embedded via
    `x ↦ some x`, UNIONED with the fully-padded terminal `{⊥}³` (input `⊥` and both outputs `⊥`)
    — the paper's `∪ {⊥}³`. -/
noncomputable def LmemApp (inp : Inputs K) : Set (Option (LTmem K) × OutMem K) :=
  { p | ∃ x, p.1 = some x ∧ (x, p.2) ∈ Lmem inp } ∪ { (none, none, none) }

/-- **`L_mem` is nonempty (content witness).** -/
theorem Lmem_nonempty (inp : Inputs K) : (Lmem inp).Nonempty := by
  classical
  refine ⟨(⟨MState.halt, ⟨FP.atomFP inp.z 0, 0, 0⟩⟩, (none, none)), 0, 0, MemRec.zero, ?_⟩
  exact ⟨verBool_holds _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end MemoryTable
end Nock
