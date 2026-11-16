import NockvmE2E.Exec.VLink
import NockvmE2E.Exec.PubExe
import Mathlib.Algebra.QuadraticAlgebra.Defs

set_option autoImplicit false

namespace NockvmE2E.Exec.SP

open NockvmE2E.Exec NockvmE2E.Exec.VL

/-- `K' = K[sqrt 7]` (nock's `Quad δ`, `δ = 7`): `i^2 = 7 + 0 i`. -/
abbrev Q : Type := QuadraticAlgebra KC 7 0

/-- nock's `Quad.mk _ a b`. -/
noncomputable def qmk (a b : KC) : Q := ⟨a, b⟩

/-- inverse by conjugate over norm (`0⁻¹ = 0`); equals the field inverse of nock's `Quad δ` (δ = 7 nonsquare). -/
noncomputable def qinv (x : Q) : Q :=
  ⟨x.re * (x.re * x.re - 7 * (x.im * x.im))⁻¹, -(x.im * (x.re * x.re - 7 * (x.im * x.im))⁻¹)⟩

/-- nock's `FiniteIO.compress ⟨γ, ρ⟩ v = ρ + Walk.rlc γ v`, `rlc γ v = Σ_c γ^c v_c`. -/
noncomputable def compressQ {m : ℕ} (γ ρ : Q) (v : Fin m → Q) : Q :=
  ρ + ∑ c : Fin m, γ ^ (c : ℕ) * v c

/-! ## Executable `K6` into `Q` -/

def canon6 (a : PE.K6) : Prop := canon3 a.re ∧ canon3 a.im

noncomputable def toQ6 (a : PE.K6) : Q := ⟨toKV a.re, toKV a.im⟩

theorem psiV_seven : psiV VF.seven = 7 := by
  unfold psiV; rw [zv_seven]; exact map_ofNat _ 7

theorem toKV_smul7 (x : VF.K3) : toKV (VF.K3.smul VF.seven x) = 7 * toKV x := by
  rw [toKV_smul, psiV_seven]

theorem canon6_add (a b : PE.K6) (ha : canon6 a) (hb : canon6 b) : canon6 (PE.K6.add a b) :=
  ⟨canon3_add _ _ ha.1 hb.1, canon3_add _ _ ha.2 hb.2⟩

theorem toQ6_add (a b : PE.K6) (ha : canon6 a) (hb : canon6 b) :
    toQ6 (PE.K6.add a b) = toQ6 a + toQ6 b := by
  ext
  · simp [toQ6, PE.K6.add, toKV_add _ _ ha.1 hb.1]
  · simp [toQ6, PE.K6.add, toKV_add _ _ ha.2 hb.2]

theorem canon6_mul (a b : PE.K6) : canon6 (PE.K6.mul a b) :=
  ⟨canon3_add _ _ (canon3_mul _ _) (canon3_smul _ _), canon3_add _ _ (canon3_mul _ _) (canon3_mul _ _)⟩

theorem toQ6_mul (a b : PE.K6) : toQ6 (PE.K6.mul a b) = toQ6 a * toQ6 b := by
  ext
  · simp [toQ6, PE.K6.mul, toKV_add _ _ (canon3_mul _ _) (canon3_smul _ _), toKV_mul, toKV_smul7]
    ring
  · simp [toQ6, PE.K6.mul, toKV_add _ _ (canon3_mul _ _) (canon3_mul _ _), toKV_mul]

theorem canon6_zero : canon6 PE.K6.zero := ⟨canon3_zero, canon3_zero⟩
theorem canon6_one : canon6 PE.K6.one := ⟨canon3_one, canon3_zero⟩
theorem canon6_base (x : UInt64) (h : canon x) : canon6 (PE.K6.base x) := ⟨canon3_ofG _ h, canon3_zero⟩

theorem toQ6_zero : toQ6 PE.K6.zero = 0 := by
  ext <;> simp [toQ6, PE.K6.zero, toKV_zero]
theorem toQ6_one : toQ6 PE.K6.one = 1 := by
  ext <;> simp [toQ6, PE.K6.one, toKV_one, toKV_zero]

theorem canon6_inv0 (a : PE.K6) : canon6 (PE.K6.inv0 a) :=
  ⟨canon3_mul _ _, canon3_neg _ (canon3_mul _ _)⟩

theorem toQ6_inv0 (a : PE.K6) : toQ6 (PE.K6.inv0 a) = qinv (toQ6 a) := by
  have hn : canon3 (VF.K3.sub (VF.K3.mul a.re a.re) (VF.K3.smul VF.seven (VF.K3.mul a.im a.im))) :=
    canon3_sub _ _ (canon3_mul _ _) (canon3_smul _ _)
  have hk : toKV (VF.K3.inv (VF.K3.sub (VF.K3.mul a.re a.re) (VF.K3.smul VF.seven (VF.K3.mul a.im a.im)))) =
      (toKV a.re * toKV a.re - 7 * (toKV a.im * toKV a.im))⁻¹ := by
    rw [toKV_inv, toKV_sub _ _ (canon3_mul _ _) (canon3_smul _ _), toKV_mul, toKV_smul7, toKV_mul]
  ext
  · simp [toQ6, PE.K6.inv0, qinv, toKV_mul, hk]
  · simp [toQ6, PE.K6.inv0, qinv, toKV_neg _ (canon3_mul _ _), toKV_mul, hk]

/-! ## `compress` -/

noncomputable def Tl (γ : Q) : List Q → Q
  | [] => 0
  | x :: xs => x + γ * Tl γ xs

/-- the `i`-th entry of an executable record (default `0`) as a `Fin m → Q` -/
noncomputable def recQ {m : ℕ} (l : List PE.K6) : Fin m → Q := fun c => toQ6 (l.getD c PE.K6.zero)

theorem Tl_eq (γ : Q) : ∀ l : List PE.K6,
    Tl γ (l.map toQ6) = ∑ c : Fin l.length, γ ^ (c : ℕ) * toQ6 (l.getD c PE.K6.zero)
  | [] => by simp [Tl]
  | x :: xs => by
      rw [List.map_cons, Tl, Tl_eq γ xs, List.length_cons, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]; ring

theorem compress_fold (g : PE.K6) (hg : canon6 g) (γ : Q) (hγ : γ = toQ6 g) :
    ∀ (l : List PE.K6), (∀ x ∈ l, canon6 x) → ∀ (a pw : PE.K6), canon6 a → canon6 pw →
      let r := l.foldl (fun (st : PE.K6 × PE.K6) x => (PE.K6.add st.1 (PE.K6.mul st.2 x), PE.K6.mul st.2 g)) (a, pw)
      canon6 r.1 ∧ toQ6 r.1 = toQ6 a + toQ6 pw * Tl γ (l.map toQ6)
  | [], _, a, pw, ha, hpw => by simp [Tl, ha]
  | x :: xs, hl, a, pw, ha, hpw => by
      have hx := hl x (by simp)
      have hxs : ∀ y ∈ xs, canon6 y := fun y hy => hl y (by simp [hy])
      have ih := compress_fold g hg γ hγ xs hxs (PE.K6.add a (PE.K6.mul pw x)) (PE.K6.mul pw g)
        (canon6_add _ _ ha (canon6_mul _ _)) (canon6_mul _ _)
      simp only [List.foldl_cons, List.map_cons, Tl]
      refine ⟨ih.1, ?_⟩
      rw [ih.2, toQ6_add _ _ ha (canon6_mul _ _), toQ6_mul, toQ6_mul, ← hγ]
      ring

theorem toQ6_compress {m : ℕ} (g rho : PE.K6) (l : List PE.K6) (hl : l.length = m) (hg : canon6 g)
    (hr : canon6 rho) (hv : ∀ x ∈ l, canon6 x) :
    canon6 (PE.compress g rho l) ∧
    toQ6 (PE.compress g rho l) = compressQ (toQ6 g) (toQ6 rho) (recQ l : Fin m → Q) := by
  have h := compress_fold g hg (toQ6 g) rfl l hv rho PE.K6.one hr canon6_one
  refine ⟨h.1, ?_⟩
  unfold PE.compress
  rw [h.2, toQ6_one, one_mul, Tl_eq]
  subst hl
  rfl

/-- a fold of `K6.add s (f r).inv0` -/
theorem foldl_invSum {α : Type} (f : α → PE.K6) (l : List α) : ∀ (a : PE.K6), canon6 a →
    canon6 (l.foldl (fun s r => PE.K6.add s (f r).inv0) a) ∧
    toQ6 (l.foldl (fun s r => PE.K6.add s (f r).inv0) a) = toQ6 a + (l.map fun r => qinv (toQ6 (f r))).sum := by
  induction l with
  | nil => intro a ha; simp [ha]
  | cons x xs ih =>
      intro a ha
      have h := ih (PE.K6.add a (f x).inv0) (canon6_add _ _ ha (canon6_inv0 _))
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      refine ⟨h.1, ?_⟩
      rw [h.2, toQ6_add _ _ ha (canon6_inv0 _), toQ6_inv0]
      ring


/-! ## Canonicity of the noun fingerprint and the records -/

theorem canon_ofNat (n : ℕ) (h : n < VF.PN) : canon (UInt64.ofNat n) := by
  unfold canon
  rw [UInt64.toNat_ofNat_of_lt' (by unfold VF.PN at h; rw [UInt64.size]; omega)]
  rw [p_lit]; exact h

theorem limbsAux_lt : ∀ (f n : ℕ), ∀ a ∈ PE.limbsAux f n, a < 4294967296
  | 0, _ => by simp [PE.limbsAux]
  | f + 1, n => by
      intro a ha
      unfold PE.limbsAux at ha
      split_ifs at ha with h
      · simp at ha
      · simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact Nat.mod_lt _ (by norm_num)
        · exact limbsAux_lt f _ a ha

theorem canon6_hornerL (y : PE.K6) (hy : canon6 y) : ∀ l : List ℕ, (∀ a ∈ l, a < 4294967296) →
    canon6 (PE.hornerL y l)
  | [], _ => canon6_zero
  | a :: l, h => by
      unfold PE.hornerL
      exact canon6_add _ _ (canon6_base _ (canon_ofNat a (by unfold VF.PN; have := h a (by simp); omega)))
        (canon6_mul _ _)

theorem canon6_leafE (y : PE.K6) (hy : canon6 y) (n : ℕ) : canon6 (PE.leafE y n) := by
  unfold PE.leafE
  split_ifs with h
  · exact canon6_base _ (canon_ofNat n h)
  · exact canon6_hornerL y hy _ (limbsAux_lt _ _)

def FpCan (e : PE.Fp3) : Prop := canon6 e.size ∧ canon6 e.dyck ∧ canon6 e.leaf

def StackCan (st : Option (List PE.Fp3)) : Prop := ∀ s, st = some s → ∀ e ∈ s, FpCan e

theorem encStep_can (z zinv y : PE.K6) (hz : canon6 z) (hzi : canon6 zinv) (hy : canon6 y)
    (st : Option (List PE.Fp3)) (t : PE.Tok) (h : StackCan st) : StackCan (PE.encStep z zinv y st t) := by
  intro s hs e he
  unfold PE.encStep at hs
  match st, t, hs with
  | none, _, hs => simp at hs
  | some s0, .atom n, hs =>
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨hz, canon6_zero, canon6_leafE y hy n⟩
      · exact h s0 rfl e he
  | some (a :: b :: s0), .cell, hs =>
      simp only [Option.some.injEq] at hs
      subst hs
      have ha := h (a :: b :: s0) rfl a (by simp)
      have hb := h (a :: b :: s0) rfl b (by simp)
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨canon6_mul _ _, canon6_add _ _ (canon6_add _ _ (canon6_mul _ _) (canon6_mul _ _)) (canon6_mul _ _),
          canon6_add _ _ ha.2.2 (canon6_mul _ _)⟩
      · exact h (a :: b :: s0) rfl e (by simp [he])
  | some [], .cell, hs => simp at hs
  | some [_], .cell, hs => simp at hs

theorem foldl_encStep_can (z zinv y : PE.K6) (hz : canon6 z) (hzi : canon6 zinv) (hy : canon6 y) :
    ∀ (l : List PE.Tok) (st : Option (List PE.Fp3)), StackCan st → StackCan (l.foldl (PE.encStep z zinv y) st)
  | [], st, h => h
  | t :: l, st, h => foldl_encStep_can z zinv y hz hzi hy l _ (encStep_can z zinv y hz hzi hy st t h)

theorem enc_can (z y : PE.K6) (hz : canon6 z) (hy : canon6 y) (toks : List PE.Tok) (e : PE.Fp3)
    (h : PE.enc z y toks = some e) : FpCan e := by
  unfold PE.enc at h
  have hs := foldl_encStep_can z z.inv0 y hz (canon6_inv0 z) hy toks.reverse (some [])
    (by intro s hs e he; simp at hs; subst hs; simp at he)
  revert h
  generalize toks.reverse.foldl (PE.encStep z z.inv0 y) (some []) = r at hs
  intro h
  rcases r with _ | _ | ⟨e', _ | ⟨e2, l⟩⟩
  · simp at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact hs _ rfl _ (by simp)
  · simp at h

theorem canon6_claimVec (e : PE.Fp3) (he : FpCan e) (idx hi lo : ℕ) (hidx : idx < VF.PN) (hhi : hi < VF.PN)
    (hlo : lo < VF.PN) : ∀ x ∈ PE.claimVec e idx hi lo, canon6 x := by
  intro x hx
  simp only [PE.claimVec, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact he.1
  · exact he.2.1
  · exact he.2.2
  · exact ⟨canon3_ofG _ (canon_ofNat lo hlo), canon3_ofG _ (canon_ofNat hi hhi)⟩
  · exact canon6_base _ (canon_ofNat idx hidx)


/-! ## Slices, `kv`, `pp` -/

/-- the `i`-th `K`-value (3 limbs) of a public slice, in `KC` (the body of `PE.kv`, read through `toKV`) -/
noncomputable def pubK (f : Array UInt64) (i : ℕ) : KC := toKV ⟨f[3 * i]!, f[3 * i + 1]!, f[3 * i + 2]!⟩

def ArrCan (f : Array UInt64) : Prop := ∀ j : ℕ, canon f[j]!

theorem kv_some (f : Array UInt64) (hf : ArrCan f) (i : ℕ) (x : VF.K3) (h : PE.kv f i = some x) :
    canon3 x ∧ toKV x = pubK f i := by
  unfold PE.kv at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨⟨hf _, hf _, hf _⟩, rfl⟩

theorem pp_some (f : Array UInt64) (hf : ArrCan f) (i : ℕ) (r : PE.K6) (h : PE.pp f i = some r) :
    canon6 r ∧ toQ6 r = qmk (pubK f i) (pubK f (i + 1)) := by
  unfold PE.pp at h
  rcases hk : PE.kv f i with _ | a
  · simp [hk] at h
  rcases hk2 : PE.kv f (i + 1) with _ | b
  · simp [hk, hk2] at h
  simp only [hk, hk2, bind, Option.bind, pure, Option.some.injEq] at h
  subst h
  have h1 := kv_some f hf _ _ hk
  have h2 := kv_some f hf _ _ hk2
  exact ⟨⟨h1.1, h2.1⟩, by simp [toQ6, qmk, h1.2, h2.2]⟩

theorem beq_K3 {a b : VF.K3} (h : (a == b) = true) : a = b := (K3_beq_iff a b).mp h

theorem beq_K6 {a b : PE.K6} (h : (a == b) = true) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  change (a1 == b1 && a2 == b2) = true at h
  rw [Bool.and_eq_true] at h
  rw [beq_K3 h.1, beq_K3 h.2]


/-! ## The J-8 public relation `PubJ8Rel`

Quotes nockvm `the nockvm library-cand/Nock/V1J8/Static.lean:236` `PubEqJ8 δ b Pb c χ M` (eight conjuncts, in order), with
`δ = 7`, `K = KC`, `𝕂′ = Q`, `Quad.mk _ a b = qmk a b`, `M.ρ/pubsC/pubsW/pubsJ/pubsA/pubsV` the arguments of the same name
(`pubsW` = walkJ8 table, `pubsJ` = jet, `pubsC` = cell, `pubsA` = atom, `pubsV` = walkAtom), and the three non-field parts
abstracted as data:
 * `pinConsR`   = `(pinCons Pb.regs Pb.idx).map liftRec`,
 * `claimRecs`  = `claimRecsJ8 δ χ c M.m`,  `pinRecs` = `pinRecsJ8 δ Pb χ`.
The compress coins of conjunct 3 are `coinsCV b δ (chalVJ8 b χ) = ⟨(χ11,χ15), (χ12,χ16)⟩` (`PubExe.lean` `γHE/ρHE`, nock's
`checkPubJ8E_iff` `hcv`), unfolded here; those of conjunct 4 are written as in `PubEqJ8` (`⟨(χ4,χ6),(χ5,χ7)⟩`).
Numerals: `WalkHQ.pubXQ = 4`, `WalkHQ.pubPQ = 6`, `CellHQ.pubHQ = 4`, `AtomChipHQ.pubMI = 8`, `pubMB = 6`, `pubC = 10`
(as in nock's `checkPubJ8E`, mirrored by `PE.pubXQ` ...). -/

noncomputable def PubJ8Rel (χ : Fin 19 → KC) (ρ : Fin 5 → Q) (ρS : Q) (pubsC pubsW pubsJ pubsA pubsV : ℕ → KC)
    (pinConsR : List (Fin 8 → Q)) (claimRecs pinRecs : List (Fin 5 → Q)) : Prop :=
  (ρ 3 + (qmk (pubsW 4) (pubsW (4 + 1)) + qmk (pubsJ 2) (pubsJ 3)) = qmk (pubsC 4) (pubsC (4 + 1))) ∧
  (ρ 4 = qmk (pubsW 6) (pubsW (6 + 1))) ∧
  (ρS + (pinConsR.map fun r => qinv (compressQ (qmk (χ 11) (χ 15)) (qmk (χ 12) (χ 16)) r)).sum
      + qmk (pubsJ 0) (pubsJ 1) = qmk (pubsA 8) (pubsA (8 + 1)) + qmk (pubsV 6) (pubsV (6 + 1))) ∧
  (((claimRecs ++ pinRecs).map fun r => qinv (compressQ (m := 5) (qmk (χ 4) (χ 6)) (qmk (χ 5) (χ 7)) r)).sum =
    qmk (pubsC 0) (pubsC 1) + qmk (pubsA 6) (pubsA (6 + 1))) ∧
  (qmk (pubsA 4) (pubsA (4 + 1)) = qmk (pubsA 10) (pubsA (10 + 1)) + qmk (pubsV 4) (pubsV (4 + 1))) ∧
  (pubsA 0 = 0 ∧ pubsA 1 = 0) ∧
  (pubsC 2 = pubsW 0 ∧ pubsC 3 = pubsW 1) ∧
  (pubsA 2 = pubsV 0 ∧ pubsA 3 = pubsV 1)

/-- the compute publics `ρ 3 = (K-value 5, K-value 7)`, `ρ 4 = (6, 8)` (indices of `ρ` other than 3, 4 are unconstrained: `0`) -/
noncomputable def rhoOf (x : Array UInt64) : Fin 5 → Q := fun i =>
  if (i : ℕ) = 3 then qmk (pubK x 5) (pubK x 7) else if (i : ℕ) = 4 then qmk (pubK x 6) (pubK x 8) else 0

/-- `ρS = (K-value 9, K-value 10)` -/
noncomputable def rhoSOf (x : Array UInt64) : Q := qmk (pubK x 9) (pubK x 10)

/-! ## Records -/

section Rec
open PE

def labelOf (x : Array UInt64) (j : Nat) : Nat := x[j]!.toNat

def claimRecS (z y : K6) (x : Array UInt64) (c : NounRec) : Option (List K6) := do
  let big := match c.noun with
    | [.atom n] => decide (n ≥ VF.PN)
    | _ => false
  let kind := if big then 2 else 1
  if c.key > 2 || labelOf x (2 * c.key) != kind then none else
  let e ← enc z y c.noun
  pure (claimVec e (labelOf x (2 * c.key + 1)) (if big then 0 else c.hi) (if big then 0 else c.lo))

def pinRecS (z y : K6) (q : NounRec) : Option (List K6) := do
  let e ← enc z y q.noun
  pure (claimVec e q.idx q.hi q.lo)

theorem mapM_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
      rw [List.mapM_cons] at h
      rcases hf : f a with _ | b0
      · simp [hf] at h
      rcases hl : l.mapM f with _ | r0
      · simp [hf, hl] at h
      simp only [hf, hl, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, by simp, hf⟩
      · obtain ⟨a', ha', h'⟩ := mapM_mem f l r0 hl b hb
        exact ⟨a', by simp [ha'], h'⟩

theorem claimRecS_can (z y : K6) (x : Array UInt64) (hz : canon6 z) (hy : canon6 y) (hx : ArrCan x)
    (c : NounRec) (hhi : c.hi < VF.PN) (hlo : c.lo < VF.PN) (r : List K6) (h : claimRecS z y x c = some r) :
    r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
  unfold claimRecS at h
  simp only [] at h
  generalize (match c.noun with | [Tok.atom n] => decide (n ≥ VF.PN) | _ => false) = big at h
  by_cases hc : (decide (c.key > 2) || labelOf x (2 * c.key) != (if big = true then 2 else 1)) = true
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h
  rcases he : enc z y c.noun with _ | e
  · simp [he] at h
  simp only [he, bind, Option.bind, pure, Option.some.injEq] at h
  subst h
  have hlab : ∀ j, labelOf x j < VF.PN := by
    intro j
    have := hx j
    unfold canon at this
    unfold labelOf VF.PN; rw [p_lit] at this; exact this
  refine ⟨rfl, canon6_claimVec e (enc_can z y hz hy _ e he) _ _ _ (hlab _) ?_ ?_⟩
  · cases big
    · exact hhi
    · simp only [if_true]; unfold VF.PN; omega
  · cases big
    · exact hlo
    · simp only [if_true]; unfold VF.PN; omega

theorem pinRecS_can (z y : K6) (hz : canon6 z) (hy : canon6 y) (q : NounRec) (hi : q.idx < VF.PN)
    (hhi : q.hi < VF.PN) (hlo : q.lo < VF.PN) (r : List K6) (h : pinRecS z y q = some r) :
    r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
  unfold pinRecS at h
  rcases he : enc z y q.noun with _ | e
  · simp [he] at h
  simp only [he, bind, Option.bind, pure, Option.some.injEq] at h
  subst h
  exact ⟨rfl, canon6_claimVec e (enc_can z y hz hy _ e he) _ _ _ hi hhi hlo⟩

theorem pinConsKey_can (id idx : ℕ) (hid : id < VF.PN) (hidx : idx < VF.PN) :
    (PE.pinConsKey id idx).length = 8 ∧ ∀ w ∈ PE.pinConsKey id idx, canon6 w := by
  refine ⟨rfl, ?_⟩
  intro w hw
  simp only [PE.pinConsKey, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  refine canon6_base _ (canon_ofNat v ?_)
  unfold VF.PN
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | exact hid | exact hidx

/-- instance data are `< p` -/
def InpCan (inp : PubIn) : Prop :=
  (∀ c ∈ inp.claimCells, c.hi < VF.PN ∧ c.lo < VF.PN) ∧
  (∀ q ∈ inp.pins, q.key < VF.PN ∧ q.idx < VF.PN ∧ q.hi < VF.PN ∧ q.lo < VF.PN)

end Rec

/-! ## `computeDerivedOk` sound: the derived compute publics -/

/-- `Σ_q γ^q psi(x[q])` over an index list, in the recursive (Horner-like) form of the executable fold -/
noncomputable def Tx (x : Array UInt64) (γ : KC) : List ℕ → KC
  | [] => 0
  | q :: qs => psiV x[q]! + γ * Tx x γ qs

theorem seed_fold (x : Array UInt64) (g : VF.K3) (hg : canon3 g) :
    ∀ (l : List ℕ), (∀ q ∈ l, canon x[q]!) → ∀ (a pw : VF.K3), canon3 a → canon3 pw →
      canon3 (l.foldl (fun (st : VF.K3 × VF.K3) q => (VF.K3.add st.1 (VF.K3.mul st.2 (VF.K3.ofG x[q]!)), VF.K3.mul st.2 g)) (a, pw)).1 ∧
      toKV (l.foldl (fun (st : VF.K3 × VF.K3) q => (VF.K3.add st.1 (VF.K3.mul st.2 (VF.K3.ofG x[q]!)), VF.K3.mul st.2 g)) (a, pw)).1
        = toKV a + toKV pw * Tx x (toKV g) l
  | [], _, a, pw, ha, _ => by simp [Tx, ha]
  | q :: qs, hl, a, pw, ha, hpw => by
      have hq : canon x[q]! := hl q (by simp)
      have hqs : ∀ y ∈ qs, canon x[y]! := fun y hy => hl y (by simp [hy])
      have hm : canon3 (VF.K3.mul pw (VF.K3.ofG x[q]!)) := canon3_mul _ _
      have ih := seed_fold x g hg qs hqs (VF.K3.add a (VF.K3.mul pw (VF.K3.ofG x[q]!))) (VF.K3.mul pw g)
        (canon3_add _ _ ha hm) (canon3_mul _ _)
      simp only [List.foldl_cons]
      refine ⟨ih.1, ?_⟩
      rw [ih.2, toKV_add _ _ ha hm, toKV_mul, toKV_mul, toKV_ofG]
      simp only [Tx]
      ring

/-- **`ComputeDerivedP`** (the proved form of `PE.computeDerivedOk` = Rust `check_compute_derived` = nock `pubVJ8E`): the 33 compute publics `x` carry
the coin-derived values: `x[6..8] = αW` (frame coin 13), `x[9..11] = αW · Σ_{q<6} γW^q · label_q` (`γW` = coin 14, `label_q = x[q]`), the pad `x[12..14] = 0`,
`x.size = 33`, and the plain-atom claim positions `(k, v)` read `x[2k] = 0`, `x[2k+1] = v`. Equalities of K-values are stated in `KC` (`toKV`). -/
def ComputeDerivedP (inp : PE.PubIn) (coins : Array VF.K3) (x : Array UInt64) : Prop :=
  x.size = 33 ∧
  toKV (VF.K3.mk x[6]! x[7]! x[8]!) = toKV coins[13]! ∧
  toKV (VF.K3.mk x[9]! x[10]! x[11]!) = toKV coins[13]! * ∑ q : Fin 6, toKV coins[14]! ^ (q : ℕ) * psiV x[(q : ℕ)]! ∧
  x[12]! = 0 ∧ x[13]! = 0 ∧ x[14]! = 0 ∧
  ∀ a ∈ inp.atoms, a.1 < 3 ∧ x[2 * a.1]! = 0 ∧ x[2 * a.1 + 1]! = UInt64.ofNat a.2

theorem computeDerivedOk_sound (inp : PE.PubIn) (coins : Array VF.K3) (x : Array UInt64)
    (hc : ∀ i : ℕ, canon3 coins[i]!) (hx : ArrCan x) (h : PE.computeDerivedOk inp coins x = true) :
    ComputeDerivedP inp coins x := by
  unfold PE.computeDerivedOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hsz, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := h
  have e1' := beq_K3 e1
  have e2' := beq_K3 e2
  refine ⟨hsz, by rw [e1'], ?_, e3, e4, e5, ?_⟩
  · rw [e2']
    have hf := seed_fold x coins[14]! (hc 14) (List.range 6) (by intro q _; exact hx q) VF.K3.zero VF.K3.one canon3_zero canon3_one
    rw [toKV_mul, hf.2, toKV_zero, toKV_one, zero_add, one_mul]
    have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide
    rw [hr, Fin.sum_univ_six]
    simp only [Tx, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    simp only [show ((3 : Fin 6) : ℕ) = 3 from rfl, show ((4 : Fin 6) : ℕ) = 4 from rfl, show ((5 : Fin 6) : ℕ) = 5 from rfl]
    ring
  · intro a ha
    have := List.all_eq_true.mp e6 a ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

/-! ## `checkPubEq` sound -/

section Main
open PE

theorem getD_true {o : Option Bool} (h : o.getD false = true) : o = some true := by
  cases o with
  | none => simp at h
  | some b => simpa using h

theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β} (h : o >>= f = some b) :
    ∃ a, o = some a ∧ f a = some b := Option.bind_eq_some_iff.mp h

theorem isZero_toKV (a : VF.K3) (h : a.isZero = true) : toKV a = 0 := by
  obtain ⟨c0, c1, c2⟩ := a
  simp only [VF.K3.isZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  subst h0 h1 h2
  exact toKV_zero

theorem checkPubEq_sound (inp : PubIn) (coins : Array VF.K3) (ps : PubSet)
    (hc : ∀ i : ℕ, canon3 coins[i]!)
    (h0 : ArrCan ps.compute) (h1 : ArrCan ps.cell) (h2 : ArrCan ps.walkJ8) (h3 : ArrCan ps.jet)
    (h4 : ArrCan ps.atom) (h5 : ArrCan ps.walkAtom) (hinp : InpCan inp)
    (h : checkPubEq inp coins ps = true) :
    (∃ cr pr : List (List K6),
      inp.claimCells.mapM (claimRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩ ps.compute) = some cr ∧
      inp.pins.mapM (pinRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some pr ∧
      PubJ8Rel (fun i : Fin 19 => toKV coins[(i : ℕ)]!) (rhoOf ps.compute) (rhoSOf ps.compute) (pubK ps.cell)
        (pubK ps.walkJ8) (pubK ps.jet) (pubK ps.atom) (pubK ps.walkAtom)
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))) ∧
      ComputeDerivedP inp coins ps.compute := by
  unfold checkPubEq at h
  simp only [] at h
  split at h
  · simp at h
  have h := getD_true h
  obtain ⟨cr, hcr, h⟩ := bind_some h
  obtain ⟨pr, hpr, h⟩ := bind_some h
  obtain ⟨w0, hw0, h⟩ := bind_some h
  obtain ⟨j2, hj2, h⟩ := bind_some h
  obtain ⟨ch, hch, h⟩ := bind_some h
  obtain ⟨w1, hw1, h⟩ := bind_some h
  obtain ⟨j0, hj0, h⟩ := bind_some h
  obtain ⟨aMI, haMI, h⟩ := bind_some h
  obtain ⟨v1, hv1, h⟩ := bind_some h
  obtain ⟨c0, hc0, h⟩ := bind_some h
  obtain ⟨aMB, haMB, h⟩ := bind_some h
  obtain ⟨aHQ, haHQ, h⟩ := bind_some h
  obtain ⟨aC, haC, h⟩ := bind_some h
  obtain ⟨v0, hv0, h⟩ := bind_some h
  obtain ⟨a0, ha0, h⟩ := bind_some h
  obtain ⟨a1, ha1, h⟩ := bind_some h
  obtain ⟨a2, ha2, h⟩ := bind_some h
  obtain ⟨a3, ha3, h⟩ := bind_some h
  obtain ⟨c2, hc2, h⟩ := bind_some h
  obtain ⟨c3, hc3, h⟩ := bind_some h
  obtain ⟨wk0, hwk0, h⟩ := bind_some h
  obtain ⟨wk1, hwk1, h⟩ := bind_some h
  obtain ⟨va0, hva0, h⟩ := bind_some h
  obtain ⟨va1, hva1, h⟩ := bind_some h
  have hfin := Option.some.inj h
  clear h
  simp only [Bool.and_eq_true] at hfin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩, e6a, e6b⟩, e7a, e7b⟩, e8a, e8b⟩ := hfin
  have hz : canon6 ⟨coins[2]!, coins[3]!⟩ := ⟨hc 2, hc 3⟩
  have hy : canon6 ⟨coins[17]!, coins[18]!⟩ := ⟨hc 17, hc 18⟩
  have hgh : canon6 ⟨coins[11]!, coins[15]!⟩ := ⟨hc 11, hc 15⟩
  have hrh : canon6 ⟨coins[12]!, coins[16]!⟩ := ⟨hc 12, hc 16⟩
  have hgv : canon6 ⟨coins[4]!, coins[6]!⟩ := ⟨hc 4, hc 6⟩
  have hrv : canon6 ⟨coins[5]!, coins[7]!⟩ := ⟨hc 5, hc 7⟩
  have hcr' : inp.claimCells.mapM (claimRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩ ps.compute) = some cr := hcr
  have hpr' : inp.pins.mapM (pinRecS ⟨coins[2]!, coins[3]!⟩ ⟨coins[17]!, coins[18]!⟩) = some pr := hpr
  have hcrc : ∀ r ∈ cr, r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
    intro r hr
    obtain ⟨c, hcm, hcc⟩ := mapM_mem _ _ _ hcr' r hr
    have := hinp.1 c hcm
    exact claimRecS_can _ _ _ hz hy h0 c this.1 this.2 r hcc
  have hprc : ∀ r ∈ pr, r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
    intro r hr
    obtain ⟨q, hqm, hqc⟩ := mapM_mem _ _ _ hpr' r hr
    have := hinp.2 q hqm
    exact pinRecS_can _ _ hz hy q this.2.1 this.2.2.1 this.2.2.2 r hqc
  refine ⟨⟨cr, pr, hcr', hpr', ?_⟩, computeDerivedOk_sound inp coins ps.compute hc h0 e0⟩
  have cr3 : canon6 (K6.mk (VF.K3.mk ps.compute[15]! ps.compute[15 + 1]! ps.compute[15 + 2]!)
      (VF.K3.mk ps.compute[21]! ps.compute[21 + 1]! ps.compute[21 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  obtain ⟨cw0, tw0⟩ := pp_some _ h2 _ _ hw0
  obtain ⟨cj2, tj2⟩ := pp_some _ h3 _ _ hj2
  obtain ⟨cch, tch⟩ := pp_some _ h1 _ _ hch
  have cr4 : canon6 (K6.mk (VF.K3.mk ps.compute[18]! ps.compute[18 + 1]! ps.compute[18 + 2]!)
      (VF.K3.mk ps.compute[24]! ps.compute[24 + 1]! ps.compute[24 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  have crS : canon6 (K6.mk (VF.K3.mk ps.compute[27]! ps.compute[27 + 1]! ps.compute[27 + 2]!)
      (VF.K3.mk ps.compute[30]! ps.compute[30 + 1]! ps.compute[30 + 2]!)) :=
    ⟨⟨h0 _, h0 _, h0 _⟩, ⟨h0 _, h0 _, h0 _⟩⟩
  have t3 : rhoOf ps.compute 3 = toQ6 (K6.mk (VF.K3.mk ps.compute[15]! ps.compute[15 + 1]! ps.compute[15 + 2]!)
      (VF.K3.mk ps.compute[21]! ps.compute[21 + 1]! ps.compute[21 + 2]!)) := by simp [rhoOf]; rfl
  have t4 : rhoOf ps.compute 4 = toQ6 (K6.mk (VF.K3.mk ps.compute[18]! ps.compute[18 + 1]! ps.compute[18 + 2]!)
      (VF.K3.mk ps.compute[24]! ps.compute[24 + 1]! ps.compute[24 + 2]!)) := by simp [rhoOf]; rfl
  have tS : rhoSOf ps.compute = toQ6 (K6.mk (VF.K3.mk ps.compute[27]! ps.compute[27 + 1]! ps.compute[27 + 2]!)
      (VF.K3.mk ps.compute[30]! ps.compute[30 + 1]! ps.compute[30 + 2]!)) := rfl
  obtain ⟨cw0, tw0⟩ := pp_some _ h2 _ _ hw0
  obtain ⟨cj2, tj2⟩ := pp_some _ h3 _ _ hj2
  obtain ⟨cch, tch⟩ := pp_some _ h1 _ _ hch
  obtain ⟨cw1, tw1⟩ := pp_some _ h2 _ _ hw1
  obtain ⟨cj0, tj0⟩ := pp_some _ h3 _ _ hj0
  obtain ⟨caMI, taMI⟩ := pp_some _ h4 _ _ haMI
  obtain ⟨cv1, tv1⟩ := pp_some _ h5 _ _ hv1
  obtain ⟨cc0, tc0⟩ := pp_some _ h1 _ _ hc0
  obtain ⟨caMB, taMB⟩ := pp_some _ h4 _ _ haMB
  obtain ⟨caHQ, taHQ⟩ := pp_some _ h4 _ _ haHQ
  obtain ⟨caC, taC⟩ := pp_some _ h4 _ _ haC
  obtain ⟨cv0, tv0⟩ := pp_some _ h5 _ _ hv0
  -- pin sum
  have hpin := foldl_invSum (fun q : NounRec => PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinConsKey q.key q.idx)) inp.pins K6.zero canon6_zero
  have hpinq : (inp.pins.map fun q => qinv (toQ6 (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
      (PE.pinConsKey q.key q.idx)))).sum =
      ((inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q)).map fun r =>
        qinv (compressQ (qmk (toKV coins[11]!) (toKV coins[15]!)) (qmk (toKV coins[12]!) (toKV coins[16]!)) r)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    have hk := hinp.2 q hq
    have hkc := pinConsKey_can q.key q.idx hk.1 hk.2.1
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hkc.1 hgh hrh hkc.2).2]
    rfl
  have hpinc : canon6 (inp.pins.foldl (fun s q => PE.K6.add s (PE.compress ⟨coins[11]!, coins[15]!⟩ ⟨coins[12]!, coins[16]!⟩
    (PE.pinConsKey q.key q.idx)).inv0) K6.zero) := hpin.1
  -- claim sum
  have hcl := foldl_invSum (fun r : List K6 => PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r)
    (cr ++ pr) K6.zero canon6_zero
  have hclq : ((cr ++ pr).map fun r => qinv (toQ6 (PE.compress ⟨coins[4]!, coins[6]!⟩ ⟨coins[5]!, coins[7]!⟩ r))).sum =
      (((cr.map fun r => (recQ r : Fin 5 → Q)) ++ (pr.map fun r => (recQ r : Fin 5 → Q))).map fun r =>
        qinv (compressQ (m := 5) (qmk (toKV coins[4]!) (toKV coins[6]!)) (qmk (toKV coins[5]!) (toKV coins[7]!)) r)).sum := by
    rw [← List.map_append, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    have hrc : r.length = 5 ∧ ∀ w ∈ r, canon6 w := by
      rcases List.mem_append.mp hr with hr | hr
      · exact hcrc r hr
      · exact hprc r hr
    simp only [Function.comp]
    rw [(toQ6_compress _ _ _ hrc.1 hgv hrv hrc.2).2]
    rfl
  obtain ⟨ca0, ta0⟩ := kv_some _ h4 _ _ ha0
  obtain ⟨ca1, ta1⟩ := kv_some _ h4 _ _ ha1
  obtain ⟨ca2, ta2⟩ := kv_some _ h4 _ _ ha2
  obtain ⟨ca3, ta3⟩ := kv_some _ h4 _ _ ha3
  obtain ⟨cc2, tc2⟩ := kv_some _ h1 _ _ hc2
  obtain ⟨cc3, tc3⟩ := kv_some _ h1 _ _ hc3
  obtain ⟨cwk0, twk0⟩ := kv_some _ h2 _ _ hwk0
  obtain ⟨cwk1, twk1⟩ := kv_some _ h2 _ _ hwk1
  obtain ⟨cva0, tva0⟩ := kv_some _ h5 _ _ hva0
  obtain ⟨cva1, tva1⟩ := kv_some _ h5 _ _ hva1
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have E := congrArg toQ6 (beq_K6 e1)
    rw [toQ6_add _ _ cr3 (canon6_add _ _ cw0 cj2), toQ6_add _ _ cw0 cj2, tw0, tj2, tch] at E
    rw [t3]; exact E
  · have E := congrArg toQ6 (beq_K6 e2)
    rw [tw1] at E
    rw [t4]; exact E
  · have E := congrArg toQ6 (beq_K6 e3)
    rw [toQ6_add _ _ (canon6_add _ _ crS hpinc) cj0, toQ6_add _ _ crS hpinc, toQ6_add _ _ caMI cv1, taMI, tv1, tj0,
      hpin.2, hpinq, toQ6_zero, zero_add] at E
    rw [tS]; exact E
  · have E := congrArg toQ6 (beq_K6 e4)
    rw [toQ6_add _ _ cc0 caMB, tc0, taMB, hcl.2, hclq, toQ6_zero, zero_add] at E
    exact E
  · have E := congrArg toQ6 (beq_K6 e5)
    rw [toQ6_add _ _ caC cv0, taHQ, taC, tv0] at E
    exact E
  · rw [← ta0]; exact isZero_toKV _ e6a
  · rw [← ta1]; exact isZero_toKV _ e6b
  · rw [← tc2, ← twk0, beq_K3 e7a]
  · rw [← tc3, ← twk1, beq_K3 e7b]
  · rw [← ta2, ← tva0, beq_K3 e8a]
  · rw [← ta3, ← tva1, beq_K3 e8b]
end Main

/-! ## `pubCheck` sound -/

theorem canon_getBang {α : Type} [Inhabited α] (P : α → Prop) (hd : P default) (f : Array α)
    (h : ∀ g ∈ f, P g) (i : ℕ) : P f[i]! := by
  by_cases hi : i < f.size
  · rw [getElem!_pos f i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg f i hi]; exact hd

theorem canon_default : canon (default : UInt64) := Gold.zero_lt
theorem canon3_default : canon3 (default : VF.K3) := ⟨Gold.zero_lt, Gold.zero_lt, Gold.zero_lt⟩

theorem ArrCan_of_mem (f : Array UInt64) (h : ∀ g ∈ f, canon g) : ArrCan f :=
  fun j => canon_getBang canon canon_default f h j

/-- the 19 frame coins as read by `pubCheck`: `slots[slotOf[i]]` -/
def coinsOf (slots : Array VF.K3) (slotOf : Array Nat) : Array VF.K3 :=
  (List.range 19).toArray.map fun i => slots[slotOf[i]!]!

/-- table `t`'s publics slice as read by `pubCheck` -/
def slOf (L : PE.PubLayout) (pub : Array UInt64) (t : Nat) : Array UInt64 :=
  if L.present[t]! then pub.extract L.bases[t]! (L.bases[t]! + L.lens[t]!) else Array.replicate L.lens[t]! 0

theorem coinsOf_get (slots : Array VF.K3) (slotOf : Array Nat) (i : ℕ) (hi : i < 19) :
    (coinsOf slots slotOf)[i]! = slots[slotOf[i]!]! := by
  unfold coinsOf
  have : i < ((List.range 19).toArray.map fun i => slots[slotOf[i]!]!).size := by simpa using hi
  rw [getElem!_pos _ i this]
  simp

theorem slOf_can (L : PE.PubLayout) (pub : Array UInt64) (hp : ∀ g ∈ pub, canon g) (t : Nat) :
    ArrCan (slOf L pub t) := by
  refine ArrCan_of_mem _ fun g hg => ?_
  unfold slOf at hg
  split_ifs at hg
  · obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.mp hg
    exact hp _ (Array.getElem_mem _)
  · rw [Array.mem_replicate] at hg
    rw [hg.2]; exact canon_default

/-- **`pubCheck_sound`.** -/
theorem pubCheck_sound (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3)
    (pub : Array UInt64) (hs : ∀ s ∈ slots, canon3 s) (hp : ∀ g ∈ pub, canon g) (hinp : InpCan inp)
    (h : PE.pubCheck inp L slotOf slots pub = true) :
    (∃ cr pr : List (List PE.K6),
      inp.claimCells.mapM (claimRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩ (slOf L pub 0)) = some cr ∧
      inp.pins.mapM (pinRecS ⟨(coinsOf slots slotOf)[2]!, (coinsOf slots slotOf)[3]!⟩
        ⟨(coinsOf slots slotOf)[17]!, (coinsOf slots slotOf)[18]!⟩) = some pr ∧
      PubJ8Rel (fun i : Fin 19 => toKV (coinsOf slots slotOf)[(i : ℕ)]!) (rhoOf (slOf L pub 0))
        (rhoSOf (slOf L pub 0)) (pubK (slOf L pub 1)) (pubK (slOf L pub 2)) (pubK (slOf L pub 3))
        (pubK (slOf L pub 4)) (pubK (slOf L pub 5))
        (inp.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q))) ∧
      ComputeDerivedP inp (coinsOf slots slotOf) (slOf L pub 0) := by
  have h' : PE.checkPubEq inp (coinsOf slots slotOf)
      ⟨slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5⟩ = true := by
    unfold PE.pubCheck at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  have hc : ∀ i : ℕ, canon3 (coinsOf slots slotOf)[i]! := by
    refine canon_getBang canon3 canon3_default _ ?_
    intro g hg
    unfold coinsOf at hg
    rw [Array.mem_map] at hg
    obtain ⟨i, _, rfl⟩ := hg
    exact canon_getBang canon3 canon3_default slots hs _
  have := checkPubEq_sound inp (coinsOf slots slotOf)
    ⟨slOf L pub 0, slOf L pub 1, slOf L pub 2, slOf L pub 3, slOf L pub 4, slOf L pub 5⟩ hc (slOf_can L pub hp 0) (slOf_can L pub hp 1) (slOf_can L pub hp 2)
    (slOf_can L pub hp 3) (slOf_can L pub hp 4) (slOf_can L pub hp 5) hinp h'
  exact this

/-! ## Non-vacuity: the real toy1 public vector -/

theorem toy1_check : PE.checkWith PE.toy1Claim PE.toy1Slots PE.toy1Pubs = true := by decide +kernel

theorem toy1_slots_can : ∀ s ∈ PE.toy1Slots, canon3 s := by
  intro s hs
  have : (PE.toy1Slots.all fun s => decide (s.c0.toNat < p ∧ s.c1.toNat < p ∧ s.c2.toNat < p)) = true := by
    decide +kernel
  rw [Array.all_eq_true] at this
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hs
  have h := this i hi
  simp only [decide_eq_true_eq] at h
  exact h

theorem toy1_pub_can : ∀ g ∈ PE.concatPubs PE.toy1Pubs, canon g := by
  intro g hg
  have : ((PE.concatPubs PE.toy1Pubs).all fun g => decide (g.toNat < p)) = true := by decide +kernel
  rw [Array.all_eq_true] at this
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hg
  have h := this i hi
  simp only [decide_eq_true_eq] at h
  exact h

theorem toy1_inp_can : InpCan PE.toy1Claim := by
  constructor
  · intro c hc
    simp only [PE.toy1Claim, List.mem_singleton] at hc
    subst hc
    unfold VF.PN; decide
  · intro q hq
    simp [PE.toy1Claim] at hq

/-- **non-vacuity**: `PubJ8Rel` holds on the real toy1 public vector, derived through `pubCheck_sound`. -/
theorem toy1_rel :
    ∃ cr pr : List (List PE.K6),
      PubJ8Rel (fun i : Fin 19 => toKV (coinsOf PE.toy1Slots PE.idSlots)[(i : ℕ)]!)
        (rhoOf (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 0))
        (rhoSOf (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 0))
        (pubK (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 1))
        (pubK (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 2))
        (pubK (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 3))
        (pubK (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 4))
        (pubK (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 5))
        (PE.toy1Claim.pins.map fun q => (recQ (PE.pinConsKey q.key q.idx) : Fin 8 → Q))
        (cr.map fun r => (recQ r : Fin 5 → Q)) (pr.map fun r => (recQ r : Fin 5 → Q)) := by
  obtain ⟨⟨cr, pr, -, -, h⟩, -⟩ := pubCheck_sound PE.toy1Claim (PE.layoutOf PE.toy1Pubs) PE.idSlots PE.toy1Slots
    (PE.concatPubs PE.toy1Pubs) toy1_slots_can toy1_pub_can toy1_inp_can toy1_check
  exact ⟨cr, pr, h⟩

/-- **non-vacuity**: `ComputeDerivedP` is satisfiable, and holds on the real toy1 compute publics (via `pubCheck_sound`). -/
theorem toy1_computeDerived :
    ComputeDerivedP PE.toy1Claim (coinsOf PE.toy1Slots PE.idSlots)
      (slOf (PE.layoutOf PE.toy1Pubs) (PE.concatPubs PE.toy1Pubs) 0) :=
  (pubCheck_sound PE.toy1Claim (PE.layoutOf PE.toy1Pubs) PE.idSlots PE.toy1Slots
    (PE.concatPubs PE.toy1Pubs) toy1_slots_can toy1_pub_can toy1_inp_can toy1_check).2

end SP

#print axioms NockvmE2E.Exec.SP.computeDerivedOk_sound
#print axioms NockvmE2E.Exec.SP.toy1_computeDerived
#print axioms NockvmE2E.Exec.SP.pubCheck_sound
#print axioms NockvmE2E.Exec.SP.toy1_rel
