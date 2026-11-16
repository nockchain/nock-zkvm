/-
  NockvmE2E/Exec/HSpecTree.lean   (HSpec, ; KERNEL-checked, Mathlib-free)

  The Merkle side of `HSpec`: the deployed tree builder `fxRagLevels` (`fxParRange`, `fxLevelsUp`, `fxSubRoot`) computes the spec tree
  `specTop`/`specSub` of VKSpecExe.lean, for ANY hash `Hf`, as soon as the LDE words agree with a word function `w`.
    * `fxParRange_get`        : `size = n`, `[i]! = f i`;
    * `fxLevelsUp_get`        : level `d` entry `i` is `specTop … (m - d) (2^d + i)`;
    * `fxSubRootF_eq_specSub` : the fuel version at fuel `cnt` equals `specSub` with the same fuel (j = 0), and any fuel `≥ cnt` agrees;
    * `fxRagLevels_root`      : the root.
  No axiom, no `sorry`.
-/
import NockvmE2E.Exec.VKSpecExe
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.J

theorem array_map_range_append {α : Type} (f : Nat → α) (a b : Nat) :
    (Array.range a).map f ++ (Array.range b).map (fun i => f (a + i)) = (Array.range (a + b)).map f := by
  apply Array.ext'
  simp [List.range_add, Array.toList_append, Array.toList_map, Array.toList_range, Function.comp_def]

/-- the chunk fold of `fxParRange`: after `c` more chunks the accumulator is `f` on `[0, min n ((c0+c)·chunk))` -/
theorem fxParRange_fold {α : Type} (n chunk : Nat) (f : Nat → α) (hc : 0 < chunk) :
    ∀ (k c : Nat), c + k ≤ (n + chunk - 1) / chunk →
      ((List.range' c k).map (fun ci => (Array.range (min chunk (n - ci * chunk))).map fun i => f (ci * chunk + i))).foldl
        (fun acc t => acc ++ t) ((Array.range (min n (c * chunk))).map f) =
      (Array.range (min n ((c + k) * chunk))).map f := by
  intro k
  induction k with
  | zero => intro c _; simp
  | succ k ih =>
    intro c hck
    have hlt : c * chunk < n := by
      have h1 : c + 1 ≤ (n + chunk - 1) / chunk := by omega
      have h2 := (Nat.le_div_iff_mul_le hc).mp h1
      have h3 : (c + 1) * chunk = c * chunk + chunk := Nat.succ_mul c chunk
      omega
    have hs : (c + 1) * chunk = c * chunk + chunk := Nat.succ_mul c chunk
    have hk : (c + 1) + k ≤ (n + chunk - 1) / chunk := by omega
    have e1 : min n (c * chunk) = c * chunk := by omega
    have e2 : c * chunk + min chunk (n - c * chunk) = min n ((c + 1) * chunk) := by omega
    simp only [List.range'_succ, List.map_cons, List.foldl_cons]
    rw [e1, array_map_range_append f (c * chunk) (min chunk (n - c * chunk)), e2]
    have := ih (c + 1) hk
    rw [show c + 1 + k = c + (k + 1) by omega] at this
    exact this

theorem fxParRange_eq {α : Type} [Inhabited α] (n chunk : Nat) (f : Nat → α) (hc : 0 < chunk) :
    fxParRange n chunk f = (Array.range n).map f := by
  have e : fxParRange n chunk f = Array.foldl (fun acc t => acc ++ t.get) #[]
      ((Array.range ((n + chunk - 1) / chunk)).map fun ci => Task.spawn fun _ =>
        (Array.range (min chunk (n - ci * chunk))).map fun i => f (ci * chunk + i)) := rfl
  have hg : ∀ (g : Unit → Array α), (Task.spawn g).get = g () := fun _ => rfl
  rw [e, ← Array.foldl_toList, Array.toList_map, Array.toList_range, List.foldl_map, List.range_eq_range']
  simp only [hg]
  have key := fxParRange_fold n chunk f hc ((n + chunk - 1) / chunk) 0 (by omega)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.min_zero] at key
  simp only [List.foldl_map] at key
  have h0 : (Array.range 0).map f = (#[] : Array α) := by simp
  rw [h0] at key
  have hge : n ≤ (n + chunk - 1) / chunk * chunk := by
    have h1 := Nat.div_add_mod (n + chunk - 1) chunk
    have h2 := Nat.mod_lt (n + chunk - 1) hc
    have h3 : chunk * ((n + chunk - 1) / chunk) = (n + chunk - 1) / chunk * chunk := Nat.mul_comm _ _
    omega
  rw [show min n ((n + chunk - 1) / chunk * chunk) = n by omega] at key
  exact key

theorem fxParRange_get {α : Type} [Inhabited α] (n chunk : Nat) (f : Nat → α) (hc : 0 < chunk) :
    (fxParRange n chunk f).size = n ∧ ∀ i < n, (fxParRange n chunk f)[i]! = f i := by
  rw [fxParRange_eq n chunk f hc]
  refine ⟨by simp, fun i hi => ?_⟩
  simp [getElem!_def, hi]

/-! ### `fxLevelsUp` -/

/-- one iteration of the `for t in [0:m]` loop of `fxLevelsUp` -/
def lvStep (H : HFn) (j m : Nat) (lv : Array (Array Dg5)) (t : Nat) : Array (Array Dg5) :=
  lv.set! (m - 1 - t) (fxParRange (2 ^ (m - 1 - t)) 256 fun i =>
    H ([tagNode, j, 2 ^ (m - 1 - t) + i] ++ (lv[m - 1 - t + 1]!)[2 * i]! ++ (lv[m - 1 - t + 1]!)[2 * i + 1]!))

theorem fxLevelsUp_eq (H : HFn) (j : Nat) (bot : Array Dg5) (m : Nat) :
    fxLevelsUp H j bot m = (List.range m).foldl (lvStep H j m) ((Array.replicate (m + 1) #[]).set! m bot) := by
  simp [fxLevelsUp, lvStep, Id.run, List.range_eq_range']
  rfl

theorem lvStep_inv (Hf : HFn) (grp : Nat → Dg5) (m : Nat) (bot : Array Dg5) (hbot : ∀ i < 2 ^ m, bot[i]! = grp i) :
    ∀ t, t ≤ m →
      ((List.range t).foldl (lvStep Hf 0 m) ((Array.replicate (m + 1) #[]).set! m bot)).size = m + 1 ∧
      ∀ d, m - t ≤ d → d ≤ m → ∀ i < 2 ^ d,
        (((List.range t).foldl (lvStep Hf 0 m) ((Array.replicate (m + 1) #[]).set! m bot))[d]!)[i]! =
          specTop Hf grp m (m - d) (2 ^ d + i) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp [Array.size_set!], fun d h1 h2 i hi => ?_⟩
    have hd : d = m := by omega
    subst hd
    simp only [List.range_zero, List.foldl_nil]
    rw [Array.getElem!_set!_self _ _ _ (by simp)]
    simp [specTop, hbot i hi]
  | succ t ih =>
    intro ht
    obtain ⟨hsz, hval⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range t).foldl (lvStep Hf 0 m) ((Array.replicate (m + 1) #[]).set! m bot) = lv at hsz hval
    refine ⟨by simp [lvStep, Array.size_set!, hsz], fun d h1 h2 i hi => ?_⟩
    by_cases hd : d = m - 1 - t
    · subst hd
      unfold lvStep
      rw [Array.getElem!_set!_self _ _ _ (by omega), (fxParRange_get _ 256 _ (by omega)).2 i hi]
      have e := hval (m - 1 - t + 1) (by omega) (by omega) (2 * i) (by rw [Nat.pow_succ]; omega)
      have e2 := hval (m - 1 - t + 1) (by omega) (by omega) (2 * i + 1) (by rw [Nat.pow_succ]; omega)
      have hm : m - (m - 1 - t) = (m - (m - 1 - t + 1)) + 1 := by omega
      rw [hm]
      simp only [specTop]
      rw [e, e2]
      have p1 : 2 ^ (m - 1 - t + 1) + 2 * i = 2 * (2 ^ (m - 1 - t) + i) := by rw [Nat.pow_succ]; omega
      have p2 : 2 ^ (m - 1 - t + 1) + (2 * i + 1) = 2 * (2 ^ (m - 1 - t) + i) + 1 := by rw [Nat.pow_succ]; omega
      rw [p1, p2]
    · unfold lvStep
      rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hd h.symm)]
      exact hval d (by omega) h2 i hi

theorem fxLevelsUp_get (Hf : HFn) (grp : Nat → Dg5) (m : Nat) (bot : Array Dg5) (hbot : ∀ i < 2 ^ m, bot[i]! = grp i) :
    ∀ d ≤ m, ∀ i < 2 ^ d, ((fxLevelsUp Hf 0 bot m)[d]!)[i]! = specTop Hf grp m (m - d) (2 ^ d + i) := by
  intro d hd i hi
  rw [fxLevelsUp_eq]
  exact (lvStep_inv Hf grp m bot hbot m (Nat.le_refl m)).2 d (by omega) hd i hi

/-! ### `fxSubRoot` and the root -/

/-- the deployed subtree root at tag 0 is `specSub` at fuel `cnt` (the two definitions are the same text) -/
theorem fxSubRootF_eq_specSub (H : HFn) (leafAt : Nat → G) :
    ∀ (f idx cnt lo : Nat), fxSubRootF H 0 leafAt f idx cnt lo = specSub H leafAt f idx cnt lo := by
  intro f
  induction f with
  | zero => intro idx cnt lo; simp [fxSubRootF, specSub]
  | succ f ih => intro idx cnt lo; simp only [fxSubRootF, specSub, ih]

theorem fxSubRoot_eq_specSub (H : HFn) (leafAt : Nat → G) (idx cnt lo : Nat) :
    fxSubRoot H 0 leafAt idx cnt lo = specSub H leafAt cnt idx cnt lo :=
  fxSubRootF_eq_specSub H leafAt cnt idx cnt lo

/-- `specSub` reads `leafAt` only on `[lo, lo + cnt)` -/
theorem specSub_congr (H : HFn) (l1 l2 : Nat → G) :
    ∀ (f idx cnt lo : Nat), (∀ r, lo ≤ r → r < lo + cnt → l1 r = l2 r) →
      specSub H l1 f idx cnt lo = specSub H l2 f idx cnt lo := by
  intro f
  induction f with
  | zero => intro idx cnt lo _; simp [specSub]
  | succ f ih =>
    intro idx cnt lo h
    simp only [specSub]
    by_cases hc : cnt == 1
    · have hc1 : cnt = 1 := by simpa using hc
      subst hc1
      simp [h lo (Nat.le_refl _) (by omega)]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hc1 : cnt ≠ 1 := by simpa using hc
      rw [ih (2 * idx) ((cnt + 1) / 2) lo (fun r h1 h2 => h r h1 (by omega)),
          ih (2 * idx + 1) (cnt - (cnt + 1) / 2) (lo + (cnt + 1) / 2) (fun r h1 h2 => h r (by omega) (by omega))]

/-- **the Merkle side of `HSpec`**: for any hash `Hf`, if the LDE words are `w` then the deployed tree's root is the spec tree's root.
`W` is the number of fixed columns (`cols.size`), the domain has `2^(m+1)` points, `half = 2^m`. -/
theorem fxRagLevels_root (Hf : HFn) (W m : Nat) (lde : Array (Array G)) (w : Nat → Nat → G)
    (hW : 1 ≤ W) (hl : ∀ r < W, ∀ i < 2 ^ (m + 1), (lde[r]!)[i]! = w r i) :
    (fxRagLevels Hf 0 W (2 ^ m) lde)[0]![0]! =
      specTop Hf (fun g => Hf ([tagNode, 0, 2 ^ m + g] ++ specSub Hf (fun r => w r g) W (2 * (2 ^ m + g)) W 0 ++
          specSub Hf (fun r => w r (g + 2 ^ m)) W (2 * (2 ^ m + g) + 1) W 0)) m m 1 := by
  have hlog : Nat.log2 (2 ^ m) = m := Nat.log2_two_pow
  have key := fxLevelsUp_get Hf
    (fun g => Hf ([tagNode, 0, 2 ^ m + g] ++ specSub Hf (fun r => w r g) W (2 * (2 ^ m + g)) W 0 ++
          specSub Hf (fun r => w r (g + 2 ^ m)) W (2 * (2 ^ m + g) + 1) W 0)) m
    (fxParRange (2 ^ m) 8 fun g =>
      let side (s : Nat) : Dg5 := fxSubRoot Hf 0 (fun r => (lde[r]!)[g + s * 2 ^ m]!) (2 * (2 ^ m + g) + s) W 0
      Hf ([tagNode, 0, 2 ^ m + g] ++ side 0 ++ side 1))
    (by
      intro g hg
      rw [(fxParRange_get _ 8 _ (by omega)).2 g hg]
      simp only [fxSubRoot_eq_specSub]
      have hg2 : g < 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      have hg3 : g + 1 * 2 ^ m < 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
      rw [specSub_congr Hf (fun r => (lde[r]!)[g + 0 * 2 ^ m]!) (fun r => w r g) W (2 * (2 ^ m + g) + 0) W 0
            (fun r _ h2 => by simpa using hl r (by omega) g hg2),
          specSub_congr Hf (fun r => (lde[r]!)[g + 1 * 2 ^ m]!) (fun r => w r (g + 2 ^ m)) W (2 * (2 ^ m + g) + 1) W 0
            (fun r _ h2 => by simpa using hl r (by omega) _ hg3)]
      rfl)
  have := key 0 (Nat.zero_le m) 0 (by simp)
  unfold fxRagLevels
  simp only [hlog]
  simpa using this

end NockvmE2E.Exec.V

open NockvmE2E.Exec.V in
#print axioms fxParRange_get
open NockvmE2E.Exec.V in
#print axioms fxLevelsUp_get
open NockvmE2E.Exec.V in
#print axioms fxSubRoot_eq_specSub
open NockvmE2E.Exec.V in
#print axioms fxRagLevels_root
