/-
  NockvmE2E/Exec/J8Shape.lean   (the J-8 shape of a loaded `ExecInst`)

  `j8ShapeOk : ExecInst → Bool` -- a total, Mathlib-free check that the loaded instance is the shape the prover writes for the J-8 relation
  (r = 2, d = 1, l = 170, hShift = 1, hN = 2^(k+1), nD = k + 7, pubMode = 0, no derived slots, 19 coins, the public point `ppt`, canonical chips without
  the `.chal 63` fallback, colKind/blockOf as `FlatProver` writes them, preprocessed columns of size ≤ hN + 1), and the soundness lemmas the
  audited side needs from it (`DomLink`, `hn32`, `hn1`, `hl`, `hmode`, `hpd`).
  `domLink_of_paramsOk` is `flatOk_dGen` (SoundClosed.lean:174) factored to `paramsOk XI = true` (the audited file is not edited).
  NOT wired into the verifier exe.
-/
import NockvmE2E.Exec.SoundClosed
import NockvmE2E.Exec.J8ShapeB
import NockvmE2E.Exec.HdagU

set_option autoImplicit false

namespace NockvmE2E.Exec.J8Shape
open NockvmE2E.Exec NockvmE2E.Exec.VL NockvmE2E.Exec.V NockvmE2E.Exec.Inst NockvmE2E.Exec.Tr

/-! ## `DomLink` from `paramsOk` (factored from `flatOk_dGen`) -/

theorem dShift_of_paramsOk (XI : ExecInst) (hp : paramsOk XI = true) : XI.dShift = 7 := by
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  exact hp.1.1.1.1.1

theorem nD_le_of_paramsOk (XI : ExecInst) (hp : paramsOk XI = true) : XI.nD ≤ 32 := by
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  exact hp.1.1.1.1.2

theorem dGen_of_paramsOk (XI : ExecInst) (hp : paramsOk XI = true) :
    psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC) := by
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hd : XI.dGen = dGenOf XI.nD := hp.2
  rw [hd, zeta_val, root_toZ]
  unfold dGenOf
  rw [psiV_pow, psiV_pow, show psiV VF.seven = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 from by
    unfold psiV; exact congrArg (algebraMap (ZMod NockvmE2E.Exec.p) KC) zv_seven]
  simp [gZ, map_pow]

/-- **`domLink_of_paramsOk`**: the verifier's `paramsOk` gives the audited `DomLink` (`dShift = 7`, `dGen = ζ_nD`) -/
theorem domLink_of_paramsOk (XI : ExecInst) (hp : paramsOk XI = true) (hn : XI.nD ≤ 32) : DomLink XI hn where
  dShift_eq := by
    rw [dShift_of_paramsOk XI hp]
    unfold psiV; exact congrArg (algebraMap (ZMod NockvmE2E.Exec.p) KC) zv_seven
  dGen_eq := dGen_of_paramsOk XI hp

/-! ## soundness lemmas of the shape -/

theorem paramsOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : paramsOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem tabsOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : tabsOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- `hn32` -/
theorem hn32_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.nD ≤ 32 := nD_le_of_paramsOk XI (paramsOk_of_shape h)

/-- `DomLink` -/
theorem domLink_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : DomLink XI (hn32_of_shape h) :=
  domLink_of_paramsOk XI (paramsOk_of_shape h) _

/-- `hn1` : `nD = k + 7 ≥ 7` -/
theorem hn1_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : 1 ≤ XI.nD := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  omega

/-- `hl` -/
theorem hl_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.l = 170 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `hmode` -/
theorem hmode_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.pubMode = 0 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `hd : d = XI.d` side: the final polynomial has exactly one coefficient -/
theorem d_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.d = 1 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `r = 2` (cur/next) -/
theorem r_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.r = 2 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- the union domain is a power of two: `hN = 2^(k+1)` (the shape) -/
theorem hN_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.hN = 2 ^ (XI.k + 1) := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `hpd`: every preprocessed column has degree `≤ hN` (coefficient array of size `≤ hN + 1`) -/
theorem hpd_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ c < XI.nc, XI.pre[c]!.size ≤ XI.hN + 1 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hs, hall, _⟩ := (by tauto : _ ∧ XI.pre.size = XI.nc ∧ (∀ i (hi : i < XI.pre.size), XI.pre[i].size ≤ XI.hN + 1) ∧ _)
  intro c hc
  have hc' : c < XI.pre.size := by omega
  rw [getElem!_pos XI.pre c hc']
  exact hall c hc'

theorem tabs_all_mem {XI : ExecInst} {f : TabInst → Bool} (h : XI.tabs.all f = true) : ∀ t ∈ XI.tabs.toList, f t = true := by
  intro t ht
  exact Array.all_eq_true_iff_forall_mem.mp h t (Array.mem_def.mpr ht)

/-- no chip of a shaped instance reaches the `.chal 63` fallback -/
theorem chips_no63_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs, chipNo63 t.chip = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) = true) t (Array.mem_def.mp ht)
  exact ((Bool.and_eq_true _ _).mp this).2

/-- `nCoins` sums to 19 -/
theorem coins19_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.nCoins[0]! + XI.nCoins[1]! = 19 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem derived_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.derived = #[] := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  have h1 : XI.derived.isEmpty = true := by tauto
  exact Array.isEmpty_iff.mp h1

/-! ## the trace-domain orbit, widths, coin-slot permutation -/

theorem orbitOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : orbitOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem widthOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : widthOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem slotOfOk_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : slotOfOk XI = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- `widthOk` per table: `nc - npub = wJ8 id` -/
theorem width_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, t.nc - t.npub = wJ8 t.chip.id := by
  intro t ht
  have := tabs_all_mem (by have := widthOk_of_shape h; unfold widthOk at this; exact this) t ht
  simpa using this

theorem slotOf_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : XI.slotOf = slotOfJ8 ∧ XI.nCoins = #[13, 6] := by
  have := slotOfOk_of_shape h
  unfold slotOfOk at this
  simpa using this

theorem zv_inj_canon {a b : UInt64} (ha : canon a) (hb : canon b) (h : zv a = zv b) : a = b := by
  unfold zv at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  unfold canon at ha hb
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact UInt64.toNat_inj.mp h

/-- **`orbit_order_of_shape`**: the trace-domain generator has order exactly `3·2^(k+1)` (J-8's `StrictOrbitDomain _ 3 (k+1)`) -/
theorem orbit_order_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : orderOf (zv XI.hGen) = 3 * 2 ^ (XI.k + 1) := by
  have ho := orbitOk_of_shape h
  unfold orbitOk at ho
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ho
  obtain ⟨⟨h1, h2⟩, h3⟩ := ho
  have e1 : zv XI.hGen ^ (3 * 2 ^ (XI.k + 1)) = 1 := by rw [← zv_pow, h1]; rfl
  have e2 : zv XI.hGen ^ (2 ^ (XI.k + 1)) ≠ 1 := by
    intro e; apply h2; rw [← zv_pow] at e
    exact zv_inj_canon (Inst.canon_pow _ _) Gold.one_lt e
  have e3 : zv XI.hGen ^ (3 * 2 ^ XI.k) ≠ 1 := by
    intro e; apply h3; rw [← zv_pow] at e
    exact zv_inj_canon (Inst.canon_pow _ _) Gold.one_lt e
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity) e1
  intro q hq hdvd
  have hq2 : q = 2 ∨ q = 3 := by
    have hd : q ∣ 3 * 2 ^ (XI.k + 1) := hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  rcases hq2 with rfl | rfl
  · have : 3 * 2 ^ (XI.k + 1) / 2 = 3 * 2 ^ XI.k := by rw [pow_succ]; omega
    rw [this]; exact e3
  · have : 3 * 2 ^ (XI.k + 1) / 3 = 2 ^ (XI.k + 1) := by omega
    rw [this]; exact e2

/-! ## non-vacuity: a concrete J-8-shaped instance

`k = 1`, `hN = 4` (the union domain), `nD = 8`; one table with `n_t = 3` rows (NOT a power of two: `H_t` is the first 3 points of the padded orbit), one trace
column, one public column, three quotient columns. -/

def toyChip : Tr.Chip :=
  { id := "toy", shared := #[.var 0 0, .mul (.ref 0) (.ref 0)], cons := #[{ kind := 0, round := 0, deg := 2, e := .ref 1 }],
    colRound := #[0], sharedK := #[false, false], consK := #[false], baseCols := 1, width := 1 }

def toyShape : ExecInst :=
  { nD := 8, dShift := 7, dGen := dGenOf 8, hN := 4, hGen := 281474976710656, hShift := 1, r := 2, k := 1, d := 1, l := 170,
    nc := 2, nq := 3, colKind := #[0, 2], blockOf := #[0, 2, 3, 3, 3], pre := #[#[], #[]], pubOf := #[1], ppt := pptJ8,
    nCoins := #[10, 9], derived := #[],
    tabs := #[{ hN := 3, col0 := 0, nc := 2, npub := 1, pubBase := 0, chip := toyChip }] }

/-- the toy chips of the four mandatory tables now carry the real J-8 widths (`widthOk`): trace columns `wJ8 id` (all in round 0), then one public column -/
def toyChipId (i : String) : Tr.Chip :=
  { toyChip with id := i, colRound := Array.replicate (wJ8 i) 0, width := wJ8 i, baseCols := wJ8 i, sharedK := #[false, false], consK := #[false] }

/-- columns: compute 124 @0, cell 243 @124, walkJ8 167 @367, atom 350 @534; total 884 -/
def toyShape4 : ExecInst :=
  { toyShape with
    hGen := 18446744069414518785,  -- 2^112 mod p: exact order 12 = 3·2^(k+1) at k = 1
    nc := 884, nCoins := #[13, 6], slotOf := slotOfJ8,
    -- literal arrays (generated): kernel evaluation of `++`/`map`/`replicate` terms re-reduces on every index and does not finish
    colKind := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    blockOf := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3],
    pre := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]],
    pubOf := #[123, 366, 533, 883],
    tabs := #[{ hN := 3, col0 := 0, nc := 124, npub := 1, pubBase := 0, chip := toyChipId "computeChipVCLHX" },
              { hN := 3, col0 := 124, nc := 243, npub := 1, pubBase := 1, chip := toyChipId "cellChipHQKW" },
              { hN := 3, col0 := 367, nc := 167, npub := 1, pubBase := 2, chip := toyChipId "walkChipJ8" },
              { hN := 3, col0 := 534, nc := 350, npub := 1, pubBase := 3, chip := toyChipId "atomChipHQL" }] }

-- the single `decide +kernel` over the whole conjunction exceeds 8 GB (each large-array conjunct is ~40 s, they do not share work); discharge the heavy conjuncts one by one and rewrite
theorem toy_params : paramsOk toyShape4 = true := by decide +kernel
theorem toy_tabs : tabsOk toyShape4 = true := by decide +kernel
theorem toy_layout : layoutShapeOk toyShape4 = true := by decide +kernel
theorem toy_mand : mandatoryOk toyShape4 = true := by decide +kernel
theorem toy_prek : preKindOk toyShape4 = true := by decide +kernel
theorem toy_orbit : orbitOk toyShape4 = true := by decide +kernel
theorem toy_width : widthOk toyShape4 = true := by decide +kernel
theorem toy_slot : slotOfOk toyShape4 = true := by decide +kernel
theorem toy_kind01 : (toyShape4.tabs.all fun t => (List.range (t.nc - t.npub)).all fun c =>
    toyShape4.colKind[t.col0 + c]! == 0 || toyShape4.colKind[t.col0 + c]! == 1) = true := by decide +kernel

theorem toyShape_ok : j8ShapeOk toyShape4 = true := by
  unfold j8ShapeOk
  rw [toy_params, toy_tabs, toy_layout, toy_mand, toy_prek, toy_orbit, toy_width, toy_slot, toy_kind01]
  decide +kernel

/-- the lemmas fire on the toy: `DomLink` and `hn32` at a concrete instance (vacuity witness for the lemma hypotheses) -/
theorem toyShape_domLink : DomLink toyShape4 (hn32_of_shape toyShape_ok) := domLink_of_shape toyShape_ok

/-! ## the instance hypotheses of `hdagU_of_tie` -/

theorem exReadsLtB_eq (w npub nch bc : Nat) : ∀ e : Tr.Ex, exReadsLtB w npub nch bc e = DagSem.exReadsLt w npub nch bc e
  | .var k i => by rcases k with _ | _ | k <;> simp [exReadsLtB, DagSem.exReadsLt]
  | .cF _ => rfl
  | .add a b => by simp [exReadsLtB, DagSem.exReadsLt, exReadsLtB_eq w npub nch bc a, exReadsLtB_eq w npub nch bc b]
  | .sub a b => by simp [exReadsLtB, DagSem.exReadsLt, exReadsLtB_eq w npub nch bc a, exReadsLtB_eq w npub nch bc b]
  | .mul a b => by simp [exReadsLtB, DagSem.exReadsLt, exReadsLtB_eq w npub nch bc a, exReadsLtB_eq w npub nch bc b]
  | .neg a => by simp [exReadsLtB, DagSem.exReadsLt, exReadsLtB_eq w npub nch bc a]
  | .pow a _ => by simp [exReadsLtB, DagSem.exReadsLt, exReadsLtB_eq w npub nch bc a]
  | .extVar k e => by rcases k with _ | _ | k <;> simp [exReadsLtB, DagSem.exReadsLt]
  | .chal _ => rfl
  | .ref _ => rfl

theorem chipReadsLtB_eq (ch : Tr.Chip) (w npub nch : Nat) : chipReadsLtB ch w npub nch = DagSem.chipReadsLt ch w npub nch := by
  have : exReadsLtB w npub nch ch.baseCols = DagSem.exReadsLt w npub nch ch.baseCols := funext (exReadsLtB_eq w npub nch ch.baseCols)
  unfold chipReadsLtB DagSem.chipReadsLt
  rw [this]

theorem hread_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) :
    ∀ t ∈ XI.tabs.toList, DagSem.chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  rw [← chipReadsLtB_eq]
  exact tabs_all_mem (by tauto : XI.tabs.all (fun t => chipReadsLtB t.chip (t.nc - t.npub) t.npub 19) = true) t ht

theorem hcanon_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, chipCanon t.chip = true := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) = true) t ht
  exact ((Bool.and_eq_true _ _).mp this).1

theorem hpreC_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  have h1 : XI.pre.all (·.all fun x => VF.based x.toNat) = true := by tauto
  intro c x hx
  apply HdagU.canon_of_based
  by_cases hc : c < XI.pre.size
  · rw [getElem!_pos XI.pre c hc] at hx
    exact Array.all_eq_true_iff_forall_mem.mp (Array.all_eq_true_iff_forall_mem.mp h1 _ (Array.getElem_mem hc)) x (Array.mem_def.mpr hx)
  · rw [getElem!_neg XI.pre c hc] at hx
    exact absurd hx (by simp [default]; intro h; exact List.not_mem_nil (Array.mem_def.mp h))

theorem hS_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : canon XI.hShift := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  exact HdagU.canon_of_based _ (by tauto)

theorem hle_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, t.hN ≤ XI.hN := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.hN ≤ XI.hN)) = true) t ht

theorem hcolB_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, t.col0 + t.nc ≤ XI.nc := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.col0 + t.nc ≤ XI.nc)) = true) t ht

theorem hpubB_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, t.pubBase + t.npub ≤ XI.pubOf.size := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.pubBase + t.npub ≤ XI.pubOf.size)) = true) t ht

theorem hnpub_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ t ∈ XI.tabs.toList, t.npub ≤ t.nc := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.npub ≤ t.nc)) = true) t ht

theorem hkind_of_shape {XI : ExecInst} (h : j8ShapeOk XI = true) : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
    XI.colKind[XI.tabs[t].col0 + c]! = 0 ∨ XI.colKind[XI.tabs[t].col0 + c]! = 1 := by
  unfold j8ShapeOk at h
  simp only [Bool.and_eq_true] at h
  intro t c hc
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c =>
    XI.colKind[t.col0 + c]! == 0 || XI.colKind[t.col0 + c]! == 1) = true) XI.tabs[t] (Array.getElem_mem_toList t.2)
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at this
  exact this c hc

/-- **`hdagU_shape_of_j8`**: the ten instance hypotheses of `HdagU.hdagU_of_tie` from `j8ShapeOk XI = true` -/
theorem hdagU_shape_of_j8 {XI : ExecInst} (h : j8ShapeOk XI = true) :
    (∀ t ∈ XI.tabs.toList, DagSem.chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true) ∧
    (∀ t ∈ XI.tabs.toList, chipCanon t.chip = true) ∧
    (∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x) ∧
    canon XI.hShift ∧
    (∀ t ∈ XI.tabs.toList, t.hN ≤ XI.hN) ∧
    (∀ t ∈ XI.tabs.toList, t.col0 + t.nc ≤ XI.nc) ∧
    (∀ t ∈ XI.tabs.toList, t.pubBase + t.npub ≤ XI.pubOf.size) ∧
    (∀ t ∈ XI.tabs.toList, t.npub ≤ t.nc) ∧
    (∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 0 ∨ XI.colKind[XI.tabs[t].col0 + c]! = 1) ∧
    XI.r = 2 :=
  ⟨hread_of_shape h, hcanon_of_shape h, hpreC_of_shape h, hS_of_shape h, hle_of_shape h, hcolB_of_shape h, hpubB_of_shape h,
   hnpub_of_shape h, hkind_of_shape h, r_of_shape h⟩

set_option linter.defProp false in
/-- the bundle fires on the toy (non-vacuity) -/
def toyShape_hdagU_shape := hdagU_shape_of_j8 toyShape_ok

end NockvmE2E.Exec.J8Shape

#print axioms NockvmE2E.Exec.J8Shape.domLink_of_paramsOk
#print axioms NockvmE2E.Exec.J8Shape.hpd_of_shape
#print axioms NockvmE2E.Exec.J8Shape.orbit_order_of_shape
#print axioms NockvmE2E.Exec.J8Shape.width_of_shape
#print axioms NockvmE2E.Exec.J8Shape.slotOf_of_shape
#print axioms NockvmE2E.Exec.J8Shape.toyShape_ok
#print axioms NockvmE2E.Exec.J8Shape.toyShape_domLink
#print axioms NockvmE2E.Exec.J8Shape.chipReadsLtB_eq
#print axioms NockvmE2E.Exec.J8Shape.hdagU_shape_of_j8
#print axioms NockvmE2E.Exec.J8Shape.toyShape_hdagU_shape
