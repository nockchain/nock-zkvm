/-
  **The assembled executable J-8 checker.**

  * **Frame coin vectors, executably** (§1): `chalsMJ8E` / `chalsAJ8ZE` / `chalsJJ8E : CoinsE → ℕ → K3` with
    `chalsMJ8E_spec` / `chalsAJ8ZE_spec` / `chalsJJ8E_spec` (`K3.toK (· χe j) = chalsMJ8 deltaF (toχ χe) j`, …), and the
    compute publics `pubVJ8E` with `pubVJ8E_spec` (`= pubVJ8 deltaF powerBasis3 …` at the lifted `ρ`, `ρS`).
  * **The input** `InJ8` (§2): claim, executable message, coins, row budgets, the registry data, and per chip the
    orbit height, the row count, the orbit generator (a `Gold`) and the rows.  `ValidJ8` (row counts positive, heights
    `≥ 1`, each generator of exact order `3 · 2^h`; decided by `validB`, the order by repeated squaring, `ordOK_iff`);
    the spec objects BUILT from the input: `mkPb` (nodes `ω^i`, orbits from the input's `ω`), `mkTr` (the Lagrange
    interpolants of the rows), coins `toχ I.χ`, message `I.M.toMsg`.
  * **`checkJ8`** (§3) = `validB ∧ checkStaticJ8 ∧ checkPubJ8E ∧ chipsB` (the seven chip checks: compute X, cell KW,
    walk J8, the J dispatch, atom HQ, the atom-walk dispatch, atom HQL), computable.
  * **`checkJ8_iff`** (§4): under the registry premise (`Rg i = some ⟨…⟩ ∧ WellTyped`, a `JetSpec` is not decidable),
    `checkJ8 I = true ↔ ∃ hv : ValidJ8 I, AcceptsJ8V deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I)
    I.r I.g`.
-/
import Nock.V1J8.MemJAW
import Nock.V1J8.MemCellKW
import Nock.V1J8.MemWalkJ8
import Nock.V1J8.MemAtom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.Check

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (chalsVCL)
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J8.Exe
open Nock.V1J8.CompX (TabX checkCompX computeChipX_iff powK toK_powK firstMaskE lastMaskE)
open Nock.V1J8.MemX (TabM checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAtomHQL checkAWOK prep2 prep3 prepJ
  checkCellKW_iff checkWalkJ8_iff checkJOK_iff checkAtomHQ_iff checkAtomHQL_iff checkAWOK_iff)

/-! ## 1. The frame coin vectors and the compute publics, executably -/

/-- `Re` of a lifted `K6`. -/
theorem re_toQ (x : K6) : Quad.re _ (K6.toQ x) = K3.toK x.re := Quad.re_mk _ _ _

/-- `Im` of a lifted `K6`. -/
theorem im_toQ (x : K6) : Quad.im _ (K6.toQ x) = K3.toK x.im := Quad.im_mk _ _ _

theorem quad_pow_re (a b : K3) (k : ℕ) :
    Quad.re _ (Quad.mk (algebraMap (ZMod p) KC deltaF) (K3.toK a) (K3.toK b) ^ k) = K3.toK (powE ⟨a, b⟩ k).re := by
  rw [show Quad.mk (algebraMap (ZMod p) KC deltaF) (K3.toK a) (K3.toK b) = K6.toQ ⟨a, b⟩ from rfl, ← toQ_powE,
    re_toQ]

theorem quad_pow_im (a b : K3) (k : ℕ) :
    Quad.im _ (Quad.mk (algebraMap (ZMod p) KC deltaF) (K3.toK a) (K3.toK b) ^ k) = K3.toK (powE ⟨a, b⟩ k).im := by
  rw [show Quad.mk (algebraMap (ZMod p) KC deltaF) (K3.toK a) (K3.toK b) = K6.toQ ⟨a, b⟩ from rfl, ← toQ_powE,
    im_toQ]

/-- The validity coin `γ′ = (χ₄, χ₆)` as a `K6`. -/
def gV (χe : CoinsE) : K6 := ⟨χe ⟨4, by decide⟩, χe ⟨6, by decide⟩⟩

/-- **The memory chips' challenge vector, executable** (`chalsMJ8` = `chalsVSQ` ∘ `chalsVS` ∘ `chalsVCL`). -/
def chalsMJ8E (χe : CoinsE) (j : ℕ) : K3 :=
  if j = 35 then χe ⟨15, by decide⟩ else if j = 36 then χe ⟨16, by decide⟩
  else if j = CellH.hGam then χe ⟨11, by decide⟩ else if j = CellH.hRho then χe ⟨12, by decide⟩
  else if h : j < 11 then χe ⟨j, lt_trans h (by decide)⟩
  else if (j - 11) % 2 = 0 then (powE (gV χe) ((j - 11) / 2)).re
  else (powE (gV χe) ((j - 12) / 2)).im

theorem chalsMJ8E_spec (χe : CoinsE) (j : ℕ) :
    K3.toK (chalsMJ8E χe j) = VerJ8.chalsMJ8 deltaF (toχ χe) j := by
  unfold chalsMJ8E VerJ8.chalsMJ8 chalsVSQ chalsVS chalsVCL
  split_ifs
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (quad_pow_re _ _ _).symm
  · exact (quad_pow_im _ _ _).symm

/-- **The atom table's challenge vector, executable** (`chalsAJ8Z` = `z` at 37 / 38, `y` at 2 / 3, else
`chalsMJ8`). -/
def chalsAJ8ZE (χe : CoinsE) (j : ℕ) : K3 :=
  if j = 37 then χe ⟨2, by decide⟩ else if j = 38 then χe ⟨3, by decide⟩
  else if j = 2 then χe ⟨17, by decide⟩ else if j = 3 then χe ⟨18, by decide⟩
  else chalsMJ8E χe j

theorem chalsAJ8ZE_spec (χe : CoinsE) (j : ℕ) :
    K3.toK (chalsAJ8ZE χe j) = ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) j := by
  unfold chalsAJ8ZE ChalsAZJ8.chalsAJ8Z ProbJ8.chalsAJ8
  split_ifs
  all_goals first
    | rfl
    | exact chalsMJ8E_spec χe j

/-- **The J chip's challenge vector, executable.** -/
def chalsJJ8E (χe : CoinsE) (j : ℕ) : K3 :=
  if j < 8 then
    (if j % 4 = 0 then χe ⟨11, by decide⟩ else if j % 4 = 1 then χe ⟨12, by decide⟩
      else if j % 4 = 2 then χe ⟨15, by decide⟩ else χe ⟨16, by decide⟩)
  else 0

theorem chalsJJ8E_spec (χe : CoinsE) (j : ℕ) :
    K3.toK (chalsJJ8E χe j) = VerJ8.chalsJJ8 (toχ χe) j := by
  unfold chalsJJ8E VerJ8.chalsJJ8
  split_ifs
  all_goals first
    | rfl
    | exact K3.toK_zero

/-- The function forms. -/
theorem chalsMJ8_eq (χe : CoinsE) : VerJ8.chalsMJ8 deltaF (toχ χe) = fun j => K3.toK (chalsMJ8E χe j) :=
  funext fun j => (chalsMJ8E_spec χe j).symm
theorem chalsAJ8Z_eq (χe : CoinsE) : ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) = fun j => K3.toK (chalsAJ8ZE χe j) :=
  funext fun j => (chalsAJ8ZE_spec χe j).symm
theorem chalsJJ8_eq (χe : CoinsE) : VerJ8.chalsJJ8 (toχ χe) = fun j => K3.toK (chalsJJ8E χe j) :=
  funext fun j => (chalsJJ8E_spec χe j).symm
theorem chalVJ8_eq (χe : CoinsE) : VerJ8.chalVJ8 powerBasis3 (toχ χe) = fun j => (chalVJ8E χe j).toZ :=
  funext fun j => (chalVJ8E_spec χe j).symm

/-- A list sum over `K3`. -/
def sumK3 : List K3 → K3
  | [] => 0
  | a :: l => a + sumK3 l

theorem toK_sumK3 : ∀ l : List K3, K3.toK (sumK3 l) = (l.map K3.toK).sum
  | [] => K3.toK_zero
  | a :: l => by rw [sumK3, K3.toK_add, toK_sumK3 l, List.map_cons, List.sum_cons]

/-- **The compute walk seed, executable** (`seedVS`: `αW · Σ_k γW^k · lift(label_k)`). -/
def seedE (c : P8PublicClaim) (m : ClaimMsgVS) (χe : CoinsE) : K3 :=
  χe ⟨13, by decide⟩ * sumK3 ((labelF (F := ZMod p) c m).zipIdx.map fun q =>
    powK (χe ⟨14, by decide⟩) q.2 * g3 (Gold.ofZ q.1))

theorem seedE_spec (c : P8PublicClaim) (m : ClaimMsgVS) (χe : CoinsE) :
    K3.toK (seedE c m χe) = seedVS (F := ZMod p) (K := KC) c m (toVS (toVSQ (toχ χe))) := by
  unfold seedE seedVS
  rw [K3.toK_mul, toK_sumK3, List.map_map]
  congr 2
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, K3.toK_mul, toK_powK, toK_g3, Gold.toZ_ofZ]
  rfl

/-- Limb `k` of a `K3` in `ZMod p`. -/
abbrev limbZ (a : K3) (k : ℕ) : ZMod p := MemX.limb a k

theorem coord_K (a : K3) (k : ℕ) (hk : k < 3) : coord powerBasis3 (K3.toK a) ⟨k, hk⟩ = limbZ a k := by
  rw [coord_powerBasis3_toK, limbZ, MemX.limb_eq a ⟨k, hk⟩]

/-- **The J-8 compute publics, executable** (claim label, `αW`, seed, `Re/Im ρ₃ ρ₄`, `Re/Im ρS`). -/
def pubVJ8E (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) (j : ℕ) : ZMod p :=
  if j < 6 then (labelF (F := ZMod p) c m).getD j 0
  else if j < 9 then limbZ (χe ⟨13, by decide⟩) (j - 6)
  else if j < 12 then limbZ (seedE c m χe) (j - 9)
  else if j < 15 then 0
  else if j < 18 then limbZ (ρ 3).re (j - 15)
  else if j < 21 then limbZ (ρ 4).re (j - 18)
  else if j < 24 then limbZ (ρ 3).im (j - 21)
  else if j < 27 then limbZ (ρ 4).im (j - 24)
  else if j < 30 then limbZ ρS.re (j - 27)
  else if j < 33 then limbZ ρS.im (j - 30)
  else 0

theorem pubVJ8E_spec (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) (j : ℕ) :
    pubVJ8E c m ρ ρS χe j =
      VerJ8.pubVJ8 deltaF powerBasis3 c m (fun i => K6.toQ (ρ i)) (K6.toQ ρS) (toχ χe) j := by
  unfold pubVJ8E VerJ8.pubVJ8 pubVHQ pubVH
  split_ifs
  all_goals first
    | rfl
    | (exfalso; omega)
    | (rw [re_toQ, coord_K])
    | (rw [im_toQ, coord_K])
    | (rw [← seedE_spec, coord_K])
    | exact (coord_K _ _ _).symm

theorem pubVJ8_eq (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) :
    VerJ8.pubVJ8 deltaF powerBasis3 c m (fun i => K6.toQ (ρ i)) (K6.toQ ρS) (toχ χe) = pubVJ8E c m ρ ρS χe :=
  funext fun j => (pubVJ8E_spec c m ρ ρS χe j).symm

/-! ## 2. The input, its validity, and the spec objects built from it -/

/-- The executable orbit-order test: `ω` has exact order `3 · 2^h` (`h ≥ 1`). -/
def ordOK (ω : Gold) (h : ℕ) : Bool :=
  eqG (Gold.pow ω (3 * 2 ^ h)) 1 && !eqG (Gold.pow ω (3 * 2 ^ (h - 1))) 1 && !eqG (Gold.pow ω (2 ^ h)) 1

theorem gpow_eq_one_iff (ω : Gold) (n : ℕ) : eqG (Gold.pow ω n) 1 = true ↔ ω.toZ ^ n = 1 := by
  rw [eqG_iff]
  constructor
  · intro h; have := congrArg Gold.toZ h; rwa [Gold.toZ_pow, Gold.toZ_one] at this
  · intro h; apply Gold.toZ_injective; rw [Gold.toZ_pow, Gold.toZ_one]; exact h

theorem ordOK_iff (ω : Gold) (h : ℕ) (h1 : 1 ≤ h) :
    ordOK ω h = true ↔ orderOf ω.toZ = 3 * 2 ^ h := by
  have e : 3 * 2 ^ h / 2 = 3 * 2 ^ (h - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h1
    simp [pow_succ]; omega
  have e3 : 3 * 2 ^ h / 3 = 2 ^ h := by omega
  unfold ordOK
  have gne : ∀ n, (!eqG (Gold.pow ω n) 1) = true ↔ ω.toZ ^ n ≠ 1 := fun n => by
    rw [Bool.not_eq_true', ← Bool.not_eq_true, gpow_eq_one_iff]
  simp only [Bool.and_eq_true, gne, gpow_eq_one_iff, and_assoc]
  constructor
  · rintro ⟨h0, h2, h3⟩
    refine orderOf_eq_of_pow_and_pow_div_prime (by positivity) h0 fun q hq hqd => ?_
    have : q = 2 ∨ q = 3 := by
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · right; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
      · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    rcases this with rfl | rfl
    · rw [e]; exact h2
    · rw [e3]; exact h3
  · intro ho
    refine ⟨?_, ?_, ?_⟩
    · rw [← ho]; exact pow_orderOf_eq_one _
    · refine pow_ne_one_of_lt_orderOf (x := ω.toZ) (by positivity) ?_
      rw [ho]; have : 0 < 2 ^ (h - 1) := by positivity
      have : 2 ^ h = 2 * 2 ^ (h - 1) := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h1
        simp [pow_succ]; ring
      omega
    · refine pow_ne_one_of_lt_orderOf (x := ω.toZ) (by positivity) ?_
      rw [ho]; have : 0 < 2 ^ h := by positivity
      omega

/-- **One chip's input**: orbit height, row count, orbit generator, the rows (column `j`, row `i`). -/
structure ChipIn where
  h : ℕ
  n : ℕ
  ω : Gold
  cols : ℕ → Fin n → ZMod p

/-- **The checker's input**: the claim, the executable message, the coins, the row budgets, the registry data, the
two root counts, the J layout, and the six chips' rows. -/
structure InJ8 where
  c : P8PublicClaim
  M : MsgE
  χ : CoinsE
  r : RowsJ8
  g : ℕ
  X : ChipIn
  C : ChipIn
  W : ChipIn
  J : ChipIn
  A : ChipIn
  V : ChipIn
  kroots : ℕ
  krootsV : ℕ
  lay : Fin J.n → Nock.Jet.ChipJ8.PRow
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  regs : List ℕ
  ids : List ℕ
  idx : ℕ → ℕ
  rk : ℕ → ℕ × ℕ

/-- A chip's orbit is admissible: height `≥ 1`, generator of exact order `3 · 2^h`. -/
structure OrbOK (q : ChipIn) : Prop where
  h1 : 1 ≤ q.h
  ord : orderOf q.ω.toZ = 3 * 2 ^ q.h

def orbB (q : ChipIn) : Bool := decide (1 ≤ q.h) && ordOK q.ω q.h

theorem orbB_iff (q : ChipIn) : orbB q = true ↔ OrbOK q := by
  unfold orbB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, ho⟩; exact ⟨h1, (ordOK_iff _ _ h1).mp ho⟩
  · rintro ⟨h1, ho⟩; exact ⟨h1, (ordOK_iff _ _ h1).mpr ho⟩

/-- **The structural facts the spec objects need** (all decidable: `validB`). -/
structure ValidJ8 (I : InJ8) : Prop where
  nX : 0 < I.X.n
  nC : 0 < I.C.n
  nW : 0 < I.W.n
  nA : 0 < I.A.n
  nV : 0 < I.V.n
  oX : OrbOK I.X
  oC : OrbOK I.C
  oW : OrbOK I.W
  oJ : OrbOK I.J
  oA : OrbOK I.A
  oV : OrbOK I.V

def validB (I : InJ8) : Bool :=
  decide (0 < I.X.n) && decide (0 < I.C.n) && decide (0 < I.W.n) && decide (0 < I.A.n) && decide (0 < I.V.n) &&
  orbB I.X && orbB I.C && orbB I.W && orbB I.J && orbB I.A && orbB I.V

theorem validB_iff (I : InJ8) : validB I = true ↔ ValidJ8 I := by
  unfold validB
  simp only [Bool.and_eq_true, decide_eq_true_eq, orbB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩, k⟩
    exact ⟨a, b, c, d, e, f, g, h, i, j, k⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩, k⟩

/-- The orbit of an admissible chip input (`βcoset = 1`). -/
def mkOrbit (q : ChipIn) (ho : OrbOK q) : StrictOrbitDomain (ZMod p) 3 q.h where
  ω := q.ω.toZ
  βcoset := 1
  e_pos := by norm_num
  h_pos := ho.h1
  order_ω := ho.ord
  βcoset_ne_zero := one_ne_zero

/-- A chip's row nodes `ω^i` (computed by repeated squaring). -/
def nodesOf (q : ChipIn) : Fin q.n → ZMod p := fun i => (Gold.pow q.ω i).toZ

theorem nodesOf_eq (q : ChipIn) (i : Fin q.n) : nodesOf q i = q.ω.toZ ^ (i : ℕ) := Gold.toZ_pow _ _

/-- **The verifier's public parameters, built from the input.** -/
def mkPb (I : InJ8) (hv : ValidJ8 I) : PubJ8 p where
  h := I.X.h
  n := I.X.n
  hn := hv.nX
  nodes := nodesOf I.X
  orbit := mkOrbit I.X hv.oX
  hC := I.C.h
  nC := I.C.n
  hnC := hv.nC
  nodesC := nodesOf I.C
  orbitC := mkOrbit I.C hv.oC
  kroots := I.kroots
  hW := I.W.h
  nW := I.W.n
  hnW := hv.nW
  nodesW := nodesOf I.W
  orbitW := mkOrbit I.W hv.oW
  hJ := I.J.h
  nJ := I.J.n
  nodesJ := nodesOf I.J
  orbitJ := mkOrbit I.J hv.oJ
  lay := I.lay
  hA := I.A.h
  nA := I.A.n
  hnA := hv.nA
  nodesA := nodesOf I.A
  orbitA := mkOrbit I.A hv.oA
  krootsV := I.krootsV
  hV := I.V.h
  nV := I.V.n
  hnV := hv.nV
  nodesV := nodesOf I.V
  orbitV := mkOrbit I.V hv.oV
  Rt := I.Rt
  regs := I.regs
  ids := I.ids
  idx := I.idx
  rk := I.rk

/-- A chip's column `j` as a polynomial: the Lagrange interpolant of the rows on the nodes. -/
noncomputable def interpOf (q : ChipIn) (j : ℕ) : (ZMod p)[X] :=
  Lagrange.interpolate Finset.univ (nodesOf q) (fun i => q.cols j i)

/-- **The six traces, built from the input.** -/
noncomputable def mkTr (I : InJ8) : TrJ8 (ZMod p) where
  C := fun j => interpOf I.X j
  M := fun j => interpOf I.C j
  W := fun j => interpOf I.W j
  J := fun j => interpOf I.J j
  A := fun j => interpOf I.A j
  V := fun j => interpOf I.V j

/-! ## 3. The tables and the checker -/

def tabX (I : InJ8) : TabX I.X.n :=
  ⟨nodesOf I.X, I.X.ω.toZ, I.X.cols, fun j => (chalVJ8E I.χ j).toZ, pubVJ8E I.c I.M.m I.M.ρ I.M.ρS I.χ⟩
def tabC (I : InJ8) : TabM I.C.n :=
  ⟨nodesOf I.C, I.C.ω.toZ, I.C.cols, chalsMJ8E I.χ, I.M.pubsC, prep2 I.C.n⟩
def tabW (I : InJ8) : TabM I.W.n :=
  ⟨nodesOf I.W, I.W.ω.toZ, I.W.cols, chalsMJ8E I.χ, I.M.pubsW, prep3 I.W.n I.kroots⟩
def tabJ (I : InJ8) : TabM I.J.n :=
  ⟨nodesOf I.J, I.J.ω.toZ, I.J.cols, chalsJJ8E I.χ, I.M.pubsJ, prepJ I.lay⟩
def tabA (I : InJ8) : TabM I.A.n :=
  ⟨nodesOf I.A, I.A.ω.toZ, I.A.cols, chalsAJ8ZE I.χ, I.M.pubsA, prep2 I.A.n⟩
def tabV (I : InJ8) : TabM I.V.n :=
  ⟨nodesOf I.V, I.V.ω.toZ, I.V.cols, chalsAJ8ZE I.χ, I.M.pubsV, prep3 I.V.n I.krootsV⟩

/-- **The seven chip checks.** -/
def chipsB (I : InJ8) : Bool :=
  checkCompX (tabX I) && checkCellKW (tabC I) && checkWalkJ8 I.kroots (tabW I) && checkJOK (tabJ I) &&
  checkAtomHQ (tabA I) && checkAWOK I.krootsV (tabV I) && checkAtomHQL (tabA I)

/-- **The executable J-8 checker**: validity, the static block, the public equations, the chips. -/
def checkJ8 (I : InJ8) : Bool :=
  if hv : validB I = true then
    checkStaticJ8 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g &&
    checkPubJ8E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && chipsB I
  else false

/-! ## 4. `checkJ8_iff` -/

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- The registry premise (`hTpl`'s non-decidable part, carried by `ChipsJ8.hreg`). -/
def RegOK (I : InJ8) (Rg : Nock.Jet.Registry) : Prop :=
  ∀ i ∈ I.regs, Rg i = some ⟨(I.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (I.Rt i)⟩ ∧ (I.Rt i).WellTyped p

theorem adj_of (q : ChipIn) (ho : OrbOK q)
    (h : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n), nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω) :
    ∀ i : Fin q.n, ∀ hi : (i : ℕ) + 1 < q.n, nodesOf q ⟨i + 1, hi⟩ = q.ω.toZ * nodesOf q i := by
  intro i hi; rw [h i hi, mul_comm]; rfl

/-- **The chip block**: under the static block, `chipsB` is exactly `ChipsJ8` (the registry premise given). -/
theorem chipsB_iff (I : InJ8) (hv : ValidJ8 I) (Rg : Nock.Jet.Registry) (hreg : RegOK I Rg)
    (hs : StaticJ8 (mkPb I hv) I.c I.M.m I.r I.g) :
    chipsB I = true ↔
      ChipsJ8 deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) := by
  have eX := computeChipX_iff (tabX I) hv.nX (mkOrbit I.X hv.oX)
    (qX deltaF powerBasis3 (mkPb I hv) (mkTr I) (tabX I).chal (tabX I).pub)
    hs.hinjX (adj_of I.X hv.oX hs.hadjX) rfl (fun j => rfl)
  have eC := checkCellKW_iff (tabC I) hv.nC (mkOrbit I.C hv.oC)
    (qM deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabC I).chals i)) (fun i => K3.toK ((tabC I).pubs i)))
    hs.hinjC (adj_of I.C hv.oC hs.hadjC) rfl rfl (fun j => rfl)
  have eW := checkWalkJ8_iff I.kroots (tabW I) hv.nW (mkOrbit I.W hv.oW)
    (qW deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabW I).chals i)) (fun i => K3.toK ((tabW I).pubs i)))
    hs.hinjW (adj_of I.W hv.oW hs.hadjW) rfl rfl (fun j => rfl)
  have eJ := checkJOK_iff (tabJ I) (mkOrbit I.J hv.oJ) I.lay
    (qJ deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabJ I).chals i)) (fun i => K3.toK ((tabJ I).pubs i)))
    rfl rfl (fun j => rfl)
  have eA := checkAtomHQ_iff (tabA I) hv.nA (mkOrbit I.A hv.oA)
    (qA deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabA I).chals i)) (fun i => K3.toK ((tabA I).pubs i)))
    hs.hinjA (adj_of I.A hv.oA hs.hadjA) rfl rfl (fun j => rfl)
  have eL := checkAtomHQL_iff (tabA I) hv.nA (mkOrbit I.A hv.oA)
    (qAL deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabA I).chals i))
      (fun i => K3.toK ((tabA I).pubs i)))
    hs.hinjA (adj_of I.A hv.oA hs.hadjA) rfl rfl (fun j => rfl)
  have eV := checkAWOK_iff I.krootsV (tabV I) hv.nV (mkOrbit I.V hv.oV)
    (qV deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabV I).chals i)) (fun i => K3.toK ((tabV I).pubs i)))
    rfl rfl (fun j => rfl)
  have hM := chalsMJ8_eq I.χ
  have hAZ := chalsAJ8Z_eq I.χ
  have hJJ := chalsJJ8_eq I.χ
  have hcv := chalVJ8_eq I.χ
  have hpv := pubVJ8_eq I.c I.M.m I.M.ρ I.M.ρS I.χ
  unfold chipsB
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hX, hC⟩, hW⟩, hJ⟩, hA⟩, hV⟩, hL⟩
    obtain ⟨sX, bX⟩ := id (eX.mpr hX)
    obtain ⟨sC, bC⟩ := eC.mpr hC
    obtain ⟨sW, bW⟩ := eW.mpr hW
    obtain ⟨sA, bA⟩ := eA.mpr hA
    obtain ⟨sL, bL⟩ := eL.mpr hL
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg⟩
    · show RAP.SatisfiesWithPreprocessing _ _
      rw [hcv]
      erw [hpv]
      exact ⟨sX, bX⟩
    · rw [hM]; exact sC
    · rw [hM]; exact bC
    · rw [hM]; exact sW
    · rw [hM]; exact bW
    · rw [hJJ]; exact eJ.mpr hJ
    · rw [hAZ]; exact sA
    · rw [hAZ]; exact bA
    · rw [hAZ]; exact eV.mpr hV
    · rw [hAZ]; exact sL
    · rw [hAZ]; exact bL
  · intro k
    have kX := k.hsatX
    have kC := k.hsatC
    have kbC := k.hbindC
    have kW := k.hsatW
    have kbW := k.hbindW
    have kJ := k.hJk
    have kA := k.hsatA
    have kbA := k.hbindA
    have kV := k.hVk
    have kL := k.hsatL
    have kbL := k.hbindL
    rw [hcv] at kX
    erw [hpv] at kX
    rw [hM] at kC kbC kW kbW
    rw [hJJ] at kJ
    rw [hAZ] at kA kbA kV kL kbL
    exact ⟨⟨⟨⟨⟨⟨eX.mp kX, eC.mp ⟨kC, kbC⟩⟩, eW.mp ⟨kW, kbW⟩⟩, eJ.mp kJ⟩, eA.mp ⟨kA, kbA⟩⟩, eV.mp kV⟩,
      eL.mp ⟨kL, kbL⟩⟩

/-- **`checkJ8_iff`: the J-8 checker is exactly the verifier.**  Under the registry premise, `checkJ8 I = true`
iff the input is valid and `AcceptsJ8V` holds at the verifier data `mkPb I`, the coins `toχ I.χ`, the message
`I.M.toMsg` and the traces `mkTr I` (the interpolants of the rows), all built from the input. -/
theorem checkJ8_iff (I : InJ8) (Rg : Nock.Jet.Registry) (hreg : RegOK I Rg) :
    checkJ8 I = true ↔ ∃ hv : ValidJ8 I,
      AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g := by
  unfold checkJ8
  constructor
  · intro h
    by_cases hb : validB I = true
    · rw [dif_pos hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hs, hp⟩, hc⟩ := h
      have hv := (validB_iff I).mp hb
      have hs' := (checkStaticJ8_iff _ _ _ _ _).mp hs
      refine ⟨hv, (acceptsJ8V_iff_exe _ Rg I.c I.χ I.M (mkTr I) I.r I.g).mpr ⟨hs, hp, ?_⟩⟩
      exact (chipsB_iff I hv Rg hreg hs').mp hc
    · rw [dif_neg hb] at h; exact absurd h Bool.false_ne_true
  · rintro ⟨hv, h⟩
    obtain ⟨hs, hp, hc⟩ := (acceptsJ8V_iff_exe _ Rg I.c I.χ I.M (mkTr I) I.r I.g).mp h
    have hb : validB I = true := (validB_iff I).mpr hv
    rw [dif_pos hb]
    simp only [Bool.and_eq_true]
    have hs' := (checkStaticJ8_iff _ _ _ _ _).mp hs
    exact ⟨⟨hs, hp⟩, (chipsB_iff I hv Rg hreg hs').mpr hc⟩

end Iff

end Nock.V1J8.Check
