/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/StatementP1.lean

 **Trace uniqueness for the J-8 AIR on the P1 block-IO fragment: the statement.**
 no coin, no existing statement edited.

 * §1 the claim-level fragment `P1FragC` (formula ops through the placeholder `OpsP1`, axes of depth `≤ 60`,
 small atoms, a terminating run of `genX` at the empty registry).
 * §2 the canonical public layout `canonPb`: the orbit generator is CONCRETE, `ω_h = 7^((p−1)/(3·2^h))` in
 Goldilocks (`orderOf_omegaG`, by a kernel power-mod check), nodes `ω^i`, and the P1 constants (`nJ = 0`,
 `nA = nV = 1`, `krootsV = 0`, empty registry). The four table sizes are a parameter `sz : P8PublicClaim →
 SizesP1`, to be instantiated by the canonical generator's sizes.
 * §3 `DegOK` (every committed column has degree below its table height), `MsgSupp` (message entries outside the
 read set are `0`), `padA` (the atom pad row).
 * §4 the side templates `canonCT` (compute: `inv4` zero pin, off-`Act` zero pins), `canonMT` (cell: strict
 lexicographic row order with 32-bit limbs and canonical limbs, the child-kind pins, the rank-inverse zero pins),
 `canonWT` (walk: root order, last-row `qinv`, the depth-certificate aux `y`); every gate of degree `≤ 4`, checked
 by `decide` on `CoeffExpr.degree`; their RAPs over the chips' own rows; `AuxP1`.
 * §5 `CanonP1`, `AcceptsCanon`; `probP1_final_clean` (soundness by implication into `probJ8V_final_clean`).
 * §6 `prob_le_of_outside'` / `probJ8X_lt_155_census32'`: the χ-dependent-target generalisations.
 * §7 `CanonEqP1` (the characterisation to be proved: outside the J-8 events an accepted canonical trace IS
 `canonOf χ`), `trace_unique_good`, and `trace_unique_prob` from it. `canonOf` is a parameter here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.Atoms (lenL)

/-! ## 1. The fragment -/

/-- The formula ops of the fragment: `[0 ax]`, `[7 b c]`, `[10 [ax d] e]` (atom axes) and autocons, at every
subformula. -/
def opsB : Noun → Bool
  | .cell x@(.cell _ _) y => opsB x && opsB y
  | .cell (.atom 0) (.atom _) => true
  | .cell (.atom 7) (.cell b c) => opsB b && opsB c
  | .cell (.atom 10) (.cell (.cell (.atom _) d) e) => opsB d && opsB e
  | _ => false

/-- **Placeholder** for the syntactic fragment predicate `P1FragC`. -/
def OpsP1 (f : Noun) : Prop := opsB f = true

/-- Every axis of a `[0 ax]` / `[10 [ax d] e]` subformula is in `[1, 2^61)` (read depth `≤ 60`). -/
def axesB : Noun → Bool
  | .cell x@(.cell _ _) y => axesB x && axesB y
  | .cell (.atom 0) (.atom ax) => decide (1 ≤ ax) && decide (ax < 2 ^ 61)
  | .cell (.atom 7) (.cell b c) => axesB b && axesB c
  | .cell (.atom 10) (.cell (.cell (.atom ax) d) e) =>
      decide (1 ≤ ax) && decide (ax < 2 ^ 61) && axesB d && axesB e
  | _ => true

/-- **The claim-level P1 fragment.** -/
structure P1FragC (c : P8PublicClaim) : Prop where
  ops : OpsP1 c.formula
  axes : axesB c.formula = true
  small : ∀ k : Fin 3, ∀ v ∈ (claimNoun c k).leafList, v < Nock.Atoms.p
  run : ∃ (fuel : ℕ) (t : NTree Nock.Edit.GenX.SkelX),
    Nock.Edit.GenX.genX InhabJ8Base.R0 fuel c.subject c.formula = some (t, c.result)

/-! ## 2. The canonical public layout -/

/-- `b^e mod m` by binary powering, `f` steps of fuel. -/
def pm (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | f + 1, b, e =>
    if e = 0 then 1 else
      if e % 2 = 1 then pm m f (b * b % m) (e / 2) * b % m else pm m f (b * b % m) (e / 2)

theorem pm_spec (m : ℕ) : ∀ (f b e : ℕ), e < 2 ^ f → ((pm m f b e : ℕ) : ZMod m) = (b : ZMod m) ^ e
  | 0, b, e, he => by
    have : e = 0 := by rw [pow_zero] at he; omega
    subst this; simp [pm]
  | f + 1, b, e, he => by
    have ih := pm_spec m f (b * b % m) (e / 2) (by rw [pow_succ] at he; omega)
    rw [ZMod.natCast_mod, Nat.cast_mul] at ih
    simp only [pm]
    split_ifs with h0 h1
    · subst h0; simp
    · rw [ZMod.natCast_mod, Nat.cast_mul, ih]
      conv_rhs => rw [← Nat.div_add_mod e 2, h1]
      ring
    · rw [ih]
      conv_rhs => rw [← Nat.div_add_mod e 2, show e % 2 = 0 by omega]
      ring

/-- **The concrete orbit generator** `ω_h = 7^((p − 1)/(3·2^h))`. -/
def omegaG (p h : ℕ) : ZMod p := (7 : ZMod p) ^ ((p - 1) / (3 * 2 ^ h))

section Order
local notation "PG" => Nock.Atoms.p

theorem pow7_eq (e : ℕ) (he : e < 2 ^ 70) : (7 : ZMod PG) ^ e = ((pm PG 70 7 e : ℕ) : ZMod PG) := by
  rw [pm_spec PG 70 7 e he]; norm_num

theorem natCast_ne_one {x : ℕ} (hx : x % PG ≠ 1 % PG) : ((x : ℕ) : ZMod PG) ≠ 1 := by
  intro h; apply hx; rw [← ZMod.natCast_eq_natCast_iff']; simpa using h

/-- `w = 7^((p−1)/(3·2^32))` has order exactly `3·2^32` (`7^((p−1)/2) ≠ 1`, `7^((p−1)/3) ≠ 1`: kernel checks). -/
theorem orderOf_w : orderOf ((7 : ZMod PG) ^ 1431655765) = 3 * 2 ^ 32 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) ?_ ?_
  · rw [← pow_mul, pow7_eq _ (by norm_num)]
    have : pm PG 70 7 (1431655765 * (3 * 2 ^ 32)) = 1 := by decide +kernel
    rw [this, Nat.cast_one]
  · intro q hq hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h3 | h2
    · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      subst this
      rw [← pow_mul, pow7_eq _ (by norm_num)]
      exact natCast_ne_one (by decide +kernel)
    · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
      subst this
      rw [← pow_mul, pow7_eq _ (by norm_num)]
      exact natCast_ne_one (by decide +kernel)

/-- **`ω_h` has order exactly `3·2^h`** for `1 ≤ h ≤ 32` (Goldilocks). -/
theorem orderOf_omegaG {h : ℕ} (h32 : h ≤ 32) : orderOf (omegaG PG h) = 3 * 2 ^ h := by
  have hP1 : PG - 1 = 1431655765 * (3 * 2 ^ 32) := by
    norm_num [Nock.Atoms.p, Nock.Field.p]
  have hsplit : (2 : ℕ) ^ 32 = 2 ^ h * 2 ^ (32 - h) := by rw [← pow_add]; congr 1; omega
  have he : (PG - 1) / (3 * 2 ^ h) = 1431655765 * 2 ^ (32 - h) := by
    rw [hP1, hsplit, show 1431655765 * (3 * (2 ^ h * 2 ^ (32 - h))) =
      (1431655765 * 2 ^ (32 - h)) * (3 * 2 ^ h) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  unfold omegaG
  rw [he, pow_mul, orderOf_pow' _ (by positivity), orderOf_w, hsplit,
    show 3 * (2 ^ h * 2 ^ (32 - h)) = (3 * 2 ^ h) * 2 ^ (32 - h) by ring, Nat.gcd_mul_left_left]
  exact Nat.mul_div_cancel _ (by positivity)

end Order

section Layout
variable {p : ℕ} [Fact p.Prime]

/-- **The concrete orbit** of height `h` (`1 ≤ h ≤ 32`, Goldilocks), coset `β = 1`. -/
def orbitG (hpG : p = Nock.Atoms.p) (h : ℕ) (h1 : 1 ≤ h) (h32 : h ≤ 32) : StrictOrbitDomain (ZMod p) 3 h where
  ω := omegaG p h
  βcoset := 1
  e_pos := by norm_num
  h_pos := h1
  order_ω := by subst hpG; exact orderOf_omegaG h32
  βcoset_ne_zero := one_ne_zero

/-- The four layout sizes the claim determines (compute rows, cell rows, walk rows, walk roots). -/
structure SizesP1 where
  n : ℕ
  nC : ℕ
  nW : ℕ
  kroots : ℕ
  hn : 0 < n
  hnC : 0 < nC
  hnW : 0 < nW
  hfit : max n (max nC nW) ≤ 2 ^ 32

/-- The common orbit height: the least `h ≥ 1` with every table `≤ 2^h`. -/
def SizesP1.ht (s : SizesP1) : ℕ := max 1 (Nat.clog 2 (max s.n (max s.nC s.nW)))

theorem SizesP1.one_le_ht (s : SizesP1) : 1 ≤ s.ht := le_max_left _ _

theorem SizesP1.ht_le_32 (s : SizesP1) : s.ht ≤ 32 :=
  max_le (by norm_num) (Nat.clog_le_of_le_pow s.hfit)

theorem SizesP1.fit_ht (s : SizesP1) : max s.n (max s.nC s.nW) ≤ 2 ^ s.ht :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- The nodes `i ↦ ω^i`. -/
def nodesG {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (n : ℕ) : Fin n → ZMod p := fun i => o.ω ^ (i : ℕ)

/-- The empty template table entry. -/
def tpl0 : Nock.Jet.Autogen.Tpl := ⟨0, Fin.elim0, Fin.elim0, .F, .const 0⟩

/-- **The canonical public layout of given sizes**: one concrete orbit, nodes `ω^i`, the P1 constants. -/
def canonPbOf (hpG : p = Nock.Atoms.p) (s : SizesP1) : PubJ8 p :=
  let o := orbitG hpG s.ht s.one_le_ht s.ht_le_32
  { h := s.ht, n := s.n, hn := s.hn, nodes := nodesG o s.n, orbit := o
    hC := s.ht, nC := s.nC, hnC := s.hnC, nodesC := nodesG o s.nC, orbitC := o
    kroots := s.kroots
    hW := s.ht, nW := s.nW, hnW := s.hnW, nodesW := nodesG o s.nW, orbitW := o
    hJ := s.ht, nJ := 0, nodesJ := nodesG o 0, orbitJ := o, lay := fun i => Fin.elim0 i
    hA := s.ht, nA := 1, hnA := one_pos, nodesA := nodesG o 1, orbitA := o
    krootsV := 0
    hV := s.ht, nV := 1, hnV := one_pos, nodesV := nodesG o 1, orbitV := o
    Rt := fun _ => tpl0, regs := [], ids := [], idx := fun _ => 0, rk := fun _ => (0, 0) }

/-- **`canonPb`**: the canonical layout of a claim, at the sizes `sz c`. -/
def canonPb (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) : PubJ8 p :=
  canonPbOf hpG (sz c)

theorem canonPb_consts (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    (canonPb hpG sz c).nJ = 0 ∧ (canonPb hpG sz c).nA = 1 ∧ (canonPb hpG sz c).nV = 1 ∧
      (canonPb hpG sz c).krootsV = 0 ∧ (canonPb hpG sz c).regs = [] ∧ (canonPb hpG sz c).ids = [] ∧
      (canonPb hpG sz c).orbit.ω = omegaG p (sz c).ht :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Layout

/-! ## 3. Degrees, message support, the atom pad -/

/-- The six-state fragment's selectors: `OP_0`, `OP_7`, `cons`, `s10`, `s10L`, `s10T`. -/
def six : List ℕ := [0, 7, 10, 11, 12, 13]

/-- The atom table's pad row (`[0 1]`, `nA = 1`), round-0 columns `< 205`. -/
def padA {F : Type} [Field F] (j : ℕ) : F := if j ∈ [0, 1, 8, 9, 18, 162, 194] then 1 else 0

/-- The aux columns: the cell sort gadget (`200`) and the walk aux (`32`). -/
structure AuxP1 (F : Type) [Field F] where
  M : Fin 200 → F[X]
  W : Fin 32 → F[X]

section Deg
variable {p : ℕ} [Fact p.Prime]

/-- **(D)**: every committed column has degree below its table height (rounds 0, 1, 2 and the aux columns). -/
structure DegOK (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) : Prop where
  C : ∀ j, (tr.C j).degree < (Pb.n : WithBot ℕ)
  M : ∀ j, (tr.M j).degree < (Pb.nC : WithBot ℕ)
  W : ∀ j, (tr.W j).degree < (Pb.nW : WithBot ℕ)
  J : ∀ j, (tr.J j).degree < (Pb.nJ : WithBot ℕ)
  A : ∀ j, (tr.A j).degree < (Pb.nA : WithBot ℕ)
  V : ∀ j, (tr.V j).degree < (Pb.nV : WithBot ℕ)
  auxM : ∀ j, (ax.M j).degree < (Pb.nC : WithBot ℕ)
  auxW : ∀ j, (ax.W j).degree < (Pb.nW : WithBot ℕ)

/-- E4 (J): at `nJ = 0`, `DegOK` forces the J trace to vanish. -/
theorem trJ_zero_of_degOK {Pb : PubJ8 p} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)} (hd : DegOK Pb tr ax)
    (h0 : Pb.nJ = 0) (j : Fin 71) : tr.J j = 0 := by
  have := hd.J j
  rw [h0, Nat.cast_zero] at this
  exact Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp this)

end Deg

section Msg
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {δ : ZMod p}

/-- **The extra pin (E6), `MsgSupp`**: every message entry outside the read set `R*` is `0`. `R*`: claim serials of cell claim
nouns; `ρ 3, ρ 4`, `ρS`; `pubsC 0..5`, `pubsW 0..7` (`2, 3` are read by the walk RAP's `pAcc` terminal),
`pubsA 0..11`; nothing of `pubsJ` (J absent) or `pubsV` (atom walk absent). -/
structure MsgSupp (c : P8PublicClaim) (M : MsgJ8' p K δ) : Prop where
  mRk : ∀ k, (M.m k).2 = (0, 0)
  mAtom : ∀ k, isCellN (claimNoun c k) = false → (M.m k).1 = 0
  rho : M.ρ 0 = 0 ∧ M.ρ 1 = 0 ∧ M.ρ 2 = 0
  pubsC : ∀ j, 6 ≤ j → M.pubsC j = 0
  pubsW : ∀ j, 8 ≤ j → M.pubsW j = 0
  pubsJ : ∀ j, M.pubsJ j = 0
  pubsA : ∀ j, 12 ≤ j → M.pubsA j = 0
  pubsV : ∀ j, M.pubsV j = 0

end Msg

/-! ## 4. The side templates -/

section Side
variable {F : Type} [Field F]

/-! ### Compute: `canonC` (`69` round-0 columns, no aux) -/

/-- `Act(c) ∩ six` for every round-0 compute column (the census table). -/
def actC (c : ℕ) : List ℕ :=
  if c < 17 then (if c ∈ six then [c] else []) else
  match c with
  | 17 | 18 => six
  | 19 => [0, 11]
  | 20 => [0, 11, 12]
  | 21 | 22 | 23 => [12]
  | 24 | 25 | 26 | 27 | 28 | 29 | 30 => six
  | 31 | 32 | 33 | 34 => [7, 10, 11, 12]
  | 35 => six
  | 36 | 37 | 38 => [0, 7, 10, 11]
  | 39 | 40 | 41 | 42 => [7, 11]
  | 43 | 44 | 45 | 46 => [11, 12]
  | 48 => [12]
  | 49 => [0]
  | 51 => [10, 11]
  | 54 => six
  | 55 => [7, 10, 11]
  | 56 | 57 => [7, 11]
  | 59 => [11]
  | 63 => [12]
  | 64 => six
  | _ => []

/-- E3: `(Σ_{s ∉ Act(c)} sel_s)·c` over all seventeen selectors. -/
def pinC (c : ℕ) : CoeffExpr F :=
  .mul (CoeffExpr.sumList ((List.range 17).filter fun s => decide (s ∉ actC c)) cv) (cv c)

/-- **The compute side gates**: E2 `(1 − s4·fast)·inv4`, then E3 for each of the `69` round-0 columns. -/
def canonCGates : List (CoeffExpr F) :=
  .mul (notE (.mul (cv 4) (cv 61))) (cv 62) :: (List.range 69).map pinC

/-- A listed sum of degree-`≤ 1` terms has degree `≤ 1`. -/
theorem sumList_deg1 (l : List ℕ) (f : ℕ → CoeffExpr F) (h : ∀ i, (f i).degree ≤ 1) :
    (CoeffExpr.sumList l f).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le l f 1 fun i _ => h i

theorem deg_app {l₁ l₂ : List (CoeffExpr F)} (h₁ : ∀ g ∈ l₁, g.degree ≤ 4) (h₂ : ∀ g ∈ l₂, g.degree ≤ 4) :
    ∀ g ∈ l₁ ++ l₂, g.degree ≤ 4 := fun g hg => (List.mem_append.mp hg).elim (h₁ g) (h₂ g)

theorem deg_map {l : List ℕ} {f : ℕ → CoeffExpr F} (h : ∀ i, (f i).degree ≤ 4) : ∀ g ∈ l.map f, g.degree ≤ 4 := by
  intro g hg; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg; exact h i

theorem pinC_deg (c : ℕ) : (pinC (F := F) c).degree ≤ 2 := by
  have := sumList_deg1 ((List.range 17).filter fun s => decide (s ∉ actC c)) (cv (F := F)) fun _ => le_refl _
  simp only [pinC, CoeffExpr.degree]; omega

/-- **Every compute side gate has degree `≤ 4`** (`3` for E2, `2` for E3). -/
theorem canonCGates_deg : ∀ g ∈ canonCGates (F := F), g.degree ≤ 4 := by
  intro g hg
  unfold canonCGates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega
  · exact deg_map (fun c => (pinC_deg c).trans (by norm_num)) g hg

/-! ### Cell: `canonM` (`134` round-0 columns + `200` aux) -/

namespace SideM
/-- First aux column. -/
def A : ℕ := 134
def bLh (i : ℕ) : ℕ := A + i
def bLl (i : ℕ) : ℕ := A + 32 + i
def bRh (i : ℕ) : ℕ := A + 64 + i
def bRl (i : ℕ) : ℕ := A + 96 + i
def tL : ℕ := A + 128
def tR : ℕ := A + 129
def s (k : ℕ) : ℕ := A + 130 + k
def d (i : ℕ) : ℕ := A + 138 + i
end SideM

open SideM in
/-- `Σ_{i<n} 2^i · next (base + i)`. -/
def bitSumN (base n : ℕ) : CoeffExpr F :=
  CoeffExpr.sumList (List.range n) fun i => .mul (.const ((2 : F) ^ i)) (nv (base + i))

/-- The 8-component sort key `(hi, lo, wL, xLh, xLl, wR, xRh, xRl)` at the current row. -/
def keyC (k : ℕ) : CoeffExpr F :=
  match k with
  | 0 => cv Cell.hi | 1 => cv Cell.lo | 2 => cv Cell.wL | 3 => bitSum (SideM.bLh 0) 32
  | 4 => bitSum (SideM.bLl 0) 32 | 5 => cv Cell.wR | 6 => bitSum (SideM.bRh 0) 32 | _ => bitSum (SideM.bRl 0) 32

/-- The sort key at the next row. -/
def keyN (k : ℕ) : CoeffExpr F :=
  match k with
  | 0 => nv Cell.hi | 1 => nv Cell.lo | 2 => nv Cell.wL | 3 => bitSumN (SideM.bLh 0) 32
  | 4 => bitSumN (SideM.bLl 0) 32 | 5 => nv Cell.wR | 6 => bitSumN (SideM.bRh 0) 32 | _ => bitSumN (SideM.bRl 0) 32

/-- One child side: `x = w·id + (1−w)·a` split as `2^32·h + l`; `h = 2^32 − 1 ⇒ l = 0` through the canonical
inverse-or-zero `t` of `h − (2^32−1)`; E1 `(1−w)·id`, `w·a`; E2 `(1 − w + w·kb)·inv`. -/
def sideM (w id a kb inv h l t : ℕ) : List (CoeffExpr F) :=
  let z : CoeffExpr F := .sub (bitSum h 32) (.const ((2 : F) ^ 32 - 1))
  let zt : CoeffExpr F := .sub (.mul z (cv t)) (.const 1)
  [ .sub (.add (.mul (cv w) (cv id)) (.mul (notE (cv w)) (cv a)))
      (.add (.mul (.const ((2 : F) ^ 32)) (bitSum h 32)) (bitSum l 32)),
    .mul z zt, .mul (cv t) zt, .mul (notE (.mul z (cv t))) (bitSum l 32),
    .mul (notE (cv w)) (cv id), .mul (cv w) (cv a),
    .mul (.add (notE (cv w)) (.mul (cv w) (cv kb))) (cv inv) ]

open SideM in
/-- **The cell side gates (with the pins E1, E2)**: booleanity of the `128` limb bits, the one-hot `s` and the `62`
difference bits; both child sides; the adjacent-row strict lexicographic order (masked by `1 − isL`); `s`, `d`
pinned `0` on the last row. -/
def canonMGates : List (CoeffExpr F) :=
  ((List.range 128).map fun i => boolE (cv (A + i))) ++
  ((List.range 70).map fun i => boolE (cv (A + 130 + i))) ++
  sideM Cell.wL Cell.idL Cell.aL CellTwinK.kbL CellTwinK.invL (bLh 0) (bLl 0) tL ++
  sideM Cell.wR Cell.idR Cell.aR CellTwinK.kbR CellTwinK.invR (bRh 0) (bRl 0) tR ++
  [ .mul (notE (cv Cell.isL)) (.sub (CoeffExpr.sumList (List.range 8) fun k => cv (s k)) (.const 1)),
    .mul (notE (cv Cell.isL)) (.sub (.sub (CoeffExpr.sumList (List.range 8) fun k =>
      .mul (cv (s k)) (.sub (keyN k) (keyC k))) (.const 1)) (bitSum (d 0) 62)) ] ++
  ((List.range 7).map fun j => .mul (.mul (notE (cv Cell.isL))
    (CoeffExpr.sumList ((List.range 8).filter fun k => decide (j < k)) fun k => cv (s k))) (.sub (keyN j) (keyC j))) ++
  ((List.range 8).map fun k => .mul (cv Cell.isL) (cv (s k))) ++
  ((List.range 62).map fun i => .mul (cv Cell.isL) (cv (d i)))

theorem bitSumN_deg (base n : ℕ) : (bitSumN (F := F) base n).degree ≤ 1 :=
  sumList_deg1 _ _ fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega

theorem keyC_deg (k : ℕ) : (keyC (F := F) k).degree ≤ 1 := by
  unfold keyC; split <;> first | exact bitSum_degree_le1 _ _ | (simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega)

theorem keyN_deg (k : ℕ) : (keyN (F := F) k).degree ≤ 1 := by
  unfold keyN; split <;> first | exact bitSumN_deg _ _ | (simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega)

theorem sideM_deg (w id a kb inv h l t : ℕ) : ∀ g ∈ sideM (F := F) w id a kb inv h l t, g.degree ≤ 4 := by
  have hh := bitSum_degree_le1 (F := F) h 32
  have hl := bitSum_degree_le1 (F := F) l 32
  intro g hg
  simp only [sideM, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega)

/-- **Every cell side gate has degree `≤ 4`** (at most `3`). -/
theorem canonMGates_deg : ∀ g ∈ canonMGates (F := F), g.degree ≤ 4 := by
  have hs : ∀ (l : List ℕ), (CoeffExpr.sumList l fun k => cv (F := F) (SideM.s k)).degree ≤ 1 :=
    fun l => sumList_deg1 l _ fun _ => le_refl _
  have hd := bitSum_degree_le1 (F := F) (SideM.d 0) 62
  have hcmp : (CoeffExpr.sumList (List.range 8) fun k =>
      (CoeffExpr.mul (cv (SideM.s k)) (.sub (keyN k) (keyC k)) : CoeffExpr F)).degree ≤ 2 :=
    CoeffExpr.degree_sumList_le _ _ 2 fun k _ => by
      have := keyN_deg (F := F) k; have := keyC_deg (F := F) k; simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega
  unfold canonMGates
  refine deg_app (deg_app (deg_app (deg_app (deg_app (deg_app (deg_app ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact deg_map fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega
  · exact deg_map fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega
  · exact sideM_deg _ _ _ _ _ _ _ _
  · exact sideM_deg _ _ _ _ _ _ _ _
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl
    · have := hs (List.range 8); simp only [CoeffExpr.degree, cv, nv, notE, boolE] at *; omega
    · simp only [CoeffExpr.degree, cv, nv, notE, boolE] at *; omega
  · exact deg_map fun j => by
      have := hs ((List.range 8).filter fun k => decide (j < k))
      have := keyN_deg (F := F) j; have := keyC_deg (F := F) j; simp only [CoeffExpr.degree, cv, nv, notE, boolE] at *; omega
  · exact deg_map fun k => by simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega
  · exact deg_map fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE]; omega

/-! ### Walk: `canonW` (`25` round-0 columns + `32` aux) -/

/-- First walk aux column: `dr` bits `25..55`, `y` at `56`. -/
def wA : ℕ := 25
def wy : ℕ := 56

/-- The consecutive-roots mask `(1 − isL)·rM·rM'`. -/
def rootPairW : CoeffExpr F := .mul (.mul (notE (cv WChip.isL)) (cv WChip.rM)) (nv WChip.rM)

/-- **The walk side gates**: consecutive roots have strictly increasing `ridx`
(`(1−isL)·rM·rM'·(ridx' − ridx − 1 − Σ 2^i dr_i)`, `dr` boolean, `dr = 0` off that mask); `isL·qinv`;
the depth gadget `y = b5(1−b2)(1−b3)`, `y(1−b4)(1−b0 b1)`. -/

def canonWGates : List (CoeffExpr F) :=
  let m : CoeffExpr F := rootPairW
  ((List.range 31).map fun i => boolE (cv (wA + i))) ++
  [ .mul m (.sub (.sub (.sub (nv WChip.ridx) (cv WChip.ridx)) (.const 1)) (bitSum wA 31)) ] ++
  ((List.range 31).map fun i => .mul (notE m) (cv (wA + i))) ++
  [ .mul (cv WChip.isL) (cv WChip.qinv),
    .sub (cv wy) (.mul (.mul (WChip.bt 5) (notE (WChip.bt 2))) (notE (WChip.bt 3))),
    .mul (.mul (cv wy) (notE (WChip.bt 4))) (notE (.mul (WChip.bt 0) (WChip.bt 1))) ]

/-- **Every walk side gate has degree `≤ 4`** (the root-order gate and its `dr` pins are exactly `4`). -/
theorem canonWGates_deg : ∀ g ∈ canonWGates (F := F), g.degree ≤ 4 := by
  have hb := bitSum_degree_le1 (F := F) wA 31
  unfold canonWGates
  refine deg_app (deg_app (deg_app (deg_map fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE, rootPairW]; omega) ?_) (deg_map fun i => by simp only [CoeffExpr.degree, cv, nv, notE, boolE, rootPairW]; omega)) ?_
  · intro g hg
    rcases List.mem_singleton.mp hg with rfl
    simp only [CoeffExpr.degree, cv, nv, notE, boolE, rootPairW]; omega
  · intro g hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> (simp only [CoeffExpr.degree, cv, nv, notE, boolE, rootPairW, WChip.bt]; omega)

/-! ### The templates (one round, base columns only) -/

/-- A one-round, base-only side template of `w` columns. -/
def sideT (w : ℕ) (gs : List (CoeffExpr F)) (hd : ∀ g ∈ gs, g.degree ≤ 4) :
    ChipTemplate F where
  rounds := 1
  rounds_pos := by decide
  baseColsOf := ![w]
  extColsOf := ![0]
  baseTransition := gs
  extTransition := []
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := hd
  extTransition_deg := by simp
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem sideT_width (w : ℕ) (gs : List (CoeffExpr F)) (hd) : (sideT w gs hd).width 3 = w := by
  show (∑ r : Fin 1, (![w] : Fin 1 → ℕ) r) + (∑ r : Fin 1, (![0] : Fin 1 → ℕ) r) * 3 = w
  simp

def canonCT : ChipTemplate F := sideT 69 canonCGates canonCGates_deg
def canonMT : ChipTemplate F := sideT 334 canonMGates canonMGates_deg
def canonWT : ChipTemplate F := sideT 57 canonWGates canonWGates_deg

theorem canonCT_width : (canonCT (F := F)).width 3 = 69 := sideT_width _ _ _
theorem canonMT_width : (canonMT (F := F)).width 3 = 334 := sideT_width _ _ _
theorem canonWT_width : (canonWT (F := F)).width 3 = 57 := sideT_width _ _ _

end Side

/-! ### The side RAPs and the side traces -/

section SideRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (b : Basis (Fin 3) (ZMod p) K)

/-- **`canonC`** over the compute rows. -/
def canonC (Pb : PubJ8 p) : RAP (ZMod p) :=
  expandChip canonCT b (fun _ => 0) (fun _ => 0) Pb.orbit (rowNodeSet Pb.nodes)
/-- **`canonM`** over the cell rows. -/
def canonM (Pb : PubJ8 p) : RAP (ZMod p) :=
  expandChip canonMT b (fun _ => 0) (fun _ => 0) Pb.orbitC (rowNodeSet Pb.nodesC)
/-- **`canonW`** over the J-8 walk rows. -/
def canonW (Pb : PubJ8 p) : RAP (ZMod p) :=
  expandChip canonWT b (fun _ => 0) (fun _ => 0) Pb.orbitW (rowNodeSet Pb.nodesW)

/-- The compute side trace: round-0 columns `0..68`. -/
def sideCQ (tr : TrJ8 (ZMod p)) : Fin ((canonCT (F := ZMod p)).width 3) → (ZMod p)[X] := fun j =>
  tr.C ⟨j, by have := j.isLt; have h2 := canonCT_width (F := ZMod p); omega⟩

/-- The cell side trace: round-0 columns `0..133`, then the `200` aux columns. -/
def sideMQ (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) : Fin ((canonMT (F := ZMod p)).width 3) → (ZMod p)[X] :=
  fun j => if h : (j : ℕ) < 134 then tr.M ⟨j, by omega⟩ else
    ax.M ⟨j - 134, by have := j.isLt; have h2 := canonMT_width (F := ZMod p); omega⟩

/-- The walk side trace: round-0 columns `0..24`, then the `32` aux columns. -/
def sideWQ (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) : Fin ((canonWT (F := ZMod p)).width 3) → (ZMod p)[X] :=
  fun j => if h : (j : ℕ) < 25 then tr.W ⟨j, by omega⟩ else
    ax.W ⟨j - 25, by have := j.isLt; have h2 := canonWT_width (F := ZMod p); omega⟩

end SideRAP

/-! ## 5. `CanonP1`, `AcceptsCanon`, soundness by implication -/

section Canon
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {g : ℕ}

/-- **The canonicalising conjuncts** at the claim `c`, the layout `Pb`, the message, the trace and the aux. -/
structure CanonP1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (c : P8PublicClaim)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) : Prop where
  hfrag : P1FragC c
  hPb : Pb = canonPb hpG sz c
  hdeg : DegOK Pb tr ax
  hC : (canonC b Pb).Satisfies (sideCQ tr)
  hM : (canonM b Pb).Satisfies (sideMQ tr ax)
  hW : (canonW b Pb).Satisfies (sideWQ tr ax)
  hV0 : tr.V = fun _ => 0
  hApad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j)
  hmsg : MsgSupp c M

/-- **`AcceptsCanon`** = the J-8 verifier's checks and the canonicalising conjuncts. -/
def AcceptsCanon (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (Rg : Nock.Jet.Registry)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))
    (r : RowsJ8) (g : ℕ) : Prop :=
  AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g ∧ CanonP1 δ b hpG sz Pb c M tr ax

open Classical in
/-- **Soundness of `AcceptsCanon`**, by implication into `probJ8V_final_clean`: the false-acceptance event of
`AcceptsCanon` is contained in that of `AcceptsJ8V`. -/
theorem probP1_final_clean [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ8 p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (sz : P8PublicClaim → SizesP1)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ (M : MsgJ8' p K δ) (ax : AuxP1 (ZMod p)), AcceptsCanon δ b hpG sz Pb Rg c χ M (Q χ) ax r g) ∧
          ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  refine lt_of_le_of_lt ?_ (CleanJ8.probJ8V_final_clean δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW
    hLA hLV hnM hreg)
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun χ hχ => ?_)) (by positivity)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
  obtain ⟨⟨M, ax, hacc, -⟩, hn⟩ := hχ
  exact ⟨⟨M, hacc⟩, hn⟩

end Canon

/-! ## 6. The χ-dependent-target generalisation -/

section Prob
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {Tr : Type}
  {St : (Coins Φ K → Tr) → Prop}

open Classical in
/-- **`prob_le_of_outside'`**: as `ProbJ8.prob_le_of_outside`, with a target `Holds χ` that may depend on the coin. -/
theorem prob_le_of_outside' (L : List (BadSummand Φ K Tr St)) (Q : Coins Φ K → Tr) (hQ : St Q)
    (Acc Holds : Coins Φ K → Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ L, ¬ s.mem (Q χ) χ) → Holds χ) :
    ((Finset.univ.filter fun χ : Coins Φ K => Acc χ ∧ ¬ Holds χ).card : ℚ) / Fintype.card (Coins Φ K) ≤
      epsilonOf L := by
  have hpos : (0 : ℚ) ≤ Fintype.card (Coins Φ K) := by positivity
  refine le_trans (div_le_div_of_nonneg_right ?_ hpos) (union_prob_le L Q hQ)
  refine Nat.cast_le.mpr (Finset.card_le_card fun χ hχ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
  simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hno
  push Not at hno
  exact hχ.2 (hsound χ hχ.1 hno)

end Prob

section Fig
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

open Classical in
/-- **`probJ8X_lt_155_census32'`**: the J-8 figure `< 2^-155` with a χ-dependent target. -/
theorem probJ8X_lt_155_census32' (X : DataJ8X (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc Holds : Coins frameJ8 K → Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8X X, ¬ s.mem (Q χ) χ) → Holds χ)
    (hcK : Fintype.card K = VclL.Events.cK) (h : RowsLe r EncInjJ8.cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds χ).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside' _ Q hQ Acc Holds hsound) (RepriceJ8.epsJ8X_lt_155_census32 X hcK h hP hg)

end Fig

/-! ## 7. Uniqueness -/

section Unique
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {P g' : ℕ}

/-- The canonical triple type: trace, aux, message. -/
abbrev TripP1 (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p) :=
  TrJ8 (ZMod p) × AuxP1 (ZMod p) × MsgJ8' p K δ

/-- **The characterisation to be proved** (`canon_eq`): outside every J-8 event of `X` at the trace, an accepted
canonical triple IS the canonical one. -/
def CanonEqP1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (Rg : Nock.Jet.Registry)
    (c : P8PublicClaim) (r : RowsJ8) (g : ℕ)
    (X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g')
    (canonOf : Coins frameJ8 K → TripP1 p K δ) : Prop :=
  ∀ (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)),
    (∀ s ∈ allJ8X X, ¬ s.mem tr χ) → AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g → (tr, ax, M) = canonOf χ

/-- **`trace_unique_good`**: two accepted canonical triples at one good coin are equal. -/
theorem trace_unique_good {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {g : ℕ}
    {X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g'}
    {canonOf : Coins frameJ8 K → TripP1 p K δ} (hcanon : CanonEqP1 δ b hpG sz Pb Rg c r g X canonOf)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) (hg' : ∀ s ∈ allJ8X X, ¬ s.mem tr' χ) :
    (tr, ax, M) = (tr', ax', M') :=
  (hcanon χ M tr ax hg h).trans (hcanon χ M' tr' ax' hg' h').symm

open Classical in
/-- **`trace_unique_prob`**: along any staged strategy, `Pr_χ[AcceptsCanon (Q χ) ∧ Q χ ≠ canonOf χ] < 2^-155`,
with the J-8 events and figure, from the characterisation `CanonEqP1`. -/
theorem trace_unique_prob (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p)
    (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (r : RowsJ8) (g : ℕ)
    (X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g')
    (canonOf : Coins frameJ8 K → TripP1 p K δ) (hcanon : CanonEqP1 δ b hpG sz Pb Rg c r g X canonOf)
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1)
    (hcK : Fintype.card K = VclL.Events.cK) (h : RowsLe r EncInjJ8.cornerC) (hP : P ≤ 2 ^ 66)
    (hg : g' ≤ 2 ^ 32) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanon δ b hpG sz Pb Rg c χ (Q χ).2.2 (Q χ).1 (Q χ).2.1 r g ∧ ¬ (Q χ = canonOf χ)).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have H := probJ8X_lt_155_census32' X (fun χ => (Q χ).1) hQ
    (fun χ => AcceptsCanon δ b hpG sz Pb Rg c χ (Q χ).2.2 (Q χ).1 (Q χ).2.1 r g) (fun χ => Q χ = canonOf χ)
    (fun χ hacc hout => hcanon χ (Q χ).2.2 (Q χ).1 (Q χ).2.1 hout hacc) hcK h hP hg
  convert H

end Unique

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.orderOf_omegaG
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.canonPb
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.canonCGates_deg
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.canonMGates_deg
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.canonWGates_deg
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.trJ_zero_of_degOK
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.probP1_final_clean
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.prob_le_of_outside'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.probJ8X_lt_155_census32'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.trace_unique_good
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1.trace_unique_prob
