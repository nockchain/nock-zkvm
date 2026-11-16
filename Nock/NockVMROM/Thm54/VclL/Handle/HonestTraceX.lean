/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestTraceX.lean

  **The honest full trace of
  `computeChipVCLHX` (123) on a generated `NTree SkelX` tree, and its acceptance.**

  * §1 `okC` / `okM`: Boolean read predicates on `CoeffExpr` / `MixedExpr` (generic in the field), and
    `eval_okC` / `eval_okM`: two environments that agree on every admitted read evaluate equally.
  * §2 the trace, in three stages so nothing is circular:
    - `baseT` — columns `< 69`: `colX` of BFS row `j + 1` with the first / last flags;
    - `preT` — columns `69..92`: Re / Im limbs of each `slotsX` slot's `A · D⁻¹` (`invV`) at the base
      environment `env0`;
    - `trX` — columns `93..110`: limbs of the exclusive prefix sums `accV` of the six accumulator terms
      at the pre-trace environment `env1`; columns `111..122`: limbs of the walk values at BFS row `j + 1`.
  * §3 the limb readings (`limb_inv`, `limb_invIm`, `trX_acc`, `limb_walk`).
  * §4 the read-set facts (by `rfl` on the template): slot `D / A` read only columns `< 69` and coins;
    accumulator activities read only columns `< 69`; inverse limbs lie below `93`; arithmetic / equality
    gates read only columns `< 69` and publics; the walk gates read the walk / label columns, two coins
    and three publics, and every walk gate that reads the next row is scaled by `1 − isLast`.
  * §5 `polyX` (Lagrange interpolation) and **`computeChipVCLHX_honest_sat`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSatX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.HonestTraceX

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS mapC mapM chalAlphaW chalGammaW pubIC pubSeed
  pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX rowOKX_of_genX)

noncomputable section

/-! ## 1. Read predicates and congruence -/

section Reads

/-- Every variable a base expression reads is admitted by `ok`. -/
def okC {F : Type} (ok : VarKind → ℕ → Bool) : CoeffExpr F → Bool
  | .const _ => true
  | .var k i => ok k i
  | .add a b => okC ok a && okC ok b
  | .sub a b => okC ok a && okC ok b
  | .mul a b => okC ok a && okC ok b
  | .neg a => okC ok a
  | .pow a _ => okC ok a

/-- Every `𝕂` leaf is admitted by `okK`, every base leaf by `okF`. -/
def okM {F : Type} (okK okF : VarKind → ℕ → Bool) : MixedExpr F → Bool
  | .Var k i => okK k i
  | .Lift g => okC okF g
  | .Scale g u => okC okF g && okM okK okF u
  | .Const _ => true
  | .Add a b => okM okK okF a && okM okK okF b
  | .Sub a b => okM okK okF a && okM okK okF b
  | .Neg a => okM okK okF a
  | .Mul a b => okM okK okF a && okM okK okF b
  | .Pow a _ => okM okK okF a

/-- The value an environment gives a variable. -/
def envAt {G : Type} (e : Env G) : VarKind → ℕ → G
  | .traceCur, i => e.trace i
  | .traceNext, i => e.traceNext i
  | .challenge, i => e.chal i
  | .publicVal, i => e.pub i

theorem okC_mapC {F G : Type} [Field F] (φ : G → F) (ok : VarKind → ℕ → Bool) (g : CoeffExpr G) :
    okC ok (mapC φ g) = okC ok g := by
  induction g <;> simp [okC, mapC, *]

theorem okM_mapM {F G : Type} [Field F] (φ : G → F) (okK okF : VarKind → ℕ → Bool) (g : MixedExpr G) :
    okM okK okF (mapM φ g) = okM okK okF g := by
  induction g <;> simp [okM, mapM, okC_mapC, *]

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem eval_okC (ok : VarKind → ℕ → Bool) (g : CoeffExpr F) (h : okC ok g = true) (e1 e2 : Env F)
    (he : ∀ k i, ok k i = true → envAt e1 k i = envAt e2 k i) : g.eval e1 = g.eval e2 := by
  induction g with
  | const c => rfl
  | var k i => have := he k i h; cases k <;> exact this
  | add a b iha ihb =>
    simp only [okC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | sub a b iha ihb =>
    simp only [okC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | mul a b iha ihb =>
    simp only [okC, Bool.and_eq_true] at h; simp only [CoeffExpr.eval, iha h.1, ihb h.2]
  | neg a ih => simp only [okC] at h; simp only [CoeffExpr.eval, ih h]
  | pow a n ih => simp only [okC] at h; simp only [CoeffExpr.eval, ih h]

theorem eval_okM (okK okF : VarKind → ℕ → Bool) (g : MixedExpr F) (h : okM okK okF g = true)
    (eK1 eK2 : Env K) (eF1 eF2 : Env F)
    (hK : ∀ k i, okK k i = true → envAt eK1 k i = envAt eK2 k i)
    (hF : ∀ k i, okF k i = true → envAt eF1 k i = envAt eF2 k i) :
    g.eval eK1 eF1 = g.eval eK2 eF2 := by
  induction g with
  | Var k i => have := hK k i h; cases k <;> exact this
  | Lift g => simp only [okM] at h; simp only [MixedExpr.eval, eval_okC okF g h eF1 eF2 hF]
  | Scale g u ih =>
    simp only [okM, Bool.and_eq_true] at h
    simp only [MixedExpr.eval, eval_okC okF g h.1 eF1 eF2 hF, ih h.2]
  | Const c => rfl
  | Add a b iha ihb =>
    simp only [okM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Sub a b iha ihb =>
    simp only [okM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Neg a ih => simp only [okM] at h; simp only [MixedExpr.eval, ih h]
  | Mul a b iha ihb =>
    simp only [okM, Bool.and_eq_true] at h; simp only [MixedExpr.eval, iha h.1, ihb h.2]
  | Pow a n ih => simp only [okM] at h; simp only [MixedExpr.eval, ih h]

/-- `evalQX` is the evaluation of the cast template. -/
theorem eval_mapC_castX (g : CoeffExpr ℚ) (env : Env F) :
    (mapC (fun q : ℚ => (q : F)) g).eval env = evalQX g env := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQX, iha, ihb]
  | sub a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQX, iha, ihb]
  | mul a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQX, iha, ihb]
  | neg a iha => simp only [mapC, CoeffExpr.eval, evalQX, iha]
  | pow a n iha => simp only [mapC, CoeffExpr.eval, evalQX, iha]

end Reads

/-! ### The admitted read sets -/

/-- Slot `D / A`, `𝕂` side: coins only. -/
def okKs : VarKind → ℕ → Bool
  | .challenge, _ => true
  | _, _ => false

/-- Columns `< 69` of the current row. -/
def okFs : VarKind → ℕ → Bool
  | .traceCur, i => decide (i < 69)
  | _, _ => false

/-- Base gates: current columns `< 69` and the publics. -/
def okB : VarKind → ℕ → Bool
  | .traceCur, i => decide (i < 69)
  | .publicVal, _ => true
  | _, _ => false

/-- Walk gates, `𝕂` side: the walk columns, the walk coins and the walk publics. -/
def okKw : VarKind → ℕ → Bool
  | .traceCur, i => i == 111 || i == 114 || i == 117 || i == 120
  | .traceNext, i => i == 111 || i == 114 || i == 117
  | .challenge, i => i == 6 || i == 9
  | .publicVal, i => i == 6 || i == 9 || i == 12

/-- Walk gates, base side: current / next columns `< 69`. -/
def okFw : VarKind → ℕ → Bool
  | .traceCur, i => decide (i < 69)
  | .traceNext, i => decide (i < 69)
  | _, _ => false

/-- The current-row-only restrictions. -/
def okKc : VarKind → ℕ → Bool
  | .traceNext, _ => false
  | k, i => okKw k i

def okFc : VarKind → ℕ → Bool
  | .traceCur, i => decide (i < 69)
  | _, _ => false

/-- A gate scaled by `1 − isLast` (`notC lastX`). -/
def isNLX : MixedExpr ℚ → Bool
  | .Scale (.sub (.const c) (.var .traceCur i)) _ => decide (c = 1) && i == 18
  | _ => false

theorem isNLX_eq (g : MixedExpr ℚ) (h : isNLX g = true) :
    ∃ u, g = MixedExpr.Scale (.sub (.const 1) (.var .traceCur 18)) u := by
  match g, h with
  | .Scale (.sub (.const c) (.var .traceCur i)) u, h =>
    simp only [isNLX, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨u, rfl⟩

/-! ## 2. The trace -/

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- Coordinate `j` of `x` (zero off `[0, 3)`). -/
def cNA (x : K) (j : ℕ) : F := if h : j < 3 then coord b x ⟨j, h⟩ else 0

variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
  (chalV pubVal : ℕ → F)

/-- The first-row flag of chip row `j` (BFS row `j + 1`). -/
def flX (j : ℕ) : F := if j + 1 = 1 then 1 else 0
/-- The last-row flag of chip row `j`. -/
def llX (j : ℕ) : F := if j + 1 = W.length then 1 else 0

/-- **Stage 1**: the honest round-0 columns `< 69` of chip row `j` (`colX` of BFS row `j + 1`). -/
def baseT (j c : ℕ) : F := colX H pd (rowAtWX W (j + 1)) (flX j) (llX W j) c

/-- The stage-1 environment of chip row `j`. -/
def env0 (j : ℕ) : Env F := ⟨baseT H pd W j, baseT H pd W (j + 1), chalV, pubVal⟩

/-- **The honest `𝕂′` slot inverse** `A · D⁻¹` of chip row `j`, read at `env0`. -/
def invV (j : ℕ) (S : SlotX F) : 𝕂′ :=
  aVal b δ S (env0 H pd W chalV pubVal j) * (dVal b δ S (env0 H pd W chalV pubVal j))⁻¹

/-- The slot by index (`inv0X.. inv3X`). -/
def slotAt : ℕ → SlotX F
  | 0 => slot0X
  | 1 => slot1X
  | 2 => slot2X
  | _ => slot3X

/-- The inverse limbs `69..92`: slot `(c − 69) / 6`, Re on offsets `0..2`, Im on `3..5`. -/
def invCol (j c : ℕ) : F :=
  if (c - 69) % 6 < 3 then
    cNA b (Quad.re _ (invV b δ H pd W chalV pubVal j (slotAt ((c - 69) / 6)))) ((c - 69) % 6)
  else cNA b (Quad.im _ (invV b δ H pd W chalV pubVal j (slotAt ((c - 69) / 6)))) ((c - 69) % 6 - 3)

/-- **Stage 2**: columns `< 93` (base and slot inverses). -/
def preT (j c : ℕ) : F :=
  if c < 69 then baseT H pd W j c else if c < 93 then invCol b δ H pd W chalV pubVal j c else 0

/-- The stage-2 environment of chip row `j`. -/
def env1 (j : ℕ) : Env F :=
  ⟨preT b δ H pd W chalV pubVal j, preT b δ H pd W chalV pubVal (j + 1), chalV, pubVal⟩

/-- The six accumulators (`accOf` order): export Re / Im, path Re / Im, service Re / Im. -/
def accSpec : ℕ → Bal × Bool
  | 0 => (.x, false)
  | 1 => (.x, true)
  | 2 => (.p, false)
  | 3 => (.p, true)
  | 4 => (.s, false)
  | _ => (.s, true)

/-- The terminal public of accumulator `a`. -/
def pubOfA : ℕ → ℕ
  | 0 => pubRhoX
  | 1 => pubRhoXIm
  | 2 => pubRhoP
  | 3 => pubRhoPIm
  | 4 => pubRhoSX
  | _ => pubRhoSXi

/-- The `ℚ`-template slots of accumulator `(bl, im)` (as in `accOf`). -/
def slotsQ (bl : Bal) (im : Bool) : List (Slot ℚ) :=
  (Handle.ChipHX.slotsX (F := ℚ)).map fun S => ⟨S.actB bl, if im then S.invIm else S.inv⟩

/-- The cast slots. -/
def slotsF (bl : Bal) (im : Bool) : List (Slot F) :=
  (slotsQ bl im).map Nock.NockVMROM.Thm54.VclL.Handle.castSlot

/-- **The exclusive prefix sum** of accumulator `a`'s per-row terms at the pre-trace. -/
def accV (a i : ℕ) : K :=
  ∑ j ∈ Finset.range i, termVal b (slotsF (accSpec a).1 (accSpec a).2) (env1 b δ H pd W chalV pubVal j)

/-- The four walk values (`ln, count, acc, walk_inv`) at BFS row `i`. -/
def walkV (ln cnt acc : ℕ → K) : ℕ → ℕ → K
  | 0, i => ln i
  | 1, i => cnt i
  | 2, i => acc i
  | _, i => (cnt i - ln i)⁻¹

variable (ln cnt acc : ℕ → K)

/-- **The honest full trace of `computeChipVCLHX`** (row `j`, column `c`; `0` for `c ≥ 123`). -/
def trX (j c : ℕ) : F :=
  if c < 93 then preT b δ H pd W chalV pubVal j c
  else if c < 111 then cNA b (accV b δ H pd W chalV pubVal ((c - 93) / 3) j) ((c - 93) % 3)
  else if c < 123 then cNA b (walkV ln cnt acc ((c - 111) / 3) (j + 1)) ((c - 111) % 3)
  else 0

/-! ## 3. Limb readings -/

theorem trX_base (j c : ℕ) (hc : c < 69) :
    trX b δ H pd W chalV pubVal ln cnt acc j c = baseT H pd W j c := by
  unfold trX preT
  rw [if_pos (by omega), if_pos hc]

theorem trX_pre (j c : ℕ) (hc : c < 93) :
    trX b δ H pd W chalV pubVal ln cnt acc j c = preT b δ H pd W chalV pubVal j c := by
  unfold trX
  rw [if_pos hc]

theorem trX_zero (j c : ℕ) (hc : 123 ≤ c) : trX b δ H pd W chalV pubVal ln cnt acc j c = 0 := by
  unfold trX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem cNA_coord (x : K) (k : Fin 3) : cNA b x k = coord b x k := by
  simp [cNA, k.isLt]

theorem limbVal_of_cNA (f : ℕ → F) (c0 : ℕ) (x : K) (h : ∀ k : Fin 3, f (c0 + k) = cNA b x k) :
    limbVal b f c0 = x := by
  refine limbVal_eq_of_coords b x f c0 fun k => ?_
  rw [h k, cNA_coord]

theorem trX_inv (j s o : ℕ) (hs : s < 4) (ho : o < 6) :
    trX b δ H pd W chalV pubVal ln cnt acc j (69 + 6 * s + o) =
      if o < 3 then cNA b (Quad.re _ (invV b δ H pd W chalV pubVal j (slotAt s))) o
      else cNA b (Quad.im _ (invV b δ H pd W chalV pubVal j (slotAt s))) (o - 3) := by
  have h1 : (69 + 6 * s + o - 69) / 6 = s := by omega
  have h2 : (69 + 6 * s + o - 69) % 6 = o := by omega
  rw [trX_pre _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  unfold preT invCol
  rw [if_neg (by omega), if_pos (by omega), h1, h2]

theorem limb_inv (j s : ℕ) (hs : s < 4) :
    limbVal b (trX b δ H pd W chalV pubVal ln cnt acc j) (69 + 6 * s) =
      Quad.re _ (invV b δ H pd W chalV pubVal j (slotAt s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  rw [trX_inv b δ H pd W chalV pubVal ln cnt acc j s k hs (by omega), if_pos k.isLt]

theorem limb_invIm (j s : ℕ) (hs : s < 4) :
    limbVal b (trX b δ H pd W chalV pubVal ln cnt acc j) (72 + 6 * s) =
      Quad.im _ (invV b δ H pd W chalV pubVal j (slotAt s)) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have e : 72 + 6 * s + (k : ℕ) = 69 + 6 * s + ((k : ℕ) + 3) := by omega
  rw [e, trX_inv b δ H pd W chalV pubVal ln cnt acc j s _ hs (by omega), if_neg (by omega)]
  simp

theorem trX_acc (j a : ℕ) (ha : a < 6) (k : Fin 3) :
    trX b δ H pd W chalV pubVal ln cnt acc j (93 + 3 * a + k) =
      coord b (accV b δ H pd W chalV pubVal a j) k := by
  have h1 : (93 + 3 * a + (k : ℕ) - 93) / 3 = a := by omega
  have h2 : (93 + 3 * a + (k : ℕ) - 93) % 3 = k := by omega
  unfold trX
  rw [if_neg (by omega), if_pos (by omega), h1, h2, cNA_coord]

theorem limb_walk (j w : ℕ) (hw : w < 4) :
    limbVal b (trX b δ H pd W chalV pubVal ln cnt acc j) (111 + 3 * w) = walkV ln cnt acc w (j + 1) := by
  refine limbVal_of_cNA b _ _ _ fun k => ?_
  have h1 : (111 + 3 * w + (k : ℕ) - 111) / 3 = w := by omega
  have h2 : (111 + 3 * w + (k : ℕ) - 111) % 3 = k := by omega
  unfold trX
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2]

end Trace

/-! ## 4. The read-set facts (template computations, `rfl`) and the congruences -/

section Facts

theorem slotsDA_ok {F : Type} [Field F] (δ : F) : (Handle.ChipHX.slotsX (F := F)).all (fun S =>
    okM okKs okFs (slotDQ F δ S).1 && okM okKs okFs (slotDQ F δ S).2 &&
    okM okKs okFs (slotAQ F δ S).1 && okM okKs okFs (slotAQ F δ S).2) = true := by
  rfl

theorem slotsAct_ok : (Handle.ChipHX.slotsX (F := ℚ)).all (fun S =>
    okC okFs (S.actB .x) && okC okFs (S.actB .p) && okC okFs (S.actB .s) &&
    decide (S.inv + 3 ≤ 93) && decide (S.invIm + 3 ≤ 93)) = true := by
  rfl

theorem arith_ok : (arithGatesX (F := ℚ)).all (okC okB) = true := by rfl

theorem eq_ok : (eqGatesX (F := ℚ)).all (fun g => okC okB g.gate) = true := by rfl

theorem walk_ok : (walkGatesX (F := ℚ)).all (okM okKw okFw) = true := by rfl

theorem walk_shape : (walkGatesX (F := ℚ)).all (fun g => okM okKc okFc g || isNLX g) = true := by rfl

end Facts

section Cong
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem slot_ok {S : SlotX F} (hS : S ∈ Handle.ChipHX.slotsX (F := F)) :
    okM okKs okFs (slotDQ F δ S).1 = true ∧ okM okKs okFs (slotDQ F δ S).2 = true ∧
    okM okKs okFs (slotAQ F δ S).1 = true ∧ okM okKs okFs (slotAQ F δ S).2 = true := by
  have h := List.all_eq_true.mp (slotsDA_ok δ) S hS
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The slot `D / A` read only columns `< 69` and the coins** (compiled: `slotsDA_ok`). -/
theorem dVal_aVal_congr {S : SlotX F} (hS : S ∈ Handle.ChipHX.slotsX (F := F)) (e1 e2 : Env F)
    (htr : ∀ c < 69, e1.trace c = e2.trace c) (hch : e1.chal = e2.chal) :
    dVal b δ S e1 = dVal b δ S e2 ∧ aVal b δ S e1 = aVal b δ S e2 := by
  obtain ⟨h1, h2, h3, h4⟩ := slot_ok δ hS
  have hK : ∀ k i, okKs k i = true → envAt (Compute.TowerD.gatherEnv b e1) k i = envAt (Compute.TowerD.gatherEnv b e2) k i := by
    intro k i hk
    cases k <;> simp [okKs] at hk
    simp [envAt, Compute.TowerD.gatherEnv, hch]
  have hF : ∀ k i, okFs k i = true → envAt e1 k i = envAt e2 k i := by
    intro k i hk
    cases k <;> simp [okFs] at hk
    exact htr i hk
  simp only [dVal, aVal, Q.val]
  rw [eval_okM okKs okFs _ h1 _ _ _ _ hK hF, eval_okM okKs okFs _ h2 _ _ _ _ hK hF,
    eval_okM okKs okFs _ h3 _ _ _ _ hK hF, eval_okM okKs okFs _ h4 _ _ _ _ hK hF]
  exact ⟨rfl, rfl⟩

theorem slotsF_mem {bl : Bal} {im : Bool} {s : Slot F} (hs : s ∈ slotsF (F := F) bl im) :
    ∃ S ∈ Handle.ChipHX.slotsX (F := ℚ),
      s = Nock.NockVMROM.Thm54.VclL.Handle.castSlot ⟨S.actB bl, if im then S.invIm else S.inv⟩ := by
  simp only [slotsF, slotsQ, List.map_map, List.mem_map, Function.comp] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  exact ⟨S, hS, rfl⟩

/-- **An accumulator term reads only columns `< 93`** (compiled: `slotsAct_ok`). -/
theorem termVal_congr (bl : Bal) (im : Bool) (e1 e2 : Env F) (htr : ∀ c < 93, e1.trace c = e2.trace c) :
    termVal b (slotsF bl im) e1 = termVal b (slotsF bl im) e2 := by
  unfold termVal
  congr 1
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨S, hS, rfl⟩ := slotsF_mem hs
  have hf := List.all_eq_true.mp slotsAct_ok S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨hx, hp⟩, hs'⟩, hi⟩, hii⟩ := hf
  have hact : okC okFs (S.actB bl) = true := by cases bl <;> assumption
  have hF : ∀ k i, okFs k i = true → envAt e1 k i = envAt e2 k i := by
    intro k i hk
    cases k <;> simp [okFs] at hk
    exact htr i (by omega)
  have hbase : (if im then S.invIm else S.inv) + 3 ≤ 93 := by split <;> assumption
  have hb2 : (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).invBase = (if im then S.invIm else S.inv) := rfl
  have hev : (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).act.eval e1 =
      (Nock.NockVMROM.Thm54.VclL.Handle.castSlot (F := F)
      ⟨S.actB bl, if im then S.invIm else S.inv⟩).act.eval e2 :=
    eval_okC okFs _ (by
      show okC okFs (mapC (fun q : ℚ => (q : F)) (S.actB bl)) = true
      rw [okC_mapC]; exact hact) e1 e2 hF
  rw [hev, hb2]
  congr 1
  unfold limbVal
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [htr _ (by have := k.isLt; omega)]

/-- **The arithmetic / equality gates read only columns `< 69` and the publics** (compiled:
`arith_ok`, `eq_ok`). -/
theorem evalQX_congr (g : CoeffExpr ℚ) (h : okC okB g = true) (e1 e2 : Env F)
    (htr : ∀ c < 69, e1.trace c = e2.trace c) (hpub : e1.pub = e2.pub) :
    evalQX g e1 = evalQX g e2 := by
  rw [← eval_mapC_castX, ← eval_mapC_castX]
  refine eval_okC okB _ (by rw [okC_mapC]; exact h) e1 e2 fun k i hk => ?_
  cases k <;> simp [okB] at hk
  · exact htr i hk
  · simp [envAt, hpub]

/-- The accumulator gates commute with the constant cast. -/
theorem accGatesX_map (slots : List (Slot ℚ)) (a p : ℕ) :
    (accGatesX slots a p).map (mapC (fun q : ℚ => (q : F))) =
      accGatesX (slots.map Nock.NockVMROM.Thm54.VclL.Handle.castSlot) a p := by
  simp only [accGatesX, List.map_append, List.map_map, Function.comp_def, accInitX, accStepX, accTermX,
    mapC, cc, notC, Nock.NockVMROM.Thm54.VclL.Handle.mapC_termCoord, Rat.cast_one]
  rfl

theorem accGatesHX_mem {g : CoeffExpr ℚ} (hg : g ∈ (accGatesHX : List (CoeffExpr ℚ))) :
    ∃ a < 6, g ∈ accGatesX (slotsQ (accSpec a).1 (accSpec a).2) (93 + 3 * a) (pubOfA a) := by
  simp only [accGatesHX, List.mem_append] at hg
  rcases hg with ((((h | h) | h) | h) | h) | h
  · exact ⟨0, by norm_num, h⟩
  · exact ⟨1, by norm_num, h⟩
  · exact ⟨2, by norm_num, h⟩
  · exact ⟨3, by norm_num, h⟩
  · exact ⟨4, by norm_num, h⟩
  · exact ⟨5, by norm_num, h⟩

theorem slot_index {S : SlotX F} (hS : S ∈ Handle.ChipHX.slotsX (F := F)) :
    ∃ s < 4, S = slotAt s ∧ S.inv = 69 + 6 * s ∧ S.invIm = 72 + 6 * s := by
  simp only [Handle.ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨1, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨2, by norm_num, rfl, rfl, rfl⟩
  · exact ⟨3, by norm_num, rfl, rfl, rfl⟩

end Cong

/-! ## 5. The trace polynomials and the acceptance -/

section Poly
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
  (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) {n : ℕ} (nodes : Fin n → F)

/-- **The honest trace polynomials of `computeChipVCLHX`**. -/
def polyX (w : ℕ) : Fin w → F[X] := fun c =>
  Lagrange.interpolate Finset.univ nodes (fun i : Fin n =>
    trX b δ H pd W chalV pubVal ln cnt acc (i : ℕ) (c : ℕ))

theorem polyX_eval (hinj : Function.Injective nodes) {w : ℕ} (c : Fin w) (i : Fin n) :
    (polyX b δ H pd W chalV pubVal ln cnt acc nodes w c).eval (nodes i) =
      trX b δ H pd W chalV pubVal ln cnt acc (i : ℕ) (c : ℕ) :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem polyX_env_trace (hinj : Function.Injective nodes) {w : ℕ} (hw : 123 ≤ w) (ω : F) (i : Fin n)
    (c : ℕ) :
    (Reify.envOfTrace (polyX b δ H pd W chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).trace c
      = trX b δ H pd W chalV pubVal ln cnt acc (i : ℕ) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc]; exact polyX_eval b δ H pd W chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ i
  · rw [dif_neg hc, trX_zero b δ H pd W chalV pubVal ln cnt acc _ _ (by omega)]

theorem polyX_env_next (hinj : Function.Injective nodes) {w : ℕ} (hw : 123 ≤ w) (ω : F) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = ω * nodes i) (c : ℕ) :
    (Reify.envOfTrace (polyX b δ H pd W chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).traceNext c
      = trX b δ H pd W chalV pubVal ln cnt acc ((i : ℕ) + 1) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc, ← hadj]
    exact polyX_eval b δ H pd W chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ ⟨(i : ℕ) + 1, hi⟩
  · rw [dif_neg hc, trX_zero b δ H pd W chalV pubVal ln cnt acc _ _ (by omega)]

theorem baseT_17 (j : ℕ) : baseT H pd W j 17 = (if j = 0 then 1 else 0 : F) := by
  simp [baseT, colX, flX]

theorem baseT_18 (j : ℕ) : baseT H pd W j 18 = (if j + 1 = W.length then 1 else 0 : F) := by
  simp [baseT, colX, llX]

theorem polyX_first (w : ℕ) (hw : 17 < w) :
    polyX b δ H pd W chalV pubVal ln cnt acc nodes w ⟨17, hw⟩ = firstRowMask nodes := by
  unfold polyX firstRowMask
  congr 1
  funext i
  rw [trX_base b δ H pd W chalV pubVal ln cnt acc _ 17 (by norm_num), baseT_17]

theorem polyX_last (hn : 0 < n) (hN : W.length = n) (w : ℕ) (hw : 18 < w) :
    polyX b δ H pd W chalV pubVal ln cnt acc nodes w ⟨18, hw⟩ = lastRowMask hn nodes := by
  unfold polyX lastRowMask
  congr 1
  funext i
  rw [trX_base b δ H pd W chalV pubVal ln cnt acc _ 18 (by norm_num), baseT_18, hN]
  have : (i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; subst h; simp; omega
    · intro h; apply Fin.ext; simp; omega
  simp only [this]

end Poly

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The honest walk columns (closed forms, as `walkGatesX_honest`). -/
def curW (H : Noun → ℕ × ℕ) (W : List (NTree SkelX)) (γ : K) : ℕ → K :=
  Walk.curCol (nodeValX (F := F) H γ) W
def lnW (α : K) : ℕ → K := lnClosed α
def cntW (W : List (NTree SkelX)) (α : K) : ℕ → K := cntClosed (Walk.foCol W) α α
def accW (H : Noun → ℕ × ℕ) (W : List (NTree SkelX)) (α γ : K) : ℕ → K :=
  accClosed (curW (F := F) H W γ) (Walk.chldCol (nodeValX (F := F) H γ) W) (Walk.foCol W) α
    (curW (F := F) H W γ 1 * α) α

open Classical in
/-- **`computeChipVCLHX` accepts the honest trace `polyX` of a generated tree** (HC3 step 3).

The chip has `n = |W|` rows, `W = bfsForest [t]` the BFS of the generated tree of `genX R m s f`; the
row nodes are injective and `ω`-adjacent.  Hypotheses:
* `hH`, `hp`: the handle map is honest at `ringChar F ≥ 16`;
* `hsm`: the run's small-atom bounds at every node (`SmallX`, per row);
* `hpair`: the op-5 α-pair limb data's local condition (`PairOK`) on every pair row;
* `hord`: the walk coin order;
* `hα hγ hpIC hpS hpO`: the walk coin / public readings (`hpS`: the seed);
* `hpub`: the claim publics `0..5` are the handles of the claim `(s, f, r)` (this discharges `PubOK`);
* `hρ`: the six accumulator terminals are the honest totals;
* `hnb`: the slot pole event does not occur (`D ≠ 0 ∨ A = 0` per slot and row). -/
theorem computeChipVCLHX_honest_sat {R : Registry} {m : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (hgen : genX R m s f = some (t, r))
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)
    (hsm : ∀ u, InTree t u → SmallX (ringChar F) (rowOfSkelX u.label))
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) →
      PairOK (F := F) (pd (rowOfSkelX u.label)))
    (α γ : K) (hord : (bfsForest [t]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = curW (F := F) H (bfsForest [t]) γ 1 * α)
    (hpO : limbVal b pubVal pubOut = 0)
    (hpub : pubVal 0 = hk H s ∧ pubVal 1 = hv H s ∧ pubVal 2 = hk H f ∧ pubVal 3 = hv H f ∧
      pubVal 4 = hk H r ∧ pubVal 5 = hv H r)
    (hρ : ∀ a < 6, ∀ k : Fin 3, pubVal (pubOfA a + k) =
      coord b (accV b δ H pd (bfsForest [t]) chalV pubVal a n) k)
    (hnb : ∀ j < n, ∀ S ∈ Handle.ChipHX.slotsX (F := F),
      dVal b δ S (env0 H pd (bfsForest [t]) chalV pubVal j) ≠ 0 ∨
        aVal b δ S (env0 H pd (bfsForest [t]) chalV pubVal j) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit)
      (polyX b δ H pd (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α)
        (accW (F := F) H (bfsForest [t]) α γ) nodes (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w) := by
  set W := bfsForest [t] with hW
  set ln : ℕ → K := lnW α with hln
  set cnt : ℕ → K := cntW W α with hcnt
  set acc : ℕ → K := accW (F := F) H W α γ with hacc
  set P := polyX b δ H pd W chalV pubVal ln cnt acc nodes
    (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w with hP
  have hw : 123 ≤ (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w := by
    rw [computeChipVCLHX_width]
  have hlen : W.length = n := hN.symm
  have hp0 : 0 < ringChar F := by omega
  have hE0 : ∀ i : Fin n, ∀ c, (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).trace c =
      trX b δ H pd W chalV pubVal ln cnt acc (i : ℕ) c :=
    fun i c => polyX_env_trace b δ H pd W chalV pubVal ln cnt acc nodes hinj hw orbit.ω i c
  have hEn : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), ∀ c,
      (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).traceNext c =
        trX b δ H pd W chalV pubVal ln cnt acc ((i : ℕ) + 1) c :=
    fun i hi c => polyX_env_next b δ H pd W chalV pubVal ln cnt acc nodes hinj hw orbit.ω i hi (hadj i hi) c
  let envs : ℕ → Env F := fun j =>
    if h : j < n then Reify.envOfTrace P orbit.ω (nodes ⟨j, h⟩) chalV pubVal
    else ⟨fun _ => 0, fun _ => 0, chalV, pubVal⟩
  have henv : ∀ i : Fin n, envs i = Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal := by
    intro i; simp [envs, i.isLt]
  have henv_chal : ∀ j, (envs j).chal = chalV := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henv_pub : ∀ j, (envs j).pub = pubVal := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henvT : ∀ j (hj : j < n) c, (envs j).trace c = trX b δ H pd W chalV pubVal ln cnt acc j c := by
    intro j hj c; rw [henv ⟨j, hj⟩]; exact hE0 ⟨j, hj⟩ c
  have henvN : ∀ j (hj : j + 1 < n) c,
      (envs j).traceNext c = trX b δ H pd W chalV pubVal ln cnt acc (j + 1) c := by
    intro j hj c
    have hj' : j < n := by omega
    rw [henv ⟨j, hj'⟩]; exact hEn ⟨j, hj'⟩ hj c
  have henvTr : ∀ j (hj : j < n), (envs j).trace = trX b δ H pd W chalV pubVal ln cnt acc j :=
    fun j hj => funext (henvT j hj)
  -- the rows
  have hin : ∀ j (hj : j < W.length), InTree t (W[j]'hj) := fun j hj =>
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  have hrowW : ∀ j (hj : j < W.length), rowAtWX W (j + 1) = rowOfSkelX (W[j]'hj).label := by
    intro j hj; simp [rowAtWX, List.getElem?_eq_getElem hj]
  have ht0 : W[0]? = some t := by
    rw [hW, Walk.walk_tail_eq t]; rfl
  have hok : ∀ j < n, RowOKX (ringChar F) (rowAtWX W (j + 1)) := by
    intro j hj
    rw [hrowW j (by omega)]
    exact rowOKX_of_genX hgen (hin j _) (hsm _ (hin j _))
  have hpr : ∀ j < n, isPair H (rowAtWX W (j + 1)) → PairOK (F := F) (pd (rowAtWX W (j + 1))) := by
    intro j hj
    rw [hrowW j (by omega)]
    exact hpair _ (hin j _)
  have hpubOK : ∀ j < n, PubOK H (rowAtWX W (j + 1)) (flX j) pubVal := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      right
      have hr1 : rowAtWX W (0 + 1) = rowOfSkelX t.label := by
        show rowAtWX W 1 = _
        simp [rowAtWX, ht0]
      obtain ⟨hs, hf, he, -⟩ := Nock.Edit.GenX.genX_label hgen
      have htr := rowOfSkelX_trip t.label
      simp only [Prod.mk.injEq] at htr
      rw [hr1, htr.1, htr.2.1, htr.2.2, hs, hf, he]
      exact hpub
    · left; simp [flX, h0]
  -- the accumulator terms at the real environments
  have hterm : ∀ a j, j < n → termVal b (slotsF (F := F) (accSpec a).1 (accSpec a).2) (envs j) =
      termVal b (slotsF (accSpec a).1 (accSpec a).2) (env1 b δ H pd W chalV pubVal j) := by
    intro a j hj
    refine termVal_congr b _ _ _ _ fun c hc => ?_
    rw [henvT j hj c, trX_pre b δ H pd W chalV pubVal ln cnt acc j c hc]
    rfl
  have hsum : ∀ a i, i ≤ n → ∑ j ∈ Finset.range i,
      termVal b (slotsF (F := F) (accSpec a).1 (accSpec a).2) (envs j) =
        accV b δ H pd W chalV pubVal a i := by
    intro a i hi
    unfold accV
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hterm a j (lt_of_lt_of_le (Finset.mem_range.mp hj) hi)
  -- the preprocessing binding
  have hbind : (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P := by
    intro j
    fin_cases j
    · exact polyX_first b δ H pd W chalV pubVal ln cnt acc nodes _ (by omega)
    · exact polyX_last b δ H pd W chalV pubVal ln cnt acc nodes hn hlen _ (by omega)
  refine (Handle.HonestSatX.computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mpr
    ⟨hbind, fun x hx g hg => ?_⟩
  have hx' : ∃ i, nodes i = x := by
    classical
    simpa [rowNodeSet] using hx
  obtain ⟨i, rfl⟩ := hx'
  have hin' : (i : ℕ) < n := i.isLt
  have hiW : (i : ℕ) < W.length := by omega
  rw [← henv i]
  -- base agreement of the real row environment
  have hbaseE : ∀ c < 69, (envs i).trace c =
      (hEnvX H pd (rowAtWX W ((i : ℕ) + 1)) (flX (i : ℕ)) (llX W (i : ℕ)) pubVal).trace c := by
    intro c hc
    rw [henvT _ hin' c, trX_base b δ H pd W chalV pubVal ln cnt acc _ c hc]
    rfl
  have hAE := arith_eq_hold H pd (rowAtWX W ((i : ℕ) + 1)) (flX (i : ℕ)) (llX W (i : ℕ)) pubVal hH hp
    (hok _ hin') (hpr _ hin') (hpubOK _ hin')
  simp only [gatesHX, List.mem_append, List.mem_flatMap] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨gw, hgw, hg⟩
  · -- base gates
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simp only [baseGatesHX, List.mem_append] at hg'
    rcases hg' with (ha | hacc') | he
    · rw [eval_mapC_castX, evalQX_congr g' (List.all_eq_true.mp arith_ok g' ha) _ _ hbaseE
        (by rw [henv_pub]; rfl)]
      exact hAE.1 g' ha
    · obtain ⟨a, ha6, hga⟩ := accGatesHX_mem hacc'
      have hmem : mapC (fun q : ℚ => (q : F)) g' ∈
          accGatesX (slotsF (F := F) (accSpec a).1 (accSpec a).2) (93 + 3 * a) (pubOfA a) := by
        rw [slotsF, ← accGatesX_map]; exact List.mem_map_of_mem hga
      refine accGatesX_prefixK b _ (93 + 3 * a) (pubOfA a) n (i : ℕ) hin' envs
        (accV b δ H pd W chalV pubVal a n) ?_ ?_ ?_ ?_ ?_ (hsum a n le_rfl) _ hmem
      · rw [henvT _ hin', trX_base b δ H pd W chalV pubVal ln cnt acc _ 17 (by norm_num), baseT_17]
      · rw [henvT _ hin', trX_base b δ H pd W chalV pubVal ln cnt acc _ 18 (by norm_num), baseT_18, hlen]
      · intro k
        rw [henvT _ hin', trX_acc b δ H pd W chalV pubVal ln cnt acc _ a ha6 k, hsum a _ hin'.le]
      · intro hlt k
        rw [henvN _ hlt, trX_acc b δ H pd W chalV pubVal ln cnt acc _ a ha6 k, hsum a _ (by omega)]
      · intro k; rw [henv_pub]; exact hρ a ha6 k
    · obtain ⟨e, he', rfl⟩ := List.mem_map.mp he
      rw [eval_mapC_castX, evalQX_congr e.gate (List.all_eq_true.mp eq_ok e he') _ _ hbaseE
        (by rw [henv_pub]; rfl)]
      exact hAE.2 e he'
  · -- the four `𝕂′` slot pairs
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
    obtain ⟨sI, hs4, rfl, hinvS, hinvSi⟩ := slot_index hS
    have hcg := dVal_aVal_congr b δ hS (envs i) (env0 H pd W chalV pubVal (i : ℕ))
      (fun c hc => by rw [henvT _ hin' c, trX_base b δ H pd W chalV pubVal ln cnt acc _ c hc]; rfl)
      (by rw [henv_chal]; rfl)
    refine slotGateQX_honest b δ (slotAt sI) (envs i) ?_ ?_ g hg
    · unfold invAt
      rw [hcg.1, hcg.2, hinvS, hinvSi, henvTr _ hin', limb_inv b δ H pd W chalV pubVal ln cnt acc _ sI hs4,
        limb_invIm b δ H pd W chalV pubVal ln cnt acc _ sI hs4, Quad.mk_re_im]
      rfl
    · rw [hcg.1, hcg.2]; exact hnb _ hin' _ hS
  · -- the compiled walk gates
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hgw
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    have hmain := walkGatesX_honest (F := F) (K := K) pd hgen hH hp0 hsm α γ hord ((i : ℕ) + 1)
      (by omega) (by rw [← hW]; omega) g0 hg0
    rw [← Nock.NockVMROM.Thm54.VclL.Handle.eval_mapM_cast] at hmain
    have hev : (mapM (fun q : ℚ => (q : F)) g0).eval (Compute.TowerD.gatherEnv b (envs i)) (envs i) = 0 := by
      have hKc : ∀ kk j, okKc kk j = true →
          envAt (Compute.TowerD.gatherEnv b (envs i)) kk j =
            envAt (walkEnvKX ln cnt acc α γ (curW (F := F) H W γ 1 * α) ((i : ℕ) + 1)) kk j := by
        intro kk j hkk
        cases kk <;> simp only [okKc, okKw, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true] at hkk
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rw [henvTr _ hin']
          rcases hkk with ((rfl | rfl) | rfl) | rfl
          · rw [show (111 : ℕ) = 111 + 3 * 0 from rfl, limb_walk b δ H pd W chalV pubVal ln cnt acc _ 0 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX]
          · rw [show (114 : ℕ) = 111 + 3 * 1 from rfl, limb_walk b δ H pd W chalV pubVal ln cnt acc _ 1 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX]
          · rw [show (117 : ℕ) = 111 + 3 * 2 from rfl, limb_walk b δ H pd W chalV pubVal ln cnt acc _ 2 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX, wAccX]
          · rw [show (120 : ℕ) = 111 + 3 * 3 from rfl, limb_walk b δ H pd W chalV pubVal ln cnt acc _ 3 (by norm_num)]
            simp [walkEnvKX, walkV, wLnX, wCntX, wAccX, wInvX]
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rw [henv_chal]
          rcases hkk with rfl | rfl
          · rw [show (6 : ℕ) = chalAlphaW from rfl, hα]; simp [walkEnvKX, chalAlphaW]
          · rw [show (9 : ℕ) = chalGammaW from rfl, hγ]; simp [walkEnvKX, chalAlphaW, chalGammaW]
        · simp only [envAt, Compute.TowerD.gatherEnv]
          rw [henv_pub]
          rcases hkk with (rfl | rfl) | rfl
          · rw [show (6 : ℕ) = pubIC from rfl, hpIC]; simp [walkEnvKX, pubIC]
          · rw [show (9 : ℕ) = pubSeed from rfl, hpS]; simp [walkEnvKX, pubIC, pubSeed]
          · rw [show (12 : ℕ) = pubOut from rfl, hpO]; simp [walkEnvKX, pubIC, pubSeed, pubOut]
      have hFc : ∀ kk j, okFc kk j = true →
          envAt (envs i) kk j = envAt (walkEnvFX (F := F) (H := H) pd W ((i : ℕ) + 1)) kk j := by
        intro kk j hkk
        cases kk <;> simp only [okFc, decide_eq_true_eq] at hkk
        · simp only [envAt]
          rw [henvT _ hin' j, trX_base b δ H pd W chalV pubVal ln cnt acc _ j hkk]
          rfl
        all_goals simp at hkk
      by_cases hlt : (i : ℕ) + 1 < n
      · rw [← hmain]
        refine eval_okM okKw okFw _ (by rw [okM_mapM]; exact List.all_eq_true.mp walk_ok g0 hg0) _ _ _ _
          (fun kk j hkk => ?_) (fun kk j hkk => ?_)
        · cases kk
          · exact hKc .traceCur j hkk
          · simp only [okKw, Bool.or_eq_true, beq_iff_eq] at hkk
            simp only [envAt, Compute.TowerD.gatherEnv]
            rw [funext (henvN _ hlt)]
            rcases hkk with (rfl | rfl) | rfl
            · rw [show (111 : ℕ) = 111 + 3 * 0 from rfl,
                limb_walk b δ H pd W chalV pubVal ln cnt acc _ 0 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX]; rfl
            · rw [show (114 : ℕ) = 111 + 3 * 1 from rfl,
                limb_walk b δ H pd W chalV pubVal ln cnt acc _ 1 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX, wCntX]; rfl
            · rw [show (117 : ℕ) = 111 + 3 * 2 from rfl,
                limb_walk b δ H pd W chalV pubVal ln cnt acc _ 2 (by norm_num)]
              simp [walkEnvKX, walkV, wLnX, wCntX, wAccX]; rfl
          · exact hKc .challenge j hkk
          · exact hKc .publicVal j hkk
        · cases kk
          · exact hFc .traceCur j hkk
          · simp only [okFw, decide_eq_true_eq] at hkk
            simp only [envAt]
            rw [henvN _ hlt j, trX_base b δ H pd W chalV pubVal ln cnt acc _ j hkk]
            rfl
          · simp [okFw] at hkk
          · simp [okFw] at hkk
      · have hlast : (i : ℕ) + 1 = W.length := by omega
        have hsh := List.all_eq_true.mp walk_shape g0 hg0
        simp only [Bool.or_eq_true] at hsh
        rcases hsh with hc | hnl
        · rw [← hmain]
          exact eval_okM okKc okFc _ (by rw [okM_mapM]; exact hc) _ _ _ _ hKc hFc
        · obtain ⟨u, rfl⟩ := isNLX_eq g0 hnl
          have h18 : (envs i).trace 18 = 1 := by
            rw [henvT _ hin', trX_base b δ H pd W chalV pubVal ln cnt acc _ 18 (by norm_num), baseT_18,
              if_pos hlast]
          simp only [mapM, mapC, MixedExpr.eval, CoeffExpr.eval, h18, Rat.cast_one, sub_self, map_zero,
            zero_mul]
    exact ((mixedCompile_zero_iff b col0Id (isCoordEnv_gather b _) _).mp hev) k

end Main

end

end Nock.NockVMROM.Thm54.VclL.HonestTraceX
