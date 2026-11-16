/-
  Nock/V1J8/PubExe.lean

The concrete field is: `p` Goldilocks, `𝕂 = KC = 𝔽_p[x]/(x³ − 7)` with the power basis `powerBasis3`, `δ = deltaF = 7`,
  `𝕂′ = KQ = Quad δ`.  Executable carriers `Gold` / `K3` / `K6` with `Gold.toZ`, `K3.toK`, `K6.toQ` commuting with the
  field operations.

  * **Coins**: `CoinsE = Fin 19 → K3`, `toχ χe : Coins frameJ8 KC`.
  * **`chalVJ8E`** (the compute challenge vector, limbs of the six compute coins) with `chalVJ8E_spec`:
    `(chalVJ8E χe j).toZ = chalVJ8 powerBasis3 (toχ χe) j`.
  * **`compressE`** with `toQ_compressE`: `toQ (compressE γ ρ v) = compress ⟨toQ γ, toQ ρ⟩ (toQ ∘ v)`.
  * **`encE`** (the bivariate fingerprint `E(z, y)`, limbs by Horner) with `encE_spec`: `= encZY (toQ z) (toQ y)` for
    ANY `Algebra 𝔽_p 𝕂′` structure (ring maps out of `ZMod p` are unique).
  * **`claimRecsJ8E` / `pinRecsJ8E` / `pinConsE`**, each mapped by `toQ` equal to `claimRecsJ8` / `pinRecsJ8` /
    `pinCons` (lifted).
  * **`MsgE`** (an executable message; `MsgE.toMsg : MsgJ8' p KC deltaF`) and **`checkPubJ8E`** (a computable `Bool`)
    with **`checkPubJ8E_iff : checkPubJ8E Pb c χe M = true ↔ PubEqJ8 deltaF powerBasis3 Pb c (toχ χe) M.toMsg`**.
-/
import Nock.V1J8.Static
import Nock.TraceGenExe.PowerBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.Exe

open Nock Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' claimRecsJ8 pinRecsJ8 claimCells rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c2 c3 c4 c5 c6 c7)

/-! ## 1. Equality tests and small embeddings -/

def eqG (a b : Gold) : Bool := a.val == b.val

theorem eqG_iff (a b : Gold) : eqG a b = true ↔ a = b := by
  unfold eqG
  rw [beq_iff_eq]
  exact ⟨Gold.ext, fun h => by rw [h]⟩

def eq3 (a b : K3) : Bool := eqG a.c0 b.c0 && eqG a.c1 b.c1 && eqG a.c2 b.c2

theorem eq3_iff (a b : K3) : eq3 a b = true ↔ K3.toK a = K3.toK b := by
  unfold eq3
  simp only [Bool.and_eq_true, eqG_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    cases a; cases b; simp_all
  · intro h
    have := K3.toK_injective h
    subst this
    exact ⟨⟨rfl, rfl⟩, rfl⟩

def eq6 (a b : K6) : Bool := eq3 a.re b.re && eq3 a.im b.im

theorem eq6_iff (a b : K6) : eq6 a b = true ↔ K6.toQ a = K6.toQ b := by
  unfold eq6
  simp only [Bool.and_eq_true, eq3_iff, K6.toQ]
  rw [Quad.mk_eq_mk_iff]

/-- `n` as a canonical `Gold`. -/
def natG (n : ℕ) : Gold := Gold.ofZ (n : ZMod p)

theorem toZ_natG (n : ℕ) : (natG n).toZ = (n : ZMod p) := Gold.toZ_ofZ _

/-- A base element of `𝕂`. -/
def g3 (g : Gold) : K3 := ⟨g, 0, 0⟩

theorem toK_g3 (g : Gold) : K3.toK (g3 g) = algebraMap (ZMod p) KC g.toZ := by
  simp [K3.toK, g3, Gold.toZ_zero]

/-- A base element of `𝕂′`. -/
def g6 (g : Gold) : K6 := ⟨g3 g, 0⟩

/-- The canonical `𝔽_p → 𝕂′` (named, so that no local `Algebra 𝔽_p 𝕂′` instance can capture it). -/
noncomputable abbrev embQ : ZMod p →+* KQ := algebraMap (ZMod p) KQ

theorem toQ_g6 (g : Gold) : K6.toQ (g6 g) = embQ g.toZ := by
  unfold g6 K6.toQ
  rw [toK_g3, K3.toK_zero, Quad.mk_base, IsScalarTower.algebraMap_apply (ZMod p) KC KQ]

theorem toQ_mk (a b : K3) : K6.toQ ⟨a, b⟩ = Quad.mk _ (K3.toK a) (K3.toK b) := rfl

/-! ## 2. Sums, powers, `RLC`, `compress` -/

def lsum : List K6 → K6
  | [] => 0
  | a :: l => a + lsum l

theorem toQ_lsum : ∀ l : List K6, K6.toQ (lsum l) = (l.map K6.toQ).sum
  | [] => by simp [lsum, K6.toQ_zero]
  | a :: l => by simp only [lsum, K6.toQ_add, List.map_cons, List.sum_cons, toQ_lsum l]

def powE (z : K6) : ℕ → K6
  | 0 => 1
  | n + 1 => powE z n * z

theorem toQ_powE (z : K6) : ∀ n, K6.toQ (powE z n) = (K6.toQ z) ^ n
  | 0 => by simp [powE, K6.toQ_one]
  | n + 1 => by rw [powE, K6.toQ_mul, toQ_powE z n]; exact (pow_succ _ _).symm

/-- `RLC^γ(v) = Σ_c γ^c v_c`. -/
def rlcE {m : ℕ} (γ : K6) (v : Fin m → K6) : K6 := lsum (List.ofFn fun c => powE γ c * v c)

theorem toQ_rlcE {m : ℕ} (γ : K6) (v : Fin m → K6) :
    K6.toQ (rlcE γ v) = Walk.rlc (K6.toQ γ) (fun c => K6.toQ (v c)) := by
  rw [rlcE, toQ_lsum, List.map_ofFn, List.sum_ofFn, Walk.rlc]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Function.comp, K6.toQ_mul, toQ_powE]

/-- `compress (γ, ρ) v = ρ + RLC^γ(v)`. -/
def compressE {m : ℕ} (γ ρ : K6) (v : Fin m → K6) : K6 := ρ + rlcE γ v

theorem toQ_compressE {m : ℕ} (γ ρ : K6) (v : Fin m → K6) :
    K6.toQ (compressE γ ρ v) =
      FiniteIO.compress (⟨K6.toQ γ, K6.toQ ρ⟩ : FiniteIO.IOCoins KQ) (fun c => K6.toQ (v c)) := by
  rw [compressE, K6.toQ_add, toQ_rlcE]; rfl

/-! ## 3. Coins and the compute challenge vector -/

abbrev CoinsE := Fin frameJ8.n → K3

/-- The spec coin of an executable coin vector. -/
noncomputable def toχ (χe : CoinsE) : Coins frameJ8 KC := fun i => K3.toK (χe i)

/-- The compute's six `𝕂` coins by slot (`coinHQ`): `0 γH`, `1 ρH`, `2 αW`, `3 γW`, `4` Im `γH`, `5` Im `ρH`. -/
def coinHQE (χe : CoinsE) (q : ℕ) : K3 :=
  if q = 0 then χe ⟨11, by decide⟩ else if q = 1 then χe ⟨12, by decide⟩
  else if q = 2 then χe ⟨13, by decide⟩ else if q = 3 then χe ⟨14, by decide⟩
  else if q = 4 then χe ⟨15, by decide⟩ else χe ⟨16, by decide⟩

theorem coinHQE_spec (χe : CoinsE) (q : ℕ) :
    K3.toK (coinHQE χe q) = coinHQ (toVSQ (toχ χe)) q := by
  unfold coinHQE coinHQ coinH
  by_cases h0 : q = 0
  · subst h0; rfl
  by_cases h1 : q = 1
  · subst h1; rfl
  by_cases h2 : q = 2
  · subst h2; rfl
  by_cases h3 : q = 3
  · subst h3; rfl
  by_cases h4 : q = 4
  · subst h4; rfl
  · simp only [h0, h1, h2, h3, h4, if_false, show ¬ q < 4 by omega]; rfl

/-- The `k`-th limb. -/
def limb (a : K3) (k : ℕ) : Gold := if k = 0 then a.c0 else if k = 1 then a.c1 else a.c2

/-- **The executable compute challenge vector** (`chalVHQ`: limbs `3q .. 3q+2` of coin `q`, `q < 6`). -/
def chalVJ8E (χe : CoinsE) (j : ℕ) : Gold := if j < 18 then limb (coinHQE χe (j / 3)) (j % 3) else 0

/-- **`chalVJ8E` is `chalVJ8` at the power basis.** -/
theorem chalVJ8E_spec (χe : CoinsE) (j : ℕ) :
    (chalVJ8E χe j).toZ = VerJ8.chalVJ8 powerBasis3 (toχ χe) j := by
  unfold chalVJ8E VerJ8.chalVJ8 chalVHQ
  split_ifs with hj
  · rw [← coinHQE_spec, coord_powerBasis3_toK]
    have h3 : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    unfold limb
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  · exact Gold.toZ_zero

/-! ## 4. The fingerprint `E(z, y)` -/

/-- An executable fingerprint. -/
structure FPE where
  size : K6
  dyck : K6
  leaf : K6

noncomputable def FPE.toQ (e : FPE) : ComputeTable.FP KQ := ⟨K6.toQ e.size, K6.toQ e.dyck, K6.toQ e.leaf⟩

/-- `FP.cons`. -/
def consE (z : K6) (a b : FPE) : FPE :=
  ⟨a.size * b.size, z * a.dyck + a.size * a.size * z⁻¹ + a.size * a.size * b.dyck, a.leaf + a.size * b.leaf⟩

def hornerE (y : K6) : List K6 → K6
  | [] => 0
  | a :: l => a + y * hornerE y l

/-- `leafVal y n`: `n` if small, the limb polynomial at `y` if big. -/
def leafE (y : K6) (n : ℕ) : K6 :=
  if n < p then g6 (natG n) else hornerE y ((Nock.Atoms.limbs n).map fun a => g6 (natG a))

/-- **`E(z, y)`** (`encZY`). -/
def encE (z y : K6) : Noun → FPE
  | .atom n => ⟨z, 0, leafE y n⟩
  | .cell a b => consE z (encE z y a) (encE z y b)

section Enc
variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem algebraMap_Fp (x : ZMod p) : algebraMap Nock.Atoms.Fp KQ x = embQ x :=
  congrArg (fun f : ZMod p →+* KQ => f x) (RingHom.ext_zmod _ _)

noncomputable def hornerQ (y : KQ) : List KQ → KQ
  | [] => 0
  | a :: l => a + y * hornerQ y l

theorem toQ_hornerE (y : K6) : ∀ l : List K6, K6.toQ (hornerE y l) = hornerQ (K6.toQ y) (l.map K6.toQ)
  | [] => by simp [hornerE, hornerQ, K6.toQ_zero]
  | a :: l => by simp only [hornerE, hornerQ, List.map_cons, K6.toQ_add, K6.toQ_mul, toQ_hornerE y l]

theorem aeval_limbPoly (y : KQ) : ∀ l : List ℕ,
    aeval y (Nock.Atoms.limbPoly l) = hornerQ y (l.map fun a : ℕ => embQ ((a : ℕ) : ZMod p))
  | [] => by simp [Nock.Atoms.limbPoly, Nock.Atoms.natPoly, hornerQ]
  | a :: l => by
      have e : Nock.Atoms.limbPoly (a :: l) = C (a : Nock.Atoms.Fp) + X * Nock.Atoms.limbPoly l := by
        simp [Nock.Atoms.limbPoly, Nock.Atoms.natPoly, Polynomial.map_add, Polynomial.map_mul]
      rw [e, map_add, map_mul, aeval_C, aeval_X, aeval_limbPoly y l, List.map_cons, hornerQ, algebraMap_Fp]

theorem leafE_spec (y : K6) (n : ℕ) : K6.toQ (leafE y n) = Nock.Atoms.leafVal (K6.toQ y) n := by
  unfold leafE Nock.Atoms.leafVal Nock.Atoms.L
  by_cases h : n < p
  · have h' : n < Nock.Atoms.p := h
    rw [if_pos h, if_pos h', aeval_C, algebraMap_Fp, toQ_g6, toZ_natG]
  · have h' : ¬ n < Nock.Atoms.p := h
    rw [if_neg h, if_neg h', toQ_hornerE, aeval_limbPoly, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp, toQ_g6, toZ_natG]

theorem encE_spec (z y : K6) :
    ∀ n : Noun, (encE z y n).toQ = EncZYJ8.encZY (K6.toQ z) (K6.toQ y) n
  | .atom n => by
      show (⟨K6.toQ z, K6.toQ 0, K6.toQ (leafE y n)⟩ : ComputeTable.FP KQ) = ComputeTable.FP.atomFP _ _
      rw [K6.toQ_zero, leafE_spec]; rfl
  | .cell a b => by
      show (consE z (encE z y a) (encE z y b)).toQ = ComputeTable.FP.cons _ _ _
      rw [← encE_spec z y a, ← encE_spec z y b]
      simp only [consE, FPE.toQ, ComputeTable.FP.cons, K6.toQ_add, K6.toQ_mul, K6.toQ_inv]

end Enc

/-! ## 5. The claim / pin records and the pin consumes -/

/-- `ClaimVS.claimVec`: fingerprint, `lo + hi√δ`, serial. -/
def claimVecE (e : FPE) (idx hi lo : Gold) : Fin 5 → K6 := fun c =>
  match (c : ℕ) with
  | 0 => e.size
  | 1 => e.dyck
  | 2 => e.leaf
  | 3 => ⟨g3 lo, g3 hi⟩
  | _ => ⟨g3 idx, 0⟩

theorem claimVecE_spec (e : FPE) (idx hi lo : Gold) :
    (fun c => K6.toQ (claimVecE e idx hi lo c)) = ClaimVS.claimVec deltaF e.toQ idx.toZ hi.toZ lo.toZ := by
  funext c
  fin_cases c <;> simp [claimVecE, ClaimVS.claimVec, FPE.toQ, toQ_mk, toK_g3, K3.toK_zero] <;> rfl

/-- The structure seed `z′ = (χ₂, χ₃)` and the limb seed `y = (χ₁₇, χ₁₈)`. -/
def zE (χe : CoinsE) : K6 := ⟨χe c2, χe c3⟩
def yE (χe : CoinsE) : K6 := ⟨χe cY1, χe cY2⟩

/-- **The executable claim records** (`claimRecsJ8`). -/
def claimRecsJ8E (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → K6) :=
  (claimCells c).map fun k => claimVecE (encE (zE χe) (yE χe) (claimNoun c k)) (natG (m k).1)
    (natG (rkC (claimNoun c k)).1) (natG (rkC (claimNoun c k)).2)

/-- **The executable pin records** (`pinRecsJ8`). -/
def pinRecsJ8E (Pb : PubJ8 p) (χe : CoinsE) : List (Fin 5 → K6) :=
  Pb.regs.map fun id => claimVecE (encE (zE χe) (yE χe) (Nock.Jet.Autogen.compile p (Pb.Rt id))) (natG (Pb.idx id))
    (natG (Pb.rk id).1) (natG (Pb.rk id).2)

/-- **The executable pin consumes** (`pinCons`, lifted to `𝕂′`). -/
def pinConsE (regs : List ℕ) (idx : ℕ → ℕ) : List (Fin 8 → K6) :=
  regs.map fun id c => g6 (Gold.ofZ ((Nock.Jet.RapJetJ8.tlF (Nock.Jet.PinJ8.pinKey (F := ZMod p) id (idx id))).getD c 0))

/-- A vector's `toQ`. -/
noncomputable def vQ {m : ℕ} (v : Fin m → K6) : Fin m → KQ := fun c => K6.toQ (v c)

section Rec
variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem claimRecsJ8E_spec (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) :
    (claimRecsJ8E χe c m).map vQ = claimRecsJ8 deltaF (toχ χe) c m := by
  unfold claimRecsJ8E claimRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show (fun c => K6.toQ (claimVecE _ _ _ _ c)) = _
  rw [claimVecE_spec, encE_spec, toZ_natG, toZ_natG, toZ_natG]
  rfl

theorem pinRecsJ8E_spec (Pb : PubJ8 p) (χe : CoinsE) :
    (pinRecsJ8E Pb χe).map vQ = pinRecsJ8 deltaF Pb (toχ χe) := by
  unfold pinRecsJ8E pinRecsJ8
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show (fun c => K6.toQ (claimVecE _ _ _ _ c)) = _
  rw [claimVecE_spec, encE_spec, toZ_natG, toZ_natG, toZ_natG]
  rfl

end Rec

theorem pinConsE_spec {iFt : Fintype KQ} {iD : DecidableEq KQ} {iDK : DecidableEq KC}
    (regs : List ℕ) (idx : ℕ → ℕ) :
    (pinConsE regs idx).map vQ =
      (Nock.Jet.PinJ8.pinCons (p := p) (K := KC) regs idx).map fun r => BalanceQ.liftRec (L := KQ) r := by
  unfold pinConsE Nock.Jet.PinJ8.pinCons
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun id _ => ?_
  funext c
  simp only [Function.comp, vQ, BalanceQ.liftRec, Nock.Jet.RapJetJ8.keyK, toQ_g6, Gold.toZ_ofZ]
  exact (IsScalarTower.algebraMap_apply (ZMod p) KC KQ _)

/-! ## 6. The executable message and the public-equation check -/

/-- **An executable message** (`MsgJ8'`). -/
structure MsgE where
  m : ClaimMsgVS
  ρ : Fin 5 → K6
  ρS : K6
  pubsC : ℕ → K3
  pubsW : ℕ → K3
  pubsJ : ℕ → K3
  pubsA : ℕ → K3
  pubsV : ℕ → K3

noncomputable def MsgE.toMsg (M : MsgE) : MsgJ8' p KC deltaF where
  m := M.m
  ρ := fun i => K6.toQ (M.ρ i)
  ρS := K6.toQ M.ρS
  pubsC := fun i => K3.toK (M.pubsC i)
  pubsW := fun i => K3.toK (M.pubsW i)
  pubsJ := fun i => K3.toK (M.pubsJ i)
  pubsA := fun i => K3.toK (M.pubsA i)
  pubsV := fun i => K3.toK (M.pubsV i)

/-- Two consecutive publics as a `𝕂′` element. -/
def pp (f : ℕ → K3) (i : ℕ) : K6 := ⟨f i, f (i + 1)⟩

/-- The handle coins `γH′ = (χ₁₁, χ₁₅)`, `ρH′ = (χ₁₂, χ₁₆)`; the validity coins `γ′ = (χ₄, χ₆)`, `ρ′ = (χ₅, χ₇)`. -/
def γHE (χe : CoinsE) : K6 := ⟨χe ⟨11, by decide⟩, χe ⟨15, by decide⟩⟩
def ρHE (χe : CoinsE) : K6 := ⟨χe ⟨12, by decide⟩, χe ⟨16, by decide⟩⟩
def γVE (χe : CoinsE) : K6 := ⟨χe c4, χe c6⟩
def ρVE (χe : CoinsE) : K6 := ⟨χe c5, χe c7⟩

/-- **The executable public-equation check**: the eight conjuncts of `PubEqJ8`, in order. -/
def checkPubJ8E (Pb : PubJ8 p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) : Bool :=
  eq6 (M.ρ 3 + (pp M.pubsW WalkHQ.pubXQ + pp M.pubsJ 2)) (pp M.pubsC CellHQ.pubHQ) &&
  eq6 (M.ρ 4) (pp M.pubsW WalkHQ.pubPQ) &&
  eq6 (M.ρS + lsum ((pinConsE Pb.regs Pb.idx).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) + pp M.pubsJ 0)
    (pp M.pubsA AtomChipHQ.pubMI + pp M.pubsV WalkHQ.pubPQ) &&
  eq6 (lsum ((claimRecsJ8E χe c M.m ++ pinRecsJ8E Pb χe).map fun r => (compressE (γVE χe) (ρVE χe) r)⁻¹))
    (pp M.pubsC 0 + pp M.pubsA AtomChipHQ.pubMB) &&
  eq6 (pp M.pubsA CellHQ.pubHQ) (pp M.pubsA AtomChipHQ.pubC + pp M.pubsV WalkHQ.pubXQ) &&
  (eq3 (M.pubsA 0) 0 && eq3 (M.pubsA 1) 0) &&
  (eq3 (M.pubsC 2) (M.pubsW 0) && eq3 (M.pubsC 3) (M.pubsW 1)) &&
  (eq3 (M.pubsA 2) (M.pubsV 0) && eq3 (M.pubsA 3) (M.pubsV 1))

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem toQ_pp (f : ℕ → K3) (i : ℕ) : K6.toQ (pp f i) = Quad.mk _ (K3.toK (f i)) (K3.toK (f (i + 1))) := rfl

/-- The inverse-sum of a list of executable records. -/
theorem toQ_invSum {m : ℕ} (γ ρ : K6) (l : List (Fin m → K6)) :
    K6.toQ (lsum (l.map fun r => (compressE γ ρ r)⁻¹)) =
      ((l.map vQ).map fun r => (FiniteIO.compress (⟨K6.toQ γ, K6.toQ ρ⟩ : FiniteIO.IOCoins KQ) r)⁻¹).sum := by
  rw [toQ_lsum, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp, K6.toQ_inv, toQ_compressE]
  rfl

/-- **`checkPubJ8E_iff`**: the executable public-equation check is exactly `PubEqJ8` at the concrete field, the
coins `toχ χe` and the message `M.toMsg`. -/
theorem checkPubJ8E_iff (Pb : PubJ8 p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) :
    checkPubJ8E Pb c χe M = true ↔ PubEqJ8 deltaF powerBasis3 Pb c (toχ χe) M.toMsg := by
  have hcv := VerJ8.coinsCV_J8 deltaF powerBasis3 (toχ χe)
  unfold checkPubJ8E PubEqJ8
  simp only [Bool.and_eq_true, eq6_iff, eq3_iff, K6.toQ_add, toQ_pp, toQ_invSum, K3.toK_zero, hcv]
  rw [pinConsE_spec, List.map_append, claimRecsJ8E_spec, pinRecsJ8E_spec]
  simp only [List.map_map, Function.comp_def, and_assoc]
  exact Iff.rfl
  all_goals infer_instance

end Iff

/-! ## 7. The partial `iff` at the concrete field -/

section Split
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **`acceptsJ8V_iff_exe`**: at the concrete field, `AcceptsJ8V` at the coins `toχ χe` and the message `M.toMsg` is
the executable static check, the executable public-equation check, and the chip residue. -/
theorem acceptsJ8V_iff_exe (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE)
    (tr : TraceJ8.TrJ8 (ZMod p)) (r : FrameJ8.RowsJ8) (g : ℕ) :
    AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 Pb Rg c (toχ χe) M.toMsg tr r g ↔
      checkStaticJ8 Pb c M.m r g = true ∧ checkPubJ8E Pb c χe M = true ∧
        ChipsJ8 deltaF powerBasis3 Pb Rg c (toχ χe) M.toMsg tr := by
  rw [acceptsJ8V_iff, checkStaticJ8_iff, checkPubJ8E_iff]
  exact Iff.rfl

end Split

end Nock.V1J8.Exe
