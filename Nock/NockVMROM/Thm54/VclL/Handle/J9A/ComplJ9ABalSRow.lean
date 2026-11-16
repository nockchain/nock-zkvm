/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalSRow.lean

* `DX_ax`: the compute denominator of `axRecX r ft o` at an environment of the coins is `compress ⟨γH, ρH⟩
    (liftRec (record at the row))`.  `DX_limb`: that of `limbRecX` is `ρH + recDenP 0 γH (id, axL, (0, limb))`.
  * `gAx`: a `[flag]`-gated `TAG_ax` consume at a `s0B`/`s10B` row is `flag · tagW (tagRec …)` (handle values).
  * `gT9_s0B`, `gT9_s10B`, `gT9_s10S`: the three new `.s` consumes (`S1`'s `gT9`) at a row of the matching kind
    (tag weight / tag weight / limb weight); `gT9_old`: all three vanish on an old row.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSC
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (ρH γH)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (DX)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (axRecX limbRecX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)

section Rows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`DX_ax`**: the compute denominator of a `TAG_ax` consume at the row's columns. -/
theorem DX_ax (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ)
    (r ft o : ChipH.Hd) :
    DX δ (Compute.TowerD.gatherEnv b e) e (axRecX r ft o) =
      FiniteIO.compress (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 8 => algebraMap (ZMod p) K
          (![e.trace r.v, e.trace ft.k, e.trace ft.v, e.trace o.k, e.trace o.v, e.trace ChipHX9.xIdX, 0,
            ((Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagAx : ℕ) : ZMod p)] c))) := by
  have hv : DenXJ8.keyX (K := K) 8 (axRecX r ft o) e = fun c : Fin 8 => algebraMap (ZMod p) K
          (![e.trace r.v, e.trace ft.k, e.trace ft.v, e.trace o.k, e.trace o.v, e.trace ChipHX9.xIdX, 0,
            ((Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagAx : ℕ) : ZMod p)] c) := by
    funext c
    fin_cases c <;> simp [DenXJ8.keyX, DenXJ8.keyXN, axRecX, ChipHX.RE.ev,
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagAx]
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by simp [axRecX]), hv]
  simp [FiniteIO.compress]

/-- **`DX_limb`**: the compute denominator of the `s10S` limb consume at the row's columns. -/
theorem DX_limb (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ) :
    DX δ (Compute.TowerD.gatherEnv b e) e limbRecX =
      ρH δ χ + recDenP 0 (γH δ χ) (e.trace ChipHX9.xIdX, e.trace ChipHX9.axLX, (0, e.trace ChipHX9.limbX)) := by
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by simp [limbRecX])]
  congr 1
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDenP]
  simp [ChipHX.RE.ev, limbRecX, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **`gAx`**: a `[flag]`-gated `TAG_ax` consume of handles `hdX a, hdX b, hdX d` whose columns `17..122` are the
J-8 row's (as on `s0B`/`s10B`) and whose id column `126` is `R`, is `flag · tagW (tagRec …)`. -/
theorem gAx (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (r : RowNX) (fst lst : ZMod p)
    (e : Nock.Reified.Env (ZMod p))
    (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ) (R : ℕ)
    (hmid : ∀ c, 17 ≤ c → c < 123 → e.trace c = HonestCompX.colX (F := ZMod p) H pd r fst lst c)
    (hid : e.trace 126 = (R : ZMod p)) (a b' d fc : ℕ) (ha : a < 12) (hb : b' < 12) (hd : d < 12) :
    algebraMap (ZMod p) 𝕂′ (e.trace fc) *
        (DX δ (Compute.TowerD.gatherEnv b e) e (axRecX (ChipHX.hdX a) (ChipHX.hdX b') (ChipHX.hdX d)))⁻¹ =
      algebraMap (ZMod p) 𝕂′ (e.trace fc) *
        ComplJ9ABalSAx.tagW δ χ (ComplJ9ABalSAx.tagRec (K := K) (HonestCompX.hv H (HonestCompX.hN r a))
          (HonestCompX.hk H (HonestCompX.hN r b')) (HonestCompX.hv H (HonestCompX.hN r b'))
          (HonestCompX.hk H (HonestCompX.hN r d)) (HonestCompX.hv H (HonestCompX.hN r d)) (R : ZMod p)) := by
  rw [DX_ax δ b e χ hch]
  have k1 : e.trace (ChipHX.hdX a).v = HonestCompX.hv H (HonestCompX.hN r a) := by
    show e.trace (26 + 2 * a) = _
    rw [hmid _ (by omega) (by omega)]; exact HonestCompX.colX_v H pd r fst lst a ha
  have k2 : e.trace (ChipHX.hdX b').k = HonestCompX.hk H (HonestCompX.hN r b') := by
    show e.trace (25 + 2 * b') = _
    rw [hmid _ (by omega) (by omega)]; exact HonestCompX.colX_k H pd r fst lst b' hb
  have k3 : e.trace (ChipHX.hdX b').v = HonestCompX.hv H (HonestCompX.hN r b') := by
    show e.trace (26 + 2 * b') = _
    rw [hmid _ (by omega) (by omega)]; exact HonestCompX.colX_v H pd r fst lst b' hb
  have k4 : e.trace (ChipHX.hdX d).k = HonestCompX.hk H (HonestCompX.hN r d) := by
    show e.trace (25 + 2 * d) = _
    rw [hmid _ (by omega) (by omega)]; exact HonestCompX.colX_k H pd r fst lst d hd
  have k5 : e.trace (ChipHX.hdX d).v = HonestCompX.hv H (HonestCompX.hN r d) := by
    show e.trace (26 + 2 * d) = _
    rw [hmid _ (by omega) (by omega)]; exact HonestCompX.colX_v H pd r fst lst d hd
  have k6 : e.trace ChipHX9.xIdX = (R : ZMod p) := hid
  rw [k1, k2, k3, k4, k5, k6]
  rfl

end Rows

section PerRow
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (gT9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (pubVal : ℕ → ZMod p) (χ : Coins frameJ8 K) (j : ℕ)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`s0B` row**: the `TAG_ax` consume `axRecX xS xFt xE` (flag column `123`) has weight
`tagW (tagRec (H s).2 (H ft).1 (H ft).2 (H e).1 (H e).2 (idOf n))`. -/
theorem gT9_s0B (hc : (rowAt9 W (j + 1)).chip = .s0B) :
    gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 123 (axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j =
      ComplJ9ABalSAx.tagW δ χ (ComplJ9ABalSAx.tagRec (K := K) ((H (rowAt9 W (j + 1)).rn.s).2 : ZMod p)
        ((H (rowAt9 W (j + 1)).rn.ft).1 : ZMod p) ((H (rowAt9 W (j + 1)).rn.ft).2 : ZMod p)
        ((H (rowAt9 W (j + 1)).rn.e).1 : ZMod p) ((H (rowAt9 W (j + 1)).rn.e).2 : ZMod p)
        ((idOf (rowAt9 W (j + 1)).n : ℕ) : ZMod p)) := by
  have hT : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  have c123 : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace 123 = 1 := by
    rw [hT]; simp [colX9, hc, colS0B]
  have h := gAx δ b H pd (rowAt9 W (j + 1)).rn (fl1 (j + 1)) (llW W (j + 1))
    (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j) χ rfl (idOf (rowAt9 W (j + 1)).n)
    (fun c h1 h2 => by
      rw [hT]
      have := ComplJ9ACompRow.colS0B_mid (F := ZMod p) H pd idOf (rowAt9 W (j + 1)).rn (rowAt9 W (j + 1)).n
        (fl1 (j + 1)) (llW W (j + 1)) c h1 h2
      simpa [colX9, hc] using this)
    (by rw [hT]; simp [colX9, hc, colS0B]) 0 6 2 123 (by norm_num) (by norm_num) (by norm_num)
  unfold gT9
  rw [c123] at h ⊢
  simp only [map_one, one_mul] at h ⊢
  exact h

/-- **`s10B` row**: the `TAG_ax` consume `axRecX xE xFtth xSf1` (flag column `124`) has weight
`tagW (tagRec (H e).2 (H ftth).1 (H ftth).2 (H sf1).1 (H sf1).2 (idOf n))`. -/
theorem gT9_s10B (hc : (rowAt9 W (j + 1)).chip = .s10B) :
    gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 124 (axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j =
      ComplJ9ABalSAx.tagW δ χ (ComplJ9ABalSAx.tagRec (K := K) ((H (rowAt9 W (j + 1)).rn.e).2 : ZMod p)
        ((H (rowAt9 W (j + 1)).rn.ftth).1 : ZMod p) ((H (rowAt9 W (j + 1)).rn.ftth).2 : ZMod p)
        ((H (rowAt9 W (j + 1)).rn.sf1).1 : ZMod p) ((H (rowAt9 W (j + 1)).rn.sf1).2 : ZMod p)
        ((idOf (rowAt9 W (j + 1)).n : ℕ) : ZMod p)) := by
  have hT : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  have c124 : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace 124 = 1 := by
    rw [hT]; simp [colX9, hc, colS10B]
  have h := gAx δ b H pd (rowAt9 W (j + 1)).rn (fl1 (j + 1)) (llW W (j + 1))
    (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j) χ rfl (idOf (rowAt9 W (j + 1)).n)
    (fun c h1 h2 => by
      rw [hT]
      have := ComplJ9ACompRow.colS10B_mid (F := ZMod p) H pd idOf (rowAt9 W (j + 1)).rn (rowAt9 W (j + 1)).n
        (fl1 (j + 1)) (llW W (j + 1)) c h1 h2
      simpa [colX9, hc] using this)
    (by rw [hT]; simp [colX9, hc, colS10B]) 2 9 3 124 (by norm_num) (by norm_num) (by norm_num)
  unfold gT9
  rw [c124] at h ⊢
  simp only [map_one, one_mul] at h ⊢
  exact h

/-- **`s10S` row**: the limb consume `limbRecX` (flag column `125`) has weight
`limbW (idOf n, axis column 135, (0, n / 2^(32 m) % 2^32))`. -/
theorem gT9_s10S (hc : (rowAt9 W (j + 1)).chip = .s10S) :
    gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal 125 limbRecX j =
      ComplJ9ABalSAx.limbW δ χ (((idOf (rowAt9 W (j + 1)).n : ℕ) : ZMod p),
        colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) 135,
        (0, (((rowAt9 W (j + 1)).n / 2 ^ (32 * (rowAt9 W (j + 1)).m) % 2 ^ 32 : ℕ) : ZMod p))) := by
  have hT : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  unfold gT9
  rw [DX_limb δ b _ χ rfl, hT]
  have c125 : colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) 125 = 1 := by
    simp [colX9, hc, colS10S]
  have c126 : colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) ChipHX9.xIdX =
      ((idOf (rowAt9 W (j + 1)).n : ℕ) : ZMod p) := by
    simp [colX9, hc, colS10S, ChipHX9.xIdX]
  have c134 : colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) ChipHX9.limbX =
      (((rowAt9 W (j + 1)).n / 2 ^ (32 * (rowAt9 W (j + 1)).m) % 2 ^ 32 : ℕ) : ZMod p) := by
    simp [colX9, hc, colS10S, ChipHX9.limbX]
  rw [c125, c126, c134]
  simp only [map_one, one_mul, ComplJ9ABalSAx.limbW]
  rfl

/-- **Old rows**: the three new `.s` consumes (flag columns `≥ 123`) vanish. -/
theorem gT9_old (hc : (rowAt9 W (j + 1)).chip = .old) (cf : ℕ) (hcf : 123 ≤ cf) (r : List ChipHX.RE) :
    gT9 δ b H pd idOf W (VerJ8.chalVJ8 b χ) pubVal cf r j = 0 := by
  have hT : (env0 H pd idOf W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      colX9 (F := ZMod p) H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  unfold gT9
  rw [hT, ComplJ9ACompRow.colX9_old_new H pd idOf _ _ _ hc cf hcf]
  simp

end PerRow

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.DX_ax
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.DX_limb
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.gAx
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.gT9_s0B
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.gT9_s10B
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.gT9_s10S
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSRow.gT9_old
