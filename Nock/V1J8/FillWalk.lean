/-
  Nock/V1J8/FillWalk.lean

* `Walk.colZ k αW mL mR c`: the example's one walk row (the dummy root `s0`, `len = 0`), every one of the 166
    columns, computable (`K6`), at memory coins `k`, walk coin `αW` and path multiplicities `mL mR`; `Walk.pubs` the
    eight publics (`ρ_X`, `ρ_P`, `ρ_XQ`, `ρ_PQ`);
  * **`walkColZ_eq`**: column `c < 166` equals the honest builder's column function (`HonestK8.certUp` of
    `WalkTraceHQ.colHQ` of `walkCol (wvals …)` with the role fill `rolesF`, under `fullCol`), given the handle coins
    of `chals` are `(γH′, ρH′)` and `chals 0 = αW`;
  * **`walkTrace_eq`**: the interpolants ARE `InhabJ8MemWalk.trW0`; **`walkTrace_eq_frame`** / **`interpOf_walk`** at
    the frame coins (`coOf χe`, `αW = chalsMJ8E χe 0`, `chals = chalsMJ8 deltaF (toχ χe)`).
-/
import Nock.V1J8.FillCell
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.FillMem

open Nock Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.V1J8.Exe Nock.V1J8.Check

/-! ## 1. The walk-J8 fill of the example (one row: the dummy root `s0`) -/

namespace Walk
variable (k : Co) (αW : K3) (mL mR : ℕ)

def pE : FPE := consE k.z (atomFPE k.z (lq 0)) (atomFPE k.z (lq 0))
def lE : FPE := atomFPE k.z (lq 0)

def xInv : K6 := (compressE k.γ k.ρ (![(pE k).size, (pE k).dyck, (pE k).leaf, (lE k).size, (lE k).dyck,
  (lE k).leaf, (lE k).size, (lE k).dyck, (lE k).leaf, lq 0, lq 0] : Fin 11 → K6))⁻¹
def pInvL : K6 := (compressE k.γ k.ρ (![(pE k).size, (pE k).dyck, (pE k).leaf, (lE k).size, (lE k).dyck,
  (lE k).leaf, lq 2, lq 0] : Fin 8 → K6))⁻¹
def pInvR : K6 := (compressE k.γ k.ρ (![(pE k).size, (pE k).dyck, (pE k).leaf, (lE k).size, (lE k).dyck,
  (lE k).leaf, lq 3, lq 0] : Fin 8 → K6))⁻¹
def pAcc : K6 := lq mL * pInvL k + lq mR * pInvR k

/-- The fingerprint slots `p l r root` (`r = l`, `root = p`). -/
def fpSlot : ℕ → K6
  | 0 => (pE k).size | 1 => (pE k).dyck | 2 => (pE k).leaf
  | 3 => (lE k).size | 4 => (lE k).dyck | 5 => (lE k).leaf
  | 6 => (lE k).size | 7 => (lE k).dyck | 8 => (lE k).leaf
  | 9 => (pE k).size | 10 => (pE k).dyck | _ => (pE k).leaf

/-- The IO slots `xInv pInvL pInvR xAcc pAcc`. -/
def ioSlot : ℕ → K6
  | 0 => xInv k | 1 => pInvL k | 2 => pInvR k | 3 => xInv k | _ => pAcc k mL mR

def wrole (ρ : ℕ) : K3 :=
  if ρ < 24 then (if ρ % 2 = 0 then (fpSlot k (ρ / 2)).re else (fpSlot k (ρ / 2)).im)
  else if ρ = 24 then αW else if ρ = 25 then αW else if ρ = 26 then 0
  else if (ρ - 27) % 2 = 0 then (ioSlot k mL mR ((ρ - 27) / 2)).re else (ioSlot k mL mR ((ρ - 27) / 2)).im

def hX : K6 := compressE k.γH k.ρH (![0, 0, 0, 0, 0] : Fin 5 → K6)
def hPL : K6 := compressE k.γH k.ρH (![0, lq 2, 0, 0] : Fin 4 → K6)
def hPR : K6 := compressE k.γH k.ρH (![0, lq 3, 0, 0] : Fin 4 → K6)
def hPA : K6 := lq mL * (hPL k)⁻¹ + lq mR * (hPR k)⁻¹

/-- The handle `𝕂′` roles `xi pl pr xa pa` (Re / Im). -/
def hslot : ℕ → K6
  | 0 => (hX k)⁻¹ | 1 => (hPL k)⁻¹ | 2 => (hPR k)⁻¹ | 3 => (hX k)⁻¹ | _ => hPA k mL mR

def hrole (t : ℕ) : K3 := if t % 2 = 0 then (hslot k mL mR (t / 2)).re else (hslot k mL mR (t / 2)).im

/-- **Column `c` of the walk row** (166 columns). -/
def colZ (c : ℕ) : ZMod p :=
  if c < 3 then 1 else if c = 4 then 1 else if c = 10 then (mL : ZMod p) else if c = 11 then (mR : ZMod p)
  else if c < 14 then 0 else if c < 21 then 1
  else if c < 25 then 0 else if c < 136 then limbZ (wrole k αW mL mR ((c - 25) / 3)) ((c - 25) % 3)
  else if c < 166 then limbZ (hrole k mL mR ((c - 136) / 3)) ((c - 136) % 3) else 0

/-- The eight publics: `ρ_X` (0, 1), `ρ_P` (2, 3), `ρ_XQ` (4, 5), `ρ_PQ` (6, 7). -/
def pubs (j : ℕ) : K3 :=
  if j = 0 then (xInv k).re else if j = 1 then (xInv k).im
  else if j = 2 then (pAcc k mL mR).re else if j = 3 then (pAcc k mL mR).im
  else if j = 4 then (hX k)⁻¹.re else if j = 5 then (hX k)⁻¹.im
  else if j = 6 then (hPA k mL mR).re else if j = 7 then (hPA k mL mR).im else 0

def cols : ℕ → Fin 1 → ZMod p := fun c _ => colZ k αW mL mR c

end Walk

/-! ## 2. Bridges -/

section WBridge
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell (aRv)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk

variable (k : Co) (αW : K3) (mL mR : ℕ)

/-- The example's walk row at `K6`-coins `k`, walk coin `αW`. -/
noncomputable abbrev wrowQ : WalkVals (ZMod p) KC KQ := wrow deltaF (K3.toK αW) (K6.toQ k.z) mL mR

theorem liftQ_aRv0 : liftQ (K := KC) deltaF (aRv (0 : ℕ) : ZMod p) = liftQ deltaF (0 : ZMod p) := by
  simp [aRv] <;> rfl

theorem wpE_eq : (Walk.pE k).toQ = (wrowQ k αW mL mR).p := by
  rw [Walk.pE, toQ_consE, toQ_atomFPE, toQ_lq]
  simp only [wrow, liftQ_aRv0, Nat.cast_zero]
theorem wlE_eq : (Walk.lE k).toQ = (wrowQ k αW mL mR).l := by
  rw [Walk.lE, toQ_atomFPE, toQ_lq]; simp only [wrow, Nat.cast_zero]
theorem wrE_eq : (Walk.lE k).toQ = (wrowQ k αW mL mR).r := by
  rw [Walk.lE, toQ_atomFPE, toQ_lq]; simp only [wrow, liftQ_aRv0, Nat.cast_zero]
theorem wroot_eq : (Walk.pE k).toQ = (wrowQ k αW mL mR).root := by
  rw [Walk.pE, toQ_consE, toQ_atomFPE, toQ_lq]
  simp only [wrow, liftQ_aRv0, Nat.cast_zero]

theorem wxInv_eq : K6.toQ (Walk.xInv k) =
    (FiniteIO.compress (m := 11) (ioQ k) (wxKeyV deltaF (wrowQ k αW mL mR)))⁻¹ := by
  rw [Walk.xInv, K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := wpE_eq k αW mL mR
  have hl := wlE_eq k αW mL mR
  have hr := wrE_eq k αW mL mR
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · show K6.toQ (lq 0) = liftQ deltaF ((0 : ℕ) : ZMod p); rw [toQ_lq]
  · show K6.toQ (lq 0) = liftQ deltaF (0 : ZMod p); rw [toQ_lq, Nat.cast_zero]

theorem wpInvL_eq : K6.toQ (Walk.pInvL k) =
    (FiniteIO.compress (m := 8) (ioQ k) (wrecLV deltaF (wrowQ k αW mL mR)))⁻¹ := by
  rw [Walk.pInvL, K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := wroot_eq k αW mL mR
  have hl := wlE_eq k αW mL mR
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · show K6.toQ (lq 2) = liftQ deltaF (2 * (1 : ZMod p)); rw [toQ_lq, mul_one]; rfl
  · show K6.toQ (lq 0) = liftQ deltaF ((0 : ℕ) : ZMod p); rw [toQ_lq]

theorem wpInvR_eq : K6.toQ (Walk.pInvR k) =
    (FiniteIO.compress (m := 8) (ioQ k) (wrecRV deltaF (wrowQ k αW mL mR)))⁻¹ := by
  rw [Walk.pInvR, K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := wroot_eq k αW mL mR
  have hr := wrE_eq k αW mL mR
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · show K6.toQ (lq 3) = liftQ deltaF (2 * (1 : ZMod p) + 1); rw [toQ_lq]; norm_num
  · show K6.toQ (lq 0) = liftQ deltaF ((0 : ℕ) : ZMod p); rw [toQ_lq]


/-- The filled walk rows at `K6`-coins `k`. -/
noncomputable abbrev wvalsQ : Fin 1 → WalkVals (ZMod p) KC KQ :=
  wvals deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (K3.toK αW) (K6.toQ k.z) mL mR

theorem fpSlot_eq (i : Fin 1) (s : ℕ) (hs : s < 12) :
    K6.toQ (Walk.fpSlot k s) = (wvalsQ k αW mL mR i).fpSlot s := by
  have hp := wpE_eq k αW mL mR
  have hl := wlE_eq k αW mL mR
  have hr := wrE_eq k αW mL mR
  have ht := wroot_eq k αW mL mR
  interval_cases s
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact congrArg ComputeTable.FP.size ht
  · exact congrArg ComputeTable.FP.dyck ht
  · exact congrArg ComputeTable.FP.leaf ht

theorem ioSlot_eq (i : Fin 1) (s : ℕ) (hs : s < 5) :
    K6.toQ (Walk.ioSlot k mL mR s) = (wvalsQ k αW mL mR i).ioSlot s := by
  have hi : (i : ℕ) = 0 := by omega
  interval_cases s
  · exact wxInv_eq k αW mL mR
  · exact wpInvL_eq k αW mL mR
  · exact wpInvR_eq k αW mL mR
  · show K6.toQ (Walk.xInv k) = ∑ q ∈ Finset.range ((i : ℕ) + 1),
      (walkFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (wrowQ k αW mL mR)).xInv
    rw [hi, Finset.sum_range_one]; exact wxInv_eq k αW mL mR
  · show K6.toQ (Walk.pAcc k mL mR) = ∑ q ∈ Finset.range ((i : ℕ) + 1),
      wpTermV deltaF (walkFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (wrowQ k αW mL mR))
    rw [hi, Finset.sum_range_one, Walk.pAcc, K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq,
      wpInvL_eq k αW mL mR, wpInvR_eq k αW mL mR]
    rfl

theorem wrole_eq (i : Fin 1) (ρ : ℕ) (hρ : ρ < 37) :
    K3.toK (Walk.wrole k αW mL mR ρ) = wroleVal deltaF (wvalsQ k αW mL mR i) ρ := by
  unfold Walk.wrole wroleVal
  split_ifs
  · rw [← fpSlot_eq k αW mL mR i _ (by omega), re_toQ]
  · rw [← fpSlot_eq k αW mL mR i _ (by omega), im_toQ]
  · rfl
  · rfl
  · exact K3.toK_zero
  · rw [← ioSlot_eq k αW mL mR i _ (by omega), re_toQ]
  · rw [← ioSlot_eq k αW mL mR i _ (by omega), im_toQ]

end WBridge

/-! ## 3. The handle roles -/

section WHandle
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell (hcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]
variable (k : Co) (mL mR : ℕ) (hn : 0 < 1) (nodes : Fin 1 → ZMod p) {h : ℕ}
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → KC)

/-- The honest walk column function at `K6`-coins `k`. -/
noncomputable abbrev wcolQ : ℕ → Fin 1 → ZMod p :=
  wcol deltaF powerBasis3 chals (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mL mR

/-- The honest handle role fill. -/
noncomputable abbrev rolesQ : WalkTraceH.Roles 1 KQ :=
  WalkTraceHQ.rolesF deltaF 1 powerBasis3 hn nodes orbit chals pubs (wcolQ k mL mR chals) 0 0 0 0

theorem hden_eq (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) (m : ℕ) (v : ℕ → ZMod p)
    (w : Fin m → K6) (hw : ∀ c : Fin m, K6.toQ (w c) = liftQ deltaF (v c)) :
    hden deltaF chals m v = K6.toQ (compressE k.γH k.ρH w) := by
  rw [hden, hco, toQ_compressE]
  congr 1
  funext c
  rw [hw c]; rfl

theorem z0Q : K6.toQ 0 = liftQ (K := KC) deltaF (0 : ZMod p) := by
  rw [K6.toQ_zero, liftQ, map_zero, map_zero]

theorem hX_eq (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) :
    hden deltaF chals 5 vX = K6.toQ (Walk.hX k) :=
  hden_eq k chals hco 5 vX _ fun c => by fin_cases c <;> exact z0Q
theorem hPL_eq (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) :
    hden deltaF chals 4 vPL = K6.toQ (Walk.hPL k) :=
  hden_eq k chals hco 4 vPL _ fun c => by
    fin_cases c
    · exact z0Q
    · show K6.toQ (lq 2) = liftQ deltaF (if (1 : ℕ) = 1 then (2 : ZMod p) else 0)
      rw [toQ_lq, if_pos rfl]; rfl
    · exact z0Q
    · exact z0Q
theorem hPR_eq (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) :
    hden deltaF chals 4 vPR = K6.toQ (Walk.hPR k) :=
  hden_eq k chals hco 4 vPR _ fun c => by
    fin_cases c
    · exact z0Q
    · show K6.toQ (lq 3) = liftQ deltaF (if (1 : ℕ) = 1 then (3 : ZMod p) else 0)
      rw [toQ_lq, if_pos rfl]; rfl
    · exact z0Q
    · exact z0Q

section Roles
variable (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) (i : Fin 1)
include hinj hco

theorem dX_eq :
    WalkTraceHQ.dRow deltaF 1 powerBasis3 hn nodes orbit chals pubs WalkHC.xKeyH (wcolQ k mL mR chals) 0 0 0 0 i =
      K6.toQ (Walk.hX k) := by
  have := (dRow0 deltaF powerBasis3 hn nodes orbit chals pubs hinj (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mL mR i).1
  rw [hX_eq k chals hco] at this; exact this
theorem dL_eq :
    WalkTraceHQ.dRow deltaF 1 powerBasis3 hn nodes orbit chals pubs WalkHC.recLH (wcolQ k mL mR chals) 0 0 0 0 i =
      K6.toQ (Walk.hPL k) := by
  have := (dRow0 deltaF powerBasis3 hn nodes orbit chals pubs hinj (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mL mR i).2.1
  rw [hPL_eq k chals hco] at this; exact this
theorem dR_eq :
    WalkTraceHQ.dRow deltaF 1 powerBasis3 hn nodes orbit chals pubs WalkHC.recRH (wcolQ k mL mR chals) 0 0 0 0 i =
      K6.toQ (Walk.hPR k) := by
  have := (dRow0 deltaF powerBasis3 hn nodes orbit chals pubs hinj (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mL mR i).2.2
  rw [hPR_eq k chals hco] at this; exact this

/-- **The handle role values**: `K3.toK (hrole t) = roleVal (rolesF …) t i`. -/
theorem hrole_eq (t : ℕ) (ht : t < 10) :
    K3.toK (Walk.hrole k mL mR t) = WalkTraceHQ.roleVal deltaF (rolesQ k mL mR hn nodes orbit chals pubs) t i := by
  have i0 : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
  have hX := dX_eq k mL mR hn nodes orbit chals pubs hinj hco
  have hL := dL_eq k mL mR hn nodes orbit chals pubs hinj hco
  have hR := dR_eq k mL mR hn nodes orbit chals pubs hinj hco
  have xi : (rolesQ k mL mR hn nodes orbit chals pubs).xi i = K6.toQ (Walk.hX k)⁻¹ := by
    rw [K6.toQ_inv, ← hX i]; rfl
  have pl : (rolesQ k mL mR hn nodes orbit chals pubs).pl i = K6.toQ (Walk.hPL k)⁻¹ := by
    rw [K6.toQ_inv, ← hL i]; rfl
  have pr : (rolesQ k mL mR hn nodes orbit chals pubs).pr i = K6.toQ (Walk.hPR k)⁻¹ := by
    rw [K6.toQ_inv, ← hR i]; rfl
  have xa : (rolesQ k mL mR hn nodes orbit chals pubs).xa i = K6.toQ (Walk.hX k)⁻¹ := by
    show ∑ j ∈ Finset.range ((i : ℕ) + 1), (WalkTraceHQ.dN deltaF 1 powerBasis3 hn nodes orbit chals pubs
      (wcolQ k mL mR chals) 0 0 0 0 WalkHC.xKeyH j)⁻¹ = _
    rw [i0, Fin.val_mk, zero_add, Finset.sum_range_one, WalkTraceHQ.dN, dif_pos (by norm_num), hX, K6.toQ_inv]
  have m10 : WalkTraceH.cN 0 (wcolQ k mL mR chals WChip.mL) = (mL : ZMod p) := by
    rw [WalkTraceH.cN, dif_pos (by norm_num)]; rfl
  have m11 : WalkTraceH.cN 0 (wcolQ k mL mR chals WChip.mR) = (mR : ZMod p) := by
    rw [WalkTraceH.cN, dif_pos (by norm_num)]; rfl
  have pa : (rolesQ k mL mR hn nodes orbit chals pubs).pa i = K6.toQ (Walk.hPA k mL mR) := by
    show ∑ j ∈ Finset.range ((i : ℕ) + 1),
      (liftQ deltaF (WalkTraceH.cN j (wcolQ k mL mR chals WChip.mL)) *
        (WalkTraceHQ.dN deltaF 1 powerBasis3 hn nodes orbit chals pubs (wcolQ k mL mR chals) 0 0 0 0
          WalkHC.recLH j)⁻¹ +
      liftQ deltaF (WalkTraceH.cN j (wcolQ k mL mR chals WChip.mR)) *
        (WalkTraceHQ.dN deltaF 1 powerBasis3 hn nodes orbit chals pubs (wcolQ k mL mR chals) 0 0 0 0
          WalkHC.recRH j)⁻¹) = _
    rw [i0, Fin.val_mk, zero_add, Finset.sum_range_one, WalkTraceHQ.dN, WalkTraceHQ.dN, dif_pos (show 0 < 1 by norm_num),
      dif_pos (show 0 < 1 by norm_num), hL,
      hR, m10, m11, Walk.hPA, K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq, K6.toQ_inv, K6.toQ_inv]
  clear hX hL hR m10 m11
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t
  · rw [show Walk.hrole k mL mR 0 = (Walk.hX k)⁻¹.re from rfl, ← re_toQ, ← xi]; rfl
  · rw [show Walk.hrole k mL mR 1 = (Walk.hX k)⁻¹.im from rfl, ← im_toQ, ← xi]; rfl
  · rw [show Walk.hrole k mL mR 2 = (Walk.hPL k)⁻¹.re from rfl, ← re_toQ, ← pl]; rfl
  · rw [show Walk.hrole k mL mR 3 = (Walk.hPL k)⁻¹.im from rfl, ← im_toQ, ← pl]; rfl
  · rw [show Walk.hrole k mL mR 4 = (Walk.hPR k)⁻¹.re from rfl, ← re_toQ, ← pr]; rfl
  · rw [show Walk.hrole k mL mR 5 = (Walk.hPR k)⁻¹.im from rfl, ← im_toQ, ← pr]; rfl
  · rw [show Walk.hrole k mL mR 6 = (Walk.hX k)⁻¹.re from rfl, ← re_toQ, ← xa]; rfl
  · rw [show Walk.hrole k mL mR 7 = (Walk.hX k)⁻¹.im from rfl, ← im_toQ, ← xa]; rfl
  · rw [show Walk.hrole k mL mR 8 = (Walk.hPA k mL mR).re from rfl, ← re_toQ, ← pa]; rfl
  · rw [show Walk.hrole k mL mR 9 = (Walk.hPA k mL mR).im from rfl, ← im_toQ, ← pa]; rfl
  · omega

end Roles


theorem coordN_toK (x : K3) (m : ℕ) : coordN powerBasis3 (K3.toK x) m = limbZ x (m % 3) := by
  rw [coordN, coord_K]

theorem wcolQ_eq (αW : K3) (hα : chals 0 = K3.toK αW) :
    wcolQ k mL mR chals = walkCol deltaF powerBasis3 1 (wvalsQ k αW mL mR) := by
  simp only [wcolQ, wcol, hα]

/-- **Column `c < 166` of the executable walk fill = the honest builder's column function** (`certUp` of `colHQ`
of `walkCol (wvals …)` with the role fill `rolesF`, under `fullCol`). -/
theorem walkColZ_eq (αW : K3) (hinj : Function.Injective nodes)
    (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) (hα : chals 0 = K3.toK αW)
    (c : ℕ) (hc : c < 166) (i : Fin 1) :
    Walk.colZ k αW mL mR c =
      fullCol hn (HonestK8.certUp (WalkTraceHQ.colHQ deltaF 1 powerBasis3 (wcolQ k mL mR chals) 0 0 0 0
        (rolesQ k mL mR hn nodes orbit chals pubs)) (fun _ => 0)) c i := by
  have i0 : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
  by_cases h0 : c = 0
  · subst h0; simp [Walk.colZ, fullCol, i0]
  by_cases h1 : c = 1
  · subst h1; simp [Walk.colZ, fullCol, i0]
  simp only [fullCol, if_neg h0, if_neg h1, HonestK8.certUp]
  by_cases hcert : 14 ≤ c ∧ c < 21
  · rw [if_pos hcert]
    obtain ⟨c1, c2⟩ := hcert
    interval_cases c <;> simp [Walk.colZ, HonestK8.fixVal8, HonestK8.certB8, HonestK8.top8, HonestK8.rem8]
  rw [if_neg hcert]
  simp only [WalkTraceHQ.colHQ, extColF, WalkTraceH.walkTemplate_width]
  by_cases hb : c < 21
  · rw [if_pos hb, wcolQ_eq k mL mR chals αW hα]
    simp only [walkCol, if_pos hb]
    have : 2 ≤ c ∧ c < 14 := by omega
    obtain ⟨c1, c2⟩ := this
    show _ = (wrowQ k αW mL mR).base 1 i c
    interval_cases c <;> simp [Walk.colZ, WalkVals.base, WalkVals.named, wrow, i0]
  rw [if_neg hb]
  by_cases hk : c < 25
  · rw [if_pos hk]
    have : 21 ≤ c := by omega
    interval_cases c <;> simp [Walk.colZ, WalkTraceHQ.new]
  rw [if_neg hk]
  by_cases hr : c < 136
  · rw [if_pos (show c < 132 + (25 - 21) by omega), wcolQ_eq k mL mR chals αW hα]
    simp only [walkCol, if_neg (show ¬ (c - (25 - 21) < 21) by omega)]
    have e1 : c - (25 - 21) - 21 = c - 25 := by omega
    simp only [e1]
    rw [← wrole_eq k αW mL mR i _ (by omega), coord_K]
    simp only [Walk.colZ, if_neg (show ¬ c < 3 by omega), if_neg (show c ≠ 4 by omega),
      if_neg (show c ≠ 10 by omega), if_neg (show c ≠ 11 by omega), if_neg (show ¬ c < 14 by omega),
      if_neg (show ¬ c < 21 by omega), if_neg hk, if_pos hr]
  rw [if_neg (show ¬ c < 132 + (25 - 21) by omega)]
  simp only [WalkTraceHQ.new, if_neg (show c ≠ 21 by omega), if_neg (show c ≠ 22 by omega),
    if_neg (show c ≠ 23 by omega), if_neg (show c ≠ 24 by omega), if_pos (show 136 ≤ c ∧ c < 166 from ⟨by omega, hc⟩)]
  rw [← hrole_eq k mL mR hn nodes orbit chals pubs hinj hco i _ (by omega), coordN_toK]
  simp only [Walk.colZ, if_neg (show ¬ c < 3 by omega), if_neg (show c ≠ 4 by omega),
    if_neg (show c ≠ 10 by omega), if_neg (show c ≠ 11 by omega), if_neg (show ¬ c < 14 by omega),
    if_neg (show ¬ c < 21 by omega), if_neg hk, if_neg hr, if_pos hc]


/-- **The executable walk fill's interpolants ARE the honest `walkChipJ8` trace `trW0`**, column by column. -/
theorem walkTrace_eq (αW : K3) (hinj : Function.Injective nodes)
    (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩) (hα : chals 0 = K3.toK αW) (j : Fin 166) :
    Lagrange.interpolate Finset.univ nodes (fun i => Walk.cols k αW mL mR j i) =
      trW0 deltaF powerBasis3 hn nodes orbit chals pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mL mR j := by
  unfold trW0 honestQ
  congr 1
  funext i
  exact walkColZ_eq k mL mR hn nodes orbit chals pubs αW hinj hco hα j j.isLt i

end WHandle

/-! ## 4. At the frame coins -/

section WFrame
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **At the frame coins** (`coOf χe`, walk coin `chalsMJ8E χe 0`, `chals = chalsMJ8 deltaF (toχ χe)`). -/
theorem walkTrace_eq_frame (χe : CoinsE) (mL mR : ℕ) (hn : 0 < 1) (nodes : Fin 1 → ZMod p)
    (hinj : Function.Injective nodes) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h) (pubs : ℕ → KC)
    (j : Fin 166) :
    Lagrange.interpolate Finset.univ nodes (fun i => Walk.cols (coOf χe) (chalsMJ8E χe 0) mL mR j i) =
      trW0 deltaF powerBasis3 hn nodes orbit (VerJ8.chalsMJ8 deltaF (toχ χe)) pubs
        (K6.toQ (γVE χe)) (K6.toQ (ρVE χe)) (K6.toQ (zE χe)) mL mR j := by
  rw [chalsMJ8_eq]
  exact walkTrace_eq (coOf χe) mL mR hn nodes orbit _ pubs (chalsMJ8E χe 0) hinj (hcoins_frame χe) rfl j

/-- The same for the checker's `interpOf` (walk chip of the input, nodes `ω^i`). -/
theorem interpOf_walk (χe : CoinsE) (mL mR : ℕ) (hw : ℕ) (ω : Gold)
    (hinj : Function.Injective (nodesOf ⟨hw, 1, ω, Walk.cols (coOf χe) (chalsMJ8E χe 0) mL mR⟩)) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (pubs : ℕ → KC) (j : Fin 166) :
    interpOf ⟨hw, 1, ω, Walk.cols (coOf χe) (chalsMJ8E χe 0) mL mR⟩ j =
      trW0 deltaF powerBasis3 (by norm_num) (nodesOf ⟨hw, 1, ω, Walk.cols (coOf χe) (chalsMJ8E χe 0) mL mR⟩) orbit
        (VerJ8.chalsMJ8 deltaF (toχ χe)) pubs (K6.toQ (γVE χe)) (K6.toQ (ρVE χe)) (K6.toQ (zE χe)) mL mR j :=
  walkTrace_eq_frame χe mL mR _ _ hinj orbit pubs j

end WFrame

end Nock.V1J8.FillMem
