/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestAttainH.lean

  Additive.

  * `slotAD_congr`: `A` and `D` of a slot read only the trace columns `< 43`, the pole coin and `γ`;
    so they are independent of the inverse limbs (columns 43..51).
  * `honestFill_attainable`: every env has a twin that agrees with it off the nine inverse columns and
    satisfies `HonestFill` (the inverse limbs are `A / D`, written coordinate by coordinate).
  * `rowOfSkelH_hosted`: `rowOfSkelH` hosts `hdN sf1 / tlN sf1` on OP3 by construction; the hosting
    hypothesis of `termVal*_honest` / `accGatesH_honest_rows` is discharged
    (`accGatesH_honest_rowsSkel`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestFillH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowsH
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.SemanticStrategy ComputeTable

noncomputable section

section Hosted

theorem rowOfSkelH_hosted (sk : ComputeRowSkeleton) :
    (rowOfSkelH sk).op = 3 →
      (rowOfSkelH sk).ftth = VclL.hdN (rowOfSkelH sk).sf1 ∧
      (rowOfSkelH sk).fttt = VclL.tlN (rowOfSkelH sk).sf1 := by
  intro h
  rw [rowOfSkelH_op] at h
  simp [rowOfSkelH, h]

end Hosted

section Attain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

theorem slots_len_ents : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents, x.rcd.length ≤ 5 := by decide

theorem slots_len_pair : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ fl a b, S.pair = some (fl, a, b) →
    a.length ≤ 5 ∧ b.length ≤ 5 := by
  intro S hS fl a b hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · simp [slot0] at hp
  · simp [slot1] at hp
  · simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨by decide, by decide⟩

theorem den_congr (r : List ℕ) (hr5 : r.length ≤ 5) (hr : ∀ c ∈ r, c < 43) (eK1 eK2 : Env K)
    (e1 e2 : Env F) (h : ∀ c < 43, e1.trace c = e2.trace c)
    (hγ : eK1.chal chalGammaL = eK2.chal chalGammaL) (hρ : eK1.chal chalRhoL = eK2.chal chalRhoL) :
    evalMQ (ChipH.den r : MixedExpr ℚ) eK1 e1 = evalMQ (ChipH.den r : MixedExpr ℚ) eK2 e2 := by
  rw [evalMQ_den eK1 e1 r hr5, evalMQ_den eK2 e2 r hr5]
  simp only [coinsOf, hγ, hρ]
  rw [entKey_congr (K := K) r hr e1 e2 h]

theorem slotAD_congr (S : SlotSpec ℚ) (hS : S ∈ (slots : List (SlotSpec ℚ))) (eK1 eK2 : Env K)
    (e1 e2 : Env F) (h : ∀ c < 43, e1.trace c = e2.trace c)
    (hγ : eK1.chal chalGammaL = eK2.chal chalGammaL) (hρ : eK1.chal chalRhoL = eK2.chal chalRhoL) :
    slotAR e1 eK1 S = slotAR e2 eK2 S ∧ slotDR e1 eK1 S = slotDR e2 eK2 S := by
  have hact : ∀ x ∈ S.ents, evalQ x.act e1 = evalQ x.act e2 :=
    fun x hx => evalQ_congr 43 _ (slots_read S hS x hx).1 e1 e2 h
  have hden : ∀ x ∈ S.ents, evalMQ (ChipH.den x.rcd : MixedExpr ℚ) eK1 e1 =
      evalMQ (ChipH.den x.rcd : MixedExpr ℚ) eK2 e2 :=
    fun x hx => den_congr x.rcd (slots_len_ents S hS x hx) (slots_read S hS x hx).2 eK1 eK2 e1 e2 h hγ hρ
  have hmapA : S.ents.map (fun x => evalQ x.act e1) = S.ents.map (fun x => evalQ x.act e2) :=
    List.map_congr_left hact
  have hmapD : S.ents.map (fun x => algebraMap F K (evalQ x.act e1) * evalMQ (ChipH.den x.rcd : MixedExpr ℚ) eK1 e1) =
      S.ents.map (fun x => algebraMap F K (evalQ x.act e2) * evalMQ (ChipH.den x.rcd : MixedExpr ℚ) eK2 e2) :=
    List.map_congr_left fun x hx => by rw [hact x hx, hden x hx]
  unfold slotAR slotDR
  rw [hmapA, hmapD]
  rcases hp : S.pair with _ | ⟨fl, a, b⟩
  · simp
  · obtain ⟨hfl, ha, hb⟩ := slots_pair_read S hS fl a b hp
    obtain ⟨ha5, hb5⟩ := slots_len_pair S hS fl a b hp
    have hf : e1.trace fl = e2.trace fl := h fl hfl
    have h1 := den_congr a ha5 ha eK1 eK2 e1 e2 h hγ hρ
    have h2 := den_congr b hb5 hb eK1 eK2 e1 e2 h hγ hρ
    simp [evalQ_cc, hf, h1, h2]

variable [FiniteDimensional F K]

/-- Coordinate `j` of `x` (zero off `[0, 3)`). -/
def coordNA (b : Basis (Fin 3) F K) (x : K) (j : ℕ) : F := if h : j < 3 then coord b x ⟨j, h⟩ else 0

/-- The honest value of a slot's inverse: `A / D` at the given row env. -/
def slotInvVal (b : Basis (Fin 3) F K) (eF : Env F) (S : SlotSpec ℚ) : K :=
  slotAR eF (gE b eF) S * (slotDR eF (gE b eF) S)⁻¹

/-- The trace with the nine inverse columns (43..51) overwritten by the coordinates of the honest inverses. -/
def fillTrace (b : Basis (Fin 3) F K) (eF : Env F) (i : ℕ) : F :=
  if 43 ≤ i ∧ i < 46 then coordNA b (slotInvVal b eF slot0) (i - 43)
  else if 46 ≤ i ∧ i < 49 then coordNA b (slotInvVal b eF slot1) (i - 46)
  else if 49 ≤ i ∧ i < 52 then coordNA b (slotInvVal b eF slot2) (i - 49)
  else eF.trace i

def fillEnv (b : Basis (Fin 3) F K) (eF : Env F) : Env F := { eF with trace := fillTrace b eF }

theorem limb_fill (b : Basis (Fin 3) F K) (eF : Env F) (S : SlotSpec ℚ) (base : ℕ)
    (hb : ∀ k : Fin 3, fillTrace b eF (base + (k : ℕ)) = coordNA b (slotInvVal b eF S) (k : ℕ)) :
    limbVal b (fillTrace b eF) base = slotInvVal b eF S := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  rw [hb k]
  simp [coordNA, k.isLt]

/-- **`HonestFill` is attainable**: the env with the nine inverse columns overwritten by the coordinates of
`A / D` (read at the original) agrees with the original on every column `< 43`, the coins and the publics,
and satisfies `HonestFill`.  Nothing is assumed: `A` and `D` read only columns `< 43` and the coins
(`slotAD_congr`), so they do not move when the inverse columns are rewritten. -/
theorem honestFill_attainable (b : Basis (Fin 3) F K) (eF : Env F) :
    (∀ c < 43, (fillEnv b eF).trace c = eF.trace c) ∧ (fillEnv b eF).chal = eF.chal ∧
      (fillEnv b eF).pub = eF.pub ∧ (fillEnv b eF).traceNext = eF.traceNext ∧
      HonestFill b (fillEnv b eF) := by
  refine ⟨fun c hc => ?_, rfl, rfl, rfl, ?_⟩
  · show fillTrace b eF c = _
    unfold fillTrace
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro S hS
    have hS' : S ∈ (slots : List (SlotSpec ℚ)) := hS
    have hcong := slotAD_congr S hS' (gE b (fillEnv b eF)) (gE b eF) (fillEnv b eF) eF
      (fun c hc => by
        show fillTrace b eF c = _
        unfold fillTrace
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
      rfl rfl
    show limbVal b (fillTrace b eF) S.inv = slotAR (fillEnv b eF) _ S * (slotDR (fillEnv b eF) _ S)⁻¹
    rw [hcong.1, hcong.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · exact limb_fill b eF _ 43 (fun k => by
        have := k.isLt
        unfold fillTrace
        rw [if_pos (by omega)]; congr 1; omega)
    · exact limb_fill b eF _ 46 (fun k => by
        have := k.isLt
        unfold fillTrace
        rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega)
    · exact limb_fill b eF _ 49 (fun k => by
        have := k.isLt
        unfold fillTrace
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega)

end Attain

end

section Wired
variable {F K : Type} [Field F] [Field K] [Algebra F K]

open Classical in
/-- **The 18 accumulator gates at the honest rows `rowOfSkelH (sk j)`, hosting derived.**  The OP3 hosting
hypothesis of `accGatesH_honest_rows` is `rowOfSkelH_hosted`; `HonestFill` is attainable
(`honestFill_attainable`). -/
theorem accGatesH_honest_rowsSkel (b : Basis (Fin 3) F K) (N i : ℕ) (hi : i < N) (envs : ℕ → Env F)
    (cells : List Noun) (sk : ℕ → ComputeRowSkeleton) (fst lst : ℕ → F)
    (hrow : ∀ j < N, (rowOfSkelH (sk j)).Sem ∧ AtRow cells (rowOfSkelH (sk j)) (fst j) (lst j) (envs j) ∧
      HonestFill b (envs j) ∧ NotBadRow (gE b (envs j)) (envs j))
    (h11 : (envs i).trace 11 = if i = 0 then 1 else 0)
    (h12 : (envs i).trace 12 = if i + 1 = N then 1 else 0)
    (haX : ∀ k : Fin 3, (envs i).trace (accX + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsX (F := F)) (envs j)) k)
    (haXn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accX + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsX (F := F)) (envs j)) k)
    (haP : ∀ k : Fin 3, (envs i).trace (accP + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsP (F := F)) (envs j)) k)
    (haPn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accP + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsP (F := F)) (envs j)) k)
    (hpx : ∀ k : Fin 3, (envs i).pub (pubRhoX + k) =
      coord b (rxTot b cells (fun j => rowOfSkelH (sk j)) envs N) k)
    (hpp : ∀ k : Fin 3, (envs i).pub (pubRhoP + k) =
      coord b (rpTot b cells (fun j => rowOfSkelH (sk j)) envs N) k) :
    ∀ g ∈ (accGatesH : List (CoeffExpr ℚ)).map (mapC (fun q : ℚ => (q : F))),
      g.eval (envs i) = 0 :=
  accGatesH_honest_rows b N i hi envs cells (fun j => rowOfSkelH (sk j)) fst lst
    (fun j hj => by
      obtain ⟨hs, hE, hf, hn⟩ := hrow j hj
      exact ⟨hs, hE, rowOfSkelH_hosted (sk j), hf, hn⟩)
    h11 h12 haX haXn haP haPn hpx hpp

end Wired


end Nock.NockVMROM.Thm54.VclL.Handle
