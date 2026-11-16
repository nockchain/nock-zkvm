/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/RowSemSatX9.lean

* **`recOKI_of_9`** (LINK bridge (b)) — on a record of class `≠ 1` (every old-row record, `recClass_old`),
    `RecOK9 ⇒ RecOKI`: the `walkRecA` root `(2, rv)` that `PreI`
    supplies denotes an atom (`DenOKX.big`) whose `valId` is `V rv` (`DenOKX9.k2`), so `WalkAOK9`'s `V`-read is
    `WalkAOK`'s `D`-read; every other class-`0` record is `RecOKA`'s `RecOK` verbatim.
  * **`rowSemX9_of_chip`** — all 20 chip states (`csIdx`): old states through `activeX9_eq`, `recOKI_of_9` and
    `rowSemX9_old`; `s0B`, `s10B`, `s10S` through `sem_s0B`, `sem_s10B`, `sem_s10S`.  The old states take the
    J-8 antecedent `PreI` on their records (`hpre`) and C-2's `HalvingOK` (`hv`) as hypotheses: they are the
    guarded pipeline's obligations (RowSemIJ8 discharges `PreI` through the tree, not per row).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemChipX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LocalVSX9I

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9

open Nock Nock.Reified Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (mapC)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (activeX RecOK HalvingOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8 (RecOKA WalkAOK IsWalkA)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (PreI PreS RecOKI)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I (RowSemX9I)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.Jet (Registry)

variable {p : ℕ} [Fact p.Prime] {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry}

/-! ## 1. LINK bridge (b): `RecOK9 ⇒ RecOKI` off class `1` -/

/-- **LINK bridge (b).**  Off the `TAG_ax` class, a served genuine twin record is a served genuine J-8 record in
the implication form. -/
theorem recOKI_of_9 (hD : DenOKX9 p D V) {comb : ℕ → Noun} {r : List ℕ × Bal} (hc : recClass r ≠ 1)
    (h : RecOK9 D V R comb r) : RecOKI D R comb r := by
  intro hpre
  obtain ⟨l, bl⟩ := r
  by_cases hw : IsWalkA (l, bl)
  · obtain ⟨hs, hl⟩ := hw
    simp only at hs hl
    subst hs
    have h2 : recClass (l, .s) = 2 := by simp [recClass, hl]
    have e : RecOK9 D V R comb (l, .s) = WalkAOK9 V comb l := by
      unfold RecOK9; rw [h2]; rfl
    rw [e] at h
    have ew : RecOKA D R comb (l, .s) = WalkAOK D comb l := by
      have hw' : IsWalkA (l, .s) := by unfold IsWalkA; exact ⟨rfl, hl⟩
      unfold RecOKA; simp only [hw', ↓reduceIte]
    rw [ew]
    match l, hl with
    | [rv, ax, lk, lv], _ =>
      obtain ⟨n, hV, h0, h1⟩ := h
      simp only [PreI, PreS, ite_true] at hpre
      obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hpre
      obtain ⟨n', rfl, -⟩ := hD.base.big _ _ hX
      have hk := hD.k2 _ _ hX
      rw [hV] at hk
      cases Option.some.inj hk
      exact ⟨n, hX, h0, h1⟩
  · have h0 : recClass (l, bl) = 0 := by
      by_cases hs : bl = .s
      · subst hs
        have hl : l.length ≠ 4 := fun hl => hw (by unfold IsWalkA; exact ⟨rfl, hl⟩)
        simp only [recClass] at hc ⊢
        split_ifs at hc ⊢ <;> simp_all
      · cases bl <;> simp_all [recClass]
    have e : RecOK9 D V R comb (l, bl) = RecOK D R (fun _ _ => (0, 0)) (l, bl) := by
      unfold RecOK9; rw [h0]; rfl
    have ea : RecOKA D R comb (l, bl) = RecOK D R (fun _ _ => (0, 0)) (l, bl) := by
      unfold RecOKA; simp only [hw, ↓reduceIte]
    rw [e] at h
    rw [ea]
    exact h

/-! ## 2. Every chip state -/

/-- **Design S6: a twin row decodes to `RowSemX9`, at each of the 20 chip states.** -/
theorem rowSemX9_of_chip (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V) {env : Env (ZMod p)}
    (hB : BaseHoldsX9 env) (cs : CSt) (hOH : OneHotAt9 env (csIdx cs))
    (hOK : ∀ r ∈ activeX9 env, RecOK9 D V R combN r)
    (hpre : ∀ st, cs = .old st → ∀ r ∈ activeX env, PreI D r)
    (hv : ∀ st, cs = .old st → HalvingOK env st) :
    RowSemX9 p D V R (rowOfX9 env cs) := by
  have hp17 : 17 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : p ≤ 2 ^ 64 := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  cases cs with
  | old st =>
    have hN := hOH.newOff (stIdx_lt st)
    refine rowSemX9_old (comb := combN) hD hp17 hB st hOH (fun r hr => ?_) (hv st rfl)
    exact recOKI_of_9 hD (recClass_old hr) (hOK r (by rw [activeX9_eq hN]; exact hr)) (hpre st rfl r hr)
  | s0B => exact sem_s0B hD hp17 hB hOH fun r hr _ => hOK r hr
  | s10B => exact sem_s10B hD hp17 hp64 hB hOH fun r hr _ => hOK r hr
  | s10S => exact sem_s10S hpG hD hB hOH fun r hr _ => hOK r hr

/-- **LINK bridge (b), guarded**: `RecOK9I ⇒ RecOKI` off class `1`. -/
theorem recOKI_of_9I (hD : DenOKX9 p D V) {comb : ℕ → Noun} {r : List ℕ × Bal} (hc : recClass r ≠ 1)
    (h : RecOK9I D V R comb r) : RecOKI D R comb r :=
  fun hpre => recOKI_of_9 hD hc (h fun _ => hpre) hpre

/-- **Design S6 at the guarded obligation**: from `RecOK9I` (no per-row `PreI` hypothesis), every twin row
satisfies the guarded semantics `RowSemX9I` (RowSemIJ8's `rowSemXI_of_chip` on old rows). -/
theorem rowSemX9I_of_chip (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V) {env : Env (ZMod p)}
    (hB : BaseHoldsX9 env) (cs : CSt) (hOH : OneHotAt9 env (csIdx cs))
    (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R combN r)
    (hv : ∀ st, cs = .old st → HalvingOK env st) :
    RowSemX9I p D V R (rowOfX9 env cs) := by
  have hp17 : 17 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : p ≤ 2 ^ 64 := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  cases cs with
  | old st =>
    have hN := hOH.newOff (stIdx_lt st)
    have hB8 := baseHoldsX_of_X9 hB hN
    have hOH8 : OneHotAt env (stIdx st) := fun i hi =>
      hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
    obtain ⟨hI, hk⟩ := RowSemIJ8.rowSemXI_of_chip hD.base hp17 hB8 st hOH8
      (fun r hr => recOKI_of_9I hD (recClass_old hr) (hOK r (by rw [activeX9_eq hN]; exact hr))) (hv st rfl)
    refine ⟨⟨fun hpre => ⟨rfl, hI.1 hpre⟩, ⟨rfl, hI.2⟩⟩, ?_⟩
    intro i hi hc
    have hc' : chainPosX st i = false := by
      have : chainPosX9 (StateX9.ofX st) i = false := hc
      rwa [chainPosX9_ofX] at this
    exact hk i hi hc'
  | s0B => exact ⟨⟨fun _ => (sem_s0B hD hp17 hB hOH hOK).1, trivial⟩, (sem_s0B hD hp17 hB hOH hOK).2⟩
  | s10B =>
    exact ⟨⟨fun _ => (sem_s10B hD hp17 hp64 hB hOH hOK).1, trivial⟩, (sem_s10B hD hp17 hp64 hB hOH hOK).2⟩
  | s10S => exact ⟨⟨fun _ => (sem_s10S hpG hD hB hOH hOK).1, trivial⟩, (sem_s10S hpG hD hB hOH hOK).2⟩

/-! ## 3. At the assembly (`computeChipVCLHX9`) -/

section Sat
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K] {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → ZMod p) (b : Basis (Fin 3) (ZMod p) K) (δ : ZMod p) (chalV pubVal : ℕ → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X])

/-- **Base row facts at the assembly**: `BaseHoldsX9` at every row, read through `permX9`. -/
theorem baseX9_of_sat (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : ZMod p) (hx : x ∈ rowNodeSet nodes) :
    BaseHoldsX9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) := by
  intro t ht
  have h0 := computeChipVCLHX9_sat_twin hn nodes b δ chalV pubVal orbit P hsat x hx
    (mapC (fun q : ℚ => (q : ZMod p)) t)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ht)))
  rwa [eval_mapC_cast, ← RapWalkJ8.evalQX_eq] at h0

/-- **Design S6 at the assembly**: every row of a satisfying `computeChipVCLHX9` trace, read through `permX9`,
decodes to `RowSemX9` at its chip state. -/
theorem rowSemX9_of_sat (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V)
    (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : ZMod p) (hx : x ∈ rowNodeSet nodes) (cs : CSt)
    (hOH : OneHotAt9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) (csIdx cs))
    (hOK : ∀ r ∈ activeX9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)),
      RecOK9 D V R combN r)
    (hpre : ∀ st, cs = .old st →
      ∀ r ∈ activeX (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)), PreI D r)
    (hv : ∀ st, cs = .old st →
      HalvingOK (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) st) :
    RowSemX9 p D V R (rowOfX9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) cs) :=
  rowSemX9_of_chip hpG hD (baseX9_of_sat hn nodes b δ chalV pubVal orbit P hsat x hx) cs hOH hOK hpre hv

/-- **Design S6 at the assembly, guarded.** -/
theorem rowSemX9I_of_sat (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V)
    (hsat : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.Satisfies P)
    (x : ZMod p) (hx : x ∈ rowNodeSet nodes) (cs : CSt)
    (hOH : OneHotAt9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) (csIdx cs))
    (hOK : ∀ r ∈ activeX9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)),
      RecOK9I D V R combN r)
    (hv : ∀ st, cs = .old st →
      HalvingOK (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) st) :
    RowSemX9I p D V R
      (rowOfX9 (Env.viaPerm permX9 (Nock.Framework.Reify.envOfTrace P orbit.ω x chalV pubVal)) cs) :=
  rowSemX9I_of_chip hpG hD (baseX9_of_sat hn nodes b δ chalV pubVal orbit P hsat x hx) cs hOH hOK hv

end Sat

end Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9

open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms recOKI_of_9
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms rowSemX9_of_chip
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms baseX9_of_sat
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms rowSemX9_of_sat
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms rowSemX9I_of_chip
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemSatX9 in
#print axioms rowSemX9I_of_sat
