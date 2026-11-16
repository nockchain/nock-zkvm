/-
  `CheckedRegistry.lean` is untouched.

  * `VerifiedRegistry.addPrims V prims`: register every `(id, op) ∈ prims` at `primSpec op` (`addPrim`, folded
    right, so the head of `prims` is the outermost entry).
  * `CompiledByP p Rg Rt prims`: every entry whose id is NOT a primitive id is a compiled `Rt` template with the
    chip's public checks (the `CompiledBy` clause), and every primitive id is registered at its `primSpec`.
  * `CheckedRegP`: a `CheckedReg` plus a primitive list with distinct ids; `toVR := C.toCR.toVR.addPrims prims`;
    `CheckedRegP.compiledByP`.
  * **`hRt_hregAx_ofP`** (the twin binder of `hRt_hregAx_of`): at every generated run, every CALLED id is either a
    compiled `Rt` template entry (`hRt`/`hregAx` restricted to the non-primitive called ids) or a primitive entry
    `Rg.R id = some (primSpec op)` with `(id, op) ∈ prims`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry
import Nock.Jet.PrimJ9

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP
open Nock Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.Jet Nock.Jet.Autogen
open Nock.Jet.Prim (PrimOp primSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry

/-- Register every primitive of `prims` (folded right: the head of `prims` is the outermost `add`). -/
def addPrims (V : VerifiedRegistry) : List (ℕ × PrimOp) → VerifiedRegistry
  | [] => V
  | q :: qs => (addPrims V qs).addPrim q.1 q.2

theorem addPrims_R_of_not_mem (V : VerifiedRegistry) :
    ∀ (prims : List (ℕ × PrimOp)) (id : ℕ), id ∉ prims.map Prod.fst → (addPrims V prims).R id = V.R id
  | [], _, _ => rfl
  | q :: qs, id, h => by
    have h1 : id ≠ q.1 := fun e => h (by simp [e])
    have h2 : id ∉ qs.map Prod.fst := fun e => h (List.mem_cons_of_mem _ e)
    show (if id = q.1 then some (primSpec q.2) else (addPrims V qs).R id) = V.R id
    rw [if_neg h1]; exact addPrims_R_of_not_mem V qs id h2

theorem addPrims_R_of_mem (V : VerifiedRegistry) :
    ∀ (prims : List (ℕ × PrimOp)), (prims.map Prod.fst).Nodup →
      ∀ q ∈ prims, (addPrims V prims).R q.1 = some (primSpec q.2)
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q' :: qs, hnd, q, hq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show (if q.1 = q'.1 then some (primSpec q'.2) else (addPrims V qs).R q.1) = some (primSpec q.2)
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [if_pos rfl]
    · have hne : q.1 ≠ q'.1 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hq')
      rw [if_neg hne]; exact addPrims_R_of_mem V qs hnd.2 q hq'

/-- **`CompiledByP`**: non-primitive entries are compiled `Rt` templates with the chip's public checks; every
primitive id is registered at its `primSpec`. -/
def CompiledByP (p : ℕ) (Rg : VerifiedRegistry) (Rt : ℕ → Tpl) (prims : List (ℕ × PrimOp)) : Prop :=
  (∀ id j, Rg.R id = some j → id ∉ prims.map Prod.fst →
    j = ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧
      (Rt id).WellTyped p ∧ ∀ i, (Rt id).ax i < p) ∧
  ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)

/-- `CompiledBy` is `CompiledByP` with no primitive. -/
theorem compiledByP_nil {p : ℕ} {Rg : VerifiedRegistry} {Rt : ℕ → Tpl} (h : CompiledBy p Rg Rt) :
    CompiledByP p Rg Rt [] :=
  ⟨fun id j hj _ => h id j hj, fun q hq => absurd hq List.not_mem_nil⟩

/-- A checked registry with primitives: the template part, the primitive list, distinct primitive ids. -/
structure CheckedRegP (p : ℕ) where
  toCR : CheckedReg p
  prims : List (ℕ × PrimOp)
  ndP : (prims.map Prod.fst).Nodup

def CheckedRegP.toVR {p : ℕ} (C : CheckedRegP p) : VerifiedRegistry := addPrims C.toCR.toVR C.prims

theorem CheckedRegP.compiledByP {p : ℕ} (C : CheckedRegP p) : CompiledByP p C.toVR C.toCR.Rt C.prims := by
  refine ⟨fun id j h hn => ?_, fun q hq => addPrims_R_of_mem _ C.prims C.ndP q hq⟩
  rw [CheckedRegP.toVR, addPrims_R_of_not_mem _ C.prims id hn] at h
  exact C.toCR.compiledBy id j h

/-- **`hRt_hregAx_ofP`: the prim-aware binder pair at a generated run.**  Every called id that is not a primitive
id is a compiled `Rt` entry (with `axPosB`, well typed, axes `< p`); every called primitive id is registered at
its `primSpec`. -/
theorem hRt_hregAx_ofP {p : ℕ} {Rg : VerifiedRegistry} {Rt : ℕ → Tpl} {prims : List (ℕ × PrimOp)}
    (hC : CompiledByP p Rg Rt prims)
    {n : ℕ} {s f r : Noun} {t : NTree SkelX} (h : genX Rg.R n s f = some (t, r)) :
    (∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
        Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p) ∧
    (∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst → ∀ i, (Rt id).ax i < p) ∧
    (∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) := by
  refine ⟨fun id hid hn => ?_, fun id hid hn => ?_, hC.2⟩
  · obtain ⟨j, hj⟩ := called_some h hid
    obtain ⟨rfl, ha, hw, -⟩ := hC.1 id j hj hn
    exact ⟨hj, ha, hw⟩
  · obtain ⟨j, hj⟩ := called_some h hid
    exact (hC.1 id j hj hn).2.2.2

/-- The "Tpl entry or prim entry" form of the binder: every called id is one or the other. -/
theorem called_tpl_or_prim {p : ℕ} {Rg : VerifiedRegistry} {Rt : ℕ → Tpl} {prims : List (ℕ × PrimOp)}
    (hC : CompiledByP p Rg Rt prims)
    {n : ℕ} {s f r : Noun} {t : NTree SkelX} (h : genX Rg.R n s f = some (t, r)) :
    ∀ id ∈ CalledIds t,
      (Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧
        (Rt id).WellTyped p ∧ ∀ i, (Rt id).ax i < p) ∨
      ∃ op, (id, op) ∈ prims ∧ Rg.R id = some (primSpec op) := by
  intro id hid
  by_cases hn : id ∈ prims.map Prod.fst
  · right
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
    exact ⟨q.2, hq, hC.2 q hq⟩
  · left
    obtain ⟨j, hj⟩ := called_some h hid
    obtain ⟨rfl, ha, hw, hx⟩ := hC.1 id j hj hn
    exact ⟨hj, ha, hw, hx⟩

end Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP
#print axioms addPrims_R_of_not_mem
#print axioms addPrims_R_of_mem
#print axioms compiledByP_nil
#print axioms CheckedRegP.compiledByP
#print axioms hRt_hregAx_ofP
#print axioms called_tpl_or_prim
end Axioms
