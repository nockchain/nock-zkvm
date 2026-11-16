/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProviderG.lean

`ProviderG` / `BudgetG` / `ClaimSpecG` / `AcceptsGenericG` are `ProviderJ8.Provider` / `Budget` / `ClaimSpec` /
  `AcceptsGeneric` with the public record `Pub`, the message `Msg`, the traces `Tr`, the coins `Ch` and the rows `Rows`
  as type parameters; the five fields (`hprov hbal hclaim hsize hbud`) are the same.  `Bal` and `SizeClass` are the J-8
  ones (`ProviderJ8.Bal`, `ProviderJ8.SizeClass`).

  * `ProviderJ8.Provider.toG`, `ClaimSpec.toG`, `Budget.toG`: the J-8 objects as generic ones;
  * `acceptsGenericG_j8_iff`: at the J-8 types `AcceptsGenericG (Ps.map toG) C.toG bud.toG` is exactly
    `ProviderJ8.AcceptsGeneric Ps C bud`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProviderG

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8 (Bal SizeClass)

noncomputable section

section Def
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **One provider over `Pub / Msg / Tr`, coins `Ch`**: same four fields as `ProviderJ8.Provider`. -/
structure ProviderG (Pub Msg Tr Ch : Type) where
  chipOK : (ℕ → ZMod p) → Pub → Msg → Tr → Ch → Prop
  absentOK : Pub → Msg → Prop
  term : Bal → Pub → Msg → 𝕂′
  size : SizeClass → Pub → ℕ

/-- **The size and budget component** over `Pub`, `Rows`. -/
structure BudgetG (Pub Rows : Type) where
  offset : SizeClass → Pub → ℕ
  cap : SizeClass → ℕ
  ok : Pub → Rows → ℕ → Prop

/-- **The claim component** over `Pub / Msg / Ch`. -/
structure ClaimSpecG (Pub Msg Ch : Type) where
  pubs : P8PublicClaim → Msg → Ch → ℕ → ZMod p
  verifierTerm : Bal → P8PublicClaim → Pub → Msg → Ch → 𝕂′
  checks : Nock.Jet.Registry → P8PublicClaim → Pub → Msg → Prop

/-- **The generic verifier predicate over arbitrary record types**: the five fields of `ProviderJ8.AcceptsGeneric`. -/
structure AcceptsGenericG {Pub Msg Tr Ch Rows : Type} (Ps : List (ProviderG (K := K) δ Pub Msg Tr Ch))
    (C : ClaimSpecG (K := K) δ Pub Msg Ch) (bud : BudgetG Pub Rows)
    (Pb : Pub) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Ch) (M : Msg) (tr : Tr) (r : Rows) (g : ℕ) :
    Prop where
  hprov : ∀ P ∈ Ps, P.chipOK (C.pubs c M χ) Pb M tr χ ∨ P.absentOK Pb M
  hbal : ∀ β : Bal, (Ps.map fun P => P.term β Pb M).sum + C.verifierTerm β c Pb M χ = 0
  hclaim : C.checks Rg c Pb M
  hsize : ∀ s : SizeClass, (Ps.map fun P => P.size s Pb).sum + bud.offset s Pb < bud.cap s
  hbud : bud.ok Pb r g

/-! ### The J-8 objects as generic ones -/

variable {δ}

/-- A J-8 provider as a generic one at the J-8 types. -/
def _root_.Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8.Provider.toG
    (P : ProviderJ8.Provider (K := K) δ) :
    ProviderG (K := K) δ (PubJ8 p) (MsgJ8' p K δ) (TrJ8 (ZMod p)) (Coins frameJ8 K) where
  chipOK := P.chipOK
  absentOK := P.absentOK
  term := P.term
  size := P.size

/-- A J-8 claim component as a generic one. -/
def _root_.Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8.ClaimSpec.toG
    (C : ProviderJ8.ClaimSpec (K := K) δ) :
    ClaimSpecG (K := K) δ (PubJ8 p) (MsgJ8' p K δ) (Coins frameJ8 K) where
  pubs := C.pubs
  verifierTerm := C.verifierTerm
  checks := C.checks

/-- A J-8 budget as a generic one. -/
def _root_.Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8.Budget.toG (bud : ProviderJ8.Budget (p := p)) :
    BudgetG (PubJ8 p) RowsJ8 where
  offset := bud.offset
  cap := bud.cap
  ok := bud.ok

/-- **`acceptsGenericG_j8_iff`**: at the J-8 types the generic predicate over the lifted objects is
`ProviderJ8.AcceptsGeneric`. -/
theorem acceptsGenericG_j8_iff (Ps : List (ProviderJ8.Provider (K := K) δ))
    (C : ProviderJ8.ClaimSpec (K := K) δ) (bud : ProviderJ8.Budget (p := p))
    (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) :
    AcceptsGenericG δ (Ps.map ProviderJ8.Provider.toG) (ProviderJ8.ClaimSpec.toG C) (ProviderJ8.Budget.toG bud)
        Pb Rg c χ M tr r g ↔
      ProviderJ8.AcceptsGeneric δ Ps C bud Pb Rg c χ M tr r g := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.hclaim, ?_, h.hbud⟩
    · intro P hP
      exact h.hprov (ProviderJ8.Provider.toG P) (List.mem_map_of_mem hP)
    · intro β
      have := h.hbal β
      simpa [List.map_map, Function.comp_def, ProviderJ8.Provider.toG, ProviderJ8.ClaimSpec.toG] using this
    · intro s
      have := h.hsize s
      simpa [List.map_map, Function.comp_def, ProviderJ8.Provider.toG, ProviderJ8.Budget.toG] using this
  · intro h
    refine ⟨?_, ?_, h.hclaim, ?_, h.hbud⟩
    · intro P hP
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hP
      exact h.hprov Q hQ
    · intro β
      have := h.hbal β
      simpa [List.map_map, Function.comp_def, ProviderJ8.Provider.toG, ProviderJ8.ClaimSpec.toG] using this
    · intro s
      have := h.hsize s
      simpa [List.map_map, Function.comp_def, ProviderJ8.Provider.toG, ProviderJ8.Budget.toG] using this

end Def

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProviderG

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderG
#print axioms acceptsGenericG_j8_iff
end Axioms
