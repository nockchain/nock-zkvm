/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProviderJ8.lean

The provider-parametric verifier predicate: `Bal` (the eight balance classes), `SizeClass`, `Provider`, `Budget`,
  `ClaimSpec` and `AcceptsGeneric`.  All types are the CONCRETE J-8 types (`PubJ8`, `MsgJ8'`, `TrJ8`, `Coins frameJ8`),
  per design R3: the J-8 instance is the same proposition regrouped, so the bound transfers by an iff.

  **Reduction against the design's §1 sketch (disclosed):** `Provider` carries `chipOK`, `absentOK`, `term`, `size`
  only.  The sketch's `cons`/`prov` (record lists), `bad` (summands) and `staged` are NOT fields here: no conjunct of
  `AcceptsJ8V` reads them (they matter for completeness, step 2, which is stated over the same data as
  `ComplJ8Obligations`), and adding unused fields would be unchecked text.  `chipOK` additionally takes the claim's
  compute publics `pubV` (J-8 `pubVJ8`, J-9 `pubVJ9`): the compute chip's satisfaction is read at them, and that is what
  J-9 B swaps.  The registry statics `hlay…hlt` live in `ClaimSpec.checks` (the design allows either home).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)

noncomputable section

/-- **The balance classes of J-8** (the eight public equations of `AcceptsJ8V`). -/
inductive Bal
  | export | path | service | validity | atomHandle | atomValidity | fxC | fxA

/-- The size classes: the two public-length checks `hlenC`, `hlenA`. -/
inductive SizeClass
  | rows | atoms

section Def
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **One provider**: its chip's conjuncts (PRESENT case, read at the claim's compute publics), its ABSENT case, its
signed contribution to each balance class, and its sizes.  `absentOK = fun _ _ => False` for a mandatory provider. -/
structure Provider where
  chipOK : (ℕ → ZMod p) → PubJ8 p → MsgJ8' p K δ → TrJ8 (ZMod p) → Coins frameJ8 K → Prop
  absentOK : PubJ8 p → MsgJ8' p K δ → Prop
  term : Bal → PubJ8 p → MsgJ8' p K δ → 𝕂′
  size : SizeClass → PubJ8 p → ℕ

/-- **The size and budget component.**  `cap`/`offset` give the strict size checks; `ok` the public budgets. -/
structure Budget where
  offset : SizeClass → PubJ8 p → ℕ
  cap : SizeClass → ℕ
  ok : PubJ8 p → RowsJ8 → ℕ → Prop

/-- **The claim component** (what J-9 B replaces): the compute publics, the verifier-computed terms of each balance
class, and the static claim / registry checks. -/
structure ClaimSpec where
  pubs : P8PublicClaim → MsgJ8' p K δ → Coins frameJ8 K → ℕ → ZMod p
  verifierTerm : Bal → P8PublicClaim → PubJ8 p → MsgJ8' p K δ → Coins frameJ8 K → 𝕂′
  checks : Nock.Jet.Registry → P8PublicClaim → PubJ8 p → MsgJ8' p K δ → Prop

/-- **The generic verifier predicate.**  Binders as `AcceptsJ8V` plus the provider list, claim and budget. -/
structure AcceptsGeneric (Ps : List (Provider (K := K) δ)) (C : ClaimSpec (K := K) δ) (bud : Budget (p := p))
    (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) : Prop where
  hprov : ∀ P ∈ Ps, P.chipOK (C.pubs c M χ) Pb M tr χ ∨ P.absentOK Pb M
  hbal : ∀ β : Bal, (Ps.map fun P => P.term β Pb M).sum + C.verifierTerm β c Pb M χ = 0
  hclaim : C.checks Rg c Pb M
  hsize : ∀ s : SizeClass, (Ps.map fun P => P.size s Pb).sum + bud.offset s Pb < bud.cap s
  hbud : bud.ok Pb r g

end Def

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8
