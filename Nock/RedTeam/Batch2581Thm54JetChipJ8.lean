/-
  Nock/RedTeam/Batch2581Thm54JetChipJ8.lean

  * `jetTemplateJ8_width`: width `71` (`29` base + `14` `𝕂`-roles × `3`), by `rfl`.
  * `gatesJ_degree`, `baseGatesJ_deg`: every gate `≤ 4`.
  * `gatesJ_keyOK`, `baseGatesJ_serialFree`: a handle value is read only as an RLC key entry;
    positive controls `keyOKJ_flags`.
  * `jetChip_sound` / `jetChip_holds`: `Accepted` + `MemoryBB` ⇒ J-3a's skeleton + `LocalOK` +
    `NodeLookupSound` + `ReadsGenuine`, the registry binding, and `HoldsN`.
  * Matmul `n = 2` at `p = 1009`: honest acceptance (`toy_accepted`, `toy_memory`), the soundness
    theorem applied to it (`toy_holds`), a tampered `mul` row rejected.
-/
import Nock.Jet.ChipJ8Toy

set_option autoImplicit false

namespace Nock.RedTeam.Batch2581

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-! ## Statements -/

example {F : Type} [Field F] (δ : F) : (jetTemplateJ8 δ).width 3 = 71 := jetTemplateJ8_width δ

example {F : Type} [Field F] (δ : F) : ∀ g ∈ gatesJ δ, g.degree ≤ 4 := gatesJ_degree δ

example {p : ℕ} [Fact p.Prime] (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) (hA : Accepted R regs ids rows) (hM : MemoryBB R rows den)
    (c i : ℕ) (hc : ids[c]? = some i) (hax : axPosB (R i) = true)
    (rc : CRow (ZMod p)) (hrc : rc ∈ rows) (hpre : rc.pre = callPre R c i)
    (s : Noun) (hs : den (rc.w.kL, rc.w.vL) = some s) :
    den (rc.w.kN, rc.w.vN) = some (compile p (R i)) ∧
    ∃ t : JTable, callRows t c = t ∧ t.map JRow.node = nodesOf (R i) ∧ (∀ r ∈ t, LocalOK p r) ∧
      NodeLookupSound t ∧ ReadsGenuine s t ∧
      ∃ out ∈ t, out.node.id = 0 ∧ den (rc.w.kR, rc.w.vR) = some out.val :=
  jetChip_sound R regs ids rows den hA hM c i hc hax rc hrc hpre s hs

example {p : ℕ} [Fact p.Prime] (R : ℕ → Tpl) (regs ids : List ℕ) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) (hA : Accepted R regs ids rows) (hM : MemoryBB R rows den)
    (c i : ℕ) (hc : ids[c]? = some i) (hax : axPosB (R i) = true) (hT : (R i).WellTyped p)
    (rc : CRow (ZMod p)) (hrc : rc ∈ rows) (hpre : rc.pre = callPre R c i)
    (s : Noun) (hs : den (rc.w.kL, rc.w.vL) = some s) :
    den (rc.w.kN, rc.w.vN) = some (compile p (R i)) ∧
    ∃ e, den (rc.w.kR, rc.w.vR) = some e ∧ (R i).sem p s = some e ∧
      HoldsN ⟨s, compile p (R i), e⟩ :=
  jetChip_holds R regs ids rows den hA hM c i hc hax hT rc hrc hpre s hs

/-- The black box asks only: kind-`0` atoms, genuine export records, the registry claim binding. -/
example {p : ℕ} [Fact p.Prime] (R : ℕ → Tpl) (rows : List (CRow (ZMod p)))
    (den : ZMod p × ZMod p → Option Noun) : MemoryBB R rows den ↔
    (∀ v : ZMod p, den (0, v) = some (.atom v.val)) ∧
    (∀ r ∈ rows, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) → recB den r = true) ∧
    (∀ r ∈ rows, r.pre.kd = .reg → den (r.w.kN, r.w.vN) = some (compile p (R r.pre.id))) :=
  ⟨fun h => ⟨h.den0, h.gen, h.reg⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-! ## Matmul `n = 2` -/

example : toyRowsJ.length = 237 := toyRowsJ_length
example : Accepted toyR [0] [0] toyRowsJ := toy_accepted
example : MemoryBB toyR toyRowsJ toyDen := toy_memory
example : toyDen (toyCall.w.kR, toyCall.w.vR) = some toyCG := toyCall_out

/-! ## Negative controls -/

/-- A tampered `mul` value fails the base gates, so `jetChip_sound` cannot be applied. -/
example : ¬ ∀ r ∈ toyTamperedJ, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod 1009))),
    g.eval (envOf r) = 0 := toy_tampered_rejected

example : keyOKJe (F := ℚ) (.Mul (.Var .traceCur 0) (.Lift (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv Col.vN))) = false :=
  keyOKJ_flags.1

/-! ## Axioms -/

#print axioms jetTemplateJ8_width
#print axioms gatesJ_degree
#print axioms gatesJ_keyOK
#print axioms baseGatesJ_serialFree
#print axioms keyOKJ_flags
#print axioms jetChip_sound
#print axioms jetChip_holds
#print axioms toy_accepted
#print axioms toy_memory
#print axioms toy_holds
#print axioms toy_tampered_rejected

end Nock.RedTeam.Batch2581
