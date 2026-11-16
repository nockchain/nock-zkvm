/-
**the runtime link gate `linkGate9` and the pure verdict `verdict9`**.
Lifted from earlier prototypes.  The loader (JSON + chip parser) is UNTRUSTED: the verifier exe evaluates `verdict9` on the instance it actually
loaded.  `verdict9 ... = .ok c` gives `famGates ∧ l = 170 ∧ linkGate9 XI c = true ∧ verifyFlatE = .ok `, and `linkGate9_wit` turns the gate
into every datum binder of `exec_e2e_J9A` (see `E2EJ9ARun.lean`).  `claimOf` is an untrusted decoder, re-checked by the gate (hcl/hpin/hat
are equalities with the re-encoding of `c`).
-/
import NockvmE2E.J9A.E2EJ9AToyR
import NockvmE2E.Exec.FamGates
set_option autoImplicit false
set_option maxRecDepth 100000
namespace NockvmE2E.J9A.RunGate9
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9 NockvmE2E.J9A.DatX9Ok NockvmE2E.J9A.InstJ9AW NockvmE2E.J9A.E2EJ9AToyR
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs)

instance : DecidableEq NockvmE2E.Exec.PE.Tok := fun a b =>
  match a, b with
  | .cell, .cell => isTrue rfl
  | .atom x, .atom y => if h : x = y then isTrue (by simp [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .cell, .atom _ => isFalse (by intro h; cases h)
  | .atom _, .cell => isFalse (by intro h; cases h)
instance : DecidableEq NockvmE2E.Exec.PE.NounRec := fun a b =>
  match a, b with
  | ⟨k, n, i, h, l⟩, ⟨k', n', i', h', l'⟩ =>
    if h1 : k = k' ∧ n = n' ∧ i = i' ∧ h = h' ∧ l = l' then
      isTrue (by obtain ⟨e1, e2, e3, e4, e5⟩ := h1; subst e1 e2 e3 e4 e5; rfl)
    else isFalse (by intro e; cases e; exact h1 ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- the numerals the gate reads off the loaded chips (walkJ8 → kroots, walkHQK → krootsV) -/
def numOfId (XI : ExecInst) (id : String) : ℕ :=
  match XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | some t => (chipNumeralF famJ9A t.chip).getD 0
  | none => 0
def kOf (XI : ExecInst) : ℕ := numOfId XI "walkChipJ8"
def kVOf (XI : ExecInst) : ℕ := if (tabOf XI "walkChipHQK").isSome then numOfId XI "walkChipHQK" else 0

/-- every premise of `witness9` other than `shapeOkF` (a famGates gate), at `k := kOf XI`, `kV := kVOf XI` -/
def LinkOK9 (XI : ExecInst) (c : P8PublicClaim) : Prop :=
  hNof XI "jetChipJ8" = 0 ∧ 1 ≤ kOf XI ∧ kOf XI ≤ hNof XI "walkChipJ8" ∧
  ((tabOf XI "walkChipHQK").isSome = true → 1 ≤ kVOf XI ∧ kVOf XI ≤ hNof XI "walkChipHQK") ∧
  ((tabOf XI "walkChipHQK").isSome = false → kVOf XI = 0) ∧
  ((∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < P) ∧
   (∀ x ∈ (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c),
      x.leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ hNof XI "atomChipHQL" + 2) ∧
   isCellN c.formula = true) ∧
  XI.pubIn.claimCells = (claimCells c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ++
      (claimBigs P c).map (NockvmE2E.J8.RVUJ8.claimRec (claimNoun c)) ∧
  XI.pubIn.pins = [] ∧
  XI.pubIn.atoms = (List.finRange 3).filterMap (fun i => match claimNoun c i with
      | .atom v => if P ≤ v then none else some (i.val, v) | .cell _ _ => none) ∧
  (∀ t : Fin XI.tabs.size, (chipNumeralF famJ9A XI.tabs[t].chip).getD 0 = numP XI (kOf XI) (kVOf XI) (sigma9 XI t)) ∧
  (hNof XI "jetChipJ8" = 0 → XI.pubLay.present[3]! = false) ∧
  ((if (tabOf XI "walkChipHQK").isSome then kVOf XI else 0) = 0 → XI.pubLay.present[5]! = false) ∧
  ((tabOf XI "axisChipJ9").isSome = false → XI.pubLay.present[6]! = false) ∧
  ((tabOf XI "splitChipJ9").isSome = false → XI.pubLay.present[7]! = false) ∧
  (∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id ≠ "jetChipJ8")

instance (XI : ExecInst) (c : P8PublicClaim) : Decidable (LinkOK9 XI c) := by unfold LinkOK9; infer_instance

/-- the runtime gate -/
def linkGate9 (XI : ExecInst) (c : P8PublicClaim) : Bool := decide (LinkOK9 XI c)

/-- soundness of the gate: every datum binder of exec_e2e_J9A holds at the loaded instance, at claim `c` -/
theorem linkGate9_wit (XI : ExecInst) (c : P8PublicClaim) (h : shapeOkF famJ9A XI = true) (hg : linkGate9 XI c = true) :
    Wit9 XI c (fun _ => True) := by
  have hL : LinkOK9 XI c := of_decide_eq_true hg
  obtain ⟨hJ, hk1, hkW, hV, hV0, ⟨hc1, hc2, hc3⟩, hcl, hpin, hat, hnum, hpJ, hpV, hpX, hpS, hnj⟩ := hL
  exact witness9 XI h hJ (kOf XI) (kVOf XI) hk1 hkW hV hV0 c ⟨hc1, hc2, hc3⟩ hcl hpin hat hnum hpJ hpV hpX hpS hnj _ trivial

/-! ## the claim decoder (UNTRUSTED; total, fuel-bounded so that it is also kernel-evaluable) -/

/-- prefix tokens → noun; `fuel` bounds the depth (≥ token count + 1 suffices) -/
def nounOfToks : ℕ → List PE.Tok → Option (Nock.Noun × List PE.Tok)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .atom n :: r => some (.atom n, r)
  | f + 1, .cell :: r => do
    let (a, r1) ← nounOfToks f r
    let (b, r2) ← nounOfToks f r1
    pure (.cell a b, r2)

/-- UNTRUSTED decoder of the three claim positions from the public input; its output is re-checked by `linkGate9` -/
def claimOf (p : PE.PubIn) : Option P8PublicClaim := do
  let pos (k : ℕ) : Option Nock.Noun :=
    match p.claimCells.find? (·.key == k) with
    | some r => (nounOfToks (r.noun.length + 1) r.noun).map (·.1)
    | none => (p.atoms.find? (·.1 == k)).map (fun kv => .atom kv.2)
  pure ⟨← pos 0, ← pos 1, ← pos 2⟩

/-! ## the pure verdict the exe runs after loading (any loader) -/

/-- gates, `l = 170`, claim decode, link gate, then the flat verifier; returns the claim the exe prints -/
def verdict9 (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List ℕ) (π : FlatProof) : Except String P8PublicClaim :=
  match NockvmE2E.Exec.FamGates.famGatesFail famJ9A XI with
  | some e => .error s!"famGates j9a: {e}"
  | none =>
    if XI.l != 170 then .error "l != 170" else
    match claimOf XI.pubIn with
    | none => .error "claim: undecodable"
    | some c =>
      if !linkGate9 XI c then .error "linkGate9" else
      match verifyFlatE XI H FS z π with
      | .error e => .error e
      | .ok _ => .ok c

theorem verdict9_sound {XI : ExecInst} {H : HFn} {FS : FSFn} {z : List ℕ} {π : FlatProof} {c : P8PublicClaim}
    (h : verdict9 XI H FS z π = .ok c) :
    NockvmE2E.Exec.FamGates.famGates famJ9A XI = true ∧ XI.l = 170 ∧ linkGate9 XI c = true ∧ verifyFlatE XI H FS z π = .ok () := by
  unfold verdict9 at h
  split at h
  · cases h
  · rename_i hf
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i c' hc
        split at h
        · cases h
        · rename_i hg
          split at h
          · cases h
          · rename_i u hv
            cases h
            refine ⟨NockvmE2E.Exec.FamGates.famGatesFail_none.mp hf, ?_, ?_, hv⟩
            · simpa using hl
            · simpa using hg

theorem xi170_of_l {XI : ExecInst} (h : XI.l = 170) : XI170 XI = XI := by
  cases XI
  simp only at h
  subst h
  rfl

/-! ## the gate at the executed literals (kernel evaluation) -/

open Toy9R in
theorem gate_toy : linkGate9 (XI170 toy9R) cToy = true := by decide +kernel
open Toy9R in
theorem gate_toyF : linkGate9 (XI170 toy9RF) cToyF = true := by decide +kernel
open Toy9R in
/-- the gate binds the claim: the right instance with the other instance's claim is rejected -/
theorem gate_toy_wrongclaim : linkGate9 (XI170 toy9R) cToyF = false := by decide +kernel

open Toy9R in
/-- the decoder reads `cToy` off the toy instance's public input (field-wise; `P8PublicClaim` has no `DecidableEq`) -/
theorem claimOf_toy_fields : (claimOf toy9R.pubIn).map (fun c => (c.subject, c.formula, c.result)) =
    some (cToy.subject, cToy.formula, cToy.result) := by decide +kernel

open Toy9R in
theorem claimOf_toy : claimOf toy9R.pubIn = some cToy := by
  have h := claimOf_toy_fields
  rcases hc : claimOf toy9R.pubIn with _ | ⟨s, f, r⟩
  · rw [hc] at h; simp at h
  · rw [hc] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [cToy] at h1 h2 h3 ⊢
    subst h1 h2 h3
    rfl

end NockvmE2E.J9A.RunGate9

#print axioms NockvmE2E.J9A.RunGate9.linkGate9_wit
#print axioms NockvmE2E.J9A.RunGate9.verdict9_sound
#print axioms NockvmE2E.J9A.RunGate9.xi170_of_l
#print axioms NockvmE2E.J9A.RunGate9.gate_toy
#print axioms NockvmE2E.J9A.RunGate9.gate_toyF
#print axioms NockvmE2E.J9A.RunGate9.gate_toy_wrongclaim
#print axioms NockvmE2E.J9A.RunGate9.claimOf_toy
