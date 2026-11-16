/-
  Nock/RedTeam/Batch594Thm54FormRSlotGates.lean

  Compiled here:
  * §1 symbol-by-symbol: every gate body evaluates to the authority's polynomial, written out
    independently (`auth*`) over raw environment reads (`slotT_mr1` … `cprime_auth`).
  * §2 the λ coin: source `.challenge 9` lowers to the typed `𝕂` challenge `9`, whose three
    coordinates are raw slots `27, 28, 29`; `lamPow d` compiles to powers of those same three
    slots; the two `𝕂` pins compile to `6` coordinate gates (all limbs of `H` and `T`); the
    record `T` read lowers to the typed `𝕂` helper `1` = limbs `299..301`.  The pre-retype read
    `.var.challenge 9` is coin `3` coordinate `0` (`old_raw_slot9_is_coin3_limb0`).
  * §3 slot-9 census of the deployed extension list: the selector-packed non-IO basis reads
    challenges `{0..6, 10}` only (no slot `9` fold); slot `9` and the `λ`-power indices
    `100..163` occur only in the four sampled-IO gates.
  * §4 degrees: the lowered denominator pins have typed degree `1 / 3 / 3` (record RLC `≤ 2`); `formRLamPins` `≤ 4`; the
    deployed list `≤ 4` (cited).
  * §5 honest: `formR_slots` (general λ) and `sampledDenom_eq_formR` (at `formRDefault`) cited
    by type; an independent concrete check at `p = 769` (`n = 10`).
  * §6 the fixed-63-bit `C'` ignores `c_j` for `j > n − 1` (padding; known caveat, item 8).
-/
import Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch594

open Nock Nock.Reified Nock.NockVMROM.Thm54
open OptimizedComputeSubstitution OptimizedComputeCorrectedFinal OptimizedComputeGateBasis
open OptimizedComputeFormRSlots OptimizedComputeFinalTypedLowering

/-! ## §1 Symbol by symbol, against the authority -/

section Symbols

variable {K : Type} [Field K] (E : Env K)

/-- Authority `G = op₂ + op₅ + op₆ + op₇ + op₈ + op₉` (one-hot selector columns `opCol`). -/
def authG : K := E.trace 2 + E.trace 5 + E.trace 6 + E.trace 7 + E.trace 8 + E.trace 9

/-- Authority `λ` (𝕂 coin), `λ^{n−1}` and `λ^{n−1−d}` as the build sources them. -/
def authLam : K := E.chal 9
def authLamPow (d : ℕ) : K := E.chal (100 + d)

/-- Authority `C' = λ^{n−1} + Σ_{j=1}^{63} c_j λ^{n−1−j}` (`c_j` at column `202 + j − 1`). -/
def authCprime : K :=
  authLamPow E 0 + ∑ j ∈ Finset.range 63, E.trace (202 + j) * authLamPow E (j + 1)

/-- Authority `T` (certificate 𝕂 helper, typed column `299`). -/
def authT : K := E.trace 299

theorem G_auth : (sampledGSel .traceCur).eval E = authG E := by
  simp [sampledGSel, authG, Expr.eval, add_assoc]

theorem opCol_G :
    [Nock.Reified.opCol .s2, Nock.Reified.opCol .s5, Nock.Reified.opCol .s6,
      Nock.Reified.opCol .s7, Nock.Reified.opCol .s8, Nock.Reified.opCol .s9,
      Nock.Reified.opCol .s0] = [2, 5, 6, 7, 8, 9, 0] := rfl

theorem cprime_auth : (sampledCprime .traceCur).eval E = authCprime E := by
  rw [sampledCprime_eval]; rfl

/-- mr₁ `T`: `λ`. -/
theorem slotT_mr1 : (sampledSlotT .traceCur 67).eval E = authLam E := rfl

/-- mr₁ `C'`: `λ^{n−1} + λ^{n−2}`. -/
theorem slotC_mr1 :
    (sampledSlotC .traceCur 67).eval E = authLamPow E 0 + authLamPow E 1 := rfl

/-- mr₂ `T_slot = op₀·T + G·λ`. -/
theorem slotT_mr2 :
    (sampledSlotT .traceCur 75).eval E = E.trace 0 * authT E + authG E * authLam E := by
  simp [sampledSlotT, certTVar, sampledLam, Expr.eval, authT, authLam, ← G_auth]

/-- mr₂ `C_slot = op₀·C' + G·λ^{n−1}`. -/
theorem slotC_mr2 :
    (sampledSlotC .traceCur 75).eval E =
      E.trace 0 * authCprime E + authG E * authLamPow E 0 := by
  simp [sampledSlotC, lamPowVar, Expr.eval, authLamPow, ← G_auth, ← cprime_auth]

/-- mr₃ `op₆·λ + op₉·T`. -/
theorem slotT_mr3 :
    (sampledSlotT .traceCur 83).eval E = E.trace 6 * authLam E + E.trace 9 * authT E := rfl

/-- mr₃ `op₆·λ^{n−1} + op₉·C'`. -/
theorem slotC_mr3 :
    (sampledSlotC .traceCur 83).eval E =
      E.trace 6 * authLamPow E 0 + E.trace 9 * authCprime E := by
  simp [sampledSlotC, lamPowVar, Expr.eval, authLamPow, ← cprime_auth]

/-- The typed reading of `λ^{n−1−d}` on the lowered environment: `n − 1 = pwScaleExp K`
(`Nat.size (ringChar K) − 1`), `0` beyond `n − 1`; in particular `λ^{n−2}` at `d = 1`. -/
theorem lamPow_reading {F : Type} [Field F] [Algebra F K] (env : CorrectedFinalTypedEnv F K)
    (d : ℕ) (hd : d < 64) :
    (lamPowVar d).eval env.toSourceEnv = lamPowVal (env.chal 9) d := by
  simp only [lamPowVar, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv]
  rw [dif_neg (by omega), if_pos (by omega)]
  simp

end Symbols

/-! ## §2 The λ coin: all three limbs -/

theorem lam_lowers : correctedLowerFinal sampledLam = some (.challenge 9) := rfl

theorem lamPow_lowers (d : ℕ) (hd : d < 64) :
    correctedLowerFinal (lamPowVar d) = some (.lamPow ⟨d, hd⟩) := by
  simp only [lamPowVar, correctedLowerFinal]
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp

theorem certT_lowers : correctedLowerFinal (certTVar .traceCur) = some (.certExt 1) := rfl

/-- A record slot read at the successor row would not lower (and so would be dropped by
`filterMap`); the deployed list is length-checked (`corrected_lowered_counts`). -/
theorem certT_next_does_not_lower : correctedLowerFinal (certTVar .traceNext) = none := rfl

section Limbs

variable {F K : Type} [Field F] [Field K] [Algebra F K] (b : Module.Basis (Fin 3) F K)

/-- `λ` = typed `𝕂` challenge `9` = raw slots `27, 28, 29`. -/
theorem lam_raw_slots (k : Fin 3) :
    correctedFinalTypedCompile b (.challenge 9) k = .var .challenge (27 + (k : ℕ)) := rfl

/-- The pre-retype gadget read `.var.challenge 9` is coin `3`, coordinate `0`. -/
theorem old_raw_slot9_is_coin3_limb0 :
    correctedFinalTypedCompile b (.challenge 3) 0 = .var .challenge 9 := rfl

/-- `lamPow d` compiles to the `(n−1−d)`-th power of the same three raw slots `27..29`. -/
theorem lamPow_raw_slots (d : Fin 64) (k : Fin 3) (hd : (d : ℕ) ≤ MemoryTable.pwScaleExp K) :
    correctedFinalTypedCompile b (.lamPow d) k =
      CoordinateCompiler.powVec b (fun k' => .var .challenge (27 + (k' : ℕ)))
        (MemoryTable.pwScaleExp K - d) k := by
  simp [correctedFinalTypedCompile, hd]

/-- `H` / `T` helpers: limbs `296..298` / `299..301`. -/
theorem certExt_limbs (i : Fin 2) (k : Fin 3) :
    correctedFinalTypedCompile b (.certExt i) k = .var .traceCur (296 + 3 * (i : ℕ) + (k : ℕ)) :=
  rfl

theorem lamPins_six : (correctedCompileList b formRLamPins).length = 6 := by
  simp [correctedCompileList, formRLamPins]

/-- The pins' factors read `m_k` (column `202 + 63 + k`) and the 𝕂 coin `9` at `λ^{2^k}`. -/
theorem lamFactor_body (k : Fin 6) :
    formRLamFactor k = .add (.const 1)
      (.mul (.certBase ⟨63 + (k : ℕ), by omega⟩)
        (.sub (.pow (.challenge 9) (2 ^ (k : ℕ))) (.const 1))) := rfl

/-- The pins are deployed. -/
theorem lamPins_deployed (n : ℕ) :
    ∀ g ∈ correctedCompileList b formRLamPins, g ∈ correctedFinalComputeAllGates n b := by
  intro g hg
  simp only [correctedFinalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inr hg)

end Limbs

/-! ## §3 Slot-9 census of the deployed extension source list -/

def chalIdx : Nock.Reified.Expr → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Const _ => []
  | .Add a b => chalIdx a ++ chalIdx b
  | .Sub a b => chalIdx a ++ chalIdx b
  | .Mul a b => chalIdx a ++ chalIdx b
  | .Neg a => chalIdx a
  | .Pow a _ => chalIdx a

/-- The paper-packed non-IO basis reads no slot-`9` fold and no λ power. -/
theorem packed_no_slot9 :
    (paperPackingNonIOGates.flatMap chalIdx).all (fun i => i ≤ 6 || i == 10) = true := by
  decide +kernel

/-- Slot `9` and `100..163` live only in the four sampled-IO gates, and those read nothing
outside `{0, 7, 8, 9} ∪ [100, 164)`. -/
theorem sampledIO_chal_census :
    (finalSampledIOTransitionGates.flatMap chalIdx).all
      (fun i => i == 0 || i == 7 || i == 8 || i == 9 || (100 ≤ i && i < 164)) = true := by
  decide +kernel

theorem sampledIO_reads_slot9 :
    (finalSampledIOTransitionGates.flatMap chalIdx).contains 9 = true := by
  decide +kernel

theorem deployed_ext_is_packed_plus_sampled :
    finalExtTransitionGates = paperPackingNonIOGates ++ finalSampledIOTransitionGates := rfl

theorem endpoints_no_slot9 :
    ([finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit,
        finalAccTerminal, finalLnInit, finalMaskedWalkAccInit].flatMap chalIdx).contains 9
      = false := by
  decide +kernel

/-! ## §4 Degrees -/

theorem denomPin_typed_degree (j : Fin 3) :
    ((correctedLowerFinal (sampledDenomPin .traceCur j)).map
      CorrectedFinalTypedExpr.degree) = some (if j = 0 then 1 else 3) := by
  fin_cases j <;> decide +kernel

theorem slotT_typed_degree (j : Fin 3) :
    ((correctedLowerFinal (sampledSlotT .traceCur (67 + 8 * (j : ℕ)))).map
      CorrectedFinalTypedExpr.degree) = some (if j = 0 then 0 else 2) := by
  fin_cases j <;> decide +kernel

theorem slotC_typed_degree (j : Fin 3) :
    ((correctedLowerFinal (sampledSlotC .traceCur (67 + 8 * (j : ℕ)))).map
      CorrectedFinalTypedExpr.degree) = some (if j = 0 then 0 else 2) := by
  fin_cases j <;> decide +kernel

#check @formRLamPins_degree
#check @correctedFinalComputeAllGates_degree

/-! ## §5 Honest denominators -/

#check @formR_slots
#check @OptimizedComputeFormRDenoms.sampledSlotRecord_eq_formR
#check @OptimizedComputeFormRDenoms.sampledDenom_eq_formR

section Concrete

instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩

theorem n_769 : MemoryTable.pwScaleExp (ZMod 769) = 9 := by
  simp [MemoryTable.pwScaleExp, ZMod.ringChar_zmod_n]
  decide

/-- mr₁ (axis `3`): `T = λ`, `C' = λ^9 + λ^8` at `λ = 2`. -/
theorem honest_axis3 :
    MemoryTable.formRT (2 : ZMod 769) 3 = 2 ∧ MemoryTable.formRC (2 : ZMod 769) 3 = 2^9 + 2^8 := by
  refine ⟨by decide, ?_⟩
  simp only [MemoryTable.formRC, n_769]
  decide

/-- mr₂ / mr₃ constant axis `2`: `T = λ`, `C' = λ^9`. -/
theorem honest_axis2 :
    MemoryTable.formRT (2 : ZMod 769) 2 = 2 ∧ MemoryTable.formRC (2 : ZMod 769) 2 = 2^9 := by
  refine ⟨by decide, ?_⟩
  simp only [MemoryTable.formRC, n_769]
  decide

/-- Axis `6 = 0b110`: `T = λ^2`, `C' = λ^9 + λ^8` (bits `c₁ = 1`, `c₂ = 0`). -/
theorem honest_axis6 :
    MemoryTable.formRT (2 : ZMod 769) 6 = 4 ∧ MemoryTable.formRC (2 : ZMod 769) 6 = 2^9 + 2^8 := by
  refine ⟨by decide, ?_⟩
  simp only [MemoryTable.formRC, n_769]
  decide

/-! ## §6 Fixed 63-bit `C'` against `n − 1` bits (padding; known caveat) -/

/-- At `n = 10` every `c_j`, `j ≥ 10`, enters `C'` with weight `lamPowVal λ j = 0`. -/
theorem high_bits_weight_zero (j : ℕ) (hj : 10 ≤ j) (lam : ZMod 769) :
    lamPowVal lam j = 0 := by
  simp [lamPowVal, n_769]; omega

end Concrete

/-! ## §7 Closure membership -/

open Lean Meta Elab Command

partial def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    for c in ci.type.getUsedConstants ++ v.getUsedConstants do
      if !seen.contains c then stack := stack.push c
  return seen

run_cmd do
  let env ← getEnv
  let cap := closureOf env ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let inNames : List Name :=
    [``sampledSlotT, ``sampledSlotC, ``sampledCprime, ``sampledGSel, ``sampledLam,
     ``lamPowVar, ``sampledRecordRLC, ``sampledDenom, ``formRLamPins, ``formRLamHPin,
     ``formRLamTPin, ``formRLamFactor, ``correctedFinalComputeAllGates, ``lamPowVal]
  for n in inNames do
    unless cap.contains n do throwError m!"expected {n} in nockCompiles_zmod closure"
  let report : List Name :=
    [``OptimizedComputeFormRDenoms.sampledDenom_eq_formR,
     ``OptimizedComputeFormRDenoms.sampledSlotRecord_eq_formR, ``formR_slots,
     ``legacySampledRecordRLC, ``finalFoldChallenge,
     ``OptimizedComputeRangeCertificate.powerPins]
  for n in report do
    logInfo m!"CLOSURE {n} in nockCompiles_zmod: {cap.contains n}"
  logInfo m!"CLOSURE size {cap.size}"

end Nock.RedTeam.Batch594

#print axioms Nock.RedTeam.Batch594.slotC_mr2
#print axioms Nock.RedTeam.Batch594.lamPow_reading
#print axioms Nock.RedTeam.Batch594.lamPow_raw_slots
#print axioms Nock.RedTeam.Batch594.lamPins_six
#print axioms Nock.RedTeam.Batch594.packed_no_slot9
#print axioms Nock.RedTeam.Batch594.sampledIO_chal_census
#print axioms Nock.RedTeam.Batch594.endpoints_no_slot9
#print axioms Nock.RedTeam.Batch594.denomPin_typed_degree
#print axioms Nock.RedTeam.Batch594.honest_axis6
#print axioms Nock.RedTeam.Batch594.high_bits_weight_zero
