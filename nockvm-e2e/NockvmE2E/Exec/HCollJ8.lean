import NockvmE2E.Exec.LazyColl
import NockvmE2E.Exec.VKTrace
import NockvmE2E.Exec.E2EOnlineP

/-!  `hcoll_J8`, the discharge of the `hcoll` hypothesis of `exec_e2e_J8V'''` (over `VKcollC`), under the skeleton hypothesis
`hsk` (tree 0 of the side skeletons is the VK tree) and the numeric `hT`.  `hcoll_generic` (LazyColl) + `vkcollC_trace` (VKTrace).
Also `Hof_nil`, the falsifiability witness for `hsk`, and satisfiability of `hsk`/`hT`.  (`XX` for the instance: `X` is a notation token.) -/

open OracleComp OracleSpec ENNReal BinaryTree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.HCollJ8
open NockvmE2E.Exec NockvmE2E.Exec.E2EJ8V NockvmE2E.Exec.V NockvmE2E.Exec.E2E NockvmE2E.Exec.E2EOnlineP NockvmE2E.Exec.VKBind NockvmE2E.Exec.VKBindBridge
  NockvmE2E.Exec.LazyColl NockvmE2E.Merkle NockvmE2E.Merkle.BadBound
open Interaction.Oracle Interaction.Oracle.FiatShamir Interaction.Oracle.Security.StateRestoration ProtocolSpec

/-- **falsifiability witness** for `hsk`: with no side skeletons every input fails to decode and the side hash is the constant zero digest -/
theorem Hof_nil (h : NQuery ([] : List Skeleton) → DgJ8) (x : List ℕ) : Hof [] h x = dgZero := by
  unfold Hof
  have : decQ ([] : List Skeleton) x = none := by
    unfold decQ
    split
    · split
      · rename_i j _ _ _
        simp
      · rfl
    · rfl
  rw [this]

/-- **`hcoll_J8`**: the `hcoll` hypothesis of `exec_e2e_J8V'''`, proved (given `hsk`, `hT`; `hspec` is the setup-correctness named hypothesis) -/
theorem hcoll_J8 {D : Type} {R : D → Type} [DecidableEq D] [instR : SampleableType (∀ d, R d)] {O : Type}
    {skelsF : List Skeleton} [Finite (NQuery skelsF)] {Op : Type} [Finite Op] [DecidableEq Op]
    {Stmt' Salt' : Type} [DecidableEq Stmt'] [DecidableEq Salt'] [Finite Stmt'] [Finite Salt'] {ms : MRounds DgJ8}
    [instRF : SampleableType (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' ms d')]
    (XX : ExecInst) (hgates : setupGates XX = true) (hspec : HSpec XX)
    (hsk : skelsF[0]? = some (VKTrace.skelVK XX))
    (sideOf : (∀ d, R d) → O → Stmt' × Salt' × PublicMessages (compiledRoundsK DgJ8 Op ms))
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn R) +
      OracleSpec.ofFn (succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' ms)) (Option O))
    (πFO : O → FixProof) (Q_Hf V T : ℕ)
    (hHf : ∀ g, IsQueryBoundP (sideAdv sideOf Aon g)
      (@isHashQuery (NQuery skelsF) DgJ8 _ (SoundnessWorld.KC DgJ8 Op Stmt' Salt' ms)) Q_Hf)
    (hT : 2 * ((VKBind.vkSp XX).total - 1) ≤ T) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' ms d');
        let o ← simulateQ (E2EOnlineP.withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => VKBindBridge.VKcollC XX
          (vkSide XX skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op ms) => Key.Challenge k) gF)
          (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op ms) => Key.Challenge k) gF) (πFO o)] ≤
      ((Q_Hf + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card DgJ8 : ℝ≥0∞)) := by
  have hg := hcoll_generic (skelsF := skelsF) (Op := Op) (Stmt := Stmt') (Salt := Salt') (ms := ms) sideOf Aon Q_Hf
    (2 * ((VKBind.vkSp XX).total - 1)) hHf (fun o => VKTrace.vkProg XX skelsF (πFO o))
    (fun o => VKTrace.vkProg_bound XX skelsF (πFO o))
    (fun gF o => VKBindBridge.VKcollC XX
      (vkSide XX skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op ms) => Key.Challenge k) gF)
      (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op ms) => Key.Challenge k) gF) (πFO o))
    (fun gF o hc => by
      have hv : vkSide XX skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op ms) => Key.Challenge k) gF
          = vkSpec XX (Hof skelsF (fun q => gF (.inl q))) :=
        mkVKData'_vk_eq_vkSpec hspec hgates _
      rw [hv] at hc
      exact VKTrace.vkcollC_trace XX hgates hsk (fun q => gF (.inl q)) (πFO o) hc)
  refine le_trans hg ?_
  rw [Nat.card_eq_fintype_card]
  refine ENNReal.div_le_div_right ?_ _
  have h1 : Q_Hf + 2 * ((VKBind.vkSp XX).total - 1) ≤ Q_Hf + V + T := by omega
  have h2 : (((Q_Hf + 2 * ((VKBind.vkSp XX).total - 1)) ^ 2 : ℕ) : ℝ≥0∞) ≤ (((Q_Hf + V + T) ^ 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.pow_le_pow_left h1 2
  simpa using h2

/-- satisfiability of `hsk` and `hT`: the minimal instance `skelsF := [skelVK XX]`, `T := 2 (total - 1)` -/
theorem hsk_hT_sat (XX : ExecInst) :
    ([VKTrace.skelVK XX] : List Skeleton)[0]? = some (VKTrace.skelVK XX) ∧
      2 * ((VKBind.vkSp XX).total - 1) ≤ 2 * ((VKBind.vkSp XX).total - 1) := ⟨rfl, le_rfl⟩

end NockvmE2E.Exec.HCollJ8

#print axioms NockvmE2E.Exec.HCollJ8.hcoll_J8
#print axioms NockvmE2E.Exec.HCollJ8.Hof_nil
#print axioms NockvmE2E.Exec.HCollJ8.hsk_hT_sat
