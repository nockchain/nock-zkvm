/-
the ONLINE end-to-end theorem with the side proof's Merkle hash and Fiat-Shamir oracle as an ORACLE
(section 1.1; supersedes `E2EOnline.exec_e2e_online` / `exec_e2e_J8V`, which are kept unchanged).

Why: in `exec_e2e_J8V` the side proof hashes with `hFix (HT g)`, which is the constant `dgZero` off the main tree indices, and the
adversary receives the side oracle table `gF` as a VALUE with `FSfOf` a free parameter, so `hFix` is unsatisfiable by general adversaries.
Here:
  * the side verifier is the primed executable `verifyOnline'` (VKp.lean) with its own hash `Hf` and Fiat-Shamir function `FSf`;
  * the side oracle `gF` is a total table `∀ d, RF d` accessed ONLY through oracle queries: the adversary lives in `OracleComp (mainSpec + sideSpec)`;
    `repackP` simulates `sideSpec` by a self-sampled table, so the main query budgets keep their meaning;
  * `HfOf` and `FSfOf` are FIXED functions of the side table (they are not adversary data): J-8 instance `exec_e2e_J8V'`.

MODELLING ASSUMPTION (label: model, not proved): the Tip5 hash on the side tags (tag-shifted in the executable, `hFix`) is an independent
random oracle from the main one, of the same standing as `Hof` for the main proof.  It is consistent with the executable because the side
tags (>= 64 under `hFix`) are disjoint from the main tags (< 4+k, k <= 25 since nD <= 32).
-/
import NockvmE2E.Exec.SoundOnlineP
import NockvmE2E.Exec.E2EOnline

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EOnlineP
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.E2EOnline

section Generic
variable {D : Type} {R : D → Type} [DecidableEq D] [SampleableType (∀ d, R d)]
  {DF : Type} {RF : DF → Type} [DecidableEq DF] [SampleableType (∀ d, RF d)] {O O' : Type}

/-- both oracles answered from total tables: the main oracle by `g`, the side oracle by `gF` -/
noncomputable def withTable2 (g : ∀ d, R d) (gF : ∀ d, RF d) :
    QueryImpl ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) ProbComp :=
  E2E.withTable g + (QueryImpl.ofFn gF).liftTarget ProbComp

/-- the side oracle answered from the table `gF` inside the main oracle computation (main queries pass through) -/
noncomputable def sideImpl (gF : ∀ d, RF d) :
    QueryImpl ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (OracleComp (unifSpec + OracleSpec.ofFn R)) :=
  QueryImpl.id' (unifSpec + OracleSpec.ofFn R) + (QueryImpl.ofFn gF).liftTarget (OracleComp (unifSpec + OracleSpec.ofFn R))

/-- re-pack an adversary with oracle access to `mainSpec + sideSpec` (output `O`, carrying `πF`) into a flat one over `mainSpec` only:
it samples the side table itself, simulates `sideSpec` from it, and relabels the output by `rp` -/
noncomputable def repackP (rp : O → O')
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O)) :
    OracleComp (unifSpec + OracleSpec.ofFn R) (Option O') :=
  E2EOnline.repack (GF := ∀ d, RF d) rp (fun gF => simulateQ (sideImpl gF) A)

theorem sim_side (g : ∀ d, R d) (gF : ∀ d, RF d)
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O)) :
    simulateQ (E2E.withTable g) (simulateQ (sideImpl gF) A) = simulateQ (withTable2 g gF) A := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) A
  rcases t with t | t
  · simp [sideImpl, withTable2]
  · simp only [sideImpl, withTable2, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.ofFn_apply]
    change simulateQ _ (liftM (pure (gF t) : Id _)) = liftM (pure (gF t) : Id _)
    simp [liftM_pure]

theorem sim_repackP (rp : O → O') (g : ∀ d, R d)
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O)) :
    simulateQ (E2E.withTable g) (repackP rp A) =
      (do let gF ← ($ᵗ (∀ d, RF d) : ProbComp _)
          let o ← simulateQ (withTable2 g gF) A
          pure (o.map rp)) := by
  unfold repackP
  rw [E2EOnline.sim_repack]
  simp only [sim_side]

variable (X0 : ExecInst) (HOf : (∀ d, R d) → HFn) (FSOf : (∀ d, R d) → FSFn)
  (HfOf : (∀ d, RF d) → HFn) (FSfOf : (∀ d, RF d) → FSFn) (vkOf : (∀ d, RF d) → VK) (rp : O → O')
  (zO : O → List Nat) (πO : O → FlatProof) (πFO : O → FixProof) (BadO : O → Prop)
  (zO' : O' → List Nat) (πO' : O' → FlatProof) (BadO' : O' → Prop)

/-- **`exec_e2e_onlineP`** (generic in the instance `X0`, both oracle types, the adversary's output type).
`hvk`: the VK is the honest `setup'` of the instance under the side hash, a function of the SIDE table only.
`hz hπ hBad`: `rp` keeps the statement, the main proof and the event.
`hflat`: the FLAT experiment against the re-packed adversary (it samples the side table itself, `πF` rides in its free witness) has
`Pr[verifyFlat ∧ Bad] ≤ ε`.
`hFix`: `Pr[FixFail'] ≤ εfix` in the ONLINE experiment (`g`, `gF` independent tables, the adversary has oracle access to both) -- the
NAMED hypothesis that ..6 discharge. -/
theorem exec_e2e_onlineP (hvk : ∀ gF, setup' X0 (HfOf gF) = some (vkOf gF))
    (hz : ∀ o, zO' (rp o) = zO o) (hπ : ∀ o, πO' (rp o) = πO o) (hBad : ∀ o, BadO' (rp o) ↔ BadO o)
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O))
    (ε εfix : ℝ≥0∞)
    (hflat : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repackP rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] ≤ ε)
    (hFix : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] ≤ ε + εfix := by
  let M : ProbComp ((∀ d, R d) × (∀ d, RF d) × Option O) :=
    do let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A; pure (g, gF, o)
  let Pon : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyOnline' (vkOf x.2.1) (HOf x.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o) = true ∧ BadO o
  let Pfl : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyFlat X0 (HOf x.1) (FSOf x.1) (zO o) (πO o) = true ∧ BadO o
  let Pfx : ((∀ d, R d) × (∀ d, RF d) × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => FixFail' X0 (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o)
  have e0 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] =
      Pr{let x ← M}[Pon x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : ∀ d, RF d) (o : Option O) => match o with
      | none => False
      | some o => verifyOnline' (vkOf gF) (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o)
  have e1 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] =
      Pr{let x ← M}[Pfx x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : ∀ d, RF d) (o : Option O) => match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))
  have e2 : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repackP rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] = Pr{let x ← M}[Pfl x] := by
    simp only [sim_repackP, M, Pfl, prEvent_eq_evalDist_map]
    simp
    congr! 3
    congr 1
    funext a
    congr 1
    funext o
    rcases o with _ | o
    · rfl
    · show (verifyFlat X0 (HOf _) (FSOf _) (zO' (rp o)) (πO' (rp o)) = true ∧ BadO' (rp o)) = _
      rw [hz, hπ, propext (hBad o)]
  have hmono : Pr{let x ← M}[Pon x] ≤ Pr{let x ← M}[Pfl x ∨ Pfx x] := by
    refine prEvent_mono_of_support M Pon _ ?_
    rintro ⟨g, gF, o⟩ _ h
    rcases o with _ | o
    · exact absurd h id
    · obtain ⟨h1, h2⟩ := h
      rcases verifyOnline_split' X0 (HOf g) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) (vkOf gF) (hvk gF) h1 with h3 | h3
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr h3
  rw [e0]
  rw [e2] at hflat
  rw [e1] at hFix
  exact hmono.trans ((prEvent_or_le M Pfl Pfx).trans (add_le_add hflat hFix))

/-- `hFix` is satisfiable, the meaningful form: for ANY adversary whose side proofs never pass `verifyFix'` while claiming a false value
(e.g. whose `πF` carries the true evaluations), `Pr[FixFail'] = 0`.  A statement about the adversary hypothesis `hon`; it does NOT say that the
honest side prover meets `hon` (that is setup-correctness / completeness, /7-5). -/
theorem hFix_of_honestP
    (A : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O))
    (hon : ∀ g gF o, some o ∈ support (simulateQ (withTable2 g gF) A) →
      ¬ FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d); let o ← simulateQ (withTable2 g gF) A}[
      match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ 0 := by
  rw [pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : ∀ d, RF d) (o : Option O) => match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))]
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)
  rintro ⟨g, gF, o⟩ hx
  rcases o with _ | o
  · exact id
  · simp at hx
    exact hon g gF o hx

/-- the default (empty) side proof is rejected by `verifyFix'` whenever the VK has a fixed column (shape check) -/
theorem verifyFix'_default_ne (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (hc : vk.cols.size ≠ 0) :
    verifyFix' vk Hf FSf z ctx zeta default ≠ .ok () := by
  unfold verifyFix'
  have : ((default : FixProof).vF.size == vk.cols.size && (List.range vk.cols.size).all (fun j => (default : FixProof).vF[j]!.size == fixLen vk.X vk.cols[j]!) &&
       (default : FixProof).pfinal.size == vk.X.d && (default : FixProof).pos.size == vk.X.l && (default : FixProof).roots.size == vk.X.k &&
       (default : FixProof).vals.size == 1 + vk.X.k && (default : FixProof).sibs.size == 1 + vk.X.k) = false := by
    have h0 : ((default : FixProof).vF.size == vk.cols.size) = false := by
      have h00 : (default : FixProof).vF.size = 0 := rfl
      simp [h00, Ne.symm hc]
    simp [h0]
  simp only [ckE, this]
  simp [Bind.bind, Except.bind]

/-- Vacuity witness for `hFix` (NOT the never-answering adversary: this one ANSWERS `some o0` on every run).  Its side proof is the default
`FixProof`, which fails `verifyFix'`'s shape check whenever the VK has a fixed column (`hcols`, always true for `setup'`: `fixCols` contains
`zh`), so `FixFail'` is false and `hFix` holds with `εfix = 0`.  Honest label: this exercises the answering branch of `hFix` but is NOT an
honest prover; the honest `proveFix'` instance needs setup correctness. -/
theorem hFix_toy_answering (o0 : O) (hπF : πFO o0 = default) (hcols : ∀ gF, (vkOf gF).cols.size ≠ 0) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d, RF d);
       let o ← simulateQ (withTable2 g gF) ((pure (some o0)) :
         OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn RF) (Option O))}[
      match o with
      | none => False
      | some o => FixFail' X0 (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ 0 := by
  refine hFix_of_honestP X0 FSOf HfOf FSfOf vkOf zO πO πFO _ (fun g gF o ho hF => ?_)
  simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ho
  subst ho
  have h1 := hF.1
  rw [hπF] at h1
  exact verifyFix'_default_ne _ _ _ _ _ _ (hcols gF) h1

end Generic
end NockvmE2E.Exec.E2EOnlineP

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EJ8V
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.J8 NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.InstJ8 (Φ0)

/-! ## 1. hop 0 from the exe's chip check: `HopsOK`, `NumOK`, the constraint-count cap -/

open NockvmE2E.Exec.E2EJ8F
open NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM
open NockvmE2E.Exec.E2EJ8 NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)
open NockvmE2E.Exec.MaskOk (maskOk)

variable (XI0 : ExecInst) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true) (hshX : J8Shape.j8ShapeXOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeX IX (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin (IX).Jm.T)

set_option hygiene false in
local notation "JXn" => (IX).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "prV" => prX IX (XI170 XI0).pubOf.size tp hcapV

/- the executed chip check and the datum numerals (labels in the ledger at the end) -/
variable (hchips : chipsOk (XI170 XI0) = true)
  (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size,
    (chipNumeral (XI170 XI0).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 XI0) t))

set_option hygiene false in
local notation "hd1" => ((J8Shape.d_of_shape hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_X IX (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_X IX (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hopsV" => (hops_of_chips IX hchips litTies hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops_of_chips IX hchips litTies hnum0).2.1
set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX jDers jMeta hnumV hopsV)
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn prV ωS (31 / 64) (friBound s1 1)
set_option hygiene false in
local notation "RestP" => RestJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "RestVP" => RestVJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "cIV" => cIX IX (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "mV" => (XI170 XI0).nc * (JXn).r + (PJ).nq - 1

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (NockvmE2E.Exec.E2EJ8F.F.hmV_X XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0)

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeX hshX).trans rfl : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeX IX (XI170 XI0).pubOf.size tp hcapV rfl hshX
set_option hygiene false in
local notation "HBLKQ" => hblkq_X IX (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (J8Shape.hn1_of_shape hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (J8Shape.hn32_of_shape hsh)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 1 (XI170 XI0).l DgJ8 encK MDV LV (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC (MDV).toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 1 (XI170 XI0).l DgJ8 encK LV
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cIV sl0X sl1X
  (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).1
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

/-! ## side oracle: `sideSpec := (NQuery skelsF →ₒ DgJ8) + FS keys`, with FIXED views `HfOf`, `FSfOf` -/

/-- answers of the side oracle: digests on node queries of the side trees, challenges on the side Fiat-Shamir keys `FK` -/
abbrev SideRng (skelsF : List Skeleton) {FK : Type} (FR : FK → Type) : NQuery skelsF ⊕ FK → Type :=
  Sum.elim (fun _ => DgJ8) FR

/-- the side Merkle hash: the flat view of the table's node answers (`Hof`: zero digest off the image, as for the main oracle) -/
def HfOf (skelsF : List Skeleton) {FK : Type} (FR : FK → Type) (gF : ∀ d, SideRng skelsF FR d) : HFn :=
  Hof skelsF (fun q => gF (.inl q))

/-- the side Fiat-Shamir function: the flat transcript prefix is decoded to the key `fkOf x` (the side compiled protocol's decoder, fixed),
the table's challenge there is read out as `nl` limbs by `frOf` (fixed) -/
def FSfOf (skelsF : List Skeleton) {FK : Type} (FR : FK → Type) (fkOf : List (List ℕ) → FK)
    (frOf : ∀ k, FR k → ℕ → List ℕ) (gF : ∀ d, SideRng skelsF FR d) : FSFn :=
  fun x nl => frOf (fkOf x) (gF (.inr (fkOf x))) nl

/-- the honest VK as an explicit function of the side table (no `Classical.choose`) -/
def vkSide (XX : ExecInst) (skelsF : List Skeleton) {FK : Type} (FR : FK → Type) (gF : ∀ d, SideRng skelsF FR d) : VK :=
  (mkVKData' XX (HfOf skelsF FR gF)).vk

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
set_option maxHeartbeats 4000000 in
/-- **`exec_e2e_J8V'`**: the J-8 instance of `exec_e2e_onlineP`; `hflat := exec_e2e_J8F` on the re-packed adversary `repackP rp Aon`,
`Bad := ¬ HoldsN`.  Compared to `exec_e2e_J8V`: the side oracle is ORACLE ACCESS (`Aon` lives in `SuccinctSpecK + ofFn (SideRng ..)`, the query
budgets `hFS hHq` are for the re-packed adversary that simulates the side oracle from a self-sampled table); `HfOf`/`FSfOf` are the FIXED
views of the side table (`HfOf skelsF FR` = `Hof skelsF` on the node half, `FSfOf` via the fixed decoder `fkOf`/readout `frOf`; the side
compiled protocol that instantiates `FK FR fkOf frOf skelsF` is /3); `hsetup` is replaced by the executed instance check
`hgates : setupGates (XI170 XI0) = true` and the VK is the explicit `vkSide` (honest `setup'` under the side hash).
The side trees' tags are those of `verifyFix'`: 0 (VK tree) and 4+w (FRI tree w), so `skelsF` has length >= 4+k with trees 1..3 unused.
`hFix : Pr[FixFail'] ≤ εfix` is the remaining NAMED HYPOTHESIS (..6 discharge it). -/
theorem exec_e2e_J8V' {Statement Salt W : Type} {skelsF : List Skeleton} {FK : Type} {FR : FK → Type} [DecidableEq FK]
    (fkOf : List (List ℕ) → FK) (frOf : ∀ k, FR k → ℕ → List ℕ) [SampleableType (∀ d, SideRng skelsF FR d)] [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    (hmask : maskOk (XI170 XI0) = true) (hnumeralOk : NockvmE2E.Exec.MaskOk.numeralOk (XI170 XI0) = true)
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.Exec.MaskBridge.LagrAt IX (XI170 XI0).pubOf.size tp hcapV t c)
    (hgates : setupGates (XI170 XI0) = true)
    (Aon : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) + OracleSpec.ofFn (SideRng skelsF FR))
      (Option (Statement × Salt × FlatProof × FixProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF
        (E2EOnlineP.repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF
        (E2EOnlineP.repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn)
    (εfix : ℝ≥0∞)
    (hFix : Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ (∀ d, SideRng skelsF FR d); let o ← simulateQ (E2EOnlineP.withTable2 g gF) Aon}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        FixFail' (XI170 XI0) (vkSide (XI170 XI0) skelsF FR gF) (HfOf skelsF FR gF)
          (FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf skelsF FR fkOf frOf gF) (encZ (z, salt)) π πF] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ (∀ d, SideRng skelsF FR d); let o ← simulateQ (E2EOnlineP.withTable2 g gF) Aon}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        verifyOnline' (vkSide (XI170 XI0) skelsF FR gF)
          (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g) (HfOf skelsF FR gF)
          (FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf skelsF FR fkOf frOf gF) (encZ (z, salt)) π πF = true ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ + εfix := by
  have hJ := NockvmE2E.Exec.E2EJ8F.F.exec_e2e_J8F XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0 I0 I Ifin m0 mf hl encZ decZ hz hS hlink hids
    hmask hnumeralOk hjet
    (E2EOnlineP.repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon)
    Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  refine le_trans (le_of_eq (E2EOnline.pr_triple_congr _ _ _ _ _ ?conv)) (E2EOnlineP.exec_e2e_onlineP (XI170 XI0)
    (fun g => HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)
    (fun g => FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
      (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
    (HfOf skelsF FR) (FSfOf skelsF FR fkOf frOf) (vkSide (XI170 XI0) skelsF FR)
    (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2)))
    (fun o => encZ (o.1, o.2.1)) (fun o => o.2.2.1) (fun o => o.2.2.2.1) (fun _ => ¬ Nock.Jet.HoldsN D.d.c)
    (fun o => encZ (o.1, o.2.1)) (fun o => o.2.2.1) (fun _ => ¬ Nock.Jet.HoldsN D.d.c)
    (fun gF => setup'_of_gates hgates _) (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) Aon _ εfix
    ?_ ?_)
  rotate_left
  · refine le_trans (le_of_eq (E2EOnline.pr_pair_congr _ _ _ _ ?_)) hJ
    intro g o
    rcases o with _ | ⟨z, salt, π, w⟩ <;> exact Iff.rfl
  · refine le_trans (le_of_eq (E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hFix
    intro g gF o
    rcases o with _ | ⟨z, salt, π, πF, w⟩ <;> exact Iff.rfl
  · intro g gF o
    rcases o with _ | ⟨z, salt, π, πF, w⟩ <;> exact Iff.rfl


#print axioms NockvmE2E.Exec.E2EOnlineP.verifyFix'_default_ne
#print axioms NockvmE2E.Exec.E2EOnlineP.sim_repackP
#print axioms NockvmE2E.Exec.E2EOnlineP.exec_e2e_onlineP
#print axioms NockvmE2E.Exec.E2EOnlineP.hFix_of_honestP
#print axioms NockvmE2E.Exec.E2EOnlineP.hFix_toy_answering
#print axioms NockvmE2E.Exec.E2EJ8V.exec_e2e_J8V'
