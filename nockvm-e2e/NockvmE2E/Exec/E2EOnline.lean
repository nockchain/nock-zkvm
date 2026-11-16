/-
the ONLINE end-to-end theorem.
  * `exec_e2e_online`: GENERIC in the instance. If the FLAT experiment (the oracle `g`, the side proof dropped into the adversary's free
    witness) has `Pr[verifyFlat ∧ Bad] ≤ ε` (hypothesis `hflat`), then in the ONLINE experiment (oracle pair `(g, gF)`, `gF` independent of `g`)
    `Pr[verifyOnline ∧ Bad] ≤ ε + Pr[FixFail]`.  Split lemma (Exec/SoundOnline.lean) + union bound + the re-packing equality.
  * `exec_e2e_J8V`: the J-8 instance, `hflat := exec_e2e_J8F` on the re-packed adversary, `Bad := ¬ HoldsN`; `≤ 2^-82 + εfix` under `hFix`.
  * `hFix` is NOT discharged here.  Non-vacuity: `Pr[FixFail] = 0` in the model where the side proof's evaluations are the true ones.
-/
import NockvmE2E.Exec.SoundOnline
import NockvmE2E.Exec.E2EJ8F

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EOnline
open NockvmE2E.Exec NockvmE2E.Exec.V

theorem pr_triple {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {A B C : Type}
    (mx : m A) (f : A → m B) (h : A → B → m C) (P : A → B → C → Prop) :
    Pr{let a ← mx; let b ← f a; let c ← h a b}[P a b c] =
      Pr{let x ← (do let a ← mx; let b ← f a; let c ← h a b; pure (a, b, c))}[P x.1 x.2.1 x.2.2] := by
  first | rfl | simp [prEvent_eq_evalDist_map]

theorem pr_pair {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {A B : Type}
    (mx : m A) (f : A → m B) (P : A → B → Prop) :
    Pr{let a ← mx; let b ← f a}[P a b] = Pr{let x ← (do let a ← mx; let b ← f a; pure (a, b))}[P x.1 x.2] := by
  simp

theorem pr_pair_congr {A B : Type}
    (mx : ProbComp A) (f : A → ProbComp B) (p q : A → B → Prop) (h : ∀ a b, p a b ↔ q a b) :
    Pr{let a ← mx; let b ← f a}[p a b] = Pr{let a ← mx; let b ← f a}[q a b] := by
  rw [pr_pair, pr_pair]; exact prEvent_congr_of_support _ _ _ (fun x _ => h _ _)

theorem pr_triple_congr {A B C : Type}
    (mx : ProbComp A) (f : A → ProbComp B) (h : A → B → ProbComp C) (p q : A → B → C → Prop) (hpq : ∀ a b c, p a b c ↔ q a b c) :
    Pr{let a ← mx; let b ← f a; let c ← h a b}[p a b c] = Pr{let a ← mx; let b ← f a; let c ← h a b}[q a b c] := by
  rw [pr_triple, pr_triple]; exact prEvent_congr_of_support _ _ _ (fun x _ => hpq _ _ _)

section Generic
variable {D : Type} {R : D → Type} [DecidableEq D] [SampleableType (∀ d, R d)] {GF O O' : Type} [SampleableType GF]

/-- re-pack the online adversary (output `O`, carrying `πF`) into a flat one (output `O'`, `πF` in the free witness) over the same
oracle `g`: it samples `gF` itself, then runs the online adversary and re-labels its output by `rp` -/
noncomputable def repack (rp : O → O')
    (A : GF → OracleComp (unifSpec + OracleSpec.ofFn R) (Option O)) :
    OracleComp (unifSpec + OracleSpec.ofFn R) (Option O') := do
  let gF ← (liftM ($ᵗ GF : ProbComp GF) : OracleComp (unifSpec + OracleSpec.ofFn R) GF)
  let o ← A gF
  pure (o.map rp)

theorem sim_repack (rp : O → O') (g : ∀ d, R d)
    (A : GF → OracleComp (unifSpec + OracleSpec.ofFn R) (Option O)) :
    simulateQ (E2E.withTable g) (repack rp A) =
      (do let gF ← ($ᵗ GF : ProbComp GF)
          let o ← simulateQ (E2E.withTable g) (A gF)
          pure (o.map rp)) := by
  unfold repack
  simp only [simulateQ_bind, simulateQ_pure]
  rw [E2E.withTable]
  simp only [QueryImpl.passthrough_add]
  rw [QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, simulateQ_id']
  rfl

variable (X0 : ExecInst) (HOf : (∀ d, R d) → HFn) (FSOf : (∀ d, R d) → FSFn) (FSfOf : GF → FSFn)
  (vkOf : (∀ d, R d) → VK) (rp : O → O')
  (zO : O → List Nat) (πO : O → FlatProof) (πFO : O → FixProof) (BadO : O → Prop)
  (zO' : O' → List Nat) (πO' : O' → FlatProof) (BadO' : O' → Prop)

/-- **`exec_e2e_online`** (generic in the instance `X0`, the oracle type, the adversary's output type).
`hvk`: the VK is the honest `setup` of the instance, a function of the oracle `g`.
`hz hπ hBad`: `rp` (the re-packing) keeps the statement, the main proof and the event.
`hflat`: the FLAT experiment against the re-packed adversary (it samples `gF` itself, `πF` rides in its free witness) has
`Pr[verifyFlat ∧ Bad] ≤ ε`.  `hFix`: `Pr[FixFail] ≤ εfix` in the online experiment (named;  discharges it for FRI+Merkle). -/
theorem exec_e2e_online (hvk : ∀ g, setup X0 (HOf g) = some (vkOf g))
    (hz : ∀ o, zO' (rp o) = zO o) (hπ : ∀ o, πO' (rp o) = πO o) (hBad : ∀ o, BadO' (rp o) ↔ BadO o)
    (A : GF → OracleComp (unifSpec + OracleSpec.ofFn R) (Option O))
    (ε εfix : ℝ≥0∞)
    (hflat : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repack rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] ≤ ε)
    (hFix : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF)}[
      match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF)}[
      match o with
      | none => False
      | some o => verifyOnline (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] ≤ ε + εfix := by
  let M : ProbComp ((∀ d, R d) × GF × Option O) :=
    do let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF); pure (g, gF, o)
  let Pon : ((∀ d, R d) × GF × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyOnline (vkOf x.1) (HOf x.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o) = true ∧ BadO o
  let Pfl : ((∀ d, R d) × GF × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => verifyFlat X0 (HOf x.1) (FSOf x.1) (zO o) (πO o) = true ∧ BadO o
  let Pfx : ((∀ d, R d) × GF × Option O) → Prop := fun x =>
    match x.2.2 with
    | none => False
    | some o => FixFail X0 (vkOf x.1) (HOf x.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o)
  have e0 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF)}[
      match o with
      | none => False
      | some o => verifyOnline (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o] =
      Pr{let x ← M}[Pon x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : GF) (o : Option O) => match o with
      | none => False
      | some o => verifyOnline (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) = true ∧ BadO o)
  have e1 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF)}[
      match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] =
      Pr{let x ← M}[Pfx x] :=
    pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : GF) (o : Option O) => match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))
  have e2 : Pr{let g ← $ᵗ (∀ d, R d); let o ← simulateQ (E2E.withTable g) (repack rp A)}[
      match o with
      | none => False
      | some o' => verifyFlat X0 (HOf g) (FSOf g) (zO' o') (πO' o') = true ∧ BadO' o'] = Pr{let x ← M}[Pfl x] := by
    simp only [sim_repack, M, Pfl, prEvent_eq_evalDist_map]
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
      rcases verifyOnline_split X0 (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) (vkOf g) (hvk g) h1 with h3 | h3
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr h3
  rw [e0]
  rw [e2] at hflat
  rw [e1] at hFix
  exact hmono.trans ((prEvent_or_le M Pfl Pfx).trans (add_le_add hflat hFix))

/-- **`hFix` is satisfiable: the meaningful lemma.** For ANY adversary `A` whose side proof `πF` (on every reachable output) does not
witness a false value (in particular, whose `πF` carries the TRUE evaluations), `FixFail` never holds, so `hFix` holds with `εfix = 0`.
This is a lemma about an arbitrary adversary hypothesis `hon`; it does NOT say that the actual honest side prover `proveFix` meets `hon`
(that needs the setup-correctness / completeness of `proveFix`). -/
theorem hFix_of_honest (A : GF → OracleComp (unifSpec + OracleSpec.ofFn R) (Option O))
    (hon : ∀ g gF o, some o ∈ support (simulateQ (E2E.withTable g) (A gF)) →
      ¬ FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) (A gF)}[
      match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ 0 := by
  rw [pr_triple _ _ _ (fun (g : ∀ d, R d) (gF : GF) (o : Option O) => match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))]
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)
  rintro ⟨g, gF, o⟩ hx
  rcases o with _ | o
  · exact id
  · simp at hx
    exact hon g gF o hx

/-- TRIVIAL instance of `hFix_of_honest`, to meet the vacuity rule: the instance is the NEVER-ANSWERING adversary (`pure none`).
It shows only that `hFix` is satisfiable (so `exec_e2e_online` is not stated over an uninhabitable hypothesis). It does NOT show that an
honest side prover meets `hFix`; the honest `proveFix` instance is not covered here. -/
theorem hFix_toy :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ GF; let o ← simulateQ (E2E.withTable g) ((fun _ => (pure none : OracleComp (unifSpec + OracleSpec.ofFn R) (Option O))) gF)}[
      match o with
      | none => False
      | some o => FixFail X0 (vkOf g) (HOf g) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤ 0 :=
  hFix_of_honest X0 HOf FSOf FSfOf vkOf zO πO πFO _ (fun g gF o ho => by simp at ho)
end Generic
end NockvmE2E.Exec.E2EOnline

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

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
set_option maxHeartbeats 4000000 in
/-- **`exec_e2e_J8V`**: the J-8 instance of `exec_e2e_online`, `hflat := exec_e2e_J8F` on the re-packed adversary `repack rp Aon`,
`Bad := ¬ HoldsN`.  Same binders as `exec_e2e_J8F` plus: `hsetup` ([executed] the honest `setup` of the instance succeeds for every hash;
`vk` is a function of `g`), the online adversary `Aon` (it receives the side oracle table `gF`; its output carries `πF`),
`FSfOf` (the side proof's Fiat-Shamir view of `gF`), and `hFix : Pr[FixFail] ≤ εfix` ([NAMED HYPOTHESIS],  discharges it). The query budgets
`hFS hHq` are stated for the re-packed adversary.

**Caveat:** condition `hFix` is currently unsatisfiable by general adversaries (side Merkle hash constant; adversary holds the side oracle as a
value); not e2e soundness. See `exec_e2e_J8V'`, E2EOnlineP.lean. -/
theorem exec_e2e_J8V {Statement Salt W GF : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    [SampleableType GF]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    (hmask : maskOk (XI170 XI0) = true) (hnumeralOk : NockvmE2E.Exec.MaskOk.numeralOk (XI170 XI0) = true)
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.Exec.MaskBridge.LagrAt IX (XI170 XI0).pubOf.size tp hcapV t c)
    (FSfOf : GF → FSFn) (hsetup : ∀ H, ∃ vk, setup (XI170 XI0) H = some vk)
    (Aon : GF → OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC))
      (Option (Statement × Salt × FlatProof × FixProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF
        (E2EOnline.repack (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF
        (E2EOnline.repack (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn)
    (εfix : ℝ≥0∞)
    (hFix : Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ GF; let o ← simulateQ (withTable g) (Aon gF)}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        FixFail (XI170 XI0) (Classical.choose (hsetup (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)))
          (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)
          (FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf gF) (encZ (z, salt)) π πF] ≤ εfix) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd); let gF ← $ᵗ GF; let o ← simulateQ (withTable g) (Aon gF)}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        verifyOnline (Classical.choose (hsetup (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)))
          (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)
          (FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
            (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
          (FSfOf gF) (encZ (z, salt)) π πF = true ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ + εfix := by
  have hJ := NockvmE2E.Exec.E2EJ8F.F.exec_e2e_J8F XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0 I0 I Ifin m0 mf hl encZ decZ hz hS hlink hids
    hmask hnumeralOk hjet
    (E2EOnline.repack (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon)
    Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  refine le_trans (le_of_eq (E2EOnline.pr_triple_congr _ _ _ _ _ ?conv)) (E2EOnline.exec_e2e_online (XI170 XI0)
    (fun g => HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)
    (fun g => FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV decZ
      (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g)
    FSfOf
    (fun g => Classical.choose (hsetup (HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV g)))
    (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2)))
    (fun o => encZ (o.1, o.2.1)) (fun o => o.2.2.1) (fun o => o.2.2.2.1) (fun _ => ¬ Nock.Jet.HoldsN D.d.c)
    (fun o => encZ (o.1, o.2.1)) (fun o => o.2.2.1) (fun _ => ¬ Nock.Jet.HoldsN D.d.c)
    (fun g => Classical.choose_spec (hsetup _)) (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) Aon _ εfix
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

#print axioms NockvmE2E.Exec.E2EOnline.exec_e2e_online
#print axioms NockvmE2E.Exec.E2EOnline.hFix_of_honest
#print axioms NockvmE2E.Exec.E2EOnline.hFix_toy
#print axioms NockvmE2E.Exec.E2EJ8V.exec_e2e_J8V
