/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalV1.lean

  J-9 A, L7 balance, card C4v1: `hsumC'` at `BRun9A`.

  Orbit-free, record-generic copies of `ComplJ9BBalV.key9 / bt_bh9 / mbT9 / claimBig_sum` at the J-9 A data `DA`
  (J-9 B's versions fix the orbit `o9 = orbJ8 (D9 …)`; `BRun9A` puts every table at `orbJ8 DA`), the registry pin
  congruence (`pin_sum_gen`, over any layout whose `regs / Rt / idx / rk` are the run's), and the assembly
  `hsumC'_A` (the field verbatim).  `cvT δ DA = cvT δ DD` is `rfl`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalF2
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV1

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom (D9 mbX extraPairs)
open Nock.V1J8.Gen (hdN' tlN')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

noncomputable section

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

/-- The atom-root provider inverse of atom row `j` at `DA`, at any orbit. -/
abbrev HBA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (HonestA8.dNat δ (HonestA8.dMB δ b (ComplJ9ADataRec.acsA_pos Rt hgen) (powN o _) o
    (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ)
    (colAH δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ
      (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ))
    (newBA (DA))) j)⁻¹

/-- A noun's atom-root terminal term at `DA`, at any orbit. -/
abbrev bhA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  ((ComplJ8Data.bigIdOfP p (DD).acs n).map (HBA δ b Rt hgen o χ)).getD 0

variable (hpG : p = Nock.Atoms.p)
include hpG

/-- **The big-atom key identity at `DA`** at any injective orbit. -/
theorem keyA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DA).acs.length))
    (χ : Coins frameJ8 K) (a : ℕ) (ha : a ∈ (DD).bigs) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a) ((ComplJ8Data.rootIdxP p (DD).acs a : ℕ) : ZMod p) =
      HBA δ b Rt hgen o χ (ComplJ8Data.rootIdxP p (DD).acs a) := by
  have hpa : p ≤ a := ((ComplJ8Atom.mem_bigsP p _ _ a).mp ha).2
  have hg := ComplJ9BAtom.root_get Rt hgen hpG a ha
  have hj : ComplJ8Data.rootIdxP p (DD).acs a < (DD).acs.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  exact ComplJ9BAtom.big_keyG δ b hpG (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o hinj χ _ a hpa _ hj
    (Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hg))

/-- **A child's big-atom consumer term is its atom-root provider term** (at `DA`, any injective orbit). -/
theorem bt_bhA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DA).acs.length))
    (χ : Coins frameJ8 K) (n : Noun)
    (hn : ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs) :
    btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) n = bhA δ b Rt hgen o χ n := by
  cases n with
  | cell u v => simp [btT, bhA, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP]
  | atom v =>
    by_cases hv : v < p
    · simp [btT, bhA, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
    · have hb : ComplJ8Cell.isBig (bigOf (DD)) (.atom v) = true := by
        simp [ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
      simp only [btT, hb, if_true, bhA, bigOf, ComplJ8Data.bigIdOfP, hv, if_false, Option.getD_some,
        Option.map_some]
      exact keyA δ b Rt hgen hpG o hinj χ v (hn v rfl (by omega))

/-- **The atom table's `mb` terminal at `DA`** (any injective orbit) is the sum of the cell children's atom-root
terms and the claim's. -/
theorem mbTA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o (DA).acs.length))
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ AtomChipHQ.pubMB)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ (AtomChipHQ.pubMB + 1)) =
      ((DD).cells.map fun y => bhA δ b Rt hgen o χ (hdN' y) + bhA δ b Rt hgen o χ (tlN' y)).sum +
      ([s, f, r].map fun n => bhA δ b Rt hgen o χ n).sum := by
  refine ((ComplJ8OfAtom.atomTerms δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ).2.2.2.1).trans ?_
  obtain ⟨LB, hLB⟩ : ∃ LB, LB = ((DD).cells.flatMap fun n => [hdN' n, tlN' n]).filterMap
      fun n => (ComplJ8Data.bigIdOfP p (DD).acs n).map fun i => (i, 1) := ⟨_, rfl⟩
  have hne : (DD).acs ≠ [] := List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen)
  have hrange : ∀ q ∈ LB ++ extraPairs p (DD).acs [s, f, r], 0 < q.2 → q.1 < (DD).acs.length := by
    intro q hq _
    rcases List.mem_append.mp hq with hq | hq
    · exact ComplJ8Data.mbRecs_range p Rg Rt hgen q (by
        simp only [ComplJ8Data.mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [← hLB]; exact hq) ‹_›
    · obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hq
      cases n with
      | cell u v => simp [ComplJ8Data.bigIdOfP] at hn
      | atom v =>
        by_cases hv : v < p
        · simp [ComplJ8Data.bigIdOfP, hv] at hn
        · simp only [ComplJ8Data.bigIdOfP, hv, if_false, Option.map_some, Option.some.injEq] at hn
          rw [← hn]
          exact ComplJ8Data.rootIdxP_lt p _ hne v
  have hcnt : ∀ j ∈ Finset.range (DA).acs.length,
      liftQ δ (HonestA8.cNat j (newBA (DA) AtomChipHQ.mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b (ComplJ9ADataRec.acsA_pos Rt hgen) (powN o _) o
          (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ)
          (colAH δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ
            (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) o χ))
          (newBA (DA))) j)⁻¹ =
      ((ComplJ8Data.sumAt (LB ++ extraPairs p (DD).acs [s, f, r]) j : ℕ) : 𝕂′) *
        HBA δ b Rt hgen o χ j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : HonestA8.cNat j (newBA (DA) AtomChipHQ.mb) =
        ((ComplJ8Data.sumAt (LB ++ extraPairs p (DD).acs [s, f, r]) j : ℕ) : ZMod p) := by
      rw [HonestA8.cNat, dif_pos hj', newBA_mb]
      show (((mbX (DD) [s, f, r]).getD j 0 : ℕ) : ZMod p) = _
      rw [ComplJ9BAtom.mbX_getD _ _ _ (by rw [ComplJ9BAtom.mb_size p Rg Rt hgen]; exact hj'),
        ComplJ8Data.mb_eq_cnt p Rg Rt hgen j hj', ComplJ8Data.cnt_eq_sumAt, ComplJ8Data.sumAt_append]
      simp only [ComplJ8Data.mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLB]
    rw [e]
    simp only [liftQ, map_natCast]
  refine (Finset.sum_congr rfl hcnt).trans ?_
  rw [show (DA).acs.length = (DD).acs.length from rfl]
  rw [sum_sumAt _ _ (LB ++ extraPairs p (DD).acs [s, f, r]) hrange, List.map_append, List.sum_append]
  unfold extraPairs
  rw [bigPairs_sum (ComplJ8Data.bigIdOfP p (DD).acs) (HBA δ b Rt hgen o χ) [s, f, r]]
  rw [hLB, bigPairs_sum (ComplJ8Data.bigIdOfP p (DD).acs) (HBA δ b Rt hgen o χ), sum_flatMap_two]

/-- **The claim's big-leaf records' inverse sum** is the claim's atom-root terms (at `DA`, any injective orbit). -/
theorem claimBig_sumA {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DA).acs.length)) (χ : Coins frameJ8 K)
    (hbig : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs) :
    ((ClaimJ9.claimBigRecs δ χ (ComplJ8.cJ s f r) (ComplJ8Comp.mCOf (DD).H (ComplJ8.cJ s f r))).map
      fun x => (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ([s, f, r].map fun n => bhA δ b Rt hgen o χ n).sum := by
  have hterm : ∀ x ∈ [s, f, r], (if ClaimJ9.isBigN p x = true then
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ x)
        (((DD).H x).2 : ZMod p) 0 0))⁻¹ else 0) = bhA δ b Rt hgen o χ x := by
    intro x hx
    cases x with
    | cell u v => simp [ClaimJ9.isBigN, bhA, ComplJ8Data.bigIdOfP]
    | atom a =>
      by_cases ha : p ≤ a
      · have hmem := hbig _ hx a rfl ha
        have hH : ((DD).H (.atom a)).2 = ComplJ8Data.rootIdxP p (DD).acs a := by
          show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom a)).2 = _
          simp [ComplJ8Data.hdlP, show ¬ a < p by omega]
        have hk := claimVec_kOf δ (AcceptsJ8.encJ8 δ χ) (.atom a)
          ((ComplJ8Data.rootIdxP p (DD).acs a : ℕ) : ZMod p)
        simp only [Noun.internal, Nat.zero_div, Nat.zero_mod, Nat.cast_zero] at hk
        have hb : bhA δ b Rt hgen o χ (.atom a) = HBA δ b Rt hgen o χ (ComplJ8Data.rootIdxP p (DD).acs a) := by
          simp [bhA, ComplJ8Data.bigIdOfP, show ¬ a < p by omega]
        rw [hb, ← keyA δ b Rt hgen hpG o hinj χ a hmem, if_pos (by simp [ClaimJ9.isBigN, ha]), hH, hk]
      · simp [ClaimJ9.isBigN, ha, bhA, ComplJ8Data.bigIdOfP, show a < p by omega]
  unfold ClaimJ9.claimBigRecs ClaimJ9.claimBigs
  rw [List.map_map, sum_map_ite']
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rw [← hterm s (by simp), ← hterm f (by simp), ← hterm r (by simp)]
  rfl

omit hpG in
/-- **The registry pin records' inverse sum**, over any layout whose registry data are the run's. -/
theorem pin_sum_gen (Pb : AcceptsJ8.PubJ8 p) (hreg : Pb.regs = (DD).regs) (hRtE : Pb.Rt = Rt)
    (hidx : Pb.idx = (DD).idx)
    (hrk : ∀ id, Pb.rk id = AcceptsJ8P.rkC (Nock.Jet.Autogen.compile p (Rt id))) (χ : Coins frameJ8 K) :
    ((AcceptsJ8P.pinRecsJ8 δ Pb χ).map fun x =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ((DD).regs.map fun id => cG δ (γV δ χ) (ρV δ χ) (encR δ χ) (DD).cells ((DD).idx id)).sum := by
  unfold AcceptsJ8P.pinRecsJ8
  rw [List.map_map, hreg]
  refine congrArg List.sum (List.map_congr_left (l := (DD).regs) fun id hid => ?_)
  have hmem : Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).cells := by
    have hm : Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    obtain ⟨a, c, hab⟩ := ComplJ8Data.compile_isCell p (Rt id)
    rw [hab] at hm ⊢
    exact ComplJ8Data.root_mem_cells p Rg Rt hgen hm
  show (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ
      (encR δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)))
      ((Pb.idx id : ℕ) : ZMod p) ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p)))⁻¹ = _
  rw [hRtE, hidx, hrk id]
  rw [show (DD).idx id = Nock.V1J8.Gen.idxOf (DD).cells (Nock.Jet.Autogen.compile p (Rt id)) from rfl,
    genIdxOf_eq _ _ hmem]
  unfold cG
  rw [getD_idxOf _ _ hmem, AcceptsJ8P.rkC, claimVec_kOf]

variable (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "BA" => BRun9A δ b Rt hgen hpG h31A

/-- **`hsumC'` at `BRun9A`** (the field, verbatim). -/
theorem hsumC'_A :
    ∀ χ, (BA).Good χ →
    ((ClaimJ9.claimRecsJ9 δ χ (ComplJ8.cJ s f r) ((BA).M χ).m ++
        AcceptsJ8P.pinRecsJ8 δ (BA).Pb.toPubJ8 χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsC 0) (((BA).M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA AtomChipHQ.pubMB)
          (((BA).M χ).pubsA (AtomChipHQ.pubMB + 1)) := by
  intro χ _
  have hbigC : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (DD).bigs :=
    fun n hn a h hp => ComplJ9BAtom.claim_leaf_big p Rg Rt hgen hn a (by subst h; simp [leavesOf]) hp
  have hmA : (DA).acs.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hinj := (powN_ok (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) (le_two_pow_ht (DA) hmA)).1
  have hm : ((BA).M χ).m = ComplJ8Comp.mCOf (DD).H (ComplJ8.cJ s f r) := rfl
  have hpC : ((BA).M χ).pubsC = pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen)
      (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ := rfl
  have hpA : ((BA).M χ).pubsA = pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen)
      (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ := rfl
  rw [hm, hpC, hpA]
  have hcv : Quad.mk (algebraMap (ZMod p) K δ)
      (pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ 0)
      (pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ 1) =
      cvT δ (DD) χ := by
    have e0 : pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ 0 =
        pub2 δ (cvT δ (DD) χ) 0 := by
      simp [pubsCOf, pubsC0]; rfl
    have e1 : pubsCOf δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ 1 =
        pub2 δ (cvT δ (DD) χ) 1 := by
      simp [pubsCOf, pubsC0]; rfl
    rw [e0, e1]
    exact pub2_mk2 δ _ 0 rfl
  have hbb : ((DD).cells.map fun y =>
      btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (hdN y) +
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (DD)) (tlN y)).sum =
      ((DD).cells.map fun y =>
        bhA δ b Rt hgen (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ (hdN' y) +
          bhA δ b Rt hgen (orbJ8 (DA) (hF_run Rt hgen hpG h31A)) χ (tlN' y)).sum := by
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [bt_bhA δ b Rt hgen hpG _ hinj χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inl rfl) a ha hp,
      bt_bhA δ b Rt hgen hpG _ hinj χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inr rfl) a ha hp,
      hdN_eq, tlN_eq]
  have hpin := pin_sum_gen δ Rt hgen (BA).Pb.toPubJ8 rfl rfl rfl (fun _ => rfl) χ
  unfold ClaimJ9.claimRecsJ9
  rw [List.append_assoc, List.map_append, List.sum_append, List.map_append, List.sum_append,
    claim_sum δ Rt hgen χ, claimBig_sumA δ b Rt hgen hpG _ hinj χ hbigC, hpin, hcv,
    cvT_run δ Rt hgen χ, mbTA δ b Rt hgen hpG _ hinj χ, hbb]
  ring

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV1

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV1
#print axioms keyA
#print axioms bt_bhA
#print axioms mbTA
#print axioms claimBig_sumA
#print axioms pin_sum_gen
#print axioms hsumC'_A
end Axioms
