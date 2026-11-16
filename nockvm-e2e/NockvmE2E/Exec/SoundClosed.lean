/-
  NockvmE2E/Exec/SoundClosed.lean   (proof-only)

  * `blockLayout_rank_lt` / `blockLayout_rank_inj`: the verifier's block layout has `rank c < W (blockOf c)` and distinct ranks inside a block
    (discharges the `rank < W` hypothesis of `leafPos_mem_treeSel`);
  * `verifyFlat_sound'`: `verifyFlat_sound` with the internal bookkeeping discharged (`hnD hk hl hs1 hq0 hqlen hcg`).
-/
import NockvmE2E.Exec.SoundFlat
import NockvmE2E.Exec.SoundPub

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL


theorem set!_get1 (a : Array Nat) (i j v : Nat) (h : i < a.size) : (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
    simp [Array.set!]
    split_ifs <;> simp_all
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]
    have : i ≠ j := by omega
    simp [this]

theorem modify_get1 (a : Array Nat) (i j : Nat) (h : i < a.size) : (a.modify i (· + 1))[j]! = if i = j then a[j]! + 1 else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
    simp [Array.getElem_modify]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]
    have : i ≠ j := by omega
    simp [this]

/-- a column that occupies a slot of a committed block -/
def LayoutValid (XI : ExecInst) (c : ℕ) : Prop := XI.blockOf[c]! < 4

def layoutStep (XI : ExecInst) (st : Array ℕ × Array ℕ) (c : ℕ) : Array ℕ × Array ℕ :=
  let b := XI.blockOf[c]!
  if b < 4 then (st.1.modify b (· + 1), st.2.set! c st.1[b]!) else st

theorem blockLayout_eq (XI : ExecInst) : blockLayout XI =
    (List.range (XI.nc + XI.nq)).foldl (layoutStep XI) (Array.replicate 4 0, Array.replicate (XI.nc + XI.nq) 0) := rfl

/-- the invariant of the layout fold after the columns `< m` -/
structure LInv (XI : ExecInst) (m : ℕ) (st : Array ℕ × Array ℕ) : Prop where
  s1 : st.1.size = 4
  s2 : st.2.size = XI.nc + XI.nq
  lt : ∀ c, c < m → LayoutValid XI c → st.2[c]! < st.1[XI.blockOf[c]!]!
  inj : ∀ c c', c < m → c' < m → LayoutValid XI c → LayoutValid XI c' → XI.blockOf[c]! = XI.blockOf[c']! → c ≠ c' →
    st.2[c]! ≠ st.2[c']!

theorem LInv_init (XI : ExecInst) : LInv XI 0 (Array.replicate 4 0, Array.replicate (XI.nc + XI.nq) 0) :=
  ⟨by simp, by simp, fun c hc => by omega, fun c c' hc => by omega⟩

theorem LInv_step (XI : ExecInst) (m : ℕ) (hm : m < XI.nc + XI.nq) (st : Array ℕ × Array ℕ) (h : LInv XI m st) :
    LInv XI (m + 1) (layoutStep XI st m) := by
  unfold layoutStep
  by_cases hv : LayoutValid XI m
  · have hb : XI.blockOf[m]! < 4 := hv
    simp only [hb, ite_true]
    have hs1 : XI.blockOf[m]! < st.1.size := by rw [h.s1]; exact hb
    have hs2 : m < st.2.size := by rw [h.s2]; exact hm
    refine ⟨by simp [h.s1], by simp [h.s2], ?_, ?_⟩
    · intro c hc hcv
      dsimp only
      rw [set!_get1 _ _ _ _ hs2, modify_get1 _ _ _ hs1]
      by_cases hcm : c = m
      · subst hcm; simp
      · have hlt : c < m := by omega
        have := h.lt c hlt hcv
        simp only [show ¬ m = c from fun e => hcm e.symm, ite_false]
        split_ifs
        · omega
        · omega
    · intro c c' hc hc' hcv hcv' hbb hne
      dsimp only
      rw [set!_get1 _ _ _ _ hs2, set!_get1 _ _ _ _ hs2]
      by_cases e1 : c = m <;> by_cases e2 : c' = m
      · exact absurd (e1.trans e2.symm) hne
      · subst e1
        have hlt : c' < c := by omega
        have := h.lt c' hlt hcv'
        simp only [ite_true, show ¬ c = c' from hne, ite_false]
        rw [hbb]; omega
      · subst e2
        have hlt : c < c' := by omega
        have := h.lt c hlt hcv
        simp only [ite_true, show ¬ c' = c from fun e => hne e.symm, ite_false]
        rw [← hbb]; omega
      · have h1 : c < m := by omega
        have h2 : c' < m := by omega
        simp only [show ¬ m = c from fun e => e1 e.symm, show ¬ m = c' from fun e => e2 e.symm, ite_false]
        exact h.inj c c' h1 h2 hcv hcv' hbb hne
  · have : layoutStep XI st m = st := by
      unfold layoutStep
      have hn : ¬ XI.blockOf[m]! < 4 := hv
      simp [hn]
    unfold layoutStep at this
    rw [this]
    refine ⟨h.s1, h.s2, fun c hc hcv => ?_, fun c c' hc hc' hcv hcv' hbb hne => ?_⟩
    · have : c ≠ m := fun e => hv (e ▸ hcv)
      exact h.lt c (by omega) hcv
    · have : c ≠ m := fun e => hv (e ▸ hcv)
      have : c' ≠ m := fun e => hv (e ▸ hcv')
      exact h.inj c c' (by omega) (by omega) hcv hcv' hbb hne

theorem LInv_fold (XI : ExecInst) : ∀ m, m ≤ XI.nc + XI.nq →
    LInv XI m ((List.range m).foldl (layoutStep XI) (Array.replicate 4 0, Array.replicate (XI.nc + XI.nq) 0))
  | 0, _ => LInv_init XI
  | m + 1, hm => by
      rw [List.range_succ, List.foldl_append]
      exact LInv_step XI m (by omega) _ (LInv_fold XI m (by omega))

/-- **`rank < W`**: every column of a committed block has a rank below the block's width -/
theorem blockLayout_rank_lt (XI : ExecInst) (c : ℕ) (hc : c < XI.nc + XI.nq) (hv : LayoutValid XI c) :
    (blockLayout XI).2[c]! < (blockLayout XI).1[XI.blockOf[c]!]! :=
  (LInv_fold XI _ le_rfl).lt c hc hv

/-- ranks are distinct inside a block -/
theorem blockLayout_rank_inj (XI : ExecInst) (c c' : ℕ) (hc : c < XI.nc + XI.nq) (hc' : c' < XI.nc + XI.nq)
    (hv : LayoutValid XI c) (hv' : LayoutValid XI c') (hb : XI.blockOf[c]! = XI.blockOf[c']!) (hne : c ≠ c') :
    (blockLayout XI).2[c]! ≠ (blockLayout XI).2[c']! :=
  (LInv_fold XI _ le_rfl).inj c c' hc hc' hv hv' hb hne

/-- **verifier-side L6, closed**: the base read of column `c` at `idx ∈ {g, g + half}` (`g = q % half`, `s = idx / half`) is a selected leaf of its
block's tree, for every valid column (the `rank < W` hypothesis of `leafPos_mem_treeSel` is now proved) -/
theorem baseRead_mem_treeSel (XI : ExecInst) (c : ℕ) (hc : c < XI.nc + XI.nq) (hv : LayoutValid XI c) (pos : Array ℕ) (q : ℕ)
    (hq : q ∈ pos.toList) (s : ℕ) (hs : s < 2) :
    ((q % 2 ^ (XI.nD - 1)) % 2 ^ (XI.nD - 1)) * 2 * (blockLayout XI).1[XI.blockOf[c]!]! + s * (blockLayout XI).1[XI.blockOf[c]!]!
        + (blockLayout XI).2[c]! ∈ (treeSel XI (blockLayout XI).1[XI.blockOf[c]!]! XI.blockOf[c]! pos).toList :=
  leafPos_mem_treeSel XI _ _ pos hv q _ hq (blockLayout_rank_lt XI c hc hv) s hs

/-! ###  params: the verifier's own instance-fact check `paramsOk` (dShift = 7, nD ≤ 32, injectivity of the trace domain) -/

theorem psiV_inj (a b : UInt64) (ha : canon a) (hb : canon b) (h : psiV a = psiV b) : a = b :=
  canon_inj _ _ ha hb ((algebraMap (ZMod NockvmE2E.Exec.p) KC).injective h)

theorem psiV_one : psiV 1 = 1 := by unfold psiV; rw [zv_one, map_one]
theorem psiV_zero : psiV 0 = 0 := by unfold psiV; rw [zv_zero, map_zero]

theorem canon_hGen_of_allCanon (XI : ExecInst) (z : List Nat) (π : FlatProof) (h : allCanon XI z π = true) : canon XI.hGen := by
  unfold allCanon at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hG⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  have hpp : NockvmE2E.Exec.p = VF.PN := by unfold NockvmE2E.Exec.p VF.PN; decide
  unfold VF.based at hG
  show XI.hGen.toNat < NockvmE2E.Exec.p
  rw [hpp]; simpa using hG

theorem genOrderOk_sound (g : VF.G) : ∀ (n : ℕ) (acc : VF.G), canon acc → genOrderOk g n acc = true →
    ∀ m < n, psiV acc * psiV g ^ m ≠ 1 := by
  intro n
  induction n with
  | zero => intro acc _ _ m hm; omega
  | succ n ih =>
    intro acc hacc h m hm
    unfold genOrderOk at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases m with
    | zero =>
      intro e
      rw [pow_zero, mul_one] at e
      have : acc = 1 := psiV_inj acc 1 hacc (by unfold canon; decide) (e.trans psiV_one.symm)
      simp [this] at h1
    | succ m =>
      have := ih (VF.mul acc g) (mul_lt _ _) h2 m (by omega)
      rw [psiV_mul] at this
      intro e; apply this; rw [← e]; ring

/-- **`flatOk_dGen`**: `psiV XI.dGen = zeta XI.nD` (`DomLink.dGen_eq`), read off the verifier's `paramsOk` (`dGen = dGenOf nD`) -/
theorem flatOk_dGen (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC) := by
  have hp : paramsOk XI = true := by obtain ⟨_, _, _, h, _⟩ := hok; exact h
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hd : XI.dGen = dGenOf XI.nD := hp.2
  rw [hd, zeta_val, root_toZ]
  unfold dGenOf
  rw [psiV_pow, psiV_pow, show psiV VF.seven = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 from by
    unfold psiV; exact congrArg (algebraMap (ZMod NockvmE2E.Exec.p) KC) zv_seven]
  simp [gZ, map_pow]

/-- **`hshift`, `hn32`, `hinj` read off `FlatOk`** (the verifier's `paramsOk`) -/
theorem flatOk_params (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    XI.dShift = 7 ∧ XI.nD ≤ 32 ∧
    Set.InjOn (fun i => psiV XI.hShift * psiV XI.hGen ^ i) (Finset.range XI.hN : Set ℕ) := by
  have hp : paramsOk XI = true := by obtain ⟨_, _, _, h, _⟩ := hok; exact h
  have hcS := (instCan_of_flatOk XI H FS z π hok).hShift
  have hcG := canon_hGen_of_allCanon XI z π hok.1
  unfold paramsOk at hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨⟨⟨⟨h7, h32⟩, hS1⟩, hG0⟩, hord⟩, hdg⟩ := hp
  refine ⟨h7, h32, ?_⟩
  have hSne : psiV XI.hShift ≠ 0 := by rw [hS1, psiV_one]; exact one_ne_zero
  have hGne : psiV XI.hGen ≠ 0 := fun e => hG0 (psiV_inj _ 0 hcG (by unfold canon; decide) (e.trans psiV_zero.symm))
  have key : ∀ i j : ℕ, i < j → j < XI.hN → psiV XI.hShift * psiV XI.hGen ^ i ≠ psiV XI.hShift * psiV XI.hGen ^ j := by
    intro i j hij hj e
    have e1 : psiV XI.hGen ^ i = psiV XI.hGen ^ j := mul_left_cancel₀ hSne e
    obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
    have hgi : psiV XI.hGen ^ i ≠ 0 := pow_ne_zero _ hGne
    have e2 : psiV XI.hGen * psiV XI.hGen ^ m = 1 :=
      (mul_left_cancel₀ hgi (show psiV XI.hGen ^ i * 1 = psiV XI.hGen ^ i * (psiV XI.hGen * psiV XI.hGen ^ m) from
        calc psiV XI.hGen ^ i * 1 = psiV XI.hGen ^ i := mul_one _
          _ = psiV XI.hGen ^ (i + (m + 1)) := e1
          _ = _ := by ring)).symm
    exact genOrderOk_sound XI.hGen (XI.hN - 1) XI.hGen hcG hord m (by omega) e2
  intro i hi j hj e
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hj e
  · exact key j i h hi e.symm

theorem nD_le_of_verify (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (hv : verifyFlat XI H FS z π = true) : XI.nD ≤ 32 :=
  (flatOk_params XI H FS z π ((verifyFlat_iff XI H FS z π).mp hv)).2.1

/-! ###  pubwire: the inputs of `pubCheck_sound` read off `FlatOk` -/

theorem inpCan_of_inpCanOk (inp : PE.PubIn) (h : inpCanOk inp = true) : NockvmE2E.Exec.SP.InpCan inp := by
  unfold inpCanOk at h
  rw [List.all_eq_true] at h
  have key : ∀ c ∈ inp.claimCells ++ inp.pins, c.key < VF.PN ∧ c.idx < VF.PN ∧ c.hi < VF.PN ∧ c.lo < VF.PN := by
    intro c hc
    have := h c hc
    simp only [VF.based, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    exact ⟨h1, h2, h3, h4⟩
  constructor
  · intro c hc
    have := key c (List.mem_append_left _ hc)
    exact ⟨this.2.2.1, this.2.2.2⟩
  · intro q hq
    exact key q (List.mem_append_right _ hq)

theorem flatOk_inpCan (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    NockvmE2E.Exec.SP.InpCan XI.pubIn := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hok
  exact inpCan_of_inpCanOk _ h

theorem slotsOf_canon (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    ∀ s ∈ slotsOf XI FS z π, canon3 s := by
  have hc := chalCan_of_flatOk XI H FS z π hok
  unfold slotsOf
  apply canon_slots
  intro x hx
  rcases Array.mem_append.mp hx with hx | hx
  · exact canon_k3s _ (hc 1) _ x hx
  · exact canon_k3s _ (hc 2) _ x hx

theorem pubOfProof_canon (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π) :
    ∀ g ∈ pubOfProof XI π, canon g := by
  obtain ⟨hvT, _, _, _⟩ := flatOk_limbs XI H FS z π hok
  intro g hg
  unfold pubOfProof at hg
  obtain ⟨c, _, rfl⟩ := Array.mem_map.mp hg
  exact (canon_vT_get π hvT c 0).1


end NockvmE2E.Exec.V

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle
section Closed

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (hdom : 2 ^ (∑ j, ((s1) j).val) * d.val ≤ 2 ^ XI.nD)
variable (Op : Type) [Finite Op] [DecidableEq Op]

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ωS) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L


theorem zeta_mem_openPts (XI : ExecInst) (ζ : VF.K3) : ζ ∈ (openPts XI ζ).toList := by
  simp [openPts]

/-- `DeepLink` minus `hqlen` (read off `FlatOk`: `π.vQ.size = XI.nq`, with `hnq`) and minus `hinj` (read off `FlatOk`: `paramsOk`) -/
structure DeepLinkC (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ KC) (α ζ : KC)
    (vT : ι × Fin r → KC) (vQ : Fin P.nq → KC) : Prop where
  hα : toKV (alphaOf XI FS z π) = α
  hζ : toKV (zetaOf XI FS z π) = ζ
  hlen : (termsOfK XI FS z π).length = P.ns
  hdag : ∀ i : Fin (termsOfK XI FS z π).length, (termsOfK XI FS z π).get i = A.Cv χ ζ (Fin.cast hlen i) vT
  hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)
  he : P.e = 3
  hnq : XI.nq = P.nq
  hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j
  hQ : ∀ j : Fin P.nq, toKV π.vQ[j.1]! = vQ j


/-- the remaining hypotheses of `verifyFlat_sound'` (everything else of `LocalLinks` is discharged), at `q0 := q0P` -/
structure ClosedLinks
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop) : Prop where
  hcov : CoversC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (round_bound hdom)
      (xsC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op p) (decode (pathRootsK Dg Op (MC) p).2)
  hD : DeepLinkC XI H FS zF π P A
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.a)
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.z)
      (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
      (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.2
  hpts : ∀ ck : ι × Fin r, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList,
      toKV pt = A.pt ck.1 ck.2 (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) P.z)
  hRV : PubRel (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).1
        (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
        (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
  hF : FriLinkAt s1 d XI.l
      ((combinedStmt s1 m G (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
        (deepStmt (ω := ωS) P A R0 e
          (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))), z.2))
      (Fri.toFriPath s1 d XI.l L Dg enc (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.2)
      (homV.ψ XI.dShift) (homV.ψ XI.dGen) (fun j => π.pos[j.1]!)
      (fun w i => homV.φ (SF.Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
      (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) (fun i => homV.φ (alphasOf XI FS zF π)[i]!)


theorem hcg_of_shift (hn32 : XI.nD ≤ 32) (hshift : XI.dShift = 7) :
    (((smoothDomain XI.nD hn32).cosetGenerator : KCˣ) : KC) = psiV XI.dShift := by
  rw [hshift]
  have : psiV (7 : UInt64) = algebraMap (ZMod p) KC 7 := by unfold psiV; exact congrArg (algebraMap (ZMod p) KC) zv_seven
  rw [this]
  rfl

/-- **L11, bookkeeping discharged (`verifyFlat_sound'`)**: `verifyFlat` accepts => Merkle roots (L3), the audited local check `cLocal` accepts, and
the public relation holds, under `ClosedLinks` (the J-8 / oracle-history / layout links).  `XI.nD <= 32`, `XI.dShift = 7` and the
injectivity of the trace domain (`hinj`) are read off `FlatOk` (`paramsOk`, `flatOk_params`); `hv` precedes the audited objects (the domain `smoothDomain` is built from `nD_le_of_verify hv`).  Discharged here: `hnD hk hl` (the audited parameters ARE the
instance's), `hs1` (the FRI arities are all 1), `hq0` (`q0 := q0P`), `hqlen` (read off `FlatOk`), `hcg` (from `paramsOk`). -/
theorem verifyFlat_sound'
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop)
    (hPub : XI.pubCheck (slotsOf XI FS zF π) (pubOfProof XI π) = true → PubRel (slotsOf XI FS zF π) (pubOfProof XI π))
    (Ls : ClosedLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p PubRel) :
    (∀ j, j < 4 + XI.k → ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0) → MerkleRootOk XI H π j) ∧
    cLocal P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l G Dg enc md L hdom Op decode z p = true ∧
      PubRel (slotsOf XI FS zF π) (pubOfProof XI π) := by
  have hok := (verifyFlat_iff XI H FS zF π).mp hv
  have hpar := flatOk_params XI H FS zF π hok
  have hq : π.vQ.size = P.nq := by
    obtain ⟨_, _, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    rw [h5.1.1.2, Ls.hD.hnq]
  exact verifyFlat_sound P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l G Dg enc md L hdom Op XI H FS zF π hv decode z p
    (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p) PubRel
    ⟨rfl, rfl, rfl, hcg_of_shift XI _ hpar.1, fun _ => rfl, rfl, Ls.hcov,
      ⟨Ls.hD.hα, Ls.hD.hζ, Ls.hD.hlen, Ls.hD.hdag, Ls.hD.hH, hpar.2.2, Ls.hD.he, Ls.hD.hnq, hq, Ls.hD.hcw, Ls.hD.hQ⟩,
      fun j => by
        unfold ptOf
        rcases h : e j with ck | q
        · simp only [Sum.elim_inl]; exact Ls.hpts ck
        · simp only [Sum.elim_inr]; exact ⟨_, zeta_mem_openPts XI _, Ls.hD.hζ⟩,
      hPub, Ls.hRV, Ls.hF⟩

/-- the public relation of the J-8 verifier-side objects: `pubCheck_sound`'s conclusion on `(slots, pub)` for the instance data `inp`; since it also carries `ComputeDerivedP` (the coin-derived compute publics 6..14, claim atoms) -/
def PubJ8P (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array Nat) (slots : Array VF.K3) (pub : Array UInt64) : Prop :=
  (∃ cr pr : List (List PE.K6),
      inp.claimCells.mapM (SP.claimRecS ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩
        ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩ (SP.slOf L pub 0)) = some cr ∧
      inp.pins.mapM (SP.pinRecS ⟨(SP.coinsOf slots slotOf)[2]!, (SP.coinsOf slots slotOf)[3]!⟩
        ⟨(SP.coinsOf slots slotOf)[17]!, (SP.coinsOf slots slotOf)[18]!⟩) = some pr ∧
      SP.PubJ8Rel (fun i : Fin 19 => toKV (SP.coinsOf slots slotOf)[(i : ℕ)]!) (SP.rhoOf (SP.slOf L pub 0))
        (SP.rhoSOf (SP.slOf L pub 0)) (SP.pubK (SP.slOf L pub 1)) (SP.pubK (SP.slOf L pub 2)) (SP.pubK (SP.slOf L pub 3))
        (SP.pubK (SP.slOf L pub 4)) (SP.pubK (SP.slOf L pub 5))
        (inp.pins.map fun q => (SP.recQ (PE.pinConsKey q.key q.idx) : Fin 8 → SP.Q))
        (cr.map fun r => (SP.recQ r : Fin 5 → SP.Q)) (pr.map fun r => (SP.recQ r : Fin 5 → SP.Q))) ∧
  SP.ComputeDerivedP inp (SP.coinsOf slots slotOf) (SP.slOf L pub 0)

/-- **L11 with the public relation discharged (`verifyFlat_sound_J8Pub`)**: `verifyFlat_sound'` at `PubRel := PubJ8P XI.pubIn L slotOf`; the
hypothesis `hPub` is now PROVED (`pubCheck_sound`, with `InpCan` read off `FlatOk` via `inpCanOk`, slots/publics canonical from `FlatOk`).  No link
hypothesis: the instance carries its own `pubIn`, `pubLay`, `slotOf` and the verifier calls `PE.pubCheck` on them (`pubMode = 0`, the only mode `loadInst` produces; test-mode toys are excluded by `hmode`). -/
theorem verifyFlat_sound_J8Pub
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (hmode : XI.pubMode = 0)
    (Ls : ClosedLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p
      (PubJ8P XI.pubIn XI.pubLay XI.slotOf)) :
    (∀ j, j < 4 + XI.k → ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0) → MerkleRootOk XI H π j) ∧
    cLocal P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l G Dg enc md L hdom Op decode z p = true ∧
      PubJ8P XI.pubIn XI.pubLay XI.slotOf (slotsOf XI FS zF π) (pubOfProof XI π) := by
  have hok := (verifyFlat_iff XI H FS zF π).mp hv
  refine verifyFlat_sound' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p
    (PubJ8P XI.pubIn XI.pubLay XI.slotOf) (fun hc => ?_) Ls
  have hc' : PE.pubCheck XI.pubIn XI.pubLay XI.slotOf (slotsOf XI FS zF π) (pubOfProof XI π) = true := by
    simpa [ExecInst.pubCheck, hmode] using hc
  exact SP.pubCheck_sound XI.pubIn XI.pubLay XI.slotOf _ _ (slotsOf_canon XI H FS zF π hok) (pubOfProof_canon XI H FS zF π hok)
    (flatOk_inpCan XI H FS zF π hok) hc'

/-- **`PubSound`**: the executed public check of an instance is sound for the public relation `PR`: whatever passes `XI.pubCheck` on canonical
slots / publics / instance data satisfies `PR`.  `pubSound_J8` (here) and `pubSound_J9` (`J9A/PubSoundJ9A.lean`) discharge it from `pubMode`. -/
def PubSound (XI : ExecInst) (PR : Array VF.K3 → Array VF.G → Prop) : Prop :=
  ∀ (slots : Array VF.K3) (pub : Array VF.G), (∀ s ∈ slots, canon3 s) → (∀ g ∈ pub, canon g) →
    NockvmE2E.Exec.SP.InpCan XI.pubIn → XI.pubCheck slots pub = true → PR slots pub

/-- the J-8 relation is sound at `pubMode = 0` (`SP.pubCheck_sound`) -/
theorem pubSound_J8 (XI : ExecInst) (hmode : XI.pubMode = 0) :
    PubSound XI (PubJ8P XI.pubIn XI.pubLay XI.slotOf) := by
  intro slots pub hs hp hinp hc
  have hc' : PE.pubCheck XI.pubIn XI.pubLay XI.slotOf slots pub = true := by
    simpa [ExecInst.pubCheck, hmode] using hc
  exact SP.pubCheck_sound XI.pubIn XI.pubLay XI.slotOf _ _ hs hp hinp hc'

/-- **L11 over an arbitrary public relation (`verifyFlat_sound_Pub`)**: `verifyFlat_sound'` with `hPub` from `PubSound XI PR` -/
theorem verifyFlat_sound_Pub
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (PR : Array VF.K3 → Array VF.G → Prop) (hPS : PubSound XI PR)
    (Ls : ClosedLinks XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p PR) :
    (∀ j, j < 4 + XI.k → ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0) → MerkleRootOk XI H π j) ∧
    cLocal P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l G Dg enc md L hdom Op decode z p = true ∧
      PR (slotsOf XI FS zF π) (pubOfProof XI π) := by
  have hok := (verifyFlat_iff XI H FS zF π).mp hv
  exact verifyFlat_sound' XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L hdom Op decode z p PR
    (fun hc => hPS _ _ (slotsOf_canon XI H FS zF π hok) (pubOfProof_canon XI H FS zF π hok) (flatOk_inpCan XI H FS zF π hok) hc) Ls

end Closed
end NockvmE2E.Merkle.RapFriQ

/-! ### non-vacuity of the instance-level facts (kernel, `toyInst` of `VerifyMain.lean`: `nD = 5`, `dShift = 7`) -/
namespace NockvmE2E.Exec.V

/-- the layout shape of the exe's `toyInst` (`VerifyMain.lean`: `nD = 5`, `dShift = 7`, three columns of kinds 0/1/2 in blocks 0/0/2, three chunk columns in block 3) -/
def toyInstB : ExecInst :=
  { nD := 5, dShift := 7, dGen := 2, hN := 4, hGen := 1, hShift := 1, r := 2, k := 1, d := 1, l := 4, nc := 3, nq := 3,
    colKind := #[0, 1, 2], blockOf := #[0, 0, 2, 3, 3, 3], pre := #[#[], #[], #[]], pubOf := #[2], ppt := VF.K3.one,
    nCoins := #[0, 0], derived := #[], tabs := #[], pubMode := 1 }

example : toyInstB.nD ≤ 32 := by decide
example : toyInstB.dShift = 7 := by decide
example : NockvmE2E.Exec.VL.psiV toyInstB.dShift = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 := by
  have : toyInstB.dShift = 7 := by decide
  rw [this]; unfold NockvmE2E.Exec.VL.psiV; exact congrArg (algebraMap (ZMod NockvmE2E.Exec.p) KC) NockvmE2E.Exec.VL.zv_seven
/-- the layout lemmas are about a nonempty class: columns 0 and 2 occupy block 0 resp. 2 (ranks 0 < W 1 and 0 < W 1); chunk columns share block 3 -/
example : ∃ c, c < toyInstB.nc + toyInstB.nq ∧ LayoutValid toyInstB c ∧
    (blockLayout toyInstB).2[c]! < (blockLayout toyInstB).1[toyInstB.blockOf[c]!]! := by
  have hc : 0 < toyInstB.nc + toyInstB.nq := by decide
  have hv : LayoutValid toyInstB 0 := by unfold LayoutValid; decide
  exact ⟨0, hc, hv, blockLayout_rank_lt toyInstB 0 hc hv⟩
/-- two distinct chunk columns of block 3 have distinct ranks (the layout class has nontrivial blocks) -/
example : (blockLayout toyInstB).2[3]! ≠ (blockLayout toyInstB).2[4]! :=
  blockLayout_rank_inj toyInstB 3 4 (by decide) (by decide) (by unfold LayoutValid; decide) (by unfold LayoutValid; decide) (by decide) (by decide)

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.blockLayout_rank_lt
#print axioms NockvmE2E.Exec.V.blockLayout_rank_inj
#print axioms NockvmE2E.Exec.V.baseRead_mem_treeSel
#print axioms NockvmE2E.Merkle.RapFriQ.hcg_of_shift
#print axioms NockvmE2E.Merkle.RapFriQ.verifyFlat_sound'
#print axioms NockvmE2E.Exec.V.flatOk_params
#print axioms NockvmE2E.Exec.V.flatOk_dGen
#print axioms NockvmE2E.Exec.V.flatOk_inpCan
#print axioms NockvmE2E.Merkle.RapFriQ.verifyFlat_sound_J8Pub
#print axioms NockvmE2E.Merkle.RapFriQ.verifyFlat_sound_Pub
#print axioms NockvmE2E.Merkle.RapFriQ.pubSound_J8
