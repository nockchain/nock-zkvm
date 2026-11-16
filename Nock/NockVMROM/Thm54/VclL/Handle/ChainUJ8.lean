/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChainUJ8.lean

  **Card J-8a R4b : the chain lemmas over `SmallU`** (S1, restated by R3b:
  `ReaderR3bJ8.SmallU` asks smallness only of what the chain lemmas READ — `idx aL wR aR inc cout kRO` on every
  row, `idR` on a weighted row, `idxO lO vRO` on an inc row; the free cells Q2's `no_small_reader` exhibits are not
  in it).  Each lemma is the original's statement with `Small` replaced by `SmallU`; the proofs are the originals',
  reading the conditional bounds after the condition is established.  New module, additive.

  * ℕ / field level: `chainOK_of_gatesU` (the next-row reads and the next row's smallness are needed only when
    `c_out = 1`), `oldGenuine_of_servedU`, `inc_chain_sound_of_servedU`.
  * chip level: `hchain_of_servedU` (AtomDenJ8), `agree_atomU`, `hold_of_servedU` (AtomCombJ8),
    `atomInc_provOKI_limbU`, `atomInc_provOKIU` (RecOKIJ8), `bnd_of_mbU` (AtomLeavesBJ8).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CorJ8I
import Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ChainUJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK natKey)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads ReadsNext atomChipHQ atomGates incKey tagInc
  LimbsBounded ChainOK OldGenuine ConsumeServedQ cast_inj cast_bool Bf_eq g70 g71 g72 g73 g74 ovf valR oldKey
  inc_chain_sound bnd)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF atom_base atomEnvN atomEnvN_lt acoins atomCReqs atomProvs
  liftProvs consumeServedQ_of_balance)
open Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8 (len_cases8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (AgreeRow atom_g23 restr_trace denH_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (RecOKI PreI provPI_of_forall)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.Atoms (val B B_eq)

noncomputable section

/-! ## 1. The ℕ chain relations and the old-node copy over `SmallU` -/

section Bridge
variable {F : Type} [Field F]

/-- **`chainOK_of_gates` over `SmallU`**: the next row's reads and its smallness are asked for only when the row
carries out (`c_out = 1`); on a stopping row the link and overflow relations are vacuous. -/
theorem chainOK_of_gatesU (hq : 2 ^ 63 < ringChar F) {e : Env F} {r : ℕ → ARow} {i : ℕ}
    (hg : ∀ g ∈ (atomGates (F := F)), g.eval e = 0) (hr : Reads e (r i))
    (hn : (r i).cout = 1 → ReadsNext e (r (i + 1))) (hs : SmallU (r i))
    (hs' : (r i).cout = 1 → SmallU (r (i + 1)))
    (hidx : (r i).idx = i) (hwR : (r i).wR ≤ 1) (hinc : (r i).inc = 1)
    (hlimb : (r i).aL < B ∧ (r i).lO < B) :
    ChainOK r i := by
  obtain ⟨s1, s2, s3, s5, s6, s7, s10, s4, s8911⟩ := hs
  obtain ⟨s8, s9, s11⟩ := s8911 hinc
  have sub : ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, g ∈ (atomGates (F := F))) →
      ∀ g ∈ l, g.eval e = 0 := fun l hl g h => hg g (hl g h)
  have h70 := sub g70 (fun g h => by simp [atomGates, h])
  have h71 := sub g71 (fun g h => by simp [atomGates, h])
  have h72 := sub g72 (fun g h => by simp [atomGates, h])
  have h73 := sub g73 (fun g h => by simp [atomGates, h])
  have h74 := sub g74 (fun g h => by simp [atomGates, h])
  simp only [g70, g71, g72, g73, g74, ovf, valR, CellH.valE, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, forall_const, implies_true, and_true, CoeffExpr.eval, hr.idx, hr.aL, hr.wR, hr.idR,
    hr.aR, hr.inc, hr.cout, hr.idxO, hr.lO, hr.kRO, hr.vRO,
    hinc, hidx, Nat.cast_one, one_mul, mul_one] at h70 h71 h72 h73 h74
  obtain ⟨-, -, bc, bk, -, -, -⟩ := h70
  obtain ⟨a73, b73, c73, d73⟩ := h73
  obtain ⟨a74, b74, c74, d74, e74, f74⟩ := h74
  obtain ⟨a72, b72⟩ := h72
  have hc1 := cast_bool hq (by omega) bc
  have hk1 := cast_bool hq (by omega) bk
  have hBn : B = 4294967296 := B_eq
  have cast_eq : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → (x : F) = y → x = y :=
    fun hx hy h => cast_inj hq hx hy h
  have limb : (r i).aL + B * (r i).cout = (r i).lO + 1 := by
    have := hlimb.1; have := hlimb.2
    apply cast_eq (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h | h <;> rw [h] <;> omega)
      (by omega)
    push_cast; rw [← Bf_eq]; linear_combination h71
  refine ⟨hc1, hk1, limb, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at a72 b72
    simp only [Nat.cast_zero, sub_zero, one_mul] at a72 b72
    refine ⟨cast_eq (by omega) (by omega) (sub_eq_zero.mp a72), ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hwR with h | h
    · rw [h] at b72; simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add] at b72
      simpa [ARow.valR, h] using cast_eq (by omega) (by omega) (sub_eq_zero.mp b72)
    · have s4' := s4 h
      rw [h] at b72; simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at b72
      simpa [ARow.valR, h] using cast_eq (by omega) (by omega) (sub_eq_zero.mp b72)
  · intro h1 hk
    have hn1 := hn h1
    obtain ⟨t1, t2, t3, t5, t6, t7, t10, t4, t8911⟩ := hs' h1
    rw [h1, hk] at a73 b73 c73 d73
    rw [hn1.idxO] at b73
    rw [hn1.inc] at d73
    simp only [Nat.cast_one, one_mul] at a73 b73 c73 d73
    have hw1 : (r i).wR = 1 :=
      cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp c73).symm.trans Nat.cast_one.symm)
    have s4' := s4 hw1
    have hni : (r (i + 1)).inc = 1 :=
      cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp d73).symm.trans Nat.cast_one.symm)
    obtain ⟨t8, -, -⟩ := t8911 hni
    refine ⟨hw1, ?_, ?_, hni⟩
    · apply cast_eq (by omega) (by omega); push_cast; linear_combination a73
    · exact cast_eq (by omega) (by omega) (sub_eq_zero.mp b73)
  · intro h1 hk hw0
    rw [h1, hk, hw0] at a74
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, one_mul] at a74
    apply cast_eq (by omega) (by omega); push_cast; linear_combination a74
  · intro h1 hk hw1
    have hn1 := hn h1
    obtain ⟨t1, t2, t3, t5, t6, t7, t10, t4, t8911⟩ := hs' h1
    have s4' := s4 hw1
    rw [h1, hk, hw1] at b74 c74 d74 e74 f74
    rw [hn1.aL] at d74
    rw [hn1.wR] at e74
    rw [hn1.aR] at f74
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, one_mul] at b74 c74 d74 e74 f74
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply cast_eq (by omega) (by omega)
      rw [Nat.cast_sub (by norm_num [B]), ← Bf_eq]; push_cast; linear_combination b74
    · apply cast_eq (by omega) (by omega); push_cast; linear_combination c74
    · exact cast_eq (by omega) (by norm_num) (d74.trans Nat.cast_zero.symm)
    · exact cast_eq (by omega) (by norm_num) (e74.trans Nat.cast_zero.symm)
    · exact cast_eq (by omega) (by norm_num) ((sub_eq_zero.mp f74).trans Nat.cast_one.symm)

/-- **`oldGenuine_of_served` over `SmallU`.** -/
theorem oldGenuine_of_servedU (hq : 2 ^ 63 < ringChar F) {env : ℕ → Env F} {r : ℕ → ARow} {n : ℕ}
    (hR : ∀ k < n, Reads (env k) (r k)) (hwL : ∀ k < n, (env k).trace Cell.wL = 0)
    (hwR : ∀ k < n, (r k).wR ≤ 1) (hs : ∀ k < n, SmallU (r k)) (hidx : ∀ k < n, (r k).idx = k)
    (hserved : ConsumeServedQ env n) : ∀ i < n, (r i).inc = 1 → OldGenuine r i := by
  intro i hi hinc
  have hRi := hR i hi
  obtain ⟨j, hj, hkey⟩ := hserved i hi (by rw [hRi.inc, hinc, Nat.cast_one])
  have hRj := hR j hj
  simp only [CellH.keyH, oldKey, CellH.valE, List.map_cons, List.map_nil, CoeffExpr.eval,
    List.cons.injEq, and_true, hwL j hj, hRj.idx, hRj.aL, hRj.wR, hRj.idR, hRj.aR, hRi.idxO, hRi.lO,
    hRi.kRO, hRi.vRO, sub_zero, zero_mul, one_mul, zero_add] at hkey
  obtain ⟨e1, -, e3, e4, e5⟩ := hkey
  obtain ⟨s1, s2, s3, s5, -, -, -, s4, -⟩ := hs j hj
  obtain ⟨-, -, -, -, -, -, t10, -, t8911⟩ := hs i hi
  obtain ⟨t8, t9, t11⟩ := t8911 hinc
  have ce : ∀ {x y : ℕ}, x < 2 ^ 62 → y < 2 ^ 62 → (x : F) = y → x = y :=
    fun hx hy h => cast_inj hq (by omega) (by omega) h
  have hjo : j = (r i).idxO := by rw [← hidx j hj]; exact ce s1 t8 e1
  subst hjo
  refine ⟨ce s2 t9 e3, ce s3 t10 e4, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hwR _ hj) with h | h
  · rw [h] at e5; simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add] at e5
    simpa [ARow.valR, h] using ce s5 t11 e5
  · rw [h] at e5; simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at e5
    simpa [ARow.valR, h] using ce (s4 h) t11 e5

/-- **`inc_chain_sound_of_served` over `SmallU`.** -/
theorem inc_chain_sound_of_servedU (hq : 2 ^ 63 < ringChar F) {env : ℕ → Env F} {r : ℕ → ARow}
    {n : ℕ} (hR : ∀ k < n, Reads (env k) (r k)) (hwL : ∀ k < n, (env k).trace Cell.wL = 0)
    (hs : ∀ k < n, SmallU (r k)) (hidx : ∀ k < n, (r k).idx = k)
    (hserved : ConsumeServedQ env n) (hout : ∀ k, n ≤ k → (r k).inc = 0)
    (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1) (hok : ∀ j, (r j).inc = 1 → ChainOK r j)
    {i : ℕ} {lold : List ℕ} (hinc : (r i).inc = 1) (hold : Denotes r (r i).idxO lold) :
    ∃ lnew, Denotes r i lnew ∧ val lnew = val lold + 1 := by
  refine inc_chain_sound hB hw hok (fun j hj => ?_) hinc hold
  by_cases hjn : j < n
  · exact oldGenuine_of_servedU hq hR hwL (fun k _ => hw k) hs hidx hserved j hjn hj
  · have := hout j (by omega); omega

end Bridge

/-! ## 2. `hchain` (AtomDenJ8) over `SmallU` -/

section Chain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  [DecidableEq F] [DecidableEq K] [DecidableEq (Quad (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **`AtomDenJ8.hchain_of_served` over `SmallU`.** -/
theorem hchain_of_servedU {p : ℕ} [CharP 𝕂′ p] (hq : 2 ^ 63 < ringChar F)
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (wreqs : List (Fin 5 → K))
    (hbal : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubs AtomChipHQ.pubC) (pubs (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (acoins δF chals) r)⁻¹).sum)
    (hout : ((acoins δF chals).gamma, (acoins δF chals).pole) ∉
      IOFailureEventW ((atomCReqs b nodes orbit chals pubs Q ++ wreqs).map (liftRec (K := K) (L := 𝕂′)))
        (liftProvs δF (atomProvs b nodes orbit chals pubs Q)))
    (hcount : (atomCReqs b nodes orbit chals pubs Q ++ wreqs).length < p)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (aEF b nodes orbit chals pubs Q k) (r k))
    (hs : ∀ k : Fin n, SmallU (r k)) (hidx : ∀ k : Fin n, (r k).idx = k)
    (hwL : ∀ k : Fin n, (aEF b nodes orbit chals pubs Q k).trace Cell.wL = 0)
    (hrn : ∀ k, n ≤ k → (r k).inc = 0) (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1)
    (hok : ∀ j, (r j).inc = 1 → ChainOK r j) :
    ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1 := by
  have hserved := consumeServedQ_of_balance δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj wreqs hbal
    hout hcount
  intro k hinc lold hold
  refine inc_chain_sound_of_servedU hq (env := atomEnvN b hn nodes orbit chals pubs Q) (n := n)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => hs ⟨k, hk⟩) (fun k hk => hidx ⟨k, hk⟩) hserved hrn hB hw hok
    hinc hold
  · rw [show k = ((⟨k, hk⟩ : Fin n) : ℕ) from rfl, atomEnvN_lt]; exact hR ⟨k, hk⟩
  · rw [show k = ((⟨k, hk⟩ : Fin n) : ℕ) from rfl, atomEnvN_lt]; exact hwL ⟨k, hk⟩

end Chain

/-! ## 3. `agree_atom`, `hold` (AtomCombJ8) over `SmallU` -/

section Atom
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

/-- **`AtomCombJ8.agree_atom` over `SmallU`.** -/
theorem agree_atomU (hq : 2 ^ 63 < p)
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {rA : ℕ → ARow} (hRA : ∀ k : Fin nA, Reads (aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k) (hB : LimbsBounded rA)
    (hwR : ∀ k : Fin nA, (rA k).wR ≤ 1) :
    ∀ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA
        (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).map (·.b0),
      c.idx < nA ∧ AgreeRow c (rA c.idx) := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  intro c hc
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  have R := hRA i
  obtain ⟨s1, s2, s3, s5, -, -, -, s4, -⟩ := hsA i
  obtain ⟨g2, g3⟩ := atom_g23 hsat i
  have tr : ∀ {c : ℕ}, c < 129 → (cellEnvF b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i).trace c =
      (aEF b nodesA orbitA chalsA pubsA QA i).trace c := fun hc => restr_trace δ b hnA nodesA orbitA chalsA
        pubsA QA i hc
  have nc : ∀ {x : ℕ}, x < 2 ^ 62 → natOf ((x : ℕ) : ZMod p) = x := fun hx =>
    natOf_natCast hF (by rw [hrc]; omega)
  have vc : ∀ {x : ℕ}, x < 2 ^ 62 → (((x : ℕ) : ZMod (ringChar (ZMod p)))).val = x := fun hx => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [hrc]; omega)]
  have ce : ∀ {x y : ℕ}, x < 2 ^ 62 → y < 2 ^ 62 → (x : ZMod p) = y → x = y := fun hx hy h =>
    AtomChipHQ.cast_inj (F := ZMod p) (by rw [hrc]; exact hq) (by omega) (by omega) h
  have hidx : (cellB0Of (cellEnvF b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA) i)).idx = i := by
    simp only [cellB0Of]
    rw [tr (by decide), R.idx, nc s1, hidxA i]
  simp only [cellTableOf, cellRowOf]
  refine ⟨by rw [hidx]; exact i.2, ?_⟩
  rw [hidx]
  refine ⟨?_, ?_, (hB i).1, ?_, ?_⟩
  · simp only [cellB0Of]; rw [tr (by decide), g2]; simp
  · simp only [cellB0Of]; rw [tr (by decide), R.aL, nc s2, vc s2]
  · intro hw
    simp only [cellB0Of, decide_eq_true_eq] at hw
    rw [tr (by decide), R.wR] at hw
    have h1 : (rA i).wR = 1 := ce s3 (by norm_num) (by simpa using hw)
    refine ⟨h1, ?_⟩
    simp only [cellB0Of]; rw [tr (by decide), R.idR, nc (s4 h1)]
  · intro hw
    simp only [cellB0Of, decide_eq_false_iff_not] at hw
    rw [tr (by decide), R.wR] at hw
    have h0 : (rA i).wR = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hwR i) with h | h
      · exact h
      · exact absurd (by rw [h]; simp) hw
    refine ⟨h0, ?_, (hB i).2, ?_⟩
    · simp only [cellB0Of]; rw [tr (by decide), R.aR, nc s5, vc s5]
    · intro hz
      apply g3 (by rw [R.wR, h0]; simp)
      rw [R.aR, hz]; simp

/-- **`AtomCombJ8.hold_of_served` over `SmallU`.** -/
theorem hold_of_servedU (hq : 2 ^ 63 < p)
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {rA : ℕ → ARow} (hRA : ∀ k : Fin nA, Reads (aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k) (hB : LimbsBounded rA)
    (hwR : ∀ k : Fin nA, (rA k).wR ≤ 1)
    (hcs : ConsumeServedQ (AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA) nA) :
    ∀ k : Fin nA, (rA k).inc = 1 → ∃ l, Denotes rA (rA k).idxO l := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  intro k hinc
  have env_lt : ∀ i : Fin nA, AtomServedQ.atomEnvN b hnA nodesA orbitA chalsA pubsA QA i =
      aEF b nodesA orbitA chalsA pubsA QA i := AtomServedQ.atomEnvN_lt b hnA nodesA orbitA chalsA pubsA QA
  have Rk := hRA k
  obtain ⟨j, hj, hkey⟩ := hcs k k.2 (by rw [env_lt k, Rk.inc, hinc, Nat.cast_one])
  have Rj := hRA ⟨j, hj⟩
  rw [show j = ((⟨j, hj⟩ : Fin nA) : ℕ) from rfl, env_lt ⟨j, hj⟩, env_lt k] at hkey
  have hwLj := (atom_g23 hsat ⟨j, hj⟩).1
  simp only [CellH.keyH, AtomChipHQ.oldKey, CellH.valE, List.map_cons, List.map_nil, CoeffExpr.eval,
    List.cons.injEq] at hkey
  have e1 := hkey.1
  rw [Rj.idx, Rk.idxO] at e1
  have s1 := (hsA ⟨j, hj⟩).1
  have t8 := ((hsA k).2.2.2.2.2.2.2.2 hinc).1
  have hjo : j = (rA k).idxO := by
    refine (hidxA ⟨j, hj⟩).symm.trans ?_
    exact AtomChipHQ.cast_inj (F := ZMod p) (by rw [hrc]; exact hq) (by omega) (by omega) e1
  set tA := (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA))
  have hT := AtomChipHQ.atomTable_accepts δ b hnA nodesA orbitA chalsA pubsA hF (by rw [hrc]; exact hq) hz QA
    hsat hbind hinj hadj (by rw [hrc]; exact hnp) hserved []
  have hlen : tA.length = nA := by simp [tA, cellTableOf]
  have hjt : j < tA.length := by rw [hlen]; exact hj
  have hcm : tA[j] ∈ tA := List.getElem_mem hjt
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  obtain ⟨L, R, hd, -⟩ := Nock.NockVMROM.Thm54.VclL.row_genuine (by rw [hrc]; exact hq) hz hT hcm
  have hag := agree_atomU hq hsat hRA hsA hidxA hB hwR
  obtain ⟨hlt, -⟩ := hag _ (List.mem_map_of_mem hcm)
  have hs := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsat) hF
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbind) hinj hadj
    (by rw [hrc]; exact hnp)
  have hidx : tA[j].b0.idx = j := by
    have h1 := List.getElem_of_eq hs (i := j) (by simpa using hjt)
    simpa using h1
  rw [hidx] at hd
  obtain ⟨l, hl, -⟩ := denH_denotes hs (fun c hc => (hag c hc).2) (i := j) (by rw [denH_cell]; exact hd)
  exact ⟨l, hjo ▸ hl⟩

end Atom

/-! ## 4. The inc heads (RecOKIJ8) over `SmallU` -/

section Field
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K}
  {Q : Fin (atomChipHQ δ b hn nodes orbit chals pubs).rap.w → (ZMod p)[X]}

local notation "AE" => AtomServedQ.aEF b nodes orbit chals pubs Q

/-- **`RecOKIJ8.atomInc_provOKI_limb` over `SmallU`.** -/
theorem atomInc_provOKI_limbU (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, SmallU (r k))
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} (limbA : ℕ → ℕ → HX)
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, Denotes r j l → p ≤ val l → D (2, j) = some (.atom (val l)))
    (hDenB' : ∀ j X, D (2, j) = some X → ∃ l, Denotes r j l ∧ p ≤ val l)
    (hchain : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (fun x => PreI D x → RecOK D Rg limbA x) .s
      (pad8 (atomIncProvs b nodes orbit chals pubs Q)) := by
  have hqF : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hq
  have ce : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → ((x : ℕ) : ZMod p) = y → x = y :=
    fun hx hy e => AtomChipHQ.cast_inj hqF hx hy e
  intro q hq' l hl hlt hnk
  change l.length ≤ 8 at hl
  obtain ⟨q5, hq5, rfl⟩ := List.mem_map.mp hq'
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq5
  split_ifs at hi with hmi
  · simp at hi
  rw [List.mem_singleton] at hi
  subst hi
  set e := AE i with he
  change DenXJ8.natKey (p := p) (K := K) 8 l = padK (ServeH.keyVec5 incKey e) at hnk
  have hent : ∀ c (hc : c < 5), ((l.getD c 0 : ℕ) : ZMod p) =
      ((incKey : List (CoeffExpr (ZMod p))).getD c (.const 0)).eval e := by
    intro c hc
    have := congrFun hnk ⟨c, by omega⟩
    simp only [DenXJ8.natKey, padK, ServeH.keyVec5, dif_pos hc] at this
    exact (algebraMap (ZMod p) K).injective this
  have hent' : ∀ c, 5 ≤ c → c < 8 → ((l.getD c 0 : ℕ) : ZMod p) = 0 := by
    intro c hc5 hc8
    have := congrFun hnk ⟨c, hc8⟩
    simp only [DenXJ8.natKey, padK, dif_neg (show ¬ c < 5 by omega)] at this
    exact (algebraMap (ZMod p) K).injective (this.trans (map_zero _).symm)
  have hg := AtomServedQ.atom_base δ b hn nodes orbit chals pubs Q hsat i
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have gInc := g _ (by simp [atomGates, AtomChipHQ.g70] : boolE (cv AtomChipHQ.inc) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  have gHead := g _ (by simp [atomGates, AtomChipHQ.g70] :
    CoeffExpr.mul (cv AtomChipHQ.mi) (.sub (notE (cv AtomChipHQ.inc)) (cv AtomChipHQ.conv)) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g8a := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (.sub (cv Cell.aL) (.const 1)) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  have g8b := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (.sub (cv Cell.aR) (.const (AtomChipHQ.Bf - 1))) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g8c := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (cv Cell.wR) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  simp only [boolE, notE, cv, CoeffExpr.eval] at gInc gHead g8a g8b g8c
  have hconv : e.trace AtomChipHQ.conv = 1 - e.trace AtomChipHQ.inc := by
    have := (mul_eq_zero.mp gHead).resolve_left hmi
    linear_combination -this
  have hp4 : 4 < p := by omega
  have hRi := hR i
  obtain ⟨s1, s2, s3, s5, s6, s7, s10, s4, s8911⟩ := hs i
  have hip : (i : ℕ) < 2 ^ 62 := by rw [← hidx i]; exact s1
  rcases len_cases8 l hl with hlt5 | ⟨a0, a1, a2, a3, a4, rfl⟩ | ⟨a0, a1, a2, a3, a4, a5, rfl⟩ |
      ⟨a0, a1, a2, a3, a4, a5, a6, rfl⟩ | ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  · exfalso
    have e4 := hent 4 (by norm_num)
    rw [List.getD_eq_default _ _ (by omega)] at e4
    simp only [incKey, tagInc, List.getD_cons_succ, List.getD_cons_zero, CoeffExpr.eval, Nat.cast_zero] at e4
    have := ce (x := 0) (y := 4) (by norm_num) (by norm_num) (by exact_mod_cast e4)
    omega
  · intro hpre
    have hlt' : ∀ x ∈ [a0, a1, a2, a3, a4], x < p := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
    obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := hlt'
    have e0 := hent 0 (by norm_num); have e1 := hent 1 (by norm_num); have e2 := hent 2 (by norm_num)
    have e3 := hent 3 (by norm_num); have e4 := hent 4 (by norm_num)
    simp only [incKey, tagInc, notE, cv, List.getD_cons_succ, List.getD_cons_zero, CoeffExpr.eval] at e0 e1 e2 e3 e4
    have ha4 : a4 = 4 := Nock.Jet.ChipJ8.natCast_inj_lt hx4 (by omega) (by exact_mod_cast e4)
    have ha2 : a2 = 2 := Nock.Jet.ChipJ8.natCast_inj_lt hx2 (by omega) (by exact_mod_cast e2)
    have ha3 : a3 = i := by
      rw [hRi.idx, hidx i] at e3
      exact Nock.Jet.ChipJ8.natCast_inj_lt (p := p) hx3 (show (i : ℕ) < p by omega) e3
    subst ha4 ha2 ha3
    rw [hRi.inc] at gInc hconv
    rcases mul_eq_zero.mp gInc with h0 | h1
    · -- conversion row
      have hc1 : e.trace AtomChipHQ.conv = 1 := by rw [hconv, h0, sub_zero]
      rw [hc1] at e0 e1
      rw [hc1, one_mul] at g8a g8b g8c
      have ha0 : a0 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx0 (by omega) (by rw [e0]; simp)
      have ha1 : a1 = p - 1 := by
        have h1' : ((a1 + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [e1]; ring
        rw [ZMod.natCast_eq_zero_iff] at h1'
        obtain ⟨c, hc⟩ := h1'
        rcases c with _ | _ | c
        · omega
        · omega
        · nlinarith
      subst ha0 ha1
      have haL : (r i).aL = 1 := ce (by omega) (by norm_num)
        (by rw [← hRi.aL]; exact (sub_eq_zero.mp g8a).trans Nat.cast_one.symm)
      have hwR : (r i).wR = 0 := ce (by omega) (by norm_num) (by rw [← hRi.wR, g8c, Nat.cast_zero])
      have haR : (r i).aR = B - 1 := by
        apply ce (by omega) (by norm_num [B])
        rw [← hRi.aR, sub_eq_zero.mp g8b, AtomChipHQ.Bf_eq, Nat.cast_sub (by norm_num [B]), Nat.cast_one]
      obtain ⟨hd, -, hv⟩ := AtomChipHQ.conv_sound haL hwR haR
      show ∃ n : ℕ, D (0, p - 1) = some (.atom n) ∧ D (2, i) = some (.atom (n + 1))
      refine ⟨p - 1, hD0 _, ?_⟩
      rw [hDenB _ _ hd (by rw [hv, hpG]; omega), hv, hpG]
    · -- inc row: the antecedent makes the old row a big denoted row
      have hinc : (r i).inc = 1 := ce (by omega) (by norm_num) ((sub_eq_zero.mp h1).trans Nat.cast_one.symm)
      obtain ⟨s8, s9, s11⟩ := s8911 hinc
      have hc0 : e.trace AtomChipHQ.conv = 0 := by rw [hconv, sub_eq_zero.mp h1, sub_self]
      rw [hc0] at e0 e1
      have ha0 : a0 = 2 := Nock.Jet.ChipJ8.natCast_inj_lt hx0 (by omega) (by rw [e0]; norm_num)
      have ha1 : a1 = (r i).idxO := by
        rw [hRi.idxO] at e1
        exact Nock.Jet.ChipJ8.natCast_inj_lt hx1 (by omega) (by rw [e1]; ring)
      subst ha0 ha1
      have hpre' : D (2, (r i).idxO) ≠ none := hpre
      obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hpre'
      obtain ⟨lold, hl0, hb0⟩ := hDenB' _ _ hX
      obtain ⟨lnew, hd, hv⟩ := hchain i hinc lold hl0
      exact ⟨val lold, hDenB _ _ hl0 hb0, by rw [hDenB _ _ hd (by omega), hv]⟩
  · intro _; simp [RecOK]
  · intro _; simp [RecOK]
  · intro _
    have hx7 : a7 < p := hlt a7 (by simp)
    have e7 := hent' 7 (by norm_num) (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have : a7 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx7 (by omega) (by exact_mod_cast e7)
    subst this
    simp [RecOK]

/-- **`RecOKIJ8.atomInc_provOKI` over `SmallU`.** -/
theorem atomInc_provOKIU (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, SmallU (r k))
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, Denotes r j l → p ≤ val l → D (2, j) = some (.atom (val l)))
    (hDenB' : ∀ j X, D (2, j) = some X → ∃ l, Denotes r j l ∧ p ≤ val l)
    (hchain : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (RecOKI D Rg comb) .s (pad8 (atomIncProvs b nodes orbit chals pubs Q)) :=
  provPI_of_forall fun limbA =>
    atomInc_provOKI_limbU hq hsat hR hs hidx limbA hD0 hDenB hDenB' hchain hpG

/-- **`AtomLeavesBJ8.bnd_of_mb` over `SmallU`** (g4 at an exported row, read in ℕ). -/
theorem bnd_of_mbU (hq : 2 ^ 63 < p) (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, SmallU (r k)) (k : Fin n)
    (hmb : (AE k).trace AtomChipHQ.mb = 1) :
    (r k).wR = 0 → (r k).aR = B - 1 ∧ (r k).aL ≠ 0 := by
  intro hw
  have hqF : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hq
  have ce : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → ((x : ℕ) : ZMod p) = y → x = y :=
    fun hx hy e => AtomChipHQ.cast_inj hqF hx hy e
  have hg := AtomServedQ.atom_base δ b hn nodes orbit chals pubs Q hsat k
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have g4a := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR))) (.sub (cv Cell.aR) (.const (AtomChipHQ.Bf - 1))) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g4b := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR)))
      (.sub (.mul (cv Cell.aL) (cv AtomChipHQ.invB)) (.const 1)) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  simp only [notE, cv, CoeffExpr.eval] at g4a g4b
  have hRk := hR k
  obtain ⟨s1, s2, s3, s5, -⟩ := hs k
  rw [hmb, hRk.wR, hw, Nat.cast_zero, sub_zero, one_mul, one_mul] at g4a g4b
  refine ⟨?_, ?_⟩
  · apply ce (by omega) (by norm_num [B])
    rw [← hRk.aR, sub_eq_zero.mp g4a, AtomChipHQ.Bf_eq, Nat.cast_sub (by norm_num [B]), Nat.cast_one]
  · intro h0
    rw [hRk.aL, h0, Nat.cast_zero, zero_mul, zero_sub] at g4b
    exact one_ne_zero (neg_eq_zero.mp g4b)

end Field

end

end Nock.NockVMROM.Thm54.VclL.Handle.ChainUJ8
