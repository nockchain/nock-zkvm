/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/CtxBuildAL.lean

  **The `AluSZOps` context `Ctx` of an accepted ALU chip.**

  * `rank0_vp` (generic cell chip): a claim-shaped consumer `claimVec e v 0 0` of the two-provider cell validity
    balance with rank `(0, 0)` is an EXTERNAL key (`(e, 0, 0, v) ∈ vp`): `PinJ8.regClaims_provided` at one record,
    and no cell row provides rank `(0, 0)` (`cell_key_rank_pos`).
  * `valKey_mem`: an ALU row with `aV = 1` puts its validity read `[z, 0, L, 0, sv]` (as `claimVec (atomFP z L) sv 0 0`)
    in `aluFpReqsOf`.
  * `readOK_rStar`: `ReadOK` at the J-9 A reader `rA` moves to the padded reader `rStar rA nA` (`AluSZOps` gap (ii)).
  * **`ctxAL`**: the `AluSZOps` context over the window `rowsAL` (`AluSZOps.rowsOf` at `chalsALJ8`, `y = (χ_{cY1}, χ_{cY2})`)
    with `al = alR`, `t = RR49AL.atomAL r Pb tr`, `r = rStar rA nA`; `walk` is `AtomWalkAL.walk_rStar`, `read` is
    `AluSZOps.readOK_of_served` at the empty cell table (the served key is external, `rank0_vp`), moved to `rStar`.
  * **`hsemAL`**: `CtxAL.hsem_of_ctx` at `ctxAL` (the `hsem` input of `AluShareAL.jetProv_ok`).
-/
import Nock.Jet.PinJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CtxAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CtxBuildAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (Rows Readout Ctx ALRow ReadOK rowsOf aluEF aluEK eFn eKn eFn_lt
  eKn_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead (Served2)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_y)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (PregOK)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.ComputeTable (FP)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. A rank-`(0, 0)` consumer of the cell validity balance is an external key -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- **A rank-`(0, 0)` claim-shaped consumer is an external key** (`regClaims_provided` at one record; a cell row
never provides rank `(0, 0)`, `cell_key_rank_pos`). -/
theorem rank0_vp [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]
    [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
    (hF : GeneratedField.PrimeFieldElems F)
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 5 → Quad (algebraMap F K δF)))
    (xs : List ((Fin 5 → Quad (algebraMap F K δF)) × Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p)
    (vp : List (VKey (Quad (algebraMap F K δF))))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvpr : ∀ k ∈ vp, k.2.1 < ringChar F ∧ k.2.2.1 < ringChar F ∧ k.2.2.2 < ringChar F)
    (hq : 2 ^ 63 < ringChar F) {z : Quad (algebraMap F K δF)}
    (hrows : ∀ c ∈ cellTableOf δF b nodes orbit chals pubs Q, RowOK z c)
    {e : FP (Quad (algebraMap F K δF))} {v : ℕ} (hmem : ClaimVS.claimVec δF e (v : F) 0 0 ∈ reqs)
    (hv : v < ringChar F) :
    (e, 0, 0, v) ∈ vp := by
  have hprov := Nock.Jet.PinJ8.regClaims_provided δF b hn nodes orbit chals pubs Q hF hsat hbind hinj hadj γ ρ hok
    reqs xs hsum hout hxne hcount vp hx hvpr (regs := [0]) (Ef := fun _ => e) (rk := fun _ => (0, 0))
    (idx := fun _ => v) (fun _ _ => by simpa using hmem) (fun _ _ => ⟨by omega, by omega, hv⟩) 0
    (List.mem_singleton_self 0)
  rcases hprov with ⟨c, hc, heq⟩ | hv'
  · exfalso
    simp only [Prod.mk.injEq] at heq
    exact cell_key_rank_pos hq hrows hc ⟨heq.2.1.symm, heq.2.2.1.symm⟩
  · exact hv'

end Cell

/-! ## 2. The ALU's validity read is a claim-shaped consumer -/

section Key
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (chals pubs : ℕ → K)

local notation "EF" => aluEF b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL (qAL δ b Pb tr chals pubs)
local notation "EK" => aluEK b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL (qAL δ b Pb tr chals pubs)

/-- **The ALU validity read of an `aV = 1` row** is `claimVec (atomFP z L) sv 0 0` in `aluFpReqsOf`. -/
theorem valKey_mem (i : Fin Pb.nL) (h1 : (EF i).trace aV = 1) :
    ClaimVS.claimVec δ (FP.atomFP ((AtomChipHQ.zAt : QE Fp).ev δ (EK i) (EF i)) ((QE.var L : QE Fp).ev δ (EK i) (EF i)))
      ((((EF i).trace sv).val : ℕ) : Fp) 0 0 ∈ aluFpReqsOf δ b Pb tr chals := by
  unfold aluFpReqsOf
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  have h1' : (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i).trace
      aV = 1 := h1
  rw [if_neg (by rw [h1']; exact one_ne_zero)]
  refine List.mem_singleton.mpr ?_
  funext c
  fin_cases c
  · rfl
  · show (0 : Quad (algebraMap Fp K δ)) = _
    simp [valKey, ev_zero]
  · rfl
  · show Quad.mk _ (algebraMap Fp K 0) (algebraMap Fp K 0) = _
    simp [valKey, ev_zero, Quad.mk_zero']
  · show Quad.mk _ (algebraMap Fp K ((((EF i).trace sv).val : ℕ) : Fp)) 0 = _
    simp only [valKey, List.getD_cons_succ, List.getD_cons_zero, Fin.isValue]
    rw [ev_base, ZMod.natCast_zmod_val, Quad.mk_base]
    rfl

end Key

/-! ## 3. `ReadOK` at the padded reader -/

section Pad
variable {K : Type} [Field K] [Algebra Fp K] {δ : Fp} [Fact (¬ IsSquare (algebraMap Fp K δ))]

/-- **`ReadOK` moves from the J-9 A reader `rA` to the padded reader `rStar rA nA`** (`AluSZOps` gap (ii) workaround:
`Ctx.r` is the padded reader).  A read names a big denoted row, which is a table row (`hden2`). -/
theorem readOK_rStar {rA : ℕ → ARow} {nA : ℕ}
    (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (hden2 : ∀ j l, Denotes rA j l → Nock.Atoms.p ≤ Nock.Atoms.val l → j < nA)
    {y Lv : Quad (algebraMap Fp K δ)} {v : ℕ} (h : ReadOK y rA Lv v) : ReadOK y (AtomWalkAL.rStar rA nA) Lv v := by
  obtain ⟨l, hl, hbig, hcan, hL, hext⟩ := h
  have hv := hden2 v l hl hbig
  have hpad : ∀ k, nA ≤ k → ∀ l, Denotes rA k l → Nock.Atoms.val l < Nock.Atoms.p := by
    intro k hk l hl'
    by_contra hc
    have := hden2 k l hl' (by omega)
    omega
  refine ⟨l, AtomWalkAL.denotes_rStar_of hin hl hv, hbig, hcan, hL, ?_⟩
  rw [AtomWalkAL.extB_rStar hin hpad]
  exact hext

end Pad

/-! ## 4. The `AluSZOps` context of an accepted ALU chip -/

section Build
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (χ : Coins frameJ8 K) (pubsL : ℕ → K)

local notation "CHL" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL
local notation "QLL" => qAL δ b Pb tr (chalsALJ8 δ χ) pubsL

/-- **The ALU window** (`AluSZOps.rowsOf` at the ALU challenge vector `chalsALJ8`, limb coin `y = (χ_{cY1}, χ_{cY2})`;
the preg selector is boolean by `PregOK`). -/
def rowsAL (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) : Rows δ K :=
  rowsOf b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL hsat hbind hinj hadj
    (fun i => by rw [(hpre.2 i).1]; split_ifs <;> simp) (Quad.mk _ (χ cY1) (χ cY2)) (chalsALJ8_y δ χ)
    (chalsALJ8_ypow δ χ)

theorem rowsAL_n (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) :
    (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).n = Pb.nL := rfl

theorem rowsAL_y (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) :
    (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).y = Quad.mk _ (χ cY1) (χ cY2) := rfl

theorem rowsAL_eF (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) {i : ℕ} (hi : i < Pb.nL) :
    (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eF i =
      aluEF b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL ⟨i, hi⟩ :=
  eFn_lt _ _ _ _ _ _ _ _ hi

theorem rowsAL_eK (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) {i : ℕ} (hi : i < Pb.nL) :
    (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eK i =
      aluEK b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL ⟨i, hi⟩ :=
  eKn_lt _ _ _ _ _ _ _ _ hi

/-- **The window reads the coin-free ALU rows** (`hvAll` of `CtxAL.hsem_of_ctx`). -/
theorem rowsAL_v (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (i : ℕ) (hi : i < Pb.nL) (j : ℕ) :
    (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).v i j = (alE0 (K := K) δ b Pb tr ⟨i, hi⟩).trace j := by
  show ((rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eF i).trace j = _
  rw [rowsAL_eF δ b Pb tr χ pubsL hsat hbind hinj hadj hpre hi]; rfl

end Build

section Ctx
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] {δ : Fp}
  [Fact (¬ IsSquare (algebraMap Fp K δ))] {b : Basis (Fin 3) Fp K}
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K] [Algebra Fp (Quad (algebraMap Fp K δ))]
  [Algebra (ZMod (ringChar Fp)) (Quad (algebraMap Fp K δ))]
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {χ : Coins frameJ8 K} {pubsL : ℕ → K}

local notation "CHL" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL
local notation "QLL" => qAL δ b Pb tr (chalsALJ8 δ χ) pubsL

variable {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → Fp} {orbitA : StrictOrbitDomain Fp 3 hA} {pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).rap.w → Fp[X]}

/-- **The `AluSZOps` context of the ALU window** (see the module header).  Atom side: the hypotheses of
`AluSZOps.readOK_of_served` at the reader `rA` (its `hserved` is discharged at the EMPTY cell table, because the
served key is an external atom-table key: `hvp`, from `rank0_vp`), child serials in range (`hin`), big denoted rows
are table rows (`hden2`), the round-0 table reads `rA` (`hrow`, `hlen`).

**`AluSZOps` gap (ii) workaround** (`AtomWalkAL`): `Ctx.r` is the padded reader `rStar rA nA`, not `rA`; `Ctx.walk` is
false at `rA` past the table. -/
def ctxAL (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (r : RowsJ9AL)
    (hsatA : (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).rap.Satisfies QA)
    (hbindA : (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnpA : nA < Nock.Atoms.p) (hyA : Quad.mk (algebraMap Fp K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA (chalsAJ8Z δ χ) pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA QA)))
    {rA : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (aEF b nodesA orbitA (chalsAJ8Z δ χ) pubsA QA k) (rA k))
    (hs : ∀ k : Fin nA, SmallU (rA k)) (hidx : ∀ k : Fin nA, (rA k).idx = k) (hB : LimbsBounded rA)
    (hwR : ∀ k : Fin nA, (rA k).wR ≤ 1) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    (hin : ∀ j < nA, (rA j).wR = 1 → (rA j).idR < nA)
    (hden2 : ∀ j l, Denotes rA j l → Nock.Atoms.p ≤ Nock.Atoms.val l → j < nA)
    (hrow : AtomWalkAL.RowRead (RR49AL.atomAL r Pb tr) rA nA) (hlen : nA ≤ (RR49AL.atomAL r Pb tr).length)
    (hvp : ∀ (e : FP (Quad (algebraMap Fp K δ))) (v : ℕ),
      ClaimVS.claimVec δ e (v : Fp) 0 0 ∈ aluFpReqsOf δ b Pb tr (chalsALJ8 δ χ) → v < Nock.Atoms.p →
      (e, 0, 0, v) ∈ AcceptsJ8P.mbVp δ b nodesA orbitA (chalsAJ8Z δ χ) pubsA QA) :
    Ctx (rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre) where
  al := CtxAL.alR _
  hal := CtxAL.readout_alR _
  t := RR49AL.atomAL r Pb tr
  r := AtomWalkAL.rStar rA nA
  walk := AtomWalkAL.walk_rStar hrow hlen
  read i hi haV := by
    have hi' : i < Pb.nL := hi
    have h1 : (aluEF b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL ⟨i, hi'⟩).trace aV = 1 := by
      have := haV
      simp only [Rows.v] at this
      rwa [rowsAL_eF δ b Pb tr χ pubsL hsat hbind hinj hadj hpre hi'] at this
    show ReadOK (Quad.mk _ (χ cY1) (χ cY2)) _ ((QE.var L : QE Fp).ev δ
      ((rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eK i)
      ((rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eF i))
      (((rowsAL δ b Pb tr χ pubsL hsat hbind hinj hadj hpre).eF i).trace sv).val
    rw [rowsAL_eF δ b Pb tr χ pubsL hsat hbind hinj hadj hpre hi', rowsAL_eK δ b Pb tr χ pubsL hsat hbind hinj hadj hpre hi']
    have hm := valKey_mem δ b Pb tr (chalsALJ8 δ χ) pubsL ⟨i, hi'⟩ h1
    have hz : (AtomChipHQ.zAt : QE Fp).ev δ
        (aluEK b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL ⟨i, hi'⟩)
        (aluEF b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL QLL ⟨i, hi'⟩) =
        Quad.mk _ (chalsAJ8Z δ χ 37) (chalsAJ8Z δ χ 38) := by
      rw [AtomChipHQ.zAt, ev_chal, AluSumAL.eK_chal δ b Pb tr (chalsALJ8 δ χ) pubsL,
        AluSumAL.eK_chal δ b Pb tr (chalsALJ8 δ χ) pubsL, chalsALJ8_of_lt δ χ (by omega),
        chalsALJ8_of_lt δ χ (by omega)]
    rw [hz] at hm
    have hv := hvp _ _ hm (ZMod.val_lt _)
    refine readOK_rStar hin hden2 (AluSZOps.readOK_of_served hsatA hbindA hinjA hadjA hnpA hyA hservedA hR hs
      hidx hB hwR hTout _ rfl (q := Nock.Atoms.p) (by norm_num [Nock.Atoms.p, Nock.Field.p]) (t := [])
      (zc := 0) (by simp) ?_ (chalsAJ8Z_y δ χ))
    simp only [Served2, expand, vProv, List.map_nil, List.nil_append, List.mem_flatMap, List.mem_map,
      List.mem_replicate]
    exact ⟨_, ⟨_, hv, rfl⟩, one_ne_zero, rfl⟩

end Ctx

end

end Nock.NockVMROM.Thm54.VclL.Handle.CtxBuildAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.CtxBuildAL
#print axioms rank0_vp
#print axioms valKey_mem
#print axioms readOK_rStar
end Axioms
