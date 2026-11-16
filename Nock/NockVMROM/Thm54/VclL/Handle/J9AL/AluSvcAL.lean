/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSvcAL.lean

  **The ALU share `aluPL` of the service step.**

  * `keyX_mem` / `cell3_of_x`: a `hdr` row's export read `keyX (vS, kA, vA, kB, vB)` is in the ALU export reads;
    once the `.x` block is served and its providers meet `RecOK9I`, it is `Cell3 D (1, vS) (kA, vA) (kB, vB)` (the
    `hcell` input of `AluShareAL.jetProv_ok`).
  * `tag_ne76`: an in-chip / other tag `k < 6` is neither the ALU keyRg tag `7` nor the op-record tag `6` (`h7O` of
    `BindAL.hdr_binding`).
  * `hsemAL`: `CtxAL.hsem_of_ctx` at `CtxBuildAL.ctxAL` (the `hsem` input of `jetProv_ok`; both `AluSZOps` workarounds are
    named there).
  * **`aluShare`**: `ProvP (RecOK9I D V Rg combN) .s (aluPL …)` (ALU present): `regProv_ok ++ jetProv_ok`, the
    binding from `hdr_binding`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CtxBuildAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.BindAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSvcAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (keyVecL)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (Ctx opColOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (PregOK pinRgP)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX Cell3)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I recClass pre9_off)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf natKey)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.ComputeTable (FP)
open Nock.Jet.Prim (PrimOp primSem primC primSpec)
open Nock.Atoms (Fp)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Tags -/

/-- A tag `k < 6` is neither `7` nor `6` (in `K`, through `Fp`). -/
theorem tag_ne76 {K : Type} [Field K] [Algebra Fp K] {k : ℕ} (hk : k < 6) :
    algebraMap Fp K ((k : ℕ) : Fp) ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧
      algebraMap Fp K ((k : ℕ) : Fp) ≠ algebraMap Fp K ((6 : ℕ) : Fp) := by
  have hp : 7 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  constructor
  · intro e
    have e' := (algebraMap Fp K).injective e
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp] at e'
    omega
  · intro e
    have e' := (algebraMap Fp K).injective e
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'
    omega

/-- A `0` tag is neither `7` nor `6`. -/
theorem zero_ne76 {K : Type} [Field K] [Algebra Fp K] :
    (0 : K) ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧ (0 : K) ≠ algebraMap Fp K ((6 : ℕ) : Fp) := by
  have h := tag_ne76 (K := K) (k := 0) (by norm_num)
  simpa using h

/-! ## 2. The export read -/

section Export
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp}

local notation "E0" => alE0 (K := K) δ b Pb tr

/-- A `hdr` row's export read is in `aluExportReqsOf`. -/
theorem keyX_mem (i : Fin Pb.nL) (hH : (E0 i).trace sH = 1) :
    keyVecL (K := K) 5 keyXE (E0 i) ∈ aluExportReqsOf (K := K) δ b Pb tr := by
  unfold aluExportReqsOf
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  rw [if_neg (by rw [hH]; exact one_ne_zero)]
  exact List.mem_singleton_self _

/-- **The export `Cell3`** (`hcell` of `jetProv_ok`): a served `.x` read whose providers meet `RecOK9I`. -/
theorem cell3_of_x {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry}
    {provsX : List ((Fin (mOf .x) → K) × K)} {extX : List (Fin (mOf .x) → K)}
    (hsv : ∀ c ∈ extX, c ∈ provsX.map Prod.fst)
    (hXp : ProvP (p := Nock.Atoms.p) (K := K) (RecOK9I D V Rg combN) .x provsX)
    (i : Fin Pb.nL) (hmem : keyVecL (K := K) 5 keyXE (E0 i) ∈ extX) :
    Cell3 D (1, ((E0 i).trace vS).val) (((E0 i).trace kA).val, ((E0 i).trace vA).val)
      (((E0 i).trace kB).val, ((E0 i).trace vB).val) := by
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hsv _ hmem)
  have hk : natKey (p := Nock.Atoms.p) (K := K) (mOf .x)
      [((E0 i).trace vS).val, ((E0 i).trace kA).val, ((E0 i).trace vA).val, ((E0 i).trace kB).val,
        ((E0 i).trace vB).val] = q.1 := by
    rw [hqe]
    funext c
    fin_cases c <;>
      simp [natKey, keyVecL, keyXE, keyXRE, reE, CoeffExpr.eval, cv, ZMod.natCast_zmod_val]
  have hlt : ∀ e ∈ [((E0 i).trace vS).val, ((E0 i).trace kA).val, ((E0 i).trace vA).val, ((E0 i).trace kB).val,
      ((E0 i).trace vB).val], e < Nock.Atoms.p := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ZMod.val_lt _
  have h := hXp q hq _ (by simp [mOf]) hlt hk (pre9_off (by decide))
  have hc0 : recClass ([((E0 i).trace vS).val, ((E0 i).trace kA).val, ((E0 i).trace vA).val,
      ((E0 i).trace kB).val, ((E0 i).trace vB).val], Bal.x) = 0 := rfl
  unfold RecOK9 at h
  rw [hc0, if_neg (by omega), if_neg (by omega)] at h
  exact h

end Export

/-! ## 3. `hsem` from the `AluSZOps` context -/

section Sem
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] {δ : Fp}
  [Fact (¬ IsSquare (algebraMap Fp K δ))] {b : Basis (Fin 3) Fp K}
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K] [Algebra Fp (Quad (algebraMap Fp K δ))]
  [Algebra (ZMod (ringChar Fp)) (Quad (algebraMap Fp K δ))]
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {χ : Coins frameJ8 K} {pubsL : ℕ → K}

local notation "CHL" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL (chalsALJ8 δ χ) pubsL Pb.preL
local notation "QLL" => qAL δ b Pb tr (chalsALJ8 δ χ) pubsL
local notation "E0" => alE0 (K := K) δ b Pb tr

variable {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → Fp} {orbitA : StrictOrbitDomain Fp 3 hA} {pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA (chalsAJ8Z δ χ) pubsA).rap.w → Fp[X]}

/-- **`hsem` of `jetProv_ok` at the J-9 A denotation** (`CtxAL.hsem_of_ctx` at `CtxBuildAL.ctxAL`).
`AluSZOps` gap (i) workaround: the consumed event is `RR49AL.arithAL` (`hχ`), `op_sound6`'s own at the constant readouts
(`CtxAL.event_of_arithAL`).  `AluSZOps` gap (ii) workaround: the context's reader is `rStar rA nA`
(`CtxAL.hden_D` moves its denotations back to `rA`). -/
theorem hsemAL (hsat : (CHL).rap.Satisfies QLL) (hbind : (CHL).BindsPreprocessing QLL)
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
      (e, 0, 0, v) ∈ AcceptsJ8P.mbVp δ b nodesA orbitA (chalsAJ8Z δ χ) pubsA QA)
    (hAL : Pb.nL ≤ r.AL) (hχ : ¬ (RR49AL.arithAL δ b r Pb).mem tr χ) {q : ℕ} (tC : List (CellRowB0 q))
    (V : ℕ → Option ℕ) :
    ∀ i : Fin Pb.nL, (E0 i).trace sH = 1 → ∀ op : PrimOp, op ≠ .dec → (E0 i).trace (opColOf op) = 1 →
      ∃ na nb nc,
        DenJ9A.denJ9A tC Nock.Atoms.p rA V (((E0 i).trace kA).val, ((E0 i).trace vA).val) = some (.atom na) ∧
        DenJ9A.denJ9A tC Nock.Atoms.p rA V (((E0 i).trace kB).val, ((E0 i).trace vB).val) = some (.atom nb) ∧
        DenJ9A.denJ9A tC Nock.Atoms.p rA V (((E0 i).trace kE).val, ((E0 i).trace vE).val) = some (.atom nc) ∧
        primSem op na nb = some nc := by
  have hpad : ∀ k, nA ≤ k → ∀ l, Denotes rA k l → Nock.Atoms.val l < Nock.Atoms.p := by
    intro k hk l hl
    by_contra hc
    have := hden2 k l hl (by omega)
    omega
  exact CtxAL.hsem_of_ctx δ b
    (CtxBuildAL.ctxAL hsat hbind hinj hadj hpre r hsatA hbindA hinjA hadjA hnpA hyA hservedA hR hs hidx hB hwR
      hTout hin hden2 hrow hlen hvp)
    rfl (fun i hi j => CtxBuildAL.rowsAL_v δ b Pb tr χ pubsL hsat hbind hinj hadj hpre i hi j) hAL rfl rfl rfl
    hin hpad rfl hχ tC V

end Sem

/-! ## 4. The ALU share -/

section Share
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp} {chals pubs : ℕ → K}

local notation "CH" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL
local notation "QL" => qAL δ b Pb tr chals pubs
local notation "E0" => alE0 (K := K) δ b Pb tr

/-- **The ALU share of the service step** (ALU present): the `preg` provides (`regProv_ok`) and the jet provides
(`jetProv_ok`, binding from `hdr_binding` over the served keyRg / op consumes and the verifier pins). -/
theorem aluShare (hon : Pb.aluOn = true) (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hpre : PregOK Pb.nodesL Pb.prims Pb.preL) (hndP : (Pb.prims.map Prod.fst).Nodup)
    (hlt : ∀ q ∈ Pb.prims, q.1 < Nock.Atoms.p ∧ Pb.idxP q.1 < Nock.Atoms.p)
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry}
    (hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (primSpec q.2))
    (hpin : ∀ q ∈ Pb.prims, D (1, Pb.idxP q.1) = some (primC q.2))
    {pO : List ((Fin 8 → K) × K)}
    (h7O : ∀ q ∈ pO, q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧
      q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((6 : ℕ) : Fp))
    (hserv : ∀ c ∈ aluRegReqsOf (K := K) δ b Pb tr ++ pinRgP (p := Nock.Atoms.p) (K := K) Pb,
      c ∈ (aluRegProvsOf (K := K) δ b Pb tr ++ pO).map Prod.fst)
    (hcell : ∀ i : Fin Pb.nL, (E0 i).trace sH = 1 →
      Cell3 D (1, ((E0 i).trace vS).val) (((E0 i).trace kA).val, ((E0 i).trace vA).val)
        (((E0 i).trace kB).val, ((E0 i).trace vB).val))
    (hsem : ∀ i : Fin Pb.nL, (E0 i).trace sH = 1 → ∀ op : PrimOp, op ≠ .dec → (E0 i).trace (opColOf op) = 1 →
      ∃ na nb nc, D (((E0 i).trace kA).val, ((E0 i).trace vA).val) = some (.atom na) ∧
        D (((E0 i).trace kB).val, ((E0 i).trace vB).val) = some (.atom nb) ∧
        D (((E0 i).trace kE).val, ((E0 i).trace vE).val) = some (.atom nc) ∧ primSem op na nb = some nc) :
    ProvP (p := Nock.Atoms.p) (K := K) (RecOK9I D V Rg combN) .s (RR49AL.aluPL δ b Pb tr) := by
  rw [RR49AL.aluPL, if_pos hon]
  exact ServiceJ8.provP_append.mpr
    ⟨AluShareAL.regProv_ok δ b (by norm_num [Nock.Atoms.p, Nock.Field.p]) Pb tr,
     AluShareAL.jetProv_ok δ b hsat hlt hPrim hpin
      (BindAL.hdr_binding δ b hsat hbind hpre hndP (fun q hq => (hlt q hq).1) h7O hserv) hcell hsem⟩

end Share

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSvcAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluSvcAL
#print axioms tag_ne76
#print axioms keyX_mem
#print axioms cell3_of_x
#print axioms hsemAL
#print axioms aluShare
end Axioms
