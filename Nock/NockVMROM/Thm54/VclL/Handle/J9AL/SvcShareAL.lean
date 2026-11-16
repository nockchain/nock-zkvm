/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/SvcShareAL.lean

  **The service step `hsvc` of `FinalLGGAL` with the ALU share.**
  * `keyJet7`, `aluPL_tag`, `aluPL_hAw`: an ALU provide's entry `7` is the tag `7` (keyRg), `6` (op record) or `3`
    (keyJet), so nonzero (`hAw` of `SvcAL.provP_service9AL`).
  * `hservAL`, `ne76_of`: the served premise of `BindAL.hdr_binding` from ONE served fact over the J provides and the
    other provides (`ServeAL.served_JAL`), reshuffled to `aluRegProvsOf ++ pO`, `pO` with no tag `7` / `6`.
  * **`axShareAL_svc`**: `ShareJ9A.axShare_svc` with the ALU share `pA` appended to the axis share, at ONE
    denotation `D` (the ALU share's `ProvP` is a fact about that `D`): `SvcAL.provP_service9AL` (axis present) or
    `SvcAL.svc_absentAL` (absent).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSvcAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.SvcAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ServeAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ShareJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SvcShareAL

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (DenOKX9)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (keyVecL)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9 (recOK9I_p)
open Nock.Atoms (Fp)

noncomputable section

/-! ## 1. Tags of the ALU provides -/

section Tags
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K) {Pb : PubJ9AL Nock.Atoms.p} {tr : TrJ9AL Fp}

theorem keyJet7 (e : Env Fp) :
    keyVecL (K := K) 8 AluSZChipJ9.keyJetE e ⟨7, by norm_num⟩ = algebraMap Fp K ((3 : ℕ) : Fp) := by
  simp [keyVecL, AluSZChipJ9.keyJetE, AluSZChipJ9.keyJetRE, AluSZChipJ9.reE, CoeffExpr.eval]

/-- A jet provide of the ALU carries tag `3`. -/
theorem aluJet_tag : ∀ q ∈ aluJetProvsOf (K := K) δ b Pb tr,
    q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((3 : ℕ) : Fp) := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  split_ifs at hi
  · cases hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact keyJet7 _

/-- **An ALU provide's entry `7` is `7`, `6` or `3`.** -/
theorem aluPL_tag : ∀ q ∈ RR49AL.aluPL δ b Pb tr,
    q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((7 : ℕ) : Fp) ∨ q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((6 : ℕ) : Fp) ∨
      q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((3 : ℕ) : Fp) := by
  intro q hq
  unfold RR49AL.aluPL at hq
  split_ifs at hq
  · rcases List.mem_append.mp hq with h | h
    · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp h
      split_ifs at hi
      · cases hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact Or.inl (BindAL.keyRg7 _)
        · exact Or.inr (Or.inl (BindAL.opRec7 _))
    · exact Or.inr (Or.inr (aluJet_tag δ b q h))
  · cases hq

theorem alg_ne_zero {k : ℕ} (h0 : 0 < k) (hk : k < 8) : algebraMap Fp K ((k : ℕ) : Fp) ≠ 0 := by
  intro e
  have e' : ((k : ℕ) : Fp) = 0 := (algebraMap Fp K).injective (e.trans (map_zero _).symm)
  have hp : 8 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  have h1 := congrArg ZMod.val e'
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-- **`hAw` of `provP_service9AL` at the ALU share.** -/
theorem aluPL_hAw : ∀ q ∈ RR49AL.aluPL δ b Pb tr, ∃ c : Fin (mOf .s), 4 ≤ (c : ℕ) ∧ q.1 c ≠ 0 := by
  intro q hq
  have ht := aluPL_tag δ b q hq
  refine ⟨⟨7, by norm_num [mOf]⟩, by norm_num, fun h0 => ?_⟩
  have h7 : q.1 ⟨7, by norm_num⟩ = 0 := h0
  rcases ht with h | h | h <;> rw [h] at h7 <;> exact alg_ne_zero (by norm_num) (by norm_num) h7

/-- A `0` tag or a tag `k < 6` is neither `7` nor `6`. -/
theorem ne76_of {x : K} (h : x = 0 ∨ ∃ k < 6, x = algebraMap Fp K ((k : ℕ) : Fp)) :
    x ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧ x ≠ algebraMap Fp K ((6 : ℕ) : Fp) := by
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact AluSvcAL.zero_ne76
  · exact AluSvcAL.tag_ne76 hk

/-- **The served premise of `hdr_binding`**, from one served fact over `JP ++ (pI ++ pW ++ (pX ++ aluPL) ++ pS)`. -/
theorem hservAL (hon : Pb.aluOn = true) {JP pI pW pX pS : List ((Fin 8 → K) × K)}
    (hsv : ∀ c ∈ aluRegReqsOf (K := K) δ b Pb tr ++ AcceptsJ9AL.pinRgP (p := Nock.Atoms.p) (K := K) Pb,
      c ∈ (JP ++ (pI ++ pW ++ (pX ++ RR49AL.aluPL δ b Pb tr) ++ pS)).map Prod.fst) :
    ∀ c ∈ aluRegReqsOf (K := K) δ b Pb tr ++ AcceptsJ9AL.pinRgP (p := Nock.Atoms.p) (K := K) Pb,
      c ∈ (aluRegProvsOf (K := K) δ b Pb tr ++
        (JP ++ pI ++ pW ++ pX ++ aluJetProvsOf (K := K) δ b Pb tr ++ pS)).map Prod.fst := by
  intro c hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hsv c hc)
  refine List.mem_map_of_mem ?_
  rw [RR49AL.aluPL, if_pos hon] at hq
  simp only [List.mem_append] at hq ⊢
  rcases hq with h | ((h | h) | (h | (h | h))) | h
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr h)

/-- **`h7O` of `hdr_binding`** at `pO = JP ++ pI ++ pW ++ pX ++ aluJet ++ pS`. -/
theorem h7OAL {JP pI pW pX pS : List ((Fin 8 → K) × K)}
    (hJ : ∀ q ∈ JP, ∃ k < 6, q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((k : ℕ) : Fp))
    (hI : ∀ q ∈ pI, q.1 ⟨7, by norm_num⟩ = 0) (hW : ∀ q ∈ pW, q.1 ⟨7, by norm_num⟩ = 0)
    (hX : ∀ q ∈ pX, q.1 ⟨7, by norm_num⟩ = algebraMap Fp K ((5 : ℕ) : Fp))
    (hS : ∀ q ∈ pS, q.1 ⟨7, by norm_num⟩ = 0) :
    ∀ q ∈ JP ++ pI ++ pW ++ pX ++ aluJetProvsOf (K := K) δ b Pb tr ++ pS,
      q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((7 : ℕ) : Fp) ∧
        q.1 ⟨7, by norm_num⟩ ≠ algebraMap Fp K ((6 : ℕ) : Fp) := by
  intro q hq
  refine ne76_of ?_
  simp only [List.mem_append] at hq
  rcases hq with ((((h | h) | h) | h) | h) | h
  · exact Or.inr (hJ q h)
  · exact Or.inl (hI q h)
  · exact Or.inl (hW q h)
  · exact Or.inr ⟨5, by norm_num, hX q h⟩
  · exact Or.inr ⟨3, by norm_num, aluJet_tag δ b q h⟩
  · exact Or.inl (hS q h)

end Tags

/-! ## 2. The service step with the ALU share -/

section Svc
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}

/-- **`ShareJ9A.axShare_svc` with the ALU share `pA`**, at one denotation `D`. -/
theorem axShareAL_svc (hpG : p = Nock.Atoms.p) {axOn : Bool} {hX nX : ℕ} {hnX : 0 < nX}
    {nodesX : Fin nX → ZMod p} {orbitX : StrictOrbitDomain (ZMod p) 3 hX} {chalsX pubsX : ℕ → K}
    {QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X]}
    (hAX : AXChipOK δ b axOn hnX nodesX orbitX chalsX pubsX QX)
    {V : ℕ → Option ℕ} {pI pW pS : List ((Fin 8 → K) × K)} {extS : List (Fin 8 → K)}
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hW : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hsubS : ∀ c ∈ (if axOn then AxisChipJ9.axLimbReqs b nodesX orbitX chalsX pubsX QX else []), c ∈ extS)
    (hsubP : ∀ c ∈ (if axOn then AxisChipJ9.axPathReqs b nodesX orbitX chalsX pubsX QX else []), c ∈ extP)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} (hD : DenOKX9 p D V)
    (hPp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p pP)
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    {pA : List ((Fin 8 → K) × K)} (hA : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pA)
    (hAw : ∀ q ∈ pA, ∃ c : Fin (mOf .s), 4 ≤ (c : ℕ) ∧ q.1 c ≠ 0)
    {pJ : List ((Fin 8 → K) × K)} (hJ : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ)
    (hsvS : ∀ c ∈ extS, c ∈ (pJ ++ pI ++ pW ++
      ((if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []) ++ pA) ++ pS).map Prod.fst)
    (hsvP : ∀ c ∈ extP, c ∈ pP.map Prod.fst) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s
      (pJ ++ pI ++ pW ++ ((if axOn then AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX else []) ++ pA) ++ pS) := by
  rcases hAX with ⟨hon, hsat, hbind, hinj, hadj, -⟩ | ⟨hoff, -⟩
  · subst hon
    simp only [if_true] at hsvS hsubS hsubP ⊢
    have hsubS' : ∀ i : Fin nX,
        AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extS :=
      fun i => hsubS _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have hsubP' : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
        AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extP := by
      intro i hz
      refine hsubP _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
      rw [if_neg (by rw [hz, sub_zero]; exact one_ne_zero)]
      exact List.mem_singleton_self _
    exact SvcAL.provP_service9AL δ b hnX nodesX orbitX chalsX pubsX QX hpG hsat hbind hinj hadj Rg hD hJ hI
      (hW D Rg) (hS D Rg) hA hAw hsvS hsubS' (fun a b' c d hr => recOK9I_p a b' c d hr) hsvP hsubP' hPp
  · subst hoff
    simp only [Bool.false_eq_true, if_false]
    exact SvcAL.svc_absentAL hJ hI (hW D Rg) (hS D Rg) hA

end Svc

end

end Nock.NockVMROM.Thm54.VclL.Handle.SvcShareAL
