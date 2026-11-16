/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHMemSat2.lean

  Copies of `ComplJ9BBalF.awOK_D9` (generic `D`), `ComplJ9ATables.awOK_runA` and `ComplJ9ATables.atomOK_runA` with
  `orbJ8 _ hF` replaced by `o` and `powN_ok …` replaced by the hypotheses. `ComplJ9ATables.atomOK_mbA` is already
  generic in `nodes orbit hinj hadj` (no copy needed). No `n ≤ 2^h` assumption. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (idxRW walkRow0R wRowsBR wValsBR wColBR)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (chalsAZ_0 chalsAZ_1 zA_eq)

noncomputable section

/-! ## 1. The J-9 atom walk at an arbitrary orbit -/

section AWRun9o
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **`ComplJ9BBalF.awOK_D9` at an arbitrary orbit `o` and nodes `powN o (nVOf D)`** (`hinj hadj` instead of `hF`). -/
theorem awOK_D9o (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hp63 : 2 ^ 63 < p)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hA : 0 < D.acs.length)
    (hinj : Function.Injective (powN o (nVOf D)))
    (hadj : ∀ (i : Fin (nVOf D)) (hi : (i : ℕ) + 1 < nVOf D), powN o (nVOf D) ⟨(i : ℕ) + 1, hi⟩ = powN o (nVOf D) i * o.ω)
    (χ : Coins frameJ8 K) (hgV : ∀ e ∈ famAWV9 δ D (K := K), χ ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 δ D (K := K), χ ∉ e.ev) :
    AWChipOK δ b (krVOf D) (nV_pos D) (powN o (nVOf D)) o (chalsAJ8Z δ χ)
      (pubsVOf9 δ b D o χ)
      (fun j => trVOf9 δ b D o χ
        (Fin.cast (CellTwinK.walkChipHQK_width δ (krVOf D) b (nV_pos D) _ _ _ _) j)) := by
  by_cases h0 : D.preads = []
  · refine ComplJ8AW.awOK_absent δ b (krVOf D) (nV_pos D) _ _ _ _ (by simp [krVOf, h0]) _ ?_
    simp [pubsVOf9, h0]
  have hk : krVOf D = krW D.acs D.preads := by simp [krVOf, h0]
  have hN : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, h0]
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hcells : D.acs.length < ringChar (ZMod p) := by
    have := h31 _ hmA; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hkp : krW D.acs D.preads + (walkRows D.acs D.preads).length < ringChar (ZMod p) := by
    have h1 := h31 _ hmV
    have h2 := krW_le_rows D.acs D.preads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; rw [hN] at h1; omega
  have hrows := famAWV9_good δ D χ hgV
  have hpoleH : ∀ (i : Fin (nVOf D)), ∀ x ∈ awHx9 δ D i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hgH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := aw_dRow_split9 δ b D o hinj χ (pubsVOf9 δ b D o χ)
  have hP : ∀ i, pubsVOf9 δ b D o χ i =
      if i < 4 then pubsV09 δ D χ i else if i < 6 then pub2 δ (vhX9 δ b D o χ) i
      else if i < 8 then pub2 δ (vhP9 δ b D o χ) i else 0 := by
    intro i; simp only [pubsVOf9, if_neg h0]
  have hP0 : ∀ i, pubsV09 δ D χ i =
      if i < 2 then pub2 δ (vxT9 δ D χ) i else if i < 4 then pub2 δ (vpT9 δ D χ) i else 0 := by
    intro i; simp only [pubsV09, if_neg h0]
  have qx : ∀ i, i < 2 → pubsVOf9 δ b D o χ i = pub2 δ (vxT9 δ D χ) i := by
    intro i hi; rw [hP, if_pos (show i < 4 by omega), hP0, if_pos hi]
  have qp : ∀ i, 2 ≤ i → i < 4 → pubsVOf9 δ b D o χ i = pub2 δ (vpT9 δ D χ) i := by
    intro i h1 h2; rw [hP, if_pos h2, hP0, if_neg (show ¬ i < 2 by omega), if_pos h2]
  have qhx : ∀ i, 4 ≤ i → i < 6 → pubsVOf9 δ b D o χ i = pub2 δ (vhX9 δ b D o χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_pos h2]
  have qhp : ∀ i, 6 ≤ i → i < 8 → pubsVOf9 δ b D o χ i = pub2 δ (vhP9 δ b D o χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_neg (show ¬ i < 6 by omega), if_pos h2]
  have hres := ComplJ9BAWR.awOK_listR δ b (nV_pos D) (powN o (nVOf D)) o (chalsAJ8Z δ χ)
    (pubsVOf9 δ b D o χ) (encA δ χ) (γV δ χ) (ρV δ χ) D.acs (rIA D) D.preads (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)
    (by rw [hrc]; exact hp63) hcells (rIA_le D hA) hwalkA hkp hN hinj hadj (ChalsAZJ8.chalsAJ8Z_ok δ χ)
    (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).1) (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).2.1)
    (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).2.2)
    (by
      rw [qx 0 (by norm_num), qx 1 (by norm_num), pub2_mk2 δ _ 0 rfl]
      rfl)
    (by
      rw [qp 2 (by norm_num) (by norm_num), qp 3 (by norm_num) (by norm_num), pub2_mk2 δ _ 2 rfl]
      rfl)
    (fun i => hdlA_kind _ _) (fun i => hdlA_kind _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).idx, (kLV9 D i, vLV9 D i),
        (kRV9 D i, vRV9 D i))) (by simp only [awHx9, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre,
        (kLV9 D i, vLV9 D i))) (by simp only [awHx9, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre + 1,
        (kRV9 D i, vRV9 D i))) (by
          simp only [awHx9, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by
      show Quad.mk _ (pubsVOf9 δ b D o χ 4) (pubsVOf9 δ b D o χ 5) = _
      rw [qhx 4 (by norm_num) (by norm_num), qhx 5 (by norm_num) (by norm_num), pub2_mk2 δ _ 4 rfl]
      unfold vhX9
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN9
      rw [hk, aw_dN_pubs9 δ b D o hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D o χ) _ (Or.inl rfl)])
    (by
      show Quad.mk _ (pubsVOf9 δ b D o χ 6) (pubsVOf9 δ b D o χ 7) = _
      rw [qhp 6 (by norm_num) (by norm_num), qhp 7 (by norm_num) (by norm_num), pub2_mk2 δ _ 6 rfl]
      unfold vhP9
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN9
      rw [hk, aw_dN_pubs9 δ b D o hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D o χ) _
          (Or.inr (Or.inl rfl)),
        aw_dN_pubs9 δ b D o hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D o χ) _ (Or.inr (Or.inr rfl))])
  unfold trVOf9
  rw [hk]
  exact hres

end AWRun9o

/-! ## 2. The J-9 A atom walk at `DA`, arbitrary orbit -/

section AwRunAo
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-- **`ComplJ9ATables.awOK_runA` at an arbitrary orbit `o`**: at a coin outside the two atom-walk pole families, the
J-9 atom walk accepts the honest atom-walk trace over the J-9 A atom-walk reads, at nodes `powN o (nVOf DA)`. -/
theorem awOK_runAo {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DA))
    (hax9 : ComplJ9ABinders.ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hinj : Function.Injective (powN o (nVOf (DA))))
    (hadj : ∀ (i : Fin (nVOf (DA))) (hi : (i : ℕ) + 1 < nVOf (DA)),
      powN o (nVOf (DA)) ⟨(i : ℕ) + 1, hi⟩ = powN o (nVOf (DA)) i * o.ω)
    (χ : Coins frameJ8 K) (gV : ∀ e ∈ famAWV9 δ (DA) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAWH9 δ (DA) (K := K), χ ∉ e.ev) :
    AWChipOK δ b (krVOf (DA)) (nV_pos (DA)) (powN o (nVOf (DA))) o (chalsAJ8Z δ χ)
      (pubsVOf9 δ b (DA) o χ)
      (fun j => trVOf9 δ b (DA) o χ
        (Fin.cast (CellTwinK.walkChipHQK_width δ (krVOf (DA)) b (nV_pos (DA)) _ _ _ _) j)) :=
  awOK_D9o δ b (DA) o hp63 h31
    (ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA) (ComplJ9ADataRec.acsA_pos Rt hgen) hinj hadj χ gV gH

end AwRunAo

/-! ## 3. The atom table (both views) at `DA`, arbitrary orbit -/

section AtomRunAo
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-- **`ComplJ9ATables.atomOK_runA` at an arbitrary orbit `o`**: at a coin outside the six atom pole families of `DA`
at `o`, the honest atom trace at `DA` is accepted and bound by `atomChipHQ` and `atomChipHQL`, at nodes
`powN o (DA).acs.length` (`hinj hadj` supplied; no `DvdOK`, no `n ≤ 2^h`). -/
theorem atomOK_runAo (hpG : p = Nock.Atoms.p) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hA : 0 < (DA).acs.length) (h31 : Rows31 (DA))
    (hinj : Function.Injective (powN o (DA).acs.length))
    (hadj : ∀ (i : Fin (DA).acs.length) (hi : (i : ℕ) + 1 < (DA).acs.length),
      powN o (DA).acs.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DA).acs.length i * o.ω)
    (χ : Coins frameJ8 K)
    (gZ : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) (gV : ∀ e ∈ famAV δ (DA) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAH δ b (DA) hA o (K := K), χ ∉ e.ev)
    (gMB : ∀ e ∈ famMB δ b (DA) hA o (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b (DA) hA o (K := K), χ ∉ e.ev)
    (gMI : ∀ e ∈ famMI δ b (DA) hA o (K := K), χ ∉ e.ev) :
    let P := pubsAOf δ b (DA) hA o χ
    let tr := HonestA8.atomTraceHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (DA) hA o χ P)
      (newBA (DA))
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies tr ∧
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing tr ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) := by
  intro P tr
  subst hpG
  have hz := famAZ_good δ χ gZ
  have hv := famAV_good δ (j9aDataOf Nock.Atoms.p Rg Rt hgen) χ gV
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ gH gMB gC gMI P
  have hmA : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf Nock.Atoms.p Rg Rt hgen) := by
    simp [sizesJ8]
  have hmA9 : (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j9aDataOf Nock.Atoms.p Rg Rt hgen) := by simp [sizesJ8]
  have hN := rows_leA Rg Rt hgen h31
  obtain ⟨hcell, hrank, htl⟩ := acs_okA Rg Rt hgen hN (h31 _ hmA9)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN o _) o (chalsAJ8Z δ χ) P (γV δ χ) (ρV δ χ)
    (zA δ χ) (fun _ => none) (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _) hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      colAH δ b _ hA o χ P Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs
            (j9aDataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ P i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  exact atomOK_mbA δ b Rg Rt hgen hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ P)
    (ComplJ9BAtom.mbX (j8DataOf Nock.Atoms.p Rg Rt hgen) [s, f, r]) (genHyp_mbXA Rg Rt hgen hN) hinj hadj hcol hsat0
    hpMB hpC hpMI tMB tC tMI

end AtomRunAo

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2
#print axioms awOK_D9o
#print axioms awOK_runAo
#print axioms atomOK_runAo
end Axioms
