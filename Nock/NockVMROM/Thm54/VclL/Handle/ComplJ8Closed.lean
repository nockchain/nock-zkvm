/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Closed.lean

  `complJ8` (`ComplJ8Of`) carries the open obligations `OpenJ8` at `BRun` (families `famsOf`).  The atom-table and
  atom-walk families `famsA` live in a module that imports `ComplJ8Of`, so they cannot
  enter `famsOf` without an import cycle.  This module therefore states the result at
  `BRunA := BOf … (avOf …) (famsOf ++ famsA)` (`famsAll`):
  * `good_mono`: a coin good for a larger family list is good for a smaller one (the bad list only grows); the
    run's traces, message and public data do not depend on the family list, so every `OpenJ8` field proved at
    `BRun` applies at `BRunA` by `exact … χ (good_mono … hχ)`;
  * `obligations_of_fams`: `obligations_of_run` with the family list generalized (`famsOf ⊆ fams`, side
    conditions, pin count `≤ 2^66`);
  * `famsAll_facts`: the side conditions and the pin count `≤ 2^40 + 1 + 15·2^31 ≤ 2^66` of `famsAll`;
  * **`complJ8_closed`**: `complJ8`'s conclusion at `BRunA`, nothing carried; `ε_c` is `BRunA`'s (from `famsAll`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ComplJ8Obligations ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

noncomputable section

section Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **All the run's pole families**: `famsOf` (compute, cell, walk, J) and `famsA` (atom table, atom walk). -/
def famsAll (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length) :
    List (List (BadSpec K)) :=
  famsOf δ b D hF hC ++ famsA δ b D hF hA

/-- **The honest record of the run with every family** (`hF hC hA` derived from the row binder). -/
abbrev BRunA (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) : HonestJ8 p K δ Rg fuel s f r :=
  BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen)
    (avOf δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (acs_pos Rt hgen))
    (famsAll δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen))

/-- **Goodness is antitone in the family list.** -/
theorem good_mono (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) (AV : AVPart p K) {fams fams' : List (List (BadSpec K))}
    (hsub : ∀ L ∈ fams, L ∈ fams') (χ : Coins frameJ8 K)
    (h : (BOf δ b Rt hgen hF hC hA AV fams').Good χ) : (BOf δ b Rt hgen hF hC hA AV fams).Good χ := by
  have h' : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams'),
      χ ∉ e.1 := h
  show ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams), χ ∉ e.1
  intro e he
  apply h'
  simp only [badOf, badList, List.mem_map, List.mem_append, List.mem_flatten] at he ⊢
  obtain ⟨x, hx, rfl⟩ := he
  refine ⟨x, ?_, rfl⟩
  rcases hx with hx | ⟨L, hL, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨L, hsub L hL, hx⟩

/-- `BRunA`-good coins are `BRun`-good. -/
theorem goodA (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (h : (BRunA δ b Rt hgen hpG h31).Good χ) : (BRun δ b Rt hgen hpG h31).Good χ :=
  good_mono δ b Rt hgen _ _ _ _ (fun L hL => List.mem_append_left _ hL) χ h

/-- **The families together**: side conditions, pins only, pin count `≤ 2^66`. -/
theorem famsAll_facts (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hC : 0 < D.cells.length)
    (hA : 0 < D.acs.length) (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) :
    (∀ L ∈ famsAll δ b D hF hC hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsAll δ b D hF hC hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsAll δ b D hF hC hA (K := K)).map nPins).sum ≤ 2 ^ 66 := by
  obtain ⟨o1, p1, c1⟩ := famsOf_facts δ b (K := K) D hF hC h31
  obtain ⟨o2, p2, c2⟩ := famsA_facts δ b (K := K) D hF hA
  have hacs := h31 _ (show D.acs.length ∈ sizesJ8 D by simp [sizesJ8])
  have hnV := h31 _ (show nVOf D ∈ sizesJ8 D by simp [sizesJ8])
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, o2 L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, p2 L h]
  · rw [famsAll, List.map_append, List.sum_append]
    have e : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have e40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
    rw [e] at hacs hnV; rw [e40] at c1; rw [e66]
    omega

/-- **`obligations_of_fams`**: `obligations_of_run` at any family list containing `famsOf`, with its side
conditions and pin count. -/
theorem obligations_of_fams (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t)
    (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) (fams : List (List (BadSpec K)))
    (hsub : ∀ L ∈ famsOf δ b (j8DataOf p Rg Rt hgen) hF hC, L ∈ fams)
    (hOK : ∀ L ∈ fams, ∀ e ∈ L, e.OK) (hpin : ∀ L ∈ fams, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (hcnt : (fams.map nPins).sum ≤ 2 ^ 66)
    (O : OpenJ8 δ b (BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams)) :
    ComplJ8Obligations δ b (BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams) := by
  have hcl : ∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p := fun k v hv =>
    hclA k v (by rw [hv]; simp [Noun.leafList])
  have hreg := regs_called (p := p) Rt hgen
  have hregLeaf : ∀ id ∈ (j8DataOf p Rg Rt hgen).regs, ∀ v ∈ (Nock.Jet.Autogen.compile p (Rt id)).leafList, v < p :=
    ComplJ8RegLeaf.compile_leaves_lt_reg (by omega) Rt _ (fun id hid => (hRt id (hreg id hid)).2.2)
      (fun id hid => hregAx id (hreg id hid))
  have mem : ∀ {L}, L ∈ famsOf δ b (j8DataOf p Rg Rt hgen) hF hC → L ∈ fams := fun h => hsub _ h
  have m0 := mem (L := ComplJ8CompPole.compPoles (K := K) δ (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
      (bfsForest [(j8DataOf p Rg Rt hgen).t]) (bfsForest [(j8DataOf p Rg Rt hgen).t]).length) List.mem_cons_self
  have m1 := mem (L := famCellV δ (j8DataOf p Rg Rt hgen)) (List.mem_cons_of_mem _ List.mem_cons_self)
  have m2 := mem (L := famCellH δ b (j8DataOf p Rg Rt hgen) hC (orbJ8 _ hF))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m3 := mem (L := famWalkV δ (j8DataOf p Rg Rt hgen))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have m4 := mem (L := famWalkH δ (j8DataOf p Rg Rt hgen))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))
  have m5 := mem (L := famJ δ (j8DataOf p Rg Rt hgen))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := compute_group δ b Rt hgen hF hC hA
    (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams hp63 hax hop5 hcl m0
  obtain ⟨n1, n2⟩ := nodes_ok δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams
  obtain ⟨g1, g2, g3⟩ := nodes_group δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams hp63 h31
  obtain ⟨w1, w2⟩ := bad_group δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams hOK hpin
    (fun _ => hcnt)
  exact
    { hH := c1, hpair := c2, hN := c3, hinjX := n1, hadjX := n2,
      htrC := fun χ => htrC_run δ b Rt hgen hF hC hA _ _ χ,
      hpIC := c4, hpS := c5, hpO := c6, hpub := c7, hρ := c8, goodC := c9,
      cellOK := fun χ hχ => cellOK_run δ b Rt hgen hF hC hA _ _ hpG hp63 hleaf m1 m2 χ hχ,
      cellNodes := g1,
      walkOK := fun χ hχ => walkOK_run δ b Rt hgen hF hC hA _ _ hp63 h31 hwalk m3 m4 χ hχ,
      walkNodes := g2,
      jOK := fun χ hχ => jOK_run δ b Rt hgen hF hC hA _ _ hp63 h31 hRt m5 χ hχ,
      atomOK := O.atomOK, atomNodes := g3, awOK := O.awOK, balG := O.balG, balV := O.balV, balF := O.balF,
      stat := stat_run δ b Rt hgen hF hC hA _ _ hp63 hax h31 hleaf hRt,
      claim := fun χ => claim_run δ b Rt hgen hF hC hA _ _ hp63 h31 hclA hleaf hregLeaf χ,
      budget := budget_run δ b Rt hgen hF hC hA _ _ hp63 h31,
      wt := w1,
      staged := staged_run δ b Rt hgen hF hC hA _ _ (stA_run δ b _ hF hA) (stV_run δ b _ hF hA),
      fig := w2 }

/-- **`OpenJ8` at `BRunA`, closed**: `atomOK` and `awOK` are stated at any family list containing theirs;
`balG`, `balV` and `balF` are proved at `BRun` and applied through `goodA`. -/
theorem openJ8_closed (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    OpenJ8 δ b (BRunA δ b Rt hgen hpG h31) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have mA : ∀ {L}, L ∈ famsA δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (acs_pos Rt hgen) →
      L ∈ famsAll δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) :=
    fun h => List.mem_append_right _ h
  exact
    { atomOK := fun χ hχ => atomOK_run δ b Rt hgen hpG _ _ _ _ hax hop5 h31 hclA hRt
        (mA (by simp [famsA])) (mA (by simp [famsA])) (mA (by simp [famsA])) (mA (by simp [famsA]))
        (mA (by simp [famsA])) (mA (by simp [famsA])) χ hχ
      awOK := fun χ hχ => awOK_run δ b Rt hgen _ _ _ _ hp63 h31 hwalkA
        (mA (by simp [famsA])) (mA (by simp [famsA])) χ hχ
      balG := fun χ hχ => ComplJ8OfBalG.balG_closed δ b Rt hgen hpG hax hop5 hRt h31 hwalk
        (ComplJ8OfBalG.hI_run δ b Rt hgen hpG hax hop5 hclA hRt h31)
        (fun χ _ => ComplJ8OfBalG.hA_run δ b Rt hgen hpG hop5 hclA hRt h31 χ)
        (ComplJ8OfBalJ.hJ_run δ b Rt hgen hpG hax hRt h31) χ (goodA δ b Rt hgen hpG h31 χ hχ)
      balV := fun χ hχ => ComplJ8OfBal.balV_closed δ b Rt hgen hpG hax hop5 hclA hRt h31 χ
        (goodA δ b Rt hgen hpG h31 χ hχ)
      balF := fun χ hχ => ComplJ8OfBal.balF_closed δ b Rt hgen hpG hop5 hclA hRt h31 hwalk χ
        (goodA δ b Rt hgen hpG h31 χ hχ) }

open Classical in
/-- **`complJ8_closed`: J-8 general completeness at Goldilocks, nothing carried.**  For every generated run
`hgen` of every program over every registry `Rg` whose called jets are registered in compiled form (`hRt`,
`hregAx`), under the run binders `hax hop5`, the claim binder `hclA`, the leaf binder `hleaf`, the walk-depth
binders `hwalk` (reads) and `hwalkA` (atom reads), and every table `≤ 2^31` rows (`h31`): at the run's honest
record `BRunA` (every pole family), honest acceptance at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the claim
holds, and at `|K| = cK` the figure `ε_c < 2^-120` with a good coin. -/
theorem complJ8_closed (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    let B := BRunA δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ8 B.tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V δ b B.Pb Rg.R (cJ s f r) χ (B.M χ) (B.tr χ) B.rows B.g) := by
  intro B
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨hOK, hpin, hcnt⟩ := famsAll_facts δ b (K := K) (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31)
    (cells_pos Rt hgen) (acs_pos Rt hgen) h31
  have O := obligations_of_fams δ b Rt hgen hpG hp63 hax hop5 hclA hleaf hwalk hRt hregAx h31
    (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) _
    (fun L hL => List.mem_append_left _ hL) hOK hpin hcnt
    (openJ8_closed δ b Rt hgen hpG hax hop5 hclA hwalk hwalkA hRt h31)
  refine ⟨fun χ hχ => ComplJ8.honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ,
    ComplJ8.probJ8_notGood_le δ b B O, O.staged, genX_sound Rg.faithful B.hgen, fun hcK => ?_⟩
  have hrows : ComplJ8.RowsLe31 B.Pb := rowsLe31_of δ b Rt hgen _ _ _ _ _ h31
  have hfig := O.fig hpG hcK hrows
  obtain ⟨χ, hχ⟩ := ComplJ8.exists_good δ b B O (lt_trans hfig (by norm_num))
  exact ⟨hfig, χ, ComplJ8.honest_accepted_J8_of_obligations δ b B O hp63 hax hop5 χ hχ⟩

end Closed

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
