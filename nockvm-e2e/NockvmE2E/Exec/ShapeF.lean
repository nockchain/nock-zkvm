/-
  NockvmE2E/Exec/ShapeF.lean   (Mathlib-side lemmas over a chip family `Fam`)

  `Fam`: the chip-id-dependent data of the exe's shape / chip checks (ids, mandatory ids, preprocessed-column indices, widths, commit rounds, public-table layout,
  expected chip literals).  `shapeOkF F`, `shapeXOkF F`, `chipsOkF F` are `j8ShapeOk`, `j8ShapeXOk`, `chipsOk` with every chip-id list read off `F`;
  `famJ8` recovers J-8 and `j8ShapeOk = shapeOkF famJ8` (etc.) hold by `rfl`.  The `*_of_shape` lemmas of `J8Shape.lean` are re-derived over `shapeOkF F`.
  Additive: no existing file is edited; the exe still calls `j8ShapeOk`.  Ties `tieB (spec id k) lit` per literal are `LitTiesF`.
-/
import NockvmE2E.Exec.J8Shape
import NockvmE2E.Exec.J8ShapeX
import NockvmE2E.Exec.J8Chips

set_option autoImplicit false

namespace NockvmE2E.Exec.ShapeF
open NockvmE2E.Exec NockvmE2E.Exec.VL NockvmE2E.Exec.V NockvmE2E.Exec.Inst NockvmE2E.Exec.Tr
open NockvmE2E.Exec.J8Shape NockvmE2E.Exec.J8Chips

/-- a chip family -/
structure Fam where
  ids : List String                          -- admissible chip ids
  mandatory : List String                    -- ids that must occur
  preIdx : String → Array Nat                -- local preprocessed (kind 1) columns per id
  widthOf : String → Nat                     -- non-public width per id
  colR : String → Nat → Nat                  -- commit round (Merkle block) of local column c
  tabOf : String → Option Nat                -- public-table index of an id
  tabLens : Array Nat                        -- public limbs per table (size = number of tables)
  lits : String → List (Nat × Chip)          -- (numeral, expected verifier chip literal) per id
  pubCap : Nat                               -- cap on the number of public cells (`pubOf.size`)
  pubMode : Nat                              -- the public relation of the family: 0 = J-8 `PE.pubCheck`, 2 = J-9 A `PE.pubCheck9`

/-- `j8ShapeOk` with the chip-id data from `F` -/
def mandatoryOkF (F : Fam) (XI : ExecInst) : Bool :=
  let ids := XI.tabs.toList.map (·.chip.id)
  distinctB ids && ids.all (fun i => F.ids.contains i) && F.mandatory.all ids.contains

def preKindOkF (F : Fam) (XI : ExecInst) : Bool :=
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c =>
    (XI.colKind[t.col0 + c]! == 1) == (F.preIdx t.chip.id).contains c)

def widthOkF (F : Fam) (XI : ExecInst) : Bool := XI.tabs.all (fun t => t.nc - t.npub == F.widthOf t.chip.id)

def shapeOkF (F : Fam) (XI : ExecInst) : Bool :=
  paramsOk XI && tabsOk XI &&
  XI.r == 2 && XI.d == 1 && XI.l == 170 && XI.hShift == 1 && XI.hN == 2 ^ (XI.k + 1) && XI.nD == XI.k + 7 &&
  XI.pubMode == F.pubMode && XI.derived.isEmpty && XI.nCoins.size == 2 && XI.nCoins[0]! + XI.nCoins[1]! == 19 &&
  XI.ppt == pptJ8 && XI.nq % 3 == 0 && layoutShapeOk XI &&
  XI.pre.size == XI.nc && XI.pre.all (fun a => decide (a.size ≤ XI.hN + 1)) &&
  XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) &&
  XI.tabs.all (fun t => chipReadsLtB t.chip (t.nc - t.npub) t.npub 19) &&
  XI.pre.all (·.all fun x => VF.based x.toNat) && VF.based XI.hShift.toNat &&
  XI.tabs.all (fun t => decide (t.hN ≤ XI.hN)) &&
  XI.tabs.all (fun t => decide (t.col0 + t.nc ≤ XI.nc)) &&
  XI.tabs.all (fun t => decide (t.pubBase + t.npub ≤ XI.pubOf.size)) &&
  XI.tabs.all (fun t => decide (t.npub ≤ t.nc)) &&
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c => XI.colKind[t.col0 + c]! == 0 || XI.colKind[t.col0 + c]! == 1) &&
  mandatoryOkF F XI && preKindOkF F XI &&
  orbitOk XI && widthOkF F XI && slotOfOk XI

def blockTabOkF (F : Fam) (XI : ExecInst) : Bool :=
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c => XI.blockOf[t.col0 + c]! == F.colR t.chip.id c)

def layOkF (F : Fam) (XI : ExecInst) : Bool :=
  XI.pubLay.bases.size == F.tabLens.size && XI.pubLay.lens.size == F.tabLens.size && XI.pubLay.present.size == F.tabLens.size &&
  XI.pubLay.lens == F.tabLens &&
  XI.tabs.all (fun t => match F.tabOf t.chip.id with
    | none => false
    | some i => XI.pubLay.present[i]! && XI.pubLay.bases[i]! == t.pubBase && t.npub == F.tabLens[i]!) &&
  (List.range F.tabLens.size).all (fun i => XI.pubLay.present[i]! == XI.tabs.any (fun t => F.tabOf t.chip.id == some i))

def shapeXOkF (F : Fam) (XI : ExecInst) : Bool :=
  XI.nq == 9 && decide (XI.pubOf.size ≤ F.pubCap) && blockTabOkF F XI && layOkF F XI

/-- `expectedOf` of a family -/
def expectedOfF (F : Fam) (id : String) : List (Nat × Chip) := F.lits id

def chipNumeralF (F : Fam) (c : Chip) : Option Nat := ((expectedOfF F c.id).find? fun p => chipEqB c p.2).map (·.1)

def chipsOkF (F : Fam) (XI : ExecInst) : Bool := XI.tabs.all fun t => (chipNumeralF F t.chip).isSome

theorem num_findF (F : Fam) (c : Chip) (k : ℕ) (h : chipNumeralF F c = some k) :
    ∃ lit, (k, lit) ∈ expectedOfF F c.id ∧ chipEqB c lit = true := by
  unfold chipNumeralF at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p.2, by simpa using List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩

/-! ## J-8 -/

def famJ8 : Fam where
  ids := ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"]
  mandatory := ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL"]
  preIdx := preIdxJ8
  widthOf := wJ8
  colR := colRB
  tabOf := PE.tabOfId
  tabLens := PE.tabLens
  lits := expectedOf
  pubCap := 926
  pubMode := 0

theorem mandatoryOk_famJ8 : mandatoryOkF famJ8 = mandatoryOk := rfl
theorem preKindOk_famJ8 : preKindOkF famJ8 = preKindOk := rfl
theorem widthOk_famJ8 : widthOkF famJ8 = widthOk := rfl
theorem blockTabOk_famJ8 : blockTabOkF famJ8 = blockTabOk := rfl
theorem layOk_famJ8 : layOkF famJ8 = layOk := rfl
/-- `j8ShapeOk = shapeOkF famJ8` (definitional) -/
theorem j8ShapeOk_eq : j8ShapeOk = shapeOkF famJ8 := rfl
theorem j8ShapeXOk_eq : j8ShapeXOk = shapeXOkF famJ8 := rfl
theorem expectedOf_eq : expectedOf = expectedOfF famJ8 := rfl
theorem chipNumeral_eq : chipNumeral = chipNumeralF famJ8 := rfl
theorem chipsOk_eq : chipsOk = chipsOkF famJ8 := rfl

/-! ## the `*_of_shape` lemmas over `shapeOkF F` -/

section lemmas
variable {F : Fam} {XI : ExecInst}

theorem paramsOk_of_shapeF (h : shapeOkF F XI = true) : paramsOk XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem tabsOk_of_shapeF (h : shapeOkF F XI = true) : tabsOk XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem hn32_of_shapeF (h : shapeOkF F XI = true) : XI.nD ≤ 32 := nD_le_of_paramsOk XI (paramsOk_of_shapeF h)

theorem domLink_of_shapeF (h : shapeOkF F XI = true) : DomLink XI (hn32_of_shapeF h) :=
  domLink_of_paramsOk XI (paramsOk_of_shapeF h) _

theorem hn1_of_shapeF (h : shapeOkF F XI = true) : 1 ≤ XI.nD := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; omega

theorem hl_of_shapeF (h : shapeOkF F XI = true) : XI.l = 170 := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem hmode_of_shapeF (h : shapeOkF F XI = true) : XI.pubMode = F.pubMode := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem d_of_shapeF (h : shapeOkF F XI = true) : XI.d = 1 := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem r_of_shapeF (h : shapeOkF F XI = true) : XI.r = 2 := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem hN_of_shapeF (h : shapeOkF F XI = true) : XI.hN = 2 ^ (XI.k + 1) := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem hpd_of_shapeF (h : shapeOkF F XI = true) : ∀ c < XI.nc, XI.pre[c]!.size ≤ XI.hN + 1 := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hs, hall, _⟩ := (by tauto : _ ∧ XI.pre.size = XI.nc ∧ (∀ i (hi : i < XI.pre.size), XI.pre[i].size ≤ XI.hN + 1) ∧ _)
  intro c hc
  have hc' : c < XI.pre.size := by omega
  rw [getElem!_pos XI.pre c hc']
  exact hall c hc'

theorem chips_no63_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs, chipNo63 t.chip = true := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) = true) t (Array.mem_def.mp ht)
  exact ((Bool.and_eq_true _ _).mp this).2

theorem coins19_of_shapeF (h : shapeOkF F XI = true) : XI.nCoins[0]! + XI.nCoins[1]! = 19 := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; tauto

theorem derived_of_shapeF (h : shapeOkF F XI = true) : XI.derived = #[] := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  have h1 : XI.derived.isEmpty = true := by tauto
  exact Array.isEmpty_iff.mp h1

theorem orbitOk_of_shapeF (h : shapeOkF F XI = true) : orbitOk XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem widthOk_of_shapeF (h : shapeOkF F XI = true) : widthOkF F XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem slotOfOk_of_shapeF (h : shapeOkF F XI = true) : slotOfOk XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem mandatoryOk_of_shapeF (h : shapeOkF F XI = true) : mandatoryOkF F XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

theorem preKindOk_of_shapeF (h : shapeOkF F XI = true) : preKindOkF F XI = true := by
  unfold shapeOkF at h; simp only [Bool.and_eq_true] at h; tauto

/-- `widthOk` per table: `nc - npub = F.widthOf id` -/
theorem width_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, t.nc - t.npub = F.widthOf t.chip.id := by
  intro t ht
  have := tabs_all_mem (by have := widthOk_of_shapeF h; unfold widthOkF at this; exact this) t ht
  simpa using this

theorem slotOf_of_shapeF (h : shapeOkF F XI = true) : XI.slotOf = slotOfJ8 ∧ XI.nCoins = #[13, 6] := by
  have := slotOfOk_of_shapeF h
  unfold slotOfOk at this
  simpa using this

/-- the trace-domain generator has order exactly `3·2^(k+1)` -/
theorem orbit_order_of_shapeF (h : shapeOkF F XI = true) : orderOf (zv XI.hGen) = 3 * 2 ^ (XI.k + 1) := by
  have ho := orbitOk_of_shapeF h
  unfold orbitOk at ho
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ho
  obtain ⟨⟨h1, h2⟩, h3⟩ := ho
  have e1 : zv XI.hGen ^ (3 * 2 ^ (XI.k + 1)) = 1 := by rw [← zv_pow, h1]; rfl
  have e2 : zv XI.hGen ^ (2 ^ (XI.k + 1)) ≠ 1 := by
    intro e; apply h2; rw [← zv_pow] at e
    exact zv_inj_canon (Inst.canon_pow _ _) Gold.one_lt e
  have e3 : zv XI.hGen ^ (3 * 2 ^ XI.k) ≠ 1 := by
    intro e; apply h3; rw [← zv_pow] at e
    exact zv_inj_canon (Inst.canon_pow _ _) Gold.one_lt e
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity) e1
  intro q hq hdvd
  have hq2 : q = 2 ∨ q = 3 := by
    have hd : q ∣ 3 * 2 ^ (XI.k + 1) := hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  rcases hq2 with rfl | rfl
  · have : 3 * 2 ^ (XI.k + 1) / 2 = 3 * 2 ^ XI.k := by rw [pow_succ]; omega
    rw [this]; exact e3
  · have : 3 * 2 ^ (XI.k + 1) / 3 = 2 ^ (XI.k + 1) := by omega
    rw [this]; exact e2

/-! ### the `hdagU_of_tie` instance hypotheses -/

theorem hread_of_shapeF (h : shapeOkF F XI = true) :
    ∀ t ∈ XI.tabs.toList, DagSem.chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  rw [← chipReadsLtB_eq]
  exact tabs_all_mem (by tauto : XI.tabs.all (fun t => chipReadsLtB t.chip (t.nc - t.npub) t.npub 19) = true) t ht

theorem hcanon_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, chipCanon t.chip = true := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => chipCanon t.chip && chipNo63 t.chip) = true) t ht
  exact ((Bool.and_eq_true _ _).mp this).1

theorem hpreC_of_shapeF (h : shapeOkF F XI = true) : ∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  have h1 : XI.pre.all (·.all fun x => VF.based x.toNat) = true := by tauto
  intro c x hx
  apply HdagU.canon_of_based
  by_cases hc : c < XI.pre.size
  · rw [getElem!_pos XI.pre c hc] at hx
    exact Array.all_eq_true_iff_forall_mem.mp (Array.all_eq_true_iff_forall_mem.mp h1 _ (Array.getElem_mem hc)) x (Array.mem_def.mpr hx)
  · rw [getElem!_neg XI.pre c hc] at hx
    exact absurd hx (by simp [default]; intro h; exact List.not_mem_nil (Array.mem_def.mp h))

theorem hS_of_shapeF (h : shapeOkF F XI = true) : canon XI.hShift := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  exact HdagU.canon_of_based _ (by tauto)

theorem hle_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, t.hN ≤ XI.hN := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.hN ≤ XI.hN)) = true) t ht

theorem hcolB_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, t.col0 + t.nc ≤ XI.nc := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.col0 + t.nc ≤ XI.nc)) = true) t ht

theorem hpubB_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, t.pubBase + t.npub ≤ XI.pubOf.size := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.pubBase + t.npub ≤ XI.pubOf.size)) = true) t ht

theorem hnpub_of_shapeF (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, t.npub ≤ t.nc := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t ht
  simpa using tabs_all_mem (by tauto : XI.tabs.all (fun t => decide (t.npub ≤ t.nc)) = true) t ht

theorem hkind_of_shapeF (h : shapeOkF F XI = true) : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
    XI.colKind[XI.tabs[t].col0 + c]! = 0 ∨ XI.colKind[XI.tabs[t].col0 + c]! = 1 := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true] at h
  intro t c hc
  have := tabs_all_mem (by tauto : XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c =>
    XI.colKind[t.col0 + c]! == 0 || XI.colKind[t.col0 + c]! == 1) = true) XI.tabs[t] (Array.getElem_mem_toList t.2)
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at this
  exact this c hc

/-- the ten instance hypotheses of `HdagU.hdagU_of_tie` from `shapeOkF F XI = true` -/
theorem hdagU_shape_of_F (h : shapeOkF F XI = true) :
    (∀ t ∈ XI.tabs.toList, DagSem.chipReadsLt t.chip (t.nc - t.npub) t.npub 19 = true) ∧
    (∀ t ∈ XI.tabs.toList, chipCanon t.chip = true) ∧
    (∀ c : ℕ, ∀ x ∈ XI.pre[c]!.toList, canon x) ∧
    canon XI.hShift ∧
    (∀ t ∈ XI.tabs.toList, t.hN ≤ XI.hN) ∧
    (∀ t ∈ XI.tabs.toList, t.col0 + t.nc ≤ XI.nc) ∧
    (∀ t ∈ XI.tabs.toList, t.pubBase + t.npub ≤ XI.pubOf.size) ∧
    (∀ t ∈ XI.tabs.toList, t.npub ≤ t.nc) ∧
    (∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 0 ∨ XI.colKind[XI.tabs[t].col0 + c]! = 1) ∧
    XI.r = 2 :=
  ⟨hread_of_shapeF h, hcanon_of_shapeF h, hpreC_of_shapeF h, hS_of_shapeF h, hle_of_shapeF h, hcolB_of_shapeF h, hpubB_of_shapeF h,
   hnpub_of_shapeF h, hkind_of_shapeF h, r_of_shapeF h⟩

end lemmas

/-! ## J-8 non-vacuity: the toy instance is `shapeOkF famJ8`-shaped, and the lemmas fire -/

theorem toyShapeF_ok : shapeOkF famJ8 toyShape4 = true := toyShape_ok

theorem toyShapeF_domLink : DomLink toyShape4 (hn32_of_shapeF toyShapeF_ok) := domLink_of_shapeF toyShapeF_ok

theorem toyShapeF_orbit : orderOf (zv toyShape4.hGen) = 3 * 2 ^ (toyShape4.k + 1) := orbit_order_of_shapeF toyShapeF_ok

set_option linter.defProp false in
def toyShapeF_hdagU := hdagU_shape_of_F toyShapeF_ok

end NockvmE2E.Exec.ShapeF

#print axioms NockvmE2E.Exec.ShapeF.j8ShapeOk_eq
#print axioms NockvmE2E.Exec.ShapeF.j8ShapeXOk_eq
#print axioms NockvmE2E.Exec.ShapeF.chipsOk_eq
#print axioms NockvmE2E.Exec.ShapeF.num_findF
#print axioms NockvmE2E.Exec.ShapeF.domLink_of_shapeF
#print axioms NockvmE2E.Exec.ShapeF.hpd_of_shapeF
#print axioms NockvmE2E.Exec.ShapeF.orbit_order_of_shapeF
#print axioms NockvmE2E.Exec.ShapeF.width_of_shapeF
#print axioms NockvmE2E.Exec.ShapeF.hdagU_shape_of_F
#print axioms NockvmE2E.Exec.ShapeF.toyShapeF_ok
#print axioms NockvmE2E.Exec.ShapeF.toyShapeF_domLink
#print axioms NockvmE2E.Exec.ShapeF.toyShapeF_orbit
