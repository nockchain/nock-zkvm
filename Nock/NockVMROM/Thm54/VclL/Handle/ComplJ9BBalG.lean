/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BBalG.lean

* §1 `hI`: the inc data `hI` reads, stated over an ABSTRACT `info` (`IncInfoOK`: `mi` per target row, `conv` at
    `rootIdxP p`, target rows inc); `stepF9` / `fold9` / `incInfoOK_infoOfP` prove it for the current `infoOfP` at
    any limb count (`incChain_conv_mi`, `incChain_inc`; no single-step chain assumed, `mhx` not read).
    `incSum_eq9` (generic data record, any `mb`) and `hI9` (the run's data up to `mb` / `info`, every coin and orbit)
    from binders `hpG hax hop5`, `hinfo : IncInfoOK …` and `hidxO : IdxOOK D` (the old-row column at the depth-0
    rows keys `rootIdxP p acs v`; GLA's fix (B)).  `idxOOK_tab` gives `IdxOOK` for the CURRENT `tabOf` under the
    TEMPORARY `HincDup` (the comb(p) duplicate: the current generator's inc row for `p → p + 1` records the FIRST
    copy of `comb p`, the compute the LAST; `HincDup` is used there only), hence `hI9_mb`.
  * §2 `hA` compute half: `recsA_chP` (every AW record of a comb is the pointer handle `chPP` of its slot, any limb
    count; `recsA_hdl`, the `Gen.hdl` version, is kept but unused), `combFD_mem`, `pair_facts9`, `awT_run9`, `awSum9`
    (the pair consumes total `Σ_{x ∈ preads} WA9 x`, root at `rIAP`, leaf at `chPP p D.acs D.rows`; body = GLB's `ComplJ9BBalF.WA9`) and `hA9`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

section IncFold9
open Nock.V1J8.Gen (AInfo idxOf combOf spineOf incChain)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (stepF fuelOf getD_modify size_incChain incChain_inc
  incChain_conv_mi Reach)
variable (p : ℕ) (acsL : List Noun) (rows : Array RowNX)

/-- **The inc data an `hI` proof reads** (abstract `info`, any limb count): `mi` sums the counts of the operands
targeting the row; `conv` marks `rootIdxP p` for a conversion operand; the target row of a non-conversion operand is
an inc row. -/
def IncInfoOK (ops : List (ℕ × ℕ)) (info : Array AInfo) : Prop :=
  (∀ k < acsL.length, (info.getD k AInfo.z).mi =
      ((ops.filter fun vc => ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k).map Prod.snd).sum) ∧
  (∀ k < acsL.length, ((info.getD k AInfo.z).conv = true ↔
      ∃ vc ∈ ops, vc.1 + 1 = p ∧ ComplJ8Data.rootIdxP p acsL p = k)) ∧
  (∀ vc ∈ ops, vc.1 + 1 ≠ p → idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))) < acsL.length →
      (info.getD (idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1)))) AInfo.z).inc = true)

theorem stepF9 (a : Array AInfo) (vc : ℕ × ℕ) :
    (stepF p acsL rows a vc).size = a.size ∧
    (∀ k < a.size, ((stepF p acsL rows a vc).getD k AInfo.z).mi = (a.getD k AInfo.z).mi +
      (if ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k then vc.2 else 0)) ∧
    (∀ k < a.size, (((stepF p acsL rows a vc).getD k AInfo.z).conv = true ↔ (a.getD k AInfo.z).conv = true ∨
      (vc.1 + 1 = p ∧ ComplJ8Data.rootIdxP p acsL p = k))) ∧
    (∀ k, (a.getD k AInfo.z).inc = true → ((stepF p acsL rows a vc).getD k AInfo.z).inc = true) ∧
    (vc.1 + 1 ≠ p → 2 ≤ (Nock.Atoms.limbs vc.1).length → 2 ≤ (Nock.Atoms.limbs (vc.1 + 1)).length →
      idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))) < a.size →
      ((stepF p acsL rows a vc).getD (idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1)))) AInfo.z).inc = true) := by
  by_cases hp : vc.1 + 1 = p
  · simp only [stepF, if_pos hp]
    refine ⟨by simp, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun h => absurd hp h⟩
    · rw [getD_modify, hp]; split_ifs <;> simp_all
    · rw [getD_modify]; split_ifs <;> simp_all
    · rw [getD_modify]; split_ifs <;> simp_all
  · simp only [stepF, if_neg hp]
    have hs1 := size_incChain (rows := rows) p acsL (fuelOf vc.1) (spineOf (Nock.Atoms.limbs (vc.1 + 1)))
      (spineOf (Nock.Atoms.limbs vc.1)) a
    have cm := fun k => incChain_conv_mi (rows := rows) p acsL (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) a k
    have hin := fun k => incChain_inc (rows := rows) p acsL (fuelOf vc.1) (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) a k
    have e1 : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).inc = x.inc :=
      fun c _ x => by split_ifs <;> rfl
    have e2 : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).conv = x.conv :=
      fun c _ x => by split_ifs <;> rfl
    refine ⟨by simp [hs1], fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ h1 h2 ht => ?_⟩
    · rw [getD_modify, hs1]
      by_cases hq : ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k
      · rw [if_pos ⟨hq, hk⟩, if_pos hq, (cm k).2]
      · rw [if_neg (fun h => hq h.1), if_neg hq, (cm k).2]; simp
    · rw [getD_modify, e2, (cm k).1]; simp [hp]
    · rw [getD_modify, e1]; exact (hin k).mpr (Or.inl hk)
    · rw [getD_modify, e1]
      refine (hin _).mpr (Or.inr ⟨ht, 0, ⟨by simp [fuelOf], by simpa using h2, by simpa using h1,
        fun i hi => by omega⟩, by simp⟩)

theorem fold9 : ∀ (l : List (ℕ × ℕ)) (a : Array AInfo),
    (l.foldl (stepF p acsL rows) a).size = a.size ∧
    (∀ k < a.size, ((l.foldl (stepF p acsL rows) a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi +
        ((l.filter fun vc => ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k).map Prod.snd).sum) ∧
    (∀ k < a.size, (((l.foldl (stepF p acsL rows) a).getD k AInfo.z).conv = true ↔ (a.getD k AInfo.z).conv = true ∨
        ∃ vc ∈ l, vc.1 + 1 = p ∧ ComplJ8Data.rootIdxP p acsL p = k)) ∧
    (∀ k, (a.getD k AInfo.z).inc = true → ((l.foldl (stepF p acsL rows) a).getD k AInfo.z).inc = true) ∧
    (∀ vc ∈ l, vc.1 + 1 ≠ p → 2 ≤ (Nock.Atoms.limbs vc.1).length → 2 ≤ (Nock.Atoms.limbs (vc.1 + 1)).length →
      idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))) < a.size →
      ((l.foldl (stepF p acsL rows) a).getD (idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1)))) AInfo.z).inc = true)
  | [], a => ⟨rfl, fun k _ => by simp, fun k _ => by simp, fun k h => h, fun vc h => by simp at h⟩
  | vc :: l, a => by
    obtain ⟨s1, s2, s3, s4, s5⟩ := stepF9 p acsL rows a vc
    obtain ⟨i1, i2, i3, i4, i5⟩ := fold9 l (stepF p acsL rows a vc)
    simp only [List.foldl_cons]
    refine ⟨i1.trans s1, fun k hk => ?_, fun k hk => ?_, fun k hk => i4 k (s4 k hk), fun w hw hp h1 h2 ht => ?_⟩
    · rw [i2 k (s1 ▸ hk), s2 k hk, List.filter_cons]
      by_cases hq : ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k
      · simp only [hq, if_true, decide_true, List.map_cons, List.sum_cons]; ring
      · simp [hq]
    · rw [i3 k (s1 ▸ hk), s3 k hk]
      constructor
      · rintro ((h1 | ⟨h1, h3⟩) | ⟨w, hw, h1, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨vc, List.mem_cons_self, h1, h3⟩
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h1, h3⟩
      · rintro (h1 | ⟨w, hw, h1, h3⟩)
        · exact Or.inl (Or.inl h1)
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact Or.inl (Or.inr ⟨h1, h3⟩)
          · exact Or.inr ⟨w, hw, h1, h3⟩
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact i4 _ (s5 hp h1 h2 ht)
      · exact i5 w hw hp h1 h2 (s1 ▸ ht)

/-- **`infoOfP` meets `IncInfoOK` at any limb count** (the non-conversion operands are big, two or more limbs). -/
theorem incInfoOK_infoOfP
    (hl : ∀ vc ∈ ComplJ8Data.incOpsP p rows, vc.1 + 1 ≠ p →
      2 ≤ (Nock.Atoms.limbs vc.1).length ∧ 2 ≤ (Nock.Atoms.limbs (vc.1 + 1)).length) :
    IncInfoOK p acsL (ComplJ8Data.incOpsP p rows) (ComplJ8Data.infoOfP p acsL rows) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := fold9 p acsL rows (ComplJ8Data.incOpsP p rows) (Array.replicate acsL.length AInfo.z)
  have hz : ∀ k < acsL.length, (Array.replicate acsL.length AInfo.z).getD k AInfo.z = AInfo.z := by
    intro k hk; simp [Array.getD_eq_getD_getElem?, hk]
  -- GLA patch (fixes (A), (B)): the fold sits under the post-pass and `recountMhx`, which keep `mi`, `conv`, `inc`.
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun vc hvc hp ht => ?_⟩
  · rw [(ComplJ8Atom.info_fields _ _ _ k).2.2.2.2.2.2]; unfold ComplJ8Atom.infoFold
    rw [h2 k (by simpa using hk), hz k hk]; simp [AInfo.z]
  · rw [(ComplJ8Atom.info_fields _ _ _ k).2.1]; unfold ComplJ8Atom.infoFold
    rw [h3 k (by simpa using hk), hz k hk]; simp [AInfo.z]
  · rw [(ComplJ8Atom.info_fields _ _ _ _).1]; unfold ComplJ8Atom.infoFold
    exact h5 vc hvc hp (hl vc hvc hp).1 (hl vc hvc hp).2 (by simpa using ht)

end IncFold9

section IncAtomSum9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom table's inc old-row column at the depth-0 rows** (abstract; GLA's fix (B) supplies it): the target
row `idxOf (comb (v + 1))` of a non-conversion operand `v` keys `v`'s root serial `rootIdxP p acs v` (the compute
handle of `v`).  Depth `≥ 1` rows are not read by `hI`. -/
def IdxOOK (D : J8Data p Rg fuel s f r) : Prop :=
  ∀ vc ∈ ComplJ8Data.incOpsP p D.rows, vc.1 + 1 ≠ p →
    ∀ hk : Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (vc.1 + 1))) < D.acs.length,
      newBA D AtomChipHQ.idxO ⟨_, hk⟩ = ((ComplJ8Data.rootIdxP p D.acs vc.1 : ℕ) : ZMod p)

/-- **TEMPORARY hypothesis (the comb(p) duplicate, GLC finding 1; to be retired by GLA's fix (B))**: if `p` itself
is a slow-OP4 operand, the first and last rows of `comb p` coincide.  The CURRENT generator's inc row for
`p → p + 1` records its old row at the FIRST copy of `comb p` (`idxOf`), while the compute's inc record uses
`H p = (2, lastIdxOf (comb p))`.  Used in exactly one place: `idxOOK_tab` (`IdxOOK` for the current `tabOf`). -/
def HincDup (q : ℕ) (rows : Array RowNX) (acs : List Noun) : Prop :=
  q ∈ (ComplJ8Data.incOpsP q rows).map Prod.fst →
    Nock.V1J8.Gen.lastIdxOf acs (ComplJ8Data.combPP q) = Nock.V1J8.Gen.idxOf acs (ComplJ8Data.combPP q)

/-- The operand facts `incSum_eq9` reads (`genHyp`'s `ops` with the atom-table rows of the combs). -/
def OpsOK (q : ℕ) (rows : Array RowNX) (acs : List Noun) : Prop :=
  ∀ vc ∈ ComplJ8Data.incOpsP q rows,
    (vc.1 + 1 = q → ComplJ8Data.combPP q ∈ acs) ∧
    (vc.1 + 1 ≠ q → q ≤ vc.1 ∧ Nock.V1J8.Gen.combOf (Nock.Atoms.limbs vc.1) ∈ acs ∧
      Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (vc.1 + 1)) ∈ acs)

set_option maxHeartbeats 2000000 in
/-- **The atom table's inc terminal, by operand, at any limb count** (generic data record: any `mb`, abstract
`info` meeting `IncInfoOK`): the `mi`-weighted inc-key LogUp total is `Σ_{(v, c) ∈ incOps} c · FI v`. -/
theorem incSum_eq9 (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r)
    (hHdl : D.H = ComplJ8Data.hdlP p D.cells D.acs)
    (hI : IncInfoOK p D.acs (ComplJ8Data.incOpsP p D.rows) D.info)
    (hops : OpsOK p D.rows D.acs) (hidxO : IdxOOK D)
    (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K) (pubs : ℕ → K) :
    ∑ j ∈ Finset.range D.acs.length,
        liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mi)) *
          (HonestA8.dNat δ (HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs
            (colAH δ b D hA o χ pubs) (newBA D)) j)⁻¹ =
      ((ComplJ8Data.incOpsP p D.rows).map fun vc => (vc.2 : 𝕂′) * FI δ D χ vc.1).sum := by
  subst hpG
  set ops := ComplJ8Data.incOpsP Nock.Atoms.p D.rows with hops'
  obtain ⟨hmi, hconv, hinc⟩ := hI
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [ComplJ8OfBal.genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  have hgetD : ∀ c ∈ D.acs, ∀ d, D.acs.getD (Nock.V1J8.Gen.idxOf D.acs c) d = c := by
    intro c hc d
    rw [List.getD_eq_getElem _ _ (hlt c hc)]
    simp only [ComplJ8OfBal.genIdxOf_eq _ _ hc]
    exact List.getElem_idxOf _
  have hgetL : ∀ c ∈ D.acs, ∀ d, D.acs.getD (Nock.V1J8.Gen.lastIdxOf D.acs c) d = c := by
    intro c hc d
    simp [List.getD_eq_getElem?_getD, ComplJ8Atom.lastIdxOf_mem _ _ hc]
  have hne : D.acs ≠ [] := List.ne_nil_of_length_pos hA
  have hrP : ComplJ8Data.rootIdxP Nock.Atoms.p D.acs Nock.Atoms.p =
      Nock.V1J8.Gen.lastIdxOf D.acs (ComplJ8Data.combPP Nock.Atoms.p) := by
    simp [ComplJ8Data.rootIdxP]
  have hrN : ∀ a, a ≠ Nock.Atoms.p → ComplJ8Data.rootIdxP Nock.Atoms.p D.acs a =
      Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) := by
    intro a ha; simp [ComplJ8Data.rootIdxP, ha]
  set tgt : ℕ × ℕ → ℕ := fun vc => ComplJ8Data.rootIdxP Nock.Atoms.p D.acs (vc.1 + 1) with htgt
  have htl : ∀ vc ∈ ops, tgt vc < D.acs.length := by
    intro vc hvc
    by_cases hp : vc.1 + 1 = Nock.Atoms.p
    · simp only [htgt, hp, hrP]; exact ComplJ8Data.lastIdxOf_lt _ _ hne
    · simp only [htgt, hrN _ hp]; exact hlt _ ((hops vc hvc).2 hp).2.2
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs)
          (newBA D)) j)⁻¹ =
      ((((ops.filter fun vc => tgt vc = j).map Prod.snd).sum : ℕ) : Quad (algebraMap (ZMod Nock.Atoms.p) K δ)) *
        GAt δ b D hA o χ pubs j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj', GAt, newBA_mi, hmi j hj', liftQ, map_natCast]
    rfl
  rw [Finset.sum_congr rfl hterm, ← sum_serialW D.acs.length tgt Prod.snd (GAt δ b D hA o χ pubs) ops htl]
  refine congrArg List.sum (List.map_congr_left fun vc hvc => ?_)
  congr 1
  rcases vc with ⟨v, c⟩
  dsimp only
  have hk := htl (v, c) hvc
  have hH : HonestCompX.HdlOK Nock.Atoms.p D.H := hHdl ▸ ComplJ8Data.hdlOK_hdlP Nock.Atoms.p D.cells D.acs
  have hHb : ∀ a, Nock.Atoms.p ≤ a → D.H (.atom a) = (2, ComplJ8Data.rootIdxP Nock.Atoms.p D.acs a) := by
    intro a ha
    rw [hHdl]
    simp [ComplJ8Data.hdlP, Nat.not_lt.mpr ha]
  obtain ⟨x, hx, -, -, hle⟩ := ComplJ8Atom.mem_incOpsP _ _ (v, c) hvc
  simp only [GAt, dif_pos hk, FI]
  rw [dMI_key δ b D hA o hinj χ pubs ⟨tgt (v, c), hk⟩, newBA_conv]
  congr 2
  by_cases hp : v + 1 = Nock.Atoms.p
  · have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = true :=
      (hconv _ hk).mpr ⟨(v, c), hvc, hp, by simp only [htgt, hp]⟩
    have hsm : D.H (.atom v) = (0, v) := hH.small v (by omega)
    have hv1 : ((v : ℕ) : ZMod Nock.Atoms.p) = -1 := by
      have : ((v + 1 : ℕ) : ZMod Nock.Atoms.p) = 0 := by rw [hp, ZMod.natCast_self]
      push_cast at this; linear_combination this
    simp only [hc, if_true, hsm, hHb (v + 1) (by omega), hv1]
    simp only [htgt]
    norm_num
  · obtain ⟨hpv, m1, m2⟩ := (hops (v, c) hvc).2 hp
    have hpv' : Nock.Atoms.p < v + 1 := by omega
    have hl1 : 2 ≤ (Nock.Atoms.limbs v).length := HonestPairX.two_le_length_limbs (by
      have : Nock.Atoms.B ≤ Nock.Atoms.p := by simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
      omega)
    have hl2 : 2 ≤ (Nock.Atoms.limbs (v + 1)).length := HonestPairX.two_le_length_limbs (by
      have : Nock.Atoms.B ≤ Nock.Atoms.p := by simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
      omega)
    have hkt : tgt (v, c) = Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1))) := by
      simp only [htgt, hrN _ hp]
    have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = false := by
      cases hcc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv
      · rfl
      · exfalso
        obtain ⟨wc, hwc, hwp, hwk⟩ := (hconv _ hk).mp hcc
        have mP := (hops wc hwc).1 hwp
        rw [hrP, hkt] at hwk
        have e1 : ComplJ8Data.combPP Nock.Atoms.p = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1)) := by
          rw [← hgetL _ mP Nock.V1J8.Gen.padN, ← hgetD _ m2 Nock.V1J8.Gen.padN, hwk]
        have e2 : Nock.Atoms.limbs Nock.Atoms.p = Nock.Atoms.limbs (v + 1) := by
          rw [← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs Nock.Atoms.p) (by rw [Nock.Atoms.limbs_p]; simp),
            ← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs (v + 1)) hl2]
          exact congrArg ComplJ8Atom.unComb e1
        have e3 : Nock.Atoms.p = v + 1 := by
          rw [← Nock.Atoms.val_limbs Nock.Atoms.p, ← Nock.Atoms.val_limbs (v + 1), e2]
        exact hp e3.symm
    have hidx : newBA D AtomChipHQ.idxO ⟨tgt (v, c), hk⟩ =
        ((ComplJ8Data.rootIdxP Nock.Atoms.p D.acs v : ℕ) : ZMod Nock.Atoms.p) := by
      have e : (⟨tgt (v, c), hk⟩ : Fin D.acs.length) = ⟨_, hkt ▸ hk⟩ := Fin.ext hkt
      rw [e]; exact hidxO (v, c) hvc hp _
    rw [hidx]
    simp only [hc, Bool.false_eq_true, if_false, hHb v hpv, hHb (v + 1) (by omega)]
    simp only [htgt]
    norm_num

end IncAtomSum9

section IncRun9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The run's operands meet `OpsOK`** (from `complJ8`'s binders `hpG hax hop5`, any limb count). -/
theorem opsOK_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    OpsOK p (j8DataOf p Rg Rt hgen).rows (j8DataOf p Rg Rt hgen).acs := by
  intro vc hvc
  subst hpG
  have hg := ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 hN
  have hl : ∀ a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs, 2 ≤ (Nock.Atoms.limbs a).length := by
    intro a ha
    have : Nock.Atoms.B ≤ Nock.Atoms.p := by simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
    exact HonestPairX.two_le_length_limbs (by have := hg.big a ha; omega)
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have hm := (hg.ops vc hvc).1 hp
    exact ComplJ8OfBal.comb_mem_acs Rt hgen rfl hm (hl _ hm)
  · obtain ⟨h1, h2⟩ := (hg.ops vc hvc).2 hp
    exact ⟨hg.big _ h1, ComplJ8OfBal.comb_mem_acs Rt hgen rfl h1 (hl _ h1),
      ComplJ8OfBal.comb_mem_acs Rt hgen rfl h2 (hl _ h2)⟩

/-- **The fixed generator meets `IdxOOK` at the run, at any `mb`** (GLA fix (B); replaces `idxOOK_tab`, which took
the TEMPORARY `HincDup` and stated `IdxOOK` at an arbitrary data record, true only while the old index was the tail
pointer): the depth-0 inc row of a non-conversion operand `v` keys `rootIdxP p acs v` (`ComplJ8Atom.idxO_root`).
Binders `hpG hax hop5`; no corner binder. -/
theorem idxOOK_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) (mb : Array ℕ) :
    IdxOOK ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r) := by
  subst hpG
  intro vc hvc hp hk
  rw [newBA_idxO]
  have h := ComplJ8Atom.idxO_root _ _ _ _ (ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 hN) vc hvc hp
  exact congrArg (fun n : ℕ => (n : ZMod Nock.Atoms.p)) h

/-- **The current `infoOfP` meets `IncInfoOK` at the run, at any limb count.** -/
theorem incInfoOK_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    IncInfoOK p (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows)
      (j8DataOf p Rg Rt hgen).info := by
  refine incInfoOK_infoOfP p _ _ fun vc hvc hp => ?_
  obtain ⟨h1, -, -⟩ := (opsOK_run Rt hgen hpG hax hop5 hN vc hvc).2 hp
  have : Nock.Atoms.B ≤ p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  exact ⟨HonestPairX.two_le_length_limbs (by omega), HonestPairX.two_le_length_limbs (by omega)⟩

set_option maxHeartbeats 2000000 in
/-- **`hI` at general limbs**: at any data record `D` that agrees with the run's `j8DataOf` on `rows acs H cells`
(any `mb` and `info`; J-9 B:
`mb := mb9`), with `info` meeting `IncInfoOK` (hypothesis `hinfo`; `incInfoOK_run` supplies it for the current
`infoOfP`), the compute's inc consumes total the atom table's inc terminal, at every coin and orbit, from
`complJ8`'s binders `hpG hax hop5` and the abstract old-row column `hidxO : IdxOOK D` (GLA's fix (B); for the
current `tabOf`, `idxOOK_tab` under the TEMPORARY `HincDup`). -/
theorem hI9 (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) (D : J8Data p Rg fuel s f r)
    (hr : D.rows = (j8DataOf p Rg Rt hgen).rows) (ha : D.acs = (j8DataOf p Rg Rt hgen).acs)
    (hH : D.H = (j8DataOf p Rg Rt hgen).H) (hc : D.cells = (j8DataOf p Rg Rt hgen).cells)
    (hinfo : IncInfoOK p D.acs (ComplJ8Data.incOpsP p D.rows) D.info) (hidxO : IdxOOK D)
    (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubMI) (pubsAOf δ b D hA o χ (AtomChipHQ.pubMI + 1)) := by
  obtain ⟨-, -, -, -, -, tMI⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  have hops : OpsOK p D.rows D.acs := by
    rw [hr, ha]; exact opsOK_run Rt hgen hpG hax hop5 hN
  have hHdl : D.H = ComplJ8Data.hdlP p D.cells D.acs := by rw [hH, hc, ha]; rfl
  have hFI : FI δ D χ = FI δ (j8DataOf p Rg Rt hgen) χ := by funext v; simp only [FI, hH]
  rw [tMI, incSum_eq9 δ b hpG D hHdl hinfo hops hidxO hA o hinj χ _, incT_total δ b Rt hgen hax hop5 χ _, hFI, hr]

end IncRun9

/-! ## hA: the atom-walk pair consumes at general limbs (compute half) -/

section CombRecs
open Nock.V1J8.Gen (combOf spineOf idxOf)
variable {p : ℕ} [Fact p.Prime]

theorem combOf_cell (l : List ℕ) (h : 2 ≤ l.length) : ∃ u w, combOf l = .cell u w := by
  have := ComplJ8OfBal.combOf_isCell l h
  cases hc : combOf l with
  | atom v => rw [hc] at this; simp [Noun.isCell] at this
  | cell u w => exact ⟨u, w, rfl⟩

/-- **Every AW record of a comb is the honest `acs` handle (`Gen.hdl`) of its slot** (any number of limbs): a
`(2·ax, 0, x)` record is the inline limb `x`; a `(2·ax + 1, 1, sx (d+1))` record is the suffix comb, with `sx` its
row in `acs`. -/
theorem recsA_hdl (acs : List Noun) (sx : ℕ → ℕ) (R : Noun) : ∀ (l : List ℕ) (d ax : ℕ), 1 ≤ ax →
    Noun.slot ax R = some (combOf l) → (∀ x ∈ l, x < Nock.V1J8.Gen.P) →
    (∀ e, 1 ≤ e → 2 ≤ (l.drop e).length → sx (d + e) = idxOf acs (combOf (l.drop e))) →
    ∀ q ∈ HonestPairX.recsA sx d ax l, ∃ ch, Noun.slot q.1 R = some ch ∧
      Nock.V1J8.Gen.hdl acs ch = (q.2.1, q.2.2)
  | [x, x'], d, ax, hax, hs, hl, _ => by
    intro q hq
    simp only [HonestPairX.recsA, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · refine ⟨.atom x, ?_, by simp [Nock.V1J8.Gen.hdl, hl x (by simp)]⟩
      rw [Nock.GlobalCarryAxis.slot_double ax hax, hs]; rfl
    · refine ⟨.atom x', ?_, by simp [Nock.V1J8.Gen.hdl, hl x' (by simp)]⟩
      rw [Nock.GlobalCarryAxis.slot_double_succ ax hax, hs]; rfl
  | x :: x1 :: x2 :: xs, d, ax, hax, hs, hl, hsx => by
    intro q hq
    have hc : combOf (x :: x1 :: x2 :: xs) = .cell (.atom x) (combOf (x1 :: x2 :: xs)) :=
      ComplJ8Atom.combOf_cons x _ (by simp)
    have hsR : Noun.slot (2 * ax + 1) R = some (combOf (x1 :: x2 :: xs)) := by
      rw [Nock.GlobalCarryAxis.slot_double_succ ax hax, hs, hc]; rfl
    simp only [HonestPairX.recsA, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · refine ⟨.atom x, ?_, by simp [Nock.V1J8.Gen.hdl, hl x (by simp)]⟩
      rw [Nock.GlobalCarryAxis.slot_double ax hax, hs, hc]; rfl
    · refine ⟨_, hsR, ?_⟩
      obtain ⟨u, w, hw⟩ := combOf_cell (x1 :: x2 :: xs) (by simp)
      have h1 := hsx 1 le_rfl (by simp)
      simp only [List.drop_one, List.tail_cons] at h1
      rw [hw] at h1 ⊢
      simp [Nock.V1J8.Gen.hdl, h1]
    · refine recsA_hdl acs sx R (x1 :: x2 :: xs) (d + 1) (2 * ax + 1) (by omega) hsR
        (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (fun e he h2 => ?_) q hq
      have := hsx (e + 1) (by omega) (by simpa using h2)
      rw [show d + 1 + e = d + (e + 1) by omega, this]
      simp
  | [], _, _, _, _, _, _ => by simp [HonestPairX.recsA]
  | [_], _, _, _, _, _, _ => by simp [HonestPairX.recsA]

/-- **`recsA_hdl` at the pointer** (J9BC5A): when the spine serial `sx` at depth `d + e` is the PARENT row's tail
pointer `ptrP (combOf (l.drop (e − 1)))`, every AW record of the comb at axis `ax` is the pointer child handle
`chPP` of its read `(R, axis)`. -/
theorem recsA_chP (acs : List Noun) (rows : Array RowNX) (sx : ℕ → ℕ) (R : Noun) :
    ∀ (l : List ℕ) (d ax : ℕ), 1 ≤ ax →
    Noun.slot ax R = some (combOf l) → (∀ x ∈ l, x < Nock.V1J8.Gen.P) →
    (∀ e, 1 ≤ e → 2 ≤ (l.drop e).length → sx (d + e) = ComplJ8Data.ptrP p acs rows (combOf (l.drop (e - 1)))) →
    ∀ q ∈ HonestPairX.recsA sx d ax l, ∃ ch, Noun.slot q.1 R = some ch ∧
      ComplJ8Data.chPP p acs rows (R, q.1) = (q.2.1, q.2.2)
  | [x, x'], d, ax, hax, hs, hl, _ => by
    intro q hq
    simp only [HonestPairX.recsA, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · have e1 : Noun.slot (2 * ax) R = some (.atom x) := by
        rw [Nock.GlobalCarryAxis.slot_double ax hax, hs]; rfl
      refine ⟨.atom x, e1, ?_⟩
      simp [ComplJ8Data.chPP, e1, Nock.V1J8.Gen.hdl, hl x (by simp)]
    · have e1 : Noun.slot (2 * ax + 1) R = some (.atom x') := by
        rw [Nock.GlobalCarryAxis.slot_double_succ ax hax, hs]; rfl
      refine ⟨.atom x', e1, ?_⟩
      simp [ComplJ8Data.chPP, e1, Nock.V1J8.Gen.hdl, hl x' (by simp)]
  | x :: x1 :: x2 :: xs, d, ax, hax, hs, hl, hsx => by
    intro q hq
    have hc : combOf (x :: x1 :: x2 :: xs) = .cell (.atom x) (combOf (x1 :: x2 :: xs)) :=
      ComplJ8Atom.combOf_cons x _ (by simp)
    have hsR : Noun.slot (2 * ax + 1) R = some (combOf (x1 :: x2 :: xs)) := by
      rw [Nock.GlobalCarryAxis.slot_double_succ ax hax, hs, hc]; rfl
    simp only [HonestPairX.recsA, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · have e1 : Noun.slot (2 * ax) R = some (.atom x) := by
        rw [Nock.GlobalCarryAxis.slot_double ax hax, hs, hc]; rfl
      refine ⟨.atom x, e1, ?_⟩
      simp [ComplJ8Data.chPP, e1, Nock.V1J8.Gen.hdl, hl x (by simp)]
    · refine ⟨_, hsR, ?_⟩
      obtain ⟨u, w, hw⟩ := combOf_cell (x1 :: x2 :: xs) (by simp)
      have h1 := hsx 1 le_rfl (by simp)
      simp only [Nat.sub_self, List.drop_zero] at h1
      have hodd : (2 * ax + 1) % 2 = 1 ∧ 2 ≤ 2 * ax + 1 := ⟨by omega, by omega⟩
      have hdiv : (2 * ax + 1) / 2 = ax := by omega
      simp only [ComplJ8Data.chPP, hsR, hw, Option.getD_some, if_pos hodd, hdiv, hs, h1]
    · refine recsA_chP acs rows sx R (x1 :: x2 :: xs) (d + 1) (2 * ax + 1) (by omega) hsR
        (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (fun e he h2 => ?_) q hq
      have := hsx (e + 1) (by omega) (by simpa using h2)
      rw [show d + 1 + e = d + (e + 1) by omega, this]
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      simp
  | [], _, _, _, _, _, _ => by simp [HonestPairX.recsA]
  | [_], _, _, _, _, _, _ => by simp [HonestPairX.recsA]

/-- **The first difference of two combs is a record of each** (no distinctness needed). -/
theorem combFD_mem (sxa sxb : ℕ → ℕ) : ∀ (xs ys : List ℕ) (d ax : ℕ), 2 ≤ xs.length → 2 ≤ ys.length →
    ((HonestPairX.combFD sxa sxb d ax xs ys).1, (HonestPairX.combFD sxa sxb d ax xs ys).2.1) ∈
        HonestPairX.recsA sxa d ax xs ∧
      ((HonestPairX.combFD sxa sxb d ax xs ys).1, (HonestPairX.combFD sxa sxb d ax xs ys).2.2) ∈
        HonestPairX.recsA sxb d ax ys
  | [x, x'], [y, y'], d, ax, _, _ => by
    by_cases h : x = y <;> simp [HonestPairX.combFD, HonestPairX.recsA, h]
  | [x, x'], y :: y1 :: y2 :: ys, d, ax, _, _ => by
    by_cases h : x = y <;> simp [HonestPairX.combFD, HonestPairX.recsA, h]
  | x :: x1 :: x2 :: xs, [y, y'], d, ax, _, _ => by
    by_cases h : x = y <;> simp [HonestPairX.combFD, HonestPairX.recsA, h]
  | x :: x1 :: x2 :: xs, y :: y1 :: y2 :: ys, d, ax, _, _ => by
    by_cases h : x = y
    · obtain ⟨h5, h6⟩ := combFD_mem sxa sxb (x1 :: x2 :: xs) (y1 :: y2 :: ys) (d + 1) (2 * ax + 1)
        (by simp) (by simp)
      simp only [HonestPairX.combFD, if_pos h]
      exact ⟨by simp only [HonestPairX.recsA]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h5),
        by simp only [HonestPairX.recsA]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h6)⟩
    · simp [HonestPairX.combFD, HonestPairX.recsA, h]
  | [], _, _, _, h, _ => by simp at h
  | [_], _, _, _, h, _ => by simp at h
  | _ :: _ :: _, [], _, _, _, h => by simp at h
  | _ :: _ :: _, [_], _, _, _, h => by simp at h

theorem spineOf_getD : ∀ (l : List ℕ) (e : ℕ), 2 ≤ (l.drop e).length →
    (spineOf l).getD e (.atom 0) = combOf (l.drop e)
  | x :: y :: rest, 0, _ => by simp [spineOf]
  | x :: y :: rest, e + 1, h => by
    rw [ComplJ8Atom.spineOf_cons2 _ (by simp)]
    simp only [List.getD_cons_succ, List.tail_cons]
    exact spineOf_getD (y :: rest) e (by simpa using h)
  | [], e, h => by simp at h
  | [x], e, h => by cases e <;> simp at h

/-- **`sxPP = sxOf` when `comb p` has no duplicate**: the pointer of the depth `e - 1` spine row is the
`idxOf` of its tail, which is the depth `e` suffix comb. -/
theorem sxPP_eq_sxOf {p : ℕ} (acs : List Noun) (rows : Array RowNX)
    (h : Nock.V1J8.Gen.lastIdxOf acs (ComplJ8Data.combPP p) = Nock.V1J8.Gen.idxOf acs (ComplJ8Data.combPP p))
    (a e : ℕ) (he : 1 ≤ e) (h2 : 2 ≤ ((Nock.Atoms.limbs a).drop e).length) :
    ComplJ8Data.sxPP p acs rows a e = Nock.V1J8.Gen.sxOf acs a e := by
  unfold ComplJ8Data.sxPP Nock.V1J8.Gen.sxOf
  rw [ComplJ8Data.ptrP_eq_idxOf (p := p) acs rows h]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h3 : 3 ≤ ((Nock.Atoms.limbs a).drop k).length := by
    rw [List.length_drop] at h2 ⊢; omega
  rw [Nat.add_sub_cancel, spineOf_getD _ k (by omega), spineOf_getD _ (k + 1) h2,
    ComplJ8Atom.tl_combOf _ (by omega), if_pos h3, List.tail_drop]

end CombRecs

section AWRun9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 atom-walk read weight**: `1 / (ρH + recDenP 0 γH (rIAP root, axis, chPP p D.acs D.rows (root, axis)))` — the
root at `rIAP` (`comb p` at its LAST row, as the generator) and the leaf at the pointer handle `chPP` (a cell child at an
odd axis is `(1, ptrP …)` of its parent; any other child is `Gen.hdl D.acs`). -/
noncomputable def WA9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (x : Noun × ℕ) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (((ComplJ8Data.rIAP p D.acs x.1 : ℕ) : ZMod p),
    ((x.2 : ℕ) : ZMod p),
    ((((ComplJ8Data.chPP p D.acs D.rows x).1 : ℕ) : ZMod p),
     (((ComplJ8Data.chPP p D.acs D.rows x).2 : ℕ) : ZMod p))))⁻¹

theorem WA9_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (x : Noun × ℕ)
    {k v : ℕ} (hh : ComplJ8Data.chPP p D.acs D.rows x = (k, v)) :
    WA9 δ D χ x = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((ComplJ8Data.rIAP p D.acs x.1 : ℕ) : ZMod p), ((x.2 : ℕ) : ZMod p), (((k : ℕ) : ZMod p), ((v : ℕ) : ZMod p))))⁻¹ := by
  simp only [WA9, hh]

/-- A big atom's root serial is `rIAP` of its root comb. -/
theorem rootIdx_rIAP (hpG : p = Nock.Atoms.p) (acs : List Noun) {a : ℕ} (h2 : 2 ≤ (Nock.Atoms.limbs a).length) :
    ComplJ8Data.rootIdxP p acs a = ComplJ8Data.rIAP p acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) := by
  obtain ⟨u, w, hw⟩ := combOf_cell (Nock.Atoms.limbs a) h2
  by_cases ha : a = p
  · subst ha; simp [ComplJ8Data.rootIdxP, ComplJ8Data.rIAP, ComplJ8Data.combPP]
  · have hne : Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ≠ ComplJ8Data.combPP p := by
      intro e
      apply ha
      have e2 : Nock.Atoms.limbs a = Nock.Atoms.limbs p := by
        rw [← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs a) h2,
          ← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs p) (by rw [hpG, Nock.Atoms.limbs_p]; simp)]
        exact congrArg ComplJ8Atom.unComb e
      rw [← Nock.Atoms.val_limbs a, ← Nock.Atoms.val_limbs p, e2]
    simp only [ComplJ8Data.rootIdxP, ha, if_false, ComplJ8Data.rIAP, hne]
    rw [hw]; rfl

/-- The suffix combs of a big atom of the run are atom-table rows. -/
theorem suffix_mem_acs (hpG : p = Nock.Atoms.p) {a : ℕ} (ha : a ∈ (j8DataOf p Rg Rt hgen).bigs) (e : ℕ)
    (h2 : 2 ≤ ((Nock.Atoms.limbs a).drop e).length) :
    Nock.V1J8.Gen.combOf ((Nock.Atoms.limbs a).drop e) ∈ (j8DataOf p Rg Rt hgen).acs := by
  subst hpG
  rw [ComplJ8BigBound.data_acs hgen]
  exact (ComplJ8Atom.mem_acsP _ _ _).mpr (Or.inl ((ComplJ8Atom.mem_spineL _ _).mpr
    ⟨a, ha, (ComplJ8Atom.mem_spineOf _ _).mpr ⟨e, h2, rfl⟩⟩))

/-- **An honest op-5 pair row's two atom-walk reads, any number of limbs**: both leaves are big atoms of the run,
and the comb's slot at the first-difference axis has the recorded `(kind, value)` as its honest `acs` handle. -/
theorem pair_facts9 (hpG : p = Nock.Atoms.p) {row : RowNX} (hrow : row ∈ (j8DataOf p Rg Rt hgen).rows.toList)
    (hpair : HonestCompX.isPair (j8DataOf p Rg Rt hgen).H row) :
    ∃ a c, row.ftth = .atom a ∧ row.fttt = .atom c ∧ a ∈ (j8DataOf p Rg Rt hgen).bigs ∧
      c ∈ (j8DataOf p Rg Rt hgen).bigs ∧
      (∃ ch, Noun.slot ((j8DataOf p Rg Rt hgen).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) = some ch ∧
        ComplJ8Data.chPP p (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).rows
            (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a), ((j8DataOf p Rg Rt hgen).pd row).1) =
          (((j8DataOf p Rg Rt hgen).pd row).2.1.1, ((j8DataOf p Rg Rt hgen).pd row).2.1.2)) ∧
      (∃ ch, Noun.slot ((j8DataOf p Rg Rt hgen).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) = some ch ∧
        ComplJ8Data.chPP p (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).rows
            (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c), ((j8DataOf p Rg Rt hgen).pd row).1) =
          (((j8DataOf p Rg Rt hgen).pd row).2.2.1, ((j8DataOf p Rg Rt hgen).pd row).2.2.2)) := by
  set D := j8DataOf p Rg Rt hgen with hD
  obtain ⟨-, -, h1, h2⟩ := hpair
  have hkind : ∀ n : Noun, n ∈ rowHandleNounsX row → (D.H n).1 = 2 →
      ∃ a, n = .atom a ∧ a ∈ D.bigs := by
    intro n hn hk
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    rw [hH] at hk
    cases n with
    | cell l r' => simp [ComplJ8Data.hdlP] at hk
    | atom a =>
      have hpa : p ≤ a := by
        by_contra hlt
        simp [ComplJ8Data.hdlP, show a < p by omega] at hk
      refine ⟨a, rfl, ?_⟩
      show a ∈ ComplJ8Data.bigsP p D.roots D.rows
      refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hpa⟩
      refine List.mem_flatMap.mpr ⟨.atom a, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ?_⟩
      simp [leavesOf]
  obtain ⟨a, ha', ha⟩ := hkind row.ftth (by simp [rowHandleNounsX]) h1
  obtain ⟨c, hc', hc⟩ := hkind row.fttt (by simp [rowHandleNounsX]) h2
  have hB : Nock.Atoms.B ≤ p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  have hbig : ∀ x ∈ D.bigs, p ≤ x := fun x hx => ((ComplJ8Atom.mem_bigsP p _ _ x).mp hx).2
  have hla : 2 ≤ (Nock.Atoms.limbs a).length := HonestPairX.two_le_length_limbs (by have := hbig a ha; omega)
  have hlc : 2 ≤ (Nock.Atoms.limbs c).length := HonestPairX.two_le_length_limbs (by have := hbig c hc; omega)
  have e : D.pd row = HonestPairX.combFD (ComplJ8Data.sxPP p D.acs D.rows a) (ComplJ8Data.sxPP p D.acs D.rows c) 0 1
      (Nock.Atoms.limbs a) (Nock.Atoms.limbs c) := by
    show HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row = _
    unfold HonestPairX.pdX; rw [ha', hc']
  obtain ⟨m1, m2⟩ := combFD_mem (ComplJ8Data.sxPP p D.acs D.rows a) (ComplJ8Data.sxPP p D.acs D.rows c)
    (Nock.Atoms.limbs a) (Nock.Atoms.limbs c) 0 1 hla hlc
  have hsx : ∀ x ∈ D.bigs, ∀ e', 1 ≤ e' → 2 ≤ ((Nock.Atoms.limbs x).drop e').length →
      ComplJ8Data.sxPP p D.acs D.rows x (0 + e') =
        ComplJ8Data.ptrP p D.acs D.rows (Nock.V1J8.Gen.combOf ((Nock.Atoms.limbs x).drop (e' - 1))) := by
    intro x hx e' he h2
    have h2' : 2 ≤ ((Nock.Atoms.limbs x).drop (e' - 1)).length := by
      have : ((Nock.Atoms.limbs x).drop e').length ≤ ((Nock.Atoms.limbs x).drop (e' - 1)).length := by
        simp only [List.length_drop]; omega
      omega
    simp only [ComplJ8Data.sxPP, zero_add, spineOf_getD _ (e' - 1) h2']
  have hBP : Nock.Atoms.B ≤ Nock.V1J8.Gen.P := by simp [Nock.Atoms.B, Nock.V1J8.Gen.P, Nock.Field.p]
  have hlP : ∀ x, ∀ y ∈ Nock.Atoms.limbs x, y < Nock.V1J8.Gen.P := fun x y hy => by
    have := HonestPairX.limbs_lt x y hy; omega
  have s1 := recsA_chP D.acs D.rows (ComplJ8Data.sxPP p D.acs D.rows a) (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a))
    (Nock.Atoms.limbs a) 0 1 le_rfl (by simp [Noun.slot]) (hlP a) (hsx a ha) _ m1
  have s2 := recsA_chP D.acs D.rows (ComplJ8Data.sxPP p D.acs D.rows c) (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c))
    (Nock.Atoms.limbs c) 0 1 le_rfl (by simp [Noun.slot]) (hlP c) (hsx c hc) _ m2
  rw [← e] at s1 s2
  exact ⟨a, c, ha', hc', ha, hc, s1, s2⟩


set_option maxHeartbeats 2000000 in
/-- **Run row `j`'s atom-walk pair consume at any limb count** is the `WA9` total of the row's atom-walk reads. -/
theorem awT_run9 (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ)
    (hj : j < (bfsForest [t]).length) :
    awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((if Nock.V1J8.FillX.isPairB (j8DataOf p Rg Rt hgen).H (rowOfSkelX ((bfsForest [t])[j]'hj).label) then
          [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).ftth)),
              ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1),
           (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).fttt)),
              ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1)]
        else []).map fun x => WA9 δ (j8DataOf p Rg Rt hgen) χ x).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ D.rows.toList := by
    simp only [hrr, hD, j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold awT
  rw [DX_walkA δ b _ χ rfl, DX_walkA δ b _ χ rfl, htr]
  simp only [ChipHX.xFtth, ChipHX.xFttt, ChipHX.xL1, ChipHX.xL2, ChipHX.hdX, HonestCompX.cx64, HonestCompX.cx63,
    HonestCompX.cx65, HonestCompX.cx66, HonestCompX.cx67, HonestCompX.cx68]
  rw [show (26 + 2 * 9 : ℕ) = 44 from rfl, show (26 + 2 * 10 : ℕ) = 46 from rfl, HonestCompX.cxFtth_v,
    HonestCompX.cxFttt_v]
  by_cases hp : HonestCompX.isPair D.H rr
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = true := (Nock.V1J8.FillX.isPairB_iff D.H rr).mpr hp
    rw [if_pos hpB]
    obtain ⟨a, c, ha', hc', ha, hc, ⟨ch1, hs1, hh1⟩, ⟨ch2, hs2, hh2⟩⟩ := pair_facts9 Rt hgen hpG hrowm hp
    have hst : rr.st = .s5 := hp.1
    have hB : Nock.Atoms.B ≤ p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
    have hbig : ∀ x ∈ D.bigs, p ≤ x := fun x hx => ((ComplJ8Atom.mem_bigsP p _ _ x).mp hx).2
    have hroot : ∀ x ∈ D.bigs, (D.H (.atom x)).2 =
        ComplJ8Data.rIAP p D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs x)) := by
      intro x hx
      show (ComplJ8Data.hdlP p D.cells D.acs (.atom x)).2 = _
      have : ¬ x < p := Nat.not_lt.mpr (hbig x hx)
      simp only [ComplJ8Data.hdlP, this, if_false]
      exact rootIdx_rIAP hpG D.acs (HonestPairX.two_le_length_limbs (by have := hbig x hx; omega))
    have e1 := WA9_eq δ D χ (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a), (D.pd rr).1) hh1
    have e2 := WA9_eq δ D χ (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c), (D.pd rr).1) hh2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ha', hc',
      Nock.V1J8.Gen.atomV]
    rw [e1, e2]
    simp only [HonestCompX.cPr2, HonestCompX.cAx2, HonestCompX.cL, hst, if_pos hp, HonestCompX.hv, hroot a ha,
      hroot c hc, map_one, one_mul]
    rfl
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = false := by
      cases h : Nock.V1J8.FillX.isPairB D.H rr
      · rfl
      · exact absurd ((Nock.V1J8.FillX.isPairB_iff D.H rr).mp h) hp
    rw [if_neg (by simp [hpB])]
    simp [HonestCompX.cPr2, hp]

/-- **`hA`'s compute half at general limbs**: the compute's atom-walk pair consumes total the `WA9` weights of the
run's atom-walk reads `D.preads` (binder `hpG` only). -/
theorem awSum9 (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((j8DataOf p Rg Rt hgen).preads.map fun x => WA9 δ (j8DataOf p Rg Rt hgen) χ x).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => ((if Nock.V1J8.FillX.isPairB D.H (rowOfSkelX u.label) then
        [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).ftth)),
            (D.pd (rowOfSkelX u.label)).1),
         (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).fttt)),
            (D.pd (rowOfSkelX u.label)).1)]
      else []).map fun x => WA9 δ D χ x).sum with hgdef
  have hrow : ∀ j ∈ Finset.range W.length,
      awT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [awT_run9 δ b Rt hgen hpG χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g, preads_eq Rt hgen, ComplJ8OfBalG.sum_flatMap_map]

/-- **`hA` at general limbs, from its provide half**: if the atom walk's handle-provide public `PQ` is the `WA9`
total of `D.preads` (hypothesis `hV`; the J-9 atom-walk spec rows with `rIAP` roots and `chPP` (pointer) children
discharge it, GLB), the compute's pair consumes total it, at every coin. -/
theorem hA9 (hpG : p = Nock.Atoms.p) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (P : ℕ → K)
    (hV : Quad.mk _ (P WalkHQ.pubPQ) (P (WalkHQ.pubPQ + 1)) =
      ((j8DataOf p Rg Rt hgen).preads.map (WA9 δ (j8DataOf p Rg Rt hgen) χ)).sum) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (P WalkHQ.pubPQ) (P (WalkHQ.pubPQ + 1)) := by
  rw [awSum9 δ b Rt hgen hpG χ pubVal, hV]

end AWRun9

section IncRun9b
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

set_option maxHeartbeats 2000000 in
/-- **`hI9` at the run's data with any `mb`** (J-9 B: `mb := mb9`), the fixed `infoOfP` and `tabOf` (`idxOOK_run`;
the `hdup : HincDup` binder is kept for interface stability and is UNUSED since GLA fix (B)). -/
theorem hI9_mb (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31) (mb : Array ℕ)
    (hdup : HincDup p (j8DataOf p Rg Rt hgen).rows (j8DataOf p Rg Rt hgen).acs)
    (hA : 0 < ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r).acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (j8DataOf p Rg Rt hgen).acs.length)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      Quad.mk _ (pubsAOf δ b ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r) hA o χ
          AtomChipHQ.pubMI)
        (pubsAOf δ b ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r) hA o χ
          (AtomChipHQ.pubMI + 1)) :=
  hI9 δ b Rt hgen hpG hax hop5 hN ({ j8DataOf p Rg Rt hgen with mb := mb } : J8Data p Rg fuel s f r) rfl rfl rfl rfl
    (incInfoOK_run Rt hgen hpG hax hop5 hN)
    (idxOOK_run Rt hgen hpG hax hop5 hN mb) hA o hinj χ pubVal

end IncRun9b

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG
