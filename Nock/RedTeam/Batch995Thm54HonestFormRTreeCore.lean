/-
  Nock/RedTeam/Batch995Thm54HonestFormRTreeCore.lean

  No `hgood`, no event.

  Three env-free facts the honest component-11 argument is assembled from:

  * §A **renaming.**  `rn g t` renames every read / verify exponent of `t` by `g` and writes the
    verify node's `a` as `0` (the decoded tree's convention, `DecodedLambdaEvent.decodedMTreeOfEnvs`).
    If `g` is injective on the exponents of `t`, counts and top-down paths transport
    (`readCount_rn`, `rpaths_rn`,...), and `formRCounts` depends on the certificate maps only at the
    tree's exponents (`formRCounts_congr`).
  * §B **the served walk gives the paths.**  On a `ServedMemoryTrace.ServiceWalk` with read / verify
    exponent lists `Nodup`, every read exponent `e` has one read path `q` and one verify path
    `q ++ axisPath s.axis`, `s` the walk's service at `e` (`ServiceWalk.paths`).  Nothing beyond the
    walk's own route constructors is used: the route is the binary expansion of the record's axis.
  * §C **the certificate of an axis is its path.**  `bitsOf (formRCertShift a) (formRCertBit a ·-1)`
    is `axisPath a` (`bitsOf_cert_eq_axisPath`), with padding (`padding_cert`).

  §D assembles: `formRCounts n mm cc (rn g t) = 0` from §A–§C (`formRCounts_rn_zero`), through
  `Batch575.formR_counts_zero_iff`.
-/
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.FormRCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch995

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch554 (vpaths rpaths bitsOf bitsOf_length)

noncomputable section

variable {K : Type} [Field K]

/-! ## A. Renaming exponents and erasing the verify `a` -/

/-- Rename every exponent by `g`; write the verify node's `a` as `0`. -/
def rn (g : ℕ → ℕ) : MTree K → MTree K
  | .halt => .halt
  | .decompose l r => .decompose (rn g l) (rn g r)
  | .read e c => .read (g e) (rn g c)
  | .verify e _ c => .verify (g e) 0 (rn g c)

/-- The exponents occurring in `t` (read and verify). -/
def exps (t : MTree K) : List ℕ := readExps t ++ verifyExps t

theorem readExps_rn (g : ℕ → ℕ) : ∀ t : MTree K, readExps (rn g t) = (readExps t).map g
  | .halt => rfl
  | .decompose l r => by simp [rn, readExps, readExps_rn g l, readExps_rn g r]
  | .read e c => by simp [rn, readExps, readExps_rn g c]
  | .verify e _ c => by simp [rn, readExps, readExps_rn g c]

theorem verifyExps_rn (g : ℕ → ℕ) : ∀ t : MTree K, verifyExps (rn g t) = (verifyExps t).map g
  | .halt => rfl
  | .decompose l r => by simp [rn, verifyExps, verifyExps_rn g l, verifyExps_rn g r]
  | .read e c => by simp [rn, verifyExps, verifyExps_rn g c]
  | .verify e _ c => by simp [rn, verifyExps, verifyExps_rn g c]

/-- Injectivity of `g` on a set containing the exponents of `t`. -/
def InjOnExps (g : ℕ → ℕ) (S : ℕ → Prop) : Prop := ∀ a b, S a → S b → g a = g b → a = b

theorem mem_exps_decompose_l {l r : MTree K} {e : ℕ} (h : e ∈ exps l) :
    e ∈ exps (.decompose l r) := by
  simp only [exps, readExps, verifyExps, List.mem_append] at h ⊢; tauto

theorem mem_exps_decompose_r {l r : MTree K} {e : ℕ} (h : e ∈ exps r) :
    e ∈ exps (.decompose l r) := by
  simp only [exps, readExps, verifyExps, List.mem_append] at h ⊢; tauto

theorem mem_exps_read_c {e' : ℕ} {c : MTree K} {e : ℕ} (h : e ∈ exps c) :
    e ∈ exps (.read e' c) := by
  simp only [exps, readExps, verifyExps, List.mem_append, List.mem_cons] at h ⊢; tauto

theorem mem_exps_verify_c {e' : ℕ} {a : K} {c : MTree K} {e : ℕ} (h : e ∈ exps c) :
    e ∈ exps (.verify e' a c) := by
  simp only [exps, readExps, verifyExps, List.mem_append, List.mem_cons] at h ⊢; tauto

theorem mem_exps_read_self (e' : ℕ) (c : MTree K) : e' ∈ exps (.read e' c) := by
  simp [exps, readExps]

theorem mem_exps_verify_self (e' : ℕ) (a : K) (c : MTree K) : e' ∈ exps (.verify e' a c) := by
  simp [exps, verifyExps]

/-- Transport of a read / verify-indexed statistic `f` along `rn g`, for `e` in `S`. -/
theorem readCount_rn (g : ℕ → ℕ) (S : ℕ → Prop) (hg : InjOnExps g S) (e : ℕ) (he : S e) :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → readCount (g e) (rn g t) = readCount e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [rn, readCount]
      rw [readCount_rn g S hg e he l fun x hx => hS x (mem_exps_decompose_l hx),
        readCount_rn g S hg e he r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [rn, readCount]
      rw [readCount_rn g S hg e he c fun x hx => hS x (mem_exps_read_c hx)]
      have : g e' = g e ↔ e' = e :=
        ⟨hg e' e (hS e' (mem_exps_read_self e' c)) he, fun h => h ▸ rfl⟩
      simp only [this]
  | .verify e' _ c, hS => by
      simp only [rn, readCount]
      exact readCount_rn g S hg e he c fun x hx => hS x (mem_exps_verify_c hx)

theorem verifyCount_rn (g : ℕ → ℕ) (S : ℕ → Prop) (hg : InjOnExps g S) (e : ℕ) (he : S e) :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → verifyCount (g e) (rn g t) = verifyCount e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [rn, verifyCount]
      rw [verifyCount_rn g S hg e he l fun x hx => hS x (mem_exps_decompose_l hx),
        verifyCount_rn g S hg e he r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [rn, verifyCount]
      exact verifyCount_rn g S hg e he c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [rn, verifyCount]
      rw [verifyCount_rn g S hg e he c fun x hx => hS x (mem_exps_verify_c hx)]
      have : g e' = g e ↔ e' = e :=
        ⟨hg e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

theorem rpaths_rn (g : ℕ → ℕ) (S : ℕ → Prop) (hg : InjOnExps g S) (e : ℕ) (he : S e) :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → rpaths (g e) (rn g t) = rpaths e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [rn, rpaths]
      rw [rpaths_rn g S hg e he l fun x hx => hS x (mem_exps_decompose_l hx),
        rpaths_rn g S hg e he r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [rn, rpaths]
      rw [rpaths_rn g S hg e he c fun x hx => hS x (mem_exps_read_c hx)]
      have : g e' = g e ↔ e' = e :=
        ⟨hg e' e (hS e' (mem_exps_read_self e' c)) he, fun h => h ▸ rfl⟩
      simp only [this]
  | .verify e' _ c, hS => by
      simp only [rn, rpaths]
      exact rpaths_rn g S hg e he c fun x hx => hS x (mem_exps_verify_c hx)

theorem vpaths_rn (g : ℕ → ℕ) (S : ℕ → Prop) (hg : InjOnExps g S) (e : ℕ) (he : S e) :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → vpaths (g e) (rn g t) = vpaths e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [rn, vpaths]
      rw [vpaths_rn g S hg e he l fun x hx => hS x (mem_exps_decompose_l hx),
        vpaths_rn g S hg e he r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [rn, vpaths]
      exact vpaths_rn g S hg e he c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [rn, vpaths]
      rw [vpaths_rn g S hg e he c fun x hx => hS x (mem_exps_verify_c hx)]
      have : g e' = g e ↔ e' = e :=
        ⟨hg e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

/-- A value outside `g`'s image of the exponents is neither read nor verified in `rn g t`. -/
theorem readCount_rn_out (g : ℕ → ℕ) (x : ℕ) :
    ∀ t : MTree K, (∀ e ∈ exps t, g e ≠ x) → readCount x (rn g t) = 0
  | .halt, _ => rfl
  | .decompose l r, h => by
      simp only [rn, readCount]
      rw [readCount_rn_out g x l fun e he => h e (mem_exps_decompose_l he),
        readCount_rn_out g x r fun e he => h e (mem_exps_decompose_r he)]
  | .read e' c, h => by
      simp only [rn, readCount]
      rw [readCount_rn_out g x c fun e he => h e (mem_exps_read_c he),
        if_neg (h e' (mem_exps_read_self e' c))]
  | .verify e' _ c, h => by
      simp only [rn, readCount]
      exact readCount_rn_out g x c fun e he => h e (mem_exps_verify_c he)

theorem verifyCount_rn_out (g : ℕ → ℕ) (x : ℕ) :
    ∀ t : MTree K, (∀ e ∈ exps t, g e ≠ x) → verifyCount x (rn g t) = 0
  | .halt, _ => rfl
  | .decompose l r, h => by
      simp only [rn, verifyCount]
      rw [verifyCount_rn_out g x l fun e he => h e (mem_exps_decompose_l he),
        verifyCount_rn_out g x r fun e he => h e (mem_exps_decompose_r he)]
  | .read e' c, h => by
      simp only [rn, verifyCount]
      exact verifyCount_rn_out g x c fun e he => h e (mem_exps_read_c he)
  | .verify e' _ c, h => by
      simp only [rn, verifyCount]
      rw [verifyCount_rn_out g x c fun e he => h e (mem_exps_verify_c he),
        if_neg (h e' (mem_exps_verify_self e' _ c))]

/-- The exponents of `rn g t` are `g`'s image of those of `t`. -/
theorem exps_rn (g : ℕ → ℕ) (t : MTree K) : exps (rn g t) = (exps t).map g := by
  simp [exps, readExps_rn, verifyExps_rn]

/-- `formRPw` reads the certificate shift only at the tree's exponents. -/
theorem formRPw_congr (n : ℕ) (mm mm' : ℕ → ℕ) :
    ∀ t : MTree K, (∀ e ∈ exps t, mm e = mm' e) → formRPw n mm t = formRPw n mm' t
  | .halt, _ => rfl
  | .decompose l r, h => by
      simp only [formRPw]
      rw [formRPw_congr n mm mm' l fun e he => h e (mem_exps_decompose_l he),
        formRPw_congr n mm mm' r fun e he => h e (mem_exps_decompose_r he)]
  | .read e c, h => by
      simp only [formRPw]
      rw [formRPw_congr n mm mm' c fun x hx => h x (mem_exps_read_c hx),
        h e (mem_exps_read_self e c)]
  | .verify e _ c, h => by
      simp only [formRPw]
      rw [formRPw_congr n mm mm' c fun x hx => h x (mem_exps_verify_c hx)]

/-- `formRCounts` reads the certificate only at the tree's exponents. -/
theorem formRCounts_congr (n : ℕ) (mm mm' : ℕ → ℕ) (cc cc' : ℕ → ℕ → Bool) :
    ∀ t : MTree K, (∀ e ∈ exps t, mm e = mm' e ∧ cc e = cc' e) →
      formRCounts n mm cc t = formRCounts n mm' cc' t
  | .halt, _ => rfl
  | .decompose l r, h => by
      simp only [formRCounts]
      rw [formRCounts_congr n mm mm' cc cc' l fun e he => h e (mem_exps_decompose_l he),
        formRCounts_congr n mm mm' cc cc' r fun e he => h e (mem_exps_decompose_r he),
        formRPw_congr n mm mm' l fun e he => (h e (mem_exps_decompose_l he)).1,
        formRPw_congr n mm mm' r fun e he => (h e (mem_exps_decompose_r he)).1]
  | .read e c, h => by
      simp only [formRCounts]
      rw [formRCounts_congr n mm mm' cc cc' c fun x hx => h x (mem_exps_read_c hx),
        (h e (mem_exps_read_self e c)).1, (h e (mem_exps_read_self e c)).2]
  | .verify e _ c, h => by
      simp only [formRCounts]
      rw [formRCounts_congr n mm mm' cc cc' c fun x hx => h x (mem_exps_verify_c hx)]

/-! ## B. The served walk gives the read / verify paths -/

section Walk

variable {F : Type} [Field F] [Algebra F K]
variable {cfg : Nock.NockVMROM.Thm54.ExactConfig F K} {exec : Nock.NockVMROM.Thm54.ExactExecution cfg}
variable {services : List (Service cfg exec)}

/-- A route ends at exactly one verify node, at relative path `bs`. -/
theorem route_vpaths {e : ℕ} {child : Noun} {recAxis : K} {bs : List Bool} {n : Noun}
    {t : MTree K} (h : VerifyRoute e child recAxis bs n t) : vpaths e t = [bs] := by
  induction h with
  | here hchild hcommitted hr hv =>
      simp [Batch554.vpaths, vpaths_eq_nil e _ hv]
  | left route hr hv ih =>
      simp [Batch554.vpaths, ih, vpaths_eq_nil e _ hv]
  | right hr hv route ih =>
      simp [Batch554.vpaths, ih, vpaths_eq_nil e _ hv]
  | read_other hne route ih => simpa [Batch554.vpaths] using ih
  | verify_other hne route ih => simpa [Batch554.vpaths, hne] using ih

/-- The read count of an exponent is at most its verify count on a served walk. -/
theorem walk_rc_le_vc {n : Noun} {t : MTree K} (h : ServiceWalk services n t)
    (hnd : (readExps t).Nodup) (e : ℕ) : readCount e t ≤ verifyCount e t :=
  rc_le_vc_of_rvn t h.readVerifyNested (fun q => readCount_le_one q t hnd) e

/-- **The served walk's paths.**  Every read exponent `e` of a served walk with `Nodup` read and
verify exponent lists has one read path `q` and one verify path `q ++ axisPath s.axis`, `s` the
walk's service at `e`. -/
theorem ServiceWalk.paths {n : Noun} {t : MTree K} (h : ServiceWalk services n t) :
    (readExps t).Nodup → (verifyExps t).Nodup →
      ∀ e ∈ readExps t, ∃ s ∈ services, s.exponent = e ∧
        ∃ q, rpaths e t = [q] ∧ vpaths e t = [q ++ axisPath s.axis] := by
  induction h with
  | halt => intro _ _ e he; simp [readExps] at he
  | @decompose nl nr l r hl hr ihl ihr =>
      intro hrnd hvnd e he
      rw [readExps] at hrnd he
      rw [verifyExps] at hvnd
      have hrl : (readExps l).Nodup := hrnd.of_append_left
      have hrr : (readExps r).Nodup := hrnd.of_append_right
      have hvl : (verifyExps l).Nodup := hvnd.of_append_left
      have hvr : (verifyExps r).Nodup := hvnd.of_append_right
      have hrdis : (readExps l).Disjoint (readExps r) := List.disjoint_of_nodup_append hrnd
      have hvdis : (verifyExps l).Disjoint (verifyExps r) := List.disjoint_of_nodup_append hvnd
      rcases List.mem_append.mp he with hel | her
      · obtain ⟨s, hs, hse, q, hq, hv⟩ := ihl hrl hvl e hel
        have hr0 : readCount e r = 0 := by
          rw [readCount_eq_count, List.count_eq_zero_of_not_mem (hrdis hel)]
        have hvl1 : e ∈ verifyExps l := by
          have h1 : 1 ≤ readCount e l := by
            rw [readCount_eq_count]; exact List.count_pos_iff.mpr hel
          have h2 := walk_rc_le_vc hl hrl e
          rw [verifyCount_eq_count] at h2
          exact List.count_pos_iff.mp (by omega)
        have hv0 : verifyCount e r = 0 := by
          rw [verifyCount_eq_count, List.count_eq_zero_of_not_mem (hvdis hvl1)]
        refine ⟨s, hs, hse, false :: q, ?_, ?_⟩
        · simp [Batch554.rpaths, hq, rpaths_eq_nil e r hr0]
        · simp [Batch554.vpaths, hv, vpaths_eq_nil e r hv0]
      · obtain ⟨s, hs, hse, q, hq, hv⟩ := ihr hrr hvr e her
        have hr0 : readCount e l = 0 := by
          rw [readCount_eq_count, List.count_eq_zero_of_not_mem (fun hc => hrdis hc her)]
        have hvr1 : e ∈ verifyExps r := by
          have h1 : 1 ≤ readCount e r := by
            rw [readCount_eq_count]; exact List.count_pos_iff.mpr her
          have h2 := walk_rc_le_vc hr hrr e
          rw [verifyCount_eq_count] at h2
          exact List.count_pos_iff.mp (by omega)
        have hv0 : verifyCount e l = 0 := by
          rw [verifyCount_eq_count, List.count_eq_zero_of_not_mem (fun hc => hvdis hc hvr1)]
        refine ⟨s, hs, hse, true :: q, ?_, ?_⟩
        · simp [Batch554.rpaths, hq, rpaths_eq_nil e l hr0]
        · simp [Batch554.vpaths, hv, vpaths_eq_nil e l hv0]
  | @read n e' c s hs he hroot route below ih =>
      intro hrnd hvnd e hmem
      rw [readExps] at hrnd hmem
      rcases List.mem_cons.mp hmem with rfl | hec
      · obtain ⟨hr0, -, -, -, -, -, -⟩ := route.spec
        refine ⟨s, hs, he, [], ?_, ?_⟩
        · simp [Batch554.rpaths, rpaths_eq_nil _ c hr0]
        · simp [Batch554.vpaths, route_vpaths route]
      · have hne : e' ≠ e := by
          intro hEq
          exact (List.nodup_cons.mp hrnd).1 (hEq ▸ hec)
        obtain ⟨s', hs', hse', q, hq, hv⟩ := ih (List.nodup_cons.mp hrnd).2
          (by rw [verifyExps] at hvnd; exact hvnd) e hec
        refine ⟨s', hs', hse', q, ?_, ?_⟩
        · simp [Batch554.rpaths, hne, hq]
        · simpa [Batch554.vpaths] using hv
  | @verify n e' a c below ih =>
      intro hrnd hvnd e hmem
      rw [readExps] at hrnd hmem
      rw [verifyExps] at hvnd
      have hne : e' ≠ e := by
        intro hEq
        subst hEq
        have hle := walk_rc_le_vc below hrnd e'
        have hrc : 1 ≤ readCount e' c := by
          rw [readCount_eq_count]; exact List.count_pos_iff.mpr hmem
        have hmemv : e' ∈ verifyExps c := by
          rw [verifyCount_eq_count] at hle
          exact List.count_pos_iff.mp (by omega)
        exact (List.nodup_cons.mp hvnd).1 hmemv
      obtain ⟨s', hs', hse', q, hq, hv⟩ := ih hrnd (List.nodup_cons.mp hvnd).2 e hmem
      refine ⟨s', hs', hse', q, ?_, ?_⟩
      · simpa [Batch554.rpaths] using hq
      · simp [Batch554.vpaths, hne, hv]

end Walk

/-! ## C. The certificate of an axis is its descent path -/

/-- `log₂ (a / 2) + 1 = log₂ a` for `a ≥ 2`. -/
theorem log2_div_two_succ {a : ℕ} (h : 2 ≤ a) : (a / 2).log2 + 1 = a.log2 := by
  conv_rhs => rw [Nat.log2_def]
  rw [if_pos (by omega)]

theorem testBit_div_two (a i : ℕ) : (a / 2).testBit i = a.testBit (i + 1) := by
  rw [Nat.testBit_succ]

/-- **The axis path is the MSB-first binary expansion below the leading `1`.** -/
theorem axisPath_eq_ofFn : ∀ a : ℕ, 1 ≤ a →
    axisPath a = List.ofFn (fun i : Fin a.log2 => a.testBit (a.log2 - 1 - i)) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro ha
      by_cases h2 : a < 2
      · have ha1 : a = 1 := by omega
        subst ha1
        rw [axisPath_of_lt_two (by omega)]
        simp [show Nat.log2 1 = 0 by decide]
      · have h2' : 2 ≤ a := by omega
        rw [axisPath_of_two_le h2', ih (a / 2) (by omega) (by omega)]
        have hl := log2_div_two_succ h2'
        set m := (a / 2).log2 with hm
        rw [← hl]
        rw [List.ofFn_succ', List.concat_eq_append]
        congr 1
        · congr 1
          funext i
          simp only [Fin.val_castSucc]
          rw [testBit_div_two]
          congr 1
          have := i.isLt
          omega
        · simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, List.cons.injEq, and_true]
          rw [Nat.testBit_zero]

/-- **`bitsOf` of an axis's certificate is the axis path.** -/
theorem bitsOf_cert_eq_axisPath (a : ℕ) (ha : 1 ≤ a) (c : ℕ → Bool)
    (hc : ∀ k, 1 ≤ k → c k = MemoryTable.formRCertBit a (k - 1)) :
    bitsOf (MemoryTable.formRCertShift a) c = axisPath a := by
  rw [axisPath_eq_ofFn a ha, MemoryTable.formRCertShift_eq_log2]
  unfold Batch554.bitsOf
  congr 1
  funext i
  rw [hc (i.val + 1) (by omega), Nat.add_sub_cancel]
  unfold MemoryTable.formRCertBit
  rw [MemoryTable.formRCertShift_eq_log2, if_pos i.isLt]

/-- The certificate of an axis is padded. -/
theorem padding_cert (n a : ℕ) (c : ℕ → Bool)
    (hc : ∀ k, 1 ≤ k → c k = MemoryTable.formRCertBit a (k - 1)) :
    Padding n (MemoryTable.formRCertShift a) c := by
  intro j hj _
  rw [hc j (by omega)]
  unfold MemoryTable.formRCertBit
  rw [if_neg (by omega)]

/-! ## D. -/

/-- **`formRCounts (rn g t) = 0`** from the tree facts and the certificate match.  `t`: read and
verify exponents `Nodup`, the same support, and every read exponent's paths `q`, `q ++ axisPath a`
with the certificate `(mm, cc)` at `g e` the certificate of `a` (`1 ≤ a`, `log₂ a ≤ n − 1`). -/
theorem formRCounts_rn_zero (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (g : ℕ → ℕ)
    (t : MTree K) (hg : InjOnExps g (fun x => x ∈ exps t))
    (hR : (readExps t).Nodup) (hV : (verifyExps t).Nodup)
    (hsupp : ∀ e, e ∈ readExps t ↔ e ∈ verifyExps t)
    (hpath : ∀ e ∈ readExps t, ∃ a q, 1 ≤ a ∧ a.log2 ≤ n - 1 ∧
      rpaths e t = [q] ∧ vpaths e t = [q ++ axisPath a] ∧
      mm (g e) = MemoryTable.formRCertShift a ∧
      ∀ k, 1 ≤ k → cc (g e) k = MemoryTable.formRCertBit a (k - 1)) :
    formRCounts n mm cc (rn g t) = 0 := by
  classical
  set S : ℕ → Prop := fun x => x ∈ exps t with hSdef
  have hSt : ∀ x ∈ exps t, S x := fun x hx => hx
  -- the localized certificate
  let mm' : ℕ → ℕ := fun x => if x ∈ exps (rn g t) then mm x else 0
  let cc' : ℕ → ℕ → Bool := fun x => if x ∈ exps (rn g t) then cc x else fun _ => false
  have hcongr : formRCounts n mm cc (rn g t) = formRCounts n mm' cc' (rn g t) :=
    formRCounts_congr n mm mm' cc cc' (rn g t) fun x hx => by simp [mm', cc', hx]
  rw [hcongr]
  -- counts transport
  have hcnt : ∀ x, (readCount x (rn g t) = 0 ∧ verifyCount x (rn g t) = 0) ∨
      ∃ e ∈ exps t, g e = x := by
    intro x
    by_cases h : ∃ e ∈ exps t, g e = x
    · exact Or.inr h
    · push Not at h
      exact Or.inl ⟨readCount_rn_out g x t h, verifyCount_rn_out g x t h⟩
  have hU : UniqueExponents (rn g t) := by
    intro x
    rcases hcnt x with ⟨h1, h2⟩ | ⟨e, he, rfl⟩
    · omega
    · rw [readCount_rn g S hg e he t hSt, verifyCount_rn g S hg e he t hSt]
      exact ⟨readCount_le_one e t hR, verifyCount_le_one e t hV⟩
  have hm : ∀ x, mm' x ≤ n - 1 := by
    intro x
    by_cases hx : x ∈ exps (rn g t)
    · simp only [mm', if_pos hx]
      rw [exps_rn] at hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have heR : e ∈ readExps t := by
        simp only [exps, List.mem_append] at he
        rcases he with h | h
        · exact h
        · exact (hsupp e).mpr h
      obtain ⟨a, q, ha, hlog, -, -, hmm, -⟩ := hpath e heR
      rw [hmm, MemoryTable.formRCertShift_eq_log2]; exact hlog
    · simp [mm', hx]
  refine (formR_counts_zero_iff n mm' cc' (rn g t) hU hm).mpr ⟨?_, ?_⟩
  · intro x
    rcases hcnt x with ⟨h1, h2⟩ | ⟨e, he, rfl⟩
    · omega
    · rw [readCount_rn g S hg e he t hSt, verifyCount_rn g S hg e he t hSt,
        readCount_eq_count, verifyCount_eq_count]
      by_cases hr : e ∈ readExps t
      · rw [List.count_eq_one_of_mem hR hr, List.count_eq_one_of_mem hV ((hsupp e).mp hr)]
      · rw [List.count_eq_zero_of_not_mem hr,
          List.count_eq_zero_of_not_mem (fun h => hr ((hsupp e).mpr h))]
  · intro x hx
    rcases hcnt x with ⟨h1, h2⟩ | ⟨e, he, rfl⟩
    · exact absurd hx.1 (by omega)
    · have hr1 : readCount e t = 1 := by
        rw [← readCount_rn g S hg e he t hSt]; exact hx.1
      have heR : e ∈ readExps t := by
        rw [readCount_eq_count] at hr1; exact List.count_pos_iff.mp (by omega)
      obtain ⟨a, q, ha, hlog, hq, hv, hmm, hcc⟩ := hpath e heR
      have hin : g e ∈ exps (rn g t) := by
        rw [exps_rn]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      have hmm' : mm' (g e) = MemoryTable.formRCertShift a := by simp [mm', hin, hmm]
      have hcc' : ∀ k, 1 ≤ k → cc' (g e) k = MemoryTable.formRCertBit a (k - 1) := by
        intro k hk; simp [cc', hin, hcc k hk]
      refine ⟨?_, q, ?_, ?_⟩
      · rw [hmm']; exact padding_cert n a _ hcc'
      · rw [rpaths_rn g S hg e he t hSt]; exact hq
      · rw [vpaths_rn g S hg e he t hSt, hv, hmm', bitsOf_cert_eq_axisPath a ha _ hcc']

end

end Nock.RedTeam.Batch995

#print axioms Nock.RedTeam.Batch995.ServiceWalk.paths
#print axioms Nock.RedTeam.Batch995.bitsOf_cert_eq_axisPath
#print axioms Nock.RedTeam.Batch995.formRCounts_rn_zero
