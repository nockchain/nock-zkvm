/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Bal.lean

  **The cross-table balances as one generic
  multiset identity.**

  * **`Tab`**: one table's side of one LogUp balance: a consumer record list `cons` and a provider list `prov` of
    `(key, multiplicity)` pairs.  `tot f T = Σ_{x ∈ cons} f x − Σ_{(κ,m) ∈ prov} m · f κ`.
  * **`Balanced Ts`** (a list of tables): the provider keys of all tables are duplicate-free, every consumed record
    is provided by some table, and every provider's multiplicity is the number of its consumers over ALL tables.
  * **`tabs_balance`**: `Balanced Ts → Σ_T tot f T = 0`, for every `f` (no pole condition: the identity is a
    rearrangement).  This is the whole multiset identity; it does not fix the number or kind of tables.
  * **Adding a provider/consumer list** (J-9 B claim big-atom records, the J-9 A limb provider): append one table;
    `balanced_append` / `tabs_balance_append` split the identity, and `Balanced` is re-checked on the joint list
    only through `hcnt` (the per-provider counts).
  * **J-8 instance lemmas** (`balG_of_tabs`, `balV_of_tabs`, `balF_of_eq`): the three balance obligations of
    `ComplJ8Obligations` at one coin, from one `Balanced` table list per balance and one equation per public saying
    it is its table's total (`+ tot` on the consumer side, `− tot` on the provider side).  The pin and claim sums
    the verifier computes are tables with a consumer list and no provider (`pinTab`, `claimTab`), proved
    `rfl`-level.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.PinJ8 (pinCons)
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK isPair PairOK hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Module

noncomputable section

/-! ## 1. Counting -/

section Count
variable {α R : Type} [DecidableEq α] [CommRing R]

theorem sum_ite_count (f : α → R) (x : α) : ∀ L : List α,
    (L.map fun κ => if x = κ then f κ else 0).sum = (L.count x : R) * f x
  | [] => by simp
  | y :: L => by
    rw [List.map_cons, List.sum_cons, sum_ite_count f x L, List.count_cons]
    by_cases h : x = y
    · subst h; simp; ring
    · have h2 : (y == x) = false := by simpa using Ne.symm h
      simp [h, h2]

/-- **LogUp counting**: over a duplicate-free key list `L` covering `C`, `Σ_{x ∈ C} f x = Σ_{κ ∈ L} #C(κ) · f κ`. -/
theorem sum_count (f : α → R) (L : List α) (hL : L.Nodup) : ∀ C : List α, (∀ x ∈ C, x ∈ L) →
    (C.map f).sum = (L.map fun κ => (C.count κ : R) * f κ).sum
  | [], _ => by simp
  | x :: C, h => by
    have ih := sum_count f L hL C (fun y hy => h y (by simp [hy]))
    have hx : (L.map fun κ => if x = κ then f κ else 0).sum = f x := by
      rw [sum_ite_count, List.count_eq_one_of_mem hL (h x (by simp))]; simp
    rw [List.map_cons, List.sum_cons, ih, ← hx, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro κ _
    by_cases hk : x = κ
    · subst hk; simp [List.count_cons]; ring
    · have h' : (κ == x) = false := by simpa using Ne.symm hk
      simp [hk, h', List.count_cons]

end Count

/-! ## 2. Tables and the generic multiset identity -/

section Tabs
variable {α R : Type} [DecidableEq α] [CommRing R]

/-- **One table's side of one LogUp balance**: consumed records, and provided keys with their multiplicities. -/
structure Tab (α R : Type) where
  cons : List α
  prov : List (α × R)

/-- The table's total: consumers minus multiplicity-weighted providers. -/
def tot (f : α → R) (T : Tab α R) : R :=
  (T.cons.map f).sum - (T.prov.map fun q => q.2 * f q.1).sum

/-- All consumed records of a table list. -/
def allCons (Ts : List (Tab α R)) : List α := Ts.flatMap Tab.cons

/-- All provider entries of a table list. -/
def allProv (Ts : List (Tab α R)) : List (α × R) := Ts.flatMap Tab.prov

/-- **The balance condition** on a table list: provider keys duplicate-free, every consumed record provided, and
every provider's multiplicity = its number of consumers over all tables. -/
structure Balanced (Ts : List (Tab α R)) : Prop where
  hnd : ((allProv Ts).map Prod.fst).Nodup
  hcov : ∀ x ∈ allCons Ts, x ∈ (allProv Ts).map Prod.fst
  hcnt : ∀ q ∈ allProv Ts, q.2 = ((allCons Ts).count q.1 : R)

theorem sum_tot (f : α → R) (Ts : List (Tab α R)) :
    (Ts.map (tot f)).sum = ((allCons Ts).map f).sum - ((allProv Ts).map fun q => q.2 * f q.1).sum := by
  induction Ts with
  | nil => simp [allCons, allProv]
  | cons T Ts ih =>
    simp only [List.map_cons, List.sum_cons, ih, allCons, allProv, List.flatMap_cons, List.map_append,
      List.sum_append, tot]
    ring

/-- **The multiset identity**: a balanced table list has total zero, for every `f`. -/
theorem tabs_balance (f : α → R) (Ts : List (Tab α R)) (hB : Balanced Ts) : (Ts.map (tot f)).sum = 0 := by
  rw [sum_tot]
  have hP : ((allProv Ts).map fun q => q.2 * f q.1).sum =
      (((allProv Ts).map Prod.fst).map fun κ => ((allCons Ts).count κ : R) * f κ).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    simp [hB.hcnt q hq]
  rw [hP, ← sum_count f _ hB.hnd _ hB.hcov, sub_self]

/-- Appending tables: the identity splits. -/
theorem sum_tot_append (f : α → R) (Ts Us : List (Tab α R)) :
    ((Ts ++ Us).map (tot f)).sum = (Ts.map (tot f)).sum + (Us.map (tot f)).sum := by
  rw [List.map_append, List.sum_append]

/-- A one-table list with no providers and no consumers. -/
theorem balanced_nil : Balanced ([] : List (Tab α R)) :=
  ⟨by simp [allProv], by simp [allCons], by simp [allProv]⟩

/-- **Two balances, two quantities**: if `a = Σ_{T ∈ Ls} tot` and `c = − Σ_{T ∈ Rs} tot` and `Ls ++ Rs` is balanced,
then `a = c`. -/
theorem eq_of_tabs (f : α → R) (Ls Rs : List (Tab α R)) (hB : Balanced (Ls ++ Rs)) (a c : R)
    (ha : a = (Ls.map (tot f)).sum) (hc : c = -(Rs.map (tot f)).sum) : a = c := by
  have h := tabs_balance f _ hB
  rw [sum_tot_append] at h
  rw [ha, hc]
  linear_combination h

end Tabs

/-! ## 3. The verifier-computed consumer tables -/

section Verifier
variable {α R : Type} [DecidableEq α] [CommRing R]

/-- A verifier-computed consumer list as a table (no provider). -/
def consTab (C : List α) : Tab α R := ⟨C, []⟩

theorem tot_consTab (f : α → R) (C : List α) : tot f (consTab (R := R) C) = (C.map f).sum := by
  simp [tot, consTab]

/-- A provider-only table. -/
def provTab (P : List (α × R)) : Tab α R := ⟨[], P⟩

theorem tot_provTab (f : α → R) (P : List (α × R)) :
    tot f (provTab P) = -(P.map fun q => q.2 * f q.1).sum := by
  simp [tot, provTab]


/-- **A chip as one table**: per row, its consumed records and its `(key, multiplicity)` provides. -/
def tabOfRows {ρ : Type} (rows : List ρ) (consR : ρ → List α) (provR : ρ → List (α × R)) : Tab α R :=
  ⟨rows.flatMap consR, rows.flatMap provR⟩

/-- **A chip's row-sum terminal is its table's total**: `Σ_r (Σ_{cons r} f − Σ_{prov r} m · f) = tot`.  Each chip lane
identifies its terminal with this row sum (for J: `termJ_eq`, `termJ_sum_of_mv`). -/
theorem tot_tabOfRows {ρ : Type} (f : α → R) (rows : List ρ) (consR : ρ → List α) (provR : ρ → List (α × R)) :
    (rows.map fun r => ((consR r).map f).sum - ((provR r).map fun q => q.2 * f q.1).sum).sum =
      tot f (tabOfRows rows consR provR) := by
  induction rows with
  | nil => simp [tot, tabOfRows]
  | cons r rows ih =>
    simp only [List.map_cons, List.sum_cons, ih, tot, tabOfRows, List.flatMap_cons, List.map_append,
      List.sum_append]
    ring

/-- The same over a `Fin`-indexed row family. -/
theorem tot_tabOfRows_fin {ρ : Type} {n : ℕ} (f : α → R) (rows : Fin n → ρ) (consR : ρ → List α)
    (provR : ρ → List (α × R)) :
    ∑ i, (((consR (rows i)).map f).sum - ((provR (rows i)).map fun q => q.2 * f q.1).sum) =
      tot f (tabOfRows (List.ofFn rows) consR provR) := by
  rw [← tot_tabOfRows, List.map_ofFn, List.sum_ofFn]
  rfl


/-- A mixed table's total is its consumer part's plus its provider part's. -/
theorem tot_split (f : α → R) (T : Tab α R) : tot f T = tot f (consTab T.cons) + tot f (provTab T.prov) := by
  simp [tot, consTab, provTab, sub_eq_add_neg]

/-- **The honest multiplicities** of a provider key list against a list of consumer lists: each key counted over
ALL consumer lists. -/
def counted (Cs : List (List α)) (P : List α) : List (α × R) := P.map fun κ => (κ, ((Cs.flatten).count κ : R))

/-- **The generic honest balance**: consumer lists `Cs` and provider key lists `Ps` (any number of each); if the
provider keys are duplicate-free and cover every consumed record, then the consumer tables together with the
provider tables at the counted multiplicities are `Balanced`.  Adding a consumer or provider list (a new table)
re-instantiates this lemma; nothing else changes. -/
theorem balanced_counted (Cs Ps : List (List α)) (hnd : Ps.flatten.Nodup)
    (hcov : ∀ x ∈ Cs.flatten, x ∈ Ps.flatten) :
    Balanced (Cs.map (consTab (R := R)) ++ Ps.map fun P => provTab (counted (R := R) Cs P)) := by
  have hC0 : ∀ (A B : List (Tab α R)), allCons (A ++ B) = allCons A ++ allCons B := fun A B => by
    simp [allCons, List.flatMap_append]
  have hP0 : ∀ (A B : List (Tab α R)), allProv (A ++ B) = allProv A ++ allProv B := fun A B => by
    simp [allProv, List.flatMap_append]
  have hC1 : ∀ Ds : List (List α), allCons (Ds.map (consTab (R := R))) = Ds.flatten := by
    intro Ds; induction Ds with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, List.flatten_cons, allCons, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hC2 : ∀ Qs : List (List α), allCons (Qs.map fun P => provTab (counted (R := R) Cs P)) = [] := by
    intro Qs; induction Qs with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, allCons, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hP1 : ∀ Ds : List (List α), allProv (Ds.map (consTab (R := R))) = [] := by
    intro Ds; induction Ds with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, allProv, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hP2 : ∀ Qs : List (List α), allProv (Qs.map fun P => provTab (counted (R := R) Cs P)) =
      Qs.flatten.map fun κ => (κ, ((Cs.flatten).count κ : R)) := by
    intro Qs; induction Qs with
    | nil => rfl
    | cons D Ds ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, allProv, List.flatMap_cons] at ih ⊢
      rw [ih]; rfl
  have hC : allCons (Cs.map (consTab (R := R)) ++ Ps.map fun P => provTab (counted (R := R) Cs P)) = Cs.flatten := by
    rw [hC0, hC1, hC2, List.append_nil]
  have hP : (allProv (Cs.map (consTab (R := R)) ++ Ps.map fun P => provTab (counted (R := R) Cs P))) =
      Ps.flatten.map fun κ => (κ, ((Cs.flatten).count κ : R)) := by
    rw [hP0, hP1, hP2, List.nil_append]
  have hfst : (Ps.flatten.map fun κ => (κ, ((Cs.flatten).count κ : R))).map Prod.fst = Ps.flatten := by
    rw [List.map_map]; exact List.map_id' _
  refine ⟨?_, ?_, ?_⟩
  · rw [hP, hfst]; exact hnd
  · rw [hC, hP, hfst]; exact hcov
  · rw [hP, hC]
    intro q hq
    obtain ⟨κ, -, rfl⟩ := List.mem_map.mp hq
    rfl


/-- A provider list in `(multiplicity, key)` form with `ℕ` multiplicities (the shape of L0's record lists). -/
def provTabN (P : List (ℕ × α)) : Tab α R := ⟨[], P.map fun q => (q.2, (q.1 : R))⟩

/-- **The balance at the data level** (`ℕ` multiplicities, any number of consumer lists `Cs` and provider lists
`Ps`): provider keys duplicate-free, every consumed record provided, and every provider multiplicity is the
number of its consumers over ALL consumer lists. -/
structure BalancedN (Cs : List (List α)) (Ps : List (List (ℕ × α))) : Prop where
  hnd : (Ps.flatten.map Prod.snd).Nodup
  hcov : ∀ x ∈ Cs.flatten, x ∈ Ps.flatten.map Prod.snd
  hcnt : ∀ q ∈ Ps.flatten, q.1 = Cs.flatten.count q.2

/-- **`BalancedN` gives `Balanced`** of the consumer tables followed by the provider tables. -/
theorem balanced_of_N (Cs : List (List α)) (Ps : List (List (ℕ × α))) (hB : BalancedN Cs Ps) :
    Balanced (Cs.map (consTab (R := R)) ++ Ps.map (provTabN (R := R))) := by
  have hC0 : ∀ (A B : List (Tab α R)), allCons (A ++ B) = allCons A ++ allCons B := fun A B => by
    simp [allCons, List.flatMap_append]
  have hP0 : ∀ (A B : List (Tab α R)), allProv (A ++ B) = allProv A ++ allProv B := fun A B => by
    simp [allProv, List.flatMap_append]
  have hC1 : ∀ Ds : List (List α), allCons (Ds.map (consTab (R := R))) = Ds.flatten := by
    intro Ds; induction Ds with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, List.flatten_cons, allCons, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hC2 : ∀ Qs : List (List (ℕ × α)), allCons (Qs.map (provTabN (R := R))) = [] := by
    intro Qs; induction Qs with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, allCons, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hP1 : ∀ Ds : List (List α), allProv (Ds.map (consTab (R := R))) = [] := by
    intro Ds; induction Ds with
    | nil => rfl
    | cons D Ds ih => simp only [List.map_cons, allProv, List.flatMap_cons] at ih ⊢; rw [ih]; rfl
  have hP2 : ∀ Qs : List (List (ℕ × α)), allProv (Qs.map (provTabN (R := R))) =
      Qs.flatten.map fun q => (q.2, (q.1 : R)) := by
    intro Qs; induction Qs with
    | nil => rfl
    | cons D Ds ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append, allProv, List.flatMap_cons] at ih ⊢
      rw [ih]; rfl
  have hC : allCons (Cs.map (consTab (R := R)) ++ Ps.map (provTabN (R := R))) = Cs.flatten := by
    rw [hC0, hC1, hC2, List.append_nil]
  have hP : allProv (Cs.map (consTab (R := R)) ++ Ps.map (provTabN (R := R))) =
      Ps.flatten.map fun q => (q.2, (q.1 : R)) := by
    rw [hP0, hP1, hP2, List.nil_append]
  have hfst : (Ps.flatten.map fun q => (q.2, (q.1 : R))).map Prod.fst = Ps.flatten.map Prod.snd := by
    rw [List.map_map]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hP, hfst]; exact hB.hnd
  · rw [hC, hP, hfst]; exact hB.hcov
  · rw [hP, hC]
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    simp [hB.hcnt q' hq']

/-- **The data-level multiset identity**: `Σ_{C ∈ Cs} Σ_{x ∈ C} f x = Σ_{P ∈ Ps} Σ_{(m,κ) ∈ P} m · f κ`. -/
theorem balanceN (f : α → R) (Cs : List (List α)) (Ps : List (List (ℕ × α))) (hB : BalancedN Cs Ps) :
    (Cs.map fun C => (C.map f).sum).sum = (Ps.map fun P => (P.map fun q => (q.1 : R) * f q.2).sum).sum := by
  have h := tabs_balance f _ (balanced_of_N (R := R) Cs Ps hB)
  rw [sum_tot_append, List.map_map, List.map_map] at h
  have h1 : (tot f ∘ consTab (R := R)) = fun C => (C.map f).sum := by
    funext C; simp [tot_consTab]
  have h2 : (tot f ∘ provTabN (R := R)) = fun P => -(P.map fun q => (q.1 : R) * f q.2).sum := by
    funext P; simp [tot, provTabN, List.map_map, Function.comp_def]
  rw [h1, h2] at h
  have h3 : (Ps.map fun P => -(P.map fun q => (q.1 : R) * f q.2).sum).sum =
      -(Ps.map fun P => (P.map fun q => (q.1 : R) * f q.2).sum).sum := by
    clear h hB h1 h2
    induction Ps with
    | nil => simp
    | cons P Ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [h3] at h
  linear_combination h

end Verifier

/-! ## 4. J-8 instance lemmas: the three balance obligations at one coin -/

section J8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The service-balance denominator (the `hGS` sum's `f`). -/
abbrev fS (χ : Coins frameJ8 K) (x : Fin 8 → K) : 𝕂′ := (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹

/-- The claim-validity denominator (the `hsumC'` sum's `f`). -/
abbrev fV (χ : Coins frameJ8 K) (x : Fin 5 → 𝕂′) : 𝕂′ :=
  (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹

/-- The total of a table list. -/
abbrev tots {α : Type} (f : α → 𝕂′) (Ts : List (Tab α 𝕂′)) : 𝕂′ := (Ts.map (tot f)).sum

/-- **`balG` at one coin (J-8 instance).**  Three balances; every public is the total of its OWN list of tables
(`+` on the consumer side, `−` on the provider side), and each balance's tables, concatenated, are `Balanced`:
the export balance (`ρ₃ + walk export + J export = cell handle provides`, over `f₁`), the path balance
(`ρ₄ = walk path provides`, over `f₂`), the service balance (`ρS + registry pins + J terminal = atom MI +
atom-walk path`, over `fS`; the registry pins are the verifier table `consTab (pinCons …)`).  A new provider or
consumer list is one more table in the list of the public that carries it. -/
theorem balG_of_tabs {α₁ α₂ : Type} [DecidableEq α₁] [DecidableEq α₂] (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (regs : List ℕ) (idx : ℕ → ℕ)
    -- export balance
    (f₁ : α₁ → 𝕂′) (Lρ3 LWx LJx LC : List (Tab α₁ 𝕂′)) (hB1 : Balanced ((Lρ3 ++ LWx ++ LJx) ++ LC))
    (h1ρ : M.ρ 3 = tots δ f₁ Lρ3)
    (h1W : Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) = tots δ f₁ LWx)
    (h1J : Quad.mk _ (M.pubsJ 2) (M.pubsJ 3) = tots δ f₁ LJx)
    (h1C : Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1)) = -tots δ f₁ LC)
    -- path balance
    (f₂ : α₂ → 𝕂′) (Lρ4 LWp : List (Tab α₂ 𝕂′)) (hB2 : Balanced (Lρ4 ++ LWp))
    (h2ρ : M.ρ 4 = tots δ f₂ Lρ4)
    (h2W : Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1)) = -tots δ f₂ LWp)
    -- service balance
    (LρS LJs LA LV : List (Tab (Fin 8 → K) 𝕂′))
    (hB3 : Balanced ((LρS ++ [consTab (pinCons (p := p) (K := K) regs idx)] ++ LJs) ++ (LA ++ LV)))
    (h3ρ : M.ρS = tots δ (fS δ b χ) LρS)
    (h3J : Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) = tots δ (fS δ b χ) LJs)
    (h3A : Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) = -tots δ (fS δ b χ) LA)
    (h3V : Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) = -tots δ (fS δ b χ) LV) :
    M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
      Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1)) ∧
    M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1)) ∧
    M.ρS + ((pinCons (p := p) (K := K) regs idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
      Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_tabs f₁ (Lρ3 ++ LWx ++ LJx) LC hB1 _ _ ?_ h1C
    simp only [List.map_append, List.sum_append, h1ρ, h1W, h1J, tots]; ring
  · exact eq_of_tabs f₂ Lρ4 LWp hB2 _ _ h2ρ h2W
  · refine eq_of_tabs (fS δ b χ) (LρS ++ [consTab (pinCons (p := p) (K := K) regs idx)] ++ LJs) (LA ++ LV) hB3
      _ _ ?_ ?_
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        tot_consTab, h3J, h3ρ, tots, add_zero]
    · rw [h3A, h3V]
      simp only [List.map_append, List.sum_append, tots]
      ring

/-- **`balV` at one coin (J-8 instance).**  The cell-validity balance (the verifier's claim + pin records, a
consumer table, against the cell validity terminal and the atom MB terminal, over `fV`), the atom handle balance
(`atom HQ = atom C + atom-walk X`), and the atom validity terminal (a balanced table list: zero).  Every public is
the total of its own table list. -/
theorem balV_of_tabs {α₄ α₅ : Type} [DecidableEq α₄] [DecidableEq α₅] (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (c : P8PublicClaim) (Pb : PubJ8 p)
    -- cell validity
    (LCv LAb : List (Tab (Fin 5 → 𝕂′) 𝕂′))
    (hB1 : Balanced ([consTab (claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ)] ++ (LCv ++ LAb)))
    (h1C : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) = -tots δ (fV δ χ) LCv)
    (h1A : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1)) =
      -tots δ (fV δ χ) LAb)
    -- atom handle balance
    (f₄ : α₄ → 𝕂′) (LAh LAc LVx : List (Tab α₄ 𝕂′)) (hB2 : Balanced (LAh ++ (LAc ++ LVx)))
    (h2H : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) = tots δ f₄ LAh)
    (h2C : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) =
      -tots δ f₄ LAc)
    (h2V : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1)) =
      -tots δ f₄ LVx)
    -- atom validity terminal
    (f₅ : α₅ → 𝕂′) (T0 : List (Tab α₅ 𝕂′)) (hB3 : Balanced T0)
    (h3 : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 0) (M.pubsA 1) = tots δ f₅ T0) :
    ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1)) ∧
    (M.pubsA 0 = 0 ∧ M.pubsA 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_tabs (fV δ χ) [consTab (claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ)] (LCv ++ LAb) hB1 _ _ ?_ ?_
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tot_consTab, add_zero]
    · rw [h1C, h1A]; simp only [List.map_append, List.sum_append, tots]; ring
  · refine eq_of_tabs f₄ LAh (LAc ++ LVx) hB2 _ _ h2H ?_
    rw [h2C, h2V]; simp only [List.map_append, List.sum_append, tots]; ring
  · have h := tabs_balance f₅ T0 hB3
    rw [show (T0.map (tot f₅)).sum = tots δ f₅ T0 from rfl, ← h3, Quad.mk_eq_zero_iff] at h
    exact h

/-- **`balF` at one coin (J-8 instance).**  The fingerprint-export links: each pair of publics is the same total. -/
theorem balF_of_eq (M : MsgJ8' p K δ) (xC xA : 𝕂′)
    (hC : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) = xC)
    (hW : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1) = xC)
    (hA : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) = xA)
    (hV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1) = xA) :
    (M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1) ∧ (M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1) := by
  have h1 := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsC 2, M.pubsC 3)) (a₂ := (M.pubsW 0, M.pubsW 1))
    (hC.trans hW.symm)
  have h2 := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsA 2, M.pubsA 3)) (a₂ := (M.pubsV 0, M.pubsV 1))
    (hA.trans hV.symm)
  simp only [Prod.mk.injEq] at h1 h2
  exact ⟨h1, h2⟩

end J8

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bal
