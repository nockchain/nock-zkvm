/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestLookups.lean

  Additive; no existing module edited.

  1. `accGatesH_honest`: the 18 accumulator gates (export and path, `e = 3`) of the chip's `ℚ`-template
     (cast into `F`) vanish at row `i` of a prefix-sum fill whose public terminals are the totals
     (the telescope), by `accGates_prefixK` through the cast lemma `accGates_map`.
  2. `slotGate_honest`: a slot gate (the three slot gates are `slots.map slotGate`) vanishes when the
     slot's inverse column is `A / D`, under the pole-free condition `D ≠ 0 ∨ A = 0` (the denominators
     of the active records are not hit by the pole coin: the honest bad event).
  3. `sum_reindex`: the balance content.  A list of consumed records, each the image of a row of a nodup
     closure under an injective key, sums (any `f`) to the multiplicity-weighted sum over the closure, with
     multiplicity `L.count (key n)`: the honest `mh` column of the cell twin.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand
import Nock.NockVMROM.Thm54.VclL.Handle.HonestToys
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL

noncomputable section

/-! ## 1. Evaluation of `𝕂`-gates of the `ℚ` template -/

section EvalM
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Evaluation of a `ℚ`-template mixed gate: base constants are cast into `F`. -/
def evalMQ : MixedExpr ℚ → Env K → Env F → K
  | .Var .traceCur i, eK, _ => eK.trace i
  | .Var .traceNext i, eK, _ => eK.traceNext i
  | .Var .challenge i, eK, _ => eK.chal i
  | .Var .publicVal i, eK, _ => eK.pub i
  | .Lift g, _, eF => algebraMap F K (evalQ g eF)
  | .Scale g u, eK, eF => algebraMap F K (evalQ g eF) * evalMQ u eK eF
  | .Const c, _, _ => (c : K)
  | .Add x y, eK, eF => evalMQ x eK eF + evalMQ y eK eF
  | .Sub x y, eK, eF => evalMQ x eK eF - evalMQ y eK eF
  | .Neg x, eK, eF => - evalMQ x eK eF
  | .Mul x y, eK, eF => evalMQ x eK eF * evalMQ y eK eF
  | .Pow x n, eK, eF => (evalMQ x eK eF) ^ n

theorem eval_mapM_cast (g : MixedExpr ℚ) (eK : Env K) (eF : Env F) :
    (mapM (fun q : ℚ => (q : F)) g).eval eK eF = evalMQ g eK eF := by
  induction g with
  | Var k i => cases k <;> rfl
  | Lift g => simp only [mapM, MixedExpr.eval, evalMQ, eval_mapC_cast]
  | Scale g u ih => simp only [mapM, MixedExpr.eval, evalMQ, eval_mapC_cast, ih]
  | Const c => rfl
  | Add a b iha ihb => simp only [mapM, MixedExpr.eval, evalMQ, iha, ihb]
  | Sub a b iha ihb => simp only [mapM, MixedExpr.eval, evalMQ, iha, ihb]
  | Neg a ih => simp only [mapM, MixedExpr.eval, evalMQ, ih]
  | Mul a b iha ihb => simp only [mapM, MixedExpr.eval, evalMQ, iha, ihb]
  | Pow a n ih => simp only [mapM, MixedExpr.eval, evalMQ, ih]

theorem evalMQ_sumM (l : List (MixedExpr ℚ)) (eK : Env K) (eF : Env F) :
    evalMQ (sumM l) eK eF = (l.map fun g => evalMQ g eK eF).sum := by
  induction l with
  | nil => simp [sumM, evalMQ]
  | cons a l ih => simp only [sumM, List.foldr_cons, evalMQ] at ih ⊢; simp [ih]

theorem evalQ_sumListQ {ι : Type} (l : List ι) (f : ι → CoeffExpr ℚ) (env : Env F) :
    evalQ (CoeffExpr.sumList l f) env = (l.map fun i => evalQ (f i) env).sum := evalQ_sumList l f env

/-- **The value of a slot gate**: `inv · D − A`, with `D = Σ act·den (+ pr·den_a·den_b)` and
`A = Σ act (+ pr·(den_a + den_b))`. -/
theorem evalMQ_slotGate (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) :
    evalMQ (slotGate S) eK eF =
      eK.trace S.inv *
        ((S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
          (match S.pair with
           | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
           | none => 0)) -
      (algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
        (match S.pair with
         | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
         | none => 0)) := by
  unfold slotGate
  cases hp : S.pair with
  | none =>
    simp [evalMQ, evalMQ_sumM, List.map_map, Function.comp_def, evalQ_sumList]
  | some p =>
    obtain ⟨fl, a, b⟩ := p
    simp [evalMQ, evalMQ_sumM, List.map_map, Function.comp_def, evalQ_sumList]

/-- **Slot gate at honest values.**  If the inverse column holds `A / D` and the denominators are
pole-free (`D ≠ 0` or `A = 0`), the slot gate vanishes. -/
theorem slotGate_honest (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (D A : K)
    (hD : D = (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
          (match S.pair with
           | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
           | none => 0))
    (hA : A = algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
        (match S.pair with
         | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
         | none => 0))
    (hinv : eK.trace S.inv = A * D⁻¹) (hpole : D ≠ 0 ∨ A = 0) :
    evalMQ (slotGate S) eK eF = 0 := by
  rw [evalMQ_slotGate, ← hD, ← hA, hinv]
  rcases hpole with h | h
  · rw [mul_assoc, inv_mul_cancel₀ h, mul_one, sub_self]
  · rw [h]; simp

/-- NC: a wrong inverse (`A/D + 1`) at a non-zero `D` fails the slot gate. -/
theorem slotGate_wrong_inverse (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (D A : K)
    (hD : D = (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
          (match S.pair with
           | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
           | none => 0))
    (hA : A = algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
        (match S.pair with
         | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
         | none => 0))
    (hinv : eK.trace S.inv = A * D⁻¹ + 1) (hD0 : D ≠ 0) :
    evalMQ (slotGate S) eK eF ≠ 0 := by
  rw [evalMQ_slotGate, ← hD, ← hA, hinv]
  have : (A * D⁻¹ + 1) * D - A = D := by field_simp; ring
  rw [this]; exact hD0

end EvalM

/-! ## 2. The accumulator gates at a prefix-sum fill -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem mapC_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr ℚ) :
    mapC (fun q : ℚ => (q : F)) (CoeffExpr.sumList l f) =
      CoeffExpr.sumList l (fun i => mapC (fun q : ℚ => (q : F)) (f i)) := by
  induction l with
  | nil => simp [CoeffExpr.sumList, mapC]
  | cons a l ih => simp only [CoeffExpr.sumList, List.foldr_cons, mapC] at ih ⊢; rw [ih]

theorem sumList_map {ι κ : Type} (l : List ι) (g : ι → κ) (f : κ → CoeffExpr F) :
    CoeffExpr.sumList (l.map g) f = CoeffExpr.sumList l (fun i => f (g i)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [CoeffExpr.sumList, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih]

/-- The cast slots of the `ℚ`-template. -/
def castSlot (s : Slot ℚ) : Slot F := ⟨mapC (fun q : ℚ => (q : F)) s.act, s.invBase⟩

theorem mapC_termCoord (slots : List (Slot ℚ)) (k : ℕ) :
    mapC (fun q : ℚ => (q : F)) (termCoord slots k) = termCoord (slots.map castSlot) k := by
  simp only [termCoord]
  rw [mapC_sumList, sumList_map]
  rfl

theorem mapC_accStep (slots : List (Slot ℚ)) (a k : ℕ) :
    mapC (fun q : ℚ => (q : F)) (accStepGate slots a k) = accStepGate (slots.map castSlot) a k := by
  simp only [accStepGate, mapC, mapC_termCoord, Rat.cast_one]

theorem mapC_accTerm (slots : List (Slot ℚ)) (a p k : ℕ) :
    mapC (fun q : ℚ => (q : F)) (accTermGate slots a p k) =
      accTermGate (slots.map castSlot) a p k := by
  simp only [accTermGate, mapC, mapC_termCoord]

/-- The cast of an accumulator-gate list is the accumulator-gate list of the cast slots. -/
theorem accGates_map (e : ℕ) (slots : List (Slot ℚ)) (a p : ℕ) :
    (accGates e slots a p).map (mapC (fun q : ℚ => (q : F))) =
      accGates e (slots.map castSlot) a p := by
  simp only [accGates, List.map_append, List.map_map, Function.comp_def, mapC_accStep,
    mapC_accTerm]
  rfl

/-- The export-side slots (cast): the term of the export accumulator is `Σ actX · inv`. -/
def slotsX : List (Slot F) :=
  ((slots : List (SlotSpec ℚ)).map fun S => (⟨S.actX, S.inv⟩ : Slot ℚ)).map castSlot
def slotsP : List (Slot F) :=
  ((slots : List (SlotSpec ℚ)).map fun S => (⟨S.actP, S.inv⟩ : Slot ℚ)).map castSlot

/-- **The 18 accumulator gates of `computeChipVCLH` at row `i` of a prefix-sum fill** (export: `accX` /
public `pubRhoX`; path: `accP` / `pubRhoP`; `e = 3`).  The accumulator limbs hold the exclusive prefix sums
of the per-row terms, the publics the totals (the telescope).  Through `accGates_map` and
`accGates_prefixK`; no hypothesis beyond the fill itself. -/
theorem accGatesH_honest (b : Basis (Fin 3) F K) (N i : ℕ) (hi : i < N) (envs : ℕ → Env F)
    (rx rp : K)
    (h11 : (envs i).trace 11 = if i = 0 then 1 else 0)
    (h12 : (envs i).trace 12 = if i + 1 = N then 1 else 0)
    (hrx : ∑ j ∈ Finset.range N, termVal b (slotsX (F := F)) (envs j) = rx)
    (hrp : ∑ j ∈ Finset.range N, termVal b (slotsP (F := F)) (envs j) = rp)
    (haX : ∀ k : Fin 3, (envs i).trace (accX + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsX (F := F)) (envs j)) k)
    (haXn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accX + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsX (F := F)) (envs j)) k)
    (haP : ∀ k : Fin 3, (envs i).trace (accP + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsP (F := F)) (envs j)) k)
    (haPn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accP + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsP (F := F)) (envs j)) k)
    (hpx : ∀ k : Fin 3, (envs i).pub (pubRhoX + k) = coord b rx k)
    (hpp : ∀ k : Fin 3, (envs i).pub (pubRhoP + k) = coord b rp k) :
    ∀ g ∈ (accGatesH : List (CoeffExpr ℚ)).map (mapC (fun q : ℚ => (q : F))),
      g.eval (envs i) = 0 := by
  intro g hg
  simp only [accGatesH, List.map_append, accGates_map, List.mem_append] at hg
  rcases hg with hg | hg
  · exact accGates_prefixK b _ accX pubRhoX N i hi envs rx h11 h12 haX haXn hpx hrx g hg
  · exact accGates_prefixK b _ accP pubRhoP N i hi envs rp h11 h12 haP haPn hpp hrp g hg

/-- NC: a terminal off by one fails the export terminal gate on the last row (so the gates do
discriminate). -/
theorem accGatesH_wrong_terminal (E : Env F) (hF : (1 : F) ≠ 0)
    (h12 : E.trace 12 = 1)
    (hpub : E.pub (pubRhoX + 0) = E.trace (accX + 0) + (termCoord (slotsX (F := F)) 0).eval E + 1) :
    ∃ g ∈ (accGatesH : List (CoeffExpr ℚ)).map (mapC (fun q : ℚ => (q : F))), g.eval E ≠ 0 := by
  simp only [accGatesH, List.map_append, accGates_map, List.mem_append]
  obtain ⟨g, hg, hne⟩ := accTerm_rejects_wrong_terminal 3 (slotsX (F := F)) accX pubRhoX E hF 0
    (by norm_num) h12 hpub
  exact ⟨g, Or.inl hg, hne⟩

end Acc

/-! ## 3. Balance content: the multiplicity reindexing -/

section Balance
variable {α M : Type} [AddCommMonoid M] [BEq α] [LawfulBEq α]

/-- **The honest `mh` multiplicity**: a list `L` of consumed records, each the image of a row of the
nodup closure `cells` under a key that is injective on `cells`, sums (any weight `f`) to the closure
sum weighted by `L.count (key n)`. -/
theorem sum_reindex (cells : List Noun) (hnd : cells.Nodup) (key : Noun → α)
    (hinj : ∀ a ∈ cells, ∀ b ∈ cells, key a = key b → a = b) (f : α → M) :
    ∀ L : List α, (∀ x ∈ L, ∃ n ∈ cells, key n = x) →
      (L.map f).sum = (cells.map fun n => (L.count (key n)) • f (key n)).sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro hL
    obtain ⟨n0, hn0, hx⟩ := hL x (by simp)
    have ih' := ih (fun y hy => hL y (by simp [hy]))
    have hsplit : (cells.map fun n => ((x :: L).count (key n)) • f (key n)).sum =
        (cells.map fun n => (L.count (key n)) • f (key n)).sum + f x := by
      have h1 : ∀ n ∈ cells, ((x :: L).count (key n)) • f (key n) =
          (L.count (key n)) • f (key n) + (if n = n0 then f x else 0) := by
        intro n hn
        rw [List.count_cons]
        by_cases hk : key n = x
        · have : n = n0 := hinj n hn n0 hn0 (hk.trans hx.symm)
          subst this
          simp [hk, add_smul]
        · have : n ≠ n0 := fun h => hk (h ▸ hx)
          have hk' : ¬ x = key n := fun h => hk h.symm
          simp [hk', this]
      rw [List.map_congr_left h1, List.sum_map_add]
      congr 1
      rw [← List.sum_toFinset _ hnd]
      simp [hn0]
    rw [hsplit, ← ih']
    simp [add_comm]

end Balance

/-! ## 4. The export records the VS compute side consumes are keys of closure rows -/

section Export
variable {F : Type} [Field F]

/-- The export key of a closure noun: `(serial, handle of head, handle of tail)`. -/
def expKey (cells : List Noun) (n : Noun) : F × (F × F) × (F × F) :=
  ((cells.idxOf n : F), hdl cells (hdN n), hdl cells (tlN n))

/-- **The export records of a VS compute row** (`slots`: L1 `f`, L2 `f_t`, L3 `f_tt` (OP6), cons `e`,
OP8 `m`, OP3 cell witness), as `(parent, left, right)` nouns.  The OP3 witness children are
`hdN sf1 / tlN sf1`: the hosted `f_tth / f_ttt` columns must hold these (see FINDING). -/
def exportEntries (r : RowN) : List (Noun × Noun × Noun) :=
  [(r.f, r.fh, r.ft)] ++
  (if r.op = 2 ∨ r.op = 5 ∨ r.op = 6 ∨ r.op = 7 ∨ r.op = 8 ∨ r.op = 9 then [(r.ft, r.fth, r.ftt)] else []) ++
  (if r.op = 6 then [(r.ftt, r.ftth, r.fttt)] else []) ++
  (if r.op = 10 then [(r.e, r.sf1, r.sf2)] else []) ++
  (if r.op = 8 then [(r.m, r.sf2, r.s)] else []) ++
  (if r.op = 3 ∧ r.sf1.isCell = true then [(r.sf1, hdN r.sf1, tlN r.sf1)] else [])

/-- The consumed record of an entry. -/
def entryRec (cells : List Noun) (x : Noun × Noun × Noun) : F × (F × F) × (F × F) :=
  ((cells.idxOf x.1 : F), hdl cells x.2.1, hdl cells x.2.2)

/-- **Each export entry of a semantically valid row is a cell split `p = [l r]`.** -/
theorem cell_eta (a : Noun) (h : a.isCell = true) : a = .cell (hdN a) (tlN a) := by
  cases a with
  | atom _ => simp [Noun.isCell] at h
  | cell _ _ => rfl

theorem exportEntries_cell (r : RowN) (hs : r.Sem) :
    ∀ x ∈ exportEntries r, x.1 = .cell x.2.1 x.2.2 := by
  unfold RowN.Sem at hs
  unfold exportEntries
  have hle : r.op ≤ 10 := by
    by_contra h
    split at hs <;> first | exact hs | omega
  revert hs
  generalize r.op = op at hle ⊢
  intro hs
  interval_cases op <;> simp_all [hdN, tlN]
  all_goals (intro hc; exact cell_eta _ hc)

/-- Each entry's consumed record is the export key of its parent. -/
theorem entryRec_eq_expKey (cells : List Noun) (r : RowN) (hs : r.Sem) :
    ∀ x ∈ exportEntries r, (entryRec cells x : F × (F × F) × (F × F)) = expKey cells x.1 := by
  intro x hx
  have hc := exportEntries_cell r hs x hx
  obtain ⟨p, l, rr⟩ := x
  simp only at hc
  subst hc
  simp [entryRec, expKey, hdN, tlN]

/-- The parent of every export entry is one of the twelve handle nouns of the effective row. -/
theorem entry_parent_mem (r : RowN) :
    ∀ x ∈ exportEntries r, x.1 ∈ rowHandleNouns (hn r) := by
  intro x hx
  by_cases h5 : r.op = 5
  · simp [exportEntries, h5] at hx
    simp [rowHandleNouns, hn, h5]
    rcases hx with rfl | rfl <;> simp
  · rw [hn_of_ne r h5]
    simp only [exportEntries, List.mem_append, List.mem_ite_nil_right,
      rowHandleNouns, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with (((((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp

/-- **The export side balances.**  Every export record the VS compute rows consume is the key of a row of
the extended-demand table; the keys are injective on the table (serial = closure position, `n < char F`);
so the consumed multiset reindexes onto the table, with the honest multiplicity `mh n = count of the
consumed records equal to the key of n`.  Whatever the weight `f` (in particular `1/den`), the compute total
of the export accumulator equals the cell twin's `mh`-weighted provided total. -/
theorem export_balance {M : Type} [AddCommMonoid M] [DecidableEq F]
    {K : Type} [Field K] (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem)
    (hlen : (demandH rows).cells.length < ringChar F) (f : F × (F × F) × (F × F) → M) :
    ((rows.flatMap fun g => (exportEntries (rowOfSkel g.skel)).map
        (entryRec (F := F) (demandH rows).cells)).map f).sum =
      ((demandH rows).cells.map fun n =>
        ((rows.flatMap fun g => (exportEntries (rowOfSkel g.skel)).map
            (entryRec (F := F) (demandH rows).cells)).count (expKey (demandH rows).cells n)) •
          f (expKey (demandH rows).cells n)).sum := by
  refine sum_reindex (demandH rows).cells (closureOf_nodup _) (expKey (demandH rows).cells) ?_ f _ ?_
  · intro a ha b hb h
    have h1 := congrArg Prod.fst h
    simp only [expKey] at h1
    have hia := List.idxOf_lt_length_iff.mpr ha
    have hib := List.idxOf_lt_length_iff.mpr hb
    exact (honest_handle_eq_iff (demandH rows) ha hb).mp
      (cast_inj_of_lt (hia.trans hlen) (hib.trans hlen) h1)
  · intro x hx
    simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨g, hg, e, he, rfl⟩ := hx
    have hcell := exportEntries_cell _ (hsem g hg) e he
    refine ⟨e.1, handle_cells_mem rows hg e.1 (entry_parent_mem _ e he) (by rw [hcell]; rfl), ?_⟩
    exact (entryRec_eq_expKey _ _ (hsem g hg) e he).symm

/-- **Every row of a run's BFS is semantically valid** (the discharge of `hsem` for a run). -/
theorem run_rows_sem {K : Type} [Field K] {fuel : ℕ} {subject formula result : Noun}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows (airReorder t), (rowOfSkel g.skel).Sem := by
  intro g hg
  unfold bfsRows at hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ u).mp hu
  simp only [List.mem_singleton] at hc
  subst hc
  exact airReorder_rowShape h u hin

/-- The OP3 slot-2 record `(sf1_e; f_tth, f_ttt)` is then NOT the export key of
`sf1` (here `sf1 = [1 2]`), so the honest OP3 row must host `hdN sf1 / tlN sf1` there (no base gate
reads these columns on OP3; `exportEntries` uses the corrected values). -/
theorem op3_witness_unhosted :
    (entryRec [Noun.cell (.atom 1) (.atom 2)]
        (Noun.cell (.atom 1) (.atom 2), Noun.atom 0, Noun.atom 0) : Z67 × (Z67 × Z67) × (Z67 × Z67)) ≠
      expKey [Noun.cell (.atom 1) (.atom 2)] (Noun.cell (.atom 1) (.atom 2)) := by
  decide

end Export

end

end Nock.NockVMROM.Thm54.VclL.Handle
