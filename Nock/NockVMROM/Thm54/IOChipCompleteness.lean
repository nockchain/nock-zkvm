import Nock.NockVMROM.Thm54.IOChipSoundness
import Nock.NockVMROM.Thm54.TraceEncoding
import Mathlib.Tactic.NormNum.Prime

/-!
# AIR-level completeness of the `K`-valued IO chip

`Nock/NockVMROM/Thm54/IOChipSoundness.lean` proves the hostile direction: an arbitrary pair of
committed polynomial traces satisfying the kind-segmented ordinary RAPs of the two `K`-valued IO
chips implies the record-level IO language `IO.LIO` (`io_lio_of_satisfies`).  That theorem is an
implication, and `hypotheses_inhabited` only shows its hypothesis bundle is non-empty at a
hand-built *two-row* deployment.  What was missing is the converse at the AIR level: given
`IO.LIO`, an honest prover can actually *produce* committed polynomial columns which satisfy those
same RAPs, at the real record length.  Without it the chip could in principle be
unsatisfiable-in-practice.

This module supplies that existence theorem.

## What is reused, and what the new step is

* **Record-level completeness is already proved.**  `FiniteIO.finiteIO_complete_of_LIO`
  (`FiniteFieldIO.lean:246`) turns `IO.LIO` plus the pole-miss condition into a
  `PostChallengeIOWitness` satisfying `FiniteIOAccepts`.  Every accumulator, reciprocal and
  multiplicity value used below is read off *that* witness; no accumulator is reconstructed here.
* **The soundness module's gate-evaluation lemmas are equations, not implications**
  (`IOChipSoundness.lean:100`-`:156`), so they run in this direction unchanged.  `rowEnv`,
  `rowPt`, `ChipRows` and `ChipAgreement` are the soundness module's own definitions, used
  verbatim, so the columns produced here are exactly the objects `io_lio_of_satisfies` consumes.
* **The row geometry is the certified orbit prefix.**  `Framework.Thm54.OrbitDomain` supplies
  node injectivity below the certified capacity (`orbitPoint_injective`), the three per-kind
  domains, and — through `orbit_mem_transitionDomain_iff_active_nonterminal`
  (`Thm54/TraceEncoding.lean:29`) — the fact that the transition domain contains *exactly* the
  non-terminal active rows.  That last `iff` is what makes the per-kind vanishing obligations
  discharge: a transition gate has to vanish on every point of its domain, so the domain must not
  contain the terminal row.
* **The genuinely new step is the interpolation/encoding step**: `encodeCells` is the
  column-by-column Lagrange interpolant of the row values through the orbit nodes, mirroring
  `NockVMROM.TraceEncoding.encodeComputeTrace` (`:176`) and
  `PlusIOSegmentedRAP.encodeEnvTrace` (`:637`) but at the chip's own width and without importing
  the exact-configuration stack.

## Why the flat AIR is not attempted

Imposing `ioAccInit` and `ioProgAccStep` on the *same* rows forces `inv = 0`, contradicting
`ioInvPin`, so a flat `airToRAP` over the whole IO AIR is unsatisfiable.  The
deployment built here is therefore kind-segmented: `.boundary` on the first row only,
`.transition` on the `n` record rows only, `.terminal` on the extra `n`-th row only.

## The carried hypotheses, and why each is honest

* `hcap : records.requests.length + 1 ≤ 2 ^ D.h` — the orbit must be long enough for the `n`
  record rows plus the terminal accumulator row.  This is the row-count side condition the M1
  target statement already carries (`horb`), not a weakening: with a shorter orbit the row points
  collide and there is no injective node set to interpolate through.
* `hden : ∀ v ∈ requests ++ responses, compress coins v ≠ 0` — the sampled pole must miss every
  compressed record.  `ioInvPin` *forces* the reciprocal column to be a genuine inverse, so
  completeness cannot hold without it; it is exactly `finiteIO_complete_of_LIO`'s own hypothesis
  and exactly counted event (1) of the soundness analysis
  (`FiniteFieldIOSoundness.IOPoleHitEvent`).  `hypotheses_inhabited` carries the same condition as
  `hne`.

Both are conditions on the *deployment and the coins*, not on the program, and neither weakens the
conclusion: the conclusion is an existence statement about polynomial assignments.

## Non-vacuity

`completeness_hypotheses_inhabited` shows the hypothesis bundle holds at any orbit domain with
`1 ≤ D.h`, any coins and any single record with a nonzero compressed denominator;
`satisfies_of_io_lio_concrete` then instantiates the whole chain at `ZMod 97` with a genuinely
non-empty record list, so the conclusion is inhabited at a chip with a real record row.
-/

namespace Nock.NockVMROM.Thm54.IOChip

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open scoped BigOperators Polynomial

variable {K : Type*} [Field K] {m : ℕ}

/-! ## 1. The interpolation encoder

Column `j` of the committed trace is the Lagrange interpolant of the `j`-th row value through the
row nodes.  This is the step from *vanishing gates* to *satisfying polynomial columns*. -/

/-- **The committed trace of a table of row values.**  Column `j` interpolates
    `i ↦ cells i j` through the nodes.  Same construction as
    `NockVMROM.TraceEncoding.encodeComputeTrace` (`:176`), at an arbitrary width. -/
noncomputable def encodeCells {n : ℕ} (w : ℕ) (nodes : Fin n → K) (cells : Fin n → ℕ → K) :
    Fin w → K[X] :=
  fun j => Lagrange.interpolate Finset.univ nodes (fun i => cells i (j : ℕ))

/-- Eval-at-node for `encodeCells`: at node `i`, column `j` returns row `i`'s value. -/
theorem encodeCells_eval_at_node {n : ℕ} (w : ℕ) (nodes : Fin n → K) (cells : Fin n → ℕ → K)
    (hnodes : Function.Injective nodes) (i : Fin n) (j : Fin w) :
    (encodeCells w nodes cells j).eval (nodes i) = cells i (j : ℕ) :=
  Lagrange.eval_interpolate_at_node (fun i => cells i (j : ℕ)) hnodes.injOn (Finset.mem_univ i)

/-- **The soundness module's row read, on an interpolated trace.**  `rowEnv`'s current-row read at
    row `i` returns exactly the tabulated value, provided the nodes are the deployment's row
    points. -/
theorem rowEnv_trace_encodeCells {n w : ℕ} (q : SegmentedRAPParams K) (x₀ : K)
    (nodes : Fin n → K) (cells : Fin n → ℕ → K) (hnodes : Function.Injective nodes)
    (hnode : ∀ i : Fin n, nodes i = rowPt q.ω x₀ (i : ℕ))
    (i : Fin n) (j : ℕ) (hj : j < w) :
    (rowEnv q x₀ (encodeCells w nodes cells) (i : ℕ)).trace j = cells i j := by
  rw [rowEnv_trace_eq q x₀ (encodeCells w nodes cells) (i : ℕ) j hj, ← hnode i]
  exact encodeCells_eval_at_node w nodes cells hnodes i ⟨j, hj⟩

/-! ## 2. The chip's row values

The column layout is `FiniteFieldIOAIR.lean`'s: `acc`, `inv`, `mult`, `multInv`, then the `m`
record columns at offset `4`. -/

/-- **One row of the chip, as a function of the column index.**  All four scalar columns and the
    record vector are `ℕ`-indexed; the terminal row's non-accumulator entries are irrelevant
    (no gate is deployed there) and are supplied by the same functions. -/
noncomputable def chipCell (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin m → K)
    (i j : ℕ) : K :=
  if j = 0 then acc i
  else if j = 1 then inv i
  else if j = 2 then mult i
  else if j = 3 then multInv i
  else if hj : 4 ≤ j ∧ j - 4 < m then recs i ⟨j - 4, hj.2⟩
  else 0

section Cells

variable (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin m → K) (i : ℕ)

theorem chipCell_acc : chipCell acc inv mult multInv recs i 0 = acc i := by
  simp [chipCell]

theorem chipCell_inv : chipCell acc inv mult multInv recs i 1 = inv i := by
  simp [chipCell]

theorem chipCell_mult : chipCell acc inv mult multInv recs i 2 = mult i := by
  simp [chipCell]

theorem chipCell_multInv : chipCell acc inv mult multInv recs i 3 = multInv i := by
  simp [chipCell]

theorem chipCell_rec (c : Fin m) :
    chipCell acc inv mult multInv recs i (4 + (c : ℕ)) = recs i c := by
  have h0 : ¬ (4 + (c : ℕ) = 0) := by omega
  have h1 : ¬ (4 + (c : ℕ) = 1) := by omega
  have h2 : ¬ (4 + (c : ℕ) = 2) := by omega
  have h3 : ¬ (4 + (c : ℕ) = 3) := by omega
  have h4 : 4 ≤ 4 + (c : ℕ) ∧ 4 + (c : ℕ) - 4 < m := ⟨by omega, by have := c.isLt; omega⟩
  simp only [chipCell, if_neg h0, if_neg h1, if_neg h2, if_neg h3, dif_pos h4]
  exact congrArg (recs i) (Fin.ext (show 4 + (c : ℕ) - 4 = (c : ℕ) from by omega))

end Cells

/-! ## 3. The deployment and the committed trace -/

/-- **The kind-segmented deployment of one IO chip on an orbit prefix of `n + 1` rows.**
    `.boundary` sits on the first row, `.transition` on the `n` record rows (the orbit prefix with
    its last point erased), `.terminal` on the extra row `n`.  The `.row` segment is empty: the
    chip has no row-local gates. -/
noncomputable def chipParams (D : OrbitDomain K) (coins : IOCoins K) (terminal : K)
    (n : ℕ) : SegmentedRAPParams K where
  chalVal := fun j => if j = 0 then coins.gamma else if j = 1 then coins.pole else 0
  pubVal := fun _ => terminal
  eDeg := 1
  hExp := D.h + 1
  ω := D.ω
  βcoset := D.βcoset
  domain := fun k => match k with
    | .boundary => D.boundaryDomain
    | .transition => D.transitionDomain (n + 1) (Nat.succ_pos n)
    | .terminal => D.terminalDomain (n + 1) (Nat.succ_pos n)
    | .row => ∅
  βcoset_ne_zero := D.βcoset_ne_zero
  hExp_pos := Nat.le_add_left 1 D.h

/-- **The committed trace of one IO chip.**  `n + 1` rows interpolated through the orbit prefix
    based at `D.βcoset`. -/
noncomputable def chipTrace (D : OrbitDomain K) (n : ℕ) (acc inv mult multInv : ℕ → K)
    (recs : ℕ → Fin m → K) : Fin (m + 4) → K[X] :=
  encodeCells (m + 4) (fun i : Fin (n + 1) => D.orbitPoint (i : ℕ))
    (fun i => chipCell acc inv mult multInv recs (i : ℕ))

theorem chipTrace_def (D : OrbitDomain K) (n : ℕ) (acc inv mult multInv : ℕ → K)
    (recs : ℕ → Fin m → K) :
    chipTrace D n acc inv mult multInv recs
      = encodeCells (m + 4) (fun i : Fin (n + 1) => D.orbitPoint (i : ℕ))
          (fun i => chipCell acc inv mult multInv recs (i : ℕ)) := rfl

section Deployment

variable (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (n : ℕ)

theorem chipParams_omega : (chipParams D coins terminal n).ω = D.ω := rfl

theorem chipParams_gamma : (chipParams D coins terminal n).chalVal 0 = coins.gamma := rfl

theorem chipParams_pole : (chipParams D coins terminal n).chalVal 1 = coins.pole := rfl

theorem chipParams_pub : (chipParams D coins terminal n).pubVal 0 = terminal := rfl

theorem chipParams_domain_boundary :
    (chipParams D coins terminal n).domain .boundary = D.boundaryDomain := rfl

theorem chipParams_domain_transition :
    (chipParams D coins terminal n).domain .transition
      = D.transitionDomain (n + 1) (Nat.succ_pos n) := rfl

theorem chipParams_domain_terminal :
    (chipParams D coins terminal n).domain .terminal
      = D.terminalDomain (n + 1) (Nat.succ_pos n) := rfl

/-- The deployment's `i`-th row point is the `i`-th orbit point. -/
theorem chipRowPt (i : ℕ) :
    rowPt (chipParams D coins terminal n).ω D.βcoset i = D.orbitPoint i := by
  show D.ω ^ i * D.βcoset = D.βcoset * D.ω ^ i
  exact mul_comm _ _

/-- The terminal row of an `n + 1`-row prefix is orbit point `n`. -/
theorem terminalPoint_succ :
    D.terminalPoint (n + 1) (Nat.succ_pos n) = D.orbitPoint n := by
  simp only [OrbitDomain.terminalPoint, OrbitDomain.lastIndex]
  rfl

end Deployment

/-! ## 4. Reading the committed trace back -/

section Read

variable (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) {n : ℕ}
  (acc inv mult multInv : ℕ → K) (recs : ℕ → Fin m → K)

/-- **Every committed column reads back its tabulated row value**, at every row of the prefix. -/
theorem chipTrace_read (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) (j : ℕ)
    (hj : j < m + 4) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace j
      = chipCell acc inv mult multInv recs i j := by
  have h := rowEnv_trace_encodeCells (w := m + 4) (chipParams D coins terminal n) D.βcoset
    (fun i : Fin (n + 1) => D.orbitPoint (i : ℕ))
    (fun i : Fin (n + 1) => chipCell acc inv mult multInv recs (i : ℕ))
    (D.orbitPoint_injective hcap)
    (fun i => (chipRowPt D coins terminal n (i : ℕ)).symm) ⟨i, hi⟩ j hj
  exact h

theorem chipTrace_acc (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace 0 = acc i := by
  rw [chipTrace_read D coins terminal acc inv mult multInv recs hcap i hi 0 (by omega),
    chipCell_acc]

theorem chipTrace_inv (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace 1 = inv i := by
  rw [chipTrace_read D coins terminal acc inv mult multInv recs hcap i hi 1 (by omega),
    chipCell_inv]

theorem chipTrace_mult (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace 2 = mult i := by
  rw [chipTrace_read D coins terminal acc inv mult multInv recs hcap i hi 2 (by omega),
    chipCell_mult]

theorem chipTrace_multInv (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace 3 = multInv i := by
  rw [chipTrace_read D coins terminal acc inv mult multInv recs hcap i hi 3 (by omega),
    chipCell_multInv]

theorem chipTrace_rec (hcap : n + 1 ≤ 2 ^ D.h) (i : ℕ) (hi : i < n + 1) (c : Fin m) :
    (rowEnv (chipParams D coins terminal n) D.βcoset
        (chipTrace D n acc inv mult multInv recs) i).trace (4 + (c : ℕ)) = recs i c := by
  have hj : 4 + (c : ℕ) < m + 4 := by have := c.isLt; omega
  rw [chipTrace_read D coins terminal acc inv mult multInv recs hcap i hi _ hj, chipCell_rec]

end Read

/-! ## 5. The chip-level completeness core

Given `ℕ`-indexed honest columns satisfying the scalar gate equations on the `n` record rows, the
interpolated trace satisfies both chips' kind-segmented ordinary RAPs, the row-domain deployment
condition, and the committed-column agreement. -/

/-- The `ℕ`-indexed view of a `Fin`-indexed committed column. -/
noncomputable def natOfFin {N : ℕ} (f : Fin N → K) (i : ℕ) : K :=
  if h : i < N then f ⟨i, h⟩ else 0

theorem natOfFin_apply {N : ℕ} (f : Fin N → K) (i : Fin N) : natOfFin f (i : ℕ) = f i := by
  rw [natOfFin, dif_pos i.isLt]

/-- The `ℕ`-indexed view of a committed record list. -/
noncomputable def listCol (l : List (Fin m → K)) (i : ℕ) : Fin m → K :=
  if h : i < l.length then l.get ⟨i, h⟩ else 0

theorem listCol_get (l : List (Fin m → K)) (i : Fin l.length) : listCol l (i : ℕ) = l.get i := by
  rw [listCol, dif_pos i.isLt]

/-- **The core: honest scalar columns give satisfying polynomial columns.**

The four conclusions are exactly the four hypotheses `io_lio_of_satisfies` needs of one chip:
per-kind ordinary RAP satisfaction for the request AIR, the same for the response AIR, the
row-domain deployment condition, and the committed-column agreement. -/
theorem chip_satisfies (D : OrbitDomain K) (coins : IOCoins K) (terminal : K)
    (recsL : List (Fin m → K)) (acc inv mult multInv : ℕ → K)
    (hcap : recsL.length + 1 ≤ 2 ^ D.h)
    (hinit : acc 0 = 0)
    (hpin : ∀ i, i < recsL.length → compress coins (listCol recsL i) * inv i = 1)
    (hbool : ∀ i, i < recsL.length → mult i * (mult i - 1) = 0)
    (hminv : ∀ i, i < recsL.length → mult i * multInv i = 1)
    (hstepP : ∀ i, i < recsL.length → acc (i + 1) = acc i + inv i)
    (hstepM : ∀ i, i < recsL.length → acc (i + 1) = acc i + mult i * inv i)
    (hterm : acc recsL.length = terminal) :
    (∀ k : Reified.ConstraintKind,
        ((chipParams D coins terminal recsL.length).rap (finiteIOProgAIR m) k).Satisfies
          (chipTrace D recsL.length acc inv mult multInv (listCol recsL)))
      ∧ (∀ k : Reified.ConstraintKind,
        ((chipParams D coins terminal recsL.length).rap (finiteIOMemAIR m) k).Satisfies
          (chipTrace D recsL.length acc inv mult multInv (listCol recsL)))
      ∧ ChipRows recsL.length (chipParams D coins terminal recsL.length) D.βcoset
      ∧ ChipAgreement recsL coins terminal (chipParams D coins terminal recsL.length) D.βcoset
          (chipTrace D recsL.length acc inv mult multInv (listCol recsL)) := by
  classical
  set n := recsL.length with hn
  set q := chipParams D coins terminal n with hqdef
  set P := chipTrace D n acc inv mult multInv (listCol recsL) with hPdef
  -- column reads
  have hacc : ∀ i, i < n + 1 → (rowEnv q D.βcoset P i).trace 0 = acc i :=
    fun i hi => chipTrace_acc D coins terminal acc inv mult multInv (listCol recsL) hcap i hi
  have hinv : ∀ i, i < n + 1 → (rowEnv q D.βcoset P i).trace 1 = inv i :=
    fun i hi => chipTrace_inv D coins terminal acc inv mult multInv (listCol recsL) hcap i hi
  have hmul : ∀ i, i < n + 1 → (rowEnv q D.βcoset P i).trace 2 = mult i :=
    fun i hi => chipTrace_mult D coins terminal acc inv mult multInv (listCol recsL) hcap i hi
  have hmi : ∀ i, i < n + 1 → (rowEnv q D.βcoset P i).trace 3 = multInv i :=
    fun i hi => chipTrace_multInv D coins terminal acc inv mult multInv (listCol recsL) hcap i hi
  have hrec : ∀ i, i < n + 1 → ∀ c : Fin m,
      (rowEnv q D.βcoset P i).trace (4 + (c : ℕ)) = listCol recsL i c :=
    fun i hi c => chipTrace_rec D coins terminal acc inv mult multInv (listCol recsL) hcap i hi c
  -- the scalar gate facts, row by row
  have gInit : ioAccInit.eval (rowEnv q D.βcoset P 0) = 0 := by
    rw [ioAccInit_eval_rowEnv, hacc 0 (by omega), hinit]
  have gTerm : ioTerm.eval (rowEnv q D.βcoset P n) = 0 := by
    rw [ioTerm_eval_rowEnv]
    have hp : q.pubVal 0 = terminal := rfl
    rw [hp, hacc n (by omega), hterm, sub_self]
  have gPin : ∀ i, i < n → (ioInvPin m 4).eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    have hg : q.chalVal 0 = coins.gamma := rfl
    have hpo : q.chalVal 1 = coins.pole := rfl
    rw [ioInvPin_eval_rowEnv q D.βcoset P i coins (listCol recsL i)
      (fun c => hrec i (by omega) c) hg hpo, hinv i (by omega), hpin i hi, sub_self]
  have gBool : ∀ i, i < n → ioMultBool.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioMultBool_eval_rowEnv, hmul i (by omega)]
    exact hbool i hi
  have gMInv : ∀ i, i < n → ioMultInvPin.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioMultInvPin_eval_rowEnv, hmul i (by omega), hmi i (by omega), hminv i hi, sub_self]
  have gStepP : ∀ i, i < n → ioProgAccStep.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioProgAccStep_eval_rowEnv, hacc (i + 1) (by omega), hacc i (by omega),
      hinv i (by omega), hstepP i hi]
    ring
  have gStepM : ∀ i, i < n → ioMemAccStep.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioMemAccStep_eval_rowEnv, hacc (i + 1) (by omega), hacc i (by omega),
      hinv i (by omega), hmul i (by omega), hstepM i hi]
    ring
  -- reading the three per-kind domains back as rows
  have hdb : ∀ x ∈ q.domain (.boundary : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P 0 := by
    intro x hx
    have hx1 : x = D.βcoset := by
      have : x ∈ D.boundaryDomain := hx
      simpa [OrbitDomain.boundaryDomain] using this
    have h0 : rowPt q.ω D.βcoset 0 = D.βcoset := by
      rw [chipRowPt D coins terminal n 0, OrbitDomain.orbitPoint_zero]
    rw [hx1, rowEnv, h0]
  have hdt : ∀ x ∈ q.domain (.transition : Reified.ConstraintKind),
      ∃ i, i < n ∧ envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P i := by
    intro x hx
    have hx' : x ∈ D.transitionDomain (n + 1) (Nat.succ_pos n) := hx
    obtain ⟨i, hi, rfl⟩ :=
      (orbit_mem_transitionDomain_iff_active_nonterminal D (n + 1) (Nat.succ_pos n) hcap x).mp hx'
    refine ⟨(i : ℕ), by omega, ?_⟩
    -- `hi : (i : ℕ) + 1 < n + 1`
    rw [rowEnv, chipRowPt D coins terminal n (i : ℕ)]
  have hdm : ∀ x ∈ q.domain (.terminal : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P n := by
    intro x hx
    have hx' : x ∈ D.terminalDomain (n + 1) (Nat.succ_pos n) := hx
    have hxe : x = D.terminalPoint (n + 1) (Nat.succ_pos n) := by
      simpa [OrbitDomain.terminalDomain] using hx'
    have hn' : rowPt q.ω D.βcoset n = D.terminalPoint (n + 1) (Nat.succ_pos n) := by
      rw [chipRowPt D coins terminal n n, terminalPoint_succ D n]
    rw [hxe, rowEnv, hn']
  -- the four conclusions
  have satP : ∀ k : Reified.ConstraintKind,
      (q.rap (finiteIOProgAIR m) k).Satisfies P := by
    refine (segmented_is_kinded (finiteIOProgAIR m) q.chalVal q.pubVal q.eDeg q.hExp q.ω
      q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain P).mpr ?_
    intro c hc x hx
    simp only [finiteIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · show ioAccInit.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdb x hx]; exact gInit
    · show (ioInvPin m 4).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gPin i hi
    · show ioProgAccStep.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gStepP i hi
    · show ioTerm.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdm x hx]; exact gTerm
  have satM : ∀ k : Reified.ConstraintKind,
      (q.rap (finiteIOMemAIR m) k).Satisfies P := by
    refine (segmented_is_kinded (finiteIOMemAIR m) q.chalVal q.pubVal q.eDeg q.hExp q.ω
      q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain P).mpr ?_
    intro c hc x hx
    simp only [finiteIOMemAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · show ioAccInit.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdb x hx]; exact gInit
    · show (ioInvPin m 4).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gPin i hi
    · show ioMultBool.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gBool i hi
    · show ioMultInvPin.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gMInv i hi
    · show ioMemAccStep.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      obtain ⟨i, hi, he⟩ := hdt x hx
      rw [he]; exact gStepM i hi
    · show ioTerm.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
      rw [hdm x hx]; exact gTerm
  have rows : ChipRows n q D.βcoset := by
    refine { boundary_mem := ?_, transition_mem := ?_, terminal_mem := ?_ }
    · have h0 : rowPt q.ω D.βcoset 0 = D.βcoset := by
        rw [chipRowPt D coins terminal n 0, OrbitDomain.orbitPoint_zero]
      show rowPt q.ω D.βcoset 0 ∈ D.boundaryDomain
      rw [h0]
      exact D.boundaryPoint_mem_boundaryDomain
    · intro i hi
      show rowPt q.ω D.βcoset i ∈ D.transitionDomain (n + 1) (Nat.succ_pos n)
      rw [chipRowPt D coins terminal n i]
      exact D.orbitPoint_mem_transitionDomain (Nat.succ_pos n) hcap ⟨i, by omega⟩
        (show i + 1 < n + 1 from by omega)
    · show rowPt q.ω D.βcoset n ∈ D.terminalDomain (n + 1) (Nat.succ_pos n)
      rw [chipRowPt D coins terminal n n, ← terminalPoint_succ D n]
      exact D.terminalPoint_mem_terminalDomain (n + 1) (Nat.succ_pos n)
  have agree : ChipAgreement recsL coins terminal q D.βcoset P := by
    refine { gamma_eq := rfl, pole_eq := rfl, terminal_eq := rfl, record_eq := ?_ }
    intro i c
    have hi : (i : ℕ) < n + 1 := by have := i.isLt; omega
    rw [hrec (i : ℕ) hi c, listCol_get]
  exact ⟨satP, satM, rows, agree⟩

/-! ## 6. The headline: `IO.LIO` gives satisfying committed columns -/

/-- **`satisfies_of_io_lio` — AIR-level completeness of the `K`-valued IO chip.**

Given the record-level IO language `IO.LIO`, an orbit long enough for the record rows plus the
terminal row, and a sampled pole missing every compressed record, there exist kind-segmented
deployments, committed *polynomial* traces and a shared terminal for which both chips' ordinary
per-kind RAPs are satisfied, the row-domain deployment conditions hold, and the committed columns
agree with the records and the coins.

This is the exact converse of `io_lio_of_satisfies` (`IOChipSoundness.lean:408`): the six
conjuncts are that theorem's six chip hypotheses.

The honest column values come from `finiteIO_complete_of_LIO` (`FiniteFieldIO.lean:246`); the new
content is the interpolation step, `encodeCells`.  Note `hlio` forces
`records.requests.length = records.responses.length` (`List.Perm.length_eq`), so a single capacity
hypothesis covers both chips. -/
theorem satisfies_of_io_lio {Ksz : ℕ} (D : OrbitDomain K)
    (records : PreChallengeRecords K m) (coins : IOCoins K)
    (hlio : IO.LIO Ksz records.requests records.responses)
    (hden : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0)
    (hcap : records.requests.length + 1 ≤ 2 ^ D.h) :
    ∃ (qp qm : SegmentedRAPParams K) (x₀p x₀m terminal : K)
      (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
      (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X]),
        (∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
      ∧ (∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
      ∧ ChipRows records.requests.length qp x₀p
      ∧ ChipRows records.responses.length qm x₀m
      ∧ ChipAgreement records.requests coins terminal qp x₀p Pp
      ∧ ChipAgreement records.responses coins terminal qm x₀m Pm := by
  classical
  obtain ⟨w, hw⟩ := finiteIO_complete_of_LIO (Ksz := Ksz) records coins hlio hden
  have hlen : records.requests.length = records.responses.length := hlio.2.2.length_eq
  -- request-side scalar columns
  have hPinit : natOfFin w.requestAcc 0 = 0 := by
    have := natOfFin_apply w.requestAcc (0 : Fin (records.requests.length + 1))
    rw [show ((0 : Fin (records.requests.length + 1)) : ℕ) = 0 from rfl] at this
    rw [this, hw.requestInit]
  have hPpin : ∀ i, i < records.requests.length →
      compress coins (listCol records.requests i) * natOfFin w.requestInv i = 1 := by
    intro i hi
    rw [show listCol records.requests i = records.requests.get ⟨i, hi⟩ from
      listCol_get records.requests ⟨i, hi⟩,
      show natOfFin w.requestInv i = w.requestInv ⟨i, hi⟩ from
      natOfFin_apply w.requestInv ⟨i, hi⟩]
    exact hw.requestInvPin ⟨i, hi⟩
  have hPstep : ∀ i, i < records.requests.length →
      natOfFin w.requestAcc (i + 1) = natOfFin w.requestAcc i + natOfFin w.requestInv i := by
    intro i hi
    have hs := hw.requestStep ⟨i, hi⟩
    rw [show natOfFin w.requestAcc (i + 1)
        = w.requestAcc (Fin.succ ⟨i, hi⟩) from natOfFin_apply w.requestAcc (Fin.succ ⟨i, hi⟩),
      show natOfFin w.requestAcc i
        = w.requestAcc (Fin.castSucc ⟨i, hi⟩) from
          natOfFin_apply w.requestAcc (Fin.castSucc ⟨i, hi⟩),
      show natOfFin w.requestInv i = w.requestInv ⟨i, hi⟩ from
        natOfFin_apply w.requestInv ⟨i, hi⟩]
    exact hs
  have hPterm : natOfFin w.requestAcc records.requests.length = w.terminal := by
    rw [show natOfFin w.requestAcc records.requests.length
        = w.requestAcc (Fin.last records.requests.length) from
      natOfFin_apply w.requestAcc (Fin.last records.requests.length)]
    exact hw.requestTerm
  -- response-side scalar columns
  have hMinit : natOfFin w.responseAcc 0 = 0 := by
    have := natOfFin_apply w.responseAcc (0 : Fin (records.responses.length + 1))
    rw [show ((0 : Fin (records.responses.length + 1)) : ℕ) = 0 from rfl] at this
    rw [this, hw.responseInit]
  have hMpin : ∀ i, i < records.responses.length →
      compress coins (listCol records.responses i) * natOfFin w.responseInv i = 1 := by
    intro i hi
    rw [show listCol records.responses i = records.responses.get ⟨i, hi⟩ from
      listCol_get records.responses ⟨i, hi⟩,
      show natOfFin w.responseInv i = w.responseInv ⟨i, hi⟩ from
      natOfFin_apply w.responseInv ⟨i, hi⟩]
    exact hw.responseInvPin ⟨i, hi⟩
  have hMbool : ∀ i, i < records.responses.length →
      natOfFin w.multiplicity i * (natOfFin w.multiplicity i - 1) = 0 := by
    intro i hi
    rw [show natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      natOfFin_apply w.multiplicity ⟨i, hi⟩]
    exact hw.multBool ⟨i, hi⟩
  have hMminv : ∀ i, i < records.responses.length →
      natOfFin w.multiplicity i * natOfFin w.multInv i = 1 := by
    intro i hi
    rw [show natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      natOfFin_apply w.multiplicity ⟨i, hi⟩,
      show natOfFin w.multInv i = w.multInv ⟨i, hi⟩ from natOfFin_apply w.multInv ⟨i, hi⟩]
    exact hw.multInvPin ⟨i, hi⟩
  have hMstepM : ∀ i, i < records.responses.length →
      natOfFin w.responseAcc (i + 1)
        = natOfFin w.responseAcc i + natOfFin w.multiplicity i * natOfFin w.responseInv i := by
    intro i hi
    have hs := hw.responseStep ⟨i, hi⟩
    rw [show natOfFin w.responseAcc (i + 1)
        = w.responseAcc (Fin.succ ⟨i, hi⟩) from natOfFin_apply w.responseAcc (Fin.succ ⟨i, hi⟩),
      show natOfFin w.responseAcc i
        = w.responseAcc (Fin.castSucc ⟨i, hi⟩) from
          natOfFin_apply w.responseAcc (Fin.castSucc ⟨i, hi⟩),
      show natOfFin w.responseInv i = w.responseInv ⟨i, hi⟩ from
        natOfFin_apply w.responseInv ⟨i, hi⟩,
      show natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
        natOfFin_apply w.multiplicity ⟨i, hi⟩]
    exact hs
  have hMstepP : ∀ i, i < records.responses.length →
      natOfFin w.responseAcc (i + 1)
        = natOfFin w.responseAcc i + natOfFin w.responseInv i := by
    intro i hi
    rw [hMstepM i hi, show natOfFin w.multiplicity i = w.multiplicity ⟨i, hi⟩ from
      natOfFin_apply w.multiplicity ⟨i, hi⟩, multiplicity_eq_one hw ⟨i, hi⟩, one_mul]
  have hPstepM : ∀ i, i < records.requests.length →
      natOfFin w.requestAcc (i + 1)
        = natOfFin w.requestAcc i + (fun _ : ℕ => (1 : K)) i * natOfFin w.requestInv i := by
    intro i hi
    rw [hPstep i hi, one_mul]
  have hMterm : natOfFin w.responseAcc records.responses.length = w.terminal := by
    rw [show natOfFin w.responseAcc records.responses.length
        = w.responseAcc (Fin.last records.responses.length) from
      natOfFin_apply w.responseAcc (Fin.last records.responses.length)]
    exact hw.responseTerm
  -- the two chips
  have hcapM : records.responses.length + 1 ≤ 2 ^ D.h := by rw [← hlen]; exact hcap
  obtain ⟨satP, _, rowsP, agreeP⟩ :=
    chip_satisfies D coins w.terminal records.requests (natOfFin w.requestAcc)
      (natOfFin w.requestInv) (fun _ => 1) (fun _ => 1) hcap hPinit hPpin
      (fun i _ => by ring) (fun i _ => by ring) hPstep hPstepM hPterm
  obtain ⟨_, satM, rowsM, agreeM⟩ :=
    chip_satisfies D coins w.terminal records.responses (natOfFin w.responseAcc)
      (natOfFin w.responseInv) (natOfFin w.multiplicity) (natOfFin w.multInv) hcapM
      hMinit hMpin hMbool hMminv hMstepP hMstepM hMterm
  exact ⟨chipParams D coins w.terminal records.requests.length,
    chipParams D coins w.terminal records.responses.length, D.βcoset, D.βcoset, w.terminal,
    chipTrace D records.requests.length (natOfFin w.requestAcc) (natOfFin w.requestInv)
      (fun _ => 1) (fun _ => 1) (listCol records.requests),
    chipTrace D records.responses.length (natOfFin w.responseAcc) (natOfFin w.responseInv)
      (natOfFin w.multiplicity) (natOfFin w.multInv) (listCol records.responses),
    satP, satM, rowsP, rowsM, agreeP, agreeM⟩

/-! ## 7. The shapes really are converse

`lio_roundtrip` is **not** a new mathematical fact — as a proposition it is `IO.LIO → IO.LIO`.
Its content is entirely type-level: it compiles only if the six conjuncts `satisfies_of_io_lio`
produces are *literally* the six chip hypotheses `io_lio_of_satisfies`
(`IOChipSoundness.lean:408`) consumes, at the same `q`, `x₀`, `terminal`, `Pp`, `Pm`.  It is the
machine-checked form of the claim that this module is the converse of that one, and it is what
rules out the failure mode of proving completeness for a *neighbouring* deployment shape. -/

section RoundTrip

variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- **Type-level converse check** (see the section docstring: the proposition itself is trivial).
    The committed columns built by `satisfies_of_io_lio` are accepted, verbatim, as the hostile
    input of `io_lio_of_satisfies`. -/
theorem lio_roundtrip {Ksz : ℕ} (D : OrbitDomain K)
    (records : PreChallengeRecords K m) (coins : IOCoins K)
    (hlio : IO.LIO Ksz records.requests records.responses)
    (hden : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0)
    (hcap : records.requests.length + 1 ≤ 2 ^ D.h)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hgam : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses := by
  obtain ⟨qp, qm, x₀p, x₀m, terminal, Pp, Pm, hsatP, hsatM, hrowsP, hrowsM, hagP, hagM⟩ :=
    satisfies_of_io_lio (Ksz := Ksz) D records coins hlio hden hcap
  exact io_lio_of_satisfies (Ksz := Ksz) records coins terminal qp qm x₀p x₀m Pp Pm
    hsatP hsatM hrowsP hrowsM hagP hagM hKp hKreq hKresp hreqnd hrespnd hgam hpole

end RoundTrip

/-! ## 8. Non-vacuity -/

/-- **The completeness hypotheses are inhabited at a non-empty record list.**  For any orbit
    domain with `1 ≤ D.h` (two rows of capacity: one record row and the terminal row), any coins,
    and any record whose compressed denominator is nonzero, the hypotheses of
    `satisfies_of_io_lio` all hold at the one-request / one-response record pair. -/
theorem completeness_hypotheses_inhabited (D : OrbitDomain K) (hh : 1 ≤ D.h)
    (coins : IOCoins K) (rec : Fin m → K) (hne : compress coins rec ≠ 0) :
    IO.LIO 1 ([rec] : List (Fin m → K)) [rec]
      ∧ (∀ v ∈ ([rec] : List (Fin m → K)) ++ [rec], compress coins v ≠ 0)
      ∧ ([rec] : List (Fin m → K)).length + 1 ≤ 2 ^ D.h := by
  refine ⟨⟨⟨le_refl 1, le_refl 1⟩, List.nodup_singleton _, List.Perm.refl _⟩, ?_, ?_⟩
  · intro v hv
    have : v = rec := by
      simpa using hv
    rw [this]; exact hne
  · have : (2 : ℕ) ^ 1 ≤ 2 ^ D.h := Nat.pow_le_pow_right (by omega) hh
    simpa using this

/-- **The conclusion of `satisfies_of_io_lio` is inhabited at a non-empty record list.**  Same
    hypotheses as `completeness_hypotheses_inhabited`, conclusion the existence statement. -/
theorem satisfies_of_io_lio_nonvacuous (D : OrbitDomain K) (hh : 1 ≤ D.h)
    (coins : IOCoins K) (rec : Fin m → K) (hne : compress coins rec ≠ 0) :
    ∃ (qp qm : SegmentedRAPParams K) (x₀p x₀m terminal : K)
      (Pp : Fin (finiteIOProgAIR m).numTraceCols → K[X])
      (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X]),
        (∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR m) k).Satisfies Pp)
      ∧ (∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
      ∧ ChipRows ([rec] : List (Fin m → K)).length qp x₀p
      ∧ ChipRows ([rec] : List (Fin m → K)).length qm x₀m
      ∧ ChipAgreement ([rec] : List (Fin m → K)) coins terminal qp x₀p Pp
      ∧ ChipAgreement ([rec] : List (Fin m → K)) coins terminal qm x₀m Pm := by
  obtain ⟨hlio, hden, hcap⟩ := completeness_hypotheses_inhabited D hh coins rec hne
  exact satisfies_of_io_lio (Ksz := 1) D ⟨[rec], [rec]⟩ coins hlio hden hcap

/-! ### A concrete orbit domain, so the non-vacuity witness is not itself conditional -/

section Concrete

local instance primeIOChip97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- `-1 = 96` has multiplicative order `2 = 2 ^ 1` in `ZMod 97`. -/
theorem order_ninetysix : orderOf (96 : ZMod 97) = 2 ^ 1 := by
  have h2 : ((96 : ZMod 97)) ^ 2 = 1 := by decide
  have h1 : ((96 : ZMod 97)) ≠ 1 := by decide
  simpa using orderOf_eq_prime h2 h1

/-- A concrete two-row orbit domain over `ZMod 97`. -/
noncomputable def concreteOrbit : OrbitDomain (ZMod 97) where
  h := 1
  ω := 96
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := order_ninetysix

/-- **The whole chain is inhabited over a concrete field.**  At `m = 1`, coins `(γ, pole) = (0, 1)`
    and the single zero record, `satisfies_of_io_lio` produces committed polynomial columns for a
    chip with one genuine record row plus the terminal row. -/
theorem satisfies_of_io_lio_concrete :
    ∃ (qp qm : SegmentedRAPParams (ZMod 97)) (x₀p x₀m terminal : ZMod 97)
      (Pp : Fin (finiteIOProgAIR 1).numTraceCols → (ZMod 97)[X])
      (Pm : Fin (finiteIOMemAIR 1).numTraceCols → (ZMod 97)[X]),
        (∀ k : Reified.ConstraintKind, (qp.rap (finiteIOProgAIR 1) k).Satisfies Pp)
      ∧ (∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR 1) k).Satisfies Pm)
      ∧ ChipRows ([(0 : Fin 1 → ZMod 97)]).length qp x₀p
      ∧ ChipRows ([(0 : Fin 1 → ZMod 97)]).length qm x₀m
      ∧ ChipAgreement ([(0 : Fin 1 → ZMod 97)]) ⟨0, 1⟩ terminal qp x₀p Pp
      ∧ ChipAgreement ([(0 : Fin 1 → ZMod 97)]) ⟨0, 1⟩ terminal qm x₀m Pm := by
  have hne : compress (⟨0, 1⟩ : IOCoins (ZMod 97)) (0 : Fin 1 → ZMod 97) ≠ 0 := by
    show (1 : ZMod 97) + Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) ≠ 0
    rw [show Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 0 from by
      simp [Walk.rlc], add_zero]
    decide
  exact satisfies_of_io_lio_nonvacuous concreteOrbit (le_refl 1) ⟨0, 1⟩ 0 hne

end Concrete

end Nock.NockVMROM.Thm54.IOChip

#print axioms Nock.NockVMROM.Thm54.IOChip.encodeCells_eval_at_node
#print axioms Nock.NockVMROM.Thm54.IOChip.rowEnv_trace_encodeCells
#print axioms Nock.NockVMROM.Thm54.IOChip.chipTrace_read
#print axioms Nock.NockVMROM.Thm54.IOChip.chip_satisfies
#print axioms Nock.NockVMROM.Thm54.IOChip.satisfies_of_io_lio
#print axioms Nock.NockVMROM.Thm54.IOChip.lio_roundtrip
#print axioms Nock.NockVMROM.Thm54.IOChip.completeness_hypotheses_inhabited
#print axioms Nock.NockVMROM.Thm54.IOChip.satisfies_of_io_lio_nonvacuous
#print axioms Nock.NockVMROM.Thm54.IOChip.satisfies_of_io_lio_concrete
