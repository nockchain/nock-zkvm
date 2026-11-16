/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueP1.lean

 **Trace uniqueness on the P1 fragment: the uniqueness core `trace_unique_good'`.**

 * `AcceptsCanon2`: `AcceptsCanon` and the compute side template `canonC2` (E8, E9) on the trace.
 * `OpenP1`: the facts about two accepted tuples that this module does NOT derive, each a named field with the
 step of the proof architecture it belongs to and where it should come from (the round-0 determination of the
 compute, cell and walk tables, the cell and walk aux columns, the walk's round-1 labels, the two cell tables
 being validity-served, the claim serials).
 * `zC_of_outside`, `yA_of_outside`: the two seeds the rounds need are nonzero at a coin outside `allJ8X X`, when
 `X.C` is a lifted list `withLiftC R L` (as at the absent-atom-walk data of `LinkJ8A.probJ8V_absent`, where it
 holds by `rfl`).
 * **`trace_unique_good'`**: two tuples `(tr, ax, M)`, `(tr', ax', M')` accepted by `AcceptsCanon2` at one claim,
 layout and coin `χ` outside every event of `allJ8X X` are equal, given `Comp12P1` (the compute rounds 1/2,
 `hcomp12`) and `OpenP1`. Order: step 0 (the layout constants of `canonPb`), steps 8–9 (rounds 1 and 2 of every
 table and the cell, walk and atom publics, `AsmRoundsP1.rowsEq_of_round0`), step 11 (the degree lift
 `DegLiftP1.tr_eq_of_rows`, `aux_eq_of_rows`), step 10 (the message, `RoundsP1.msg_eq`).

 The coin hypothesis `hg` (outside `allJ8X X`) gives the two nonzero seeds; `hg'` is carried in the statement and is
 the intended source, with `hg`, of the coin-level fields of `OpenP1`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1

section Unique
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`AcceptsCanon2`**: `AcceptsCanon` and the compute side template `canonC2` (the E8 inactive-slot inverse pins and
the E9 last-row `wInv` pin) on the trace. -/
def AcceptsCanon2 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (Rg : Nock.Jet.Registry)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))
    (r : RowsJ8) (g : ℕ) : Prop :=
  AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g ∧ (canonC2 b Pb).Satisfies (sideC2Q tr)

/-- **The open facts** about two accepted tuples `(tr, ax, M)`, `(tr', ax', M')` at one layout `Pb`, claim `c` and
coin `χ`: each field is a named hypothesis of `trace_unique_good'`, with its step and its intended source. -/
structure OpenP1 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M M' : MsgJ8' p K δ)
    (tr tr' : TrJ8 (ZMod p)) (ax ax' : AuxP1 (ZMod p)) : Prop where
  /-- Steps 1, 4, 6, 7: the round-0 compute columns (`< 69`) agree at every row. Source: the compute rows as nouns
 (the extraction twins, `RowBridgeP1.rowBridge`, `GenXDet.genuineNX_eq_genX` with `AsmRowsP1.P1FragC.p1Frag`),
 the handle serials (step 4), the multiplicities (`CountsP1`, step 6) and the E3 zero pins (`PinsP1`, step 7). -/
  r0C : ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)
  /-- Steps 2, 3, 4, 6: the round-0 cell columns (`< 134`) agree at every row. Source: the cell set is the honest
 closure (step 2), the cell list is fixed by the set (`CellOrderP1.rows_eq_of_set`, step 3), the remaining
 columns (kinds, rank bits, the E1/E2 inverses) and the multiplicities `mv mx mx1 mh` (`CountsP1`). -/
  r0M : ∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)
  /-- Step 3: the cell aux columns (limb bits, the inverse-or-zero columns, the one-hot `s`, the difference bits)
 agree at every row. Source: `CellOrderP1` (`limbs_canon`, `firstDiff`) from the equal sort keys. -/
  auxM : ∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)
  /-- Steps 5, 6: the round-0 walk columns (`< 25`) agree at every row. Source: the roots as a set and their order
 (root order, `PinsP1`), the trie at `nW` fixed (`walkRows`), the depth bits, `q`, `qinv`, and `mL mR` (`CountsP1`). -/
  r0W : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)
  /-- Step 5: the walk aux columns (`dr` bits, `y`) agree at every row. Source: `PinsP1` (root order remainder,
 depth certificate `y`). -/
  auxW : ∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)
  /-- Step 8: the walk's round-1 label columns (`25 .. 96`: the four `𝕂′` labels `p l r root`) agree at every row.
 Source: the export consume and the path records (`l = p_child` from the validity key match), with the cell
 fingerprints of `RoundsCellP1`. -/
  r1W : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
    ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)
  /-- Step 8: the first cell table is validity-served. Source: the soundness chain (the validity balance `hsumC'`
 with two providers, `TwoProviderQ.served2_of_balanced2`, outside the validity IO event). -/
  servedC : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)))
  /-- Step 8: the second cell table is validity-served (as `servedC`). -/
  servedC' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)))
  /-- Steps 4, 10: the claim serials of the cell claim nouns agree. Source: the claim records are consumed against
 the cell table's validity providers (`hsumC'`), whose serials are the row indices of the (equal) cell list. -/
  claim : ∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {P g' : ℕ}

omit [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))] in
/-- **The memory chips' seed is nonzero** at a coin outside `allJ8X X` with `X.C = withLiftC R L` (the zero-seed
summand of the 40th's lifted class, `ListJ8C.hz_of_outside40C`). -/
theorem zC_of_outside {r : RowsJ8} {g : ℕ} {X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    {R : ListJ8C.DataJ8C (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    {L : Lift40J8.Data40J8 (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r}
    (hX : X.C = ListJ8C.withLiftC R L) {tr : TrJ8 (ZMod p)} {χ : Coins frameJ8 K}
    (hg : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
  refine ListJ8C.hz_of_outside40C R L (fun s hs => hg s ?_) (chalsMJ8 δ χ) rfl rfl
  rw [← hX] at hs
  exact List.mem_append_left _ hs

omit [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))] in
/-- **The atom table's coin `z′ = y` is nonzero** at a coin outside `allJ8X X` (the atom-census summand,
`ListJ8C.atom_hz_of_outsideC`; leaves `2, 3` of the rewired vector are `chalsAJ8`'s). -/
theorem yA_of_outside {r : RowsJ8} {g : ℕ} {X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    {tr : TrJ8 (ZMod p)} {χ : Coins frameJ8 K} (hg : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
  rw [ChalsAZJ8.chalsAJ8Z_of_ne δ χ (by omega) (by omega), ChalsAZJ8.chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
  exact ListJ8C.atom_hz_of_outsideC X.C fun s hs => hg s (List.mem_append_left _ hs)

theorem two63_lt_ringChar (hpG : p = Nock.Atoms.p) : 2 ^ 63 < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n, hpG]
  norm_num [Nock.Atoms.p, Nock.Field.p]

/-- **`trace_unique_good'`: the uniqueness core.** Two tuples accepted by `AcceptsCanon2` at one claim `c`, layout
`Pb`, registry and coin `χ`, with `χ` outside every event of `allJ8X X` at both traces (`X.C` a lifted list
`withLiftC R L`), are equal, given the compute
rounds lemma `hcomp12` and the open facts `O`. -/
theorem trace_unique_good' {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {g : ℕ}
    {X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g'}
    {R : ListJ8C.DataJ8C (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g'}
    {L : Lift40J8.Data40J8 (q := q) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r} (hX : X.C = ListJ8C.withLiftC R L)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) (hg' : ∀ s ∈ allJ8X X, ¬ s.mem tr' χ)
    (hcomp12 : Comp12P1 δ b Pb Rg c χ r g)
    (O : OpenP1 δ b Pb c χ M M' tr tr' ax ax') :
    (tr, ax, M) = (tr', ax', M') := by
  obtain ⟨⟨hA, hC⟩, hC2⟩ := h
  obtain ⟨⟨hA', hC'⟩, hC2'⟩ := h'
  -- step 0: the layout constants
  have hJ0 : Pb.nJ = 0 := by rw [hC.hPb]; exact (canonPb_consts hpG sz c).1
  -- steps 8, 9: rounds 1 and 2 of every table, and the publics
  obtain ⟨hrows, pC, pW, pA⟩ := rowsEq_of_round0 δ b hA hA' hC.hdeg hC'.hdeg hC2 hC2' hC.hApad hC'.hApad hcomp12
    (two63_lt_ringChar hpG) (zC_of_outside δ hX hg) (yA_of_outside δ hg) O.servedC O.servedC' O.r0C O.r0M O.r0W O.r1W
  -- step 11: the degree lift
  have htr : tr = tr' := tr_eq_of_rows hC.hdeg hC'.hdeg hJ0 hC.hV0 hC'.hV0 hA.hinjX hA.hinjC hA.hinjW hA.hinjA hrows
  have hax : ax = ax' := aux_eq_of_rows hC.hdeg hC'.hdeg hA.hinjC hA.hinjW O.auxM O.auxW
  subst htr hax
  -- step 10: the message
  have hM := RoundsP1.msg_eq δ b hA hA' hC.hmsg hC'.hmsg O.claim pC pW pA
  rw [hM]

end Unique

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1.zC_of_outside
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1.yA_of_outside
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1.two63_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1.trace_unique_good'
