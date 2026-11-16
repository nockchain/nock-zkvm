/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/NounSetP1.lean

 **The cell table's noun links, its noun set (= the honest closure) and its multiplicities (trace uniqueness, P1
 fragment).**

 * §1 the row decoder `decN` / `nounOf` of a table of row values, by fuel; `RowServed` (every weighted child names a
 row with that serial and that rank); **`nounLink_of_served`**: on a `TableM` table with `RowServed`, `nounOf` is a
 `NounLink`.
 * §2 the bridge from `AcceptsCanon` and the restricted cell table's `ValidityServed` (`ServedP1.cell_served_P1`):
 **`rowServed_of_accepts`**, **`nounLink_of_accepts`**.
 * §3 the honest closure `cellsOfRoots`: its members are cells below a root, it is duplicate-free;
 **`closure_subset`**: every closure noun is a row noun, given that every honest root that is a cell is denoted by
 some handle (`hrowsC`) and that the chip's handle decoder agrees with the row nouns on cells (`hDN`).
 * §4 **`nouns_eq_closure`** (row count = closure size, rows distinct ⇒ the row-noun set IS the closure) and
 **`hset_of_closure`** for two traces.
 * §5 **`hmul_of_counts`**: the four multiplicity columns agree from the per-trace count characterisation
 (`CountsP1.*_eq_count`) and agreeing consumer counts.
 * §6 **`r0M_auxM_final`**: `OpenR0MP1.r0M_auxM_of_set` with §1–§5 plugged in.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1
import Nock.V1J8.GenComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1

noncomputable section

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

/-! ## 1. The row decoder -/

section Decoder
variable {p : ℕ} [Fact p.Prime]

/-- **The row decoder by fuel**: row `i` is the cell of its two sides; a weighted side (`w = 1`) is the row whose
serial is the side's `id`, an unweighted side is the atom named by its `a` column. -/
def decN (v : ℕ → ℕ → ZMod p) : ℕ → ℕ → Noun
  | 0, _ => .atom 0
  | f + 1, i =>
    .cell (if v i Cell.wL = 1 then decN v f (v i Cell.idL).val else .atom (v i Cell.aL).val)
      (if v i Cell.wR = 1 then decN v f (v i Cell.idR).val else .atom (v i Cell.aR).val)

/-- **The noun of row `i`**: the decoder at fuel `rank + 1`. -/
def nounOf (v : ℕ → ℕ → ZMod p) (i : ℕ) : Noun := decN v (rk (v i) + 1) i

theorem decN_succ (v : ℕ → ℕ → ZMod p) (f i : ℕ) : decN v (f + 1) i =
    .cell (if v i Cell.wL = 1 then decN v f (v i Cell.idL).val else .atom (v i Cell.aL).val)
      (if v i Cell.wR = 1 then decN v f (v i Cell.idR).val else .atom (v i Cell.aR).val) := rfl

/-- **Every weighted side names a row**: a row with the side's serial and the side's rank limbs. -/
def RowServed (v : ℕ → ℕ → ZMod p) (n : ℕ) : Prop :=
  ∀ i < n,
    (v i Cell.wL = 1 → ∃ j < n, v j Cell.idx = v i Cell.idL ∧ v j Cell.lo = v i Cell.loL ∧
      v j Cell.hi = v i Cell.hiL) ∧
    (v i Cell.wR = 1 → ∃ j < n, v j Cell.idx = v i Cell.idR ∧ v j Cell.lo = v i Cell.loR ∧
      v j Cell.hi = v i Cell.hiR)

variable {v : ℕ → ℕ → ZMod p} {n : ℕ}

/-- One side of a served row: the limbs are below `2^62`, an unweighted side has rank `0`, a weighted side names the
row `(v i id).val` of rank `hi·2^62 + lo`. -/
theorem side_facts (T : TableM v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p) {i w sid lo hi : ℕ} (hi' : i < n)
    (hatom : v i w = 0 → v i lo = 0 ∧ v i hi = 0) (hwb : v i w = 0 ∨ v i w = 1)
    (hsv : v i w = 1 → ∃ j < n, v j Cell.idx = v i sid ∧ v j Cell.lo = v i lo ∧ v j Cell.hi = v i hi) :
    (v i lo).val < 2 ^ 62 ∧ (v i hi).val < 2 ^ 62 ∧
      (v i w = 0 → (v i hi).val * 2 ^ 62 + (v i lo).val = 0) ∧
      (v i w = 1 → (v i sid).val < n ∧ v ((v i sid).val) Cell.idx = v i sid ∧
        v ((v i sid).val) Cell.lo = v i lo ∧ v ((v i sid).val) Cell.hi = v i hi ∧
        rk (v ((v i sid).val)) = (v i hi).val * 2 ^ 62 + (v i lo).val) := by
  rcases hwb with h0 | h1
  · obtain ⟨a, b⟩ := hatom h0
    rw [a, b]
    refine ⟨by simp, by simp, fun _ => by simp, fun h => ?_⟩
    rw [h0] at h; exact absurd h zero_ne_one
  · obtain ⟨j, hj, e1, e2, e3⟩ := hsv h1
    have hjv : (v i sid).val = j := by
      rw [← e1, T.idx_row j hj, val_natCast_lt (by omega)]
    rw [hjv]
    refine ⟨?_, ?_, fun h => ?_, fun _ => ⟨hj, e1, e2, e3, ?_⟩⟩
    · rw [← e2]; exact T.lo_lt hp hj
    · rw [← e3]; exact T.hi_lt hp hj
    · rw [h1] at h; exact absurd h one_ne_zero
    · unfold rk; rw [e2, e3]

/-- **A weighted child's row has a strictly smaller rank**, and the row's rank is the sum plus one. -/
theorem rank_split (T : TableM v n) (S : RowServed v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p) {i : ℕ} (hi : i < n) :
    rk (v i) = ((v i Cell.hiL).val * 2 ^ 62 + (v i Cell.loL).val) +
      ((v i Cell.hiR).val * 2 ^ 62 + (v i Cell.loR).val) + 1 := by
  obtain ⟨l1, l2, -, -⟩ := side_facts (sid := Cell.idL) T hp hnp hi (atomL T hi) (T.cell hi).wL (S i hi).1
  obtain ⟨r1, r2, -, -⟩ := side_facts (sid := Cell.idR) T hp hnp hi (atomR T hi) (T.cell hi).wR (S i hi).2
  have h := rank_rec hp (T.cell hi) l1 l2 r1 r2
  change rk (v i) = _ at h
  rw [h]
  rfl

/-- **The decoder is stable above the rank**: at every fuel `f > rk`, row `i` decodes to `nounOf v i`. -/
theorem decN_stable (T : TableM v n) (S : RowServed v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p) :
    ∀ m, ∀ i < n, rk (v i) = m → ∀ f, m < f → decN v f i = decN v (m + 1) i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i hi hm f hf
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hsplit := rank_split T S hp hnp hi
  obtain ⟨-, -, -, lw⟩ := side_facts (sid := Cell.idL) T hp hnp hi (atomL T hi) (T.cell hi).wL (S i hi).1
  obtain ⟨-, -, -, rw'⟩ := side_facts (sid := Cell.idR) T hp hnp hi (atomR T hi) (T.cell hi).wR (S i hi).2
  rw [decN_succ, decN_succ]
  refine congrArg₂ Noun.cell ?_ ?_
  · split_ifs with hw
    · obtain ⟨hj, -, -, -, hr⟩ := lw hw
      have h1 := ih _ (by omega) _ hj hr f (by omega)
      have h2 := ih _ (by omega) _ hj hr m (by omega)
      rw [h1, h2]
    · rfl
  · split_ifs with hw
    · obtain ⟨hj, -, -, -, hr⟩ := rw' hw
      have h1 := ih _ (by omega) _ hj hr f (by omega)
      have h2 := ih _ (by omega) _ hj hr m (by omega)
      rw [h1, h2]
    · rfl

/-- A weighted side's child decodes, at the parent's fuel, to the child row's noun. -/
theorem child_noun (T : TableM v n) (S : RowServed v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hlt : rk (v j) < rk (v i)) : decN v (rk (v i)) j = nounOf v j :=
  decN_stable T S hp hnp _ j hj rfl _ hlt

/-- **`nounLink_of_served`: the decoded nouns are a `NounLink`.** -/
theorem nounLink_of_served (T : TableM v n) (S : RowServed v n) (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) :
    NounLink v n (nounOf v) := by
  have hp := hp63_of hpG
  refine ⟨fun i hi => ?_⟩
  have hsplit := rank_split T S hp hnp hi
  obtain ⟨-, -, lz, lw⟩ := side_facts (sid := Cell.idL) T hp hnp hi (atomL T hi) (T.cell hi).wL (S i hi).1
  obtain ⟨-, -, rz, rw'⟩ := side_facts (sid := Cell.idR) T hp hnp hi (atomR T hi) (T.cell hi).wR (S i hi).2
  refine ⟨_, _, decN_succ v (rk (v i)) i, ?_, ?_⟩
  · rcases (T.cell hi).wL with h0 | h1
    · change v i Cell.wL = 0 at h0
      left
      have : ¬ v i Cell.wL = 1 := by rw [h0]; exact zero_ne_one
      exact ⟨h0, ite_eq_right_iff.mpr fun h => absurd h this⟩
    · change v i Cell.wL = 1 at h1
      right
      obtain ⟨hj, e1, e2, e3, hr⟩ := lw h1
      refine ⟨h1, _, hj, e1, ?_, e2, e3⟩
      rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
      exact (child_noun T S hp hnp hi hj (by omega)).symm
  · rcases (T.cell hi).wR with h0 | h1
    · change v i Cell.wR = 0 at h0
      left
      have : ¬ v i Cell.wR = 1 := by rw [h0]; exact zero_ne_one
      exact ⟨h0, ite_eq_right_iff.mpr fun h => absurd h this⟩
    · change v i Cell.wR = 1 at h1
      right
      obtain ⟨hj, e1, e2, e3, hr⟩ := rw' h1
      refine ⟨h1, _, hj, e1, ?_, e2, e3⟩
      rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
      exact (child_noun T S hp hnp hi hj (by omega)).symm

end Decoder

/-! ## 2. The bridge from `AcceptsCanon` and the validity-served cell table -/

section Bridge
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **A validity-served cell table serves its row values**: if the base environment of every row agrees with `v`
on the first `129` columns, every weighted side of `v` names a row with that serial and rank (`natOf` is injective
on `ZMod p`). -/
theorem rowServed_of_table {h n : ℕ} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {chals pubs : ℕ → K} {w : ℕ} {Q : Fin w → (ZMod p)[X]} {v : ℕ → ℕ → ZMod p}
    (hS : ValidityServed (cellTableOf δ b nodes orbit chals pubs Q))
    (hv : ∀ i (hi : i < n) j, j < 129 → (cellEnvF b nodes orbit chals pubs Q ⟨i, hi⟩).trace j = v i j) :
    RowServed v n := by
  have hF := GeneratedField.primeFieldElems_zmod p
  intro i hi
  have hmem : cellRowOf δ (cellEnvK δ b nodes orbit chals pubs Q ⟨i, hi⟩)
      (cellEnvF b nodes orbit chals pubs Q ⟨i, hi⟩) ∈ cellTableOf δ b nodes orbit chals pubs Q :=
    List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨hL, hR⟩ := hS _ hmem
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have hwT : decide ((cellEnvF b nodes orbit chals pubs Q ⟨i, hi⟩).trace Cell.wL = 1) = true := by
      rw [hv i hi _ (by decide)]; exact decide_eq_true hw
    obtain ⟨c', hc', -, hhi, hlo, hid⟩ := hL hwT
    obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_ofFn.mp hc'
    refine ⟨j, hj, ?_, ?_, ?_⟩
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hid).symm
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hlo).symm
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hhi).symm
  · have hwT : decide ((cellEnvF b nodes orbit chals pubs Q ⟨i, hi⟩).trace Cell.wR = 1) = true := by
      rw [hv i hi _ (by decide)]; exact decide_eq_true hw
    obtain ⟨c', hc', -, hhi, hlo, hid⟩ := hR hwT
    obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_ofFn.mp hc'
    refine ⟨j, hj, ?_, ?_, ?_⟩
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hid).symm
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hlo).symm
    · rw [← hv j hj _ (by decide), ← hv i hi _ (by decide)]; exact (natOf_inj hF hhi).symm

/-- The handle-twin base environment of an accepted trace reads the side row values `vM` on the first `134`
columns. -/
theorem hqkEF_vM {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (i : ℕ) (hi : i < (canonPb hpG sz c).nC)
    {j : ℕ} (hj : j < 134) :
    (TwoProviderQ.hqkEF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) ⟨i, hi⟩).trace j =
      vM tr ax (canonPb hpG sz c).orbitC.ω i j :=
  ((envOfTrace_vM_agree tr ax (canonPb hpG sz c).orbitC.ω i _ _
    (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) (by rw [CellTwinKW.cellChipHQKW_width]; norm_num)
    (fun j hj => rfl)).1 j hj).symm

/-- The restricted cell table's base environment of an accepted trace reads `vM` on the first `129` columns. -/
theorem cellEnvF_vM {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (i : ℕ)
    (hi : i < (canonPb hpG sz c).nC) {j : ℕ} (hj : j < 129) :
    (cellEnvF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
        (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC)) ⟨i, hi⟩).trace j =
      vM tr ax (canonPb hpG sz c).orbitC.ω i j := by
  rw [← CellTwinKW.hqkwEF_trace δ b (canonPb hpG sz c).hnC _ _ _ _ _ ⟨i, hi⟩ hj]
  exact hqkEF_vM δ b tr ax i hi (by omega)

/-- **`nounLink_of_accepts`**: an `AcceptsCanon` trace whose restricted cell table is validity-served
(`ServedP1.cell_served_P1`) has side row values forming a `TableM` table with `RowServed`, and the decoded row
nouns `nounOf (vM …)` are a `NounLink`. Per trace. -/
theorem nounLink_of_accepts {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)))) :
    TableM (vM tr ax Pb.orbitC.ω) Pb.nC ∧ RowServed (vM tr ax Pb.orbitC.ω) Pb.nC ∧
      NounLink (vM tr ax Pb.orbitC.ω) Pb.nC (nounOf (vM tr ax Pb.orbitC.ω)) := by
  obtain ⟨T, -⟩ := tableM_of_accepts δ b h
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  have S : RowServed (vM tr ax Pb.orbitC.ω) Pb.nC := by
    have hPb := h.2.hPb
    subst hPb
    exact rowServed_of_table δ b hS fun i hi j hj => cellEnvF_vM δ b tr ax i hi hj
  exact ⟨T, S, nounLink_of_served T S hpG hnp⟩

end Bridge

/-! ## 3. The honest closure -/

section Closure
open Nock.V1J8.Gen (addCells cellsOfRoots rootsOf)

/-- `X` occurs in `m` (reflexive). -/
inductive SubN : Noun → Noun → Prop
  | refl (X : Noun) : SubN X X
  | left {X a b : Noun} : SubN X a → SubN X (.cell a b)
  | right {X a b : Noun} : SubN X b → SubN X (.cell a b)

theorem subN_atom {X : Noun} {k : ℕ} (h : SubN X (.atom k)) : X = .atom k := by
  cases h; rfl

/-- **No junk**: a member of `addCells m acc` is in `acc` or a cell occurring in `m`. -/
theorem mem_addCells : ∀ (m : Noun) (acc : List Noun) (X : Noun), X ∈ addCells m acc →
    X ∈ acc ∨ ((∃ a b, X = .cell a b) ∧ SubN X m)
  | .atom k, acc, X, hX => by simp only [addCells] at hX; exact Or.inl hX
  | .cell a b, acc, X, hX => by
    simp only [addCells] at hX
    split_ifs at hX with hin
    · exact Or.inl hX
    · rcases mem_addCells b _ X hX with h1 | ⟨hc, hs⟩
      · rcases mem_addCells a _ X h1 with h2 | ⟨hc, hs⟩
        · rcases List.mem_append.mp h2 with h3 | h3
          · exact Or.inl h3
          · rw [List.mem_singleton] at h3
            exact Or.inr ⟨⟨a, b, h3⟩, h3 ▸ SubN.refl _⟩
        · exact Or.inr ⟨hc, SubN.left hs⟩
      · exact Or.inr ⟨hc, SubN.right hs⟩

theorem nodup_addCells : ∀ (m : Noun) (acc : List Noun), acc.Nodup → (addCells m acc).Nodup
  | .atom k, acc, h => by simp only [addCells]; exact h
  | .cell a b, acc, h => by
    simp only [addCells]
    split_ifs with hin
    · exact h
    · refine nodup_addCells b _ (nodup_addCells a _ ?_)
      rw [List.nodup_append]
      refine ⟨h, List.nodup_singleton _, fun x hx y hy hxy => ?_⟩
      rw [List.mem_singleton] at hy
      exact hin (hy ▸ hxy ▸ hx)

theorem mem_foldl_addCells : ∀ (roots acc : List Noun) (X : Noun),
    X ∈ roots.foldl (fun acc n => addCells n acc) acc →
      X ∈ acc ∨ ((∃ a b, X = .cell a b) ∧ ∃ r ∈ roots, SubN X r)
  | [], acc, X, hX => Or.inl hX
  | r :: rs, acc, X, hX => by
    rw [List.foldl_cons] at hX
    rcases mem_foldl_addCells rs _ X hX with h1 | ⟨hc, r', hr', hs⟩
    · rcases mem_addCells r acc X h1 with h2 | ⟨hc, hs⟩
      · exact Or.inl h2
      · exact Or.inr ⟨hc, r, List.mem_cons_self .., hs⟩
    · exact Or.inr ⟨hc, r', List.mem_cons_of_mem _ hr', hs⟩

theorem nodup_foldl_addCells : ∀ (roots acc : List Noun), acc.Nodup →
    (roots.foldl (fun acc n => addCells n acc) acc).Nodup
  | [], acc, h => h
  | r :: rs, acc, h => by
    rw [List.foldl_cons]; exact nodup_foldl_addCells rs _ (nodup_addCells r acc h)

/-- **The members of the closure** are cells occurring in some root. -/
theorem mem_cellsOfRoots {roots : List Noun} {X : Noun} (h : X ∈ cellsOfRoots roots) :
    (∃ a b, X = .cell a b) ∧ ∃ r ∈ roots, SubN X r := by
  rcases mem_foldl_addCells roots [] X h with h1 | h1
  · simp at h1
  · exact h1

/-- **The closure has no duplicates.** -/
theorem cellsOfRoots_nodup (roots : List Noun) : (cellsOfRoots roots).Nodup :=
  nodup_foldl_addCells roots [] List.nodup_nil

variable {p : ℕ} [Fact p.Prime] {v : ℕ → ℕ → ZMod p} {n : ℕ} {N : ℕ → Noun}

/-- **Validity children are provided**: every cell occurring in a row noun is a row noun. -/
theorem sub_provided (L : NounLink v n N) {X m : Noun} (hs : SubN X m) (hX : ∃ a b, X = .cell a b) :
    (∃ i < n, N i = m) → ∃ i < n, N i = X := by
  induction hs with
  | refl => exact id
  | @left a b hs ih =>
    rintro ⟨i, hi, hN⟩
    obtain ⟨A, B, hNi, hl, -⟩ := L.link i hi
    rw [hN] at hNi
    injection hNi with hA hB
    rcases hl with ⟨-, hAt⟩ | ⟨-, c, hc, -, hNc, -⟩
    · exfalso
      obtain ⟨a', b', rfl⟩ := hX
      rw [hA, hAt] at hs
      exact Noun.noConfusion (subN_atom hs)
    · exact ih ⟨c, hc, by rw [hNc, hA]⟩
  | @right a b hs ih =>
    rintro ⟨i, hi, hN⟩
    obtain ⟨A, B, hNi, -, hr⟩ := L.link i hi
    rw [hN] at hNi
    injection hNi with hA hB
    rcases hr with ⟨-, hBt⟩ | ⟨-, c, hc, -, hNc, -⟩
    · exfalso
      obtain ⟨a', b', rfl⟩ := hX
      rw [hB, hBt] at hs
      exact Noun.noConfusion (subN_atom hs)
    · exact ih ⟨c, hc, by rw [hNc, hB]⟩

/-- **`closure_subset_of_roots`**: if every root that is a cell is a row noun, every closure noun is. -/
theorem closure_subset_of_roots (L : NounLink v n N) {roots : List Noun}
    (hroots : ∀ X ∈ roots, ∀ a b, X = .cell a b → ∃ i < n, N i = X) :
    ∀ X ∈ cellsOfRoots roots, ∃ i < n, N i = X := by
  intro X hX
  obtain ⟨hc, r, hr, hs⟩ := mem_cellsOfRoots hX
  cases r with
  | atom k =>
    obtain ⟨a, b, rfl⟩ := hc
    exact Noun.noConfusion (subN_atom hs)
  | cell a b => exact sub_provided L hs hc (hroots _ hr a b rfl)

/-- **`closure_subset`: every noun of the honest closure `cellsOfRoots (rootsOf c rows)` is a row noun.**
Hypotheses: the noun link (`nounLink_of_accepts`); a handle decoder `D` that agrees with the row nouns on cells
(`hDN`: a handle denoting a cell denotes a row noun — the cell table's decode); and the honest roots are denoted
(`hrowsC`: each claim noun and each handle noun of each honest row that is a cell is `D` of some handle, the decoded compute rows
being the honest rows). -/
theorem closure_subset (L : NounLink v n N) {D : LocalVSX.HX → Option Noun}
    (hDN : ∀ hd A B, D hd = some (.cell A B) → ∃ i < n, N i = .cell A B)
    (c : P8PublicClaim) (rows : Array Nock.Edit.GenX.RowNX)
    (hrowsC : ∀ X ∈ rootsOf c rows, ∀ A B, X = .cell A B → ∃ hd, D hd = some X) :
    ∀ X ∈ cellsOfRoots (rootsOf c rows), ∃ i < n, N i = X := by
  refine closure_subset_of_roots L fun X hX a b hc => ?_
  obtain ⟨hd, hD⟩ := hrowsC X hX a b hc
  rw [hc] at hD ⊢
  exact hDN hd a b hD

/-! ## 4. The row-noun set is the closure -/

variable {v' : ℕ → ℕ → ZMod p} {N' : ℕ → Noun}

/-- **`nouns_eq_closure`**: with as many rows as the closure has nouns, and every closure noun a row noun, the row
nouns (pairwise distinct, `nouns_inj`) are exactly the closure. -/
theorem nouns_eq_closure (T : TableM v n) (L : NounLink v n N) (hpG : p = Nock.Atoms.p) (hnp : n ≤ p)
    {cl : List Noun} (hnd : cl.Nodup) (hcard : n = cl.length) (hsub : ∀ X ∈ cl, ∃ i < n, N i = X) :
    ∀ m, (∃ i < n, N i = m) ↔ m ∈ cl := by
  classical
  have hS : ((List.range n).map N).Nodup :=
    (T.nouns_pairwise L hpG hnp).imp fun {x y} (hxy : nlt x y) (e : x = y) => nlt_irrefl y (e ▸ hxy)
  have hsubF : cl.toFinset ⊆ ((List.range n).map N).toFinset := by
    intro X hX
    rw [List.mem_toFinset] at hX ⊢
    rw [mem_range_map_iff]
    exact hsub X hX
  have hc1 : cl.toFinset.card = n := by rw [List.toFinset_card_of_nodup hnd, hcard]
  have hc2 : ((List.range n).map N).toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hS]; simp
  have heq := Finset.eq_of_subset_of_card_le hsubF (by rw [hc1, hc2])
  intro m
  rw [← mem_range_map_iff, ← List.mem_toFinset, ← heq, List.mem_toFinset]

/-- **`hset_of_closure`**: two linked tables whose row-noun sets are both the closure have the same noun set. -/
theorem hset_of_closure {n' : ℕ} {cl : List Noun} (h1 : ∀ m, (∃ i < n, N i = m) ↔ m ∈ cl)
    (h2 : ∀ m, (∃ i < n', N' i = m) ↔ m ∈ cl) : ∀ m, (∃ i < n, N i = m) ↔ (∃ j < n', N' j = m) :=
  fun m => (h1 m).trans (h2 m).symm

end Closure

/-! ## 5. The multiplicities -/

section Mul
variable {p : ℕ} [Fact p.Prime]

/-- **The four multiplicity columns are consumer counts** at every row (`CountsP1.mv_eq_count`, `mx_eq_count`,
`mx1_eq_count`, `mh_eq_count`, read through `cellEnvF_vM` / `hqkEF_vM`): `cnt k i` is the number of consumers of row
`i`'s key in balance `k` (`0` validity, `1` export side 0, `2` export side 1, `3` handle export). -/
structure MulCounts (v : ℕ → ℕ → ZMod p) (n : ℕ) (cnt : Fin 4 → ℕ → ℕ) : Prop where
  mv : ∀ i < n, v i Cell.mv = (cnt 0 i : ZMod p)
  mx : ∀ i < n, v i Cell.mx = (cnt 1 i : ZMod p)
  mx1 : ∀ i < n, v i Cell.mx1 = (cnt 2 i : ZMod p)
  mh : ∀ i < n, v i CellH.mh = (cnt 3 i : ZMod p)

/-- **`hmul_of_counts`**: two tables whose multiplicity columns are consumer counts, with the same consumer counts
row by row (the consumer lists agree under the compute and walk determination and the round-1 fingerprints agree, so
each row key is consumed equally often), agree on `mv mx mx1 mh`. -/
theorem hmul_of_counts {v v' : ℕ → ℕ → ZMod p} {n : ℕ} {cnt cnt' : Fin 4 → ℕ → ℕ}
    (C : MulCounts v n cnt) (C' : MulCounts v' n cnt') (hcnt : ∀ k, ∀ i < n, cnt k i = cnt' k i) :
    ∀ i < n, MulEq v v' i := fun i hi =>
  ⟨by rw [C.mv i hi, C'.mv i hi, hcnt 0 i hi], by rw [C.mx i hi, C'.mx i hi, hcnt 1 i hi],
    by rw [C.mx1 i hi, C'.mx1 i hi, hcnt 2 i hi], by rw [C.mh i hi, C'.mh i hi, hcnt 3 i hi]⟩

end Mul

/-! ## 6. Assembly -/

section Final
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`nounSet_of_accepts`**: per trace, the decoded row nouns are a `NounLink` and are exactly the honest closure,
given the validity-served cell table (`hS`), the handle decoder facts (`hDN`, `hrowsC`) and the table size (`hsz`). -/
theorem nounSet_of_accepts {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))))
    (rows : Array Nock.Edit.GenX.RowNX) (hsz : Pb.nC = (cellsOfRoots (rootsOf c rows)).length)
    {D : LocalVSX.HX → Option Noun}
    (hDN : ∀ hd A B, D hd = some (.cell A B) → ∃ i < Pb.nC, nounOf (vM tr ax Pb.orbitC.ω) i = .cell A B)
    (hrowsC : ∀ X ∈ rootsOf c rows, ∀ A B, X = .cell A B → ∃ hd, D hd = some X) :
    NounLink (vM tr ax Pb.orbitC.ω) Pb.nC (nounOf (vM tr ax Pb.orbitC.ω)) ∧
      ∀ m, (∃ i < Pb.nC, nounOf (vM tr ax Pb.orbitC.ω) i = m) ↔ m ∈ cellsOfRoots (rootsOf c rows) := by
  obtain ⟨T, -, L⟩ := nounLink_of_accepts δ b h hS
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  exact ⟨L, nouns_eq_closure T L hpG hnp (cellsOfRoots_nodup _) hsz (closure_subset L hDN c rows hrowsC)⟩

/-- **`r0M_auxM_final`: the cell table's round-0 and aux columns of two accepted traces agree** (the open facts
`OpenP1.r0M`, `OpenP1.auxM`). `OpenR0MP1.r0M_auxM_of_set` with the noun links (`nounLink_of_accepts`), the noun
set (`nounSet_of_accepts`, both traces equal to the honest closure of the same honest rows) and the multiplicities
(`hmul_of_counts`). Remaining hypotheses: the validity-served cell tables `hS`, `hS'` (`ServedP1.servedC_pair_P1`),
the handle decoders `hDN`, `hDN'` and the honest roots `hrowsC`, `hrowsC'` (the compute and walk determination), the
size `hsz`, and the consumer counts `C`, `C'` with `hcnt` (round 1). -/
theorem r0M_auxM_final {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC))))
    (rows : Array Nock.Edit.GenX.RowNX) (hsz : Pb.nC = (cellsOfRoots (rootsOf c rows)).length)
    {D D' : LocalVSX.HX → Option Noun}
    (hDN : ∀ hd A B, D hd = some (.cell A B) → ∃ i < Pb.nC, nounOf (vM tr ax Pb.orbitC.ω) i = .cell A B)
    (hDN' : ∀ hd A B, D' hd = some (.cell A B) → ∃ i < Pb.nC, nounOf (vM tr' ax' Pb.orbitC.ω) i = .cell A B)
    (hrowsC : ∀ X ∈ rootsOf c rows, ∀ A B, X = .cell A B → ∃ hd, D hd = some X) (hrowsC' : ∀ X ∈ rootsOf c rows, ∀ A B, X = .cell A B → ∃ hd, D' hd = some X)
    {cnt cnt' : Fin 4 → ℕ → ℕ} (C : MulCounts (vM tr ax Pb.orbitC.ω) Pb.nC cnt)
    (C' : MulCounts (vM tr' ax' Pb.orbitC.ω) Pb.nC cnt') (hcnt : ∀ k, ∀ i < Pb.nC, cnt k i = cnt' k i) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) := by
  obtain ⟨L, e1⟩ := nounSet_of_accepts δ b h hS rows hsz hDN hrowsC
  obtain ⟨L', e2⟩ := nounSet_of_accepts δ b h' hS' rows hsz hDN' hrowsC'
  exact r0M_auxM_of_set δ b h h' L L' (hset_of_closure e1 e2) (hmul_of_counts C C' hcnt)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.nounLink_of_served
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.rowServed_of_table
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.nounLink_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.closure_subset
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.nouns_eq_closure
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.hmul_of_counts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.nounSet_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1.r0M_auxM_final
