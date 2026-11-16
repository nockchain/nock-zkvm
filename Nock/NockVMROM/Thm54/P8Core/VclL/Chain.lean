/-
  Nock/NockVMROM/Thm54/P8Core/VclL/Chain.lean

  **T3, `chain_sound` at the real NPR.**

  The genuine-table
  hypothesis of the pregreen is now a THEOREM (`row_genuine`, T1); what remains is injectivity.

  **The injectivity T3 needs, measured exactly** (both hypotheses are used, each at one place):
  * `hinj` — `enc z` injective on the decoded set `decodedNouns` (used when an edge's `p` equals the
    current node's fingerprint and the current node is a decoded cell): priced by T2
    (`decodedNouns_inj_of_not_mem`);
  * `hatom` — no ATOM CHILD of a row (a zero-weight child `atom aX.val`, `wX = false`) has the
    fingerprint of a decoded cell (used when an edge continues from a node reached through a
    zero-weight child).  **T2 does not price these pairs**: the atom children are not in T2's noun
    list `decodedNouns ++ skel`.  See `chain_needs_atom_pairs` for the step that consumes it.

  * `chainWalk`, `axisFold`, `chain_slot`, `axisFold_lt` (the pregreen's, verbatim);
  * `Edge`, `childOf`, `chainEnd`, `EdgeExported`, `ExportBalanced`, `edge_exported_of_balanced`;
  * `AtomChildren`, `decodeB0_idx_lt`;
  * **T3** `chain_sound` (any root in the decoded set or an atom child), `chain_sound_root`
    (option R: the root is `preZNounOfTable rootIdx`), `chain_sound_of_census` (T2's event plus the
    atom-child hypothesis).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Census

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. The noun-level chain (`VclProbes` §0, verbatim) -/

def chainWalk : Noun → List Bool → Option Noun
  | n, [] => some n
  | .cell l r, b :: bs => chainWalk (if b then r else l) bs
  | .atom _, _ :: _ => none

def axisFold (bits : List Bool) : ℕ :=
  bits.foldl (fun a b => 2 * a + (if b then 1 else 0)) 1

theorem axisFold_append (bits : List Bool) (b : Bool) :
    axisFold (bits ++ [b]) = 2 * axisFold bits + (if b then 1 else 0) := by
  unfold axisFold; simp [List.foldl_append]

theorem chainWalk_append (n : Noun) (bits : List Bool) (b : Bool) :
    chainWalk n (bits ++ [b]) =
      match chainWalk n bits with
      | some (.cell l r) => some (if b then r else l)
      | _ => none := by
  induction bits generalizing n with
  | nil => cases n <;> simp [chainWalk]
  | cons c cs ih =>
    cases n with
    | atom a => simp [chainWalk]
    | cell l r => simp only [List.cons_append, chainWalk]; exact ih _

theorem axisFold_pos (bits : List Bool) : 1 ≤ axisFold bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [axisFold]
  | append_singleton bs b _ => rw [axisFold_append]; omega

/-- **The fold of the side bits is the Nock axis**. -/
theorem chain_slot (root : Noun) (bits : List Bool) :
    Noun.slot (axisFold bits) root = chainWalk root bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [axisFold, chainWalk, Noun.slot]
  | append_singleton bs b ih =>
    rw [axisFold_append, chainWalk_append, ← ih]
    have h1 := axisFold_pos bs
    obtain ⟨a, ha⟩ : ∃ a, 2 * axisFold bs + (if b then 1 else 0) = a + 2 :=
      ⟨2 * axisFold bs + (if b then 1 else 0) - 2, by split_ifs <;> omega⟩
    rw [ha, Noun.slot]
    have hdiv : (a + 2) / 2 = axisFold bs := by split_ifs at ha <;> omega
    have hmod : ((a + 2) % 2 == 0) = !b := by
      cases b <;> simp at ha <;> simp <;> omega
    rw [hdiv, hmod]
    cases Noun.slot (axisFold bs) root with
    | none => rfl
    | some n => cases n with
      | atom _ => rfl
      | cell l r => cases b <;> rfl

theorem axisFold_lt (bits : List Bool) : axisFold bits < 2 ^ (bits.length + 1) := by
  induction bits using List.reverseRecOn with
  | nil => simp [axisFold]
  | append_singleton bs b ih =>
    rw [axisFold_append]; simp only [List.length_append, List.length_singleton]
    rw [pow_succ]; split_ifs <;> omega

/-! ## 2. The path chip's edges (option R) -/

section Edges
variable {q : ℕ} {Kfp : Type} [Field Kfp]

/-- A path-chip edge row: the consumed cell `(p, l, r)`, its serial `cellIdx` (B0), the side bit. -/
structure Edge (Kfp : Type) where
  p : FP Kfp
  l : FP Kfp
  r : FP Kfp
  side : Bool
  cellIdx : ℕ

def childOf (e : Edge Kfp) : FP Kfp := if e.side then e.r else e.l

/-- Decidable equality of fingerprint triples (coordinatewise). -/
instance fpDecEq [DecidableEq Kfp] : DecidableEq (FP Kfp) := fun a b =>
  if h : a.size = b.size ∧ a.dyck = b.dyck ∧ a.leaf = b.leaf then
    isTrue (FP.ext h.1 h.2.1 h.2.2)
  else isFalse (fun hab => h (hab ▸ ⟨rfl, rfl, rfl⟩))

/-- The chain's terminal fingerprint, linking each edge's parent to the previous child. -/
def chainEnd [DecidableEq Kfp] : FP Kfp → List (Edge Kfp) → Option (FP Kfp)
  | cur, [] => some cur
  | cur, e :: es => if e.p = cur then chainEnd (childOf e) es else none

/-- An edge is exported by the table: a row at serial `cellIdx` carries exactly `(p, l, r)`. -/
def EdgeExported (t : List (CellRow q Kfp)) (e : Edge Kfp) : Prop :=
  ∃ c ∈ t, c.b0.idx = e.cellIdx ∧ c.p = e.p ∧ c.l = e.l ∧ c.r = e.r

/-- Export keys `(p, l, r, idx)` (option R, `m_x = 10`). -/
abbrev XKey (Kfp : Type) := FP Kfp × FP Kfp × FP Kfp × ℕ

def xProv (t : List (CellRow q Kfp)) : List (XKey Kfp × ℕ) :=
  t.map fun c => ((c.p, c.l, c.r, c.b0.idx), c.b0.mx)

/-- **The export multiset balance**: the table's exports = the path chip's edge consumptions plus
the compute-side cell lookups `cl`. -/
def ExportBalanced (t : List (CellRow q Kfp)) (edges : List (Edge Kfp)) (cl : List (XKey Kfp)) :
    Prop :=
  (expand (xProv t)).Perm
    (expand (edges.map (fun e => ((e.p, e.l, e.r, e.cellIdx), 1)) ++ cl.map (·, 1)))

theorem edge_exported_of_balanced {t : List (CellRow q Kfp)} {edges : List (Edge Kfp)}
    {cl : List (XKey Kfp)} (h : ExportBalanced t edges cl) {e : Edge Kfp} (he : e ∈ edges) :
    EdgeExported t e := by
  have hmem : (e.p, e.l, e.r, e.cellIdx) ∈
      expand (edges.map (fun e => ((e.p, e.l, e.r, e.cellIdx), 1)) ++ cl.map (·, 1)) := by
    rw [mem_expand]
    exact ⟨((e.p, e.l, e.r, e.cellIdx), 1), List.mem_append_left _ (List.mem_map_of_mem he),
      one_ne_zero, rfl⟩
  have hprov := h.mem_iff.mpr hmem
  rw [mem_expand] at hprov
  obtain ⟨kc, hkc, -, hk⟩ := hprov
  simp only [xProv, List.mem_map] at hkc
  obtain ⟨c, hc, rfl⟩ := hkc
  simp only [Prod.mk.injEq] at hk
  exact ⟨c, hc, hk.2.2.2.symm, hk.1.symm, hk.2.1.symm, hk.2.2.1.symm⟩

/-- The atom children of a table: the nouns named by zero-weight child slots. -/
def AtomChildren (t : List (CellRow q Kfp)) : Set Noun :=
  {n | ∃ c ∈ t, (c.b0.wL = false ∧ n = .atom c.b0.aL.val) ∨ (c.b0.wR = false ∧ n = .atom c.b0.aR.val)}

end Edges

/-- A decoded serial is in range. -/
theorem decodeB0_idx_lt {q : ℕ} (t : List (CellRowB0 q)) :
    ∀ f i n, decodeB0 t f i = some n → i < t.length
  | 0, _, _, h => by simp [decodeB0] at h
  | f + 1, i, n, h => by
    simp only [decodeB0, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, -⟩ := h
    exact (List.getElem?_eq_some_iff.mp hc).1

/-! ## 3. T3 -/

section T3
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

theorem mem_decodedNouns_of {t : List (CellRowB0 q)} {i : ℕ} {n : Noun}
    (h : preZNounOfTable t i = some n) : n ∈ decodedNouns t :=
  mem_decodedNouns.mpr ⟨i, decodeB0_idx_lt t _ _ _ h, h⟩

/-- **T3 (`chain_sound` at the real NPR).**  On an accepted table, if `enc z` is injective on the
decoded set (`hinj`, T2) and no atom child collides with a decoded cell (`hatom`), then every
linked chain of exported edges from a root that is decoded (or an atom child) ends at the
fingerprint of `Noun.slot (axisFold sides) root`, which is again decoded or an atom child. -/
theorem chain_sound [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (hinj : ∀ a ∈ decodedNouns (t.map (·.b0)), ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z b → a = b)
    (hatom : ∀ a ∈ AtomChildren t, ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a ≠ GlobalCarryRecognizer.enc z b) :
    ∀ (es : List (Edge Kfp)) (root : Noun),
      (root ∈ decodedNouns (t.map (·.b0)) ∨ root ∈ AtomChildren t) →
      (∀ e ∈ es, EdgeExported t e) →
      ∀ ch, chainEnd (GlobalCarryRecognizer.enc z root) es = some ch →
        ∃ n, GlobalCarryRecognizer.enc z n = ch ∧
          chainWalk root (es.map Edge.side) = some n ∧
          Noun.slot (axisFold (es.map Edge.side)) root = some n ∧
          (n ∈ decodedNouns (t.map (·.b0)) ∨ n ∈ AtomChildren t) := by
  intro es
  induction es with
  | nil =>
    intro root hS _ ch hend
    simp only [chainEnd, Option.some.injEq] at hend
    exact ⟨root, hend, rfl, by rw [chain_slot]; rfl, hS⟩
  | cons e es ih =>
    intro root hS hexp ch hend
    obtain ⟨c, hc, hidx, hp, hl, hr⟩ := hexp e (by simp)
    obtain ⟨L, R, hd, hcp, hcl, hcr, hLw, hLa, hRw, hRa⟩ := row_genuine hq hz h hc
    have hcellD : Noun.cell L R ∈ decodedNouns (t.map (·.b0)) := mem_decodedNouns_of hd
    simp only [chainEnd] at hend
    by_cases hpe : e.p = GlobalCarryRecognizer.enc z root
    swap
    · rw [if_neg hpe] at hend; exact absurd hend (by simp)
    rw [if_pos hpe] at hend
    have hfp : GlobalCarryRecognizer.enc z root = GlobalCarryRecognizer.enc z (.cell L R) := by
      rw [← hpe, ← hp, hcp]
    have hroot : root = Noun.cell L R := by
      rcases hS with hS | hS
      · exact hinj root hS _ hcellD hfp
      · exact absurd hfp (hatom root hS _ hcellD)
    subst hroot
    have hchild : childOf e = GlobalCarryRecognizer.enc z (if e.side then R else L) := by
      simp only [childOf, ← hl, ← hr, hcl, hcr]; split_ifs <;> rfl
    rw [hchild] at hend
    have hchS : (if e.side then R else L) ∈ decodedNouns (t.map (·.b0)) ∨
        (if e.side then R else L) ∈ AtomChildren t := by
      split_ifs
      · cases hw : c.b0.wR
        · exact Or.inr ⟨c, hc, Or.inr ⟨hw, hRa hw⟩⟩
        · exact Or.inl (mem_decodedNouns_of (hRw hw))
      · cases hw : c.b0.wL
        · exact Or.inr ⟨c, hc, Or.inl ⟨hw, hLa hw⟩⟩
        · exact Or.inl (mem_decodedNouns_of (hLw hw))
    obtain ⟨n, hfn, hwalk, -, hnS⟩ :=
      ih _ hchS (fun e' he' => hexp e' (by simp [he'])) ch hend
    refine ⟨n, hfn, ?_, ?_, hnS⟩
    · simp only [List.map_cons, chainWalk]; exact hwalk
    · rw [chain_slot]; simp only [List.map_cons, chainWalk]; exact hwalk

/-- **T3 at option R**: the chain's root is the B0 decode of `rootIdx` (the chain's first
`cellIdx`); the record's child is the fingerprint of `Noun.slot (axisFold sides) root`. -/
theorem chain_sound_root [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (hinj : ∀ a ∈ decodedNouns (t.map (·.b0)), ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z b → a = b)
    (hatom : ∀ a ∈ AtomChildren t, ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a ≠ GlobalCarryRecognizer.enc z b)
    {rootIdx : ℕ} {root : Noun} (hroot : preZNounOfTable (t.map (·.b0)) rootIdx = some root)
    (es : List (Edge Kfp)) (hexp : ∀ e ∈ es, EdgeExported t e) {ch : FP Kfp}
    (hend : chainEnd (GlobalCarryRecognizer.enc z root) es = some ch) :
    ∃ n, GlobalCarryRecognizer.enc z n = ch ∧
      Noun.slot (axisFold (es.map Edge.side)) root = some n := by
  obtain ⟨n, hfn, -, hslot, -⟩ :=
    chain_sound hq hz h hinj hatom es root (Or.inl (mem_decodedNouns_of hroot)) hexp ch hend
  exact ⟨n, hfn, hslot⟩

/-- **T3 from the census**: outside T2's bad seeds and under `hatom`. -/
theorem chain_sound_of_census [Fintype Kfp] [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    (hz : z ≠ 0) {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (skel : List Noun) (hgood : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) skel)
    (hatom : ∀ a ∈ AtomChildren t, ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a ≠ GlobalCarryRecognizer.enc z b)
    {rootIdx : ℕ} {root : Noun} (hroot : preZNounOfTable (t.map (·.b0)) rootIdx = some root)
    (es : List (Edge Kfp)) (hexp : ∀ e ∈ es, EdgeExported t e) {ch : FP Kfp}
    (hend : chainEnd (GlobalCarryRecognizer.enc z root) es = some ch) :
    ∃ n, GlobalCarryRecognizer.enc z n = ch ∧
      Noun.slot (axisFold (es.map Edge.side)) root = some n :=
  chain_sound_root hq hz h (decodedNouns_inj_of_not_mem hq hz h skel hgood) hatom hroot es hexp hend

theorem chain_needs_atom_pairs [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {a : Noun} (e : Edge Kfp) (es : List (Edge Kfp)) (hexp : EdgeExported t e) {ch : FP Kfp}
    (hend : chainEnd (GlobalCarryRecognizer.enc z a) (e :: es) = some ch) :
    ∃ n ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z n ∧ ∃ L R, n = .cell L R := by
  obtain ⟨c, hc, -, hp, -, -⟩ := hexp
  obtain ⟨L, R, hd, hcp, -⟩ := row_genuine hq hz h hc
  simp only [chainEnd] at hend
  by_cases hpe : e.p = GlobalCarryRecognizer.enc z a
  swap
  · rw [if_neg hpe] at hend; exact absurd hend (by simp)
  exact ⟨_, mem_decodedNouns_of hd, by rw [← hpe, ← hp, hcp], L, R, rfl⟩

end T3

end Nock.NockVMROM.Thm54.VclL
