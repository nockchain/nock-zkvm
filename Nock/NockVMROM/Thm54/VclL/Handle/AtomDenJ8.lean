/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomDenJ8.lean

  **`atomInc_provOK`'s `hDen` and `hchain` from A-2.**
  New module, additive.

  * `denotes_unique`: a row's limb list is unique (`Denotes` is functional).
  * **`extA r`**, the definition of the external-atom denotation: `extA r j = atom (val l)` when row `j` denotes the
    limb list `l`, `none` otherwise.  `extA_of_denotes`; **`hDen_extA`** — `hDen` of `IncHeadJ8.atomInc_provOK` at
    `D = denK t (extA r)` (any cell table `t`), with no premise.  Since `ProvXJ8.provOK_x` and `WalkKJ8.provOK_p`
    are generic in `ext`, `D := denK (cellTable.map b0) (extA rA)` serves all three balances.
  * **`hchain_of_served`**: `hchain` of `atomInc_provOK` from A-2's `inc_chain_sound_of_served`, with A-2's
    `ConsumeServedQ` discharged by `AtomServedQ.consumeServedQ_of_balance` (summand #4 outside its IO event);
    the remaining premises are A-2's: `wL = 0` (g2), the ℕ reading (`Reads`, `Small`, `idx = k`), no inc past the
    table (`hrn`), `LimbsBounded` (g1), `wR ≤ 1`, and `ChainOK` at every inc row (`AtomChipHQ.chainOK_of_gates` per
    row, given the next row's `ReadsNext` and `aL, l_o < B`).

  Not here: `hold` (an inc row's old handle denotes: termination of the old row's `idR` chain).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ LimbsBounded ChainOK
  inc_chain_sound_of_served)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF atomEnvN atomEnvN_lt acoins atomCReqs atomProvs
  liftProvs consumeServedQ_of_balance)
open Nock.Atoms (val)

noncomputable section

/-! ## 1. `Denotes` is functional; the external-atom denotation `extA` -/

theorem denotes_unique {r : ℕ → ARow} {i : ℕ} {l l' : List ℕ} (h : Denotes r i l) (h' : Denotes r i l') :
    l = l' := by
  induction h generalizing l' with
  | @top j hw =>
    cases h' with
    | top _ => rfl
    | step hw' _ => rw [hw] at hw'; exact absurd hw' (by norm_num)
  | @step j l hw _ ih =>
    cases h' with
    | top hw' => rw [hw] at hw'; exact absurd hw' (by norm_num)
    | step _ hd' => rw [ih hd']

open Classical in
/-- **The external-atom denotation** of the atom table read as `r`: handle `(2, j)` denotes `val l` when row `j`
denotes the limb list `l` (unique, `denotes_unique`). -/
def extA (r : ℕ → ARow) (j : ℕ) : Option Noun :=
  if h : ∃ l, Denotes r j l then some (.atom (val (Classical.choose h))) else none

theorem extA_of_denotes {r : ℕ → ARow} {j : ℕ} {l : List ℕ} (h : Denotes r j l) :
    extA r j = some (.atom (val l)) := by
  have he : ∃ l, Denotes r j l := ⟨l, h⟩
  simp only [extA, dif_pos he]
  rw [denotes_unique (Classical.choose_spec he) h]

/-- **`hDen` of `atomInc_provOK`** at `D = denK t (extA r)`. -/
theorem hDen_extA {q : ℕ} (t : List (CellRowB0 q)) (r : ℕ → ARow) :
    ∀ j l, Denotes r j l → denK t (extA r) (2, j) = some (.atom (val l)) :=
  fun _ _ h => extA_of_denotes h

theorem hD0_denK {q : ℕ} (t : List (CellRowB0 q)) (e : ℕ → Option Noun) :
    ∀ v, denK t e (0, v) = some (.atom v) := fun _ => rfl

/-! ## 2. `hchain` from A-2 with `ConsumeServedQ` from the atom export balance -/

section Chain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  [DecidableEq F] [DecidableEq K] [DecidableEq (Quad (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **`hchain` of `atomInc_provOK` from A-2**: on an accepted `atomChipHQ` trace whose export balance holds
(summand #4: `hbal`, outside its IO event `hout`, counts `< p`), under A-2's ℕ-level premises, every inc row whose
old handle denotes `l_old` denotes some `l_new` with `val l_new = val l_old + 1`. -/
theorem hchain_of_served {p : ℕ} [CharP 𝕂′ p] (hq : 2 ^ 63 < ringChar F)
    (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (wreqs : List (Fin 5 → K))
    (hbal : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubs AtomChipHQ.pubC) (pubs (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (acoins δF chals) r)⁻¹).sum)
    (hout : ((acoins δF chals).gamma, (acoins δF chals).pole) ∉
      IOFailureEventW ((atomCReqs b nodes orbit chals pubs Q ++ wreqs).map (liftRec (K := K) (L := 𝕂′)))
        (liftProvs δF (atomProvs b nodes orbit chals pubs Q)))
    (hcount : (atomCReqs b nodes orbit chals pubs Q ++ wreqs).length < p)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (aEF b nodes orbit chals pubs Q k) (r k))
    (hs : ∀ k : Fin n, (r k).Small) (hidx : ∀ k : Fin n, (r k).idx = k)
    (hwL : ∀ k : Fin n, (aEF b nodes orbit chals pubs Q k).trace Cell.wL = 0)
    (hrn : ∀ k, n ≤ k → (r k).inc = 0) (hB : LimbsBounded r) (hw : ∀ j, (r j).wR ≤ 1)
    (hok : ∀ j, (r j).inc = 1 → ChainOK r j) :
    ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1 := by
  have hserved := consumeServedQ_of_balance δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj wreqs hbal
    hout hcount
  intro k hinc lold hold
  refine inc_chain_sound_of_served hq (env := atomEnvN b hn nodes orbit chals pubs Q) (n := n)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => hs ⟨k, hk⟩) (fun k hk => hidx ⟨k, hk⟩) hserved hrn hB hw hok
    hinc hold
  · rw [show k = ((⟨k, hk⟩ : Fin n) : ℕ) from rfl, atomEnvN_lt]; exact hR ⟨k, hk⟩
  · rw [show k = ((⟨k, hk⟩ : Fin n) : ℕ) from rfl, atomEnvN_lt]; exact hwL ⟨k, hk⟩

end Chain

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8
