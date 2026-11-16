/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BOf.lean

* `famsAll9 = famsOf (j8DataOf) ++ famsA (j9DataOf)`; **`BRun9`**: `ComplJ8Closed.BRunA` with the compute trace at
    the J-9 publics (`ComplJ9BComp.trCOf9`), the atom table (trace and publics) at `j9DataOf`, the bad list at
    `famsAll9`.
  * `good9`: a `BRun9`-good coin is good for `BOf … fams` at any `fams ⊆ famsAll9`.
  * `compute_group9`: the compute fields of `ComplJ9BObligations` at `BRun9` (no claim-leaf binder).
  * `claim_run9`: the J-9 claim field at `BRun9` (`hclI` at cell / big positions, `hcen'` via the spine of every big
    claim leaf lying in `acs`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9B
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BComp
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom
import Nock.V1J9.GenJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf mbCountsP bigIdOfP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (tripOf)

noncomputable section

/-! ## 1. The J-9 data: `mb` with the claim's big atoms -/

/-- **`mb9`** (`GenJ9.mbCounts9` at `p`): `mbCountsP` plus one at the atom root of each big claim atom.  Sealed
(`irreducible_def`, equation `mbCountsP9_def`) so that comparisons of `j9DataOf` with `j8DataOf` fail fast at `mb`. -/
irreducible_def mbCountsP9 (p : ℕ) (acsL cs : List Noun) (c : P8PublicClaim) : Array ℕ :=
  ((ClaimJ9.claimBigs p c).map fun k => FrameVS.claimNoun c k).foldl (fun a n => match bigIdOfP p acsL n with
    | some i => Nock.V1J8.Gen.bump a i 1
    | none => a) (mbCountsP p acsL cs)

/-- `j8DataOf` with `mb`
bumped once at the atom root of every big claim atom (`mbX`; a small atom or a cell gets no bump). Its `mb` is the
transcription `mbCountsP9` of the generator's (`j9_mb_eq`, `mbCountsP9_gen`). -/
abbrev j9DataOf (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) : J8Data p Rg fuel s f r :=
  ComplJ9BAtom.D9 (p := p) Rt hgen [s, f, r]

/-! ### The generator correspondence of `mb9` -/

section MbGen
variable {p : ℕ} [Fact p.Prime]

/-- **The claim's big positions are exactly its big atoms**: on the claim's nouns, filtering by `isBigN` first does
not change the atom-root pairs (`bigIdOfP` is `none` off big atoms, in particular on a cell, whatever big leaves it
holds). -/
theorem extraPairs_claimBigs (acs : List Noun) (c : P8PublicClaim) :
    ComplJ9BAtom.extraPairs p acs ((ClaimJ9.claimBigs p c).map (FrameVS.claimNoun c)) =
      ComplJ9BAtom.extraPairs p acs [c.subject, c.formula, c.result] := by
  have key : ∀ n : Noun, ClaimJ9.isBigN p n = false → bigIdOfP p acs n = none := by
    intro n hn
    cases n with
    | atom v =>
      have : ¬ p ≤ v := by simpa [ClaimJ9.isBigN] using hn
      simp [bigIdOfP, show v < p by omega]
    | cell a d => rfl
  have hfilt : ∀ l : List Noun, ComplJ9BAtom.extraPairs p acs (l.filter (ClaimJ9.isBigN p)) =
      ComplJ9BAtom.extraPairs p acs l := by
    intro l
    induction l with
    | nil => rfl
    | cons n l ih =>
      unfold ComplJ9BAtom.extraPairs at ih ⊢
      by_cases hb : ClaimJ9.isBigN p n = true
      · simp [List.filter_cons, hb, List.filterMap_cons, ih]
      · have hn : ClaimJ9.isBigN p n = false := by simpa using hb
        simp [List.filter_cons, hn, List.filterMap_cons, key n hn, ih]
  have e : (ClaimJ9.claimBigs p c).map (FrameVS.claimNoun c) =
      [c.subject, c.formula, c.result].filter (ClaimJ9.isBigN p) := by
    have hl : [c.subject, c.formula, c.result] = (List.finRange 3).map (FrameVS.claimNoun c) := rfl
    unfold ClaimJ9.claimBigs
    rw [hl, List.filter_map]
    rfl
  rw [e, hfilt]

/-- **`mb9` of the run is the transcription `mbCountsP9`** (the generator's claim-big-atom export at modulus `p`). -/
theorem j9_mb_eq (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j9DataOf p Rg Rt hgen).mb =
      mbCountsP9 p (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).cells (cJ s f r) := by
  rw [mbCountsP9_def]
  refine Eq.symm ((ComplJ9BAtom.foldl_bumpOpt_eq p _ _ _).trans ?_)
  rw [extraPairs_claimBigs]
  rfl

end MbGen

/-- **`mbCountsP9` at Goldilocks is the J-9 generator's `mb`** (`GenJ9.mbCounts9`, what `genJ9A` exports). -/
theorem mbCountsP9_gen (acsL cs : List Noun) (c : P8PublicClaim) :
    mbCountsP9 Nock.V1J8.Gen.P acsL cs c = Nock.V1J9.Gen9.mbCounts9 acsL cs c := by
  rw [mbCountsP9_def]
  rfl

/-! ## 2. The honest record -/

/-- **The J-9 compute trace, sealed** (`trCOf9` behind `irreducible_def`): `BRunG` and L6's `BOf` differ only in the
compute trace, and the sealed constant makes every failed whole-record comparison between them stop at once instead
of unfolding both compute traces. -/
irreducible_def trC9w {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    (b : Basis (Fin 3) (ZMod p) K) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (W : List (NTree SkelX)) (c : P8PublicClaim) (χ : Coins frameJ8 K) {n : ℕ} (nodes : Fin n → ZMod p) :
    Fin 123 → (ZMod p)[X] :=
  ComplJ9BComp.trCOf9 δ b H pd W c χ nodes


section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "D9" => j9DataOf p Rg Rt hgen

/-- The J-9 data's divisibility side condition (as `DD`'s: the sizes do not read `mb`). -/
theorem dvd9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 DD) : DvdOK D9 := dvdOK_of_rows hpG _ h31

theorem acs9_pos : 0 < (D9).acs.length := acs_pos Rt hgen

/-- **The run's pole families at J-9, at atom families `FA`**: `famsOf` at `DD` (compute, cell, walk, J) and the
atom table / atom walk families `FA`. -/
def famsAll9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 DD) (FA : List (List (BadSpec K))) : List (List (BadSpec K)) :=
  famsOf δ b DD (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) ++ FA

/-- **The J-9 B honest record of the run at an atom part `AV` and atom families `FA`**: L6's `BOf` at `AV` and
`famsAll9 FA` (so the atom table and atom walk, traces and publics, are `AV`'s and the bad list is at `famsAll9 FA`)
with the compute trace at `pubVJ9` (`trCOf9`).  Every other field is `BOf`'s, i.e. `BRunA`'s. -/
def BRunG (hpG : p = Nock.Atoms.p) (h31 : Rows31 DD) (AV : AVPart p K) (FA : List (List (BadSpec K))) :
    HonestJ8 p K δ Rg fuel s f r where
  t := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).t
  hgen := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).hgen
  H := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).H
  pd := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).pd
  Pb := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).Pb
  M := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).M
  tr := fun χ =>
    { C := trC9w δ b (DD).H (DD).pd (bfsForest [(DD).t]) (cJ s f r) χ (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).Pb.nodes
      M := ((BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).tr χ).M
      W := ((BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).tr χ).W
      J := ((BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).tr χ).J
      A := ((BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).tr χ).A
      V := ((BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).tr χ).V }
  rows := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).rows
  g := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).g
  bad := (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).bad


def famsA9 (D DW : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) : List (List (BadSpec K)) :=
  [famAZ, famAV δ D, famAH δ b D hA (orbJ8 D hF), famMB δ b D hA (orbJ8 D hF), famC δ b D hA (orbJ8 D hF),
    famMI δ b D hA (orbJ8 D hF), ComplJ9BBalF.famAWV9 δ DW, ComplJ9BBalF.famAWH9 δ DW]


abbrev AV9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 DD) : AVPart p K :=
  ComplJ9BBalF.avOf9 δ b DD (dvdOK_of_rows hpG _ h31) (avOf δ b D9 (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen))

/-- **The J-9 B honest record of the run** (`BRunG` at the J-9 atom part and families). -/
abbrev BRun9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 DD) : HonestJ8 p K δ Rg fuel s f r :=
  BRunG δ b Rt hgen hpG h31 (AV9 δ b Rt hgen hpG h31) (famsA9 δ b D9 DD (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen))

variable (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (AV : AVPart p K) (FA : List (List (BadSpec K)))

theorem BRun9_t : (BRunG δ b Rt hgen hpG h31 AV FA).t = (BRunA δ b Rt hgen hpG h31).t := rfl
theorem BRun9_H : (BRunG δ b Rt hgen hpG h31 AV FA).H = (BRunA δ b Rt hgen hpG h31).H := rfl
theorem BRun9_pd : (BRunG δ b Rt hgen hpG h31 AV FA).pd = (BRunA δ b Rt hgen hpG h31).pd := rfl
theorem BRun9_Pb : (BRunG δ b Rt hgen hpG h31 AV FA).Pb = (BRunA δ b Rt hgen hpG h31).Pb := rfl
theorem BRun9_pubsA (χ : Coins frameJ8 K) : ((BRunG δ b Rt hgen hpG h31 AV FA).M χ).pubsA = AV.pubsA χ := rfl
theorem BRun9_pubsV (χ : Coins frameJ8 K) : ((BRunG δ b Rt hgen hpG h31 AV FA).M χ).pubsV = AV.pubsV χ := rfl
theorem BRun9_trA (χ : Coins frameJ8 K) : ((BRunG δ b Rt hgen hpG h31 AV FA).tr χ).A = AV.trA χ := rfl
theorem BRun9_trV (χ : Coins frameJ8 K) : ((BRunG δ b Rt hgen hpG h31 AV FA).tr χ).V = AV.trV χ := rfl

/-- **`BRunG`-good coins are good for `BOf … AV' fams` at any family list inside `famsAll9 FA`** (any atom part). -/
theorem good9 (AV' : AVPart p K) {fams : List (List (BadSpec K))}
    (hsub : ∀ L ∈ fams, L ∈ famsAll9 δ b Rt hgen hpG h31 FA) (χ : Coins frameJ8 K)
    (h : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV' fams).Good χ :=
  good_mono δ b Rt hgen _ _ _ AV' hsub χ h

/-- `BRunG`-good coins are `BRun`-good (the J-8 record at `famsOf`, where the J-8 balance lemmas live). -/
theorem good9_run (χ : Coins frameJ8 K) (h : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    (BRun δ b Rt hgen hpG h31).Good χ :=
  good9 δ b Rt hgen hpG h31 AV FA _ (fun L hL => List.mem_append_left _ hL) χ h

/-- `BRunG`-good coins avoid every event of every atom family in `FA`. -/
theorem good9_FA (χ : Coins frameJ8 K) (h : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    ∀ L ∈ FA, ∀ e ∈ L, χ ∉ e.ev := by
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DD).t]).length)] (famsAll9 δ b Rt hgen hpG h31 FA)),
      χ ∉ e.1 := h
  intro L hL e he
  exact ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, List.mem_append_right _ hL, he⟩))

/-! ## 3. The compute fields at `pubVJ9` -/

theorem pubJ9_eq (χ : Coins frameJ8 K) :
    ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ =
      ComplJ9BComp.pubCOf9 δ b (DD).H (DD).pd (bfsForest [(DD).t]) (cJ s f r) χ := rfl

/-- **The compute group of `ComplJ9BObligations` at `BRun9`** (no claim-leaf binder). -/
theorem compute_group9 (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t) :
    HonestCompX.HdlOK (ringChar (ZMod p)) (BRunG δ b Rt hgen hpG h31 AV FA).H ∧
    (∀ u, InTree (BRunG δ b Rt hgen hpG h31 AV FA).t u → HonestCompX.isPair (BRunG δ b Rt hgen hpG h31 AV FA).H (rowOfSkelX u.label) →
      HonestCompX.PairOK (F := ZMod p) ((BRunG δ b Rt hgen hpG h31 AV FA).pd (rowOfSkelX u.label))) ∧
    (BRunG δ b Rt hgen hpG h31 AV FA).Pb.n = (BRunG δ b Rt hgen hpG h31 AV FA).W.length ∧
    (∀ χ, limbVal b (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) ChipH.pubIC = ComplJ8.αJ b χ) ∧
    (∀ χ, limbVal b (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) ChipH.pubSeed =
      VclL.HonestTraceX.curW (F := ZMod p) (BRunG δ b Rt hgen hpG h31 AV FA).H (BRunG δ b Rt hgen hpG h31 AV FA).W (ComplJ8.γJ b χ) 1 * ComplJ8.αJ b χ) ∧
    (∀ χ, limbVal b (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) ChipH.pubOut = 0) ∧
    (∀ χ, ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 0 = HonestCompX.hk (BRunG δ b Rt hgen hpG h31 AV FA).H s ∧ ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 1 = HonestCompX.hv (BRunG δ b Rt hgen hpG h31 AV FA).H s ∧
      ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 2 = HonestCompX.hk (BRunG δ b Rt hgen hpG h31 AV FA).H f ∧ ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 3 = HonestCompX.hv (BRunG δ b Rt hgen hpG h31 AV FA).H f ∧
      ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 4 = HonestCompX.hk (BRunG δ b Rt hgen hpG h31 AV FA).H r ∧ ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ 5 = HonestCompX.hv (BRunG δ b Rt hgen hpG h31 AV FA).H r) ∧
    (∀ χ, ∀ a < 6, ∀ k : Fin 3, ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ (VclL.HonestTraceX.pubOfA a + k) =
      coord b (VclL.HonestTraceX.accV b δ (BRunG δ b Rt hgen hpG h31 AV FA).H (BRunG δ b Rt hgen hpG h31 AV FA).pd (BRunG δ b Rt hgen hpG h31 AV FA).W (chalVJ8 b χ) (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) a (BRunG δ b Rt hgen hpG h31 AV FA).Pb.n) k) ∧
    (∀ χ, (BRunG δ b Rt hgen hpG h31 AV FA).Good χ → (BRunG δ b Rt hgen hpG h31 AV FA).W.length ≤ orderOf (ComplJ8.αJ b χ) ∧
      ∀ j < (BRunG δ b Rt hgen hpG h31 AV FA).Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
        HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 (BRunG δ b Rt hgen hpG h31 AV FA).H (BRunG δ b Rt hgen hpG h31 AV FA).pd (BRunG δ b Rt hgen hpG h31 AV FA).W (chalVJ8 b χ) (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) j) ≠ 0 ∨
          HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 (BRunG δ b Rt hgen hpG h31 AV FA).H (BRunG δ b Rt hgen hpG h31 AV FA).pd (BRunG δ b Rt hgen hpG h31 AV FA).W (chalVJ8 b χ) (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) j) = 0) := by
  have hH' : HonestCompX.HdlOK p (DD).H := by
    have := ComplJ8CompRun.hH_run Rt hgen (p := p); rwa [ZMod.ringChar_zmod_n] at this
  have hlab := genX_label hgen
  have hroot : tripOf (DD).t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, j8DataOf, hlab.1, hlab.2.1, hlab.2.2.1]
  refine ⟨ComplJ8CompRun.hH_run Rt hgen (p := p),
    ComplJ8Atom.hpair_of_binders hgen (ComplJ8CompRun.hH_run Rt hgen) hp63 _ hax hop5,
    rfl, fun χ => ComplJ9BComp.hpIC9 δ b _ _ _ _ χ,
    fun χ => ComplJ9BComp.hpS9 δ b (DD).pd _ hH' rfl hroot χ, fun χ => ComplJ9BComp.hpO9 δ b _ _ _ _ χ,
    fun χ => ComplJ9BComp.hpub9 δ b (DD).pd _ hH' χ, fun χ => ComplJ9BComp.hρ9 δ b _ _ _ _ χ, ?_⟩
  intro χ hχ
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DD).t]).length)] (famsAll9 δ b Rt hgen hpG h31 FA)),
      χ ∉ e.1 := hχ
  refine ⟨?_, fun j hj S hS => ?_⟩
  · rw [ComplJ8Bad.αJ_eq]
    exact ComplJ8Bad.good_ord hg (List.mem_append_left _ (List.mem_singleton_self _))
  · have hcomp : ComplJ8CompPole.compPoles (K := K) δ (DD).H (DD).pd (bfsForest [(DD).t])
        (bfsForest [(DD).t]).length ∈ famsAll9 δ b Rt hgen hpG h31 FA :=
      List.mem_append_left _ List.mem_cons_self
    rcases ComplJ8CompPole.compDen_ok δ b (DD).H (DD).pd (bfsForest [(DD).t]) (bfsForest [(DD).t]).length
      (ComplJ9B.pubJ9 δ b (BRunG δ b Rt hgen hpG h31 AV FA) χ) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hcomp, he⟩)))
      j hj S hS with h | h
    exacts [Or.inr h, Or.inl h]



/-! ## 4. The J-9 claim field -/

theorem leavesOf_eq : ∀ n : Noun, leavesOf n = n.leafList
  | .atom _ => rfl
  | .cell x y => by simp [leavesOf, Noun.leafList, leavesOf_eq x, leavesOf_eq y]

/-- **Every big leaf of a demand root has `≤ |acs| + 1` limbs** (its spine rows are distinct members of `acs`). -/
theorem lenL_root (hpG' : p = Nock.Atoms.p) {x : Noun} (hx : x ∈ (DD).roots) (v : ℕ) (hv : v ∈ x.leafList) :
    Nock.Atoms.lenL v ≤ (DD).acs.length + 2 := by
  subst hpG'
  unfold Nock.Atoms.lenL
  split_ifs with h
  · omega
  · have hb : v ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs := by
      refine (ComplJ8Atom.mem_bigsP Nock.Atoms.p _ _ v).mpr ⟨?_, by omega⟩
      exact List.mem_flatMap.mpr ⟨x, List.mem_append_left _ hx, by rw [leavesOf_eq]; exact hv⟩
    have hsp : ∀ y ∈ Nock.V1J8.Gen.spineOf (Nock.Atoms.limbs v), y ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs :=
      fun y hy => (ComplJ8Atom.mem_acsP _ _ y).mpr (Or.inl ((ComplJ8Atom.mem_spineL _ y).mpr ⟨v, hb, hy⟩))
    have h1 := ComplJ8Atom.len_le_of_sub (ComplJ8OfAtom.spineOf_facts (Nock.Atoms.limbs v)).1 hsp
    have h2 := (ComplJ8OfAtom.spineOf_facts (Nock.Atoms.limbs v)).2
    omega

/-- **The J-9 claim field at `BRunG`** (any atom part): `hclI` at cell and big positions, `hclR`, `hcen'` over
`censusGJ9` (limb lengths `≤ nA + 2`), `hcellF`.  Binders: `hp63 h31 hleaf` (every census noun is a demand root). -/
theorem claim_run9 (hp63 : 2 ^ 63 < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (χ : Coins frameJ8 K) :
    (∀ k : Fin 3, (FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true ∨
        ClaimJ9.isBigN p (FrameVS.claimNoun (cJ s f r) k) = true) → (((BRunG δ b Rt hgen hpG h31 AV FA).M χ).m k).1 < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true →
      (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ ClaimJ9.censusGJ9 (BRunG δ b Rt hgen hpG h31 AV FA).Pb (cJ s f r), x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ (BRunG δ b Rt hgen hpG h31 AV FA).Pb.nA + 2) ∧
    FrameVS.isCellN (cJ s f r).formula = true := by
  have hroot : ∀ k : Fin 3, FrameVS.claimNoun (cJ s f r) k ∈ (DD).roots := by
    intro k
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    fin_cases k <;> simp [FrameVS.claimNoun, cJ]
  have hregR : ∀ id ∈ (DD).regs, Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots := fun id hid => by
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hA := size_lt_p Rt hgen hp63 h31 (show (DD).acs.length ∈ sizesJ8 DD by simp [sizesJ8])
  have hCl := size_lt_p Rt hgen hp63 h31 (show (DD).cells.length ∈ sizesJ8 DD by simp [sizesJ8])
  have hne : (DD).cells ≠ [] := List.ne_nil_of_length_pos (cells_pos Rt hgen)
  have hneA : (DD).acs ≠ [] := List.ne_nil_of_length_pos (acs_pos Rt hgen)
  have hcf : FrameVS.isCellN (cJ s f r).formula = true := by
    obtain ⟨a, c, hfc⟩ := formula_cell_of_gen hgen
    simp [cJ, hfc, FrameVS.isCellN]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun x hx => ?_, hcf⟩
  · show ((DD).H (FrameVS.claimNoun (cJ s f r) k)).2 < p
    generalize FrameVS.claimNoun (cJ s f r) k = x at hk
    cases x with
    | atom v =>
      rcases hk with hk | hk
      · simp [FrameVS.isCellN] at hk
      · have hv : p ≤ v := by simpa [ClaimJ9.isBigN] using hk
        show (ComplJ8Data.hdlP p (DD).cells (DD).acs (.atom v)).2 < p
        simp only [ComplJ8Data.hdlP, if_neg (show ¬ v < p by omega)]
        exact lt_trans (ComplJ8Data.rootIdxP_lt p _ hneA v) hA
    | cell a c => exact lt_trans (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hCl
  · have h1 := (Noun.pbt_size (FrameVS.claimNoun (cJ s f r) k)).2
    have h2 := hleaf _ (hroot k)
    have : (FrameVS.claimNoun (cJ s f r) k).internal < 2 ^ 110 := by
      have : (2 : ℕ) ^ 109 < 2 ^ 110 := by norm_num
      omega
    have h3 : (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < 2 ^ 48 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 110 := this
        _ = 2 ^ 48 * 2 ^ 62 := by rw [← pow_add]
    have : (2 : ℕ) ^ 48 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  · have hxr : x ∈ (DD).roots := by
      simp only [ClaimJ9.censusGJ9, AcceptsJ8P.censusG, List.mem_append, List.mem_map] at hx
      rcases hx with (⟨id, hid, rfl⟩ | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
      · exact hregR id hid
      · exact hroot k
      · exact hroot k
    exact ⟨(hleaf _ hxr).trans (by unfold fuelChip; norm_num), fun v hv => lenL_root Rt hgen hpG hxr v hv⟩

/-! ## 5. The families' facts, the open fields, the obligations at `BRunG` -/

theorem famsAll9_facts (o2 : ∀ L ∈ FA, ∀ e ∈ L, e.OK) (p2 : ∀ L ∈ FA, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (c2 : (FA.map ComplJ8Bad.nPins).sum ≤ 2 ^ 65) :
    (∀ L ∈ famsAll9 δ b Rt hgen hpG h31 FA, ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsAll9 δ b Rt hgen hpG h31 FA, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsAll9 δ b Rt hgen hpG h31 FA).map ComplJ8Bad.nPins).sum ≤ 2 ^ 66 := by
  obtain ⟨o1, p1, c1⟩ := famsOf_facts δ b (K := K) (DD) (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) h31
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, o2 L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, p2 L h]
  · rw [famsAll9, List.map_append, List.sum_append]
    have e40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    have e65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
    have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
    rw [e40] at c1; rw [e65] at c2; rw [e66]
    omega

/-- **The J-9 atom families (`famsA9`): side conditions, pins only, pin count `≤ 1 + 9·|acs| + 6·nV`.** -/
theorem famsA9_facts (D DW : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) :
    (∀ L ∈ famsA9 δ b D DW hF hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsA9 δ b D DW hF hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsA9 δ b D DW hF hA (K := K)).map nPins).sum ≤ 1 + 9 * D.acs.length + 6 * nVOf DW := by
  have pZ : AllPin (famAZ (K := K)) := fun e he => by
    simp only [famAZ, List.mem_singleton] at he; subst he; exact ⟨_, _, rfl⟩
  have pV : AllPin (famAV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pH : AllPin (famAH δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMB : AllPin (famMB δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pC : AllPin (famC δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMI : AllPin (famMI δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWV : AllPin (ComplJ9BBalF.famAWV9 δ DW (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWH : AllPin (ComplJ9BBalF.famAWH9 δ DW (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    simp only [famsA9, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact famAZ_OK
    · exact famAV_OK δ D
    · exact famAH_OK δ b D hA _
    · exact famMB_OK δ b D hA _
    · exact famC_OK δ b D hA _
    · exact famMI_OK δ b D hA _
    · exact ComplJ9BBalF.famAWV9_OK δ DW
    · exact ComplJ9BBalF.famAWH9_OK δ DW
  · intro L hL e he i N hN
    simp only [famsA9, List.mem_cons, List.not_mem_nil, or_false] at hL
    have hp : AllPin L := by
      rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [pZ, pV, pH, pMB, pC, pMI, pWV, pWH]
    obtain ⟨j, g, rfl⟩ := hp e he
    cases hN
  · have l1 : (famAV δ D (K := K)).length ≤ D.acs.length * 5 := by
      unfold famAV
      exact (ComplJ8Of.length_flatMap_le _ _ 5 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l2 : (ComplJ9BBalF.famAWV9 δ DW (K := K)).length ≤ nVOf DW * 3 := by
      unfold ComplJ9BBalF.famAWV9
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l3 : (ComplJ9BBalF.famAWH9 δ DW (K := K)).length ≤ nVOf DW * 3 := by
      unfold ComplJ9BBalF.famAWH9
      refine (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => ?_).trans (by rw [List.length_range])
      rw [List.length_map]; unfold ComplJ9BBalF.awHx9; split_ifs
      · exact le_of_eq rfl
      · exact Nat.zero_le _
    simp only [famsA9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := nPins_le_length (famAZ (K := K))
    have := nPins_le_length (famAV δ D (K := K))
    have := nPins_le_length (famAH δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famMB δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famC δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famMI δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (ComplJ9BBalF.famAWV9 δ DW (K := K))
    have := nPins_le_length (ComplJ9BBalF.famAWH9 δ DW (K := K))
    have e1 : (famAZ (K := K)).length = 1 := rfl
    have e2 : (famAH δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famAH, List.length_map, List.length_range]
    have e3 : (famMB δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famMB, List.length_map, List.length_range]
    have e4 : (famC δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famC, List.length_map, List.length_range]
    have e5 : (famMI δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famMI, List.length_map, List.length_range]
    omega


/-- **The J-9 atom families of the run**: `famsA9` at `j9DataOf` satisfies `OpenJ9B`'s family side conditions
(`Σ nPins ≤ 2^65`, from the row binder). -/
theorem famsA9_run :
    (∀ L ∈ famsA9 δ b (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen) (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsA9 δ b (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen) (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsA9 δ b (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen) (K := K)).map nPins).sum ≤ 2 ^ 65 := by
  obtain ⟨o, q, c⟩ := famsA9_facts δ b (K := K) (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen)
  have hacs := h31 _ (show (DD).acs.length ∈ sizesJ8 DD by simp [sizesJ8])
  have hnV := h31 _ (show nVOf (DD) ∈ sizesJ8 DD by simp [sizesJ8])
  have e1 : (D9).acs.length = (DD).acs.length := rfl
  rw [e1] at c
  refine ⟨o, q, le_trans c ?_⟩
  have e : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have e65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
  rw [e] at hacs hnV; rw [e65]; omega

/-- **The J-9 B obligations still carried** (exact copies of the `ComplJ9BObligations` fields): the atom table
at `mb9`, the atom walk at the `rIAP`-rooted spec rows, the three balances. -/
structure OpenJ9B (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  atomOK : ∀ χ, B.Good χ →
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA)
  awOK : ∀ χ, B.Good χ → AcceptsJ8V.AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV
    (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsV (AcceptsJ8.qV δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsV)
  balG : ∀ χ, B.Good χ →
    (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3)) =
      Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1)) ∧
    (B.M χ).ρ 4 = Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
    (B.M χ).ρS + ((Nock.Jet.PinJ8.pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
        (FiniteIO.compress (TeleCQ.coinsCV b δ (chalVJ8 b χ))
          (BalanceQ.liftRec (L := Quad (algebraMap (ZMod p) K δ)) x))⁻¹).sum +
        Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) =
      Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1))
  balV : ∀ χ, B.Good χ →
    ((ClaimJ9.claimRecsJ9 δ χ (cJ s f r) (B.M χ).m ++ AcceptsJ8P.pinRecsJ8 δ B.Pb χ).map fun x =>
        (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    ((B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0)
  balF : ∀ χ, B.Good χ →
    ((B.M χ).pubsC 2 = (B.M χ).pubsW 0 ∧ (B.M χ).pubsC 3 = (B.M χ).pubsW 1) ∧
    ((B.M χ).pubsA 2 = (B.M χ).pubsV 0 ∧ (B.M χ).pubsA 3 = (B.M χ).pubsV 1)



/-! ### The cell table, the J-8 walk and the J chip at `BRunG` (L6's run lemmas, restated at `BRunG`: the traces are
compared by their components, never as whole `TrJ8` records) -/

section Chips
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP

theorem jOK_run9 (hp63 : 2 ^ 63 < p) 
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hJ : famJ δ (j8DataOf p Rg Rt hgen) ∈ (famsAll9 δ b Rt hgen hpG h31 FA)) (χ : Coins frameJ8 K)
    (hχ : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    let B := BRunG δ b Rt hgen hpG h31 AV FA
    JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
      (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ) := by
  intro B
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (j8DataOf p Rg Rt hgen).jrows.length = 0
  · refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
    have hs : ∀ (g : Fin (j8DataOf p Rg Rt hgen).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
      intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
    have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
      (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
    have e : ∀ i, pubsJOf δ (j8DataOf p Rg Rt hgen) χ i = 0 := by
      intro i
      unfold pubsJOf
      rw [hs, hs]
      split_ifs <;> simp [pub2, hz.1, hz.2]
    exact ⟨e 0, e 1, e 2, e 3⟩
  · have hn : 0 < (j8DataOf p Rg Rt hgen).jrows.length := Nat.pos_of_ne_zero h0
    obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (n := (j8DataOf p Rg Rt hgen).jrows.length)
      (le_two_pow_ht _ (by simp [sizesJ8]))
    have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] (famsAll9 δ b Rt hgen hpG h31 FA)),
        χ ∉ e.1 := hχ
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (j8DataOf p Rg Rt hgen).jrows.get)
      (ComplJ8Jet.jKeysX (j8DataOf p Rg Rt hgen).jrows.get) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hJ, he⟩)))
    have := ComplJ8Jet.jOK_present_trJ δ b (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (chalsJJ8 χ) (pubsJOf δ _ χ)
      (j8DataOf p Rg Rt hgen).jrows.get hinj hn hadj
      (fun i => ComplJ8Jet.jrows_gate_run Rt hgen hp hRt _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])
    exact this

theorem cellOK_run9 (hp63 : 2 ^ 63 < p) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hV : famCellV δ (j8DataOf p Rg Rt hgen) ∈ (famsAll9 δ b Rt hgen hpG h31 FA))
    (hH : famCellH δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) ∈ (famsAll9 δ b Rt hgen hpG h31 FA)) (χ : Coins frameJ8 K)
    (hχ : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    let B := BRunG δ b Rt hgen hpG h31 AV FA
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] (famsAll9 δ b Rt hgen hpG h31 FA)),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ (famsAll9 δ b Rt hgen hpG h31 FA), ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  obtain ⟨hz, hrows⟩ := famCellV_good δ (j8DataOf p Rg Rt hgen) χ (hin _ hV)
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (n := (j8DataOf p Rg Rt hgen).cells.length)
    (le_two_pow_ht _ (by simp [sizesJ8]))
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b (cells_pos Rt hgen) (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (chalsMJ8 δ χ)
    (pubsCOf δ b _ (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b (cells_pos Rt hgen) _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hin _ hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 4) (pub2 δ (chT δ b _ (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ (pubsC0 δ _ χ) (pubsCOf δ b _ (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)]

theorem walkOK_run9 (hp63 : 2 ^ 63 < p) 
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hV : famWalkV δ (j8DataOf p Rg Rt hgen) ∈ (famsAll9 δ b Rt hgen hpG h31 FA)) (hH : famWalkH δ (j8DataOf p Rg Rt hgen) ∈ (famsAll9 δ b Rt hgen hpG h31 FA))
    (χ : Coins frameJ8 K) (hχ : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) :
    let B := BRunG δ b Rt hgen hpG h31 AV FA
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] (famsAll9 δ b Rt hgen hpG h31 FA)),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ (famsAll9 δ b Rt hgen hpG h31 FA), ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hmW : (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length ∈
      sizesJ8 (j8DataOf p Rg Rt hgen) := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ (dvdOK_of_rows hpG _ h31)) (le_two_pow_ht _ hmW)
  have hrows := famWalkV_good δ (j8DataOf p Rg Rt hgen) χ (hin _ hV)
  have hcl : (j8DataOf p Rg Rt hgen).cells.length < ringChar (ZMod p) := by
    rw [hrc]; exact size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hkp : krW (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads +
      (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length < ringChar (ZMod p) := by
    have := h31 _ hmW
    have := krW_le_rows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hpoleH : ∀ (i : Fin (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length),
      ∀ x ∈ walkHx δ (j8DataOf p Rg Rt hgen) i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hin _ hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) hinj χ
    (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN (orbJ8 _ (dvdOK_of_rows hpG _ h31)) _) (orbJ8 _ (dvdOK_of_rows hpG _ h31))
    (chalsMJ8 δ χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
    (GeneratedField.primeFieldElems_zmod p) (by rw [hrc]; exact hp63) hcl hwalk hkp rfl hinj hadj
    (ProbJ8.chalsOK_J8 δ χ) (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.1)
    (fun j hj => (hrows j hj).2.2) (pub2_mk2 δ (wxT δ (j8DataOf p Rg Rt hgen) χ) 0 rfl).symm (pub2_mk2 δ (wpT δ (j8DataOf p Rg Rt hgen) χ) 2 rfl).symm
    (fun i => hdl_kind _ _ _) (fun i => hdl_kind _ _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).idx, (kLW _ i, vLW _ i),
        (kRW _ i, vRW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre,
        (kLW _ i, vLW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre + 1,
        (kRW _ i, vRW _ i))) (by
          simp only [walkHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ?_ ?_
  · exact hwalk'
  · show Quad.mk _ (pub2 δ (whX δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 4) (pub2 δ (whX δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 6) (pub2 δ (whP δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) hinj χ (pubsW0 δ (j8DataOf p Rg Rt hgen) χ) (pubsWOf δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ) _ (Or.inr (Or.inr rfl))]

end Chips

/-- `BRunG`-good coins are `BOf`-good at `famsAll9 FA` (the same bad list). -/
theorem goodB0 (χ : Coins frameJ8 K) (h : (BRunG δ b Rt hgen hpG h31 AV FA).Good χ) : (BOf δ b Rt hgen (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)).Good χ := fun e he => h e he

/-- **The obligations at `BRunG`** (any atom part `AV`, whose traces are staged), from the run binders and the
open fields `OpenJ9B`. -/
theorem obligations_of_run9 (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hAst : StagedCols frameJ8 TraceJ8.crA (fun χ => AV.trA χ))
    (hVst : StagedCols frameJ8 TraceJ8.crW (fun χ => AV.trV χ))
    (hFA : (∀ L ∈ FA, ∀ e ∈ L, e.OK) ∧ (∀ L ∈ FA, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
      (FA.map ComplJ8Bad.nPins).sum ≤ 2 ^ 65)
    (O : OpenJ9B δ b (BRunG δ b Rt hgen hpG h31 AV FA)) :
    ComplJ9B.ComplJ9BObligations δ b (BRunG δ b Rt hgen hpG h31 AV FA) := by
  have hF := dvdOK_of_rows hpG _ h31
  obtain ⟨hOK, hpin, hcnt⟩ := famsAll9_facts δ b Rt hgen hpG h31 FA hFA.1 hFA.2.1 hFA.2.2
  have mem : ∀ {L}, L ∈ famsOf δ b (DD) hF (cells_pos Rt hgen) → L ∈ famsAll9 δ b Rt hgen hpG h31 FA :=
    fun h => List.mem_append_left _ h
  have m1 := mem (L := famCellV δ (DD)) (List.mem_cons_of_mem _ List.mem_cons_self)
  have m2 := mem (L := famCellH δ b (DD) (cells_pos Rt hgen) (orbJ8 _ hF))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have m3 := mem (L := famWalkV δ (DD))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have m4 := mem (L := famWalkH δ (DD))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))
  have m5 := mem (L := famJ δ (DD))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) →
      encR δ χ = encR δ χ' := fun χ χ' h =>
    encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide)) (h FrameJ8.cY1 (by decide))
      (h FrameJ8.cY2 (by decide))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := compute_group9 δ b Rt hgen hpG h31 AV FA hp63 hax hop5
  obtain ⟨n1, n2⟩ := nodes_ok δ b Rt hgen hF (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA)
  obtain ⟨g1, g2, g3⟩ := nodes_group δ b Rt hgen hF (cells_pos Rt hgen) (acs_pos Rt hgen) AV
    (famsAll9 δ b Rt hgen hpG h31 FA) hp63 h31
  obtain ⟨w1, w2⟩ := bad_group δ b Rt hgen hF (cells_pos Rt hgen) (acs_pos Rt hgen) AV
    (famsAll9 δ b Rt hgen hpG h31 FA) hOK hpin (fun _ => hcnt)
  exact
    { hH := c1, hpair := c2, hN := c3, hinjX := n1, hadjX := n2,
      htrC := fun χ => by
        show trC9w δ b _ _ _ _ χ _ = _
        rw [trC9w_def]
        rfl,
      hpIC := c4, hpS := c5, hpO := c6, hpub := c7, hρ := c8, goodC := c9,
      cellOK := fun χ hχ => cellOK_run9 δ b Rt hgen hpG h31 AV FA hp63 hleaf m1 m2 χ hχ,
      cellNodes := g1,
      walkOK := fun χ hχ => walkOK_run9 δ b Rt hgen hpG h31 AV FA hp63 hwalk m3 m4 χ hχ,
      walkNodes := g2,
      jOK := fun χ hχ => jOK_run9 δ b Rt hgen hpG h31 AV FA hp63 hRt m5 χ hχ,
      atomOK := O.atomOK, atomNodes := g3, awOK := O.awOK, balG := O.balG, balV := O.balV, balF := O.balF,
      stat := stat_run δ b Rt hgen hF (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA) hp63 hax h31 hleaf hRt,
      claim := fun χ => claim_run9 δ b Rt hgen hpG h31 AV FA hp63 hleaf χ,
      budget := budget_run δ b Rt hgen hF (cells_pos Rt hgen) (acs_pos Rt hgen) AV (famsAll9 δ b Rt hgen hpG h31 FA) hp63 h31,
      wt := w1,
      staged := ⟨by
          show StagedCols frameJ8 TraceJ8.crC (fun χ => trC9w δ b _ _ _ _ χ _)
          simp only [trC9w_def]
          exact ComplJ9BComp.staged_trCOf9 δ b _ _ _,
        ComplJ8Enc.cellTrME_staged δ b (cells_pos Rt hgen) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
        ComplJ8Enc.walkTrWE_staged δ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
        ComplJ8Jet.stJ δ b _ _ _ (fun χ => rfl), hAst, hVst⟩,
      fig := w2 }

open Classical in
/-- **J-9 B completeness at `BRunG`, the open fields carried**: for every
generated run under `complJ8_closed`'s binders minus `hclA` (`hwalkA` enters with `awOK`), at an atom part `AV`
whose traces are staged: honest acceptance by `AcceptsJ9V` at every good coin, `Pr[¬Good] ≤ ε_c`, staging, the
claim holds, and at `|K| = cK` the figure `ε_c < 2^-120` with an accepting coin. -/
theorem complJ9B_open (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hAst : StagedCols frameJ8 TraceJ8.crA (fun χ => AV.trA χ))
    (hVst : StagedCols frameJ8 TraceJ8.crW (fun χ => AV.trV χ))
    (hFA : (∀ L ∈ FA, ∀ e ∈ L, e.OK) ∧ (∀ L ∈ FA, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
      (FA.map ComplJ8Bad.nPins).sum ≤ 2 ^ 65)
    (O : OpenJ9B δ b (BRunG δ b Rt hgen hpG h31 AV FA)) :
    (∀ χ, (BRunG δ b Rt hgen hpG h31 AV FA).Good χ →
      AcceptsJ9V.AcceptsJ9V δ b (BRunG δ b Rt hgen hpG h31 AV FA).Pb Rg.R (cJ s f r) χ ((BRunG δ b Rt hgen hpG h31 AV FA).M χ) ((BRunG δ b Rt hgen hpG h31 AV FA).tr χ) (BRunG δ b Rt hgen hpG h31 AV FA).rows (BRunG δ b Rt hgen hpG h31 AV FA).g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BRunG δ b Rt hgen hpG h31 AV FA).Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ (BRunG δ b Rt hgen hpG h31 AV FA).epsC) ∧
    StJ8 (BRunG δ b Rt hgen hpG h31 AV FA).tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      (BRunG δ b Rt hgen hpG h31 AV FA).epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V δ b (BRunG δ b Rt hgen hpG h31 AV FA).Pb Rg.R (cJ s f r) χ ((BRunG δ b Rt hgen hpG h31 AV FA).M χ) ((BRunG δ b Rt hgen hpG h31 AV FA).tr χ) (BRunG δ b Rt hgen hpG h31 AV FA).rows (BRunG δ b Rt hgen hpG h31 AV FA).g) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have O' := obligations_of_run9 δ b Rt hgen hpG h31 AV FA hp63 hax hop5 hleaf hwalk hRt hAst hVst hFA O
  obtain ⟨h1, h2, h3, h4, h5⟩ := ComplJ9B.complJ9B_of_obligations δ b (BRunG δ b Rt hgen hpG h31 AV FA) O' hp63 hax hop5
  exact ⟨h1, h2, h3, h4, fun hcK => h5 hpG hcK (rowsLe31_of δ b Rt hgen _ _ _ AV (famsAll9 δ b Rt hgen hpG h31 FA) h31)⟩

/-! ## 6. At `BRun9`: the atom walk and `balF` (`balF1_run`, GLB's `balF2_run9`) -/

/-- **`awOK` at `BRun9`** (binders `hp63 hwalkA`; the atom walk at `j8DataOf`). -/
theorem awOK_run9 (hp63 : 2 ^ 63 < p) (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) :
    ∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
      AcceptsJ8V.AWChipOK δ b (BRun9 δ b Rt hgen hpG h31).Pb.krootsV (BRun9 δ b Rt hgen hpG h31).Pb.hnV (BRun9 δ b Rt hgen hpG h31).Pb.nodesV (BRun9 δ b Rt hgen hpG h31).Pb.orbitV (ChalsAZJ8.chalsAJ8Z δ χ)
        ((BRun9 δ b Rt hgen hpG h31).M χ).pubsV
        (AcceptsJ8.qV δ b (BRun9 δ b Rt hgen hpG h31).Pb ((BRun9 δ b Rt hgen hpG h31).tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsV) := by
  intro χ hχ
  have hin := good9_FA δ b Rt hgen hpG h31 _ _ χ hχ
  have mV : ComplJ9BBalF.famAWV9 δ (DD) ∈
      famsA9 δ b (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen) (K := K) := by
    simp only [famsA9, List.mem_cons]; simp
  have mH : ComplJ9BBalF.famAWH9 δ (DD) ∈
      famsA9 δ b (D9) (DD) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen) (K := K) := by
    simp only [famsA9, List.mem_cons]; simp
  exact ComplJ9BBalF.awOK_D9 δ b (DD) (dvdOK_of_rows hpG _ h31) hp63 h31 hwalkA (acs_pos Rt hgen) χ (hin _ mV) (hin _ mH)

/-- **`balF` at `BRun9`** (every coin; binders `hwalk hwalkA`). -/
theorem balF_run9 (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads) (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) :
    ∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
      (((BRun9 δ b Rt hgen hpG h31).M χ).pubsC 2 = ((BRun9 δ b Rt hgen hpG h31).M χ).pubsW 0 ∧ ((BRun9 δ b Rt hgen hpG h31).M χ).pubsC 3 = ((BRun9 δ b Rt hgen hpG h31).M χ).pubsW 1) ∧
      (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA 2 = ((BRun9 δ b Rt hgen hpG h31).M χ).pubsV 0 ∧ ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA 3 = ((BRun9 δ b Rt hgen hpG h31).M χ).pubsV 1) := by
  intro χ _
  refine ⟨ComplJ8OfBal.balF1_run δ b Rt hgen hpG h31 hwalk χ, ?_⟩
  obtain ⟨a2, a3⟩ := ComplJ9BBalF.pubsAOf_23 δ b (D9) (acs9_pos Rt hgen) (orbJ8 _ (dvd9 Rt hgen hpG h31)) χ
  obtain ⟨b2, b3⟩ := ComplJ9BBalF.pubsAOf_23 δ b (DD) (acs_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ
  have ex := ComplJ9BBalF.axT_congr δ (DD) (D9) rfl rfl rfl χ
  obtain ⟨f2, f3⟩ := ComplJ9BBalF.balF2_run9 δ b Rt hgen hpG hwalkA (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ
  show pubsAOf δ b (D9) (acs9_pos Rt hgen) (orbJ8 _ (dvd9 Rt hgen hpG h31)) χ 2 =
      ComplJ9BBalF.pubsVOf9 δ b (DD) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 0 ∧
    pubsAOf δ b (D9) (acs9_pos Rt hgen) (orbJ8 _ (dvd9 Rt hgen hpG h31)) χ 3 =
      ComplJ9BBalF.pubsVOf9 δ b (DD) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ 1
  rw [a2, a3, ex, ← b2, ← b3]
  exact ⟨f2, f3⟩

/-- **`atomOK` at `BRun9`**. -/
theorem atomOK_B9 (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t) :
    ∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
    (AtomChipHQ.atomChipHQ δ b (BRun9 δ b Rt hgen hpG h31).Pb.hnA (BRun9 δ b Rt hgen hpG h31).Pb.nodesA (BRun9 δ b Rt hgen hpG h31).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b (BRun9 δ b Rt hgen hpG h31).Pb ((BRun9 δ b Rt hgen hpG h31).tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b (BRun9 δ b Rt hgen hpG h31).Pb.hnA (BRun9 δ b Rt hgen hpG h31).Pb.nodesA (BRun9 δ b Rt hgen hpG h31).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b (BRun9 δ b Rt hgen hpG h31).Pb ((BRun9 δ b Rt hgen hpG h31).tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b (BRun9 δ b Rt hgen hpG h31).Pb.hnA (BRun9 δ b Rt hgen hpG h31).Pb.nodesA (BRun9 δ b Rt hgen hpG h31).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b (BRun9 δ b Rt hgen hpG h31).Pb ((BRun9 δ b Rt hgen hpG h31).tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b (BRun9 δ b Rt hgen hpG h31).Pb.hnA (BRun9 δ b Rt hgen hpG h31).Pb.nodesA (BRun9 δ b Rt hgen hpG h31).Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b (BRun9 δ b Rt hgen hpG h31).Pb ((BRun9 δ b Rt hgen hpG h31).tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) ((BRun9 δ b Rt hgen hpG h31).M χ).pubsA) := by
  intro χ hχ
  have hin := good9_FA δ b Rt hgen hpG h31 _ _ χ hχ
  exact ComplJ9BAtom.atomOK_run9 δ b Rt hgen hpG [s, f, r] (fun n hn => hn) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen)
    hax hop5 h31 χ (hin _ (by simp [famsA9])) (hin _ (by simp [famsA9])) (hin _ (by simp [famsA9]))
    (hin _ (by simp [famsA9])) (hin _ (by simp [famsA9])) (hin _ (by simp [famsA9]))


structure Open3 (B : HonestJ8 p K δ Rg fuel s f r) : Prop where
  atomOK : ∀ χ, B.Good χ →
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQL.atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsA)
  balG : ∀ χ, B.Good χ →
    (B.M χ).ρ 3 + (Quad.mk _ ((B.M χ).pubsW WalkHQ.pubXQ) ((B.M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ ((B.M χ).pubsJ 2) ((B.M χ).pubsJ 3)) =
      Quad.mk _ ((B.M χ).pubsC CellHQ.pubHQ) ((B.M χ).pubsC (CellHQ.pubHQ + 1)) ∧
    (B.M χ).ρ 4 = Quad.mk _ ((B.M χ).pubsW WalkHQ.pubPQ) ((B.M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
    (B.M χ).ρS + ((Nock.Jet.PinJ8.pinCons (p := p) (K := K) B.Pb.regs B.Pb.idx).map fun x =>
        (FiniteIO.compress (TeleCQ.coinsCV b δ (chalVJ8 b χ))
          (BalanceQ.liftRec (L := Quad (algebraMap (ZMod p) K δ)) x))⁻¹).sum +
        Quad.mk _ ((B.M χ).pubsJ 0) ((B.M χ).pubsJ 1) =
      Quad.mk _ ((B.M χ).pubsA AtomChipHQ.pubMI) ((B.M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ ((B.M χ).pubsV WalkHQ.pubPQ) ((B.M χ).pubsV (WalkHQ.pubPQ + 1))
  balV : ∀ χ, B.Good χ →
    ((ClaimJ9.claimRecsJ9 δ χ (cJ s f r) (B.M χ).m ++ AcceptsJ8P.pinRecsJ8 δ B.Pb χ).map fun x =>
        (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsC 0) ((B.M χ).pubsC 1) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubMB) ((B.M χ).pubsA (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA CellHQ.pubHQ) ((B.M χ).pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsA AtomChipHQ.pubC) ((B.M χ).pubsA (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) ((B.M χ).pubsV WalkHQ.pubXQ) ((B.M χ).pubsV (WalkHQ.pubXQ + 1)) ∧
    ((B.M χ).pubsA 0 = 0 ∧ (B.M χ).pubsA 1 = 0)

open Classical in

theorem complJ9B_run9 (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (O : Open3 δ b (BRun9 δ b Rt hgen hpG h31)) :
    (∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
      AcceptsJ9V.AcceptsJ9V δ b (BRun9 δ b Rt hgen hpG h31).Pb Rg.R (cJ s f r) χ ((BRun9 δ b Rt hgen hpG h31).M χ) ((BRun9 δ b Rt hgen hpG h31).tr χ) (BRun9 δ b Rt hgen hpG h31).rows (BRun9 δ b Rt hgen hpG h31).g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BRun9 δ b Rt hgen hpG h31).Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ (BRun9 δ b Rt hgen hpG h31).epsC) ∧
    StJ8 (BRun9 δ b Rt hgen hpG h31).tr ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      (BRun9 δ b Rt hgen hpG h31).epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V δ b (BRun9 δ b Rt hgen hpG h31).Pb Rg.R (cJ s f r) χ ((BRun9 δ b Rt hgen hpG h31).M χ) ((BRun9 δ b Rt hgen hpG h31).tr χ) (BRun9 δ b Rt hgen hpG h31).rows (BRun9 δ b Rt hgen hpG h31).g) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  exact complJ9B_open δ b Rt hgen hpG h31 _ _ hax hop5 hleaf hwalk hRt
    (stA_run δ b (D9) (dvd9 Rt hgen hpG h31) (acs9_pos Rt hgen))
    (ComplJ9BBalF.stV_run9' δ b (DD) (dvdOK_of_rows hpG _ h31) _)
    (famsA9_run δ b Rt hgen hpG h31)
    { atomOK := O.atomOK, awOK := awOK_run9 δ b Rt hgen hpG h31 hp63 hwalkA, balG := O.balG, balV := O.balV,
      balF := balF_run9 δ b Rt hgen hpG h31 hwalk hwalkA }

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf
