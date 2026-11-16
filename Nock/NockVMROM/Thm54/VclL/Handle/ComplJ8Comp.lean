/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Comp.lean

  **The compute chip's data, claim and binder lemmas.**
  New module, additive.  Generic over the honest data `H`, `pd`, the generated tree `t` (`W = bfsForest [t]`) and
  the claim `c = cJ s f r`; L0's `J8Data` will instantiate them.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Stage
import Nock.V1J8.GenAtom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.SVFrame

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (c : P8PublicClaim)

/-- The honest claim message: serial `(H x).2`, rank limbs `rkC x`. -/
def mCOf : ClaimMsgVS := fun k => ((H (claimNoun c k)).2, rkC (claimNoun c k))

/-- The accumulator totals (read at a dummy public vector; they do not read the publics). -/
def accT (χ : Coins frameJ8 K) (a : ℕ) : K :=
  accV b δ H pd W (chalVJ8 b χ) (pubVJ8 δ b c (mCOf H c) 0 0 χ) a W.length

def ρCOf (χ : Coins frameJ8 K) : Fin 5 → 𝕂′ := fun i =>
  if (i : ℕ) = 3 then Quad.mk _ (accT δ b H pd W c χ 0) (accT δ b H pd W c χ 1)
  else if (i : ℕ) = 4 then Quad.mk _ (accT δ b H pd W c χ 2) (accT δ b H pd W c χ 3) else 0

def ρSCOf (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (accT δ b H pd W c χ 4) (accT δ b H pd W c χ 5)

/-- The compute publics of the honest message. -/
def pubCOf (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  pubVJ8 δ b c (mCOf H c) (ρCOf δ b H pd W c χ) (ρSCOf δ b H pd W c χ) χ

/-- The honest compute trace `polyX` at the walk coins of `χ` (width `123`). -/
def trCOf (χ : Coins frameJ8 K) {n : ℕ} (nodes : Fin n → ZMod p) : Fin 123 → (ZMod p)[X] :=
  polyX b δ H pd W (chalVJ8 b χ) (pubCOf δ b H pd W c χ) (lnW (InhabJ8Comp.αC0 b χ)) (cntW W (InhabJ8Comp.αC0 b χ))
    (accW (F := ZMod p) H W (InhabJ8Comp.αC0 b χ) (InhabJ8Comp.γC0 b χ)) nodes 123

theorem pub_lo (χ : Coins frameJ8 K) (j : ℕ) (hj : j < 6) :
    pubCOf δ b H pd W c χ j = (labelF (F := ZMod p) c (mCOf H c)).getD j 0 := by
  simp [pubCOf, pubVJ8, pubVHQ, pubVH, show j < 27 by omega, show j < 21 by omega, hj]

theorem hpIC (χ : Coins frameJ8 K) :
    limbVal b (pubCOf δ b H pd W c χ) pubIC = InhabJ8Comp.αC0 b χ := by
  rw [InhabJ8Comp.αC0_eq]
  refine InhabJ8Comp.limbVal_coord b _ _ _ fun k => ?_
  fin_cases k <;> simp [pubCOf, pubVJ8, pubVHQ, pubVH, toVS, toVSQ, pubIC, cAlphaW]

theorem hpO (χ : Coins frameJ8 K) : limbVal b (pubCOf δ b H pd W c χ) pubOut = 0 := by
  unfold limbVal
  refine Finset.sum_eq_zero fun k _ => ?_
  fin_cases k <;> simp [pubCOf, pubVJ8, pubVHQ, pubVH, pubOut]

theorem hρ (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubCOf δ b H pd W c χ (pubOfA a + k) =
      coord b (accV b δ H pd W (chalVJ8 b χ) (pubCOf δ b H pd W c χ) a W.length) k := by
  intro a ha k
  rw [InhabJ8Comp.accV_pub δ b H pd W (chalVJ8 b χ) (pubCOf δ b H pd W c χ) (pubVJ8 δ b c (mCOf H c) 0 0 χ)]
  change _ = coord b (accT δ b H pd W c χ a) k
  interval_cases a <;> fin_cases k <;>
    simp [pubOfA, pubCOf, pubVJ8, pubVHQ, pubVH, ρCOf, ρSCOf, pubRhoX, pubRhoXIm, pubRhoP, pubRhoPIm,
      pubRhoSX, pubRhoSXi, Quad.re_mk, Quad.im_mk]

variable {H} {c}

/-- Handle-correctness of the claim: its atoms are small. -/
theorem hvalF_claim (hH : HdlOK p H) (hcl : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p) (k : Fin 3) :
    hvalF (F := ZMod p) (claimH c (mCOf H c) k) = [hk H (claimNoun c k), hv H (claimNoun c k)] := by
  unfold claimH mCOf
  have h := hcl k
  cases hn : claimNoun c k with
  | atom v =>
    have hv' := h v hn
    have := hH.small v hv'
    simp [claimHandle, hvalF, hk, hv, this]
  | cell a d =>
    simp [claimHandle, hvalF, hk, hv, hH.cell]

theorem labelF_eq (hH : HdlOK p H) (hcl : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p) :
    labelF (F := ZMod p) c (mCOf H c) = hlX (F := ZMod p) H (c.subject, c.formula, c.result) := by
  unfold labelF hlX
  rw [hvalF_claim hH hcl 0, hvalF_claim hH hcl 1, hvalF_claim hH hcl 2]
  simp [claimNoun]

theorem hpub (hH : HdlOK p H) (hcl : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p) (χ : Coins frameJ8 K) :
    pubCOf δ b H pd W c χ 0 = hk H c.subject ∧ pubCOf δ b H pd W c χ 1 = hv H c.subject ∧
    pubCOf δ b H pd W c χ 2 = hk H c.formula ∧ pubCOf δ b H pd W c χ 3 = hv H c.formula ∧
    pubCOf δ b H pd W c χ 4 = hk H c.result ∧ pubCOf δ b H pd W c χ 5 = hv H c.result := by
  have h := labelF_eq hH hcl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [pub_lo δ b H pd W c χ _ (by norm_num), h] <;> simp [hlX]

/-- The walk seed. -/
theorem hpS (hH : HdlOK p H) (hcl : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p)
    {t : NTree SkelX} (hW : W = bfsForest [t]) (hroot : tripOf t = (c.subject, c.formula, c.result))
    (χ : Coins frameJ8 K) :
    limbVal b (pubCOf δ b H pd W c χ) pubSeed =
      curW (F := ZMod p) H W (InhabJ8Comp.γC0 b χ) 1 * InhabJ8Comp.αC0 b χ := by
  have hcur : curW (F := ZMod p) H W (InhabJ8Comp.γC0 b χ) 1 =
      Nock.NockVMROM.Thm54.VclL.Handle.rlcL (InhabJ8Comp.γC0 b χ) 0
        ((hlX (F := ZMod p) H (c.subject, c.formula, c.result)).map (algebraMap (ZMod p) K)) := by
    have hne : [t] ≠ [] := List.cons_ne_nil _ _
    have h0 : W[0]? = some t := by
      rw [hW, bfsForest_cons_eq _ hne]; simp
    simp only [curW, Walk.curCol, h0, Nat.sub_self, Option.map_some, Option.getD_some, nodeValX, lblX, hroot]
  rw [hcur, InhabJ8Comp.αC0_eq, InhabJ8Comp.γC0_eq]
  rw [InhabJ8Comp.limbVal_coord b (seedVS (F := ZMod p) c (mCOf H c) (toVS (toVSQ χ))) _ _ fun k => by
    fin_cases k <;> simp [pubCOf, pubVJ8, pubVHQ, pubVH, pubSeed]]
  unfold seedVS
  rw [labelF_eq hH hcl]
  simp [hlX, Nock.NockVMROM.Thm54.VclL.Handle.rlcL, toVS, toVSQ, cAlphaW, cGamW, List.zipIdx]
  ring

/-- **The compute trace is staged** (`staged.1`). -/
theorem staged_trCOf {n : ℕ} (nodes : Fin n → ZMod p) :
    StagedCols frameJ8 crC (fun χ => trCOf δ b H pd W c χ nodes) := by
  intro j χ χ' h
  unfold trCOf polyX
  refine congrArg (fun f => Lagrange.interpolate Finset.univ nodes f) (funext fun i => ?_)
  by_cases hj : (j : ℕ) < 69
  · rw [trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj, trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj]
  · have h0 := InhabJ8Stage.zero_of_one χ χ' (crC j) (by simp [crC, hj]) h
    have hcv := InhabJ8Stage.chalVJ8_agree b χ χ' h0
    have hα : InhabJ8Comp.αC0 b χ = InhabJ8Comp.αC0 b χ' := by
      rw [InhabJ8Comp.αC0_eq, InhabJ8Comp.αC0_eq, h0 _ rfl]
    have hγ : InhabJ8Comp.γC0 b χ = InhabJ8Comp.γC0 b χ' := by
      rw [InhabJ8Comp.γC0_eq, InhabJ8Comp.γC0_eq, h0 _ rfl]
    rw [InhabJ8Stage.trX_pub δ b _ _ _ _ (pubCOf δ b H pd W c χ) (pubCOf δ b H pd W c χ'), hcv, hα, hγ]

end Gen

section Nodes
variable {p : ℕ} [Fact p.Prime] {h n : ℕ}

/-- The compute nodes `ω^i` are injective when `n ≤ 2^h` (`vsV_injC`). -/
theorem hinjX_of (orbit : StrictOrbitDomain (ZMod p) 3 h) (nodes : Fin n → ZMod p)
    (hn : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) (hle : n ≤ 2 ^ h) : Function.Injective nodes := by
  intro a b hab
  rw [hn, hn] at hab
  apply Fin.ext
  refine pow_injOn_Iio_orderOf ?_ ?_ hab
  · show (a : ℕ) < orderOf _
    rw [orbit.order_ω]; have := a.isLt; omega
  · show (b : ℕ) < orderOf _
    rw [orbit.order_ω]; have := b.isLt; omega

/-- The compute nodes are `ω`-adjacent (`AcceptsJ8V.hadjX`). -/
theorem hadjX_of (orbit : StrictOrbitDomain (ZMod p) 3 h) (nodes : Fin n → ZMod p)
    (hn : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) :
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω := by
  intro i hi
  rw [hn, hn]; exact pow_succ _ _

end Nodes
section Hdl
open Nock.V1J8.Gen in
/-- **`hH`**: the generator's handle map `hdlB` is honest at `p = P` (small `(0, v)`, big kind `2`, cell kind `1`). -/
theorem hdlB_ok {p : ℕ} (hP : p = Nock.V1J8.Gen.P) (cs acsL : List Noun) : HdlOK p (hdlB cs acsL) where
  small v hv := by subst hP; simp [hdlB, hv]
  big v hv := by subst hP; simp [hdlB, Nat.not_lt.mpr hv]
  cell a d := by simp [hdlB]

open Nock.V1J8.Gen in
/-- A cell's serial under `hdlB` is `< p` when the cell list is shorter than `p` (the claim's `hclI`). -/
theorem hdlB_cell_lt {p : ℕ} (cs acsL : List Noun) (hlen : cs.length < p) (x : Noun) (hx : isCellN x = true) :
    (hdlB cs acsL x).2 < p := by
  cases x with
  | atom v => simp [isCellN] at hx
  | cell a d =>
    simp only [hdlB]
    have hle : ∀ (l : List Noun) (n : Noun), idxD l n ≤ l.length := by
      intro l n; induction l with
      | nil => simp [idxD]
      | cons c l ih => simp only [idxD]; split_ifs <;> simp <;> omega
    refine lt_of_le_of_lt ?_ hlen
    unfold idxOf; split_ifs
    · exact hle _ _
    · exact Nat.zero_le _
end Hdl

section Claim
variable {p : ℕ}

/-- **The claim conjuncts** (`ComplJ8Obligations.claim`) from the binders: `hleafA` the leaves of `s f r` are
`< p`, `hleafN` the claim nouns have `≤ 2^110` leaves, `hser` the serials of claim cells are `< p`, `hreg` the
registered formulas satisfy the census bound (taken from the registry lane). -/
theorem claim_J8_instance [Fact p.Prime] (hp63 : 2 ^ 63 < p) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hleafA : ∀ k : Fin 3, ∀ v ∈ (claimNoun c k).leafList, v < p)
    (hleafN : ∀ k : Fin 3, (claimNoun c k).leaves ≤ 2 ^ 110)
    (hser : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (m k).1 < p)
    (Pb : AcceptsJ8.PubJ8 p)
    (hreg : ∀ id ∈ Pb.regs, (Nock.Jet.Autogen.compile p (Pb.Rt id)).leaves ≤ fuelChip ∧
      ∀ v ∈ (Nock.Jet.Autogen.compile p (Pb.Rt id)).leafList, v < p)
    (hcf : isCellN c.formula = true) :
    (∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true → (m k).1 < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ AcceptsJ8P.censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    isCellN c.formula = true := by
  refine ⟨?_, hser, ?_, ?_, hcf⟩
  · intro k v hv
    exact hleafA k v (by simp [hv, Noun.leafList])
  · intro k _
    have h1 := (pbt_size (claimNoun c k)).2
    have h2 := hleafN k
    have : (claimNoun c k).internal < 2 ^ 110 := by omega
    have h3 : (claimNoun c k).internal / 2 ^ 62 < 2 ^ 48 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 110 := this
        _ = 2 ^ 48 * 2 ^ 62 := by rw [← pow_add]
    have : (2 : ℕ) ^ 48 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  · intro x hx
    simp only [AcceptsJ8P.censusG, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨id, hid, rfl⟩ | ⟨k, hk, rfl⟩
    · exact hreg id hid
    · exact ⟨le_trans (hleafN k) (by unfold fuelChip; exact le_rfl), hleafA k⟩
end Claim

section Budget
variable {p : ℕ} [Fact p.Prime]
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (BudJ8 jCount)
open Nock.Jet.ChipJ8 (entsX)
open Nock.Jet.ChipJ8 (ents0T ents1T ents2T ents3)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (RowsJ8)

/-- **The canonical row parameters** covering the public counts exactly (`extra` carries the free fields:
leaf bound, inc rows, claim leaves, longest limb list). -/
def canonRows (Pb : AcceptsJ8.PubJ8 p) (extra : RowsJ8) : RowsJ8 :=
  { extra with
    N := Pb.n, D := Pb.nC, W := Pb.nW, A := Pb.nA, AW := Pb.nV, J := Pb.nJ, mb := Pb.nA,
    rd := jCount entsX Pb.lay,
    calls := jCount ents2T Pb.lay + jCount ents3 Pb.lay, heads := Pb.nA, blocks := 2 * Pb.nV }

/-- The canonical budget `g`. -/
def canonG (Pb : AcceptsJ8.PubJ8 p) : ℕ := Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay)

/-- **Budget conjuncts** at the canonical rows (J-8 instance): `BudJ8` and the four row inequalities. -/
theorem budget_canon (Pb : AcceptsJ8.PubJ8 p) (extra : RowsJ8) :
    BudJ8 Pb (canonRows Pb extra) (canonG Pb + (canonRows Pb extra).N) ∧
    (Pb.regs.length ≤ canonG Pb + (canonRows Pb extra).N) ∧ Pb.nA ≤ (canonRows Pb extra).mb ∧
    Pb.nA ≤ (canonRows Pb extra).A ∧ Pb.nV ≤ (canonRows Pb extra).AW := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, le_rfl, le_rfl, le_rfl⟩ <;>
    simp only [canonRows, canonG] <;> omega

/-- **Length budgets** (J-8 instance): from `RowsLe31`, `2^63 < p`, and a registry of `≤ 2^31` ids. -/
theorem budget_lengths (hp63 : 2 ^ 63 < p) (Pb : AcceptsJ8.PubJ8 p) (hrows : ComplJ8.RowsLe31 Pb)
    (hreg : Pb.regs.length ≤ 2 ^ 31) :
    3 + Pb.regs.length + 2 * Pb.nC < p ∧ Pb.nA + Pb.nV < p ∧ Pb.nA ≤ 2 ^ 62 := by
  obtain ⟨_, h2, _, _, h5, h6⟩ := hrows
  have : (2 : ℕ) ^ 31 * 4 ≤ 2 ^ 62 := by norm_num
  have : (2 : ℕ) ^ 62 + 2 ^ 31 < 2 ^ 63 := by norm_num
  refine ⟨?_, ?_, ?_⟩ <;> omega
end Budget

section Chip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

open Classical in
/-- **The compute chip, honest at the generated tree** (one chip template): the honest data of `genX` (`H`, `pd`,
`t`) at the claim `cJ s f r`, the trace `trCOf`, satisfies `computeChipVCLHX` at every coin whose walk coin has
order `≥ |W|` and whose slots have no pole (`hord`, `hnb`: the good-coin events, supplied by the bad-event lane).
The claim side enters only through `hcl` (claim atoms `< p`; the J-8 instance, J-9 B replaces it). -/
theorem computeChip_sat {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (hH : HdlOK (ringChar (ZMod p)) H) (hp : 16 ≤ ringChar (ZMod p))
    (hsm : ∀ u, InTree t u → HonestRowX.SmallX (ringChar (ZMod p)) (rowOfSkelX u.label))
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := ZMod p) (pd (rowOfSkelX u.label)))
    (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t]).length) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 hh) (hnodes : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) (hle : n ≤ 2 ^ hh)
    (χ : Coins frameJ8 K)
    (hord : (bfsForest [t]).length ≤ orderOf (InhabJ8Comp.αC0 b χ))
    (hnb : ∀ j < n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      HonestSlotX.dVal b δ S (env0 H pd (bfsForest [t]) (chalVJ8 b χ) (pubCOf δ b H pd (bfsForest [t]) (cJ s f r) χ) j) ≠ 0 ∨
        HonestSlotX.aVal b δ S (env0 H pd (bfsForest [t]) (chalVJ8 b χ) (pubCOf δ b H pd (bfsForest [t]) (cJ s f r) χ) j) = 0) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubCOf δ b H pd (bfsForest [t]) (cJ s f r) χ) orbit)
      (trCOf δ b H pd (bfsForest [t]) (cJ s f r) χ nodes) := by
  have hlab := genX_label hgen
  have hroot : tripOf t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, hlab.1, hlab.2.1, hlab.2.2.1]
  have hH' : HdlOK p H := by rwa [ZMod.ringChar_zmod_n] at hH
  have hρ' := hρ δ b H pd (bfsForest [t]) (cJ s f r) χ
  rw [← hN] at hρ'
  exact computeChipVCLHX_honest_sat δ hgen H pd hH hp hsm hpair (InhabJ8Comp.αC0 b χ) (InhabJ8Comp.γC0 b χ)
    hord hn hN nodes (hinjX_of orbit nodes hnodes hle) b (chalVJ8 b χ) (pubCOf δ b H pd (bfsForest [t]) (cJ s f r) χ)
    orbit (fun i hi => ((hadjX_of orbit nodes hnodes i hi).trans (mul_comm _ _)))
    rfl rfl (hpIC δ b H pd _ _ χ) (hpS δ b pd _ hH' hcl rfl hroot χ) (hpO δ b H pd _ _ χ)
    (hpub δ b pd _ hH' hcl χ) hρ' hnb

end Chip

end
end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
