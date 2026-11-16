/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/RR49A.lean

The 155 figure
    is `RepriceJ9AB.numJ8X_optB_census32` (kernel `decide`): `figJ8X_155_optB`, `epsJ8X_lt_155_optB`,
    `probJ8X_lt_155_optB` here. `numJ9AX` is not used.
  * **The coin-free J-9 A lists** (round-0 columns only, `ReadsOnC frameJ8 ∅`): `extA`, `provsA`, `reqsA`, in the S8
    wiring order of `HokJ9AG9.acceptsJ9A_holdsN_finalLGG`:
    `ext .p = axPath`, `ext .s = pinCons ++ axLimb ++ jCons`,
    `provs .s = jProv ++ (pad8 inc ++ pad8 walkV ++ axTag ++ split)`; `reqs bl = (compReqsOf9 bl ++ ext bl).map liftRec`.
  * **The gates `gA gS : Bool`.**  The axis lists are present iff `gA`, the split lists iff `gS`.
  * `realIOA`, `real40A`: a J-8 datum along `toJ8` with the x / s (resp. p) lists replaced; `RR49A`, `LL4A`, `XA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LinkV1J9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComapJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.CompReqsX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RepriceJ9AB
import Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RR49A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (prob_le_of_outside)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Events (cK cK_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crJ crA crW staged_eq LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (byBal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)

noncomputable section

/-! ## 1. Option (b): the rows and the figure -/

/-- **Option (b) rows**: the J-8 rows of `r` with the provider row `blocks` enlarged by `AX + 2·SP` (the `TAG_ax`
provides and the two split provides per row join the service providers). -/
def rowsB (r : RowsJ9A) : RowsJ8 := { r.toRowsJ8 with blocks := r.blocks + r.AX + 2 * r.SP }

theorem rowsB_le {r : RowsJ9A} (h : RowsLe r.toRowsJ8 cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) :
    RowsLe (rowsB r) (rowsB cornerC9) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15⟩
  show r.blocks + r.AX + 2 * r.SP ≤ cornerC.blocks + 2 ^ 31 + 2 * 2 ^ 31
  omega

theorem rowsB_cornerC9 :
    rowsB cornerC9 = { cornerC9.toRowsJ8 with blocks := cornerC9.blocks + 2 ^ 31 + 2 * 2 ^ 31 } := rfl

/-- **The option-(b) figure: `< 2^-155`** at rows `≤ rowsB cornerC9`, `P ≤ 2^66`, `g' ≤ 2^32 + 2^31`
(`g' = g + N + AX`: `≤ 2^31` registered ids, `N ≤ 2^31` extra service consumers, `AX ≤ 2^31` axis limb consumes). -/
theorem figJ8X_155_optB (r : RowsJ8) (P g : ℕ) (h : RowsLe r (rowsB cornerC9)) (hP : P ≤ 2 ^ 66)
    (hg : g ≤ 2 ^ 32 + 2 ^ 31) : boundJ8X cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 := by
  have hn := RepriceJ9AB.numJ8X_optB_census32 cK cK_eq
  rw [← rowsB_cornerC9] at hn
  exact boundJ8X_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8X_corner h hP hg)) hn)

section Fig
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

theorem epsJ8X_lt_155_optB (X : DataJ8X (q := q) δ Tr St r P g) (hcK : Fintype.card K = cK)
    (h : RowsLe r (rowsB cornerC9)) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32 + 2 ^ 31) :
    epsilonOf (allJ8X X) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8X, quad_card, hcK]
  exact figJ8X_155_optB r P g h hP hg

open Classical in
/-- **The option-(b) probability statement**: `Pr[accept ∧ ¬ target] < 2^-155` at `g' ≤ 2^32 + 2^31`. -/
theorem probJ8X_lt_155_optB (X : DataJ8X (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8X X, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r (rowsB cornerC9)) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32 + 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8X_lt_155_optB X hcK h hP hg)

/-- **`DataJ8X` along a staging-preserving `f`.** -/
def DataJ8X.comap {Tr' : Type} {St' : (Coins frameJ8 K → Tr') → Prop} (X : DataJ8X (q := q) δ Tr St r P g)
    (f : Tr' → Tr) (hf : ∀ Q, St' Q → St fun χ => f (Q χ)) : DataJ8X (q := q) δ Tr' St' r P g where
  C := ComapJ9A.DataJ8C.comap X.C f hf
  vxReqs := fun tr χ => X.vxReqs (f tr) χ
  vxProvs := fun tr χ => X.vxProvs (f tr) χ
  vx_reads := fun Q hQ => X.vx_reads _ (hf Q hQ)

end Fig

/-! ## 2. The coin-free J-9 A lists -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 A externals** (coin-free): `x` as at J-8; `p` the axis path consumes; `s` = pins, the axis limb
consumes, the J consumes. -/
def extA (gA : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    (RealIOJ8.extT b Pb.toPubJ8 tr.toJ8 .x)
    (if gA then axPathReqsOf b Pb tr else [])
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++ (if gA then axLimbReqsOf b Pb tr else []) ++
      jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J)

/-- **The J-9 A providers** (coin-free): `x`, `p` as at J-8; `s` = J, inc, atom walk, `TAG_ax`, split. -/
def provsA (gA gS : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (RealIOJ8.provsT b Pb.toPubJ8 tr.toJ8 .x)
    (RealIOJ8.provsT b Pb.toPubJ8 tr.toJ8 .p)
    (jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
        (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
          else []) ++
        (if gA then axTagProvsOf b Pb tr else []) ++ (if gS then splitProvsOf b Pb tr else [])))

/-- **The J-9 A requests of balance `bl`** (coin-free): the twin compute's and the externals, lifted. -/
def reqsA (gA : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  (CompReqsX9.compReqsOf9 (K := K) Pb tr bl ++ extA b gA Pb tr bl).map (liftRec (L := 𝕂′))

section Congr
variable {tr tr' : TrJ9A (ZMod p)} (h : RealIOJ8.Agree0 tr.toJ8 tr'.toJ8)
  (hX : ∀ j : Fin 52, crAX j = 0 → tr.X j = tr'.X j) (hS : ∀ j : Fin 90, crSP j = 0 → tr.S j = tr'.S j)

include h hX in
theorem extA_congr (gA : Bool) (Pb : PubJ9A p) (bl : Bal) : extA b gA Pb tr bl = extA b gA Pb tr' bl := by
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.J tr'.J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  cases bl
  · exact RealIOJ8.extT_congr b h Pb.toPubJ8 .x
  · show (if gA then axPathReqsOf b Pb tr else []) = (if gA then axPathReqsOf b Pb tr' else [])
    rw [axPathReqsOf_congr b Pb hX]
  · show pinCons (p := p) (K := K) Pb.regs Pb.idx ++ (if gA then axLimbReqsOf b Pb tr else []) ++
        jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J =
      pinCons (p := p) (K := K) Pb.regs Pb.idx ++ (if gA then axLimbReqsOf b Pb tr' else []) ++
        jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr'.J
    rw [axLimbReqsOf_congr b Pb hX, hJ.2.1]

include h hX hS in
theorem provsA_congr (gA gS : Bool) (Pb : PubJ9A p) (bl : Bal) :
    provsA b gA gS Pb tr bl = provsA b gA gS Pb tr' bl := by
  have hV := DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.V tr'.V (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.V ⟨c, h1⟩ (by simp [crW, hc]))
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.J tr'.J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  have hA := ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA (fun _ => (0 : K))
      (fun _ => 0) (fun _ => (0 : K)) (fun _ => 0) tr.A tr'.A (by norm_num) (by norm_num)
      (fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp [crA, hc]))
  cases bl
  · exact RealIOJ8.provsT_congr b h Pb.toPubJ8 .x
  · exact RealIOJ8.provsT_congr b h Pb.toPubJ8 .p
  · show jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J ++
        (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
          (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)
            else []) ++
          (if gA then axTagProvsOf b Pb tr else []) ++ (if gS then splitProvsOf b Pb tr else [])) =
      jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr'.J ++
        (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr'.A) ++
          (if 1 ≤ Pb.krootsV then pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr'.V)
            else []) ++
          (if gA then axTagProvsOf b Pb tr' else []) ++ (if gS then splitProvsOf b Pb tr' else []))
    rw [hJ.2.2, hV.2, hA, axTagProvsOf_congr b Pb hX, splitProvsOf_congr b Pb hS]

include h hX in
theorem reqsA_congr (gA : Bool) (Pb : PubJ9A p) (bl : Bal)
    (hC : (CompReqsX9.compReqsOf9 (K := K) Pb tr bl) = CompReqsX9.compReqsOf9 Pb tr' bl) :
    reqsA δ b gA Pb tr bl = reqsA δ b gA Pb tr' bl := by
  unfold reqsA
  rw [hC, extA_congr b h hX gA Pb bl]

end Congr

/-- Along `StJ9A`, any two coins' traces agree on the round-0 columns of the J-8 projection, the axis chip and the
split chip. -/
theorem agreeA {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q) (χ χ' : Coins frameJ8 K) :
    RealIOJ8.Agree0 (Q χ).toJ8 (Q χ').toJ8 ∧ (∀ j : Fin 52, crAX j = 0 → (Q χ).X j = (Q χ').X j) ∧
      (∀ j : Fin 90, crSP j = 0 → (Q χ).S j = (Q χ').S j) :=
  ⟨RealIOJ8.agree0_of_staged (stJ8_toJ8 hQ) χ χ',
    fun j hj => staged_eq hQ.2.2.2.2.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le,
    fun j hj => staged_eq hQ.2.2.2.2.2.2.2 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le⟩

/-- Along `StJ9A`, the twin compute request lists are constant in the coins. -/
theorem compA_const (Pb : PubJ9A p) {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q)
    (χ χ' : Coins frameJ8 K) (bl : Bal) :
    (CompReqsX9.compReqsOf9 (K := K) Pb (Q χ) bl) = CompReqsX9.compReqsOf9 Pb (Q χ') bl :=
  CompReqsX9.compReqsX9_congr Pb.hn Pb.nodes Pb.orbit (Q χ).C (Q χ').C (by norm_num) (by norm_num)
    (fun j h1 h2 hj => staged_eq hQ.1 (r := 0) (fun i hi => absurd hi (by omega)) ⟨j, h1⟩ (by simp [crC9, hj])) bl

theorem lists_const (gA gS : Bool) (Pb : PubJ9A p) {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q)
    (χ χ' : Coins frameJ8 K) (bl : Bal) :
    reqsA δ b gA Pb (Q χ) bl = reqsA δ b gA Pb (Q χ') bl ∧
      provsA b gA gS Pb (Q χ) bl = provsA b gA gS Pb (Q χ') bl := by
  obtain ⟨h, hX, hS⟩ := agreeA hQ χ χ'
  exact ⟨reqsA_congr δ b h hX gA Pb bl (compA_const Pb hQ χ χ' bl), provsA_congr b h hX hS gA gS Pb bl⟩

end Lists

/-! ## 3. The J-9 A real data -/

section Real
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **A J-8 datum along `toJ8`, with the cell-export (#5) and service (#6) lists replaced by the J-9 A ones.** -/
def realIOA (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (gA gS : Bool) (Pb : PubJ9A p) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r P g :=
  { DataJ8C.comapA R with
    D := { (DataJ8C.comapA R).D with
      cxReqs := fun tr _ => reqsA δ b gA Pb tr .x
      cxProvs := fun tr _ => liftP (provsA b gA gS Pb tr .x)
      cx_reads := fun Q hQ χ χ' _ => by
        obtain ⟨h1, h2⟩ := lists_const δ b gA gS Pb hQ χ χ' .x
        simp only [h1, h2]
      svReqs := fun tr _ => reqsA δ b gA Pb tr .s
      svProvs := fun tr _ => effP (liftP (provsA b gA gS Pb tr .s))
      sv_reads := fun Q hQ χ χ' _ => by
        obtain ⟨h1, h2⟩ := lists_const δ b gA gS Pb hQ χ χ' .s
        simp only [h1, h2] } }

/-- **A J-8 #1 datum along `toJ8`, with the handle-path lists replaced by the J-9 A ones** (+ the axis path). -/
def real40A (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (gA gS : Bool) (Pb : PubJ9A p) :
    Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r :=
  { Data40J8.comapA L with
    pReqs := fun tr _ => reqsA δ b gA Pb tr .p
    pProvs := fun tr _ => liftP (provsA b gA gS Pb tr .p)
    p_reads := fun Q hQ ψ ψ' _ => by
      obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
      obtain ⟨h1, h2⟩ := lists_const δ b gA gS Pb hQ' (extY ψ y₁ y₂) (extY ψ' y₁ y₂) .p
      simp only [h1, h2] }

/-- **`RR49A`**: the J-9 (B) present data `LinkJ9G.RR49` along `toJ8`, x / s at the J-9 A lists. -/
abbrev RR49A (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ9A p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9 : (AcceptsJ8P.censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) (gA gS : Bool) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r P g :=
  realIOA δ b (LinkJ9G.RR49 δ b (g := g) R0 Pb.toPubJ8 c skel hs hL hP hnM hreg9) gA gS Pb

/-- **`LL4A`**: the R4 #1 data `LinkJ8R4.LL4` along `toJ8`, p at the J-9 A lists. -/
abbrev LL4A (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ9A p) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (gA gS : Bool) :
    Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r :=
  real40A δ b (LinkJ8R4.LL4 δ b L0 Pb.toPubJ8 skel hs hL) gA gS Pb

/-- **`XA`**: the full J-9 A datum. -/
def XA (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ9A p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9 : (AcceptsJ8P.censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) (gA gS : Bool) :
    DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r P g :=
  { DataJ8X.comap (withFpxV δ b (withLiftC (LinkJ9G.RR49 δ b (g := g) R0 Pb.toPubJ8 c skel hs hL hP hnM hreg9)
        (LinkJ8R4.LL4 δ b L0 Pb.toPubJ8 skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) TrJ9A.toJ8 (fun _ hQ => stJ8_toJ8 hQ) with
    C := withLiftC (RR49A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg9 gA gS) (LL4A δ b L0 Pb skel hs hL gA gS) }

/-! ### The readouts (definitional) -/

theorem rdS_A (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (gA gS : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (χ : Coins frameJ8 K) :
    (realIOA δ b R gA gS Pb).D.svReqs tr χ = reqsA δ b gA Pb tr .s ∧
      (realIOA δ b R gA gS Pb).D.svProvs tr χ = effP (liftP (provsA b gA gS Pb tr .s)) := ⟨rfl, rfl⟩

theorem rdX_A (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (gA gS : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (χ : Coins frameJ8 K) :
    (realIOA δ b R gA gS Pb).D.cxReqs tr χ = reqsA δ b gA Pb tr .x ∧
      (realIOA δ b R gA gS Pb).D.cxProvs tr χ = liftP (provsA b gA gS Pb tr .x) := ⟨rfl, rfl⟩

theorem rdP_A (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (gA gS : Bool) (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (χ : Coins frameJ8 K) :
    (real40A δ b L gA gS Pb).pReqs tr (toVSQ χ) = reqsA δ b gA Pb tr .p ∧
      (real40A δ b L gA gS Pb).pProvs tr (toVSQ χ) = liftP (provsA b gA gS Pb tr .p) := ⟨rfl, rfl⟩

end Real

end

end Nock.NockVMROM.Thm54.VclL.Handle.RR49A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.RR49A
#print axioms rowsB_le
#print axioms figJ8X_155_optB
#print axioms epsJ8X_lt_155_optB
#print axioms probJ8X_lt_155_optB
#print axioms DataJ8X.comap
#print axioms extA_congr
#print axioms provsA_congr
#print axioms lists_const
#print axioms realIOA
#print axioms real40A
#print axioms XA
#print axioms rdS_A
end Axioms
