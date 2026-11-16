/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenOrb.lean

 **orbit-parametric twins** of the `ComplJ8Of` / `ComplJ8OfAtom` / `ComplJ8Closed` definitions that fix the
 orbit `o`. Every twin takes `o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)` in place of `hF : DvdOK D`
 (suffix `O`); the proofs are the source theorems with `o` read as `o`. Nothing reads which `ω` was chosen:
 the orbit is used only through `powN_ok` (generic over any `StrictOrbitDomain`) and `le_two_pow_ht`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)

noncomputable section

section Orb
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- `PbOf` over a free orbit of height `htJ8 D`. -/
def PbOfO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length) :
    PubJ8 p where
  h := htJ8 D
  n := (bfsForest [D.t]).length
  hn := bfs_pos D.t
  nodes := powN o _
  orbit := o
  hC := htJ8 D
  nC := D.cells.length
  hnC := hC
  nodesC := powN o _
  orbitC := o
  kroots := krW D.cells D.reads
  hW := htJ8 D
  nW := (walkRows D.cells D.reads).length
  hnW := walk_pos _ _
  nodesW := powN o _
  orbitW := o
  hJ := htJ8 D
  nJ := D.jrows.length
  nodesJ := powN o _
  orbitJ := o
  lay := Nock.Jet.ChipJ8T.HonestRAP.layJ D.jrows.get
  hA := htJ8 D
  nA := D.acs.length
  hnA := hA
  nodesA := powN o _
  orbitA := o
  krootsV := krVOf D
  hV := htJ8 D
  nV := nVOf D
  hnV := nV_pos D
  nodesV := powN o _
  orbitV := o
  Rt := D.Rt
  regs := D.regs
  ids := D.ids
  idx := D.idx
  rk := D.rk

variable (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length)
  (hA : 0 < D.acs.length) (AV : AVPart p K)

/-- `trOf` over a free orbit. -/
def trOfO (χ : Coins frameJ8 K) : TrJ8 (ZMod p) where
  C := ComplJ8Comp.trCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ (PbOfO D o hC hA).nodes
  M := ComplJ8Enc.cellTrME δ b hC (powN o _) o (chalsMJ8 δ)
    (pubsCOf δ b D hC o) (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0) (mhF D) χ
  W := ComplJ8Enc.walkTrWE δ b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ)
    (pubsWOf δ b D o) (γV δ) (ρV δ) (encR δ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D) χ
  J := ComplJ8Jet.trJ δ b (powN o _) (chalsJJ8 χ) D.jrows.get
  A := AV.trA χ
  V := AV.trV χ


/-- `msgOf` over a free orbit. -/
def msgOfO (χ : Coins frameJ8 K) : MsgJ8' p K δ where
  m := ComplJ8Comp.mCOf D.H (cJ s f r)
  ρ := ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  ρS := ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  pubsC := pubsCOf δ b D hC o χ
  pubsW := pubsWOf δ b D o χ
  pubsJ := pubsJOf δ D χ
  pubsA := AV.pubsA χ
  pubsV := AV.pubsV χ


/-- `honestJ8Of` over a free orbit. -/
def honestJ8OfO (fams : List (List (BadSpec K))) : HonestJ8 p K δ Rg fuel s f r where
  t := D.t
  hgen := D.hgen
  H := D.H
  pd := D.pd
  Pb := PbOfO D o hC hA
  M := msgOfO δ b D o hC AV
  tr := trOfO δ b D o hC hA AV
  rows := ComplJ8Comp.canonRows (PbOfO D o hC hA) extraRows
  g := ComplJ8Comp.canonG (PbOfO D o hC hA)
  bad := badOf (badList [(⟨13, by decide⟩, (bfsForest [D.t]).length)] fams)

end Orb

section Orb2
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- `avOf` over a free orbit. -/
def avOfO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hA : 0 < D.acs.length) : AVPart p K where
  trA := trAOf δ b D hA (o)
  trV := trVOf δ b D (o)
  pubsA := pubsAOf δ b D hA (o)
  pubsV := pubsVOf δ b D (o)

/-- `stA_run` over a free orbit. -/
theorem stA_runO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hA : 0 < D.acs.length) :
    StagedCols frameJ8 TraceJ8.crA (fun χ => (avOfO δ b D o hA (K := K)).trA χ) :=
  ComplJ8AW.stA_gen δ b hA _ _ (fun χ => ChalsAZJ8.chalsAJ8Z δ χ) (fun χ => pubsAOf δ b D hA (o) χ)
    (fun χ => colAH δ b D hA (o) χ (pubsAOf δ b D hA (o) χ)) (newBA D)
    (fun χ χ' k hk => InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k (by omega)
      (fun h => aCol_cong δ b D χ χ' k (by omega) (fun h' => absurd h' (by omega)))
      (fun h => absurd h (by omega)))
    (fun χ χ' hχ k hk => InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k hk
      (fun h => aCol_cong δ b D χ χ' k (by omega) (fun h' => absurd h' (by omega)))
      (fun h => aCol_cong δ b D χ χ' (k - 1) (by omega) (fun _ => zA_round0 δ χ χ' hχ)))


/-- `stV_run` over a free orbit. -/
theorem stV_runO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hA : 0 < D.acs.length) :
    StagedCols frameJ8 TraceJ8.crW (fun χ => (avOfO δ b D o hA (K := K)).trV χ) :=
  ComplJ8AW.stV_gen δ b (krVOf D) (nV_pos D) _ (o) (fun χ => ChalsAZJ8.chalsAJ8Z δ χ)
    (fun χ => pubsVOf δ b D (o) χ) (fun χ => vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D)
    (fun χ χ' k hk => ComplJ8Walk.wColB_cong δ b _ _ _ _ _ _ _ _ D.acs D.preads k (by omega)
      (fun h => absurd h (by omega)))
    (fun χ χ' hχ k hk => ComplJ8Walk.wColB_cong δ b _ _ _ _ _ _ _ _ D.acs D.preads k hk
      (fun _ => zA_round0 δ χ χ' hχ))


/-- `famsOf` over a free orbit. -/
def famsOfO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length) : List (List (BadSpec K)) :=
  [ComplJ8CompPole.compPoles δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length, famCellV δ D,
    famCellH δ b D hC (o), famWalkV δ D, famWalkH δ D, famJ δ D]


/-- `famsOf_facts` over a free orbit. -/
theorem famsOfO_facts (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) :
    (∀ L ∈ famsOfO δ b D o hC (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsOfO δ b D o hC (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsOfO δ b D o hC (K := K)).map nPins).sum ≤ 2 ^ 40 := by
  have hγ := ComplJ8Bad.γH_readsOff (K := K) δ
  have hJOK : ∀ e ∈ famJ δ D (K := K), e.OK := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact ComplJ8Bad.ioPoles_OK δ _ _ _ hγ e h
    · exact ComplJ8Bad.ioPoles_OK δ _ _ _ hγ e h
  have pC : AllPin (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length) :=
    allPin_flatMap _ _ fun j _ => allPin_flatMap _ _ fun S _ => (slotPoles_len δ S _).2
  have pCV : AllPin (famCellV δ D (K := K)) := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, rfl⟩
    · exact allPin_flatMap _ _ (fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _) e he
  have pCH : AllPin (famCellH δ b D hC (o) (K := K)) := allPin_map _ _ fun x => quadPole_pin δ _ _
  have pWV : AllPin (famWalkV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _
  have pWH : AllPin (famWalkH δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => quadPole_pin δ _ _
  have pJ : AllPin (famJ δ D (K := K)) :=
    allPin_append _ _ (allPin_map _ _ fun x => quadPole_pin δ _ _) (allPin_map _ _ fun x => quadPole_pin δ _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    simp only [famsOfO, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ComplJ8CompPole.compPoles_OK δ _ _ _ _
    · exact famCellV_OK δ D
    · exact famCellH_OK δ b D hC _
    · exact famWalkV_OK δ D
    · exact famWalkH_OK δ D
    · exact hJOK
  · intro L hL e he i N hN
    simp only [famsOfO, List.mem_cons, List.not_mem_nil, or_false] at hL
    have hp : AllPin L := by rcases hL with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨j, g, rfl⟩ := hp e he
    cases hN
  · have hn := h31 _ (show (bfsForest [D.t]).length ∈ sizesJ8 D by simp [sizesJ8])
    have hnC := h31 _ (show D.cells.length ∈ sizesJ8 D by simp [sizesJ8])
    have hnW := h31 _ (show (walkRows D.cells D.reads).length ∈ sizesJ8 D by simp [sizesJ8])
    have hnJ := h31 _ (show D.jrows.length ∈ sizesJ8 D by simp [sizesJ8])
    have l1 : (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length).length ≤
        (bfsForest [D.t]).length * 12 := by
      unfold ComplJ8CompPole.compPoles
      refine (ComplJ8Of.length_flatMap_le _ _ 12 fun j _ => ?_).trans (by simp)
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun S _ => (slotPoles_len δ S _).1).trans (by simp [ComplJ8CompPole.SLOTS]; rfl)
    have l2 : (famCellV δ D (K := K)).length ≤ 1 + D.cells.length * 5 := by
      unfold famCellV
      rw [List.length_cons]
      have := ComplJ8Of.length_flatMap_le (List.range D.cells.length)
        (fun j => (cellVx δ D j (K := K)).map (ComplJ8Bad.quadPole δ WeightsJ8.c5)) 5 (fun j _ => by simp [cellVx])
      simp only [List.length_range] at this; omega
    have l3 : (famCellH δ b D hC (o) (K := K)).length ≤ D.cells.length := by simp [famCellH]
    have l4 : (famWalkV δ D (K := K)).length ≤ (walkRows D.cells D.reads).length * 3 := by
      unfold famWalkV
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => by simp [walkVx]).trans (by simp)
    have l5 : (famWalkH δ D (K := K)).length ≤ (walkRows D.cells D.reads).length * 3 := by
      unfold famWalkH
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => by rw [List.length_map]; exact walkHx_len δ D j).trans (by simp)
    have l6 : (famJ δ D (K := K)).length ≤ D.jrows.length * 28 := by
      unfold famJ ComplJ8Bad.ioPoles
      simp only [List.length_append, List.length_map]
      have h1 := jKeysT_len D.jrows.get
      have h2 := jKeysX_len D.jrows.get
      omega
    have e : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have e66 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    simp only [famsOfO, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := nPins_le_length (ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [D.t]) (bfsForest [D.t]).length)
    have := nPins_le_length (famCellV δ D (K := K))
    have := nPins_le_length (famCellH δ b D hC (o) (K := K))
    have := nPins_le_length (famWalkV δ D (K := K))
    have := nPins_le_length (famWalkH δ D (K := K))
    have := nPins_le_length (famJ δ D (K := K))
    rw [e66]; rw [e] at hn hnC hnW hnJ
    omega

/-- `famsA` over a free orbit. -/
def famsAO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hA : 0 < D.acs.length) : List (List (BadSpec K)) :=
  [famAZ, famAV δ D, famAH δ b D hA (o), famMB δ b D hA (o), famC δ b D hA (o),
    famMI δ b D hA (o), famAWV δ D, famAWH δ D]


/-- `famsA_facts` over a free orbit. -/
theorem famsAO_facts (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hA : 0 < D.acs.length) :
    (∀ L ∈ famsAO δ b D o hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsAO δ b D o hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsAO δ b D o hA (K := K)).map nPins).sum ≤ 1 + 9 * D.acs.length + 6 * nVOf D := by
  have pZ : AllPin (famAZ (K := K)) := fun e he => by
    simp only [famAZ, List.mem_singleton] at he; subst he; exact ⟨_, _, rfl⟩
  have pV : AllPin (famAV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pH : AllPin (famAH δ b D hA (o) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMB : AllPin (famMB δ b D hA (o) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pC : AllPin (famC δ b D hA (o) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMI : AllPin (famMI δ b D hA (o) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWV : AllPin (famAWV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWH : AllPin (famAWH δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    simp only [famsAO, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact famAZ_OK
    · exact famAV_OK δ D
    · exact famAH_OK δ b D hA _
    · exact famMB_OK δ b D hA _
    · exact famC_OK δ b D hA _
    · exact famMI_OK δ b D hA _
    · exact famAWV_OK δ D
    · exact famAWH_OK δ D
  · intro L hL e he i N hN
    simp only [famsAO, List.mem_cons, List.not_mem_nil, or_false] at hL
    have hp : AllPin L := by
      rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [pZ, pV, pH, pMB, pC, pMI, pWV, pWH]
    obtain ⟨j, g, rfl⟩ := hp e he
    cases hN
  · have l1 : (famAV δ D (K := K)).length ≤ D.acs.length * 5 := by
      unfold famAV
      exact (ComplJ8Of.length_flatMap_le _ _ 5 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l2 : (famAWV δ D (K := K)).length ≤ nVOf D * 3 := by
      unfold famAWV
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l3 : (famAWH δ D (K := K)).length ≤ nVOf D * 3 := by
      unfold famAWH

      refine (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => ?_).trans (by rw [List.length_range])
      rw [List.length_map]; unfold awHx; split_ifs
      · exact le_of_eq rfl
      · exact Nat.zero_le _
    simp only [famsAO, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := nPins_le_length (famAZ (K := K))
    have := nPins_le_length (famAV δ D (K := K))
    have := nPins_le_length (famAH δ b D hA (o) (K := K))
    have := nPins_le_length (famMB δ b D hA (o) (K := K))
    have := nPins_le_length (famC δ b D hA (o) (K := K))
    have := nPins_le_length (famMI δ b D hA (o) (K := K))
    have := nPins_le_length (famAWV δ D (K := K))
    have := nPins_le_length (famAWH δ D (K := K))
    have e1 : (famAZ (K := K)).length = 1 := rfl
    have e2 : (famAH δ b D hA (o) (K := K)).length = D.acs.length := by rw [famAH, List.length_map, List.length_range]
    have e3 : (famMB δ b D hA (o) (K := K)).length = D.acs.length := by rw [famMB, List.length_map, List.length_range]
    have e4 : (famC δ b D hA (o) (K := K)).length = D.acs.length := by rw [famC, List.length_map, List.length_range]
    have e5 : (famMI δ b D hA (o) (K := K)).length = D.acs.length := by rw [famMI, List.length_map, List.length_range]
    omega

/-- `famsAll` over a free orbit. -/
def famsAllO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hC : 0 < D.cells.length)
    (hA : 0 < D.acs.length) : List (List (BadSpec K)) :=
  famsOfO δ b D o hC ++ famsAO δ b D o hA

/-- `famsAll_facts` over a free orbit. -/
theorem famsAllO_facts (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D))
    (hC : 0 < D.cells.length) (hA : 0 < D.acs.length) (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) :
    (∀ L ∈ famsAllO δ b D o hC hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsAllO δ b D o hC hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsAllO δ b D o hC hA (K := K)).map nPins).sum ≤ 2 ^ 66 := by
  obtain ⟨o1, p1, c1⟩ := famsOfO_facts δ b (K := K) D o hC h31
  obtain ⟨o2, p2, c2⟩ := famsAO_facts δ b (K := K) D o hA
  have hacs := h31 _ (show D.acs.length ∈ sizesJ8 D by simp [sizesJ8])
  have hnV := h31 _ (show nVOf D ∈ sizesJ8 D by simp [sizesJ8])
  refine ⟨fun L hL => ?_, fun L hL => ?_, ?_⟩
  · rcases List.mem_append.mp hL with h | h
    exacts [o1 L h, o2 L h]
  · rcases List.mem_append.mp hL with h | h
    exacts [p1 L h, p2 L h]
  · rw [famsAllO, List.map_append, List.sum_append]
    have e : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
    have e40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
    rw [e] at hacs hnV; rw [e40] at c1; rw [e66]
    omega

/-- **`awOK_D` over a free orbit.** The atom walk at a coin outside its two pole families**, for any run data `D` whose handle kinds are in
`{0, 1, 2}`: absent (`preads = []`) by `awOK_absent`, present by `awOK_list` under `hwalkA`. -/
theorem awOK_DO (D : J8Data p Rg fuel s f r) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 D)) (hp63 : 2 ^ 63 < p)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hkind : ∀ x, ((D.H x).1 : ZMod p) = 0 ∨ ((D.H x).1 : ZMod p) = 1 ∨ ((D.H x).1 : ZMod p) = 2)
    (χ : Coins frameJ8 K) (hgV : ∀ e ∈ famAWV δ D (K := K), χ ∉ e.ev)
    (hgH : ∀ e ∈ famAWH δ D (K := K), χ ∉ e.ev) :
    AWChipOK δ b (krVOf D) (nV_pos D) (powN (o) (nVOf D)) (o) (chalsAJ8Z δ χ)
      (pubsVOf δ b D (o) χ)
      (fun j => trVOf δ b D (o) χ
        (Fin.cast (CellTwinK.walkChipHQK_width δ (krVOf D) b (nV_pos D) _ _ _ _) j)) := by
  by_cases h0 : D.preads = []
  · refine ComplJ8AW.awOK_absent δ b (krVOf D) (nV_pos D) _ _ _ _ (by simp [krVOf, h0]) _ ?_
    simp [pubsVOf, h0]
  have hk : krVOf D = krW D.acs D.preads := by simp [krVOf, h0]
  have hN : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, h0]
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (o) (le_two_pow_ht D hmV)
  have hcells : D.acs.length < ringChar (ZMod p) := by
    have := h31 _ hmA; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hkp : krW D.acs D.preads + (walkRows D.acs D.preads).length < ringChar (ZMod p) := by
    have h1 := h31 _ hmV
    have h2 := krW_le_rows D.acs D.preads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; rw [hN] at h1; omega
  have hrows := famAWV_good δ D χ hgV
  have hpoleH : ∀ (i : Fin (nVOf D)), ∀ x ∈ awHx δ D i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hgH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := aw_dRow_split δ b D (o) hinj χ (pubsVOf δ b D (o) χ)
  have hP : ∀ i, pubsVOf δ b D (o) χ i =
      if i < 4 then pubsV0 δ D χ i else if i < 6 then pub2 δ (vhX δ b D (o) χ) i
      else if i < 8 then pub2 δ (vhP δ b D (o) χ) i else 0 := by
    intro i; simp only [pubsVOf, if_neg h0]
  have hP0 : ∀ i, pubsV0 δ D χ i =
      if i < 2 then pub2 δ (vxT δ D χ) i else if i < 4 then pub2 δ (vpT δ D χ) i else 0 := by
    intro i; simp only [pubsV0, if_neg h0]
  have qx : ∀ i, i < 2 → pubsVOf δ b D (o) χ i = pub2 δ (vxT δ D χ) i := by
    intro i hi; rw [hP, if_pos (show i < 4 by omega), hP0, if_pos hi]
  have qp : ∀ i, 2 ≤ i → i < 4 → pubsVOf δ b D (o) χ i = pub2 δ (vpT δ D χ) i := by
    intro i h1 h2; rw [hP, if_pos h2, hP0, if_neg (show ¬ i < 2 by omega), if_pos h2]
  have qhx : ∀ i, 4 ≤ i → i < 6 → pubsVOf δ b D (o) χ i = pub2 δ (vhX δ b D (o) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_pos h2]
  have qhp : ∀ i, 6 ≤ i → i < 8 → pubsVOf δ b D (o) χ i = pub2 δ (vhP δ b D (o) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_neg (show ¬ i < 6 by omega), if_pos h2]
  have hres := ComplJ8AW.awOK_list δ b (nV_pos D) (powN (o) (nVOf D)) (o) (chalsAJ8Z δ χ)
    (pubsVOf δ b D (o) χ) (zA δ χ) (γV δ χ) (ρV δ χ) D.acs D.preads (kLV D) (vLV D) (kRV D) (vRV D)
    (by rw [hrc]; exact hp63) hcells hwalkA hkp hN hinj hadj (ChalsAZJ8.chalsAJ8Z_ok δ χ)
    (fun j hj => by rw [vR_eq]; exact (hrows j hj).1) (fun j hj => by rw [vR_eq]; exact (hrows j hj).2.1)
    (fun j hj => by rw [vR_eq]; exact (hrows j hj).2.2)
    (by
      rw [qx 0 (by norm_num), qx 1 (by norm_num), pub2_mk2 δ _ 0 rfl]
      rfl)
    (by
      rw [qp 2 (by norm_num) (by norm_num), qp 3 (by norm_num) (by norm_num), pub2_mk2 δ _ 2 rfl]
      rfl)
    (fun i => hkind _) (fun i => hkind _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).idx, (kLV D i, vLV D i),
        (kRV D i, vRV D i))) (by simp only [awHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre,
        (kLV D i, vLV D i))) (by simp only [awHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre + 1,
        (kRV D i, vRV D i))) (by
          simp only [awHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by
      show Quad.mk _ (pubsVOf δ b D (o) χ 4) (pubsVOf δ b D (o) χ 5) = _
      rw [qhx 4 (by norm_num) (by norm_num), qhx 5 (by norm_num) (by norm_num), pub2_mk2 δ _ 4 rfl]
      unfold vhX
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN
      rw [hk, aw_dN_pubs δ b D (o) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (o) χ) _ (Or.inl rfl)])
    (by
      show Quad.mk _ (pubsVOf δ b D (o) χ 6) (pubsVOf δ b D (o) χ 7) = _
      rw [qhp 6 (by norm_num) (by norm_num), qhp 7 (by norm_num) (by norm_num), pub2_mk2 δ _ 6 rfl]
      unfold vhP
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN
      rw [hk, aw_dN_pubs δ b D (o) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (o) χ) _
          (Or.inr (Or.inl rfl)),
        aw_dN_pubs δ b D (o) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (o) χ) _ (Or.inr (Or.inr rfl))])
  unfold trVOf
  rw [hk]
  exact hres


end Orb2

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
