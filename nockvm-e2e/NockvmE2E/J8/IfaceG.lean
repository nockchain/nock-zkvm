/-
the generic interface layer.
`NIface` (nockvm's N1-N3 at frameJ8 as ONE bundle), `CLay` (our chip layer: flat columns, tables, constraints,
publics, `accOn`), `ofIface` (the `RapAirJ` built from the two), `accOn_ofIface`; and the J-8 instances `nJ8`,
`clJ8` with `J8_eq : J8 d hd = ofIface (clJ8 d hd) (nJ8 d hd)`.
-/
import NockvmE2E.J8.InstJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.J8.IfaceG

open NockvmE2E.Rap NockvmE2E.Succ
open Nock.TraceGenExe

/-! ## 1. `NIface`: N1-N3 at nock's coin frame -/

/-- **N1-N3 at the generic level**: the summand list with its price (`< 2^-155`), POINTWISE soundness of `Acc` outside the
list, and one-round for every summand. Nock's own `BadSummand` at `frameJ8` (shared by J-8, J-9 B, J-9 A). -/
structure NIface {Tr : Type}
    (St : (Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Tr) → Prop) (Msg0 : Type)
    (Acc : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Msg0 → Tr → Prop) (Holds : Prop) where
  /-- N2: the list -/
  list : List (Nock.NockVMROM.Thm54.SVFrame.BadSummand Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC Tr St)
  /-- N2: its price -/
  eps : Nock.NockVMROM.Thm54.SVFrame.epsilonOf list < 1 / (2 : ℚ) ^ 155
  /-- N1: pointwise soundness -/
  sound : ∀ χ M tr, Acc χ M tr → (∀ s ∈ list, ¬ s.mem tr χ) → Holds
  /-- N3 -/
  oneRound : ∀ s ∈ list,
    Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.OneRoundCD Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 s.coins s.dep

/-! ## 2. `CLay`: the chip layer -/

/-- **The chip layer** (ours): flat columns, the tables and their constraints, the non-chip conjuncts, and `accOn`
(vanishing of the PRESENT tables' constraints, `Pub`, `StmtOK`, bound fixed columns give `Acc`). `Acc` is over nock's
message `Msg0` and trace `Tr`; `Msg` is the interface message (`Msg0` plus extra publics) with `msg0`. -/
structure CLay {Tr : Type}
    (St : (Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Tr) → Prop) (Msg0 : Type)
    (Acc : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Msg0 → Tr → Prop) where
  ι0 : Type
  fι : Fintype ι0
  dι : DecidableEq ι0
  colR : ι0 → ℕ
  hround : ∀ j, colR j ≤ 2
  unflat : (ι0 → (ZMod Nock.Field.p)[X]) → Tr
  stUnflat : ∀ Q : Coins InstJ8.Φ0 KC → ι0 → (ZMod Nock.Field.p)[X], TracesStaged InstJ8.Φ0 colR Q →
    St (fun χ => unflat (Q χ))
  pre : ι0 → Option (ZMod Nock.Field.p)[X]
  Msg : Type
  Mcode : Type
  fM : Fintype Mcode
  dM : DecidableEq Mcode
  dec : Mcode → Msg
  msg0 : Msg → Msg0
  T : ℕ
  Ht : Fin T → Finset (ZMod Nock.Field.p)
  H : Finset (ZMod Nock.Field.p)
  hHt : ∀ t, Ht t ⊆ H
  ωt : Fin T → ZMod Nock.Field.p
  tabC : ι0 → Fin T
  sz : Fin T → ℕ
  consT : Coins InstJ8.Φ0 KC → Msg → (t : Fin T) → Fin (sz t) →
    MvPolynomial (ι0 × Fin 2) (ZMod Nock.Field.p)
  hdeg : ∀ χ M t l, (consT χ M t l).totalDegree ≤ 4
  Pub : Coins InstJ8.Φ0 KC → Msg → Prop
  StmtOK : Prop
  /-- the tables that are present (absent ones are read off `Pub`'s absent publics, not off the trace) -/
  present : Fin T → Prop
  accOn : ∀ (χ : Coins InstJ8.Φ0 KC) (M : Msg) (tr : ι0 → (ZMod Nock.Field.p)[X]),
    (∀ t, present t → ∀ l : Fin (sz t), ∀ x ∈ Ht t, (MvPolynomial.aeval
      (fun q : ι0 × Fin 2 => (tr q.1).comp (Polynomial.C (ωt (tabC q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (consT χ M t l)).eval x = 0) →
    Pub χ M → StmtOK → (∀ j c, present (tabC j) → pre j = some c → tr j = c) →
    Acc χ (msg0 M) (unflat tr)
  cap_ns : ∑ t, sz t ≤ 2 ^ 20
  cap_m : @Fintype.card ι0 fι * 2 + 3 * (4 - 1) ≤ 2 ^ 12
  cap_H : H.card ≤ 2 ^ 26

attribute [instance] CLay.fι CLay.dι CLay.fM CLay.dM

section Gen
variable {Tr : Type} {St : (Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Tr) → Prop} {Msg0 : Type}
  {Acc : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → Msg0 → Tr → Prop}

/-- the number of constraints -/
def CLay.ns (CL : CLay St Msg0 Acc) : ℕ := ∑ t, CL.sz t

/-- the flat constraint `i` -/
noncomputable def CLay.Cfun (CL : CLay St Msg0 Acc) (χ : Coins InstJ8.Φ0 KC) (M : CL.Msg) (i : Fin CL.ns) :
    MvPolynomial (CL.ι0 × Fin 2) (ZMod Nock.Field.p) :=
  CL.consT χ M (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

/-- the table of the flat constraint `i` -/
def CLay.tabSfun (CL : CLay St Msg0 Acc) (i : Fin CL.ns) : Fin CL.T := (finSigmaFinEquiv.symm i).1

theorem vanish_conv_G (CL : CLay St Msg0 Acc) (χ : Coins InstJ8.Φ0 KC) (M : CL.Msg)
    (tr : CL.ι0 → (ZMod Nock.Field.p)[X])
    (h : ∀ i : Fin CL.ns, ∀ x ∈ CL.Ht (CL.tabSfun i), (MvPolynomial.aeval
      (fun q : CL.ι0 × Fin 2 => (tr q.1).comp (Polynomial.C (CL.ωt (CL.tabC q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (CL.Cfun χ M i)).eval x = 0) :
    ∀ t : Fin CL.T, ∀ l : Fin (CL.sz t), ∀ x ∈ CL.Ht t, (MvPolynomial.aeval
      (fun q : CL.ι0 × Fin 2 => (tr q.1).comp (Polynomial.C (CL.ωt (CL.tabC q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (CL.consT χ M t l)).eval x = 0 := by
  intro t l x hx
  have := h (finSigmaFinEquiv ⟨t, l⟩) x (by simpa [CLay.tabSfun] using hx)
  unfold CLay.Cfun at this
  rw [Equiv.symm_apply_apply] at this
  exact this

open Classical in
/-- **`ofIface`**: the `RapAirJ` of a chip layer and an N1-N3 bundle (the generic twin of `InstJ8.J8`). -/
noncomputable def ofIface {Holds : Prop} (CL : CLay St Msg0 Acc) (N : NIface St Msg0 Acc Holds) :
    RapAirJ (ZMod Nock.Field.p) KC where
  Φ0 := InstJ8.Φ0
  ι0 := CL.ι0
  fι := CL.fι
  dι := CL.dι
  colRound0 := CL.colR
  hround := CL.hround
  hcoin := InstJ8.hcoin0
  pre := CL.pre
  Msg := CL.Msg
  Mcode := CL.Mcode
  fM := CL.fM
  dM := CL.dM
  dec := CL.dec
  Acc χ M tr := Acc χ (CL.msg0 M) (CL.unflat tr)
  Holds := Holds
  summands := N.list.map (fun s => pullback CL.unflat CL.stUnflat (InstJ8.ofNock s))
  sound := by
    intro χ M tr h hs
    refine N.sound χ (CL.msg0 M) (CL.unflat tr) h ?_
    intro s hsL hmem
    exact hs _ (List.mem_map_of_mem hsL) hmem
  eps := by
    have h1 : NockvmE2E.Rap.epsilonOf (N.list.map (fun s => pullback CL.unflat CL.stUnflat (InstJ8.ofNock s))) =
        Nock.NockVMROM.Thm54.SVFrame.epsilonOf N.list := by
      have := epsilonOf_map_pullback (K := KC) CL.unflat CL.stUnflat (N.list.map InstJ8.ofNock)
      rw [List.map_map] at this
      rw [show (fun s => pullback CL.unflat CL.stUnflat (InstJ8.ofNock s)) =
        (pullback CL.unflat CL.stUnflat) ∘ InstJ8.ofNock from rfl, this]
      unfold NockvmE2E.Rap.epsilonOf Nock.NockVMROM.Thm54.SVFrame.epsilonOf
      simp only [List.map_map]
      rfl
    rw [h1]
    exact N.eps.le
  oneRound := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
    have := N.oneRound n hn
    exact ⟨this.1, this.2.1, this.2.2⟩
  H := CL.H
  T := CL.T
  Ht := CL.Ht
  hHt := CL.hHt
  ωt := CL.ωt
  r := 2
  off t k := CL.ωt t ^ (k : ℕ)
  hoff t k := rfl
  tabC := CL.tabC
  ns := CL.ns
  tabS := CL.tabSfun
  d := 4
  hd2 := Or.inl (by norm_num)
  C := CL.Cfun
  hdeg χ M i := CL.hdeg χ M _ _
  hCreads M i χ χ' h := by
    have : χ = χ' := funext fun j => h j (Finset.mem_univ j)
    rw [this]
  Pub := CL.Pub
  StmtOK := CL.StmtOK
  acc_of := by
    intro χ M tr hv hp hs hpre
    exact CL.accOn χ M tr (fun t _ => vanish_conv_G CL χ M tr hv t) hp hs (fun j c _ => hpre j c)
  cap_ns := CL.cap_ns
  cap_d := by norm_num
  cap_m := CL.cap_m
  cap_H := CL.cap_H

/-- **`accOn_ofIface`**: the interface accepts as soon as the constraints of the PRESENT tables vanish (generic twin of
`InstJ8.accOn_J8`). -/
theorem accOn_ofIface {Holds : Prop} (CL : CLay St Msg0 Acc) (N : NIface St Msg0 Acc Holds) :
    (ofIface CL N).AccOn CL.present := by
  intro χ M tr hv hp hs hpre
  refine CL.accOn χ M tr ?_ hp hs (fun j c hj => hpre j c hj)
  intro t ht l x hx
  have e : CL.tabSfun (finSigmaFinEquiv ⟨t, l⟩) = t := by
    unfold CLay.tabSfun; rw [Equiv.symm_apply_apply]
  have ht' : CL.present (CL.tabSfun (finSigmaFinEquiv ⟨t, l⟩)) := by rw [e]; exact ht
  have hx' : x ∈ CL.Ht (CL.tabSfun (finSigmaFinEquiv ⟨t, l⟩)) := by rw [e]; exact hx
  have h1 := hv (finSigmaFinEquiv ⟨t, l⟩) ht' x hx'
  have h2 : (MvPolynomial.aeval
      (fun q : CL.ι0 × Fin 2 => (tr q.1).comp (Polynomial.C (CL.ωt (CL.tabC q.1) ^ (q.2 : ℕ)) * Polynomial.X))
      (CL.Cfun χ M (finSigmaFinEquiv ⟨t, l⟩))).eval x = 0 := h1
  unfold CLay.Cfun at h2
  rw [Equiv.symm_apply_apply] at h2
  exact h2

end Gen

/-! ## 3. the J-8 instances -/

section J8
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open NockvmE2E.J8.InstJ8 (Datum DatumOK)

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinFact
  Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.twinAlg

/-- the J-8 accept predicate, over nock's message and trace -/
def AccJ8 (d : Datum) :
    Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → MsgJ8' InstJ8.P KC deltaF →
      TrJ8 (ZMod InstJ8.P) → Prop :=
  fun χ M tr => AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 d.Pb d.Rg d.c χ M tr d.r d.g

/-- **`nJ8`**: N1-N3 at J-8, the four `E2EJ8Iface` terms -/
noncomputable def nJ8 (d : Datum) (hd : DatumOK d) :
    NIface (Tr := TrJ8 (ZMod InstJ8.P)) StJ8 (MsgJ8' InstJ8.P KC deltaF) (AccJ8 d) (Nock.Jet.HoldsN d.c) where
  list := Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.listJ8V deltaF powerBasis3 d.Pb d.c d.r d.g
    hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg
  eps := Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.epsilonOf_listJ8V deltaF powerBasis3 d.Pb d.c
    hd.hcK hd.hr hd.hg hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg
  sound := by
    intro χ M tr h hs
    have := InstJ8.charP_KC'
    have := InstJ8.charP_KQ'
    exact Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.soundJ8V_pointwise deltaF powerBasis3 d.Pb hd.hRg
      d.c rfl hd.hr hd.hqM hd.hk hd.hmax hd.hg hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg χ M tr h hs
  oneRound := by
    intro s hs
    have := Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface.oneRound_listJ8V deltaF powerBasis3 d.Pb d.c d.r
      d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg s hs
    exact ⟨this.ne, this.same, this.dep_le⟩

open Classical in
set_option maxRecDepth 50000 in
/-- **`clJ8`**: the J-8 chip layer, the existing `InstJ8` pieces -/
noncomputable def clJ8 (d : Datum) (hd : DatumOK d) :
    CLay (Tr := TrJ8 (ZMod InstJ8.P)) StJ8 (MsgJ8' InstJ8.P KC deltaF) (AccJ8 d) where
  ι0 := InstJ8.Ι
  fι := inferInstance
  dι := inferInstance
  colR := InstJ8.colR
  hround := InstJ8.colR_le
  unflat := InstJ8.unflat
  stUnflat := InstJ8.stJ8_unflat
  pre := InstJ8.preJ d
  Msg := InstJ8.Msg
  Mcode := InstJ8.Mcode
  fM := inferInstance
  dM := inferInstance
  dec := InstJ8.decM
  msg0 := Prod.fst
  T := 6
  Ht := InstJ8.HtOf d
  H := InstJ8.HdomOf d
  hHt := hd.hHt
  ωt := InstJ8.omegaOf d
  tabC := InstJ8.tabΙ
  sz := InstJ8.sz d
  consT := InstJ8.consT d
  hdeg χ M t l := InstJ8.consT_deg d χ M t l
  Pub := InstJ8.PubP d
  StmtOK := InstJ8.StmtP d
  present := InstJ8.presentJ8 d
  accOn χ M tr hv hp hs hpre := InstJ8.accGen d hd χ M tr hv hp hs hpre
  cap_ns := InstJ8.cap_ns_of d
  cap_m := by
    show Fintype.card InstJ8.Ι * 2 + 3 * (4 - 1) ≤ 2 ^ 12
    rw [InstJ8.card_Ι]; norm_num
  cap_H := InstJ8.cap_H_of d hd

set_option maxRecDepth 50000 in
/-- **`J8_eq`**: the hand-written J-8 interface is the generic one at `(clJ8, nJ8)` -/
theorem J8_eq (d : Datum) (hd : DatumOK d) : InstJ8.J8 d hd = ofIface (clJ8 d hd) (nJ8 d hd) := rfl

end J8

#print axioms ofIface
#print axioms accOn_ofIface
#print axioms nJ8
#print axioms clJ8
#print axioms J8_eq

end NockvmE2E.J8.IfaceG
