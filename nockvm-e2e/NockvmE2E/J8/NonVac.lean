/-
non-vacuity: a TOY `RapAirJ (ZMod 2) (ZMod 2)` (one coin, one column,
one constraint, one weight-0 summand), so the structure is inhabited and `soundG`, `RapInput`, the round bound
are instantiated.
-/
import NockvmE2E.J8.Input
import NockvmE2E.J8.E2E
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

open Polynomial

namespace NockvmE2E.J8.Toy

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.J8

abbrev Φt : CoinFrame := ⟨1, fun _ => 0⟩

/-- A summand that prices coin `0` with weight `0` (never fires). -/
def sumd : BadSummand Φt (ZMod 2) (Unit → (ZMod 2)[X]) (TracesStaged Φt (fun _ : Unit => 0)) where
  coins := {0}
  dep := ∅
  disj := by simp
  badSet _ _ := ∅
  weight := 0
  card_le _ _ := by simp
  readsOn _ _ _ _ _ := rfl

/-- The toy interface. -/
noncomputable def toy : RapAirJ (ZMod 2) (ZMod 2) where
  Φ0 := Φt
  ι0 := Unit
  fι := inferInstance
  dι := inferInstance
  colRound0 := fun _ => 0
  hround := fun _ => by norm_num
  hcoin := fun _ => by show 0 < 2; norm_num
  pre := fun _ => none
  Msg := Unit
  Mcode := Unit
  fM := inferInstance
  dM := inferInstance
  dec := id
  Acc := fun _ _ _ => True
  Holds := True
  summands := [sumd]
  sound := fun _ _ _ _ _ => trivial
  eps := by simp [epsilonOf, sumd]
  oneRound := by
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨⟨0, by simp [sumd]⟩, by simp [sumd], by simp [sumd]⟩
  H := {1}
  T := 1
  Ht := fun _ => {1}
  hHt := fun _ => subset_rfl
  ωt := fun _ => 1
  r := 1
  off := fun _ _ => 1
  hoff := by simp
  tabC := fun _ => 0
  ns := 1
  tabS := fun _ => 0
  d := 0
  hd2 := Or.inr (fun _ => rfl)
  C := fun _ _ _ => 0
  hdeg := by simp
  hCreads := fun _ _ _ _ _ => rfl
  Pub := fun _ _ => True
  StmtOK := True
  acc_of := fun _ _ _ _ _ _ _ => trivial
  cap_ns := by norm_num
  cap_d := by norm_num
  cap_m := by simp
  cap_H := by simp

/-- Word layout of the toy: one word column carrying the polynomial itself. -/
def wm : WordMap toy (fun _ : Unit => 0) (ZMod 2)[X] where
  col := id
  hcol := fun _ => rfl
  hround := fun _ => by norm_num
  dec := fun _ w => w
  hpre := fun j c h => by simp [toy] at h

theorem toy_soundG : SoundG (rapJ toy wm (fun _ => ())) := soundG_rapJ wm _

theorem toy_rapInput : RapInput (rapJ toy wm (fun _ => ())) 4 := rapInput_rapJ wm _

theorem toy_roundBound (m0 : (rapJ toy wm (fun _ => ())).M0) (r : ℕ) :
    roundBound (rapJ toy wm (fun _ => ())) blkOf m0 r ≤ ENNReal.ofReal (1 / 2 ^ 155) :=
  roundBound_rapJ_le wm _ m0 r


/-! ## Row 6: a non-vacuity instance WITH a public column, over `ZMod 17`

`toyP : RapAirJ (ZMod 17) (ZMod 17)`: columns `Bool` (`false` = trace column, `true` = public column in round 2),
one constraint `X(false,0) - C m` reading the public message `m`; `Acc := True`, `Holds := True`. `toyPR : PubRead`
opens the public column at a fixed point and reads `m` from it. Then every J-side argument of
`rap_fri_merkle_sound_deep_J` is instantiated (`toy_e2e_J`). -/

section Public

open NockvmE2E.Merkle.RapFriQ Domain NockvmE2E.Deep

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

noncomputable instance toyNB : NonBinaryField (ZMod 17) where
  toField := inferInstance
  char_neq_2 := by decide

abbrev Φp : CoinFrame := ⟨1, fun _ => 0⟩

def sump : BadSummand Φp (ZMod 17) (Bool → (ZMod 17)[X]) (TracesStaged Φp (fun b : Bool => if b then 2 else 0)) where
  coins := {0}
  dep := ∅
  disj := by simp
  badSet _ _ := ∅
  weight := 0
  card_le _ _ := by simp
  readsOn _ _ _ _ _ := rfl

noncomputable def toyP : RapAirJ (ZMod 17) (ZMod 17) where
  Φ0 := Φp
  ι0 := Bool
  fι := inferInstance
  dι := inferInstance
  colRound0 := fun b => if b then 2 else 0
  hround := fun b => by cases b <;> simp
  hcoin := fun _ => by show 0 < 2; norm_num
  pre := fun _ => none
  Msg := ZMod 17
  Mcode := ZMod 17
  fM := inferInstance
  dM := inferInstance
  dec := id
  Acc := fun _ _ _ => True
  Holds := True
  summands := [sump]
  sound := fun _ _ _ _ _ => trivial
  eps := by simp [epsilonOf, sump]
  oneRound := by
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨⟨0, by simp [sump]⟩, by simp [sump], by simp [sump]⟩
  H := {1, 16}
  T := 1
  Ht := fun _ => {1, 16}
  hHt := fun _ => subset_rfl
  ωt := fun _ => 1
  r := 1
  off := fun _ _ => 1
  hoff := by simp
  tabC := fun _ => 0
  ns := 1
  tabS := fun _ => 0
  d := 1
  hd2 := Or.inr (fun _ => rfl)
  C := fun _ M _ => MvPolynomial.X (false, 0) - MvPolynomial.C (show ZMod 17 from M)
  hdeg := fun _ _ _ => by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    simp
  hCreads := fun _ _ _ _ _ => rfl
  Pub := fun _ _ => True
  StmtOK := True
  acc_of := fun _ _ _ _ _ _ _ => trivial
  cap_ns := by norm_num
  cap_d := by norm_num
  cap_m := by simp
  cap_H := by decide

instance : NeZero toyP.r := ⟨by show (1 : ℕ) ≠ 0; norm_num⟩

noncomputable def toyPR : PubRead toyP where
  pub := fun b => b
  ppt := fun _ => 5
  rd := fun v => v true
  gen := 1
  hrd := fun v v' h => h true rfl
  hCpub := by
    intro χ M i (p : Bool × Fin 1) hp
    have hp' : p ∈ (MvPolynomial.X (false, 0) - MvPolynomial.C (id (α := ZMod 17) M) :
        MvPolynomial (Bool × Fin 1) (ZMod 17)).vars := hp
    have h := MvPolynomial.vars_sub_subset (p := MvPolynomial.X (false, 0))
      (q := MvPolynomial.C (id (α := ZMod 17) M)) hp'
    have h3 : p ∈ ({(false, 0)} : Finset (Bool × Fin 1)) := by
      simpa [MvPolynomial.vars_X] using h
    have h2 : p = (false, 0) := Finset.mem_singleton.mp h3
    rw [h2]


private def rootp : (ZMod 17)ˣ := ⟨4, 13, by decide, by decide⟩

/-- A smooth FFT domain of size `2^2` in `ZMod 17`. -/
def domp : SmoothCosetFftDomain 2 (ZMod 17) where
  subgroupDomain :=
    { toFun := fun i ↦ rootp ^ i.toAdd.val
      map_one' := by decide
      map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := ⟨3, 6, by decide, by decide⟩

def shp : Fin 1 → ℕ+ := fun _ => 1

theorem toy_hNH : friBound shp 1 ≤ toyP.H.card := by
  have : toyP.H.card = 2 := by decide
  rw [this]
  decide

theorem toy_hpd : ∀ j c, toyP.pre j = some c → c.natDegree ≤ toyP.H.card := by
  intro j c h
  simp [toyP] at h

theorem toy_hω : ∀ i, domEmb domp i ∈ Set.range (algebraMap (ZMod 17) (ZMod 17)) :=
  fun i => ⟨domEmb domp i, by simp⟩

/-- The opening layout of the toy: 2 trace-column openings, no quotient chunk (`nq = d - 1 = 0`). -/
noncomputable def eP : Fin (1 + 1) ≃ (Bool × Fin toyP.r) ⊕
    Fin (deepParamsJ toyP toyPR domp (31 / 64) (friBound shp 1) toy_hNH toy_hpd).nq :=
  Fintype.equivOfCardEq (by
    show Fintype.card (Fin 2) = Fintype.card ((Bool × Fin 1) ⊕ Fin 0)
    simp)

noncomputable abbrev toyPJ := deepParamsJ toyP toyPR domp (31 / 64) (friBound shp 1) toy_hNH toy_hpd
noncomputable abbrev toyAJ := airJ toyP toyPR domp (31 / 64) (friBound shp 1) toy_hNH toy_hpd
noncomputable abbrev toyRJ := R0J toyP toyPR domp (31 / 64) (friBound shp 1)
noncomputable abbrev toyRtJ := RestJ toyP toyPR domp (31 / 64) (friBound shp 1) toy_hNH toy_hpd
noncomputable abbrev toyRvJ := RestVJ toyP toyPR domp (31 / 64) (friBound shp 1) toy_hNH toy_hpd

section Inst
open BatchedFri.Spec BatchedFri.Spec.BatchingRound Fri.Spec
variable [DecidableEq (toyPJ.statement toyRJ toyRtJ).M0] [Finite (toyPJ.statement toyRJ toyRtJ).M0]
  [DecidableEq (NockvmE2E.Succ.FriDeep.friPlan (ω := domp) toyPJ toyAJ toyRJ toyRtJ toyRvJ eP).Mfin]
  [Finite (NockvmE2E.Succ.FriDeep.friPlan (ω := domp) toyPJ toyAJ toyRJ toyRtJ toyRvJ eP).Mfin]
  [∀ j, SampleableType ((pSpec 0 (ω := domp) shp 170).Challenge j)]

/-- **Row 6.** Every J-side argument of `rap_fri_merkle_sound_deep_J` is instantiated on `toyP` (with a public
column): `J`, `pr`, `ω`, `s`, `d`, `hNH`, `hpd`, and the opening layout `e`. What stays a variable: the instances on
the message types, the oracle interfaces `I0 I Ifin`, the batching generator `G`, the digest type `Dg`/`enc`, the mask
data `md`, the leaf data `L`, `hdom`, `hω` (proved below as `toy_hω`), the FS model and guards, the adversary `A'`,
`Q_FS Q_H V Pn`, `θ ε hε hN hδ`, `hFS hH hterm hconfig`. -/
noncomputable def toy_e2e_J := rap_fri_merkle_sound_deep_J (ω := domp) (m := 1) toyP toyPR shp 1 170 (31 / 64) toy_hNH toy_hpd eP

/-- The numbers form (`≤ 2^-82`): same J-side instantiation (`hF`, `hDg`, rate are field/protocol arguments and stay
variables; `ZMod 17` is a toy field, so `hF` itself is not satisfiable here). -/
noncomputable def toy_e2e_J_numbers := rap_fri_merkle_sound_deep_J_numbers (ω := domp) (m := 1) toyP toyPR shp 1 toy_hNH toy_hpd eP

end Inst

/-! ## a TWO-table witness with different `H_t` (union domain), over `ZMod 17`

Table `0` owns column `0` on `H_0 = {1,16}`, table `1` owns column `1` on `H_1 = {4}`; the combined domain is
`H = {1,4,16}`. Constraint `i` is `X(i,0)^2` (degree `2`, so `hd2` holds by `2 ≤ d`). -/

section TwoTable

open NockvmE2E.Merkle.RapFriQ Domain NockvmE2E.Deep

abbrev Φ2 : CoinFrame := ⟨1, fun _ => 0⟩

def sum2 : BadSummand Φ2 (ZMod 17) (Fin 2 → (ZMod 17)[X]) (TracesStaged Φ2 (fun _ : Fin 2 => 0)) where
  coins := {0}
  dep := ∅
  disj := by simp
  badSet _ _ := ∅
  weight := 0
  card_le _ _ := by simp
  readsOn _ _ _ _ _ := rfl

def Ht2 : Fin 2 → Finset (ZMod 17) := ![{1, 16}, {4}]

noncomputable def toy2 : RapAirJ (ZMod 17) (ZMod 17) where
  Φ0 := Φ2
  ι0 := Fin 2
  fι := inferInstance
  dι := inferInstance
  colRound0 := fun _ => 0
  hround := fun _ => by norm_num
  hcoin := fun _ => by show 0 < 2; norm_num
  pre := fun _ => none
  Msg := Unit
  Mcode := Unit
  fM := inferInstance
  dM := inferInstance
  dec := id
  Acc := fun _ _ _ => True
  Holds := True
  summands := [sum2]
  sound := fun _ _ _ _ _ => trivial
  eps := by simp [epsilonOf, sum2]
  oneRound := by
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨⟨0, by simp [sum2]⟩, by simp [sum2], by simp [sum2]⟩
  H := {1, 4, 16}
  T := 2
  Ht := Ht2
  hHt := fun t => by fin_cases t <;> decide
  ωt := fun _ => 1
  r := 1
  off := fun _ _ => 1
  hoff := by simp
  tabC := id
  ns := 2
  tabS := id
  d := 2
  hd2 := Or.inl le_rfl
  C := fun _ _ i => MvPolynomial.X (i, 0) ^ 2
  hdeg := fun _ _ i => by
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    simp
  hCreads := fun _ _ _ _ _ => rfl
  Pub := fun _ _ => True
  StmtOK := True
  acc_of := fun _ _ _ _ _ _ _ => trivial
  cap_ns := by norm_num
  cap_d := by norm_num
  cap_m := by simp
  cap_H := by decide

instance : NeZero toy2.r := ⟨by show (1 : ℕ) ≠ 0; norm_num⟩

noncomputable def toy2R : PubRead toy2 where
  pub := fun _ => false
  ppt := fun _ => 5
  rd := fun _ => ()
  gen := 1
  hrd := fun _ _ _ => rfl
  hCpub := fun _ _ _ _ _ => rfl

/-- A trace satisfying each table on its own `H_t`: column `0` vanishes on `{1,16}`, column `1` on `{4}`. -/
noncomputable def tr2 : Fin 2 → (ZMod 17)[X] := ![(Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 16), Polynomial.X - Polynomial.C 4]

theorem toy2_compose (χ : Coins toy2.Φ0 (ZMod 17)) (M : toy2.Msg) (tr : Fin 2 → (ZMod 17)[X]) (i : Fin 2) :
    toy2.compose χ M tr i = (tr i) ^ 2 := by
  have : toy2.compose χ M tr i = MvPolynomial.aeval (R := ZMod 17)
      (fun p : Fin 2 × Fin 1 => (tr p.1).comp (Polynomial.C 1 * Polynomial.X))
      (MvPolynomial.X (i, 0) ^ 2 : MvPolynomial (Fin 2 × Fin 1) (ZMod 17)) := rfl
  rw [this]
  simp

/-- The RAW constraint of table `0` is NOT zero at `4 ∈ H ∖ H_0`: the multiplier is what makes it vanish on `H`. -/
theorem toy2_raw_fails (χ : Coins toy2.Φ0 (ZMod 17)) (M : toy2.Msg) :
    eval 4 (toy2.compose χ M tr2 (0 : Fin 2)) ≠ 0 := by
  rw [toy2_compose]
  simp only [tr2, eval_pow]
  simp
  decide

theorem toy2_raw_ok (χ : Coins toy2.Φ0 (ZMod 17)) (M : toy2.Msg) :
    ∀ i, ∀ x ∈ toy2.Ht (toy2.tabS i), eval x (toy2.compose χ M tr2 i) = 0 := by
  intro i x hx
  refine (congrArg (eval x) (toy2_compose χ M tr2 i)).trans ?_
  have h0 : tr2 (0 : Fin 2) = (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 16) := rfl
  have h1 : tr2 (1 : Fin 2) = Polynomial.X - Polynomial.C 4 := rfl
  fin_cases i
  · have hx' : x = 1 ∨ x = 16 := by simpa [toy2, Ht2] using hx
    show eval x (tr2 (0 : Fin 2) ^ 2) = 0
    rcases hx' with rfl | rfl <;> simp [h0]
  · have hx' : x = 4 := by simpa [toy2, Ht2] using hx
    show eval x (tr2 (1 : Fin 2) ^ 2) = 0
    subst hx'; simp [h1]

/-- ... and the multiplied constraint vanishes on the whole `H` (per-table semantics is in force). -/
theorem toy2_mult_vanishes (χ : Coins toy2.Φ0 (ZMod 17)) (M : toy2.Msg) (i : Fin 2) :
    ∀ x ∈ toy2.H, eval x (toy2.compose χ M tr2 i * Zout toy2.H (toy2.Ht (toy2.tabS i))) = 0 :=
  (vanish_iff _ _ (toy2.hHt _) _).2 (toy2_raw_ok χ M i)

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem toy2_hNH : friBound shp 1 ≤ toy2.H.card := by
  have : toy2.H.card = 3 := by decide
  rw [this]
  decide

theorem toy2_hpd : ∀ j c, toy2.pre j = some c → c.natDegree ≤ toy2.H.card := by
  intro j c h
  simp [toy2] at h

noncomputable def e2 : Fin (4 + 1) ≃ (Fin 2 × Fin toy2.r) ⊕
    Fin (deepParamsJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd).nq :=
  Fintype.equivOfCardEq (by
    show Fintype.card (Fin 5) = Fintype.card ((Fin 2 × Fin 1) ⊕ Fin 3)
    simp)

noncomputable abbrev toy2PJ := deepParamsJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd
noncomputable abbrev toy2AJ := airJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd
noncomputable abbrev toy2RJ := R0J toy2 toy2R domp (31 / 64) (friBound shp 1)
noncomputable abbrev toy2RtJ := RestJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd
noncomputable abbrev toy2RvJ := RestVJ toy2 toy2R domp (31 / 64) (friBound shp 1) toy2_hNH toy2_hpd

section Inst2
open BatchedFri.Spec BatchedFri.Spec.BatchingRound Fri.Spec
variable [DecidableEq (toy2PJ.statement toy2RJ toy2RtJ).M0] [Finite (toy2PJ.statement toy2RJ toy2RtJ).M0]
  [DecidableEq (NockvmE2E.Succ.FriDeep.friPlan (ω := domp) toy2PJ toy2AJ toy2RJ toy2RtJ toy2RvJ e2).Mfin]
  [Finite (NockvmE2E.Succ.FriDeep.friPlan (ω := domp) toy2PJ toy2AJ toy2RJ toy2RtJ toy2RvJ e2).Mfin]
  [∀ j, SampleableType ((pSpec 0 (ω := domp) shp 170).Challenge j)]

set_option linter.defProp false

/-- **The two-table witness instantiates the J-side arguments of `rap_fri_merkle_sound_deep_J`.** -/
noncomputable def toy2_e2e_J := rap_fri_merkle_sound_deep_J (ω := domp) (m := 4) toy2 toy2R shp 1 170 (31 / 64)
  toy2_hNH toy2_hpd e2

noncomputable def toy2_e2e_J_numbers :=
  rap_fri_merkle_sound_deep_J_numbers (ω := domp) (m := 4) toy2 toy2R shp 1 toy2_hNH toy2_hpd e2

end Inst2

end TwoTable

end Public

end NockvmE2E.J8.Toy
