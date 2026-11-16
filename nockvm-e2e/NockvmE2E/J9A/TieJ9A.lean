/-
the J-9 A twin of `J8/TieJ8.lean` + `J8/TieJ8G.lean`: the tie of each of the eight
tables of `consT9` (`J9A/InstJ9A.lean`) against the loaded chip's DAG values.  New: compute9 (twin compute, `permX9`), axis, split;
the five J-8 chips re-derived at `Ι9` from the J-8 generic lemmas (`nc_chip_tie`, `chk_*`, `decR_*`, `chals*_eq`).
-/
import NockvmE2E.J8.TieJ8
import NockvmE2E.J9A.InstJ9A
import NockvmE2E.Emit.ChipsJ9A
import NockvmE2E.Emit.ComputeX9
import NockvmE2E.Emit.TieR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.J9A.TieJ9A

open NockvmE2E.Emit Nock.Emit
open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open NockvmE2E.Exec NockvmE2E.Exec.DagSem
open NockvmE2E.J8.TieJ8
open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J8.InstJ8 (Φ0 truncP P)
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.TraceGenExe (powerBasis3 deltaF)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-- the `j`-th constraint of table `t` of `consT9` as a function of the valuation (`0` out of range) -/
noncomputable def consAt9 (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (t : Fin 8) (val : Ι9 × Fin 2 → KN) (j : ℕ) : KN :=
  if h : j < sz9 d t then MvPolynomial.aeval val (consT9 d χ M t ⟨j, h⟩) else 0

/-! ## 1. the generic non-compute tie (abstract constraint function) -/

theorem tie_nc' (C : ℕ → KN) (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) {ι : Type} (e : Fin (T.width 3) → ι) (val : ι × Fin 2 → KN) (chals pubs : ℕ → KN)
    (cKf : VarKind → ℕ → Bool) (cBf : VarKind → ℕ → Bool) (fc : ℕ → ℕ) (env : KEnv) (len : ℕ)
    (hcons : ∀ j, C j =
      Aof (evalA (mkEnvA e val (slotVal powerBasis3 T.baseCols chals) (slotVal powerBasis3 T.baseCols pubs)))
        (T.allGates powerBasis3) j)
    (hbc : env.bc = T.baseCols)
    (hcur : ∀ n (hn : n < T.width 3), env.cur n = val (e ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < T.width 3), env.next n = val (e ⟨n, hn⟩, 1))
    (hBc : ∀ n, cBf .challenge n = false)
    (hBt : ∀ n, cBf .traceCur n = true → n < T.width 3) (hBn : ∀ n, cBf .traceNext n = true → n < T.width 3)
    (hBp : ∀ n, cBf .publicVal n = false)
    (hKt : ∀ i, cKf .traceCur i = true → T.baseCols + 3 * i + 2 < T.width 3)
    (hKn : ∀ i, cKf .traceNext i = true → T.baseCols + 3 * i + 2 < T.width 3)
    (hKc : ∀ i, cKf .challenge i = true → chals i = env.chal (fc i))
    (hKp : ∀ i, cKf .publicVal i = true → pubs i = pubK env i)
    (okbase : ∀ g ∈ T.baseTransition, okB cBf g = true) (okmix : ∀ E ∈ T.mixedTransition, okM cKf cBf E = true) :
    ∀ ℓ < (ncRoute T.baseTransition.length T.mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute T.baseTransition.length T.mixedTransition.length).mult ℓ),
        cf k * C ((ncRoute T.baseTransition.length T.mixedTransition.length).jOf ℓ k) =
      Vof (tplVals env fc id id T.baseTransition T.mixedTransition) ℓ := by
  intro ℓ hℓ
  simp only [hcons]
  exact nc_chip_tie T hext hd1 hd3 heq e val chals pubs cKf cBf fc env len hbc hcur hnext hBc hBt hBn hBp hKt hKn hKc hKp
    okbase okmix ℓ hℓ

/-! ## 2. axis and split: templates, column maps, constraints as `Aof` -/

abbrev tAxis : ChipTemplate Gl := Nock.Emit.axisTemplate
abbrev tSplit (nA : ℕ) : ChipTemplate Gl := Nock.Emit.splitTemplateAt nA

theorem w_axis : tAxis.width 3 = 52 := by decide +kernel
theorem w_split (nA : ℕ) : (tSplit nA).width 3 = 90 := by
  show (Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.splitTemplateJ9 Nock.Emit.δ nA).width 3 = 90
  rfl
theorem bc_axis : tAxis.baseCols = 22 := by decide +kernel
theorem bc_split (nA : ℕ) : (tSplit nA).baseCols = 72 := rfl

def eAxis (j : Fin (tAxis.width 3)) : Ι9 := iX (Fin.cast w_axis j)
def eSplit (nA : ℕ) (j : Fin ((tSplit nA).width 3)) : Ι9 := iS (Fin.cast (w_split nA) j)

theorem consAt9_axis (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 6 val j = Aof (evalA (mkEnvA eAxis val (slotVal powerBasis3 22 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 22 M.1.pubsX))) (tAxis.allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 6
  · have h' : j < (tAxis.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((tAxis.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eAxis val _ _ _
  · have h' : ¬ j < (tAxis.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt9_split (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 7 val j = Aof (evalA (mkEnvA (eSplit d.Pb.nA) val (slotVal powerBasis3 72 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 72 M.1.pubsS))) ((tSplit d.Pb.nA).allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 7
  · have h' : j < ((tSplit d.Pb.nA).allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ (((tSplit d.Pb.nA).allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (eSplit d.Pb.nA) val _ _ _
  · have h' : ¬ j < ((tSplit d.Pb.nA).allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

/-! ## 3. leaf checks (kernel) -/

theorem chk_axis : chkT tAxis 4 chalM = true := by decide +kernel
theorem chk_split : ∀ nA ∈ [1, 2], chkT (tSplit nA) 2 chalM = true := by decide +kernel

/-! ## 4. the compute9 table -/

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (permX9 gatesHX9 gatesHX9P baseGatesFX9 walkGatesFX9 arithGatesX9 eqGatesX9
  slotPairsX9 accGatesHX9 baseGatesHX9 widthHX9 renC)
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (col0Id)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (mapC)

noncomputable def cArith9 : List (CoeffExpr Gl) := (arithGatesX9).map (mapC (fun q : ℚ => (q : Gl)))
noncomputable def cEq9 : List (CoeffExpr Gl) :=
  ((eqGatesX9 (F := ℚ)).map ChipH.EqG.gate).map (mapC (fun q : ℚ => (q : Gl)))
noncomputable def cAcc9 : List (MixedExpr Gl) := Nock.Emit.accKGatesHX9
noncomputable def cSlot9 : List (MixedExpr Gl) := Nock.Emit.slotPairsFlat9

theorem accGatesHX9_cast :
    (accGatesHX9 (F := Gl)) = (accGatesHX9 (F := ℚ)).map (mapC (fun q : ℚ => (q : Gl))) := by
  decide +kernel

theorem accGatesHX9_semA {K : Type} [Field K] [Algebra Gl K] (b : Module.Basis (Fin 3) Gl K) (eA : Env K) :
    ((accGatesHX9 (F := Gl)).map (evalA eA)) =
      (((Nock.Emit.accKGatesHX9).flatMap fun g => List.ofFn (mixedCompile b col0Id g)).map (evalA eA)) := by
  simp only [accGatesHX9, Nock.Emit.accKGatesHX9, ChipHX9.accOf9, Nock.Emit.accKOf9, List.flatMap_append, List.map_append,
    NockvmE2E.Emit.accGatesX_semA b _ _ _ eA]

theorem gatesHX9_eq : gatesHX9 powerBasis3 Nock.Emit.δ =
    cArith9 ++ accGatesHX9 (F := Gl) ++ cEq9 ++ Kflat col0Id (cSlot9 ++ walkGatesFX9) := by
  have hq : ∀ q : MixedExpr Gl × MixedExpr Gl,
      Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates powerBasis3 q = Kflat col0Id [q.1, q.2] := by
    intro q; simp [Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates, Kflat]
  have hq' : Nock.NockVMROM.Thm54.VclL.Compute.TowerD.qGates powerBasis3 = fun q => Kflat col0Id [q.1, q.2] := funext hq
  simp only [gatesHX9, baseGatesFX9, baseGatesHX9, hq', Kflat, cSlot9, Nock.Emit.slotPairsFlat9, List.flatMap_append,
    List.flatMap_assoc, cArith9, cEq9, accGatesHX9_cast, List.map_append, List.append_assoc]

/-- compute9 leaf conditions (twin columns `< 137`; the `𝕂`-roles are the J-8 ones) -/
def cBc9 : VarKind → ℕ → Bool
  | .traceCur, n => decide (n < 137)
  | .traceNext, n => decide (n < 137)
  | .publicVal, n => decide (n < 33)
  | .challenge, _ => false

theorem chk_compute9 :
    ((cArith9 ++ cEq9).all (okB cBc9) && (cAcc9 ++ (cSlot9 ++ walkGatesFX9)).all (okM cKc cBc9)) = true := by
  decide +kernel

theorem permX9_lt191 (n : ℕ) (h : n < 191) : permX9 n < 137 := by
  unfold permX9; split_ifs <;> omega

/-- the twin environment: the document environment read through `permX9`, `𝕂`-columns at `69` -/
def envT (env : KEnv) : KEnv := {env with cur := fun n => env.cur (permX9 n), next := fun n => env.next (permX9 n), bc := 69}

theorem evB_renC (env : KEnv) : ∀ g : CoeffExpr Gl, evB env (renC permX9 g) = evB (envT env) g
  | .const c => rfl
  | .var .traceCur i => rfl
  | .var .traceNext i => rfl
  | .var .challenge i => rfl
  | .var .publicVal i => rfl
  | .add a b => by simp only [renC, evB, evB_renC env a, evB_renC env b]
  | .sub a b => by simp only [renC, evB, evB_renC env a, evB_renC env b]
  | .mul a b => by simp only [renC, evB, evB_renC env a, evB_renC env b]
  | .neg a => by simp only [renC, evB, evB_renC env a]
  | .pow a n => by simp only [renC, evB, evB_renC env a]

theorem extK_perm (a : ℕ → NockvmE2E.Exec.KC) (s : ℕ) (hs : s ≤ 17) :
    extK a 83 s = extK (fun n => a (permX9 n)) 69 s := by
  have h0 : permX9 (69 + 3 * s) = 83 + 3 * s := by unfold permX9; split_ifs <;> omega
  have h1 : permX9 (69 + 3 * s + 1) = 83 + 3 * s + 1 := by unfold permX9; split_ifs <;> omega
  have h2 : permX9 (69 + 3 * s + 2) = 83 + 3 * s + 2 := by unfold permX9; split_ifs <;> omega
  unfold extK
  beta_reduce
  rw [h0, h1, h2]

theorem evM_perm (env : KEnv) (hbc : env.bc = 83) (fc fp : ℕ → ℕ) : ∀ E : MixedExpr Gl, okM cKc cBc9 E = true →
    evM env (renameM fc Nock.Emit.feX9 fp (Nock.Emit.renBaseM E)) = evM (envT env) (renameM fc Nock.Emit.feX fp E)
  | .Var .traceCur i, h => by
    simp only [okM, cKc, decide_eq_true_eq] at h
    have e1 : Nock.Emit.feX9 i = Nock.Emit.feX i := by
      simp only [Nock.Emit.feX9, Nock.Emit.feX]; split_ifs <;> omega
    have e2 : Nock.Emit.feX i = (i - 69) / 3 := by simp only [Nock.Emit.feX]; split_ifs <;> omega
    simp only [Nock.Emit.renBaseM, renameM, evM, e1, hbc, envT]
    rw [extK_perm _ _ (by omega)]
  | .Var .traceNext i, h => by
    simp only [okM, cKc, decide_eq_true_eq] at h
    have e1 : Nock.Emit.feX9 i = Nock.Emit.feX i := by
      simp only [Nock.Emit.feX9, Nock.Emit.feX]; split_ifs <;> omega
    have e2 : Nock.Emit.feX i = (i - 69) / 3 := by simp only [Nock.Emit.feX]; split_ifs <;> omega
    simp only [Nock.Emit.renBaseM, renameM, evM, e1, hbc, envT]
    rw [extK_perm _ _ (by omega)]
  | .Var .challenge i, h => by simp only [Nock.Emit.renBaseM, renameM, evM, envT]
  | .Var .publicVal i, h => by simp only [Nock.Emit.renBaseM, renameM, evM, envT, pubK]
  | .Lift g, h => by simp only [Nock.Emit.renBaseM, renameM, evM, evB_renC]
  | .Scale g u, h => by
    simp only [okM, Bool.and_eq_true] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evB_renC, evM_perm env hbc fc fp u h.2]
  | .Const c, h => by simp only [Nock.Emit.renBaseM, renameM, evM]
  | .Add x y, h => by
    simp only [okM, Bool.and_eq_true] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evM_perm env hbc fc fp x h.1, evM_perm env hbc fc fp y h.2]
  | .Sub x y, h => by
    simp only [okM, Bool.and_eq_true] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evM_perm env hbc fc fp x h.1, evM_perm env hbc fc fp y h.2]
  | .Neg x, h => by
    simp only [okM] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evM_perm env hbc fc fp x h]
  | .Mul x y, h => by
    simp only [okM, Bool.and_eq_true] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evM_perm env hbc fc fp x h.1, evM_perm env hbc fc fp y h.2]
  | .Pow x n, h => by
    simp only [okM] at h
    simp only [Nock.Emit.renBaseM, renameM, evM, evM_perm env hbc fc fp x h]

/-! ### the constraint of table 0 as `Aof` over the twin gate list -/

def eC9 : Fin 137 → Ι9 := fun j => iC j
def eT9 : Fin 191 → Ι9 := fun n => iC ⟨permX9 n % 137, Nat.mod_lt _ (by norm_num)⟩

theorem eT9_eq (n : ℕ) (hn : n < 191) : eT9 ⟨n, hn⟩ = iC ⟨permX9 n, permX9_lt191 n hn⟩ :=
  congrArg iC (Fin.ext (Nat.mod_eq_of_lt (permX9_lt191 n hn)))

theorem mk_tr (val : Ι9 × Fin 2 → KN) (cv pv : ℕ → ZMod P) (i : ℕ) :
    (mkEnvA eC9 val cv pv).trace (permX9 i) = (mkEnvA eT9 val cv pv).trace i ∧
    (mkEnvA eC9 val cv pv).traceNext (permX9 i) = (mkEnvA eT9 val cv pv).traceNext i := by
  by_cases h : i < 191
  · have h1 := permX9_lt191 i h
    simp only [mkEnvA, dif_pos h, dif_pos h1, eC9, eT9]
    have : permX9 i % 137 = permX9 i := Nat.mod_eq_of_lt h1
    constructor <;> congr 3 <;> exact Fin.ext this.symm
  · have h1 : ¬ permX9 i < 137 := by unfold permX9; split_ifs <;> omega
    constructor <;> simp [mkEnvA, h, h1]

theorem evalA_renC_mk (val : Ι9 × Fin 2 → KN) (cv pv : ℕ → ZMod P) :
    ∀ g : CoeffExpr Gl, evalA (mkEnvA eC9 val cv pv) (renC permX9 g) = evalA (mkEnvA eT9 val cv pv) g
  | .const c => rfl
  | .var .traceCur i => (mk_tr val cv pv i).1
  | .var .traceNext i => (mk_tr val cv pv i).2
  | .var .challenge i => rfl
  | .var .publicVal i => rfl
  | .add a b => by simp only [renC, evalA, evalA_renC_mk val cv pv a, evalA_renC_mk val cv pv b]
  | .sub a b => by simp only [renC, evalA, evalA_renC_mk val cv pv a, evalA_renC_mk val cv pv b]
  | .mul a b => by simp only [renC, evalA, evalA_renC_mk val cv pv a, evalA_renC_mk val cv pv b]
  | .neg a => by simp only [renC, evalA, evalA_renC_mk val cv pv a]
  | .pow a n => by simp only [renC, evalA, evalA_renC_mk val cv pv a]

theorem Aof_map_renC (val : Ι9 × Fin 2 → KN) (cv pv : ℕ → ZMod P) (L : List (CoeffExpr Gl)) (j : ℕ) :
    Aof (evalA (mkEnvA eC9 val cv pv)) (L.map (renC permX9)) j = Aof (evalA (mkEnvA eT9 val cv pv)) L j := by
  unfold Aof
  rw [List.getElem?_map]
  cases L[j]? with
  | none => rfl
  | some g => exact evalA_renC_mk val cv pv g

theorem consAt9_comp (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 0 val j = Aof (evalA (mkEnvA eT9 val (chalVJ8 powerBasis3 χ) (NockvmE2E.J8.InstJ8.xpF M.2)))
      (cArith9 ++ accGatesHX9 (F := Gl) ++ cEq9 ++ Kflat col0Id (cSlot9 ++ walkGatesFX9)) j := by
  rw [← gatesHX9_eq, ← Aof_map_renC]
  change _ = Aof _ (gatesHX9P powerBasis3 deltaF) j
  unfold consAt9 Aof
  by_cases h : j < sz9 d 0
  · have h' : j < (gatesHX9P powerBasis3 deltaF).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((gatesHX9P powerBasis3 deltaF).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (w := 137) eC9 val _ _ _
  · have h' : ¬ j < (gatesHX9P powerBasis3 deltaF).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]


theorem acc9_len : (accGatesHX9 (F := Gl)).length = 3 * cAcc9.length := by decide +kernel

/-- the DAG value list of the compute9 chip, at the twin environment -/
noncomputable def compVals9 (env : KEnv) : List NockvmE2E.Exec.KC :=
  cArith9.map (evB (envT env)) ++ cEq9.map (evB (envT env)) ++
    cAcc9.map (fun E => evM (envT env) (Nock.Emit.norm (renameM Nock.Emit.fX Nock.Emit.feX Nock.Emit.fpX E))) ++
    (cSlot9 ++ walkGatesFX9).map (fun E => evM (envT env) (Nock.Emit.norm (renameM Nock.Emit.fX Nock.Emit.feX Nock.Emit.fpX E)))

theorem dagVals_comp9 (env : KEnv) (hbc : env.bc = 83) :
    dagVals Nock.Emit.computeSpec9.gates env = compVals9 env := by
  have hok := chk_compute9
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have hbase : Nock.Emit.computeSpec9_0.base = (cArith9 ++ cEq9).map (renC permX9) := by
    simp [Nock.Emit.computeSpec9_0, cArith9, cEq9, List.map_append]
  have hmix : Nock.Emit.computeSpec9_0.mixed = (cAcc9 ++ (cSlot9 ++ walkGatesFX9)).map Nock.Emit.renBaseM := by
    simp [Nock.Emit.computeSpec9_0, cAcc9, cSlot9, List.append_assoc]
  have hm : ∀ L : List (MixedExpr Gl), (∀ E ∈ L, okM cKc cBc9 E = true) →
      (((L.map Nock.Emit.renBaseM).map (renameM Nock.Emit.fX Nock.Emit.feX9 Nock.Emit.fpX)).map Nock.Emit.norm).map (evM env) =
        L.map (fun E => evM (envT env) (Nock.Emit.norm (renameM Nock.Emit.fX Nock.Emit.feX Nock.Emit.fpX E))) := by
    intro L hL
    simp only [List.map_map]
    refine List.map_congr_left fun E hE => ?_
    simp only [Function.comp_apply]
    rw [evM_norm, evM_perm env hbc _ _ E (hL E hE), evM_norm]
  have hL : (∀ E ∈ cAcc9 ++ (cSlot9 ++ walkGatesFX9), okM cKc cBc9 E = true) := hok.2
  have hmm := hm _ hL
  simp only [List.map_append] at hmm
  simp only [dagVals, Nock.Emit.computeSpec9, Nock.Emit.TSpec.gates, Nock.Emit.TSpec.rename, hbase, hmix, compVals9]
  have hb : ((cArith9 ++ cEq9).map (renC permX9)).map (evB env) = (cArith9 ++ cEq9).map (evB (envT env)) := by
    simp only [List.map_map, Function.comp_def, evB_renC]
  have hmm' : ((((cAcc9 ++ (cSlot9 ++ walkGatesFX9)).map Nock.Emit.renBaseM).map
      (renameM Nock.Emit.fX Nock.Emit.feX9 Nock.Emit.fpX)).map Nock.Emit.norm).map (evM env) = _ := hm _ hL
  simp only [List.map_append] at hb hmm' ⊢
  simp only [Nock.Emit.computeSpec9_0, List.map_nil, List.append_nil, List.nil_append] at *
  rw [hb, hmm']
  simp [List.append_assoc]

/-- **the compute9 table** (the twin environment: `permX9`-read, `𝕂`-columns at 69; the document's `𝕂`-columns at 83) -/
theorem tie_comp9 (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (env : KEnv)
    (hbc : env.bc = 83)
    (hcur : ∀ n (hn : n < 137), env.cur n = val (iC ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < 137), env.next n = val (iC ⟨n, hn⟩, 1))
    (hE : SlotOK env.chal (χf χ)) (hpub : ∀ s < 33, NockvmE2E.J8.InstJ8.xpF M.2 s = env.pub s) :
    ∀ ℓ < (cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).nK,
      ∑ k ∈ Finset.range ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).mult ℓ),
        cf k * consAt9 d χ M 0 val ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).jOf ℓ k) = Vof (compVals9 env) ℓ := by
  intro ℓ hℓ
  have hok := chk_compute9
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have e1 : ∑ k ∈ Finset.range ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).mult ℓ),
        cf k * consAt9 d χ M 0 val ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).jOf ℓ k)
      = ∑ k ∈ Finset.range ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).mult ℓ),
        cf k * Aof (evalA (mkEnvA eT9 val (chalVJ8 powerBasis3 χ) (NockvmE2E.J8.InstJ8.xpF M.2)))
          (cArith9 ++ accGatesHX9 (F := Gl) ++ cEq9 ++ Kflat col0Id (cSlot9 ++ walkGatesFX9))
          ((cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).jOf ℓ k) :=
    Finset.sum_congr rfl (fun k _ => by rw [consAt9_comp])
  rw [e1]
  have hbc' : (envT env).bc = 69 := rfl
  have hacc : (accGatesHX9 (F := Gl)).map (evalA (mkEnvA eT9 val (chalVJ8 powerBasis3 χ) (NockvmE2E.J8.InstJ8.xpF M.2))) =
      (Kflat col0Id cAcc9).map (evalA (mkEnvA eT9 val (chalVJ8 powerBasis3 χ) (NockvmE2E.J8.InstJ8.xpF M.2))) :=
    accGatesHX9_semA powerBasis3 _
  have := c_chip_tie col0Id (w := 191) eT9 val (chalVJ8 powerBasis3 χ) (NockvmE2E.J8.InstJ8.xpF M.2) cKc cBc9 Nock.Emit.fX
        Nock.Emit.feX Nock.Emit.fpX (envT env) cArith9 cEq9 (accGatesHX9 (F := Gl)) cAcc9
        (cSlot9 ++ walkGatesFX9)
        (fun n hn => by
          show env.cur (permX9 n) = _
          rw [hcur _ (permX9_lt191 n hn)]
          rw [eT9_eq n hn])
        (fun n hn => by
          show env.next (permX9 n) = _
          rw [hnext _ (permX9_lt191 n hn)]
          rw [eT9_eq n hn])
        (fun n => rfl)
        (fun n hn => by have : n < 137 := by simpa [cBc9] using hn
                        omega)
        (fun n hn => by have : n < 137 := by simpa [cBc9] using hn
                        omega)
        (fun n hn => by
          have : n < 33 := by simpa [cBc9] using hn
          rw [hpub n this]; rfl)
        (fun i hi => by
          simp only [cKc, decide_eq_true_eq] at hi
          simp only [col0Id, Nock.Emit.feX, hbc', if_pos hi.1]
          omega)
        (fun i hi => by
          simp only [cKc, decide_eq_true_eq] at hi
          simp only [col0Id, Nock.Emit.feX, hbc', if_pos hi.1]
          omega)
        (fun r hr => by
          simp only [cKc, decide_eq_true_eq] at hr
          exact comp_chal χ env.chal hE r hr.1 hr.2)
        (fun r hr => by
          simp only [cKc, decide_eq_true_eq] at hr
          exact sum_pub3 (envT env) (NockvmE2E.J8.InstJ8.xpF M.2) hpub r hr.1 hr.2)
        hok.1 hok.2 hacc ℓ hℓ
  exact this

/-! ## 5. the five J-8 chips at `Ι9` -/

abbrev tWalkJ8' (k : ℕ) : ChipTemplate Gl := tWalkJ8 k

def eCell9 (j : Fin (Nock.Emit.cellKWTemplate.width 3)) : Ι9 := iM (Fin.cast (by decide) j)
def eWalk9 (k : ℕ) (j : Fin ((tWalkJ8 k).width 3)) : Ι9 := iW (Fin.cast rfl j)
def eJet9 (j : Fin (Nock.Emit.jetTemplate.width 3)) : Ι9 := iJ (Fin.cast (by decide) j)
def eAtom9 (j : Fin (Nock.Emit.atomTemplate.width 3)) : Ι9 := iA (Fin.cast (by decide) j)
def eWalkV9 (k : ℕ) (j : Fin ((tWalkV k).width 3)) : Ι9 := iV (Fin.cast rfl j)

theorem consAt9_cell (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 1 val j = Aof (evalA (mkEnvA eCell9 val (slotVal powerBasis3 134 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 134 M.1.pubsC))) (Nock.Emit.cellKWTemplate.allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 1
  · have h' : j < (Nock.Emit.cellKWTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.cellKWTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eCell9 val _ _ _
  · have h' : ¬ j < (Nock.Emit.cellKWTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt9_walk (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 2 val j = Aof (evalA (mkEnvA (eWalk9 d.Pb.kroots) val (slotVal powerBasis3 25 (chalsMJ8 deltaF χ))
      (slotVal powerBasis3 25 M.1.pubsW))) ((tWalkJ8 d.Pb.kroots).allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 2
  · have h' : j < ((tWalkJ8 d.Pb.kroots).allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ (((tWalkJ8 d.Pb.kroots).allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (eWalk9 d.Pb.kroots) val _ _ _
  · have h' : ¬ j < ((tWalkJ8 d.Pb.kroots).allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt9_jet (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 3 val j = Aof (evalA (mkEnvA eJet9 val (slotVal powerBasis3 29 (chalsJJ8 χ))
      (slotVal powerBasis3 29 M.1.pubsJ))) (Nock.Emit.jetTemplate.allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 3
  · have h' : j < (Nock.Emit.jetTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.jetTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eJet9 val _ _ _
  · have h' : ¬ j < (Nock.Emit.jetTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt9_atom (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 4 val j = Aof (evalA (mkEnvA eAtom9 val (slotVal powerBasis3 205 (chalsAJ8Z deltaF χ))
      (slotVal powerBasis3 205 M.1.pubsA))) (Nock.Emit.atomTemplate.allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 4
  · have h' : j < (Nock.Emit.atomTemplate.allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ ((Nock.Emit.atomTemplate.allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv eAtom9 val _ _ _
  · have h' : ¬ j < (Nock.Emit.atomTemplate.allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

theorem consAt9_walkV (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (j : ℕ) :
    consAt9 d χ M 5 val j = Aof (evalA (mkEnvA (eWalkV9 d.Pb.krootsV) val (slotVal powerBasis3 25 (chalsAJ8Z deltaF χ))
      (slotVal powerBasis3 25 M.1.pubsV))) ((tWalkV d.Pb.krootsV).allGates powerBasis3) j := by
  unfold consAt9 Aof
  by_cases h : j < sz9 d 5
  · have h' : j < ((tWalkV d.Pb.krootsV).allGates powerBasis3).length := h
    rw [dif_pos h, List.getElem?_eq_getElem h']
    show MvPolynomial.aeval val (truncP _ (coeffToMv _ _ (((tWalkV d.Pb.krootsV).allGates powerBasis3).get ⟨j, h'⟩))) = _
    exact aeval_trunc_coeffToMv (eWalkV9 d.Pb.krootsV) val _ _ _
  · have h' : ¬ j < ((tWalkV d.Pb.krootsV).allGates powerBasis3).length := h
    rw [dif_neg h, List.getElem?_eq_none (by omega)]

/-! ## 6. the document decodes (kernel) -/

theorem decR_compute9 : decodeDagR Nock.Emit.emit_compute9 = some Nock.Emit.computeSpec9.gates := by decide +kernel
theorem decR_axis : decodeDagR Nock.Emit.emit_axis = some Nock.Emit.axisSpec.gates := by decide +kernel
theorem decR_split_at : ∀ nA ∈ [1, 2],
    decodeDagR (Nock.Emit.emit_splitAt nA) = some (Nock.Emit.splitSpecAt nA).gates := by decide +kernel

/-! ## 7. against the loaded chip -/

theorem tieD_gen (ch : NockvmE2E.Exec.Tr.Chip) (D : DagGates) (g : DGatesDec) (hdec : decodeDagL D = some g)
    (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (hop : HopZero ch D ders cmeta ch.baseCols) (env : KEnv)
    (V : List NockvmE2E.Exec.KC) (hV : dagVals g (envE ders cmeta env) = V) (nK : ℕ) (hlen : V.length = nK) (S : ℕ → KN)
    (hS : ∀ ℓ < nK, S ℓ = Vof V ℓ) : ∀ ℓ < nK, S ℓ = (evalDagK ch env)[ℓ]! := by
  intro ℓ hℓ
  have hv := evalDagK_hop ch D g hdec ders cmeta hop env
  have hv' : (evalDagK ch env).toList = V := hv.trans hV
  rw [dag_get ch env V hv' ℓ (by omega)]
  exact hS ℓ hℓ

section TieD9
variable (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN)
  (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip)

theorem tieD9_comp (hop : HopZero ch Nock.Emit.emit_compute9 ders cmeta ch.baseCols) (hbc : env.bc = 83)
    (hcur : ∀ n (hn : n < 137), env.cur n = val (iC ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < 137), env.next n = val (iC ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ))
    (hpub : ∀ s < 33, NockvmE2E.J8.InstJ8.xpF M.2 s = env.pub s) :
    ∀ ℓ < (cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).nK,
      ∑ k ∈ Finset.range ((cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).mult ℓ),
        cf k * consAt9 d χ M 0 val ((cRoute cArith9.length cEq9.length cAcc9.length
          (cSlot9 ++ walkGatesFX9).length).jOf ℓ k) = (evalDagK ch env)[ℓ]! := by
  refine tieD_gen ch _ _ (decL_of_decR decR_compute9) ders cmeta hop env _ (dagVals_comp9 (envE ders cmeta env) hbc) _ ?_ _ ?_
  · simp only [compVals9, cRoute, List.length_append, List.length_map]
  · exact tie_comp9 d χ M val (envE ders cmeta env) hbc hcur hnext hE hpub

theorem tieD9_cell (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (Nock.Emit.emit_cellKW) ders cmeta ch.baseCols)
    (hbc : env.bc = 134)
    (hcur : ∀ n (hn : n < (Nock.Emit.cellKWTemplate).width 3), env.cur n = val (eCell9 ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (Nock.Emit.cellKWTemplate).width 3), env.next n = val (eCell9 ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 6, M.1.pubsC i = pubK env i) :
    ∀ ℓ < (ncRoute (Nock.Emit.cellKWTemplate).baseTransition.length (Nock.Emit.cellKWTemplate).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (Nock.Emit.cellKWTemplate).baseTransition.length (Nock.Emit.cellKWTemplate).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 1 val ((ncRoute (Nock.Emit.cellKWTemplate).baseTransition.length (Nock.Emit.cellKWTemplate).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_cell)
  refine tieD_gen ch _ _ (decL_of_decR NockvmE2E.Emit.decR_cellKW) ders cmeta hop env _
    (by rw [show (Nock.Emit.cellKWSpec).gates = ((TSpec.ofTemplate (Nock.Emit.cellKWTemplate)).rename Nock.Emit.fM id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 1 val) (Nock.Emit.cellKWTemplate) rfl rfl rfl rfl eCell9 val (chalsMJ8 deltaF χ) (M.1.pubsC)
    (cKmem (Nock.Emit.cellKWTemplate).baseCols ((Nock.Emit.cellKWTemplate).width 3) 6 chalM)
    (cBmem ((Nock.Emit.cellKWTemplate).width 3)) Nock.Emit.fM (envE ders cmeta env) 6 (fun j => by rw [bc_cell]; exact consAt9_cell d χ M val j)
    (by show env.bc = _; rw [bc_cell]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      exact (chalsM_eq χ i hi').trans (fM_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

theorem tieD9_jet (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (Nock.Emit.emit_jet) ders cmeta ch.baseCols)
    (hbc : env.bc = 29)
    (hcur : ∀ n (hn : n < (Nock.Emit.jetTemplate).width 3), env.cur n = val (eJet9 ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (Nock.Emit.jetTemplate).width 3), env.next n = val (eJet9 ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 4, M.1.pubsJ i = pubK env i) :
    ∀ ℓ < (ncRoute (Nock.Emit.jetTemplate).baseTransition.length (Nock.Emit.jetTemplate).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (Nock.Emit.jetTemplate).baseTransition.length (Nock.Emit.jetTemplate).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 3 val ((ncRoute (Nock.Emit.jetTemplate).baseTransition.length (Nock.Emit.jetTemplate).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_jet)
  refine tieD_gen ch _ _ (decL_of_decR NockvmE2E.Emit.decR_jet) ders cmeta hop env _
    (by rw [show (Nock.Emit.jetSpec).gates = ((TSpec.ofTemplate (Nock.Emit.jetTemplate)).rename Nock.Emit.fJ id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 3 val) (Nock.Emit.jetTemplate) rfl rfl rfl rfl eJet9 val (chalsJJ8 χ) (M.1.pubsJ)
    (cKmem (Nock.Emit.jetTemplate).baseCols ((Nock.Emit.jetTemplate).width 3) 4 chalJ)
    (cBmem ((Nock.Emit.jetTemplate).width 3)) Nock.Emit.fJ (envE ders cmeta env) 4 (fun j => by rw [bc_jet]; exact consAt9_jet d χ M val j)
    (by show env.bc = _; rw [bc_jet]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i < 8 := by simpa [cKmem, chalJ] using hi
      exact (chalsJ_eq χ i hi').trans (fJ_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

theorem tieD9_atom (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (Nock.Emit.emit_atom) ders cmeta ch.baseCols)
    (hbc : env.bc = 205)
    (hcur : ∀ n (hn : n < (Nock.Emit.atomTemplate).width 3), env.cur n = val (eAtom9 ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (Nock.Emit.atomTemplate).width 3), env.next n = val (eAtom9 ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 12, M.1.pubsA i = pubK env i) :
    ∀ ℓ < (ncRoute (Nock.Emit.atomTemplate).baseTransition.length (Nock.Emit.atomTemplate).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (Nock.Emit.atomTemplate).baseTransition.length (Nock.Emit.atomTemplate).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 4 val ((ncRoute (Nock.Emit.atomTemplate).baseTransition.length (Nock.Emit.atomTemplate).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_atom)
  refine tieD_gen ch _ _ (decL_of_decR NockvmE2E.Emit.decR_atom) ders cmeta hop env _
    (by rw [show (Nock.Emit.atomSpec).gates = ((TSpec.ofTemplate (Nock.Emit.atomTemplate)).rename Nock.Emit.fA id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 4 val) (Nock.Emit.atomTemplate) rfl rfl rfl rfl eAtom9 val (chalsAJ8Z deltaF χ) (M.1.pubsA)
    (cKmem (Nock.Emit.atomTemplate).baseCols ((Nock.Emit.atomTemplate).width 3) 12 chalA)
    (cBmem ((Nock.Emit.atomTemplate).width 3)) Nock.Emit.fA (envE ders cmeta env) 12 (fun j => by rw [bc_atom]; exact consAt9_atom d χ M val j)
    (by show env.bc = _; rw [bc_atom]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 38 := by simpa [cKmem, chalA] using hi
      exact (chalsA_eq χ i hi').trans (fA_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

theorem tieD9_axis (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (Nock.Emit.emit_axis) ders cmeta ch.baseCols)
    (hbc : env.bc = 22)
    (hcur : ∀ n (hn : n < (tAxis).width 3), env.cur n = val (eAxis ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tAxis).width 3), env.next n = val (eAxis ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 4, M.1.pubsX i = pubK env i) :
    ∀ ℓ < (ncRoute (tAxis).baseTransition.length (tAxis).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tAxis).baseTransition.length (tAxis).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 6 val ((ncRoute (tAxis).baseTransition.length (tAxis).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_axis)
  refine tieD_gen ch _ _ (decL_of_decR decR_axis) ders cmeta hop env _
    (by rw [show (Nock.Emit.axisSpec).gates = ((TSpec.ofTemplate (tAxis)).rename Nock.Emit.fM id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 6 val) (tAxis) rfl rfl rfl rfl eAxis val (chalsMJ8 deltaF χ) (M.1.pubsX)
    (cKmem (tAxis).baseCols ((tAxis).width 3) 4 chalM)
    (cBmem ((tAxis).width 3)) Nock.Emit.fM (envE ders cmeta env) 4 (fun j => by rw [bc_axis]; exact consAt9_axis d χ M val j)
    (by show env.bc = _; rw [bc_axis]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      exact (chalsM_eq χ i hi').trans (fM_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

/-- the walkJ8 numerals the J-9 A family has literals for: the J-8 six plus kroots = 3 (nockvm's toy dump; `chipWalkJ8_3`) -/
def walkKs9 : List ℕ := [1, 9, 25, 42, 48, 174, 3]

theorem walkKs9_cases {k : ℕ} (hk : k ∈ walkKs9) : k = 3 ∨ k ∈ [1, 9, 25, 42, 48, 174] := by
  simp only [walkKs9, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk ⊢
  omega

theorem decR_walkJ8_at9 : ∀ k ∈ walkKs9,
    decodeDagR (emitDag (Nock.Emit.walkJ8SpecAt k)) = some (Nock.Emit.walkJ8SpecAt k).gates := by
  intro k hk
  rcases walkKs9_cases hk with rfl | h
  · decide +kernel
  · exact decR_walkJ8_at k h

theorem chk_walkJ8_9 : ∀ k ∈ walkKs9,
    chkT (Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.walkTemplateJ8 Nock.Emit.δ k) 8 chalM = true := by
  intro k hk
  rcases walkKs9_cases hk with rfl | h
  · decide +kernel
  · exact chk_walkJ8 k h

theorem tieD9_walk (ch : NockvmE2E.Exec.Tr.Chip) (hk : d.Pb.kroots ∈ walkKs9)
    (hop : HopZero ch (emitDag (Nock.Emit.walkJ8SpecAt d.Pb.kroots)) ders cmeta ch.baseCols)
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.cur n = val (eWalk9 d.Pb.kroots ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkJ8 d.Pb.kroots).width 3), env.next n = val (eWalk9 d.Pb.kroots ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 8, M.1.pubsW i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 2 val ((ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_walkJ8_9 d.Pb.kroots hk)
  refine tieD_gen ch _ _ (decL_of_decR (decR_walkJ8_at9 _ hk)) ders cmeta hop env _
    (by rw [show (Nock.Emit.walkJ8SpecAt d.Pb.kroots).gates = ((TSpec.ofTemplate (tWalkJ8 d.Pb.kroots)).rename Nock.Emit.fM id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 2 val) (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl (eWalk9 d.Pb.kroots) val (chalsMJ8 deltaF χ) (M.1.pubsW)
    (cKmem (tWalkJ8 d.Pb.kroots).baseCols ((tWalkJ8 d.Pb.kroots).width 3) 8 chalM)
    (cBmem ((tWalkJ8 d.Pb.kroots).width 3)) Nock.Emit.fM (envE ders cmeta env) 8 (fun j => by rw [bc_walkJ8 d.Pb.kroots]; exact consAt9_walk d χ M val j)
    (by show env.bc = _; rw [bc_walkJ8 d.Pb.kroots]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      exact (chalsM_eq χ i hi').trans (fM_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

theorem tieD9_walkV (ch : NockvmE2E.Exec.Tr.Chip) (hk : d.Pb.krootsV ∈ [1, 2])
    (hop : HopZero ch (emitDag (Nock.Emit.walkAtomSpecAt d.Pb.krootsV)) ders cmeta ch.baseCols)
    (hbc : env.bc = 25)
    (hcur : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.cur n = val (eWalkV9 d.Pb.krootsV ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tWalkV d.Pb.krootsV).width 3), env.next n = val (eWalkV9 d.Pb.krootsV ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 8, M.1.pubsV i = pubK env i) :
    ∀ ℓ < (ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 5 val ((ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_walkV d.Pb.krootsV hk)
  refine tieD_gen ch _ _ (decL_of_decR (decR_walkV_at _ hk)) ders cmeta hop env _
    (by rw [show (Nock.Emit.walkAtomSpecAt d.Pb.krootsV).gates = ((TSpec.ofTemplate (tWalkV d.Pb.krootsV)).rename Nock.Emit.fM id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 5 val) (tWalkV d.Pb.krootsV) rfl rfl rfl rfl (eWalkV9 d.Pb.krootsV) val (chalsAJ8Z deltaF χ) (M.1.pubsV)
    (cKmem (tWalkV d.Pb.krootsV).baseCols ((tWalkV d.Pb.krootsV).width 3) 8 chalV)
    (cBmem ((tWalkV d.Pb.krootsV).width 3)) Nock.Emit.fM (envE ders cmeta env) 8 (fun j => by rw [bc_walkV d.Pb.krootsV]; exact consAt9_walkV d χ M val j)
    (by show env.bc = _; rw [bc_walkV d.Pb.krootsV]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 ∧ i ≠ 2 ∧ i ≠ 3 := by simpa [cKmem, chalV] using hi
      exact (chalsV_eq χ i hi'.1 hi'.2.1 hi'.2.2).trans (fM_leaf hE i hi'.1).symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

theorem tieD9_split (ch : NockvmE2E.Exec.Tr.Chip) (hk : d.Pb.nA ∈ [1, 2])
    (hop : HopZero ch (Nock.Emit.emit_splitAt d.Pb.nA) ders cmeta ch.baseCols)
    (hbc : env.bc = 72)
    (hcur : ∀ n (hn : n < (tSplit d.Pb.nA).width 3), env.cur n = val (eSplit d.Pb.nA ⟨n, hn⟩, 0))
    (hnext : ∀ n (hn : n < (tSplit d.Pb.nA).width 3), env.next n = val (eSplit d.Pb.nA ⟨n, hn⟩, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : ∀ i < 2, M.1.pubsS i = pubK env i) :
    ∀ ℓ < (ncRoute (tSplit d.Pb.nA).baseTransition.length (tSplit d.Pb.nA).mixedTransition.length).nK,
      ∑ k ∈ Finset.range ((ncRoute (tSplit d.Pb.nA).baseTransition.length (tSplit d.Pb.nA).mixedTransition.length).mult ℓ),
        cf k * consAt9 d χ M 7 val ((ncRoute (tSplit d.Pb.nA).baseTransition.length (tSplit d.Pb.nA).mixedTransition.length).jOf ℓ k) =
      (evalDagK ch env)[ℓ]! := by
  have hchk := chkT_all (chk_split _ hk)
  refine tieD_gen ch _ _ (decL_of_decR (decR_split_at _ hk)) ders cmeta hop env _
    (by rw [show (Nock.Emit.splitSpecAt d.Pb.nA).gates = ((TSpec.ofTemplate (tSplit d.Pb.nA)).rename Nock.Emit.fM id id).gates from rfl]
        exact dagVals_nc _ rfl rfl rfl rfl _ _) _ (length_tplVals _ _ _ _ _ _) _ ?_
  refine tie_nc' (consAt9 d χ M 7 val) (tSplit d.Pb.nA) rfl rfl rfl rfl (eSplit d.Pb.nA) val (chalsMJ8 deltaF χ) (M.1.pubsS)
    (cKmem (tSplit d.Pb.nA).baseCols ((tSplit d.Pb.nA).width 3) 2 chalM)
    (cBmem ((tSplit d.Pb.nA).width 3)) Nock.Emit.fM (envE ders cmeta env) 2 (fun j => by rw [bc_split d.Pb.nA]; exact consAt9_split d χ M val j)
    (by show env.bc = _; rw [bc_split d.Pb.nA]; exact hbc) hcur hnext
    (fun n => rfl) (fun n hn => by simpa [cBmem] using hn) (fun n hn => by simpa [cBmem] using hn) (fun n => rfl)
    (fun i hi => by simpa [cKmem] using hi) (fun i hi => by simpa [cKmem] using hi)
    (fun i hi => by
      have hi' : i ≤ 36 := by simpa [cKmem, chalM] using hi
      exact (chalsM_eq χ i hi').trans (fM_leaf hE i hi').symm)
    (fun i hi => hpub i (by simpa [cKmem] using hi)) hchk.1 hchk.2

end TieD9


/-! ## 8. the routing of the eight tables, and the uniform tie -/

theorem len_nc9 (T : ChipTemplate Gl) (hext : T.extTransition = []) (hd1 : T.extDeg1 = []) (hd3 : T.extDeg3 = [])
    (heq : T.equalityChecks = []) :
    (T.allGates powerBasis3).length = (ncRoute T.baseTransition.length T.mixedTransition.length).N :=
  len_nc T hext hd1 hd3 heq

/-- the routing of the eight J-9 A tables onto their DAG gates -/
noncomputable def rt9 (d : Datum9A) : Fin 8 → Route
  | 0 => cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length
  | 1 => ncRoute Nock.Emit.cellKWTemplate.baseTransition.length Nock.Emit.cellKWTemplate.mixedTransition.length
  | 2 => ncRoute (tWalkJ8 d.Pb.kroots).baseTransition.length (tWalkJ8 d.Pb.kroots).mixedTransition.length
  | 3 => ncRoute Nock.Emit.jetTemplate.baseTransition.length Nock.Emit.jetTemplate.mixedTransition.length
  | 4 => ncRoute Nock.Emit.atomTemplate.baseTransition.length Nock.Emit.atomTemplate.mixedTransition.length
  | 5 => ncRoute (tWalkV d.Pb.krootsV).baseTransition.length (tWalkV d.Pb.krootsV).mixedTransition.length
  | 6 => ncRoute tAxis.baseTransition.length tAxis.mixedTransition.length
  | 7 => ncRoute (tSplit d.Pb.nA).baseTransition.length (tSplit d.Pb.nA).mixedTransition.length

/-- the sizes of the eight tables are the route sizes -/
theorem rt9_N (d : Datum9A) (t : Fin 8) : (rt9 d t).N = sz9 d t := by
  fin_cases t
  · show (cRoute cArith9.length cEq9.length cAcc9.length (cSlot9 ++ walkGatesFX9).length).N = (gatesHX9P powerBasis3 deltaF).length
    rw [show (gatesHX9P powerBasis3 deltaF).length = (gatesHX9 powerBasis3 Nock.Emit.δ).length from List.length_map _,
      gatesHX9_eq]
    simp only [List.length_append, Kflat_length, cRoute, acc9_len]
  · exact (len_nc9 Nock.Emit.cellKWTemplate rfl rfl rfl rfl).symm
  · exact (len_nc9 (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl).symm
  · exact (len_nc9 Nock.Emit.jetTemplate rfl rfl rfl rfl).symm
  · exact (len_nc9 Nock.Emit.atomTemplate rfl rfl rfl rfl).symm
  · exact (len_nc9 (tWalkV d.Pb.krootsV) rfl rfl rfl rfl).symm
  · exact (len_nc9 tAxis rfl rfl rfl rfl).symm
  · exact (len_nc9 (tSplit d.Pb.nA) rfl rfl rfl rfl).symm

/-- the emitted DAG document of table `s` -/
def DOf9 (d : Datum9A) : Fin 8 → DagGates
  | 0 => Nock.Emit.emit_compute9
  | 1 => Nock.Emit.emit_cellKW
  | 2 => emitDag (Nock.Emit.walkJ8SpecAt d.Pb.kroots)
  | 3 => Nock.Emit.emit_jet
  | 4 => Nock.Emit.emit_atom
  | 5 => emitDag (Nock.Emit.walkAtomSpecAt d.Pb.krootsV)
  | 6 => Nock.Emit.emit_axis
  | 7 => Nock.Emit.emit_splitAt d.Pb.nA

/-- the base-column count of each J-9 A chip (the document's round-0 width) -/
def bcOf9 : Fin 8 → ℕ
  | 0 => 83 | 1 => 134 | 2 => 25 | 3 => 29 | 4 => 205 | 5 => 25 | 6 => 22 | 7 => 72

def wOf9 : Fin 8 → ℕ
  | 0 => 137 | 1 => 242 | 2 => 166 | 3 => 71 | 4 => 349 | 5 => 166 | 6 => 52 | 7 => 90

/-- the interface column of local column `n` of table `s` (total: out of range wraps) -/
def colI9 : Fin 8 → ℕ → Ι9
  | 0, n => iC ⟨n % 137, Nat.mod_lt _ (by norm_num)⟩
  | 1, n => iM ⟨n % 242, Nat.mod_lt _ (by norm_num)⟩
  | 2, n => iW ⟨n % 166, Nat.mod_lt _ (by norm_num)⟩
  | 3, n => iJ ⟨n % 71, Nat.mod_lt _ (by norm_num)⟩
  | 4, n => iA ⟨n % 349, Nat.mod_lt _ (by norm_num)⟩
  | 5, n => iV ⟨n % 166, Nat.mod_lt _ (by norm_num)⟩
  | 6, n => iX ⟨n % 52, Nat.mod_lt _ (by norm_num)⟩
  | 7, n => iS ⟨n % 90, Nat.mod_lt _ (by norm_num)⟩

theorem tabΙ9_colI9 (s : Fin 8) (n : ℕ) : tabΙ9 (colI9 s n) = s := by
  fin_cases s <;> rfl

theorem w_jet : Nock.Emit.jetTemplate.width 3 = 71 := by decide +kernel
theorem w_atom : Nock.Emit.atomTemplate.width 3 = 349 := by decide +kernel

theorem eC_eq9 (n : ℕ) (hn : n < 137) : iC (⟨n, hn⟩ : Fin 137) = colI9 0 n :=
  congrArg iC (Fin.ext (Nat.mod_eq_of_lt hn).symm)
theorem eCell_eq9 (j : Fin (Nock.Emit.cellKWTemplate.width 3)) : eCell9 j = colI9 1 j.1 :=
  congrArg iM (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 w_cell)).symm)
theorem eWalk_eq9 (k : ℕ) (j : Fin ((tWalkJ8 k).width 3)) : eWalk9 k j = colI9 2 j.1 :=
  congrArg iW (Fin.ext (Nat.mod_eq_of_lt (by exact j.2)).symm)
theorem eJet_eq9 (j : Fin (Nock.Emit.jetTemplate.width 3)) : eJet9 j = colI9 3 j.1 :=
  congrArg iJ (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 w_jet)).symm)
theorem eAtom_eq9 (j : Fin (Nock.Emit.atomTemplate.width 3)) : eAtom9 j = colI9 4 j.1 :=
  congrArg iA (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 w_atom)).symm)
theorem eWalkV_eq9 (k : ℕ) (j : Fin ((tWalkV k).width 3)) : eWalkV9 k j = colI9 5 j.1 :=
  congrArg iV (Fin.ext (Nat.mod_eq_of_lt (by exact j.2)).symm)
theorem eAxis_eq9 (j : Fin (tAxis.width 3)) : eAxis j = colI9 6 j.1 :=
  congrArg iX (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 w_axis)).symm)
theorem eSplit_eq9 (nA : ℕ) (j : Fin ((tSplit nA).width 3)) : eSplit nA j = colI9 7 j.1 :=
  congrArg iS (Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_eq j.2 (w_split nA))).symm)

/-- what `pr.rd` must hand the chip of table `s` -/
def PubsOK9 (M : Msg9) (env : KEnv) : Fin 8 → Prop
  | 0 => ∀ s < 33, NockvmE2E.J8.InstJ8.xpF M.2 s = env.pub s
  | 1 => ∀ i < 6, M.1.pubsC i = pubK env i
  | 2 => ∀ i < 8, M.1.pubsW i = pubK env i
  | 3 => ∀ i < 4, M.1.pubsJ i = pubK env i
  | 4 => ∀ i < 12, M.1.pubsA i = pubK env i
  | 5 => ∀ i < 8, M.1.pubsV i = pubK env i
  | 6 => ∀ i < 4, M.1.pubsX i = pubK env i
  | 7 => ∀ i < 2, M.1.pubsS i = pubK env i

/-- the tie of one table against its loaded chip -/
def TieAt9 (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN) (env : KEnv)
    (ch : NockvmE2E.Exec.Tr.Chip) (s : Fin 8) : Prop :=
  ∀ ℓ < (rt9 d s).nK, ∑ k ∈ Finset.range ((rt9 d s).mult ℓ), cf k * consAt9 d χ M s val ((rt9 d s).jOf ℓ k) =
    (evalDagK ch env)[ℓ]!

/-- the numerals the emitted chips exist for -/
def NumOK9 (d : Datum9A) (s : Fin 8) : Prop :=
  (s = 2 → d.Pb.kroots ∈ walkKs9) ∧ (s = 5 → d.Pb.krootsV ∈ [1, 2]) ∧ (s = 7 → d.Pb.nA ∈ [1, 2])

set_option maxHeartbeats 1600000 in
/-- **the J-9 A per-table tie, uniformly in the table** (twin of `TieJ8G.tieAt`) -/
theorem tieAt9 (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN)
    (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip) (s : Fin 8)
    (hnum : NumOK9 d s) (hop : HopZero ch (DOf9 d s) ders cmeta ch.baseCols) (hbe : env.bc = bcOf9 s)
    (hcur : ∀ n < wOf9 s, env.cur n = val (colI9 s n, 0)) (hnext : ∀ n < wOf9 s, env.next n = val (colI9 s n, 1))
    (hE : SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : PubsOK9 M env s) :
    TieAt9 d χ M val env ch s := by
  fin_cases s
  · exact tieD9_comp d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eC_eq9 n hn]; exact hcur n hn) (fun n hn => by rw [eC_eq9 n hn]; exact hnext n hn) hE hpub
  · exact tieD9_cell d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eCell_eq9]; exact hcur n (by have := hn; rwa [w_cell] at this))
      (fun n hn => by rw [eCell_eq9]; exact hnext n (by have := hn; rwa [w_cell] at this)) hE hpub
  · exact tieD9_walk d χ M val ders cmeta env ch (hnum.1 rfl) hop hbe
      (fun n hn => by rw [eWalk_eq9]; exact hcur n hn) (fun n hn => by rw [eWalk_eq9]; exact hnext n hn) hE hpub
  · exact tieD9_jet d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eJet_eq9]; exact hcur n (by have := hn; rwa [w_jet] at this))
      (fun n hn => by rw [eJet_eq9]; exact hnext n (by have := hn; rwa [w_jet] at this)) hE hpub
  · exact tieD9_atom d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eAtom_eq9]; exact hcur n (by have := hn; rwa [w_atom] at this))
      (fun n hn => by rw [eAtom_eq9]; exact hnext n (by have := hn; rwa [w_atom] at this)) hE hpub
  · exact tieD9_walkV d χ M val ders cmeta env ch (hnum.2.1 rfl) hop hbe
      (fun n hn => by rw [eWalkV_eq9]; exact hcur n hn) (fun n hn => by rw [eWalkV_eq9]; exact hnext n hn) hE hpub
  · exact tieD9_axis d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eAxis_eq9]; exact hcur n (by have := hn; rwa [w_axis] at this))
      (fun n hn => by rw [eAxis_eq9]; exact hnext n (by have := hn; rwa [w_axis] at this)) hE hpub
  · exact tieD9_split d χ M val ders cmeta env ch (hnum.2.2 rfl) hop hbe
      (fun n hn => by rw [eSplit_eq9]; exact hcur n (by have := hn; rwa [w_split] at this))
      (fun n hn => by rw [eSplit_eq9]; exact hnext n (by have := hn; rwa [w_split] at this)) hE hpub

/-! ## 9. the global fiber (eight tables): twin of `TieJ8.fiber_global` -/

section Global9
variable (sz : Fin 8 → ℕ)

/-- the local (within-table) index of a global J-8 constraint -/
def loc9 (j : Fin (∑ t : Fin 8, sz t)) : ℕ := ((finSigmaFinEquiv.symm j).2 : ℕ)

theorem loc_eq9 (j : Fin (∑ t : Fin 8, sz t)) : loc9 sz j = ((finSigmaFinEquiv.symm j).2 : ℕ) := rfl

theorem tabS_jglob9 (t : Fin 8) (l : Fin (sz t)) :
    (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨t, l⟩ : Fin (∑ t : Fin 8, sz t))).1 = t := by
  rw [Equiv.symm_apply_apply]

theorem loc_jglob9 (t : Fin 8) (l : Fin (sz t)) :
    loc9 sz (finSigmaFinEquiv ⟨t, l⟩) = l := by
  unfold loc9; rw [Equiv.symm_apply_apply]

theorem fiber_global9 (rt : Fin 8 → Route) (hN : ∀ t, (rt t).N = sz t) (t : Fin 8) (ℓ : ℕ) (hℓ : ℓ < (rt t).nK)
    (F : Fin (∑ t : Fin 8, sz t) → KN) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (∑ t : Fin 8, sz t) =>
        (finSigmaFinEquiv.symm j).1 = t ∧ ((rt t).route (loc9 sz j)).1 = ℓ),
        cf ((rt t).route (loc9 sz j)).2 * F j =
      ∑ k ∈ Finset.range ((rt t).mult ℓ), cf k *
        (if h : (rt t).jOf ℓ k < sz t then F (finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, h⟩⟩) else 0) := by
  have hlt : ∀ k, k < (rt t).mult ℓ → (rt t).jOf ℓ k < sz t := fun k hk => by
    have := ((rt t).h2 ℓ hℓ k hk).1; rw [hN t] at this; exact this
  have hdec : ∀ j : Fin (∑ t : Fin 8, sz t), (finSigmaFinEquiv.symm j).1 = t →
      ∃ h : loc9 sz j < sz t, j = finSigmaFinEquiv ⟨t, ⟨loc9 sz j, h⟩⟩ := by
    intro j hj
    obtain ⟨⟨t', l'⟩, hjj⟩ : ∃ x, finSigmaFinEquiv.symm j = x := ⟨_, rfl⟩
    rw [hjj] at hj
    simp only at hj
    subst hj
    have hl : loc9 sz j = (l' : ℕ) := by unfold loc9; rw [hjj]
    have hlt' : loc9 sz j < sz t' := by rw [hl]; exact l'.2
    refine ⟨hlt', ?_⟩
    have e1 : j = finSigmaFinEquiv ⟨t', l'⟩ := by rw [← hjj, Equiv.apply_symm_apply]
    have e2 : (⟨t', l'⟩ : Σ t, Fin (sz t)) = ⟨t', ⟨loc9 sz j, hlt'⟩⟩ := Sigma.ext rfl (heq_of_eq (Fin.ext hl.symm))
    rw [← e2]; exact e1
  refine Finset.sum_bij' (fun j _ => ((rt t).route (loc9 sz j)).2)
    (fun k hk => finSigmaFinEquiv ⟨t, ⟨(rt t).jOf ℓ k, hlt k (Finset.mem_range.mp hk)⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, _⟩ := hdec j hj.1
    have hl' : loc9 sz j < (rt t).N := by rw [hN]; exact hl
    have := ((rt t).h1 (loc9 sz j) hl').2.1
    rw [hj.2] at this
    exact Finset.mem_range.mpr this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hk' := Finset.mem_range.mp hk
    refine ⟨by rw [Equiv.symm_apply_apply], ?_⟩
    rw [loc_jglob9]
    exact congrArg Prod.fst ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc9 sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc9 sz j) hl').2.2
    rw [hj.2] at h3
    conv_rhs => rw [hjj]
    congr 2
    exact Fin.ext h3
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    show ((rt t).route (loc9 sz (finSigmaFinEquiv ⟨t, _⟩))).2 = k
    rw [loc_jglob9]
    exact congrArg Prod.snd ((rt t).h2 ℓ hℓ k hk').2
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨hl, hjj⟩ := hdec j hj.1
    have hl' : loc9 sz j < (rt t).N := by rw [hN]; exact hl
    have h3 := ((rt t).h1 (loc9 sz j) hl').2.2
    rw [hj.2] at h3
    have h4 : (rt t).jOf ℓ ((rt t).route (loc9 sz j)).2 < sz t := by rw [h3]; exact hl
    show cf _ * F j = cf _ * (if h : (rt t).jOf ℓ ((rt t).route (loc9 sz j)).2 < sz t then _ else 0)
    rw [dif_pos h4]
    congr 2
    conv_lhs => rw [hjj]
    congr 2
    exact Fin.ext h3.symm


end Global9

theorem aeval_consT9_eq (d : Datum9A) (χ : NockvmE2E.Rap.Coins Φ0 KN) (M : Msg9) (val : Ι9 × Fin 2 → KN)
    (σj : Σ t : Fin 8, Fin (sz9 d t)) :
    MvPolynomial.aeval val (consT9 d χ M σj.1 σj.2) = consAt9 d χ M σj.1 val (σj.2 : ℕ) := by
  unfold consAt9
  rw [dif_pos σj.2.2]

end NockvmE2E.J9A.TieJ9A

#print axioms NockvmE2E.J9A.TieJ9A.chk_axis
#print axioms NockvmE2E.J9A.TieJ9A.chk_split
#print axioms NockvmE2E.J9A.TieJ9A.chk_compute9
#print axioms NockvmE2E.J9A.TieJ9A.decR_compute9
#print axioms NockvmE2E.J9A.TieJ9A.decR_axis
#print axioms NockvmE2E.J9A.TieJ9A.decR_split_at
#print axioms NockvmE2E.J9A.TieJ9A.tie_comp9
#print axioms NockvmE2E.J9A.TieJ9A.tieD9_comp
#print axioms NockvmE2E.J9A.TieJ9A.tieD9_axis
#print axioms NockvmE2E.J9A.TieJ9A.tieD9_split
#print axioms NockvmE2E.J9A.TieJ9A.rt9_N
#print axioms NockvmE2E.J9A.TieJ9A.tieAt9
#print axioms NockvmE2E.J9A.TieJ9A.fiber_global9
