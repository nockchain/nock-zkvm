/-
  NockvmE2E/Exec/SoundOnline.lean   (pcs-base, ; proof-only, kernel)

  The split lemma `verifyOnline_split`: if `setup X0 H = some vk` and `verifyOnline vk … π πF` accepts, then either `verifyFlat X0 H FS z π`
  accepts (the J-8 chain's `AccF`, `FlatOk`), or `FixFail`: the side proof `πF` passes `verifyFix` but one of its claimed values
  differs from the TRUE evaluation of the fixed column (`fixTrue`: `hornerG pre`, the `Z_H` product, the `Zout` product) at the opening
  point.  Elementary, no random oracle.  Phase by phase against `FlatOk` (Sound.lean).
-/
import NockvmE2E.Exec.Sound
import NockvmE2E.Exec.VerifyOnline

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

/-- `vk.X`: the instance with `pre` erased -/
def eraseX (X0 : ExecInst) : ExecInst := { X0 with pre := X0.pre.map (fun _ => #[]) }

/-- online `curNxt` (kind-1 columns from the side proof's values) -/
def curNxtOn (XI : ExecInst) (π : FlatProof) (vF : Array (Array VF.K3)) (lay : FixLay) : Array VF.K3 × Array VF.K3 :=
  (List.range XI.nc).foldl
    (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (vF[lay.pre[c]!]!)[0]!, st.2.set! c (vF[lay.pre[c]!]!)[1]!)
      | _ => st)
    (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)

/-- flat `curNxt` (kind-1 columns by `hornerG` of the instance's `pre`), text of `verifyFlatE` -/
def curNxtFl (XI : ExecInst) (π : FlatProof) (zeta : VF.K3) : Array VF.K3 × Array VF.K3 :=
  let omZ := VF.K3.smul XI.hGen zeta
  (List.range XI.nc).foldl
    (fun (st : Array VF.K3 × Array VF.K3) c =>
      match XI.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if XI.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (VF.K3.hornerG XI.pre[c]! zeta), st.2.set! c (VF.K3.hornerG XI.pre[c]! omZ))
      | _ => st)
    (Array.replicate (XI.nc + XI.nq) VF.K3.zero, Array.replicate (XI.nc + XI.nq) VF.K3.zero)

/-- online `lhs` (the `mult_t` factor from the side proof's `zout` values) -/
def lhsOn (XI : ExecInst) (vF : Array (Array VF.K3)) (lay : FixLay) (curNxt : Array VF.K3 × Array VF.K3)
    (pub : Array G) (slots : Array VF.K3) (alpha : VF.K3) : VF.K3 :=
  (XI.tabs.foldl (fun (st : VF.K3 × VF.K3 × ℕ) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                  bc := t.chip.baseCols }
    let (s, pw) := cvals.foldl (fun (a : VF.K3 × VF.K3) v => (VF.K3.add a.1 (VF.K3.mul a.2 v), VF.K3.mul a.2 alpha)) (VF.K3.zero, st.2.1)
    let mult := if t.hN < XI.hN then (vF[lay.zout[st.2.2]!]!)[0]! else VF.K3.one
    (VF.K3.add st.1 (VF.K3.mul s mult), pw, st.2.2 + 1)) (VF.K3.zero, VF.K3.one, 0)).1

/-- flat `lhs`, text of `verifyFlatE` -/
def lhsFl (XI : ExecInst) (curNxt : Array VF.K3 × Array VF.K3) (pub : Array G) (slots : Array VF.K3) (alpha zeta : VF.K3) : VF.K3 :=
  (XI.tabs.foldl (fun (st : VF.K3 × VF.K3) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                  bc := t.chip.baseCols }
    let (s, pw) := cvals.foldl (fun (a : VF.K3 × VF.K3) v => (VF.K3.add a.1 (VF.K3.mul a.2 v), VF.K3.mul a.2 alpha)) (VF.K3.zero, st.2)
    let mult := ((List.range (XI.hN - t.hN)).foldl
      (fun (a : VF.K3 × G) _ => (VF.K3.mul a.1 (VF.K3.sub zeta (VF.K3.ofG a.2)), VF.mul a.2 XI.hGen))
      (VF.K3.one, VF.mul XI.hShift (VF.pow XI.hGen t.hN))).1
    (VF.K3.add st.1 (VF.K3.mul s mult), pw)) (VF.K3.zero, VF.K3.one)).1

/-- `verifyOnlineE` accepts, as a proposition (transcribed from `VerifyOnline.lean`; same style as `FlatOk`) -/
def OnlineOk (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop :=
  let XI := vk.X
  let nB := 4
  let k := XI.k
  let ncq := XI.nc + XI.nq
  let lay := fixLayout XI vk.cols
  allCanonOnline z π = true ∧
  (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) = true ∧
  (π.vT.size == XI.nc && π.vQ.size == XI.nq && π.pfinal.size == XI.d && π.pos.size == XI.l) = true ∧
  (∀ c ∈ List.range XI.nc, (π.vT[c]!.size == vTLen XI c) = true) ∧
  (π.pos.all (· < 2 ^ XI.nD)) = true ∧
  let pfEnc := π.pfinal.toList.flatMap VF.K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl XI
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if nlOf i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (nlOf i)
  (chals.all (·.all based)) = true ∧
  let coins0 := k3s chals[1]! XI.nCoins[0]!
  let coins1 := k3s chals[2]! XI.nCoins[1]!
  let alpha := VF.K3.ofLimbs chals[3]!
  let zeta := VF.K3.ofLimbs chals[4]!
  let cs := VF.K3.ofLimbs chals[6]!
  let alphas : Array VF.K3 := (Array.range (k + 1)).map fun w => VF.K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := chals[8 + k]!.toArray.map (· % 2 ^ XI.nD)
  (π.pos == xs) = true ∧
  verifyFix vk H FSf z (fixCtx π zeta) zeta πF = .ok () ∧
  let vF := πF.vF
  let half0 := 2 ^ (XI.nD - 1)
  let (W, rank) := blockLayout XI
  let sels : Array (Array Nat) := (Array.range (nB + k)).map fun j => treeSel XI (W.getD j 0) j π.pos
  (∀ j ∈ List.range (nB + k), treeCheck XI H π W half0 sels j = .ok ()) ∧
  let slots : Array VF.K3 := XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := (vF[lay.zh]!)[0]!
  let curNxt := curNxtOn XI π vF lay
  (∀ c ∈ XI.pubOf.toList, (decide (c < XI.nc) && XI.colKind[c]! == 2) = true ∧ ((π.vT[c]!)[0]!).isBase = true) ∧
  let pub : Array G := XI.pubOf.map fun c => ((π.vT[c]!)[0]!).c0
  (!zh.isZero) = true ∧
  let lhs := lhsOn XI vF lay curNxt pub slots alpha
  let zN := VF.K3.pow zeta XI.hN
  let qsum := (List.range XI.nq).foldl
    (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zN (j / 3))) π.vQ[j]!)) VF.K3.zero
  (lhs == VF.K3.mul zh qsum) = true ∧
  let pts := openPts XI zeta
  let dN := 2 ^ XI.nD
  (∀ pt ∈ pts.toList, (pt.pow dN != VF.K3.ofG (VF.pow XI.dShift dN)) = true) ∧
  XI.pubCheck slots pub = true ∧
  (∀ c ∈ List.range XI.nc, (XI.colKind[c]! != 1 || (List.range XI.r).all (fun o => (π.vT[c]!)[o]! == (vF[lay.pre[c]!]!)[o]!)) = true) ∧
  let ops := openingList XI cs π.vT π.vQ
  let baseAt (c idx : Nat) : G :=
    let b := XI.blockOf[c]!
    let leafPos := (idx % half0) * 2 * W[b]! + (idx / half0) * W[b]! + rank[c]!
    UInt64.ofNat (π.vals[b]!)[lb sels[b]! leafPos]!
  let word0 := deepWord XI pts ops baseAt
  ∀ q ∈ π.pos.toList,
    let g0 := q % half0
    ∃ r, friSteps XI π.vals sels alphas q (List.range' 1 k)
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt XI 0 g0) alphas[0]!) g0 = .ok r ∧
    (r.1 == VF.K3.horner π.pfinal (VF.K3.ofG (yAt XI (k + 1) r.2))) = true

theorem verifyOnlineE_ok_iff (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) :
    verifyOnlineE vk H FS FSf z π πF = .ok () ↔ OnlineOk vk H FS FSf z π πF := by
  unfold verifyOnlineE OnlineOk
  simp only [bind_unit_ok, forM_ok, ckE_ok]
  simp only [bind_ok, ckE_ok]
  exact Iff.rfl


deriving instance DecidableEq for FixCol

/-! ### the true evaluations of the fixed columns -/

/-- `Z_H(x) = ∏_{i<hN} (x - hShift·hGen^i)`: the fold of `verifyFlatE`'s `zh` -/
def zhEval (XI : ExecInst) (x : VF.K3) : VF.K3 :=
  ((List.range XI.hN).foldl
    (fun (st : VF.K3 × VF.G) _ => (VF.K3.mul st.1 (VF.K3.sub x (VF.K3.ofG st.2)), VF.mul st.2 XI.hGen)) (VF.K3.one, XI.hShift)).1

/-- `Zout(x) = ∏_{i ∈ [hNt, hN)} (x - hShift·hGen^i)`: the fold of `verifyFlatE`'s `mult_t` -/
def zoutEval (XI : ExecInst) (hNt : ℕ) (x : VF.K3) : VF.K3 :=
  ((List.range (XI.hN - hNt)).foldl
    (fun (a : VF.K3 × VF.G) _ => (VF.K3.mul a.1 (VF.K3.sub x (VF.K3.ofG a.2)), VF.mul a.2 XI.hGen))
    (VF.K3.one, VF.mul XI.hShift (VF.pow XI.hGen hNt))).1

/-- the TRUE value of a fixed column of the VK of `XI` (with its real `pre`) at `x`: Horner on the instance's coefficients, the `Z_H` product,
the `Zout` product.  (That `setup`'s NTT-built polynomials `fixPoly` evaluate to this is the setup-correctness side, .) -/
def fixTrue (XI : ExecInst) : FixCol → VF.K3 → VF.K3
  | .pre c, x => VF.K3.hornerG XI.pre[c]! x
  | .zh, x => zhEval XI x
  | .zout t, x => zoutEval XI (tabHN XI t) x

/-- the side proof's verifier accepts, yet a claimed value `vF[j][o]` differs from the true evaluation of fixed column `j` at opening point `o`
(`pts[o] = openPts X0 ζ [o]`, `ζ` the Fiat-Shamir challenge of the main proof) -/
def FixFail (X0 : ExecInst) (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop :=
  verifyFix vk H FSf z (fixCtx π (zetaOf X0 FS z π)) (zetaOf X0 FS z π) πF = .ok () ∧
  ∃ j o, j < vk.cols.size ∧ o < fixLen X0 vk.cols[j]! ∧
    (πF.vF[j]!)[o]! ≠ fixTrue X0 vk.cols[j]! ((openPts X0 (zetaOf X0 FS z π))[o]!)

/-- `setup` returns `some vk`: its gates hold, `vk.X` is `X0` with `pre` erased, `vk.cols = fixCols X0` -/
theorem setup_some {X0 : ExecInst} {H : HFn} {vk : VK} (h : setup X0 H = some vk) :
    setupGates X0 = true ∧ vk.X = eraseX X0 ∧ vk.cols = fixCols X0 := by
  unfold setup setupData at h
  by_cases hg : setupGates X0 = true
  · simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨hg, rfl, rfl⟩
  · simp only [Bool.not_eq_true] at hg
    simp [hg] at h

/-! ### the layout of the fixed columns -/

theorem set!_ne (a : Array ℕ) (i j v : ℕ) (h : i ≠ j) : (a.set! i v)[j]! = a[j]! := by
  simp [getElem!_def, h]

theorem set!_eq (a : Array ℕ) (i v : ℕ) (h : i < a.size) : (a.set! i v)[i]! = v := by
  simp [h]

theorem fixLayout_fold (XI : ExecInst) (cols : Array FixCol) :
    ∀ m, m ≤ cols.size →
      let st := (List.range m).foldl (fun (st : FixLay) j =>
        match cols[j]! with
        | .pre c => { st with pre := st.pre.set! c j }
        | .zh => { st with zh := j }
        | .zout t => { st with zout := st.zout.set! t j })
        { pre := Array.replicate XI.nc 0, zh := 0, zout := Array.replicate XI.tabs.size 0 }
      st.pre.size = XI.nc ∧ st.zout.size = XI.tabs.size ∧
      (∀ c, c < XI.nc → (∃ j, j < m ∧ cols[j]! = FixCol.pre c) → st.pre[c]! < m ∧ cols[st.pre[c]!]! = FixCol.pre c) ∧
      ((∃ j, j < m ∧ cols[j]! = FixCol.zh) → st.zh < m ∧ cols[st.zh]! = FixCol.zh) ∧
      (∀ t, t < XI.tabs.size → (∃ j, j < m ∧ cols[j]! = FixCol.zout t) → st.zout[t]! < m ∧ cols[st.zout[t]!]! = FixCol.zout t) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize ((List.range m).foldl (fun (st : FixLay) j =>
        match cols[j]! with
        | .pre c => { st with pre := st.pre.set! c j }
        | .zh => { st with zh := j }
        | .zout t => { st with zout := st.zout.set! t j })
        { pre := Array.replicate XI.nc 0, zh := 0, zout := Array.replicate XI.tabs.size 0 }) = st0 at *
    cases hcm : cols[m]! with
    | pre c0 =>
      refine ⟨by simpa [hcm] using h1, by simpa [hcm] using h2, ?_, ?_, ?_⟩
      · intro c hc ⟨j, hj, hjc⟩
        by_cases hcc : c = c0
        · subst hcc
          simp [show c < st0.pre.size by omega, hcm]
        · have hjm : j ≠ m := by
            rintro rfl; rw [hcm] at hjc; injection hjc with e; exact hcc e.symm
          have := h3 c hc ⟨j, by omega, hjc⟩
          have hne : c0 ≠ c := fun e => hcc e.symm
          simp only [hcm]
          rw [set!_ne _ _ _ _ hne]
          exact ⟨by omega, this.2⟩
      · intro ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h4 ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
      · intro t ht ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h5 t ht ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
    | zh =>
      refine ⟨by simpa [hcm] using h1, by simpa [hcm] using h2, ?_, ?_, ?_⟩
      · intro c hc ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h3 c hc ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
      · intro _
        simp only [hcm]
        exact ⟨by omega, trivial⟩
      · intro t ht ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h5 t ht ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
    | zout t0 =>
      refine ⟨by simpa [hcm] using h1, by simpa [hcm] using h2, ?_, ?_, ?_⟩
      · intro c hc ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h3 c hc ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
      · intro ⟨j, hj, hjc⟩
        have hjm : j ≠ m := by rintro rfl; rw [hcm] at hjc; simp at hjc
        have := h4 ⟨j, by omega, hjc⟩
        simp only [hcm]
        exact ⟨by omega, this.2⟩
      · intro t ht ⟨j, hj, hjc⟩
        by_cases htt : t = t0
        · subst htt
          simp [show t < st0.zout.size by omega, hcm]
        · have hjm : j ≠ m := by
            rintro rfl; rw [hcm] at hjc; injection hjc with e; exact htt e.symm
          have := h5 t ht ⟨j, by omega, hjc⟩
          have hne : t0 ≠ t := fun e => htt e.symm
          simp only [hcm]
          rw [set!_ne _ _ _ _ hne]
          exact ⟨by omega, this.2⟩

theorem fixLayout_pre (XI : ExecInst) (cols : Array FixCol) (c : ℕ) (hc : c < XI.nc)
    (hex : ∃ j, j < cols.size ∧ cols[j]! = FixCol.pre c) :
    (fixLayout XI cols).pre[c]! < cols.size ∧ cols[(fixLayout XI cols).pre[c]!]! = FixCol.pre c := by
  have := (fixLayout_fold XI cols cols.size le_rfl).2.2.1 c hc hex
  exact this

theorem fixLayout_zh (XI : ExecInst) (cols : Array FixCol) (hex : ∃ j, j < cols.size ∧ cols[j]! = FixCol.zh) :
    (fixLayout XI cols).zh < cols.size ∧ cols[(fixLayout XI cols).zh]! = FixCol.zh :=
  (fixLayout_fold XI cols cols.size le_rfl).2.2.2.1 hex

theorem fixLayout_zout (XI : ExecInst) (cols : Array FixCol) (t : ℕ) (ht : t < XI.tabs.size)
    (hex : ∃ j, j < cols.size ∧ cols[j]! = FixCol.zout t) :
    (fixLayout XI cols).zout[t]! < cols.size ∧ cols[(fixLayout XI cols).zout[t]!]! = FixCol.zout t :=
  (fixLayout_fold XI cols cols.size le_rfl).2.2.2.2 t ht hex

theorem mem_ex {cols : Array FixCol} {f : FixCol} (h : f ∈ cols) : ∃ j, j < cols.size ∧ cols[j]! = f := by
  obtain ⟨j, hj, e⟩ := Array.mem_iff_getElem.mp h
  exact ⟨j, hj, by rw [getElem!_pos cols j hj]; exact e⟩

theorem fixCols_pre (XI : ExecInst) (c : ℕ) (hc : c < XI.nc) (hk : XI.colKind[c]! = 1) :
    ∃ j, j < (fixCols XI).size ∧ (fixCols XI)[j]! = FixCol.pre c := by
  apply mem_ex
  simp only [fixCols, Array.mem_append, Array.mem_map, Array.mem_filter, Array.mem_range]
  exact Or.inl (Or.inl ⟨c, ⟨hc, by simp [hk]⟩, rfl⟩)

theorem fixCols_zh (XI : ExecInst) : ∃ j, j < (fixCols XI).size ∧ (fixCols XI)[j]! = FixCol.zh := by
  apply mem_ex
  simp [fixCols]

theorem fixCols_zout (XI : ExecInst) (t : ℕ) (ht : t < XI.tabs.size) (hl : tabHN XI t < XI.hN) :
    ∃ j, j < (fixCols XI).size ∧ (fixCols XI)[j]! = FixCol.zout t := by
  apply mem_ex
  simp only [fixCols, Array.mem_append, Array.mem_map, Array.mem_filter, Array.mem_range]
  exact Or.inr ⟨t, ⟨ht, by simp [hl]⟩, rfl⟩

/-! ### the opening points: `pts[0] = ζ`, `pts[1] = hGen·ζ` (for canonical `ζ`) -/

def ptStep (XI : ExecInst) (ζ : VF.K3) (st : Array VF.K3 × VF.K3) : Array VF.K3 × VF.K3 :=
  (st.1.push (VF.K3.mul ζ st.2), VF.K3.smul XI.hGen st.2)

def ptFold (XI : ExecInst) (ζ : VF.K3) (n : ℕ) : Array VF.K3 × VF.K3 :=
  (List.range n).foldl (fun st (_ : ℕ) => ptStep XI ζ st) (#[], VF.K3.one)

theorem ptFold_succ (XI : ExecInst) (ζ : VF.K3) (n : ℕ) : ptFold XI ζ (n + 1) = ptStep XI ζ (ptFold XI ζ n) := by
  simp [ptFold, List.range_succ, List.foldl_append]

theorem ptFold_size (XI : ExecInst) (ζ : VF.K3) : ∀ n, (ptFold XI ζ n).1.size = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [ptFold_succ]; simp [ptStep, ih]

theorem ptFold_prefix (XI : ExecInst) (ζ : VF.K3) (n : ℕ) :
    ∀ m, n ≤ m → ∀ i, i < n → (ptFold XI ζ m).1[i]? = (ptFold XI ζ n).1[i]? := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro i _; rfl
  | succ m hnm ih =>
    intro i hi
    rw [ptFold_succ]
    simp only [ptStep]
    rw [Array.getElem?_push, if_neg (by rw [ptFold_size]; omega)]
    exact ih i hi

theorem openPts_eq (XI : ExecInst) (ζ : VF.K3) :
    openPts XI ζ = ((ptFold XI ζ XI.r).1.push XI.ppt).push ζ := rfl

theorem openPts_get (XI : ExecInst) (ζ : VF.K3) (i : ℕ) (hi : i < XI.r) :
    (openPts XI ζ)[i]? = (ptFold XI ζ (i + 1)).1[i]? := by
  rw [openPts_eq]
  have hs := ptFold_size XI ζ XI.r
  rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]
  exact ptFold_prefix XI ζ (i + 1) XI.r hi i (by omega)

theorem openPts_zero (XI : ExecInst) (ζ : VF.K3) (hr : 1 ≤ XI.r) :
    (openPts XI ζ)[0]! = VF.K3.mul ζ VF.K3.one := by
  have := openPts_get XI ζ 0 (by omega)
  rw [getElem!_def, this]
  rfl

theorem openPts_one (XI : ExecInst) (ζ : VF.K3) (hr : 2 ≤ XI.r) :
    (openPts XI ζ)[1]! = VF.K3.mul ζ (VF.K3.smul XI.hGen VF.K3.one) := by
  have := openPts_get XI ζ 1 (by omega)
  rw [getElem!_def, this]
  rfl

theorem k3_mul_one (ζ : VF.K3) (h : canon3 ζ) : VF.K3.mul ζ VF.K3.one = ζ :=
  toKV_inj _ _ (canon3_mul _ _) h (by rw [toKV_mul, toKV_one, mul_one])

theorem k3_mul_smul_one (ζ : VF.K3) (g : UInt64) (h : canon3 ζ) :
    VF.K3.mul ζ (VF.K3.smul g VF.K3.one) = VF.K3.smul g ζ :=
  toKV_inj _ _ (canon3_mul _ _) (canon3_smul _ _) (by rw [toKV_mul, toKV_smul, toKV_one, toKV_smul]; ring)

theorem chalCan_of_all (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof)
    (hc' : ((chalsOf XI FS z π).all (·.all based)) = true) : ChalCan XI FS z π := by
  have hpp : NockvmE2E.Exec.p = VF.PN := by unfold NockvmE2E.Exec.p VF.PN; decide
  intro i x hx
  by_cases hi : i < (chalsOf XI FS z π).size
  · rw [getElem!_pos _ i hi] at hx
    have := (List.all_eq_true.mp ((arr_all_iff _ _).mp hc' _ (Array.getElem_mem hi))) x hx
    unfold based at this
    rw [hpp]; simpa using this
  · rw [getElem!_neg _ i hi] at hx
    exact absurd hx List.not_mem_nil

theorem allCanon_split (XI : ExecInst) (z : List Nat) (π : FlatProof) :
    allCanon XI z π = (instCanon XI && allCanonOnline z π) := by
  simp only [allCanon, instCanon, allCanonOnline, Bool.and_assoc]

/-- the online per-table multiplier fold agrees with the flat one, given that the claimed `zout` values are the products -/
theorem tabsFoldOn (ts : List TabInst) (sp : TabInst → VF.K3 → VF.K3 × VF.K3) (ms : TabInst → ℕ → VF.K3) (mf : TabInst → VF.K3) :
    ∀ (a b : VF.K3) (i : ℕ), (∀ m (hm : m < ts.length), ms ts[m] (i + m) = mf ts[m]) →
      let on := ts.foldl (fun (st : VF.K3 × VF.K3 × ℕ) t =>
        (VF.K3.add st.1 (VF.K3.mul (sp t st.2.1).1 (ms t st.2.2)), (sp t st.2.1).2, st.2.2 + 1)) (a, b, i)
      let fl := ts.foldl (fun (st : VF.K3 × VF.K3) t =>
        (VF.K3.add st.1 (VF.K3.mul (sp t st.2).1 (mf t)), (sp t st.2).2)) (a, b)
      on.1 = fl.1 := by
  induction ts with
  | nil => intro a b i _; rfl
  | cons t ts ih =>
    intro a b i h
    simp only [List.foldl_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]
    have := ih (VF.K3.add a (VF.K3.mul (sp t b).1 (mf t))) (sp t b).2 (i + 1) (by
      intro m hm
      have := h (m + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this)
    exact this


theorem curNxt_eq (X0 : ExecInst) (π : FlatProof) (vF : Array (Array VF.K3)) (lay : FixLay) (zeta : VF.K3)
    (h : ∀ c, c < X0.nc → X0.colKind[c]! = 1 →
      (vF[lay.pre[c]!]!)[0]! = VF.K3.hornerG X0.pre[c]! zeta ∧
      (vF[lay.pre[c]!]!)[1]! = VF.K3.hornerG X0.pre[c]! (VF.K3.smul X0.hGen zeta)) :
    curNxtOn X0 π vF lay = curNxtFl X0 π zeta := by
  unfold curNxtOn curNxtFl
  apply List.foldl_ext
  intro st c hc
  have hc' : c < X0.nc := List.mem_range.mp hc
  have hk := h c hc'
  show (match X0.colKind[c]! with
      | 0 => (st.1.set! c (π.vT[c]!)[0]!, st.2.set! c (if X0.r ≥ 2 then (π.vT[c]!)[1]! else VF.K3.zero))
      | 1 => (st.1.set! c (vF[lay.pre[c]!]!)[0]!, st.2.set! c (vF[lay.pre[c]!]!)[1]!)
      | _ => st) = _
  generalize hkk : X0.colKind[c]! = kk at hk ⊢
  match kk, hk with
  | 0, _ => rfl
  | 1, hk =>
    obtain ⟨e0, e1⟩ := hk rfl
    simp only [e0, e1]
  | n + 2, _ => rfl

theorem lhs_eq (X0 : ExecInst) (vF : Array (Array VF.K3)) (lay : FixLay) (zeta : VF.K3) (cn : Array VF.K3 × Array VF.K3)
    (pub : Array G) (slots : Array VF.K3) (alpha : VF.K3)
    (h : ∀ t, t < X0.tabs.size → tabHN X0 t < X0.hN → (vF[lay.zout[t]!]!)[0]! = zoutEval X0 (tabHN X0 t) zeta) :
    lhsOn X0 vF lay cn pub slots alpha = lhsFl X0 cn pub slots alpha zeta := by
  unfold lhsOn lhsFl
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  refine tabsFoldOn X0.tabs.toList
    (fun t pw =>
      let cur := cn.1.extract t.col0 (t.col0 + t.nc)
      let nxt := cn.2.extract t.col0 (t.col0 + t.nc)
      let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                    bc := t.chip.baseCols }
      cvals.foldl (fun (a : VF.K3 × VF.K3) v => (VF.K3.add a.1 (VF.K3.mul a.2 v), VF.K3.mul a.2 alpha)) (VF.K3.zero, pw))
    (fun t i => if t.hN < X0.hN then (vF[lay.zout[i]!]!)[0]! else VF.K3.one)
    (fun t => ((List.range (X0.hN - t.hN)).foldl
      (fun (a : VF.K3 × G) _ => (VF.K3.mul a.1 (VF.K3.sub zeta (VF.K3.ofG a.2)), VF.mul a.2 X0.hGen))
      (VF.K3.one, VF.mul X0.hShift (VF.pow X0.hGen t.hN))).1)
    VF.K3.zero VF.K3.one 0 ?_
  intro m hm
  simp only [Nat.zero_add]
  by_cases hl : X0.tabs.toList[m].hN < X0.hN
  · have hm' : m < X0.tabs.size := by simpa using hm
    have := h m hm' (by simp [tabHN, hm']; simpa using hl)
    simp only [hl, ite_true]
    rw [this]
    simp [zoutEval, tabHN, hm']
  · have : X0.hN - X0.tabs.toList[m].hN = 0 := by omega
    simp only [hl, ite_false, this]
    rfl

/-! `eraseX` changes `pre` only: every function of the instance that the online verifier uses is unchanged (all `rfl`) -/
section Erase
variable (X0 : ExecInst)
@[simp] theorem er_nD : (eraseX X0).nD = X0.nD := rfl
@[simp] theorem er_k : (eraseX X0).k = X0.k := rfl
@[simp] theorem er_nc : (eraseX X0).nc = X0.nc := rfl
@[simp] theorem er_nq : (eraseX X0).nq = X0.nq := rfl
@[simp] theorem er_d : (eraseX X0).d = X0.d := rfl
@[simp] theorem er_l : (eraseX X0).l = X0.l := rfl
@[simp] theorem er_r : (eraseX X0).r = X0.r := rfl
@[simp] theorem er_hN : (eraseX X0).hN = X0.hN := rfl
@[simp] theorem er_colKind : (eraseX X0).colKind = X0.colKind := rfl
@[simp] theorem er_blockOf : (eraseX X0).blockOf = X0.blockOf := rfl
@[simp] theorem er_pubOf : (eraseX X0).pubOf = X0.pubOf := rfl
@[simp] theorem er_nCoins : (eraseX X0).nCoins = X0.nCoins := rfl
@[simp] theorem er_derived : (eraseX X0).derived = X0.derived := rfl
@[simp] theorem er_tabs : (eraseX X0).tabs = X0.tabs := rfl
@[simp] theorem er_dShift : (eraseX X0).dShift = X0.dShift := rfl
@[simp] theorem er_treeSel : treeSel (eraseX X0) = treeSel X0 := rfl
@[simp] theorem er_blockLayout : blockLayout (eraseX X0) = blockLayout X0 := rfl
@[simp] theorem er_deepWord : deepWord (eraseX X0) = deepWord X0 := rfl
@[simp] theorem er_openPts : openPts (eraseX X0) = openPts X0 := rfl
@[simp] theorem er_openingList : openingList (eraseX X0) = openingList X0 := rfl
@[simp] theorem er_roundNl : roundNl (eraseX X0) = roundNl X0 := rfl
@[simp] theorem er_treeCheck : treeCheck (eraseX X0) = treeCheck X0 := rfl
@[simp] theorem er_vTLen : vTLen (eraseX X0) = vTLen X0 := rfl
@[simp] theorem er_yAt : yAt (eraseX X0) = yAt X0 := rfl
@[simp] theorem er_pubCheck : (eraseX X0).pubCheck = X0.pubCheck := rfl
@[simp] theorem er_fixLayout : fixLayout (eraseX X0) = fixLayout X0 := rfl
@[simp] theorem er_curNxtOn : curNxtOn (eraseX X0) = curNxtOn X0 := rfl
@[simp] theorem er_lhsOn : lhsOn (eraseX X0) = lhsOn X0 := rfl
end Erase

theorem friSteps_erase (X0 : ExecInst) (vals : Array (Array ℕ)) (sels : Array (Array ℕ)) (alphas : Array VF.K3) (q : ℕ) :
    ∀ (ws : List ℕ) (prev : VF.K3) (prevIdx : ℕ),
      friSteps (eraseX X0) vals sels alphas q ws prev prevIdx = friSteps X0 vals sels alphas q ws prev prevIdx := by
  intro ws
  induction ws with
  | nil => intro _ _; rfl
  | cons w ws ih =>
    intro prev prevIdx
    simp only [friSteps, ih]
    rfl

theorem preOpen_transfer (X0 : ExecInst) (π : FlatProof) (vF : Array (Array VF.K3)) (lay : FixLay) (pts : Array VF.K3) (c : ℕ)
    (hpre : X0.colKind[c]! = 1 → ∀ o, o < X0.r → (vF[lay.pre[c]!]!)[o]! = VF.K3.hornerG X0.pre[c]! (pts[o]!))
    (h : (X0.colKind[c]! != 1 || (List.range X0.r).all (fun o => (π.vT[c]!)[o]! == (vF[lay.pre[c]!]!)[o]!)) = true) :
    (X0.colKind[c]! != 1 || (List.range X0.r).all (fun o => (π.vT[c]!)[o]! == VF.K3.hornerG X0.pre[c]! (pts[o]!))) = true := by
  by_cases hk : X0.colKind[c]! = 1
  · simp only [hk, bne_self_eq_false, Bool.false_or, List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
    intro o ho
    rw [← hpre hk o ho]
    exact h o ho
  · simp [hk]

theorem online_to_flat (X0 : ExecInst) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (vk : VK)
    (hg : setupGates X0 = true) (hX : vk.X = eraseX X0) (hc : vk.cols = fixCols X0)
    (hon : OnlineOk vk H FS FSf z π πF) (hnf : ¬ FixFail X0 vk H FS FSf z π πF) : FlatOk X0 H FS z π := by
  have hg' := hg
  simp only [setupGates, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range, and_assoc] at hg'
  obtain ⟨gic, gin, gcs, gbs, gps, gnc, gnd, gnq, gr, ghN, gl, gpar, gtab, gblk⟩ := hg'
  unfold OnlineOk at hon
  simp only [hX, hc] at hon
  simp only [er_nD, er_k, er_nc, er_nq, er_d, er_l, er_r, er_hN, er_colKind, er_blockOf, er_pubOf, er_nCoins, er_derived, er_tabs, er_dShift, er_treeSel, er_blockLayout, er_deepWord, er_openPts, er_openingList, er_roundNl, er_treeCheck, er_vTLen, er_yAt, er_pubCheck, er_fixLayout, er_curNxtOn, er_lhsOn, friSteps_erase] at hon
  obtain ⟨O1, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15, O16⟩ := hon
  have hCh : ChalCan X0 FS z π := chalCan_of_all X0 FS z π O6
  have hζ : canon3 (zetaOf X0 FS z π) := canon3_zetaOf X0 FS z π hCh
  have hver : verifyFix vk H FSf z (fixCtx π (zetaOf X0 FS z π)) (zetaOf X0 FS z π) πF = .ok () := O8
  have hT : ∀ j, j < (fixCols X0).size → ∀ o, o < fixLen X0 (fixCols X0)[j]! →
      (πF.vF[j]!)[o]! = fixTrue X0 (fixCols X0)[j]! ((openPts X0 (zetaOf X0 FS z π))[o]!) := by
    intro j hj o ho
    by_contra hne
    exact hnf ⟨hver, j, o, by rw [hc]; exact hj, by rw [hc]; exact ho, by rw [hc]; exact hne⟩
  obtain ⟨lay, hlay⟩ : ∃ lay, lay = fixLayout X0 (fixCols X0) := ⟨_, rfl⟩
  rw [← hlay] at O11 O12 O15
  have hp0 : (openPts X0 (zetaOf X0 FS z π))[0]! = zetaOf X0 FS z π := by
    rw [openPts_zero X0 _ (by omega), k3_mul_one _ hζ]
  have hp1 : (openPts X0 (zetaOf X0 FS z π))[1]! = VF.K3.smul X0.hGen (zetaOf X0 FS z π) := by
    rw [openPts_one X0 _ (by omega), k3_mul_smul_one _ _ hζ]
  have hzh : (πF.vF[lay.zh]!)[0]! = zhEval X0 (zetaOf X0 FS z π) := by
    obtain ⟨hlt, hcl⟩ := fixLayout_zh X0 (fixCols X0) (fixCols_zh X0)
    rw [← hlay] at hlt hcl
    have := hT _ hlt 0 (by rw [hcl]; simp [fixLen])
    rw [this, hcl]
    simp only [fixTrue, hp0]
  have hpre : ∀ c, c < X0.nc → X0.colKind[c]! = 1 → ∀ o, o < X0.r →
      (πF.vF[lay.pre[c]!]!)[o]! = VF.K3.hornerG X0.pre[c]! ((openPts X0 (zetaOf X0 FS z π))[o]!) := by
    intro c hc hk o ho
    obtain ⟨hlt, hcl⟩ := fixLayout_pre X0 (fixCols X0) c hc (fixCols_pre X0 c hc hk)
    rw [← hlay] at hlt hcl
    have := hT _ hlt o (by rw [hcl]; simpa [fixLen] using ho)
    rw [this, hcl]
    rfl
  have hmult : ∀ t, t < X0.tabs.size → tabHN X0 t < X0.hN →
      (πF.vF[lay.zout[t]!]!)[0]! = zoutEval X0 (tabHN X0 t) (zetaOf X0 FS z π) := by
    intro t ht hl
    obtain ⟨hlt, hcl⟩ := fixLayout_zout X0 (fixCols X0) t ht (fixCols_zout X0 t ht hl)
    rw [← hlay] at hlt hcl
    have := hT _ hlt 0 (by rw [hcl]; simp [fixLen])
    rw [this, hcl]
    simp only [fixTrue, hp0]
  have hcn := curNxt_eq X0 π πF.vF lay (zetaOf X0 FS z π) (fun c hc hk =>
    ⟨by rw [hpre c hc hk 0 (by omega), hp0], by rw [hpre c hc hk 1 (by omega), hp1]⟩)
  rw [hcn] at O12
  rw [lhs_eq X0 πF.vF lay (zetaOf X0 FS z π) _ _ _ _ hmult] at O12
  rw [hzh] at O11 O12
  unfold FlatOk
  refine ⟨?F1, ?F2, ?F3, gpar, O2, O3, O4, gtab, O5, O6, O7, ?F12, O9, O10, O11, O12, O13, O14, gin, ?F20, O16⟩
  · rw [allCanon_split]; simp [gic, O1]
  · simp [gcs, gbs, gps, gnc]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  · intro c hcr
    simpa using gblk c (List.mem_range.mp hcr)
  · intro c hcr
    exact preOpen_transfer X0 π πF.vF lay _ c
      (fun hk o ho => hpre c (List.mem_range.mp hcr) hk o ho) (O15 c hcr)

/-- **The split lemma.**  If `setup X0 H = some vk` and the online verifier accepts (`π`, side proof `πF`), then the flat verifier
accepts `π` on the instance `X0` (the J-8 chain's `AccF`), or the side proof is a `FixFail`: it passes `verifyFix` while one of its claimed
fixed-column values differs from the true evaluation `fixTrue` at the opening point.  Elementary: no random oracle, no assumption on `H`, `FS`, `FSf`. -/
theorem verifyOnline_split (X0 : ExecInst) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (vk : VK)
    (hvk : setup X0 H = some vk) (hon : verifyOnline vk H FS FSf z π πF = true) :
    verifyFlat X0 H FS z π = true ∨ FixFail X0 vk H FS FSf z π πF := by
  obtain ⟨hg, hX, hc⟩ := setup_some hvk
  have hE : verifyOnlineE vk H FS FSf z π πF = .ok () := by
    unfold verifyOnline at hon
    cases h : verifyOnlineE vk H FS FSf z π πF with
    | error _ => simp [h] at hon
    | ok u => cases u; rfl
  by_cases hF : FixFail X0 vk H FS FSf z π πF
  · exact Or.inr hF
  · exact Or.inl ((verifyFlat_iff X0 H FS z π).mpr
      (online_to_flat X0 H FS FSf z π πF vk hg hX hc ((verifyOnlineE_ok_iff vk H FS FSf z π πF).mp hE) hF))

/-! ### non-vacuity: `setup` returns `some` on a toy instance with the layout of the selftest toy (`VerifyMain.toyInst`: columns trace/`isLast`/public,
one table, `hN = 4`, `nD = 5`, `k = 1`; `VerifyMain` itself cannot be imported here, its `toyInst` clashes with `Sound.lean`'s), for every hash `H`.
The kind-1 column's coefficients are a placeholder: the setup gates read only their size and canonicity. -/

def toyChipO : Tr.Chip :=
  let t := Tr.Ex.var 0 0
  let tn := Tr.Ex.var 1 0
  let isl := Tr.Ex.var 0 1
  let s := Tr.Ex.var 2 0
  let one := Tr.Ex.cF 1
  let mk (e : Tr.Ex) : Tr.Con := { kind := 0, round := 0, deg := 2, e := e }
  { id := "toy", shared := #[], colRound := #[0, 0, 0], sharedK := #[], consK := #[false, false, false], baseCols := 3, width := 3,
    cons := #[mk (.mul t (.sub t one)), mk (.mul (.sub one isl) (.add tn (.sub t one))), mk (.mul s (.sub s one))] }

def toyInstO : ExecInst :=
  let g32 := VF.pow 7 (2 ^ 32 - 1)
  { nD := 5, dShift := 7, dGen := VF.pow g32 (2 ^ 27), hN := 4, hGen := VF.pow g32 (2 ^ 30), hShift := 1
    r := 2, k := 1, d := 1, l := 4, nc := 3, nq := 3
    colKind := #[0, 1, 2], blockOf := #[0, 0, 2, 3, 3, 3], pre := #[#[], #[1, 2, 3, 4], #[]], pubOf := #[2]
    ppt := ⟨11, 5, 2⟩, nCoins := #[0, 0], derived := #[],
    tabs := #[{ hN := 4, col0 := 0, nc := 3, npub := 1, pubBase := 0, chip := toyChipO }], pubMode := 1, pubTest := fun _ p => p[0]! ≤ 1 }

theorem toy_setupGates : setupGates toyInstO = true := by decide +kernel

theorem toy_setup_some (H : HFn) : (setup toyInstO H).isSome = true := by
  simp [setup, setupData, toy_setupGates]

/-- the hypothesis `hvk` of `verifyOnline_split` is inhabited -/
theorem toy_hvk (H : HFn) : ∃ vk, setup toyInstO H = some vk := by
  obtain ⟨vk, hvk⟩ := Option.isSome_iff_exists.mp (toy_setup_some H)
  exact ⟨vk, hvk⟩

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.verifyOnline_split
#print axioms NockvmE2E.Exec.V.online_to_flat
#print axioms NockvmE2E.Exec.V.verifyOnlineE_ok_iff
#print axioms NockvmE2E.Exec.V.toy_hvk
#print axioms NockvmE2E.Exec.V.fixLayout_fold
#print axioms NockvmE2E.Exec.V.openPts_one
