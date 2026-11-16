/-
  NockvmE2E/Exec/VKp.lean   (pcs-base,  section 1.1; executed, Mathlib-free, no proofs)

  PRIMED copies of the side-proof executables with the side Merkle hash `Hf` as an explicit argument:
    `setupData' X Hf`, `setup' X Hf`, `verifyFix' vk Hf FSf ...`, `verifyOnlineE' vk H Hf FS FSf ...`, `verifyOnline' vk H Hf FS FSf ...`.
  The unprimed executables (VK.lean, VerifyOnline.lean) are UNCHANGED; they are `rfl`-abbreviations at `Hf := hFix H`
  (`setup_eq_setup'`, `verifyFix_eq_verifyFix'`, `verifyOnline_eq_verifyOnline'` below), so the exe, 's cost theorems and the tagged copies
  are unaffected.  Why: in the proof model `hFix H` is constant and the adversary holds the side oracle as a value; the primed
  versions let the proof model give the side verifier its own ORACLE `Hf` (E2EOnlineP.lean).
  Tags: the side trees use tags 0 (VK tree) and 4+w (FRI tree w), exactly as the unprimed code uses them under `hFix` (which adds 64).
-/
import NockvmE2E.Exec.VerifyOnline
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J

/-- `setupData` with the VK-tree hash `Hf` explicit; the gate-free part (the data is a function of `X` and `Hf` alone) -/
def mkVKData' (X : ExecInst) (Hf : HFn) : VKData :=
  let cols := fixCols X
  let orb := orbitPts X
  let polys := cols.map (fixPoly X orb)
  let half0 := 2 ^ (X.nD - 1)
  let lde := polys.map fun p => cosetLdeR p X.nD X.dGen
  let lv := fxRagLevels Hf 0 cols.size half0 lde
  { vk := { X := { X with pre := X.pre.map (fun _ => #[]) }, cols := cols, root := lv[0]![0]! },
    polys := polys, lde := lde, levels := lv }

def setupData' (X : ExecInst) (Hf : HFn) : Option VKData :=
  if !setupGates X then none else some (mkVKData' X Hf)

def setup' (X : ExecInst) (Hf : HFn) : Option VK := (setupData' X Hf).map (·.vk)

theorem setupData_eq_setupData' (X : ExecInst) (H : HFn) : setupData X H = setupData' X (hFix H) := rfl
theorem setup_eq_setup' (X : ExecInst) (H : HFn) : setup X H = setup' X (hFix H) := rfl

theorem setup'_of_gates {X : ExecInst} (hg : setupGates X = true) (Hf : HFn) : setup' X Hf = some (mkVKData' X Hf).vk := by
  simp [setup', setupData', hg]

/-- verify the side proof against `vk.root`: on success every `πF.vF[j][o]` is the value of fixed polynomial `j` at `openPts X ζ [o]` (up to FRI soundness) -/
def verifyFix' (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : K3) (πF : FixProof) : Except String Unit :=
  let X := vk.X
  let k := X.k
  let F := vk.cols.size
  ckE (πF.vF.size == F && (List.range F).all (fun j => πF.vF[j]!.size == fixLen X vk.cols[j]!) &&
       πF.pfinal.size == X.d && πF.pos.size == X.l && πF.roots.size == k &&
       πF.vals.size == 1 + k && πF.sibs.size == 1 + k) "fix: proof shape" >>= fun _ =>
  ckE (πF.vF.all (·.all k3Ok) && πF.pfinal.all k3Ok && πF.roots.all dgOk && πF.vals.all (·.all based) && πF.sibs.all (·.all dgOk) &&
       z.all based && ctx.all based) "fix: non-canonical limb" >>= fun _ =>
  ckE (πF.pos.all (· < 2 ^ X.nD)) "fix: position range" >>= fun _ =>
  let msgs := fixMsgs k ctx πF.vF πF.roots πF.pfinal
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if fixNl k X.l i == 0 then [] else FSf (z :: (msgs.extract 0 (i + 1)).toList) (fixNl k X.l i)
  ckE (chals.all (·.all based)) "fix: non-canonical Fiat-Shamir challenge limb" >>= fun _ =>
  let cs := K3.ofLimbs chals[1]!
  let alphas : Array K3 := (Array.range (k + 1)).map fun w => K3.ofLimbs chals[2 + w]!
  let xs : Array Nat := chals[3 + k]!.toArray.map (· % 2 ^ X.nD)
  ckE (πF.pos == xs) "fix: positions differ from the FS query challenge" >>= fun _ =>
  let half0 := 2 ^ (X.nD - 1)
  let sels : Array (Array Nat) := (Array.range (4 + k)).map fun j =>
    if j == 0 then treeSel X F 0 πF.pos else if j < 4 then #[] else treeSel X 0 j πF.pos
  -- adapter: the side proof laid out as a `FlatProof` so that `treeCheck` / `friSteps` are reused unchanged (tree 0 = VK tree, trees 1..3 empty)
  let z5 : Dg5 := [0, 0, 0, 0, 0]
  let πa : FlatProof :=
    { roots := #[vk.root, z5, z5, z5] ++ πF.roots, vT := #[], vQ := #[], pfinal := πF.pfinal, pos := πF.pos,
      vals := #[πF.vals[0]!, #[], #[], #[]] ++ πF.vals.extract 1 (1 + k),
      sibs := #[πF.sibs[0]!, #[], #[], #[]] ++ πF.sibs.extract 1 (1 + k) }
  (List.range (4 + k)).forM (treeCheck X Hf πa #[F, 0, 0, 0] half0 sels) >>= fun _ =>
  let pts := openPts X zeta
  let dN := 2 ^ X.nD
  (List.range X.r).forM (fun o => ckE (pts[o]!.pow dN != K3.ofG (VF.pow X.dShift dN)) "fix: OffDom fails") >>= fun _ =>
  let ops := fixOps X vk.cols cs πF.vF
  let baseAt (c idx : Nat) : G :=
    UInt64.ofNat πa.vals[0]![lb sels[0]! ((idx % half0) * 2 * F + (idx / half0) * F + c)]!
  let word0 := deepWord X pts ops baseAt
  πF.pos.toList.forM (fun q =>
    let g0 := q % half0
    friSteps X πa.vals sels alphas q (List.range' 1 k)
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt X 0 g0) alphas[0]!) g0 >>= fun r =>
    ckE (r.1 == K3.horner πF.pfinal (K3.ofG (yAt X (k + 1) r.2))) s!"fix: FRI final polynomial mismatch, query {q}")


theorem verifyFix_eq_verifyFix' (vk : VK) (H : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : K3) (πF : FixProof) :
    verifyFix vk H FSf z ctx zeta πF = verifyFix' vk (hFix H) FSf z ctx zeta πF := rfl

def verifyOnlineE' (vk : VK) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Except String Unit :=
  let X := vk.X
  let nB := 4
  let k := X.k
  let ncq := X.nc + X.nq
  let lay := fixLayout X vk.cols
  ckE (allCanonOnline z π) "non-canonical limb (>= p)" >>= fun _ =>
  ckE (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) "tree count" >>= fun _ =>
  ckE (π.vT.size == X.nc && π.vQ.size == X.nq && π.pfinal.size == X.d && π.pos.size == X.l) "proof shape" >>= fun _ =>
  (List.range X.nc).forM (fun c =>
    ckE (π.vT[c]!.size == vTLen X c) "vT shape") >>= fun _ =>
  ckE (π.pos.all (· < 2 ^ X.nD)) "position range" >>= fun _ =>
  -- (i) Fiat-Shamir
  let pfEnc := π.pfinal.toList.flatMap K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl X
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if nlOf i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (nlOf i)
  ckE (chals.all (·.all based)) "non-canonical Fiat-Shamir challenge limb" >>= fun _ =>
  let coins0 := k3s chals[1]! X.nCoins[0]!
  let coins1 := k3s chals[2]! X.nCoins[1]!
  let alpha := K3.ofLimbs chals[3]!
  let zeta := K3.ofLimbs chals[4]!
  let cs := K3.ofLimbs chals[6]!
  let alphas : Array K3 := (Array.range (k + 1)).map fun w => K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := chals[8 + k]!.toArray.map (· % 2 ^ X.nD)
  ckE (π.pos == xs) "positions differ from the FS query challenge" >>= fun _ =>
  -- (ii') the fixed-column side proof: `πF.vF` are the values of the VK polynomials at the opening points
  verifyFix' vk Hf FSf z (fixCtx π zeta) zeta πF >>= fun _ =>
  let vF := πF.vF
  let half0 := 2 ^ (X.nD - 1)
  let (W, rank) := blockLayout X
  -- (iii) Merkle
  let sels : Array (Array Nat) := (Array.range (nB + k)).map fun j => treeSel X (W.getD j 0) j π.pos
  (List.range (nB + k)).forM (treeCheck X H π W half0 sels) >>= fun _ =>
  -- (iv) DeepCheck
  let slots : Array K3 := X.derived.toList.foldl (fun (slots : Array K3) (be : Nat × Nat) => slots.push (K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := vF[lay.zh]![0]!
  let curNxt := (List.range X.nc).foldl
    (fun (st : Array K3 × Array K3) c =>
      match X.colKind[c]! with
      | 0 => (st.1.set! c π.vT[c]![0]!, st.2.set! c (if X.r ≥ 2 then π.vT[c]![1]! else K3.zero))
      | 1 => (st.1.set! c vF[lay.pre[c]!]![0]!, st.2.set! c vF[lay.pre[c]!]![1]!)
      | _ => st)
    (Array.replicate ncq K3.zero, Array.replicate ncq K3.zero)
  X.pubOf.toList.forM (fun c =>
    ckE (c < X.nc && X.colKind[c]! == 2) "pubOf" >>= fun _ =>
    ckE (π.vT[c]![0]!).isBase "public value not in the base field") >>= fun _ =>
  let pub : Array G := X.pubOf.map fun c => (π.vT[c]![0]!).c0
  ckE (!zh.isZero) "zeta in H" >>= fun _ =>
  let lhs := (X.tabs.foldl (fun (st : K3 × K3 × Nat) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                  bc := t.chip.baseCols }
    let (s, pw) := cvals.foldl (fun (a : K3 × K3) v => (K3.add a.1 (K3.mul a.2 v), K3.mul a.2 alpha)) (K3.zero, st.2.1)
    let mult := if t.hN < X.hN then vF[lay.zout[st.2.2]!]![0]! else K3.one
    (K3.add st.1 (K3.mul s mult), pw, st.2.2 + 1)) (K3.zero, K3.one, 0)).1
  let zN := K3.pow zeta X.hN
  let qsum := (List.range X.nq).foldl
    (fun qs j => K3.add qs (K3.mul (K3.mul (K3.pow K3.gen (j % 3)) (K3.pow zN (j / 3))) π.vQ[j]!)) K3.zero
  ckE (lhs == K3.mul zh qsum) "DeepCheck fails" >>= fun _ =>
  -- (v) OffDom
  let pts := openPts X zeta
  let dN := 2 ^ X.nD
  pts.toList.forM (fun pt => ckE (pt.pow dN != K3.ofG (VF.pow X.dShift dN)) "OffDom fails") >>= fun _ =>
  -- (vi) residual public relation
  ckE (X.pubCheck slots pub) "public relation fails" >>= fun _ =>
  -- (vi') preprocessed columns: the committed openings equal the fixed polynomial (the VK's) at every opening point
  (List.range X.nc).forM (fun c =>
    ckE (X.colKind[c]! != 1 || (List.range X.r).all (fun o => π.vT[c]![o]! == vF[lay.pre[c]!]![o]!)) "pre opening mismatch") >>= fun _ =>
  -- (vii) FRI
  let ops := openingList X cs π.vT π.vQ
  let baseAt (c idx : Nat) : G :=
    let b := X.blockOf[c]!
    let leafPos := (idx % half0) * 2 * W[b]! + (idx / half0) * W[b]! + rank[c]!
    UInt64.ofNat π.vals[b]![lb sels[b]! leafPos]!
  let word0 := deepWord X pts ops baseAt
  π.pos.toList.forM (fun q =>
    let g0 := q % half0
    friSteps X π.vals sels alphas q (List.range' 1 k)
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt X 0 g0) alphas[0]!) g0 >>= fun r =>
    ckE (r.1 == K3.horner π.pfinal (K3.ofG (yAt X (k + 1) r.2))) s!"FRI final polynomial mismatch, query {q}")


def verifyOnline' (vk : VK) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Bool :=
  match verifyOnlineE' vk H Hf FS FSf z π πF with | .ok _ => true | .error _ => false

theorem verifyOnlineE_eq_verifyOnlineE' (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) :
    verifyOnlineE vk H FS FSf z π πF = verifyOnlineE' vk H (hFix H) FS FSf z π πF := rfl

theorem verifyOnline_eq_verifyOnline' (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) :
    verifyOnline vk H FS FSf z π πF = verifyOnline' vk H (hFix H) FS FSf z π πF := rfl

end NockvmE2E.Exec.V
