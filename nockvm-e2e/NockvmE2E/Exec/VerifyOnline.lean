/-
  NockvmE2E/Exec/VerifyOnline.lean   (pcs-base, ; executed, Mathlib-free, no proofs)

  `verifyOnlineE vk H FS FSf z π πF` = `verifyFlatE` with the six O(n) steps removed:
   * `genOrderOk`/`paramsOk`, `tabsOk`, the instance part of `allCanon` (incl. `pre`), `inpCanOk`, the shape gates: run once in `setup` (`setupGates`);
   * `zh` and `mult_t`: the side-proof values `vF[zh][0]`, `vF[zout t][0]` (`verifyFix` makes them the true evaluations);
   * `curNxt` kind 1 and the pre-opening check: `vF[pre c][0..1]` instead of `hornerG X.pre[c]`.
  Everything else is the text of `verifyFlatE` (same FS rounds, same Merkle/FRI code).  Every remaining loop is bounded by l, k, nD, c, r, #tabs, |DAG|,
  |z|, |π| or |πF|.
-/
import NockvmE2E.Exec.VK
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF

/-- canonicity of the statement and the proof (the instance part is `instCanon`, done in `setup`) -/
def allCanonOnline (z : List Nat) (π : FlatProof) : Bool :=
  z.all based && π.roots.all dgOk && π.vT.all (·.all k3Ok) && π.vQ.all k3Ok && π.pfinal.all k3Ok &&
  π.vals.all (·.all based) && π.sibs.all (·.all dgOk)

def verifyOnlineE (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Except String Unit :=
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
  verifyFix vk H FSf z (fixCtx π zeta) zeta πF >>= fun _ =>
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

def verifyOnline (vk : VK) (H : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Bool :=
  match verifyOnlineE vk H FS FSf z π πF with | .ok _ => true | .error _ => false

end NockvmE2E.Exec.V
