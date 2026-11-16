/-
  NockvmE2E/Exec/VK.lean   (executed, Mathlib-free, no proofs)

  Verifier key for the J-8 flat verifier.  The O(n) steps of `verifyFlat` all compute values of FIXED,
  instance-determined polynomials at the opening points: the kind-1 (`pre`) columns, the trace vanishing polynomial `zh = Z_H`, and
  `zout t = ∏_{i ∈ [hN_t, hN)} (x - hShift·hGen^i)` (the multiplier `mult_t`).  `setup` (transparent, O(n log n), re-runnable by anyone from the
  instance) runs every instance-only gate once, computes these polynomials, their LDE on `D`, and ONE Merkle tree over them (`vk.root`).
  `FixProof` is one batched DEEP-FRI proof (same code as the main proof: `deepWord`/`friSteps`/`treeCheck`) that the claimed values
  `vF[j][o] = fix_j(pts[o])` are right; its tree tags are shifted by 64 (`hFix`) and its Fiat-Shamir oracle is a separate function `FSf`,
  so it is an independent random oracle.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.ProverField
import NockvmE2E.Exec.VKSetupR
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J

/-- a fixed polynomial of the VK: a kind-1 column, the trace vanishing polynomial, or table t's complement factor -/
inductive FixCol where
  | pre (c : Nat)
  | zh
  | zout (t : Nat)
  deriving BEq, Repr, Inhabited

def tabHN (X : ExecInst) (t : Nat) : Nat := (X.tabs[t]?.map (·.hN)).getD 0

/-- the fixed columns, in VK tree order: `pre c` for every kind-1 column, then `zh`, then `zout t` for every table with `hN_t < hN` -/
def fixCols (X : ExecInst) : Array FixCol :=
  ((Array.range X.nc).filter (fun c => X.colKind[c]! == 1)).map FixCol.pre ++ #[FixCol.zh] ++
  ((Array.range X.tabs.size).filter (fun t => tabHN X t < X.hN)).map FixCol.zout

/-- number of values opened for a fixed column: `r` for `pre`, 1 (at `ζ`) for `zh`/`zout` -/
def fixLen (X : ExecInst) : FixCol → Nat
  | .pre _ => X.r
  | _ => 1

structure FixLay where
  pre : Array Nat     -- global column -> fixed-column rank (kind 1 only)
  zh : Nat
  zout : Array Nat    -- table -> rank (tables with hN_t < hN only)

def fixLayout (X : ExecInst) (cols : Array FixCol) : FixLay :=
  (List.range cols.size).foldl (fun (st : FixLay) j =>
    match cols[j]! with
    | .pre c => { st with pre := st.pre.set! c j }
    | .zh => { st with zh := j }
    | .zout t => { st with zout := st.zout.set! t j })
    { pre := Array.replicate X.nc 0, zh := 0, zout := Array.replicate X.tabs.size 0 }

/-- the verifier key: the instance with the `pre` arrays erased (no O(n) data online), the fixed columns, and the Merkle root of their LDE -/
structure VK where
  X : ExecInst
  cols : Array FixCol
  root : Dg5

/-- one batched DEEP-FRI proof of the claimed fixed-column values `vF` (shape of `FlatProof`: tree 0 = the VK tree, then `k` FRI trees) -/
structure FixProof where
  vF : Array (Array K3)
  pfinal : Array K3
  pos : Array Nat
  roots : Array Dg5               -- k FRI roots
  vals : Array (Array Nat)        -- 1 + k trees
  sibs : Array (Array (List Nat)) -- 1 + k trees
  deriving Inhabited

/-- tree tags of the side proof are shifted by 64: its Merkle hash is a different oracle from the main proof's -/
def fixTagOff : Nat := 64
def hFix (H : HFn) : HFn := fun inp =>
  match inp with
  | t :: j :: rest => if t == tagNode then H (t :: (j + fixTagOff) :: rest) else H inp
  | _ => H inp

/-! ### setup gates: every check that reads the instance only (was in `verifyFlatE`, O(n) for `genOrderOk`/`pre`) -/

def instCanon (X : ExecInst) : Bool :=
  let gOk (x : G) : Bool := based x.toNat
  gOk X.dShift && gOk X.dGen && gOk X.hGen && gOk X.hShift && k3Ok X.ppt && X.pre.all (·.all gOk) && X.tabs.all (fun t => chipCanon t.chip)

/-- all instance-only gates of `verifyFlatE`, plus `r ≥ 2` (the next-row opening of a kind-1 column is `vF[·][1]`) and the `blockOf` range -/
def setupGates (X : ExecInst) : Bool :=
  instCanon X && inpCanOk X.pubIn &&
  X.colKind.size == X.nc && X.blockOf.size == X.nc + X.nq && X.pre.size == X.nc && X.nCoins.size == 2 &&
  X.nD ≥ X.k + 1 && X.nq % 3 == 0 && X.r ≥ 2 && X.hN ≥ 1 && X.l ≥ 1 &&
  paramsOk X && tabsOk X &&
  (List.range (X.nc + X.nq)).all (fun c => X.blockOf[c]! < 4)

/-! ### polynomial products (setup is untrusted computation: the root is re-derivable by anyone) -/

-- (the products and the LDE of the setup are in `VKSetupR.lean`: `prodLinR`, `cosetLdeR`; total and structurally recursive)

def orbitPts (X : ExecInst) : Array G := Id.run do
  let mut a : Array G := Array.mkEmpty X.hN
  let mut x : G := X.hShift
  for _ in [0:X.hN] do
    a := a.push x
    x := VF.mul x X.hGen
  return a

/-- the coefficients of fixed polynomial `fc` (the mathematical objects `FixFail` is stated against) -/
def fixPoly (X : ExecInst) (orb : Array G) : FixCol → Array G
  | .pre c => X.pre[c]!
  | .zh => prodLinR orb 0 X.hN
  | .zout t => prodLinR orb (tabHN X t) X.hN

/-! ### Merkle (same skeleton as `Verify.lean`; copies of the `FlatProver` builders over an arbitrary hash) -/

def fxParRange {α : Type} [Inhabited α] (n chunk : Nat) (f : Nat → α) : Array α := Id.run do
  let nch := (n + chunk - 1) / chunk
  let tasks := (Array.range nch).map fun ci =>
    Task.spawn fun _ => (Array.range (min chunk (n - ci * chunk))).map fun i => f (ci * chunk + i)
  return tasks.foldl (fun acc t => acc ++ t.get) #[]

def fxLevelsUp (H : HFn) (j : Nat) (bot : Array Dg5) (m : Nat) : Array (Array Dg5) := Id.run do
  let mut lv : Array (Array Dg5) := Array.replicate (m + 1) #[]
  lv := lv.set! m bot
  for t in [0:m] do
    let d := m - 1 - t
    let ch := lv[d + 1]!
    lv := lv.set! d (fxParRange (2 ^ d) 256 fun i => H ([tagNode, j, 2 ^ d + i] ++ ch[2 * i]! ++ ch[2 * i + 1]!))
  return lv

/-- fuel version (total): `cnt` is enough fuel, the recursion depth is `⌈log₂ cnt⌉`; `cnt = 0` returns `[]` (unreachable: `W ≥ 1`) -/
def fxSubRootF (H : HFn) (j : Nat) (leafAt : Nat → G) : Nat → Nat → Nat → Nat → Dg5
  | 0, _, _, _ => []
  | f + 1, idx, cnt, lo =>
    if cnt == 1 then [(leafAt lo).toNat, 0, 0, 0, 0] else
    let L := (cnt + 1) / 2
    H ([tagNode, j, idx] ++ fxSubRootF H j leafAt f (2 * idx) L lo ++ fxSubRootF H j leafAt f (2 * idx + 1) (cnt - L) (lo + L))

def fxSubRoot (H : HFn) (j : Nat) (leafAt : Nat → G) (idx cnt lo : Nat) : Dg5 := fxSubRootF H j leafAt cnt idx cnt lo

def fxRagLevels (H : HFn) (j W half : Nat) (lde : Array (Array G)) : Array (Array Dg5) :=
  let groups := fxParRange half 8 fun g =>
    let side (s : Nat) : Dg5 := fxSubRoot H j (fun r => (lde[r]!)[g + s * half]!) (2 * (half + g) + s) W 0
    H ([tagNode, j, half + g] ++ side 0 ++ side 1)
  fxLevelsUp H j groups (Nat.log2 half)

partial def fxOpenGo (sp : TSpec) (nodeAt : Nat → Dg5) (sel : Array Nat) (idx lo cnt : Nat) : Array Dg5 :=
  if cnt == 1 then #[] else
  let L := sp.split cnt
  let a := lb sel lo
  let b := lb sel (lo + L)
  let c := lb sel (lo + cnt)
  if b > a && c > b then fxOpenGo sp nodeAt sel (2 * idx) lo L ++ fxOpenGo sp nodeAt sel (2 * idx + 1) (lo + L) (cnt - L)
  else if b > a then #[nodeAt (2 * idx + 1)] ++ fxOpenGo sp nodeAt sel (2 * idx) lo L
  else #[nodeAt (2 * idx)] ++ fxOpenGo sp nodeAt sel (2 * idx + 1) (lo + L) (cnt - L)

def fxNodeAt (lv : Array (Array Dg5)) (idx : Nat) : Dg5 :=
  let d := Nat.log2 idx
  (lv[d]!)[idx - 2 ^ d]!

/-! ### setup -/

/-- `setup`'s output with the prover-side data (the polynomials, their LDE and the tree). `vk` is the public part. -/
structure VKData where
  vk : VK
  polys : Array (Array G)
  lde : Array (Array G)
  levels : Array (Array Dg5)

/-- transparent setup: `none` iff an instance gate fails.  Cost O(n log² n) (subproduct trees) + one NTT and one tree over the fixed columns. -/
def setupData (X : ExecInst) (H : HFn) : Option VKData :=
  if !setupGates X then none else
  let cols := fixCols X
  let orb := orbitPts X
  let polys := cols.map (fixPoly X orb)
  let half0 := 2 ^ (X.nD - 1)
  let lde := polys.map fun p => cosetLdeR p X.nD X.dGen
  let lv := fxRagLevels (hFix H) 0 cols.size half0 lde
  some { vk := { X := { X with pre := X.pre.map (fun _ => #[]) }, cols := cols, root := lv[0]![0]! },
         polys := polys, lde := lde, levels := lv }

def setup (X : ExecInst) (H : HFn) : Option VK := (setupData X H).map (·.vk)

/-! ### the side proof -/

/-- Fiat-Shamir context of the side proof: the four block roots of the main proof and `ζ` -/
def fixCtx (π : FlatProof) (zeta : K3) : List Nat := (π.roots.extract 0 4).toList.flatMap id ++ zeta.limbs

/-- the batched openings `(fixed column rank, point index, cs^i, value)` -/
def fixOps (X : ExecInst) (cols : Array FixCol) (cs : K3) (vF : Array (Array K3)) : Array (Nat × Nat × K3 × K3) :=
  ((List.range cols.size).foldl
    (fun (st : Array (Nat × Nat × K3 × K3) × K3) j =>
      (List.range (fixLen X cols[j]!)).foldl
        (fun (st : Array (Nat × Nat × K3 × K3) × K3) o => (st.1.push (j, o, st.2, vF[j]![o]!), K3.mul st.2 cs)) st)
    (#[], K3.one)).1

def fixNl (k l i : Nat) : Nat := if i == 0 then 0 else if i ≤ 2 + k then 3 else if i == 3 + k then l else 0

def fixMsgs (k : Nat) (ctx : List Nat) (vF : Array (Array K3)) (roots : Array Dg5) (pfinal : Array K3) : Array (List Nat) :=
  #[ctx, vF.toList.flatMap (fun a => a.toList.flatMap K3.limbs), []] ++ roots.extract 0 k ++ #[pfinal.toList.flatMap K3.limbs]

/-- the honest side prover (untrusted) -/
def proveFix (H : HFn) (FSf : FSFn) (D : VKData) (z ctx : List Nat) (zeta : K3)
    (tamperVF : Option (Nat × Nat) := none) : FixProof := Id.run do
  let X := D.vk.X
  let cols := D.vk.cols
  let Hf := hFix H
  let k := X.k
  let nD := X.nD
  let Dn := 2 ^ nD
  let half0 := Dn / 2
  let F := cols.size
  let pts := openPts X zeta
  let vF0 : Array (Array K3) := (Array.range F).map fun j =>
    (Array.range (fixLen X cols[j]!)).map fun o => K3.hornerG D.polys[j]! pts[o]!
  -- test only: a CONSISTENT forgery (the claimed value `(j, o)` is changed by 1 before Fiat-Shamir; the FRI is over the true polynomials)
  let vF := match tamperVF with
    | some (j, o) => vF0.modify j (·.modify o (fun v => K3.add v K3.one))
    | none => vF0
  let vFmsg := vF.toList.flatMap (fun a => a.toList.flatMap K3.limbs)
  let mut msgs : Array (List Nat) := #[ctx, vFmsg, []]
  let chalAt (ms : Array (List Nat)) (i nl : Nat) : List Nat := FSf (z :: (ms.extract 0 (i + 1)).toList) nl
  let cs := K3.ofLimbs (chalAt msgs 1 3)
  let ops := fixOps X cols cs vF
  let lde := D.lde
  let mut word : Array K3 := fxParRange Dn 64 fun idx => deepWord X pts ops (fun c i => (lde[c]!)[i]!) idx
  let mut friWords : Array (Array K3) := #[]
  let mut friLv : Array (Array (Array Dg5)) := #[]
  let mut alphaW := K3.ofLimbs (chalAt msgs 2 3)
  for w in [0:k + 1] do
    let halfw := 2 ^ (nD - w - 1)
    let wd0 := word
    let aw := alphaW
    word := fxParRange halfw 256 fun g => foldK3 wd0[g]! wd0[g + halfw]! (yAt X w g) aw
    if w < k then
      let wd := word
      let hf := halfw / 2
      let leaves : Array Dg5 := fxParRange halfw 256 fun p => (wd[p / 2 + (p % 2) * hf]!).limbs ++ [0, 0]
      let lv := fxLevelsUp Hf (4 + w) leaves (nD - w - 1)
      friWords := friWords.push wd
      friLv := friLv.push lv
      msgs := msgs.push lv[0]![0]!
      alphaW := K3.ofLimbs (chalAt msgs (3 + w) 3)
  let pfinal : Array K3 := #[word[0]!]
  msgs := msgs.push (pfinal.toList.flatMap K3.limbs)
  let pos : Array Nat := (chalAt msgs (3 + k) X.l).toArray.map (· % Dn)
  let mut vals : Array (Array Nat) := #[]
  let mut sibs : Array (Array Dg5) := #[]
  for j in [0:1 + k] do
    if j == 0 then
      let sel := treeSel X F 0 pos
      vals := vals.push (sel.map fun p => (lde[(p % (2 * F)) % F]!)[p / (2 * F) + ((p % (2 * F)) / F) * half0]!.toNat)
      sibs := sibs.push (fxOpenGo (ragSpec F half0) (fxNodeAt D.levels) sel 1 0 (ragSpec F half0).total)
    else
      let w := j - 1
      let sel := treeSel X 0 (3 + j) pos
      let wd := friWords[w]!
      let hf := 2 ^ (nD - w - 2)
      vals := vals.push (sel.flatMap fun p => ((wd[p / 2 + (p % 2) * hf]!).limbs).toArray)
      let sp := friSpec (2 ^ (nD - w - 1))
      sibs := sibs.push (fxOpenGo sp (fxNodeAt friLv[w]!) sel 1 0 sp.total)
  return { vF := vF, pfinal := pfinal, pos := pos, roots := msgs.extract 3 (3 + k), vals := vals, sibs := sibs.map (·.toList.toArray) }

/-- verify the side proof against `vk.root`: on success every `πF.vF[j][o]` is the value of fixed polynomial `j` at `openPts X ζ [o]` (up to FRI soundness) -/
def verifyFix (vk : VK) (H : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : K3) (πF : FixProof) : Except String Unit :=
  let X := vk.X
  let k := X.k
  let F := vk.cols.size
  let Hf := hFix H
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

/-! ### JSON (`"version": 1`) -/

def FixProof.toJson (p : FixProof) : Json :=
  Json.mkObj [("version", natJ 1),
    ("vF", Json.arr (p.vF.map fun a => Json.arr (a.map k3J))),
    ("pfinal", Json.arr (p.pfinal.map k3J)),
    ("pos", Json.arr (p.pos.map natJ)),
    ("roots", Json.arr (p.roots.map limbsJ)),
    ("trees", Json.arr ((p.vals.zip p.sibs).map fun (v, s) =>
      Json.mkObj [("vals", Json.arr (v.map natJ)), ("sibs", Json.arr (s.map fun x => limbsJ x))]))]

def FixProof.ofJson (j : Json) : Except String FixProof := do
  if (← natE "version" (get j "version")) != 1 then throw "FixProof: version != 1"
  let trees := arr (get j "trees")
  pure { vF := ← (arr (get j "vF")).mapM fun a => (arr a).mapM (k3E "vF")
         pfinal := ← (arr (get j "pfinal")).mapM (k3E "pfinal")
         pos := ← natsE "pos" (get j "pos")
         roots := ← (arr (get j "roots")).mapM fun x => (limbsE "roots" x)
         vals := ← trees.mapM fun t => (arr (get t "vals")).mapM (limbE "vals")
         sibs := ← trees.mapM fun t => (arr (get t "sibs")).mapM fun x => limbsE "sibs" x }

end NockvmE2E.Exec.V
