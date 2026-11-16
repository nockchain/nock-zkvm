/-
  NockvmE2E/Exec/Verify.lean   (executed, Mathlib-free, no proofs)

  `verifyFlat X H FS z π : Bool`  -- the flat verifier, with hash `H` and Fiat-Shamir `FS` as arguments.

  Protocol read here (ASSUMPTIONS marked [A] are the points to align with `compiledRoundsK` in the compiled rounds):
   * rounds, in order, message -> challenge squeezed after it  [A: the round/challenge map]:
       0 ->- ; 1 root0->coins0 (3*nCoins0 limbs) ; 2 root1->coins1 ; 3 root2->α ; 4 root3->ζ ; 5 (vT,vQ)->- ; 6 ->cs ;
       7 ->α_0 ; 7+w root_{3+w}->α_w (w=1..k) ; 8+k pfinal->l query limbs (each `mod 2^nD`).
   * FS key of round i = [z, m_1, .., m_i] (lists of limbs; `m_i = []` for unit messages); `FS key nl` returns `nl` limbs.  [A: salt is
     part of z, not per message]
   * Merkle: leaf digests are RAW (`[v,0,0,0,0]` base, `[c0,c1,c2,0,0]` K3); node = `H([tagNode, j, idx] ++ l ++ r)`, `j` = tree number
     (4 RAP blocks, then FRI words 1..k), `idx` = heap numbering of the path (root 1, children 2i, 2i+1).
     RAP block skeleton: perfect over the 2^(nD-1) fold-partner groups; a group = two balanced (left = ceil) subtrees of exactly W leaves
     (side 0 = domain index g, side 1 = g + 2^(nD-1)); leaf = g*2W + side*W + (rank of the column in the block).
     FRI word w: domain size 2^(nD-w), perfect tree, leaf `2*(t mod half) + t/half`.
     Openings: the pruned frontier in pre-order (a sibling digest is listed before the sub-opening it is pruned beside).
   * FRI: arity 2, word 0 = Σ_i cs^i (col_i(y) - v_i)/(y - pt_i), fold (f(y)+f(-y))/2 + α (f(y)-f(-y))/(2y).
-/
import NockvmE2E.Exec.VField
import NockvmE2E.Exec.Flat
import NockvmE2E.Exec.Dag
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF

abbrev Dg5 := List Nat
abbrev HFn := List Nat → Dg5
abbrev FSFn := List (List Nat) → Nat → List Nat

def tagNode : Nat := 0x65326506

/-- A tree skeleton: `total` leaves; `split cnt` = size of the left part of a node over `cnt` leaves. -/
structure TSpec where
  total : Nat
  split : Nat → Nat

/-- RAP block: `half = 2^(nD-1)` groups of `2W` leaves. -/
def ragSpec (W half : Nat) : TSpec :=
  { total := half * 2 * W
    split := fun cnt => if cnt > 2 * W then cnt / 2 else if cnt == 2 * W then W else (cnt + 1) / 2 }
def friSpec (total : Nat) : TSpec := { total := total, split := fun cnt => cnt / 2 }

/-- binary search by structural recursion on a fuel: `lbGo a x f lo hi` (fuel `f ≥ hi - lo` suffices, every step shrinks `hi - lo`) -/
def lbGo (a : Array Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      (if a[(lo + hi) / 2]! < x then lbGo a x f ((lo + hi) / 2 + 1) hi else lbGo a x f lo ((lo + hi) / 2))
    else lo
/-- lower bound: the first index whose entry is `≥ x` (`a` sorted) -/
def lb (a : Array Nat) (x : Nat) : Nat := lbGo a x (a.size + 1) 0 a.size

/-- Root recomputation of one pruned batch opening (the recursion of `getPutativeBatchRootAddressedM`): `sel` = sorted selected leaves,
`leaf r` = digest of the `r`-th selected leaf, `sibs` = frontier digests (pre-order), `s` = next unused sibling. -/
def goRootF (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5) :
    Nat → Nat → Nat → Nat → Nat → Option (Dg5 × Nat)
  | 0, _, _, _, _ => none
  | f + 1, idx, lo, cnt, s =>
  if cnt == 1 then
    let r := lb sel lo
    if sel[r]? == some lo then some (leaf r, s) else none
  else
    let L := sp.split cnt
    if L == 0 || L ≥ cnt then none else
    let a := lb sel lo
    let b := lb sel (lo + L)
    let c := lb sel (lo + cnt)
    let node (l r : Dg5) : Dg5 := H ([tagNode, j, idx] ++ l ++ r)
    if b > a && c > b then do
      let (l, s1) ← goRootF H sp j sel leaf sibs f (2 * idx) lo L s
      let (r, s2) ← goRootF H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) s1
      some (node l r, s2)
    else if b > a then do
      let sib ← sibs[s]?
      let (l, s1) ← goRootF H sp j sel leaf sibs f (2 * idx) lo L (s + 1)
      some (node l sib, s1)
    else if c > b then do
      let sib ← sibs[s]?
      let (r, s1) ← goRootF H sp j sel leaf sibs f (2 * idx + 1) (lo + L) (cnt - L) (s + 1)
      some (node sib r, s1)
    else none

/-- Root recomputation of one pruned batch opening (the recursion of `getPutativeBatchRootAddressedM`): `sel` = sorted selected leaves,
`leaf r` = digest of the `r`-th selected leaf, `sibs` = frontier digests (pre-order), `s` = next unused sibling.
Total: structural recursion on a fuel, `cnt` (every child has fewer leaves, checked by the `L == 0 || L ≥ cnt` guard). -/
def goRoot (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5)
    (idx lo cnt s : Nat) : Option (Dg5 × Nat) :=
  goRootF H sp j sel leaf sibs cnt idx lo cnt s

/-- the fuel suffices: any fuel `≥ cnt` gives the same result -/
theorem goRootF_fuel (H : HFn) (sp : TSpec) (j : Nat) (sel : Array Nat) (leaf : Nat → Dg5) (sibs : Array Dg5) :
    ∀ (n f f' idx lo cnt s : Nat), cnt ≤ n → n ≤ f → n ≤ f' →
      goRootF H sp j sel leaf sibs f idx lo cnt s = goRootF H sp j sel leaf sibs f' idx lo cnt s := by
  intro n
  induction n with
  | zero =>
    intro f f' idx lo cnt s hc hf hf'
    have h0 : cnt = 0 := by omega
    subst h0
    cases f <;> cases f' <;> simp [goRootF]
    all_goals (by_cases h : sp.split 0 = 0 <;> simp [h])
  | succ n ih =>
    intro f f' idx lo cnt s hc hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [goRootF]
    by_cases h1 : cnt == 1
    · simp [h1]
    · simp only [h1, ite_false, Bool.false_eq_true]
      by_cases hL : (sp.split cnt == 0 || decide (sp.split cnt ≥ cnt)) = true
      · simp [hL]
      · have hne : sp.split cnt ≠ 0 := by intro h; apply hL; simp [h]
        have hlt : sp.split cnt < cnt := Nat.lt_of_not_ge (fun h => hL (by simp [h]))
        have e1 := fun idx lo s => ih g g' idx lo (sp.split cnt) s (by omega) (by omega) (by omega)
        have e2 := fun idx lo s => ih g g' idx lo (cnt - sp.split cnt) s (by omega) (by omega) (by omega)
        simp only [hL, ite_false, Bool.false_eq_true, e1, e2]

/-- insert into a strictly increasing list (no duplicates) -/
def insertD (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: insertD x ys
/-- sorted ascending, duplicates removed (insertion; structural) -/
def sortedDistinct (a : Array Nat) : Array Nat := (a.toList.foldl (fun acc x => insertD x acc) []).toArray

def k3Ok (x : K3) : Bool := x.c0 < P && x.c1 < P && x.c2 < P
def dgOk (l : List Nat) : Bool := l.length == 5 && l.all based

/-- chunks of 3 limbs as K3 -/
def k3s (l : List Nat) (n : Nat) : Array K3 := (Array.range n).map fun i => K3.ofLimbs (l.drop (3 * i))

/-- column kind of a global column (quotient columns are kind 3) -/
def kindG (X : ExecInst) (c : Nat) : Nat := if c < X.nc then X.colKind[c]! else 3

/-- number of opened values a column carries in the proof: `r` for kinds 0/1, `1` for publics (kind 2), none otherwise -/
def vTLen (X : ExecInst) (c : Nat) : Nat := match kindG X c with | 0 | 1 => X.r | 2 => 1 | _ => 0

/-- (leaves per group-side `W_b`, rank of every column inside its block) -/
def blockLayout (X : ExecInst) : Array Nat × Array Nat :=
  (List.range (X.nc + X.nq)).foldl
    (fun (st : Array Nat × Array Nat) c =>
      let b := X.blockOf[c]!
      if b < 4 then (st.1.modify b (· + 1), st.2.set! c st.1[b]!) else st)
    (Array.replicate 4 0, Array.replicate (X.nc + X.nq) 0)

/-- sorted selected leaves of tree `j` for the query positions `pos` -/
def treeSel (X : ExecInst) (Wb j : Nat) (pos : Array Nat) : Array Nat :=
  if j < 4 then
    (if Wb == 0 then #[] else
      (sortedDistinct (pos.map (· % 2 ^ (X.nD - 1)))).flatMap fun g => (Array.range (2 * Wb)).map (g * 2 * Wb + ·))
  else
    let halfw := 2 ^ (X.nD - (j - 3) - 1)
    (sortedDistinct (pos.map (· % halfw))).flatMap fun g => #[2 * g, 2 * g + 1]

/-- the clear DEEP message `(vT, vQ)` as limbs -/
def deepMsg (vT : Array (Array K3)) (vQ : Array K3) : List Nat :=
  vT.toList.flatMap (fun a => a.toList.flatMap K3.limbs) ++ vQ.toList.flatMap K3.limbs

/-- opening points: `ζ·hGen^o` (`o < r`), then `ppt`, then `ζ` -/
def openPts (X : ExecInst) (zeta : K3) : Array K3 :=
  let st := (List.range X.r).foldl
    (fun (st : Array K3 × K3) _ => (st.1.push (K3.mul zeta st.2), K3.smul X.hGen st.2)) (#[], K3.one)
  (st.1.push X.ppt).push zeta

/-- the batched openings `(column, point index, cs^i, value)` in the order of `e` -/
def openingList (X : ExecInst) (cs : K3) (vT : Array (Array K3)) (vQ : Array K3) : Array (Nat × Nat × K3 × K3) :=
  ((List.range (X.nc + X.nq)).foldl
    (fun (st : Array (Nat × Nat × K3 × K3) × K3) c =>
      match kindG X c with
      | 0 | 1 => (List.range X.r).foldl
          (fun (st : Array (Nat × Nat × K3 × K3) × K3) o => (st.1.push (c, o, st.2, vT[c]![o]!), K3.mul st.2 cs)) st
      | 2 => (List.range X.r).foldl
          (fun (st : Array (Nat × Nat × K3 × K3) × K3) _ => (st.1.push (c, X.r, st.2, vT[c]![0]!), K3.mul st.2 cs)) st
      | 3 => (st.1.push (c, X.r + 1, st.2, vQ[c - X.nc]!), K3.mul st.2 cs)
      | _ => st)
    (#[], K3.one)).1

/-- FRI input word at domain index `idx`: `Σ_i cs^i (col_i(y) - v_i)/(y - pt_i)` -/
def deepWord (X : ExecInst) (pts : Array K3) (ops : Array (Nat × Nat × K3 × K3)) (baseAt : Nat → Nat → G) (idx : Nat) : K3 :=
  let y := VF.mul X.dShift (VF.pow X.dGen idx)
  let accs := ops.toList.foldl
    (fun (accs : Array K3) (o : Nat × Nat × K3 × K3) =>
      accs.modify o.2.1 fun a => K3.add a (K3.mul o.2.2.1 (K3.sub (K3.ofG (baseAt o.1 idx)) o.2.2.2)))
    (Array.replicate (X.r + 2) K3.zero)
  (List.range (X.r + 2)).foldl
    (fun tot p => K3.add tot (K3.mul accs[p]! (K3.inv (K3.sub (K3.ofG y) pts[p]!)))) K3.zero

def foldK3 (a b : K3) (y : G) (al : K3) : K3 :=
  K3.smul (VF.inv 2) (K3.add (K3.add a b) (K3.mul al (K3.smul (VF.inv y) (K3.sub a b))))

/-- the domain point of word `w` at index `g`: `dShift^(2^w) · (dGen^(2^w))^g` -/
def yAt (X : ExecInst) (w g : Nat) : G := VF.mul (VF.pow X.dShift (2 ^ w)) (VF.pow (VF.pow X.dGen (2 ^ w)) g)

/-- number of limbs squeezed after round `i` (see the header) -/
def roundNl (X : ExecInst) (i : Nat) : Nat :=
  if i == 1 then 3 * X.nCoins[0]! else if i == 2 then 3 * X.nCoins[1]!
  else if i == 3 || i == 4 || i == 6 then 3 else if i == 5 then 0
  else if i ≥ 7 && i ≤ 7 + X.k then 3 else if i == 8 + X.k then X.l else 0

def ckE (b : Bool) (m : String) : Except String Unit := if b then pure () else throw m

/-- the FRI fold chain of one query over the words `ws` (in order), starting from `prev` at index `prevIdx`; checks each fold -/
def friSteps (X : ExecInst) (vals : Array (Array Nat)) (sels : Array (Array Nat)) (alphas : Array K3) (q : Nat) :
    List Nat → K3 → Nat → Except String (K3 × Nat)
  | [], prev, prevIdx => pure (prev, prevIdx)
  | w :: ws, prev, prevIdx =>
    let j := 3 + w
    let halfw := 2 ^ (X.nD - w - 1)
    let gw := q % halfw
    let friAt (r : Nat) : K3 := K3.ofLimbs [vals[j]![3 * r]!, vals[j]![3 * r + 1]!, vals[j]![3 * r + 2]!]
    let a := friAt (lb sels[j]! (2 * gw))
    let b := friAt (lb sels[j]! (2 * gw + 1))
    ckE (prev == (if prevIdx < halfw then a else b)) s!"FRI fold mismatch, query {q}, word {w}" >>= fun _ =>
    friSteps X vals sels alphas q ws (foldK3 a b (yAt X w gw) alphas[w]!) gw

/-- Merkle check of tree `j` (message texts as the original loop) -/
def treeCheck (X : ExecInst) (H : HFn) (π : FlatProof) (W : Array Nat) (half0 : Nat) (sels : Array (Array Nat)) (j : Nat) :
    Except String Unit :=
  let nB := 4
  let sel := sels[j]!
  let vs := π.vals[j]!
  let per := if j < nB then 1 else 3
  ckE (vs.size == sel.size * per) s!"tree {j}: number of opened values" >>= fun _ =>
  if j < nB && W[j]! == 0 then
    ckE (π.roots[j]! == [0, 0, 0, 0, 0] && π.sibs[j]!.isEmpty) s!"tree {j}: empty block"
  else
    let sp := if j < nB then ragSpec W[j]! half0 else friSpec (2 ^ (X.nD - (j - 3)))
    let leaf (r : Nat) : Dg5 :=
      if j < nB then [vs[r]!, 0, 0, 0, 0] else [vs[3 * r]!, vs[3 * r + 1]!, vs[3 * r + 2]!, 0, 0]
    match goRoot H sp j sel leaf (π.sibs[j]!.toList.toArray) 1 0 sp.total 0 with
    | none => throw s!"tree {j}: malformed opening"
    | some (root, s) =>
      ckE (s == π.sibs[j]!.size) s!"tree {j}: unused frontier digests" >>= fun _ =>
      ckE (root == π.roots[j]!) s!"tree {j}: Merkle root mismatch"

/-- every field literal of a DAG expression is canonical (`.cF v`, `v < p`) -/
def exCanon : Tr.Ex → Bool
  | .cF v => based v.toNat
  | .add a b | .sub a b | .mul a b => exCanon a && exCanon b
  | .neg a | .pow a _ => exCanon a
  | _ => true

def chipCanon (c : Tr.Chip) : Bool := c.shared.all exCanon && c.cons.all (fun k => exCanon k.e)

/-- EVERY base-field limb of the instance, the statement and the proof is canonical (`< p`): `VF.add`/`VF.sub` are field operations only on
canonical limbs.  Instance: `dShift, dGen, hGen, hShift`, `pre`, `ppt`, every DAG literal of every table's chip; statement `z`; proof: digests, `vT`, `vQ`, `pfinal`, opened values
and frontier digests.  (The JSON loaders additionally reject a raw number `≥ p` before it reaches a `UInt64`.) -/
def allCanon (X : ExecInst) (z : List Nat) (π : FlatProof) : Bool :=
  let gOk (x : G) : Bool := based x.toNat
  gOk X.dShift && gOk X.dGen && gOk X.hGen && gOk X.hShift && k3Ok X.ppt && X.pre.all (·.all gOk) &&
  X.tabs.all (fun t => chipCanon t.chip) &&
  z.all based && π.roots.all dgOk && π.vT.all (·.all k3Ok) && π.vQ.all k3Ok && π.pfinal.all k3Ok &&
  π.vals.all (·.all based) && π.sibs.all (·.all dgOk)

/-- the public instance data (claim cells, registry pins) are canonical: every `key`, `idx`, `hi`, `lo` is `< p` (pubwire: `pubCheck_sound`'s `InpCan`) -/
def inpCanOk (inp : PE.PubIn) : Bool :=
  (inp.claimCells ++ inp.pins).all fun c => based c.key && based c.idx && based c.hi && based c.lo

/-- the tables partition the columns and the publics, each one's columns are `trace, isLast, publics`, `hN_t ≤ hN` -/
def tabsOk (X : ExecInst) : Bool :=
  let st := X.tabs.foldl (fun (st : Nat × Nat × Bool) t =>
    (st.1 + t.nc, st.2.1 + t.npub,
     st.2.2 && t.col0 == st.1 && t.pubBase == st.2.1 && 1 ≤ t.hN && t.hN ≤ X.hN && t.chip.width ≤ t.nc && t.npub ≤ t.nc &&
     t.col0 + t.nc ≤ X.nc && t.pubBase + t.npub ≤ X.pubOf.size &&
     (List.range t.nc).all (fun c =>
       (if c < t.nc - t.npub then (X.colKind[t.col0 + c]! == 0 || X.colKind[t.col0 + c]! == 1) &&
         (if X.colKind[t.col0 + c]! == 1 then X.pre[t.col0 + c]!.size ≤ X.hN + 1 else X.pre[t.col0 + c]!.size == 0)
       else X.colKind[t.col0 + c]! == 2 && X.pre[t.col0 + c]!.size == 0)) &&
     (List.range t.npub).all (fun j => X.pubOf[t.pubBase + j]! == t.col0 + (t.nc - t.npub) + j))) (0, 0, true)
  1 ≤ X.tabs.size && st.2.2 && st.1 == X.nc && st.2.1 == X.pubOf.size

/-- `genOrderOk g n acc`: `acc, acc·g, …, acc·g^(n-1)` are all `≠ 1` (`acc = g^m` on entry: no `g^m'` with `m ≤ m' < m+n` is `1`) -/
def genOrderOk (g : G) : Nat → G → Bool
  | 0, _ => true
  | n + 1, acc => (acc != 1) && genOrderOk g n (VF.mul acc g)

/-- the canonical `2^nD`-th root of unity of the FRI domain: `(7^(2^32-1))^(2^(32-nD))` (`NTT.root nD` of `Exec/Field.lean`) -/
def dGenOf (nD : Nat) : G := VF.pow (VF.pow VF.seven (2 ^ 32 - 1)) (2 ^ (32 - nD))

/-- The instance facts the audited side assumes of the verifier's domains, checked here (params):
* `dShift = 7` (the audited FRI domain is `smoothDomain nD`, coset generator `7`), `nD ≤ 32` (the largest `smoothDomain`);
* `dGen = (7^(2^32-1))^(2^(32-nD))` (`dGenOf`, the root `zeta nD` of `smoothDomain`);
* `hShift = 1` (the J-8 trace domain is `{hGen^i}`), `hGen ≠ 0` and `hGen^m ≠ 1` for `1 ≤ m < hN` (repeated multiplication, `hN - 1` steps): `i ↦ hShift·hGen^i` is injective on `i < hN`
  (the trace domain `H` has `hN` distinct points). -/
def paramsOk (X : ExecInst) : Bool :=
  X.dShift == 7 && decide (X.nD ≤ 32) && X.hShift == 1 && X.hGen != 0 && genOrderOk X.hGen (X.hN - 1) X.hGen &&
  X.dGen == dGenOf X.nD

def verifyFlatE (X : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) : Except String Unit :=
  let nB := 4
  let k := X.k
  let ncq := X.nc + X.nq
  -- canonical limbs everywhere (ONE check;  reads it off `FlatOk`)
  ckE (allCanon X z π) "non-canonical limb (>= p)" >>= fun _ =>
  -- instance + proof shape
  ckE (X.colKind.size == X.nc && X.blockOf.size == ncq && X.pre.size == X.nc && X.nCoins.size == 2) "inst shape" >>= fun _ =>
  ckE (X.nD ≥ k + 1 && X.nq % 3 == 0 && X.r ≥ 1 && X.hN ≥ 1 && X.l ≥ 1) "inst params" >>= fun _ =>
  ckE (paramsOk X) "instance params (dShift = 7, nD <= 32, hGen order >= hN)" >>= fun _ =>
  ckE (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) "tree count" >>= fun _ =>
  ckE (π.vT.size == X.nc && π.vQ.size == X.nq && π.pfinal.size == X.d && π.pos.size == X.l) "proof shape" >>= fun _ =>
  (List.range X.nc).forM (fun c =>
    ckE (π.vT[c]!.size == vTLen X c) "vT shape") >>= fun _ =>
  ckE (tabsOk X) "table layout" >>= fun _ =>
  ckE (π.pos.all (· < 2 ^ X.nD)) "position range" >>= fun _ =>
  -- (i) Fiat-Shamir: all coins from the key
  let pfEnc := π.pfinal.toList.flatMap K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl X
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if nlOf i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (nlOf i)
  -- every value drawn from Fiat-Shamir is canonical (coins, α, ζ, cs, FRI β's, query limbs): checked on the drawn limbs, not assumed of Tip5
  ckE (chals.all (·.all based)) "non-canonical Fiat-Shamir challenge limb" >>= fun _ =>
  let coins0 := k3s chals[1]! X.nCoins[0]!
  let coins1 := k3s chals[2]! X.nCoins[1]!
  let alpha := K3.ofLimbs chals[3]!
  let zeta := K3.ofLimbs chals[4]!
  let cs := K3.ofLimbs chals[6]!
  let alphas : Array K3 := (Array.range (k + 1)).map fun w => K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := chals[8 + k]!.toArray.map (· % 2 ^ X.nD)
  -- (ii) positions are the decoded query challenge
  ckE (π.pos == xs) "positions differ from the FS query challenge" >>= fun _ =>
  -- layout
  let half0 := 2 ^ (X.nD - 1)
  let (W, rank) := blockLayout X
  (List.range ncq).forM (fun c => ckE (X.blockOf[c]! < nB) "blockOf range") >>= fun _ =>
  -- (iii) Merkle: per tree, selected leaves, root recomputation
  let sels : Array (Array Nat) := (Array.range (nB + k)).map fun j => treeSel X (W.getD j 0) j π.pos
  (List.range (nB + k)).forM (treeCheck X H π W half0 sels) >>= fun _ =>
  -- (iv) DeepCheck
  let slots : Array K3 := X.derived.toList.foldl (fun (slots : Array K3) (be : Nat × Nat) => slots.push (K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := ((List.range X.hN).foldl
    (fun (st : K3 × G) _ => (K3.mul st.1 (K3.sub zeta (K3.ofG st.2)), VF.mul st.2 X.hGen)) (K3.one, X.hShift)).1
  let omZ := K3.smul X.hGen zeta
  let curNxt := (List.range X.nc).foldl
    (fun (st : Array K3 × Array K3) c =>
      match X.colKind[c]! with
      | 0 => (st.1.set! c π.vT[c]![0]!, st.2.set! c (if X.r ≥ 2 then π.vT[c]![1]! else K3.zero))
      | 1 => (st.1.set! c (K3.hornerG X.pre[c]! zeta), st.2.set! c (K3.hornerG X.pre[c]! omZ))
      | _ => st)
    (Array.replicate ncq K3.zero, Array.replicate ncq K3.zero)
  X.pubOf.toList.forM (fun c =>
    ckE (c < X.nc && X.colKind[c]! == 2) "pubOf" >>= fun _ =>
    ckE (π.vT[c]![0]!).isBase "public value not in the base field") >>= fun _ =>
  let pub : Array G := X.pubOf.map fun c => (π.vT[c]![0]!).c0
  -- constraints of table `t` times `mult_t = ∏_{i ∈ [hN_t, hN)} (ζ − hShift hGen^i)` (a product, never `Z_H / Z_{H_t}`: `K3.inv 0 = 0`);
  -- α-powers continue across the tables in table order
  ckE (!zh.isZero) "zeta in H" >>= fun _ =>
  let lhs := (X.tabs.foldl (fun (st : K3 × K3) t =>
    let cur := curNxt.1.extract t.col0 (t.col0 + t.nc)
    let nxt := curNxt.2.extract t.col0 (t.col0 + t.nc)
    let cvals := evalDag t.chip { cur := cur, next := nxt, pub := pub.extract t.pubBase (t.pubBase + t.npub), chal := slots,
                                  bc := t.chip.baseCols }
    let (s, pw) := cvals.foldl (fun (a : K3 × K3) v => (K3.add a.1 (K3.mul a.2 v), K3.mul a.2 alpha)) (K3.zero, st.2)
    let mult := ((List.range (X.hN - t.hN)).foldl
      (fun (a : K3 × G) _ => (K3.mul a.1 (K3.sub zeta (K3.ofG a.2)), VF.mul a.2 X.hGen))
      (K3.one, VF.mul X.hShift (VF.pow X.hGen t.hN))).1
    (K3.add st.1 (K3.mul s mult), pw)) (K3.zero, K3.one)).1
  let zN := K3.pow zeta X.hN
  let qsum := (List.range X.nq).foldl
    (fun qs j => K3.add qs (K3.mul (K3.mul (K3.pow K3.gen (j % 3)) (K3.pow zN (j / 3))) π.vQ[j]!)) K3.zero
  ckE (lhs == K3.mul zh qsum) "DeepCheck fails" >>= fun _ =>
  -- (v) OffDom
  let pts := openPts X zeta
  let dN := 2 ^ X.nD
  pts.toList.forM (fun pt => ckE (pt.pow dN != K3.ofG (VF.pow X.dShift dN)) "OffDom fails") >>= fun _ =>
  -- (vi) residual twin of the public relation
  ckE (X.pubCheck slots pub) "public relation fails" >>= fun _ =>
  ckE (inpCanOk X.pubIn) "non-canonical public instance data (claim/pin key, idx, hi or lo >= p)" >>= fun _ =>
  -- (vi') preprocessed columns: the committed openings equal the fixed polynomial at every opening point
  (List.range X.nc).forM (fun c =>
    ckE (X.colKind[c]! != 1 || (List.range X.r).all (fun o => π.vT[c]![o]! == K3.hornerG X.pre[c]! pts[o]!)) "pre opening mismatch") >>= fun _ =>
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

def verifyFlat (X : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) : Bool :=
  match verifyFlatE X H FS z π with | .ok _ => true | .error _ => false

end NockvmE2E.Exec.V
