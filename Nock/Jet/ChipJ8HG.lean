/-
  Nock/Jet/ChipJ8HG.lean

  `chainWG nodeWG nodesWG blockWG honestJ8G` are
  verbatim copies of `ChipJ8Toy`'s `chainW … honestJ8` with the handle function `hOf mem` replaced by an
  arbitrary `hd : Noun → ZMod p × ZMod p`. Bridge: `honestJ8G (hOf mem) = honestJ8 mem` (induction +
  `simp only`, never bare `rfl`), the `hd`-generic layout lemma `honestJ8G_pre`, and shape lemmas for the
  export / provide keys of the chain rows. -/
import Nock.Jet.ChipJ8Toy

set_option autoImplicit false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.NockVMROM.Thm54.CoordinateCompiler

section GenG
variable {p : ℕ} [Fact p.Prime]

def chainWG (hd : Noun → ZMod p × ZMod p) (c dst : ℕ) :
    ℕ → ℕ → List Bool → Noun → List (CRow (ZMod p))
  | src, _, [], x =>
    [⟨⟨.cp, 0, c, dst, src, 0⟩, mkW 0 1 0 0 0 (0, 0) (hd x) (0, 0)⟩]
  | src, ctr, b :: bs, x =>
    ⟨⟨if b then .sr else .sl, 0, c, ctr, src, 0⟩,
      mkW 0 1 0 0 0 (hd x) (hd (nhd x)) (hd (ntl x))⟩ ::
      chainWG hd c dst ctr (ctr + 1) bs (if b then ntl x else nhd x)

def nodeWG (hd : Noun → ZMod p × ZMod p) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) :
    List (CRow (ZMod p)) :=
  match nd.op with
  | .var _ ax => chainWG hd c nd.id S ctr (axPath ax) s
  | .nth j => chainWG hd c nd.id nd.a ctr (List.replicate j true ++ [false]) (lk nd.a)
  | .tlN n => chainWG hd c nd.id nd.a ctr (List.replicate n true) (lk nd.a)
  | .const k => [⟨⟨.cst, 0, c, nd.id, k, 0⟩, mkW 0 1 (k : ZMod p) 0 0 (0, 0) (0, 0) (0, 0)⟩]
  | .add => [⟨⟨.add, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 (atomVal (lk nd.id) : ZMod p)
      (atomVal (lk nd.a) : ZMod p) (atomVal (lk nd.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩]
  | .mul => [⟨⟨.mul, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 (atomVal (lk nd.id) : ZMod p)
      (atomVal (lk nd.a) : ZMod p) (atomVal (lk nd.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩]
  | .pair => [⟨⟨.rp, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 0 0 0
      (hd (lk nd.id)) (hd (lk nd.a)) (hd (lk nd.b))⟩]
  | .isF => [⟨⟨.isf, 0, c, nd.id, nd.a, 0⟩, mkW 0 1 0 (atomVal (lk nd.a) : ZMod p) 0 (0, 0) (0, 0) (0, 0)⟩]
  | .isNil => [⟨⟨.nil, 0, c, nd.id, nd.a, 0⟩, mkW 0 1 0 0 0 (0, 0) (0, 0) (0, 0)⟩]

def nodesWG (hd : Noun → ZMod p × ZMod p) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ℕ → List JNode → List (CRow (ZMod p))
  | _, [] => []
  | ctr, nd :: nds => nodeWG hd c S ctr lk s nd ++ nodesWG hd c S lk s (ctr + nodeVirt nd) nds

def blockWG (hd : Noun → ZMod p × ZMod p) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) : List (CRow (ZMod p)) :=
  let T := R i
  let N := (nodesOf T).length
  let lk := honestLook (p := p) T s c
  ⟨callPre R c i, mkW 1 1 0 0 0
      (hd (compile p T)) (hd s) (hd (lk 0))⟩ ::
    nodesWG hd c N lk s (N + 1) (nodesOf T)

def honestJ8G (hd : Noun → ZMod p × ZMod p) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) :
    List (CRow (ZMod p)) :=
  regs.map (fun i => ⟨regPre i, mkW 0 1 0 0 0
    (hd (compile p (R i))) (0, 0) (0, 0)⟩) ++
  (calls.zipIdx.flatMap fun ⟨⟨i, s⟩, c⟩ => blockWG hd R c i s)

/-! ## Bridge to the `hOf mem` generator -/

theorem chainWG_hOf (mem : List Noun) (c dst : ℕ) :
    ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun),
      chainWG (p := p) (hOf mem) c dst src ctr bs x = chainW mem c dst src ctr bs x
  | [], src, ctr, x => by simp only [chainWG, chainW]
  | b :: bs, src, ctr, x => by
    simp only [chainWG, chainW, chainWG_hOf mem c dst bs ctr (ctr + 1)]

theorem nodeWG_hOf (mem : List Noun) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) :
    nodeWG (p := p) (hOf mem) c S ctr lk s nd = nodeW mem c S ctr lk s nd := by
  unfold nodeWG nodeW
  cases nd.op <;> first | exact chainWG_hOf .. | rfl

theorem nodesWG_hOf (mem : List Noun) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ∀ (nds : List JNode) (ctr : ℕ),
      nodesWG (p := p) (hOf mem) c S lk s ctr nds = nodesW mem c S lk s ctr nds
  | [], _ => by simp only [nodesWG, nodesW]
  | nd :: nds, ctr => by
    simp only [nodesWG, nodesW, nodeWG_hOf, nodesWG_hOf mem c S lk s nds]

theorem blockWG_hOf (mem : List Noun) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) :
    blockWG (p := p) (hOf mem) R c i s = blockW mem R c i s := by
  simp only [blockWG, blockW, nodesWG_hOf]

/-- **Bridge.** The generic generator at the memory handle is the pinned honest generator. -/
theorem honestJ8G_hOf (mem : List Noun) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) :
    honestJ8G (p := p) (hOf mem) R regs calls = honestJ8 mem R regs calls := by
  simp only [honestJ8G, honestJ8, blockWG_hOf]

/-! ## Layout (`hd`-generic) -/

theorem chainWG_pre (hd : Noun → ZMod p × ZMod p) (c dst : ℕ) :
    ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun),
      (chainWG hd c dst src ctr bs x).map CRow.pre = chainPre c dst src ctr bs
  | [], src, ctr, x => rfl
  | b :: bs, src, ctr, x => by
    simp only [chainWG, chainPre, List.map_cons, chainWG_pre hd c dst bs]

theorem nodeWG_pre (hd : Noun → ZMod p × ZMod p) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) :
    (nodeWG hd c S ctr lk s nd).map CRow.pre = nodePre c S ctr nd := by
  unfold nodeWG nodePre
  cases nd.op <;> first | exact chainWG_pre .. | rfl

theorem nodesWG_pre (hd : Noun → ZMod p × ZMod p) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ∀ (nds : List JNode) (ctr : ℕ), (nodesWG hd c S lk s ctr nds).map CRow.pre = nodesPre c S ctr nds
  | [], ctr => rfl
  | nd :: nds, ctr => by
    simp only [nodesWG, nodesPre, List.map_append, nodeWG_pre, nodesWG_pre hd c S lk s nds]

theorem blockWG_pre (hd : Noun → ZMod p × ZMod p) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) :
    (blockWG (p := p) hd R c i s).map CRow.pre = blockPre R c i := by
  simp only [blockWG, blockPre, List.map_cons, nodesWG_pre]

theorem blocksWG_pre (hd : Noun → ZMod p × ZMod p) (R : ℕ → Tpl) :
    ∀ (calls : List (ℕ × Noun)) (c0 : ℕ),
      ((calls.zipIdx c0).flatMap fun x => blockWG (p := p) hd R x.2 x.1.1 x.1.2).map CRow.pre =
        blocks R c0 (calls.map Prod.fst)
  | [], c0 => rfl
  | (i, s) :: calls, c0 => by
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, blockWG_pre, List.map_cons, blocks,
      blocksWG_pre hd R calls (c0 + 1)]

/-- **The generic honest J rows have the verifier's layout**, for every handle function. -/
theorem honestJ8G_pre (hd : Noun → ZMod p × ZMod p) (R : ℕ → Tpl) (regs : List ℕ)
    (calls : List (ℕ × Noun)) :
    (honestJ8G (p := p) hd R regs calls).map CRow.pre = layoutJ8 R regs (calls.map Prod.fst) := by
  unfold honestJ8G layoutJ8
  rw [List.map_append, List.map_map]
  exact congrArg₂ _ (by simp [Function.comp_def, regPre]) (blocksWG_pre hd R calls 0)

/-! ## Key shapes of a read-chain row -/

/-- A `sl`/`sr` chain row exports `(hd x).2, hd(nhd x), hd(ntl x)` (the `keyX` record). -/
theorem keysOf_entsX_chain (hd : Noun → ZMod p × ZMod p) (c ctr src : ℕ) (b : Bool) (x : Noun) :
    keysOf entsX (⟨⟨if b then .sr else .sl, 0, c, ctr, src, 0⟩,
      mkW 0 1 0 0 0 (hd x) (hd (nhd x)) (hd (ntl x))⟩ : CRow (ZMod p)) =
      [[(hd x).2, (hd (nhd x)).1, (hd (nhd x)).2, (hd (ntl x)).1, (hd (ntl x)).2]] := by
  cases b <;> simp [keysOf, entsX, keyX, KE.ev, colOf, mkW, Col.vN, Col.kL, Col.vL, Col.kR, Col.vR]

/-- A `cp` terminal row exports nothing and provides `(1, c, dst, (hd x))`-shaped key `keyV`. -/
theorem provK_chain_cp (hd : Noun → ZMod p × ZMod p) (c dst src : ℕ) (x : Noun) :
    provK (⟨⟨.cp, 0, c, dst, src, 0⟩, mkW 0 1 0 0 0 (0, 0) (hd x) (0, 0)⟩ : CRow (ZMod p)) =
      [[1, (c : ZMod p), (dst : ZMod p), (hd x).1, (hd x).2]] := by
  simp [provK, keysOf, ents2, keyV, KE.ev, colOf, mkW, Col.cid, Col.nid, Col.kL, Col.vL]

end GenG

#print axioms chainWG_hOf
#print axioms nodeWG_hOf
#print axioms nodesWG_hOf
#print axioms blockWG_hOf
#print axioms honestJ8G_hOf
#print axioms chainWG_pre
#print axioms nodeWG_pre
#print axioms nodesWG_pre
#print axioms blockWG_pre
#print axioms blocksWG_pre
#print axioms honestJ8G_pre
#print axioms keysOf_entsX_chain
#print axioms provK_chain_cp

end Nock.Jet.ChipJ8
