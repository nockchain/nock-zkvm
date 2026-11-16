/-
  NockvmE2E/Exec/Flat.lean   (executed, Mathlib-free)

  `ExecInst`  : computable instance data of the flat verifier (domain D, union trace domain H = {hShift * hGen^i : i < hN}
                (hN = max of the tables' row counts), one `TabInst` per table (own H_t = the first `hN_t` points of the SAME orbit,
                J-8: the REAL rows, not padded, not cyclic), column layout, the constraint DAGs, the public-relation check).
  `FlatProof` : the single-instance proof (D1-D12): 4 RAP block roots + k FRI roots, the clear DEEP
                message (vT, vQ), `pfinal`, the 170 (`l`) query positions, and per tree one pruned batch opening.
  JSON (`"version": 1`) reader/writer for both (the instance is read from a file in the exe; tests build it in Lean).
-/
import NockvmE2E.Exec.VField
import NockvmE2E.Exec.Trace
import NockvmE2E.Exec.PubExe
import NockvmE2E.Exec.PubExe9
import NockvmE2E.Exec.PubExe9L
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J

/-- One table (chip) of a multi-table instance.  Its trace domain is `H_t = {hShift * hGen^i : i < hN}` (the first `hN` points of the
instance orbit), its global columns are `col0 .. col0+nc-1` = its trace columns, (kind-1 preprocessed columns are among them), then its `npub` public
columns (the DAG of `chip` indexes them locally), and its publics are `pubOf[pubBase .. pubBase+npub-1]` (a slice of the concatenated publics). -/
structure TabInst where
  hN : Nat
  col0 : Nat
  nc : Nat
  npub : Nat
  pubBase : Nat
  chip : Tr.Chip

/-- Column layout: global column `c < nc`: `colKind c = 0` committed trace column (opened at `ζ·hGen^k`, `k < r`),
`1` preprocessed (coefficients `pre c`, evaluated by the verifier, in no tree), `2` public column (committed, opened at `ppt`).
Columns `nc .. nc+nq-1` are the quotient chunk columns (base columns, opened at `ζ`, `nq = 3·(#chunks)`, chunks of `hN` coefficients).
`blockOf c ∈ {0,1,2,3}` is the Merkle block of every committed column (kinds 0, 2, quotient). -/
structure ExecInst where
  nD : Nat                    -- |D| = 2^nD
  dShift : G                  -- D = dShift · <dGen>, dGen of order 2^nD
  dGen : G
  hN : Nat                    -- |H| (union domain = max over tables of hN_t)
  hGen : G                    -- H = { hShift · hGen^i : i < hN }
  hShift : G
  r : Nat                     -- offsets per committed column (J-8: 2, cur/next)
  k : Nat                     -- committed FRI words (k+1 folds)
  d : Nat                     -- final polynomial: exactly `d` K3 coefficients
  l : Nat                     -- number of queries
  nc : Nat
  nq : Nat
  colKind : Array Nat
  blockOf : Array Nat         -- size nc + nq
  pre : Array (Array G)       -- size nc; coefficients for kind 1, else #[]
  pubOf : Array Nat           -- flat public slot -> global column (kind 2)
  ppt : K3                    -- the public point
  nCoins : Array Nat          -- K3 coins squeezed after root_0 and root_1
  derived : Array (Nat × Nat) -- slot (nCoins0+nCoins1+j) = slots[base]^exp  (γ'-power slots)
  tabs : Array TabInst
  /-- the public relation is `PE.pubCheck pubIn pubLay slotOf` (claim / pin data, table layout, coin-slot map); the verifier checks `pubIn` canonical (`inpCanOk`) -/
  pubIn : PE.PubIn := { claimCells := [], pins := [] }
  pubLay : PE.PubLayout := { bases := #[], lens := #[] }
  slotOf : Array Nat := #[]
  /-- `0` = the J-8 relation `PE.pubCheck` (what `loadInst` produces); `2` = the J-9 A relation `PE.pubCheck9` (8 tables);
  other = TEST mode (self-test toys only, they use 1): the closure `pubTest` -/
  pubMode : Nat := 0
  pubTest : Array K3 → Array G → Bool := fun _ _ => true

/-- the public relation (coin slots, concatenated publics) -/
def ExecInst.pubCheck (X : ExecInst) : Array K3 → Array G → Bool :=
  if X.pubMode == 0 then PE.pubCheck X.pubIn X.pubLay X.slotOf
  else if X.pubMode == 2 then PE.pubCheck9 X.pubIn X.pubLay X.slotOf
  else if X.pubMode == 3 then PE.pubCheck9L X.pubIn X.pubLay X.slotOf
  else X.pubTest

structure FlatProof where
  roots : Array (List Nat)        -- 4 block roots, then k FRI roots (5 limbs each)
  vT : Array (Array K3)           -- per column < nc: kind0 r values, kind2 1 value, kind1 none
  vQ : Array K3                   -- nq values at ζ
  pfinal : Array K3               -- d coefficients
  pos : Array Nat                 -- l query positions in [0, 2^nD)
  vals : Array (Array Nat)        -- per tree: opened leaf limbs in leaf order (RAP: 1 limb/leaf, FRI: 3 limbs/leaf)
  sibs : Array (Array (List Nat)) -- per tree: pruned frontier digests, pre-order
  deriving Inhabited

/-! ### JSON -/
def limbsJ (l : List Nat) : Json := Json.arr (l.map natJ).toArray
def k3J (x : K3) : Json := limbsJ x.limbs

/-- strict readers: a non-number or a limb `≥ p` is an error at LOAD (the K3 / G carriers are `UInt64`, which would wrap `2^64 + v` to `v`;
the same bound is re-checked on the loaded structure by `allCanon` in `Verify.lean`). -/
def natE (what : String) (j : Json) : Except String Nat :=
  match j.getNat? with | .ok n => pure n | .error _ => throw s!"{what}: not a natural number"
def limbE (what : String) (j : Json) : Except String Nat := do
  let n ← natE what j
  if n < PN then pure n else throw s!"{what}: non-canonical limb {n} >= p"
def limbsE (what : String) (j : Json) : Except String (List Nat) := (arr j).toList.mapM (limbE what)
def k3E (what : String) (j : Json) : Except String K3 := do
  let l ← limbsE what j
  if l.length == 3 then pure (K3.ofLimbs l) else throw s!"{what}: K3 needs 3 limbs"
def natsE (what : String) (j : Json) : Except String (Array Nat) := (arr j).mapM (natE what)

def FlatProof.toJson (p : FlatProof) : Json :=
  Json.mkObj [("version", natJ 1),
    ("roots", Json.arr (p.roots.map limbsJ)),
    ("vT", Json.arr (p.vT.map fun a => Json.arr (a.map k3J))),
    ("vQ", Json.arr (p.vQ.map k3J)),
    ("pfinal", Json.arr (p.pfinal.map k3J)),
    ("pos", Json.arr (p.pos.map natJ)),
    ("trees", Json.arr ((p.vals.zip p.sibs).map fun (v, s) =>
      Json.mkObj [("vals", Json.arr (v.map natJ)), ("sibs", Json.arr (s.map fun x => limbsJ x))]))]

def FlatProof.ofJson (j : Json) : Except String FlatProof := do
  if (← natE "version" (get j "version")) != 1 then throw "FlatProof: version != 1"
  let trees := arr (get j "trees")
  pure { roots := ← (arr (get j "roots")).mapM fun x => (limbsE "roots" x)
         vT := ← (arr (get j "vT")).mapM fun a => (arr a).mapM (k3E "vT")
         vQ := ← (arr (get j "vQ")).mapM (k3E "vQ")
         pfinal := ← (arr (get j "pfinal")).mapM (k3E "pfinal")
         pos := ← natsE "pos" (get j "pos")
         vals := ← trees.mapM fun t => (arr (get t "vals")).mapM (limbE "vals")
         sibs := ← trees.mapM fun t => (arr (get t "sibs")).mapM fun x => limbsE "sibs" x }

def loadProof (path : String) : IO FlatProof := do
  IO.ofExcept ((FlatProof.ofJson (← readJson path)).mapError IO.userError)

/-! ### public-relation instance data (claim nouns, registry pins, table layout, coin-slot map) -/

def tokJ : PE.Tok → Json
  | .cell => Json.str "c"
  | .atom n => natJ n
def tokE (j : Json) : Except String PE.Tok :=
  match j with
  | .str "c" => pure .cell
  | _ => do pure (.atom (← natE "noun token" j))
def nounRecJ (r : PE.NounRec) : Json :=
  Json.mkObj [("key", natJ r.key), ("noun", Json.arr (r.noun.map tokJ).toArray), ("idx", natJ r.idx), ("hi", natJ r.hi), ("lo", natJ r.lo)]
def nounRecE (j : Json) : Except String PE.NounRec := do
  pure { key := ← natE "key" (get j "key"), noun := ← (arr (get j "noun")).toList.mapM tokE, idx := ← natE "idx" (get j "idx")
         hi := ← natE "hi" (get j "hi"), lo := ← natE "lo" (get j "lo") }
def primRecJ (r : PE.PrimRec) : Json :=
  Json.mkObj [("id", natJ r.id), ("code", natJ r.code), ("idx", natJ r.idx), ("hi", natJ r.hi), ("lo", natJ r.lo)]
def primRecE (j : Json) : Except String PE.PrimRec := do
  pure { id := ← natE "prim.id" (get j "id"), code := ← natE "prim.code" (get j "code"), idx := ← natE "prim.idx" (get j "idx")
         hi := ← natE "prim.hi" (get j "hi"), lo := ← natE "prim.lo" (get j "lo") }
/-- `prims` and `calls` are serialised only when non-empty (J-8 / J-9 A / J-9 AL instance JSON and digests are unchanged) -/
def pubInJ (p : PE.PubIn) : Json :=
  Json.mkObj ([("claimCells", Json.arr (p.claimCells.map nounRecJ).toArray), ("pins", Json.arr (p.pins.map nounRecJ).toArray),
    ("atoms", Json.arr (p.atoms.map fun (k, v) => Json.arr #[natJ k, natJ v]).toArray)] ++
    (if p.prims.isEmpty then [] else [("prims", Json.arr (p.prims.map primRecJ).toArray)]) ++
    (if p.calls.isEmpty then [] else [("calls", Json.arr (p.calls.map natJ).toArray)]))
def pubInE (j : Json) : Except String PE.PubIn := do
  let prims ← match j.getObjVal? "prims" with
    | .ok pj => (arr pj).toList.mapM primRecE
    | .error _ => pure []
  let calls ← match j.getObjVal? "calls" with
    | .ok cj => (arr cj).toList.mapM (natE "call")
    | .error _ => pure []
  pure { claimCells := ← (arr (get j "claimCells")).toList.mapM nounRecE, pins := ← (arr (get j "pins")).toList.mapM nounRecE
         atoms := ← (arr (get j "atoms")).toList.mapM fun a => do pure (← natE "atom k" (arr a)[0]!, ← natE "atom v" (arr a)[1]!)
         prims := prims, calls := calls }

/-- the `PE.PubLayout` of a table list: table `t` of `PE` is the tab whose chip id is `PE.tabOfId` `t` (at most one; its `npub` must be
`PE.tabLens t`); tables without a tab are absent (publics = constant 0). -/
def layoutOfTabs (tabs : Array TabInst) : Except String PE.PubLayout := do
  let mut bases : Array Nat := Array.replicate 6 0
  let mut present : Array Bool := Array.replicate 6 false
  for t in tabs do
    match PE.tabOfId t.chip.id with
    | none => throw s!"unknown chip id {t.chip.id}"
    | some i =>
      if present[i]! then throw s!"duplicate table {t.chip.id}"
      if t.npub != PE.tabLens[i]! then throw s!"table {t.chip.id}: {t.npub} publics, expected {PE.tabLens[i]!}"
      bases := bases.set! i t.pubBase
      present := present.set! i true
  pure { bases := bases, lens := PE.tabLens, present := present }

/-- Instance JSON: all `ExecInst` fields except the test closure `pubTest` (`pubMode = 0`; the public relation is `PE.pubCheck pubIn pubLay slotOf`)
and the tabs' chips (`j8_<chip>.json` paths).  Every G / K3 limb must be `< p` (rejected here, before the `UInt64` carrier can wrap it). -/
def loadInst (path : String) : IO ExecInst := do
  let j ← readJson path
  let ie {α : Type} (e : Except String α) : IO α := IO.ofExcept (e.mapError IO.userError)
  let g (what : String) (x : Json) : IO G := do pure (UInt64.ofNat (← ie (limbE what x)))
  let tabs ← (arr (get j "tabs")).mapM fun t => do
    pure ({ hN := ← ie (natE "tab.hN" (get t "hN")), col0 := ← ie (natE "tab.col0" (get t "col0")), nc := ← ie (natE "tab.nc" (get t "nc"))
            npub := ← ie (natE "tab.npub" (get t "npub")), pubBase := ← ie (natE "tab.pubBase" (get t "pubBase"))
            chip := ← Tr.loadChip (str (get t "chip")) } : TabInst)
  let pubIn ← ie (pubInE (get j "pubIn"))
  let slotOf ← ie (natsE "slotOf" (get j "slotOf"))
  let layout ← ie (layoutOfTabs tabs)
  pure { nD := ← ie (natE "nD" (get j "nD")), dShift := ← g "dShift" (get j "dShift"), dGen := ← g "dGen" (get j "dGen")
         hN := ← ie (natE "hN" (get j "hN")), hGen := ← g "hGen" (get j "hGen"), hShift := ← g "hShift" (get j "hShift")
         r := ← ie (natE "r" (get j "r")), k := ← ie (natE "k" (get j "k")), d := ← ie (natE "d" (get j "d")), l := ← ie (natE "l" (get j "l"))
         nc := ← ie (natE "nc" (get j "nc")), nq := ← ie (natE "nq" (get j "nq"))
         colKind := ← ie (natsE "colKind" (get j "colKind")), blockOf := ← ie (natsE "blockOf" (get j "blockOf"))
         pre := ← (arr (get j "pre")).mapM fun a => (arr a).mapM (g "pre")
         pubOf := ← ie (natsE "pubOf" (get j "pubOf")), ppt := ← ie (k3E "ppt" (get j "ppt"))
         nCoins := ← ie (natsE "nCoins" (get j "nCoins"))
         derived := ← (arr (get j "derived")).mapM fun a => do pure (← ie (natE "derived" (arr a)[0]!), ← ie (natE "derived" (arr a)[1]!))
         tabs := tabs, pubIn := pubIn, pubLay := layout, slotOf := slotOf }

end NockvmE2E.Exec.V
