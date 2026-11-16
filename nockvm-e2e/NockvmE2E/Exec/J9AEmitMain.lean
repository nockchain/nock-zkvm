/-
  NockvmE2E/Exec/J9AEmitMain.lean   (P10)  `nockvm-e2e-j9aemit OUT [nA]`: writes `OUT/j9a_{computeChipVCLHX9,axisChipJ9,splitChipJ9}.json`
  (the prover's chip documents; `nA` = the atom table's RAW row count, the value the verifier writes as `pubNA`; default 2).
  Moved verbatim from an earlier scratch file.  Untrusted tooling; no theorem.
-/
import NockvmE2E.Emit.ChipsJ9A
import NockvmE2E.Emit.ComputeX9
import NockvmE2E.Emit.ChipsWalk
set_option autoImplicit false
namespace Nock.Emit
open Lean Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
def kindStr : VarKind → String
  | .traceCur => "trace_cur" | .traceNext => "trace_next"
  | .challenge => "challenge" | .publicVal => "public_val"

def JExpr.toJson : JExpr → Json
  | .var k i => Json.mkObj [("var", Json.mkObj [("kind", kindStr k), ("index", i)])]
  | .constF n => Json.mkObj [("const_f", toString n)]
  | .constZ z => Json.mkObj [("const_z", Lean.toJson z)]
  | .add a b => Json.mkObj [("add", Json.arr #[a.toJson, b.toJson])]
  | .sub a b => Json.mkObj [("sub", Json.arr #[a.toJson, b.toJson])]
  | .mul a b => Json.mkObj [("mul", Json.arr #[a.toJson, b.toJson])]
  | .neg a => Json.mkObj [("neg", a.toJson)]
  | .pow a n => Json.mkObj [("pow", Json.arr #[a.toJson, (n : Json)])]
  | .extVar i k => Json.mkObj [("ext_var", Json.mkObj [("ext_index", i), ("kind", kindStr k)])]
  | .extChal i => Json.mkObj [("ext_chal", Json.mkObj [("index", i)])]
  | .extLift a => Json.mkObj [("ext_lift", a.toJson)]
  | .extAdd a b => Json.mkObj [("ext_add", Json.arr #[a.toJson, b.toJson])]
  | .extSub a b => Json.mkObj [("ext_sub", Json.arr #[a.toJson, b.toJson])]
  | .extMul a b => Json.mkObj [("ext_mul", Json.arr #[a.toJson, b.toJson])]
  | .extNeg a => Json.mkObj [("ext_neg", a.toJson)]
  | .ref i => Json.mkObj [("ref", (i : Json))]

/-- The `frameJ8` `sampledAfter` (FrameJ8.lean:34-36). -/
def sampledAfterJ8 : List ℕ := [1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def coinAfter (i : ℕ) : ℕ := sampledAfterJ8.getD i 0

/-- Per-node summary: trace degree, staging round, reads `trace_next`, `1 +` max challenge / public index. -/
structure Summ where
  deg : ℕ := 0
  rnd : ℕ := 0
  next : Bool := false
  chals : List ℕ := []
  pub : ℕ := 0

def Summ.join (a b : Summ) (d : ℕ) : Summ :=
  { deg := d, rnd := max a.rnd b.rnd, next := a.next || b.next,
    chals := b.chals.foldl (fun l c => if l.contains c then l else c :: l) a.chals, pub := max a.pub b.pub }

/-- Rounds of a challenge slot: frame coin `i < 19` is `frameJ8.sampledAfter i`; derived slots `>= 19` are `γ′` powers
(coins 4 and 6, both after round 1). -/
def slotRound (i : ℕ) : ℕ := if i < 19 then coinAfter i else max (coinAfter 4) (coinAfter 6)

def baseRounds (s : TSpec) : List ℕ :=
  (s.baseCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r
def extRounds (s : TSpec) : List ℕ :=
  (s.extCols.zipIdx).flatMap fun ((n, r) : ℕ × ℕ) => List.replicate n r

def summ (br er : List ℕ) (tab : Array Summ) : JExpr → Summ
  | .ref i => tab.getD i {}
  | .var .traceCur i => { deg := 1, rnd := br.getD i 0 }
  | .var .traceNext i => { deg := 1, rnd := br.getD i 0, next := true }
  | .var .challenge i | .extChal i | .extVar i .challenge => { chals := [i], rnd := slotRound i }
  | .var .publicVal i => { pub := i / 3 + 1 }
  | .extVar i .publicVal => { pub := i + 1 }
  | .constF _ | .constZ _ => {}
  | .extVar i .traceCur => { deg := 1, rnd := er.getD i 0 }
  | .extVar i .traceNext => { deg := 1, rnd := er.getD i 0, next := true }
  | .neg a | .extNeg a | .extLift a => summ br er tab a
  | .pow a n => let x := summ br er tab a; { x with deg := if x.deg = 0 then 0 else x.deg * n }
  | .add a b | .sub a b | .extAdd a b | .extSub a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (max x.deg y.deg)
  | .mul a b | .extMul a b =>
      let x := summ br er tab a; let y := summ br er tab b; x.join y (x.deg + y.deg)

def columnsJson (s : TSpec) : Json :=
  let br := baseRounds s
  let er := extRounds s
  let nb := br.length
  let bs := br.zipIdx.map fun ((r, i) : ℕ × ℕ) =>
    Json.mkObj [("name", s!"b{i}"), ("index", i), ("round", r), ("field", Json.mkObj [("base", true)]),
      ("var_kind", "trace_cur")]
  let es := er.zipIdx.flatMap fun ((r, e) : ℕ × ℕ) => (List.range 3).map fun (c : ℕ) =>
    Json.mkObj [("name", s!"k{e}_{c}"), ("index", nb + 3 * e + c), ("round", r),
      ("field", Json.mkObj [("ext", Json.mkObj [("ext_index", e), ("coord", c)])]), ("var_kind", "trace_cur")]
  Json.arr (bs ++ es).toArray

/-- The emitted chip, with its derived numbers: `(json, challenge slots read, max public (K) idx + 1, #shared)`. -/
def chipJson (id : String) (s : TSpec) : Json × List ℕ × ℕ × ℕ :=
  let d := emitDag s
  let br := baseRounds s
  let er := extRounds s
  let tab := d.defs.foldl (fun (t : Array Summ) j => t.push (summ br er t j)) #[]
  let arr (l : List JExpr) := Json.arr (l.map JExpr.toJson).toArray
  let cs := [("base_transition", d.base), ("ext_transition", d.ext), ("mixed_transition", d.mixed),
    ("ext_deg1", d.ext1), ("ext_deg3", d.ext3), ("equality_checks", d.eqc)]
  let cons := cs.flatMap fun (nm, l) => l.zipIdx.map fun ((j, i) : JExpr × ℕ) =>
    let m := summ br er tab j
    Json.mkObj [("kind", if m.next then "transition" else "row"), ("round", m.rnd), ("degree", m.deg),
      ("source", s!"{id}.{nm}[{i}]"), ("expr", j.toJson)]
  let allS := (cs.flatMap fun (_, l) => l.map (summ br er tab)) ++ tab.toList
  let ch := allS.foldl (fun l m => m.chals.foldl (fun l c => if l.contains c then l else c :: l) l) []
  let mp := (allS.map (·.pub)).foldl max 0
  (Json.mkObj [("id", id), ("rounds", s.rounds), ("columns", columnsJson s),
    ("shared", arr d.defs),
    ("gate_lists", Json.mkObj (cs.map fun (nm, l) => (nm, arr l))),
    ("constraints", Json.arr cons.toArray), ("bus_ids", Json.arr #[])], ch, mp, d.defs.length)

/-- The 19 `frameJ8` coins (SCHEMA §Frame), each a cubic `ext_k` element. -/
def coinNames : List String :=
  ["alphaC", "gamma", "z1", "z2", "gammaP_re", "rhoP_re", "gammaP_im", "rhoP_im", "a", "b", "c",
   "gammaH_re", "rhoH_re", "alphaW", "gammaW", "gammaH_im", "rhoH_im", "y1", "y2"]

/-- Document header: modulus `x³ − 7` (`Nock/TraceGenExe/K3.lean:104`), `k_prime_delta = 7` (`K6.lean:21`); the 19 frame
coins (indices = `frameJ8` coin indices, the checker's `CoinsE`); `derived_challenges` for every slot `>= 19` read by
a chip (`γ′ = (χ4, χ6)`, `CheckJ8.lean:68` `gV`; `power = (slot − 19) / 2`; `re` iff `(slot − 19)` even). -/
def docJson (p : ℕ) (δv : ℕ) (chips : List (String × TSpec)) : Json :=
  let cj := chips.map fun c => chipJson c.1 c.2
  let slots := (cj.flatMap fun c => c.2.1).foldl (fun l c => if l.contains c then l else c :: l) []
  let derived := ((slots.filter (· ≥ 19)).mergeSort).map fun (s : ℕ) =>
    Json.mkObj [("slot", s), ("re_coin", 4), ("im_coin", 6), ("power", (((s - 19) / 2 : ℕ) : Json)),
      ("part", if (s - 19) % 2 = 0 then "re" else "im")]
  let npub := (cj.map fun c => c.2.2.1).foldl max 1
  let coins := (List.range 19).map fun (i : ℕ) =>
    Json.mkObj [("index", i), ("name", coinNames.getD i s!"chi_{i}"), ("sampled_after", coinAfter i),
      ("field", "ext_k"), ("components", 3)]
  Json.mkObj [("schema_version", 1), ("field", "goldilocks"),
    ("extension", Json.mkObj [("k_degree", 3), ("k_prime_degree", 6), ("k_prime_delta", toString δv),
      ("modulus", Json.arr #[toString (p - 7), "0", "0"])]),
    ("frame", Json.mkObj [("coins", Json.arr coins.toArray),
      ("staging_rule", "constraint.round = max(max column.round read, max coin.sampled_after read)")]),
    ("derived_challenges", Json.arr derived.toArray),
    ("public_values", Json.arr ((List.range npub).map fun (i : ℕ) =>
      Json.mkObj [("index", i), ("name", s!"pub_{i}"), ("round", 0)]).toArray),
    ("buses", Json.arr #[]),
    ("chips", Json.arr (cj.map fun c => c.1).toArray)]

end Nock.Emit
open Lean Nock.Emit Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.VclL.Handle in
def main (args : List String) : IO Unit := do
  let out := args.getD 0 "."
  let nA := (args.getD 1 "2").toNat!
  let w (nm id : String) (s : Nock.Emit.TSpec) : IO Unit :=
    IO.FS.writeFile s!"{out}/j9a_{nm}.json" ((docJson Nock.Field.p δ.val [(id, s)]).compress ++ "\n")
  w "computeChipVCLHX9" "computeChipVCLHX9" Nock.Emit.computeSpec9
  w "axisChipJ9" "axisChipJ9" Nock.Emit.axisSpec
  w "splitChipJ9" "splitChipJ9" (Nock.Emit.splitSpecAt nA)
  -- optional third argument kW: also write `walkChipJ8_k<kW>.json` (the walk chip at kroots kW; NOT in the verifier's literal list unless kW in {1,9,25,42,48,174})
  if let some kw := args[2]? then
    let k := kw.toNat!
    IO.FS.writeFile s!"{out}/walkChipJ8_k{k}.json" ((docJson Nock.Field.p δ.val [("walkChipJ8", Nock.Emit.walkJ8SpecAt k)]).compress ++ "\n")
  IO.println s!"wrote 3 chips to {out} (split nA={nA})"
