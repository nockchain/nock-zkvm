/-
  Nock/DriverJ8/DriverJ8.lean

  Built on the generic driver (`Nock/Driver/*`: Tip5 sponge, chain hash, file I/O wrappers).  `drive` runs the
  `frameJ8` protocol against a `Backend` (the J-8 tracegen at given coins, and the checker verdict `checkJ8`):

    1. absorb the domain tag, the FULL public record `Pb` (`pubFields`) and the claim, canonical and length-prefixed;
    2. Staging guard: the round-0/1 columns of each regeneration must equal the committed ones.
    3. write `coins.txt` (60 numbers, the `nockvm-j8check check --coins` format; coin 19 is padding `0 0 0`).

  `verify` recomputes the coins from the stored files only (`pub.txt`, `*.rows`, `m.txt`), rebuilds the instance from
  those files and checks it.  `interactive` draws the coins from OS randomness after each freeze.
-/
import Nock.V1J8.CheckJ8
import Nock.DriverJ8.TranscriptJ8
import Nock.Driver.IOUtil

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Nock.DriverJ8.DriverJ8

open Nock.Driver.Tip5 Nock.Driver.Transcript Nock.DriverJ8.TranscriptJ8
open Nock.TraceGenExe Nock.V1J8.Exe Nock.V1J8.Check
open System (FilePath)

/-! ## Canonical encodings (every value `< p`) -/

def limbs32 : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 4294967296 :: limbs32 f (n / 4294967296)

/-- A natural number, length-prefixed, base `2^32` limbs. -/
def encNat (n : Nat) : List Nat := let l := limbs32 (n + 1) n; l.length :: l

def encNoun : Nock.Noun → List Nat
  | .atom n => 0 :: encNat n
  | .cell a b => 1 :: (encNoun a ++ encNoun b)

def kdN : Nock.Jet.ChipJ8.Kd → Nat
  | .reg => 0 | .call => 1 | .cst => 2 | .add => 3 | .mul => 4 | .rp => 5 | .sl => 6 | .sr => 7
  | .cp => 8 | .isf => 9 | .nil => 10

def encTy : Nock.Jet.Autogen.Ty → List Nat
  | .F => [0]
  | .L n t => 1 :: n :: encTy t
  | .N => [2]   -- fresh code (F = 0, L = 1 ..., N = 2): the opaque-noun type

def encEx {k : Nat} : Nock.Jet.Autogen.Ex k → List Nat
  | .var i => [0, i.val]
  | .const n => 1 :: encNat n
  | .add a b => 2 :: (encEx a ++ encEx b)
  | .mul a b => 3 :: (encEx a ++ encEx b)
  | .nth n e => 4 :: n :: encEx e
  | .pair a b => 5 :: (encEx a ++ encEx b)

def encTpl (T : Nock.Jet.Autogen.Tpl) : List Nat :=
  [T.k] ++ (List.finRange T.k).map (fun i => T.ax i) ++ (List.finRange T.k).flatMap (fun i => encTy (T.inTy i)) ++
    encTy T.outTy ++ encEx T.body

/-- **The public record `Pb`**: every chip's `h`, row count `n*` and orbit generator, the root counts, the budget,
the J layout, the registry pin (`regs`, `ids`, `idx`, `rk`, the templates `Rt` at the ids). -/
def pubFields (I : InJ8) : List (String × List Nat) :=
  let ch := fun (nm : String) (q : ChipIn) =>
    [("h" ++ nm, [q.h]), ("n" ++ nm, [q.n]), ("omega" ++ nm, [q.ω.val.toNat])]
  ch "X" I.X ++ ch "C" I.C ++ ch "W" I.W ++ ch "J" I.J ++ ch "A" I.A ++ ch "V" I.V ++
  [("kroots", [I.kroots]), ("krootsV", [I.krootsV]), ("g", [I.g]),
   ("rows", [I.r.N, I.r.D, I.r.W, I.r.Λ, I.r.A, I.r.AW, I.r.J, I.r.mb, I.r.inc, I.r.calls, I.r.heads,
     I.r.blocks, I.r.rd, I.r.leaves, I.r.maxlen]),
   ("lay", (List.finRange I.J.n).flatMap fun i =>
      let r := I.lay i; [kdN r.kd, r.id, r.cid, r.nid, r.n1, r.n2]),
   ("regs", I.regs), ("ids", I.ids),
   ("idxrk", I.ids.flatMap fun d => [d, I.idx d, (I.rk d).1, (I.rk d).2]),
   ("Rt", I.ids.flatMap fun d => d :: encTpl (I.Rt d))]

def claimFields (I : InJ8) : List (String × List Nat) :=
  [("claim.subject", encNoun I.c.subject), ("claim.formula", encNoun I.c.formula),
   ("claim.result", encNoun I.c.result)]

/-! ## Columns by round -/

structure ChipV where
  n : Nat
  get : Nat → Nat → Nat   -- column, row
  deriving Inhabited

def ofChip (q : ChipIn) : ChipV :=
  ⟨q.n, fun c i => if h : i < q.n then (q.cols c ⟨i, h⟩).val else 0⟩

def rX (j : Nat) : Nat := if j < 69 then 0 else 1
def rC (j : Nat) : Nat := if j < 134 then 0 else if j < 188 then 1 else 2
def rW (j : Nat) : Nat := if j < 25 then 0 else if j < 97 then 1 else 2
def rJ (j : Nat) : Nat := if j < 29 then 0 else 1
def rA (j : Nat) : Nat := if j < 205 then 0 else if j < 259 then 1 else 2

/-- name, width, column-round map (`crC crM crW crJ crA crW` of `TraceJ8`), in the order `X C W J A V`. -/
def chipSpecs : List (String × Nat × (Nat → Nat)) :=
  [("compute", 123, rX), ("cell", 242, rC), ("walk", 166, rW), ("j", 71, rJ), ("atom", 349, rA), ("aw", 166, rW)]

def chipsOf (I : InJ8) : List ChipV :=
  [ofChip I.X, ofChip I.C, ofChip I.W, ofChip I.J, ofChip I.A, ofChip I.V]

def colsOfRound (r : Nat) (s : String × Nat × (Nat → Nat)) (cv : ChipV) : List Nat :=
  ((List.range s.2.1).filter fun j => s.2.2 j = r).flatMap fun j => (List.range cv.n).map (cv.get j)

def roundCommit (r : Nat) (cvs : List ChipV) : List Nat :=
  roundDigest r ((chipSpecs.zip cvs).map fun (s, cv) => fileDigest s!"{s.1}.r{r}" (colsOfRound r s cv))

/-! ## Messages -/

def k3L (k : K3) : List Nat := [k.c0.val.toNat, k.c1.val.toNat, k.c2.val.toNat]
def k6L (k : K6) : List Nat := k3L k.re ++ k3L k.im
def npub : Nat := 64

def msgFlat (M : MsgE) : List Nat :=
  (List.finRange 5).flatMap (fun i => k6L (M.ρ i)) ++ k6L M.ρS ++
  (List.finRange 3).flatMap (fun k => let t := M.m k; [t.1, t.2.1, t.2.2]) ++
  [M.pubsC, M.pubsW, M.pubsJ, M.pubsA, M.pubsV].flatMap fun f => (List.range npub).flatMap fun i => k3L (f i)

def k3At (a : Array Nat) (o : Nat) : K3 := ⟨natG a[o]!, natG a[o + 1]!, natG a[o + 2]!⟩
def k6At (a : Array Nat) (o : Nat) : K6 := ⟨k3At a o, k3At a (o + 3)⟩
def k3Zero : K3 := ⟨natG 0, natG 0, natG 0⟩

def msgOfFlat (a : Array Nat) : MsgE :=
  let pubs := fun (b : Nat) (i : Nat) => if i < npub then k3At a (b + 3 * i) else k3Zero
  { m := fun k => (a[36 + 3 * k.val]!, a[37 + 3 * k.val]!, a[38 + 3 * k.val]!)
    ρ := fun i => k6At a (6 * i.val)
    ρS := k6At a 30
    pubsC := pubs 45, pubsW := pubs (45 + 3 * npub), pubsJ := pubs (45 + 6 * npub),
    pubsA := pubs (45 + 9 * npub), pubsV := pubs (45 + 12 * npub) }

/-! ## Coins -/

def coinsToE (cs : List (Nat × Coin)) (base : CoinsE) : CoinsE := fun i =>
  match cs.find? (fun c => c.1 = i.val) with
  | some (_, [a, b, c]) => ⟨natG a, natG b, natG c⟩
  | _ => base i

def coinsText (χ : CoinsE) : String :=
  " ".intercalate (((List.range 20).flatMap fun i =>
    if h : i < 19 then k3L (χ ⟨i, h⟩) else [0, 0, 0]).map toString) ++ "\n"

def limbOfBytes (b : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldr (fun k acc => (b.get! (off + k)).toNat + 256 * acc) 0

partial def randLimb : IO Nat := do
  let n := limbOfBytes (← IO.getRandomBytes 8) 0
  if n < P then return n else randLimb

def randCoins (idx : List Nat) : IO (List (Nat × Coin)) := do
  let mut out := []
  for i in idx do
    out := out ++ [(i, [← randLimb, ← randLimb, ← randLimb])]
  return out

/-! ## The driver -/

structure Backend where
  /-- the instance generated at the given coins (a named program) -/
  gen : CoinsE → Except String InJ8
  /-- the verdict (`checkJ8`, or the scope-waived harness) -/
  check : InJ8 → Bool
  /-- placeholder for the coins not yet drawn -/
  ph : CoinsE

inductive Mode | fs | interactive
  deriving BEq

def Mode.parse? : String → Option Mode
  | "fs" => some .fs | "interactive" => some .interactive | _ => none

def getCoins (mode : Mode) (cfg : Cfg) (idx : List Nat) : IO Cfg :=
  match mode with
  | .fs => pure (step cfg (.squeeze idx))
  | .interactive => do
    let cs ← randCoins idx
    pure ((squeezeSt cfg.1 idx).2, cfg.2 ++ cs)

def fail {α : Type} (s : String) : IO α := throw (IO.userError s)

def genIO (B : Backend) (χ : CoinsE) : IO InJ8 :=
  match B.gen χ with
  | .ok I => pure I
  | .error e => fail e

def checkLimbs (what : String) (l : List Nat) : IO Unit :=
  unless l.all (· < P) do fail s!"{what}: a limb is not below p"

def lineOf (f : String × List Nat) : String := " ".intercalate (f.1 :: f.2.map toString)

def writeRows (f : FilePath) (cv : ChipV) (w : Nat) : IO Unit := do
  let lines := (List.range cv.n).map fun i => " ".intercalate ((List.range w).map fun c => toString (cv.get c i))
  Nock.Driver.IOUtil.writeText f ("\n".intercalate lines ++ "\n")

structure Result where
  accepted : Bool
  log : List String

def drive (B : Backend) (mode : Mode) (out : FilePath) (prog : String) : IO Result := do
  Nock.Driver.IOUtil.mkdirs out
  let I0 ← genIO B B.ph
  let pub := pubFields I0
  let claim := claimFields I0
  checkLimbs "public record" ((pub ++ claim).flatMap (·.2))
  let c0 := roundCommit 0 (chipsOf I0)
  let cfg0 := runFrom initCfg (hdrEvents pub claim ++ [.absorb "commit/r0" c0])
  let cfg1 ← getCoins mode cfg0 idxS0
  let I1 ← genIO B (coinsToE cfg1.2 B.ph)
  unless pubFields I1 == pub do fail "public record changed after round 0"
  unless roundCommit 0 (chipsOf I1) == c0 do fail "round-0 columns changed with the round-0 coins"
  let c1 := roundCommit 1 (chipsOf I1)
  let cfg2 := step cfg1 (.absorb "commit/r1" c1)
  let cfg3 ← getCoins mode cfg2 idxS1
  let I2 ← genIO B (coinsToE cfg3.2 B.ph)
  unless pubFields I2 == pub do fail "public record changed after round 1"
  unless roundCommit 0 (chipsOf I2) == c0 do fail "round-0 columns changed with the round-1 coins"
  unless roundCommit 1 (chipsOf I2) == c1 do fail "round-1 columns changed with the round-1 coins"
  let c2 := roundCommit 2 (chipsOf I2)
  let mm := msgFlat I2.M
  checkLimbs "message" mm
  let cfg4 := runFrom cfg3 [.absorb "commit/r2" c2, .absorb "msg" mm]
  if mode == .fs then
    unless cfg4 == run (sched pub claim c0 c1 c2 mm) do fail "driver state differs from the pure schedule"
  let ok := B.check I2
  let dir := out
  let w := Nock.Driver.IOUtil.writeText
  w (dir / "prog.txt") (prog ++ "\n")
  w (dir / "pub.txt") ("\n".intercalate ((pub ++ claim).map lineOf) ++ "\n")
  w (dir / "m.txt") (" ".intercalate (mm.map toString) ++ "\n")
  w (dir / "coins.txt") (coinsText I2.χ)
  for (s, cv) in chipSpecs.zip (chipsOf I2) do
    writeRows (dir / (s.1 ++ ".rows")) cv s.2.1
  w (dir / "transcript.txt") (
    s!"mode {if mode == .fs then "fs" else "interactive"}\ncommit0 {c0}\ncommit1 {c1}\ncommit2 {c2}\nstate {cfg4.1}\n" ++
    s!"verdict {if ok then "ACCEPT" else "REJECT"}\n")
  let evs := ["domain", s!"pub x{pub.length}", s!"claim x{claim.length}", "commit/r0", "squeeze S0", "commit/r1",
    "squeeze S1", "commit/r2", "msg"]
  return ⟨ok, evs⟩

/-! ## Verify -/

def words (s : String) : List String :=
  ((s.map fun c => if c.isWhitespace then ' ' else c).splitOn " ").filter (· ≠ "")

def readRowsV (f : FilePath) : IO (Array (Array Nat)) := do
  let s ← Nock.Driver.IOUtil.readText f
  let ls := (s.splitOn "\n").filter fun l => words l ≠ []
  let rows ← ls.mapM fun l => (words l).mapM fun w =>
    match w.toNat? with
    | some n => if n < P then pure n else fail s!"{f}: value {w} is not below p"
    | none => fail s!"{f}: not a number: {w}"
  return (rows.map List.toArray).toArray

def cvOfRows (n : Nat) (a : Array (Array Nat)) : ChipV :=
  ⟨n, fun c i => ((a[i]?).bind (·[c]?)).getD 0⟩

def chipOfV (h n ω : Nat) (cv : ChipV) : ChipIn :=
  ⟨h, n, natG ω, fun c i => ((cv.get c i.val : Nat) : ZMod Nock.Field.p)⟩

/-- Recompute the coins from the stored files only, rebuild the instance from the files, check it. -/
def verify (B : Backend) (dir : FilePath) : IO Result := do
  let ptxt ← Nock.Driver.IOUtil.readText (dir / "pub.txt")
  let lines := (ptxt.splitOn "\n").filter fun l => words l ≠ []
  let fields ← lines.mapM fun l =>
    match words l with
    | nm :: vs => do
      let ns ← vs.mapM fun v => match v.toNat? with | some n => pure n | none => fail s!"pub.txt: bad number {v}"
      pure (nm, ns)
    | [] => fail "pub.txt: empty line"
  let claim := fields.filter fun f => f.1.startsWith "claim."
  let pub := fields.filter fun f => !f.1.startsWith "claim."
  checkLimbs "pub.txt" (fields.flatMap (·.2))
  let get := fun (nm : String) => ((pub.lookup nm).getD [0]).headD 0
  let mtxt ← Nock.Driver.IOUtil.readText (dir / "m.txt")
  let mm := (words mtxt).filterMap String.toNat?
  checkLimbs "m.txt" mm
  let nOf := fun (c : String) => get ("n" ++ c)
  let names := ["X", "C", "W", "J", "A", "V"]
  let mut cvs : List ChipV := []
  for (s, c) in chipSpecs.zip names do
    let a ← readRowsV (dir / (s.1 ++ ".rows"))
    cvs := cvs ++ [cvOfRows (nOf c) a]
  let c0 := roundCommit 0 cvs
  let c1 := roundCommit 1 cvs
  let c2 := roundCommit 2 cvs
  let cfg := run (sched pub claim c0 c1 c2 mm)
  let χ := coinsToE cfg.2 B.ph
  let stored ← Nock.Driver.IOUtil.readText (dir / "coins.txt")
  let same := (words stored).filterMap String.toNat? == (words (coinsText χ)).filterMap String.toNat?
  let mut log := [s!"recomputed coins {if same then "MATCH" else "DIFFER from"} stored coins.txt"]
  let sk ← match B.gen χ with
    | .ok I => pure (some I)
    | .error e => do log := log ++ [s!"generator at the recomputed coins: {e}"]; pure none
  let some sk := sk | return ⟨false, log⟩
  log := log ++ [s!"public record {if pubFields sk == pub then "equals" else "DIFFERS from"} the skeleton's Pb"]
  let ch := fun (c : String) (cv : ChipV) => chipOfV (get ("h" ++ c)) (nOf c) (get ("omega" ++ c)) cv
  let a := (mm.toArray)
  let Jc := ch "J" cvs[3]!
  let I : InJ8 :=
    { c := sk.c, M := msgOfFlat a, χ := sk.χ, r := sk.r, g := sk.g,
      X := ch "X" cvs[0]!, C := ch "C" cvs[1]!, W := ch "W" cvs[2]!, J := Jc,
      A := ch "A" cvs[4]!, V := ch "V" cvs[5]!, kroots := get "kroots", krootsV := get "krootsV",
      lay := fun i => if h : i.val < sk.J.n then sk.lay ⟨i.val, h⟩ else ⟨.nil, 0, 0, 0, 0, 0⟩,
      Rt := sk.Rt, regs := sk.regs, ids := sk.ids, idx := sk.idx, rk := sk.rk }
  return ⟨B.check I, log⟩

end Nock.DriverJ8.DriverJ8
