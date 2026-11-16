/-
  NockvmE2E/Exec/DriveJ9AL.lean   (UNTRUSTED tooling, executed, no theorem)

  The Fiat-Shamir driver over nockvm's staged J-9 AL generator (`Nock.V1J9AL.GenJ9ALXJStaged`: gen0 / gen1 / gen2).
  `FP.proveAll` is given a `StageSrc` whose stage 1 / stage 2 call `gen1` / `gen2` at the coins that `proveAll`'s own transcript
  (`chalAt`, the verifier's `tip5FS`) derived, instead of the generic aux solver.  gen0 supplies the round-0 columns.
  The H/ proof file `GenPortJ9ALHStaged` is NOT imported.  Not zero-knowledge.
-/
import NockvmE2E.Exec.J9ALConv
import NockvmE2E.Exec.FreeProg
import NockvmE2E.Exec.FlatProver
import NockvmE2E.Exec.FixProve
import NockvmE2E.Exec.AuxFill
import Nock.V1J9AL.GenJ9ALXJStaged

set_option autoImplicit false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Exec.DriveJ9AL
open Lean NockvmE2E.Exec.J NockvmE2E.Exec.Tr NockvmE2E.Exec.FP NockvmE2E.Exec.Aux

abbrev NK3 := Nock.TraceGenExe.K3
abbrev Blk := Nock.V1J9AL.GenJ9ALXJStaged.BlkL
abbrev Rec := Nock.V1J9AL.CheckJ9AL.InJ9AL

/-- a frame value (`PF.E3`, three limbs) as nockvm's `K3` (`natG` triples, as `DriverJ8.coinsToE`) -/
def k3OfE3 (e : NockvmE2E.Exec.PF.E3) : NK3 :=
  ⟨Nock.V1J8.Exe.natG e.a.toNat, Nock.V1J8.Exe.natG e.b.toNat, Nock.V1J8.Exe.natG e.c.toNat⟩

def bumpK3 (k : NK3) : NK3 := ⟨Nock.V1J8.Exe.natG (k.c0.val.toNat + 1), k.c1, k.c2⟩

/-- the `ChipIn` of table `id` in a round block / record -/
def chipOfId (b : Blk) (id : String) : Nock.V1J8.Check.ChipIn :=
  if id == "computeChipVCLHX9" then b.X else if id == "cellChipHQKW" then b.C else if id == "walkChipJ8" then b.W
  else if id == "jetChipJ8" then b.J else if id == "atomChipHQL" then b.A else if id == "walkChipHQK" then b.V
  else if id == "axisChipJ9" then b.AX else if id == "splitChipJ9" then b.SP else b.AL

/-- the round thresholds of `blkOf` (`GenJ9ALXJStaged.cr3 a b`) per table -/
def thrOf (id : String) : Nat × Nat :=
  if id == "computeChipVCLHX9" then (83, 137) else if id == "cellChipHQKW" then (134, 188)
  else if id == "walkChipJ8" || id == "walkChipHQK" then (25, 97) else if id == "jetChipJ8" then (29, 71)
  else if id == "atomChipHQL" then (205, 259) else if id == "axisChipJ9" then (22, 22)
  else if id == "splitChipJ9" then (72, 72) else (94, 148)

def colOf (q : Nock.V1J8.Check.ChipIn) (c : Nat) : Array UInt64 :=
  (Array.range q.n).map fun i => if h : i < q.n then UInt64.ofNat (q.cols c ⟨i, h⟩).val else 0

def trOfChip (q : Nock.V1J8.Check.ChipIn) (width : Nat) (pubs : List Nat) : Tr :=
  { nRows := q.n, pub := pubs.toArray.map UInt64.ofNat, cols := (Array.range width).map (colOf q) }

/-- guard (i): the verifier chip's column rounds are the staged generator's thresholds -/
def checkRounds (act : Array (Chip × Tr)) : IO Unit := do
  for (ch, _) in act do
    let (a, b) := thrOf ch.id
    for c in [0:ch.width] do
      if Nock.V1J9AL.GenJ9ALXJStaged.cr3 a b c != ch.colRound[c]! then
        throw (IO.userError s!"GUARD (i): table {ch.id} column {c}: doc round {ch.colRound[c]!} vs staged block round {Nock.V1J9AL.GenJ9ALXJStaged.cr3 a b c}")

/-- write the round-`r` columns of block `blk` into the tables -/
def writeRound (blk : Blk) (r : Nat) (cur : Array (Chip × Tr)) : IO (Array (Chip × Tr)) := do
  let mut out := cur
  for t in [0:cur.size] do
    let (ch, tr) := cur[t]!
    let q := chipOfId blk ch.id
    if q.n != tr.nRows then throw (IO.userError s!"GUARD: table {ch.id}: block rows {q.n} vs table rows {tr.nRows}")
    let mut cols := tr.cols
    for c in [0:ch.width] do
      if ch.colRound[c]! == r then cols := cols.set! c (colOf q c)
    out := out.set! t (ch, { tr with cols := cols })
  return out

structure Shared where
  st1 : Option Nock.V1J9AL.GenJ9ALXJStaged.St1 := none
  b1 : Option Blk := none
  b2 : Option Blk := none
  rest : Option Rec := none
  cs0 : Array NK3 := #[]
  cs1 : Array NK3 := #[]

open Nock.V1J9AL.GenJ9ALXJStaged (gen1 gen2 coins0OfArray coins1OfArray) in
/-- the stage source: stage 1 = `gen1` at coins0, stage 2 = `gen2` at coins1 (+ the publics from the record `rest`).
`tamperCoin = some k`: coins0[k] += 1 before gen1 (negative test). -/
def stagedSrc (st0 : Nock.V1J9AL.GenJ9ALXJStaged.St0) (tamperCoin : Option Nat) : IO (StageSrc × IO.Ref Shared) := do
  let ref ← IO.mkRef ({} : Shared)
  let src : StageSrc := { stage := fun r f cur => do
    if r == 1 then
      let mut cs : Array NK3 := (Nock.DriverJ8.TranscriptJ8.idxS0.toArray).map fun i => k3OfE3 f[i]!
      match tamperCoin with
      | some k => if k < cs.size then cs := cs.set! k (bumpK3 cs[k]!)
      | none => pure ()
      let (b1, st1) := gen1 st0 (coins0OfArray cs)
      ref.modify fun s => { s with st1 := some st1, b1 := some b1, cs0 := cs }
      writeRound b1 1 cur
    else
      let some st1 := (← ref.get).st1 | throw (IO.userError "stage 2 before stage 1")
      let cs : Array NK3 := (Nock.DriverJ8.TranscriptJ8.idxS1.toArray).map fun i => k3OfE3 f[i]!
      let (b2, rest) := gen2 st1 (coins1OfArray cs)
      ref.modify fun s => { s with b2 := some b2, rest := some rest, cs1 := cs }
      let cur2 ← writeRound b2 2 cur
      let mut out := cur2
      for t in [0:cur2.size] do
        let (ch, tr) := cur2[t]!
        let pubs := (pubsOfRec rest ch.id).toArray.map UInt64.ofNat
        if pubs.size != tr.pub.size then throw (IO.userError s!"GUARD: table {ch.id}: publics {pubs.size} vs {tr.pub.size}")
        out := out.set! t (ch, { tr with pub := pubs })
      return out }
  return (src, ref)

/-! ## the public input from the record -/

def nounRecOf (keyField : String) (j : Json) : NockvmE2E.Exec.PE.NounRec :=
  { key := nat (get j keyField), idx := nat (get j "idx"), hi := nat (get j "hi"), lo := nat (get j "lo")
    noun := (arr (get j "noun")).toList.map fun t =>
      match t.getStr? with
      | .ok "c" => .cell
      | .ok s => .atom s.toNat!
      | .error _ => .atom (nat t) }

def pubeqOf (I : Rec) : Option Json :=
  if hv : Nock.V1J8.Check.validB I.toInJ8 = true then
    some (_root_.pubeqJson I ((Nock.V1J8.Check.validB_iff I.toInJ8).mp hv)) else none

/-- `PubIn` of a record: as `ProverMain --family j9al` reads `pubeq.json` (claim cells incl. the key-2 big-atom records, pins, prims,
plain-atom claim positions from the compute publics) -/
def pubInOfRec (I : Rec) (computePub : Array UInt64) (catj : Bool := false) : Option NockvmE2E.Exec.PE.PubIn := do
  let pe ← pubeqOf I
  let atoms : List (Nat × Nat) := (List.range 3).filterMap fun k =>
    if computePub[2 * k]! == 0 then some (k, computePub[2 * k + 1]!.toNat) else none
  let prims ← match pe.getObjVal? "prims" with
    | .ok pj => some ((arr pj).toList.map fun j =>
        ({ id := nat (get j "id"), code := nat (get j "code"), idx := nat (get j "idx"), hi := nat (get j "hi"), lo := nat (get j "lo") } : NockvmE2E.Exec.PE.PrimRec))
    | .error _ => none
  pure { claimCells := (arr (get pe "claim")).toList.map (fun j => { nounRecOf "k" j with idx := 0 }),
         pins := (arr (get pe "pins")).toList.map (nounRecOf "id"), atoms := atoms, prims := prims,
         calls := if catj then I.ids else [] }

def bumpTok : List NockvmE2E.Exec.PE.Tok → List NockvmE2E.Exec.PE.Tok
  | [] => []
  | .atom n :: r => .atom (n + 1) :: r
  | .cell :: r => .cell :: bumpTok r

/-! ## the run -/

def chipBase (dir id : String) : IO String := do
  let j9alP := s!"{dir}/j9al_{id}.json"
  let j9P := s!"{dir}/j9a_{id}.json"
  if (← System.FilePath.pathExists j9alP) then pure j9alP
  else if (← System.FilePath.pathExists j9P) then pure j9P
  else pure s!"{dir}/j8_{id}.json"

/-- `Emit.ChipsJ9AL.yDers`: pair (17, 18), powers 0..32, slots 41..106 -/
def yDersP : Array Der :=
  ((List.range 33).flatMap fun (t : Nat) =>
    [(⟨41 + 2 * t, 17, 18, t, true⟩ : Der), ⟨42 + 2 * t, 17, 18, t, false⟩]).toArray

def peakRss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  pure ((s.splitOn "\n").filter (·.startsWith "VmHWM") |>.headD "VmHWM: ?")

structure Opts where
  tamperPub : Option (Nat × Nat) := none
  tamperPre : Option (Nat × Nat × Nat) := none
  tamperCoin : Option Nat := none
  tamperPrim : Bool := false
  wrongClaim : Bool := false
  nockCheck : Bool := false
  catj : Bool := false

partial def parseArgs (o : Opts) : List String → Opts × List String
  | "--tamper-pub" :: ts :: rest =>
    match ts.splitOn ":" with
    | [t, s] => parseArgs { o with tamperPub := some (t.toNat!, s.toNat!) } rest
    | _ => (o, rest)
  | "--tamper-pre" :: ts :: rest =>
    match ts.splitOn ":" with
    | [t, c, r] => parseArgs { o with tamperPre := some (t.toNat!, c.toNat!, r.toNat!) } rest
    | _ => (o, rest)
  | "--tamper-coin" :: k :: rest => parseArgs { o with tamperCoin := some k.toNat! } rest
  | "--tamper-prim" :: rest => parseArgs { o with tamperPrim := true } rest
  | "--wrong-claim" :: rest => parseArgs { o with wrongClaim := true } rest
  | "--nock-check" :: rest => parseArgs { o with nockCheck := true } rest
  | "--reg-catj" :: rest => parseArgs { o with catj := true } rest
  | l => (o, l)

open Nock.V1J9AL.GenJ9ALXJStaged (gen0 recAt assemble assembleI) in
def run (args0 : List String) : IO UInt32 := do
  let (fo, args1) ← match NockvmE2E.Exec.FreeProg.extractFree {} args0 with
    | .ok r => pure r
    | .error e => IO.eprintln s!"ERROR: {e}"; return 2
  let (o, args) := parseArgs {} args1
  match args with
  | dir :: prog :: out :: _ =>
    let t0 ← IO.monoMsNow
    let (s, f, primsR, fuel) ← match NockvmE2E.Exec.FreeProg.resolveProg prog fo with
      | .ok p => pure p
      | .error e => IO.eprintln s!"ERROR: {e}"; return 2
    let pe := NockvmE2E.Exec.FreeProg.progErrors primsR
    unless pe.isEmpty do
      for e in pe do IO.eprintln s!"ERROR: {e}"
      return 3
    let (reg, rt) := regOf o.catj primsR   -- default: addPrims empty prims / rtP trivTpl (unchanged); `--reg-catj`: catJ
    if (Nock.V1J8.Gen.runX reg fuel s f).isNone then
      IO.eprintln s!"ERROR: {prog}: the Nock run did not finish (crash, or more than fuel {fuel} steps; try --fuel N with a larger N)"
      return 3
    let some (b0, st0) := gen0 reg rt primsR fuel s f
      | IO.eprintln s!"ERROR: {prog}: gen0 none (the run is fine but the tracegen refuses it, e.g. a prim call whose operands are not atoms)"; return 3
    -- the record at a dummy coin vector: table presence, publics of the claim slots (coin-free), pubIn
    let i0 : Rec := recAt st0 (assemble (fun _ => default) (fun _ => default))
    let se := NockvmE2E.Exec.FreeProg.sideErrors reg primsR fuel s f i0
    unless se.isEmpty do
      if fo.force then
        for e in se do IO.eprintln s!"WARNING (--allow-unverifiable): {prog}: {e}"
      else
        for e in se do IO.eprintln s!"ERROR: {prog}: {e}"
        IO.eprintln "refusing to prove: the side conditions above do not hold (see README, section 'Your own program')"
        return 3
    logMsg s!"gen0 ok: rows X {i0.X.n} C {i0.C.n} W {i0.W.n} J {i0.J.n} A {i0.A.n} V {i0.V.n} AX {i0.AX.n} SP {i0.SP.n} AL {i0.AL.n} aluOn {i0.aluOn} kroots {i0.kroots} krootsV {i0.krootsV}"
    let fam := famP9AL
    let tdir := s!"{dir}/traces/trace-{prog}"
    let tdir := if (← System.FilePath.pathExists tdir) then tdir else s!"{dir}/trace-{prog}"
    let (ders, coinMeta) ← loadMeta s!"{dir}/j8_atomChipHQL.json"
    let mut act : Array (Chip × Tr) := #[]
    for id in fam.ids do
      let q := chipOfId b0 id
      let on : Bool := if id == "axisChipJ9" then i0.axOn else if id == "splitChipJ9" then i0.spOn
        else if id == "aluChipJ9" then i0.aluOn else true
      if !on then logMsg s!"chip {id}: off, skipped (optional table)"; continue
      if id == "walkChipHQK" && i0.krootsV == 0 then logMsg s!"chip {id}: krootsV = 0 -> omitted"; continue
      if q.n == 0 then logMsg s!"chip {id}: 0 rows, skipped (empty table)"; continue
      let airP := s!"{tdir}/{id}.air.json"
      let basePath ← chipBase dir id
      let hasAir ← System.FilePath.pathExists airP
      let ch ← loadChip (if hasAir then airP else basePath)
      act := act.push (ch, trOfChip q ch.width (pubsOfRec i0 id))
    logMsg s!"loaded {act.size} chips"
    checkRounds act
    -- round-0 block: only round-0 columns are kept by proveAll (`stripAux` zeroes the rest); keep exactly block 0's
    let cp : Array UInt64 := match act.find? (fun c => c.1.id == "computeChipVCLHX9") with | some (_, tr) => tr.pub | none => #[]
    let some pubIn0 := pubInOfRec i0 cp o.catj | IO.eprintln "no pubeq (validB false) or no prims"; return 2
    let mut pubIn := pubIn0
    if o.tamperPrim then
      pubIn := { pubIn with prims := pubIn.prims.mapIdx fun i p => if i == 0 then { p with code := p.code + 1 } else p }
    if o.wrongClaim then
      pubIn := { pubIn with claimCells := pubIn.claimCells.mapIdx fun i c => if i == 0 then { c with noun := bumpTok c.noun } else c }
    IO.FS.createDirAll out
    let (src, ref) ← stagedSrc st0 o.tamperCoin
    let base := s!"{out}/{prog}"
    let chipPath (t : Nat) : String := s!"{base}-{act[t]!.1.id}.chip.json"
    let tc0 ← IO.monoMsNow
    let r ← proveAll act ders coinMeta prog chipPath 170 pubIn o.tamperPub
      (fun id => if id == "walkChipHQK" then i0.krootsV else i0.kroots) o.tamperPre fam (ders ++ yDersP) (some src) (bindPub := true)
    for n in r.notes do logMsg s!"  {n}"
    let sh ← ref.get
    let mut ok := r.ok
    -- guard: the pubIn built from the dummy-coin record equals the one from the final (FS-coin) record
    match sh.rest with
    | none => logMsg "GUARD: stage 2 never ran"; ok := false
    | some rest =>
      let cpF : Array UInt64 := (pubsOfRec rest "computeChipVCLHX9").toArray.map UInt64.ofNat
      match pubInOfRec rest cpF o.catj with
      | none => logMsg "GUARD: no pubIn from the final record"; ok := false
      | some pf =>
        if (NockvmE2E.Exec.V.pubInJ pf).compress == (NockvmE2E.Exec.V.pubInJ pubIn0).compress then
          logMsg "GUARD pubIn: dummy-coin record = FS-coin record: ok"
        else logMsg "GUARD pubIn: MISMATCH between the dummy-coin and the FS-coin record"; ok := false
      if o.nockCheck then
        match sh.b1, sh.b2 with
        | some b1, some b2 =>
          let Iq := assembleI b0 b1 b2 rest
          let v := Nock.V1J9AL.CheckJ9AL.checkJ9ALX Iq
          -- the S terminal `(1 - sL')·S` has no selector, so the last ALU row must have S1 = S2 = 0 (ext 5 / 6 = cols 109..111 / 112..114)
          if Iq.aluOn && Iq.AL.n > 0 then
            let last := Iq.AL.n - 1
            let g (c : Nat) : Nat := if h : last < Iq.AL.n then (Iq.AL.cols c ⟨last, h⟩).val else 0
            logMsg s!"LAST ALU ROW {last}: S1 = ({g 109}, {g 110}, {g 111}) S2 = ({g 112}, {g 113}, {g 114})"
          logMsg s!"NOCK-CHECK checkJ9ALX (staged record at the FS coins): {v}"
          if !v then ok := false
        | _, _ => logMsg "NOCK-CHECK: blocks missing"; ok := false
      -- coins.json (FS coins; not the PRNG placeholder)
      let coinsJ := (List.range 19).map fun (i : Nat) =>
        if h : i < 19 then Json.mkObj [("index", natJ i), ("limbs", Json.arr ((k3L (rest.χ ⟨i, h⟩)).map natJ).toArray)] else Json.null
      IO.FS.writeFile s!"{base}.coins.json" ((Json.mkObj [("prog", prog), ("family", "j9al"),
        ("driver", "fs: Tip5 Fiat-Shamir (the verifier's tip5FS transcript) via GenJ9ALXJStaged gen0/gen1/gen2"),
        ("coins", Json.arr coinsJ.toArray)]).compress ++ "\n")
    IO.FS.writeFile s!"{base}.inst.json" (instJson r.X ((Array.range act.size).map chipPath) pubIn r.slotOf).compress
    let pj := (r.π.toJson).setObjVal! "z" (NockvmE2E.Exec.V.limbsJ r.z)
    let s := pj.compress
    IO.FS.writeFile s!"{base}.proof.json" s
    let tf0 ← IO.monoMsNow
    match NockvmE2E.Exec.FixProve.proveFixFor r.X r.z r.π with
    | some πF =>
      let fs := (NockvmE2E.Exec.V.FixProof.toJson πF).compress
      IO.FS.writeFile s!"{base}.fix.json" fs
      logMsg s!"FIX PROOF written {base}.fix.json bytes={fs.utf8ByteSize} wall_ms={(← IO.monoMsNow) - tf0}"
    | none => logMsg "FIX PROOF: setup gates fail, no fix.json written"
    let tc1 ← IO.monoMsNow
    logMsg s!"PROOF RESULT ok={ok} tables={act.size} wall_ms={tc1 - tc0} proof_bytes={s.utf8ByteSize} {← peakRss}"
    logMsg s!"RESULT prog={prog} chips={act.size} self_checks={if ok then "ALL OK" else "FAILED"} wall_ms={(← IO.monoMsNow) - t0} {← peakRss}"
    pure (if ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: nockvm-e2e-j9al-prove [--subject S --formula F [--prims id:op,..] [--fuel N]  (free program; <prog> is then a file label)] [--reg-catj (Z38-1 probe: registry catJ, prog jp)] [--tamper-pub t:s] [--tamper-pre t:c:row] [--tamper-coin k] [--tamper-prim] [--wrong-claim] [--nock-check] <chips-dir> <prog: add|mul|toy|absent|jp> <out-dir>"
    pure 2

end NockvmE2E.Exec.DriveJ9AL
