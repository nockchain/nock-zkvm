/-
  NockvmE2E/Exec/ProverMain.lean
  usage: nockvm-e2e-prove [--check-coins] [--tamper-pub t:slot] [--tamper-pre t:c:row] [--family j8|j9a|j9al] <emitted-dir> <prog> <out-dir>
  ONE proof for all chips: <out-dir>/<prog>.{inst,proof}.json (+ <prog>-<chip>.chip.json, one verifier DAG per table).
  Run under a memory cap.  Prints self-checks, wall time, peak RSS (VmHWM) and proof bytes.
-/
import NockvmE2E.Exec.FlatProver
import NockvmE2E.Exec.AuxFill
import NockvmE2E.Exec.PubExe9
import NockvmE2E.Exec.FixProve
set_option autoImplicit false

open Lean NockvmE2E.Exec.PE NockvmE2E.Exec.Aux NockvmE2E.Exec.PF NockvmE2E.Exec.Tr NockvmE2E.Exec.J NockvmE2E.Exec.FP NockvmE2E.Exec.Tip5Core

def selfTest : IO Bool := do
  let mut ok := true
  let p := NockvmE2E.Exec.PF.P.toNat
  let mut a : UInt64 := 0x123456789abcdef
  let mut b : UInt64 := 0xfedcba987654321
  for _ in [0:20000] do
    a := (a * 6364136223846793005 + 1442695040888963407) % NockvmE2E.Exec.PF.P
    b := (b * 6364136223846793005 + 1) % NockvmE2E.Exec.PF.P
    if (mul a b).toNat != a.toNat * b.toNat % p then ok := false
    if (add a b).toNat != (a.toNat + b.toNat) % p then ok := false
    if (sub a b).toNat != (a.toNat + p - b.toNat) % p then ok := false
  if mul (NockvmE2E.Exec.PF.P - 1) (NockvmE2E.Exec.PF.P - 1) != 1 then ok := false
  let u := (Array.range 16).map fun i => UInt64.ofNat (i * i * 977 + 3 * i + 5)
  let w := root 4
  let f := ntt u 4 w
  for j in [0:16] do
    let mut acc : F := 0
    for i in [0:16] do acc := add acc (mul u[i]! (pow w (i * j)))
    if acc != f[j]! then ok := false
  if intt f 4 w != u then ok := false
  if mul 12345 (inv 12345) != 1 then ok := false
  let e : E3 := ⟨5, 6, 7⟩
  if E3.mul e (E3.inv e) != E3.one then ok := false
  pure ok

def peakRss : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  pure ((s.splitOn "\n").filter (·.startsWith "VmHWM") |>.headD "VmHWM: ?")

def checkCoins (act : Array (Chip × Tr)) (slots : Array E3) (ders : Array Der) (coinMeta : Array (Nat × Nat)) : IO Bool := do
  let mut ok := true
  let frame2 := frameOf (coinMeta.toList.map fun (i, _) => (i, slots[i]!))
  let frame1 := frameOf (coinMeta.toList.filterMap fun (i, sa) => if sa == 0 then some (i, slots[i]!) else none)
  let comp := completeSlots frame2 ders
  let mut dm := 0
  for d in ders do if comp[d.slot]! != slots[d.slot]! then dm := dm + 1
  logMsg s!"derived gamma'-power slots recomputed vs coins.json: {ders.size} slots, {dm} mismatches"
  if dm != 0 then ok := false
  let mut cur : Array (Chip × Tr) := act.map fun (ch, tr) => (ch, stripAux ch tr)
  for stage in [1, 2] do
    cur ← fillAll cur ders stage (if stage == 1 then frame1 else frame2)
  for i in [0:cur.size] do
    let (ch, tr) := act[i]!
    let (_, tr') := cur[i]!
    let mut mism := 0
    let mut cells := 0
    let mut first : Option (Nat × Nat) := none
    let mut badExts : Array (Nat × Nat × Nat) := #[]   -- (ext index, first row, count)
    for c in [0:ch.width] do
      if ch.colRound[c]! > 0 then
        for r in [0:tr.nRows] do
          cells := cells + 1
          if tr.cols[c]![r]! != tr'.cols[c]![r]! then
            mism := mism + 1
            if first.isNone then first := some (c, r)
            if c ≥ ch.baseCols then
              let e := (c - ch.baseCols) / 3
              match badExts.findIdx? (·.1 == e) with
              | some q => badExts := badExts.modify q fun (a, b, k) => (a, b, k + 1)
              | none => badExts := badExts.push (e, r, 1)
    let pm := (Array.range tr.pub.size).filter (fun k => tr.pub[k]! != tr'.pub[k]!)
    logMsg s!"CHECK-COINS {ch.id}: aux cells {cells}, mismatches {mism}{match first with | some (c, r) => s!" (first: col {c} row {r})" | none => ""}; publics {tr.pub.size}, mismatches {pm.size}{if pm.isEmpty then "" else s!" (first: slot {pm[0]!})"}"
    if !badExts.isEmpty then logMsg s!"    mismatched ext cols (ext, first row, #cells): {badExts.toList}"
    for (e, r, _) in badExts.extract 0 6 do
      let g (t : Tr) (k : Nat) : Nat := t.cols[ch.baseCols + 3 * e + k]![r]!.toNat
      logMsg s!"      ext {e} row {r}: dump ({g tr 0},{g tr 1},{g tr 2}) own ({g tr' 0},{g tr' 1},{g tr' 2})"
    if mism != 0 || !pm.isEmpty then ok := false
  pure ok

/-- claim cells / registry pins of `pubeq.json` (`{k | id, idx, hi, lo, noun: ["c", "1", ...]}`) -/
def nounRecOf (keyField : String) (j : Json) : NounRec :=
  { key := nat (get j keyField), idx := nat (get j "idx"), hi := nat (get j "hi"), lo := nat (get j "lo")
    noun := (arr (get j "noun")).toList.map fun t =>
      match t.getStr? with
      | .ok "c" => .cell
      | .ok s => .atom s.toNat!
      | .error _ => .atom (nat t) }

-- P10 debug: the conjuncts of `PE.checkPubEq9`, one by one (a copy of its body; the verifier file is untouched).
open NockvmE2E.Exec.VF in
def pubDbg (inp : PubIn) (coins : Array K3) (ps : Array (Array UInt64)) : List (String × Bool) :=
  let coinAt (i : Nat) : K3 := coins[i]!
  let pair (a b : Nat) : K6 := ⟨coinAt a, coinAt b⟩
  let z := pair 2 3
  let y := pair 17 18
  let gh := pair 11 15
  let rh := pair 12 16
  let gv := pair 4 6
  let rv := pair 5 7
  let x := ps[0]!
  let c3 (lo : Nat) : K3 := ⟨x[lo]!, x[lo + 1]!, x[lo + 2]!⟩
  let rho3 : K6 := ⟨c3 15, c3 21⟩
  let rho4 : K6 := ⟨c3 18, c3 24⟩
  let rhoS : K6 := ⟨c3 27, c3 30⟩
  let label (j : Nat) : Nat := x[j]!.toNat
  let claimRec (c : NounRec) : Option (List K6) := do
    let big := match c.noun with
      | [.atom n] => decide (n ≥ PN)
      | _ => false
    let kind := if big then 2 else 1
    if c.key > 2 || label (2 * c.key) != kind then none else
    let e ← enc z y c.noun
    pure (claimVec e (label (2 * c.key + 1)) (if big then 0 else c.hi) (if big then 0 else c.lo))
  let pinRec (q : NounRec) : Option (List K6) := do
    let e ← enc z y q.noun
    pure (claimVec e q.idx q.hi q.lo)
  let r : Option (List (String × Bool)) := do
    let cr ← inp.claimCells.mapM claimRec
    let pr ← inp.pins.mapM pinRec
    let sClaim := (cr ++ pr).foldl (fun s r => K6.add s (compress gv rv r).inv0) K6.zero
    let sPin := inp.pins.foldl (fun s q => K6.add s (compress gh rh (pinConsKey q.key q.idx)).inv0) K6.zero
    let w0 ← pp ps[2]! pubXQ
    let j2 ← pp ps[3]! 2
    let ch ← pp ps[1]! pubHQ
    let w1 ← pp ps[2]! pubPQ
    let axp ← pp ps[6]! pubAXp
    let axs ← pp ps[6]! pubAXs
    let sps ← pp ps[7]! pubSPs
    let j0 ← pp ps[3]! 0
    let aMI ← pp ps[4]! pubMI
    let v1 ← pp ps[5]! pubPQ
    let c0 ← pp ps[1]! 0
    let aMB ← pp ps[4]! pubMB
    let aHQ ← pp ps[4]! pubHQ
    let aC ← pp ps[4]! pubC
    let v0 ← pp ps[5]! pubXQ
    let a0 ← kv ps[4]! 0
    let a1 ← kv ps[4]! 1
    let a2 ← kv ps[4]! 2
    let a3 ← kv ps[4]! 3
    let c2 ← kv ps[1]! 2
    let c3' ← kv ps[1]! 3
    let wk0 ← kv ps[2]! 0
    let wk1 ← kv ps[2]! 1
    let va0 ← kv ps[5]! 0
    let va1 ← kv ps[5]! 1
    pure [("computeDerivedOk", computeDerivedOk inp coins x),
          ("c1 rho3+w0+j2=ch", K6.add rho3 (K6.add w0 j2) == ch),
          ("c2 rho4+axp=w1", K6.add rho4 axp == w1),
          ("c3 rhoS+sPin+j0+axs=aMI+v1+sps", K6.add (K6.add (K6.add rhoS sPin) j0) axs == K6.add (K6.add aMI v1) sps),
          ("c4 sClaim=c0+aMB", sClaim == K6.add c0 aMB),
          ("c5 aHQ=aC+v0", aHQ == K6.add aC v0),
          ("c6 a0,a1 zero", a0.isZero && a1.isZero),
          ("c7 c2=wk0,c3=wk1", c2 == wk0 && c3' == wk1),
          ("c8 a2=va0,a3=va1", a2 == va0 && a3 == va1)]
  r.getD [("OPTION NONE (claim rec / enc / slice shape)", false)]

/-- P10 isolation test: row-check the DUMPED trace (dumped aux columns, dumped publics) under the DUMPED coins; no refill. -/
def rowCheckDump (act : Array (Chip × Tr)) (slots : Array E3) (srcs : Array (Array String)) : IO Bool := do
  let mut ok := true
  for i in [0:act.size] do
    let (ch, tr) := act[i]!
    let n := tr.nRows
    let mut bad := 0
    let mut firstL : Array String := #[]
    for r in [0:n] do
      let cur := (Array.range ch.width).map fun c => E3.ofF tr.cols[c]![r]!
      let next := (Array.range ch.width).map fun c => if r + 1 < n then E3.ofF tr.cols[c]![r + 1]! else E3.zero
      let vals := evalCons ch { cur := cur, next := next, pub := tr.pub, chal := slots, bc := ch.baseCols }
      for ci in [0:ch.cons.size] do
        let k := ch.cons[ci]!.kind
        let applies := match k with | 0 => true | 1 => r + 1 < n | 2 => r == 0 | _ => r + 1 == n
        if applies && vals[ci]! != E3.zero then
          bad := bad + 1
          if firstL.size < 8 then firstL := firstL.push s!"constraint {ci} (round {ch.cons[ci]!.round}) row {r} source={srcs[i]![ci]!}"
    logMsg s!"ROWCHECK-DUMP {ch.id}: rows {n}, violations {bad}"
    for l in firstL do logMsg s!"    {l}"
    if bad != 0 then ok := false
  pure ok

/-- the chip document of `id`: the family's own emission (`j9al_<id>` for the ALU, `j9a_<id>` for the three J-9 A chips) else the J-8 emission -/
def chipBase (fam : String) (dir id : String) : IO String := do
  let j9alP := s!"{dir}/j9al_{id}.json"
  let j9P := s!"{dir}/j9a_{id}.json"
  if fam == "j9al" && (← System.FilePath.pathExists j9alP) then pure j9alP
  else if fam != "j8" && (← System.FilePath.pathExists j9P) then pure j9P
  else pure s!"{dir}/j8_{id}.json"

/-- the J-9 AL y-power derived slots (`Emit.ChipsJ9AL.yDers`: pair (17, 18), powers 0..32, slots 41..106) -/
def yDersP : Array Der :=
  ((List.range 33).flatMap fun (t : Nat) =>
    [(⟨41 + 2 * t, 17, 18, t, true⟩ : Der), ⟨42 + 2 * t, 17, 18, t, false⟩]).toArray

def main (args : List String) : IO UInt32 := do
  let rcd := args.head? == some "--rowcheck-dump"
  let args := if rcd then args.tail else args
  let check := args.head? == some "--check-coins"
  let args1 := if check then args.tail else args
  -- `--tamper-pub t:s`: table t, public slot s += 1 before commitment (test only)
  let (tamper, args2) : Option (Nat × Nat) × List String :=
    match args1 with
    | "--tamper-pub" :: ts :: rest =>
      match ts.splitOn ":" with
      | [t, s] => (some (t.toNat!, s.toNat!), rest)
      | _ => (none, rest)
    | _ => (none, args1)
  -- `--tamper-pre t:c:row` (B3V-2): table t, preprocessed column c (local), row: committed value += 1 before commitment (test only)
  let (tamperPre, args3) : Option (Nat × Nat × Nat) × List String :=
    match args2 with
    | "--tamper-pre" :: ts :: rest =>
      match ts.splitOn ":" with
      | [t, c, r] => (some (t.toNat!, c.toNat!, r.toNat!), rest)
      | _ => (none, rest)
    | _ => (none, args2)
  -- P9 `--family j8|j9a` (default j8): the chip family (table layout, public relation `pubMode`)
  let (famName, args4) : String × List String :=
    match args3 with
    | "--family" :: f :: rest => (f, rest)
    | _ => ("j8", args3)
  let some fam := famP? famName | IO.eprintln s!"unknown family {famName} (j8 | j9a | j9al)"; return 2
  match args4 with
  | dir :: prog :: out :: _ =>
    let t0 ← IO.monoMsNow
    logMsg s!"family {fam.name} (pubMode {fam.pubMode}, {fam.tabLens.size} public tables)"
    logMsg s!"self-test (field, NTT, E3): {if (← selfTest) then "ok" else "FAILED"}"
    -- the whole batch is ONE proof (all non-empty tables)
    let ids := fam.ids
    let tdir := s!"{dir}/traces/trace-{prog}"
    let tdir := if (← System.FilePath.pathExists tdir) then tdir else s!"{dir}/trace-{prog}"
    let slots0 ← loadSlots s!"{tdir}/coins.json"
    --  (j9al): the dump's y-power slots 41..106 (`derived_y`), for `--check-coins`
    let slots ← if fam.name != "j9al" then pure slots0 else do
      let d ← readJson s!"{tdir}/coins.json"
      let mut sl := slots0 ++ Array.replicate (107 - slots0.size) E3.zero
      for c in arr (get d "derived_y") do
        let l := arr (get c "limbs")
        sl := sl.set! (nat (get c "slot")) ⟨u64 l[0]!, u64 l[1]!, u64 l[2]!⟩
      pure sl
    let krootsV := nat (get (← readJson s!"{tdir}/coins.json") "krootsV")
    let krootsJ := nat (get (← readJson s!"{tdir}/coins.json") "kroots")
    let (ders, coinMeta) ← loadMeta s!"{dir}/j8_atomChipHQL.json"
    let mut act : Array (Chip × Tr) := #[]
    for id in ids do
      -- a trace dir may ship a newer emission of the chip (`<id>.air.json`, e.g. walk chips of trace-add/ne5/mat); it wins
      let airP := s!"{tdir}/{id}.air.json"
      -- j9a: the chip file `j9a_<id>.json` (the three new chips) else the J-8 emission `j8_<id>.json` (unchanged chips)
      let basePath ← chipBase fam.name dir id
      let trP := s!"{tdir}/{id}.trace.json"
      -- j9a only: the optional tables (axis, split) are skipped when the dump has no trace for them
      if fam.name != "j8" && (id == "axisChipJ9" || id == "splitChipJ9" || id == "aluChipJ9") && !(← System.FilePath.pathExists trP) then
        logMsg s!"chip {id}: no trace file, skipped (optional table)"
        continue
      let ch ← loadChip (if (← System.FilePath.pathExists airP) then airP else basePath)
      let tr ← loadTrace trP ch
      if id == "walkChipHQK" && krootsV == 0 then
        logMsg s!"chip {id}: krootsV = 0 -> omitted (atom-walk publics are the constant 0; S4-RESULT step 3)"
      else if tr.nRows == 0 then
        logMsg s!"chip {id}: 0 rows, skipped (empty table)"
      else act := act.push (ch, tr)
    logMsg s!"loaded {act.size} chips"
    if rcd then
      let mut srcs : Array (Array String) := #[]
      for (ch, _) in act do
        let airP := s!"{tdir}/{ch.id}.air.json"
        let bp ← chipBase fam.name dir ch.id
        let d ← readJson (if (← System.FilePath.pathExists airP) then airP else bp)
        srcs := srcs.push ((arr (get (arr (get d "chips"))[0]! "constraints")).map fun j =>
          match (get j "source").getStr? with | .ok s => s | .error _ => "?")
      let ok ← rowCheckDump act slots srcs
      let pe ← readJson s!"{tdir}/pubeq.json"
      let compute := act.find? (fun c => c.1.id == "computeChipVCLHX9")
      let atoms : List (Nat × Nat) := match compute with
        | some (_, tr) => (List.range 3).filterMap fun k => if tr.pub[2 * k]! == 0 then some (k, tr.pub[2 * k + 1]!.toNat) else none
        | none => []
      let pubIn : PubIn := { claimCells := (arr (get pe "claim")).toList.map (fun j => { nounRecOf "k" j with idx := 0 }), pins := (arr (get pe "pins")).toList.map (nounRecOf "id"), atoms := atoms }
      let ps : Array (Array UInt64) := (List.range 8).toArray.map fun t =>
        match act.find? (fun c => fam.tabOf c.1.id == some t) with
        | some (_, tr) => tr.pub
        | none => Array.replicate (fam.tabLens[t]!) 0
      let coins19 : Array NockvmE2E.Exec.VF.K3 := (Array.range 19).map fun i => k3ofe slots[i]!
      for (nm, b) in pubDbg pubIn coins19 ps do logMsg s!"PUBDBG {nm}: {b}"
      logMsg s!"ROWCHECK-DUMP RESULT prog={prog} {if ok then "ALL OK" else "VIOLATIONS"}"
      return (if ok then 0 else 1)
    if check then
      let ok ← checkCoins act slots (if fam.name == "j9al" then ders ++ yDersP else ders) coinMeta
      logMsg s!"CHECK-COINS RESULT prog={prog} {if ok then "0 MISMATCHES" else "MISMATCHES FOUND"}"
      return (if ok then 0 else 1)
    IO.FS.createDirAll out
    -- the claim: claim cells + registry pins from `pubeq.json`; claim positions that are plain atoms from the compute labels
    let pe ← readJson s!"{tdir}/pubeq.json"
    let compute := act.find? (fun c => c.1.id == "computeChipVCLHX" || c.1.id == "computeChipVCLHX9")
    let atoms : List (Nat × Nat) := match compute with
      | some (_, tr) => (List.range 3).filterMap fun k =>
          if tr.pub[2 * k]! == 0 then some (k, tr.pub[2 * k + 1]!.toNat) else none
      | none => []
    let pubIn0 : PubIn :=
      { claimCells := (arr (get pe "claim")).toList.map (fun j => { nounRecOf "k" j with idx := 0 }), pins := (arr (get pe "pins")).toList.map (nounRecOf "id"), atoms := atoms }
    --  (LINK F-A): claim records carry idx := 0 (Lean `claimRec` fixes it; the verifier ignores the field).
    -- P10: J-9 A big-atom claim.  nockvm's pubeq.json `claim` lists only the CELL claims; a compute label of kind 2 (big atom) at claim
    -- position k has no record, but the verifier's `claimRec` needs `{key k, [.atom n], idx := label(2k+1)}` (rank (0,0)).  A `claim`
    -- entry with `k` and a single-atom noun in pubeq.json is used as is; otherwise (FALLBACK, labelled) the unique big atom
    -- (>= PN) occurring in the claim cells' nouns is taken (for `absent` the product p+5 is the head of the subject).
    let extra : List NounRec := match compute with
      | some (_, tr) => (List.range 3).filterMap fun k =>
          if tr.pub[2 * k]! == 2 && !(pubIn0.claimCells.any (·.key == k)) then
            let bigs := pubIn0.claimCells.flatMap fun c => c.noun.filterMap fun t => match t with
              | .atom n => if n ≥ NockvmE2E.Exec.VF.PN then some n else none
              | _ => none
            match bigs with
            | n :: _ => some { key := k, idx := 0, hi := 0, lo := 0, noun := [.atom n] }
            | [] => none
          else none
      | none => []
    --  (j9al): the key-2 record is REQUIRED (J9ALEmit writes it); a missing record is a hard error, no guessing
    let missing2 : List Nat := match compute with
      | some (_, tr) => (List.range 3).filter fun k => tr.pub[2 * k]! == 2 && !(pubIn0.claimCells.any (·.key == k))
      | none => []
    if fam.name == "j9al" && !missing2.isEmpty then
      IO.eprintln s!"j9al: claim key(s) {missing2} are big atoms (compute label 2) but pubeq.json has no key record; refusing to guess"
      return 2
    let extra : List NounRec := if fam.name == "j9al" then [] else extra
    let prims : List PrimRec ← if fam.name == "j9al" then
        match pe.getObjVal? "prims" with
        | .ok pj => pure ((arr pj).toList.map fun j => { id := nat (get j "id"), code := nat (get j "code"), idx := nat (get j "idx"), hi := nat (get j "hi"), lo := nat (get j "lo") })
        | .error _ => do IO.eprintln "j9al: pubeq.json has no `prims` array"; return 2
      else pure []
    for e in extra do logMsg s!"claim key {e.key}: no record in pubeq.json; big-atom FALLBACK atom {match e.noun with | [.atom n] => n | _ => 0}"
    let pubIn : PubIn := { pubIn0 with claimCells := pubIn0.claimCells ++ extra, prims := prims }
    let base := s!"{out}/{prog}"
    let chipPath (t : Nat) : String := s!"{base}-{act[t]!.1.id}.chip.json"
    let tc0 ← IO.monoMsNow
    let r ← proveAll act ders coinMeta prog chipPath 170 pubIn tamper (fun id => if id == "walkChipHQK" then krootsV else krootsJ) tamperPre fam
      (if fam.name == "j9al" then ders ++ yDersP else #[])
    for n in r.notes do logMsg s!"  {n}"
    if !r.ok then
      let ps : Array (Array UInt64) := (List.range 8).toArray.map fun t =>
        match (Array.range act.size).find? (fun i => fam.tabOf act[i]!.1.id == some t) with
        | some i => r.pubsT[i]!
        | none => Array.replicate (fam.tabLens[t]!) 0
      let coins19 : Array NockvmE2E.Exec.VF.K3 := (Array.range 19).map fun i => k3ofe r.frame2[i]!
      for (nm, b) in pubDbg pubIn coins19 ps do logMsg s!"PUBDBG(own) {nm}: {b}"
    IO.FS.writeFile s!"{base}.inst.json" (instJson r.X ((Array.range act.size).map chipPath) pubIn r.slotOf).compress
    let pj := (r.π.toJson).setObjVal! "z" (NockvmE2E.Exec.V.limbsJ r.z)
    let s := pj.compress
    IO.FS.writeFile s!"{base}.proof.json" s
    -- the side proof πF over the fixed columns (j9a only; the main proof above is unchanged)
    if fam.name == "j9a" || fam.name == "j9al" then
      let tf0 ← IO.monoMsNow
      match NockvmE2E.Exec.FixProve.proveFixFor r.X r.z r.π with
      | some πF =>
        let fs := (NockvmE2E.Exec.V.FixProof.toJson πF).compress
        IO.FS.writeFile s!"{base}.fix.json" fs
        logMsg s!"FIX PROOF written {base}.fix.json bytes={fs.utf8ByteSize} wall_ms={(← IO.monoMsNow) - tf0}"
      | none => logMsg "FIX PROOF: setup gates fail, no fix.json written"
    let tc1 ← IO.monoMsNow
    logMsg s!"PROOF RESULT ok={r.ok} tables={act.size} wall_ms={tc1 - tc0} proof_bytes={s.utf8ByteSize} {← peakRss}"
    let t1 ← IO.monoMsNow
    logMsg s!"RESULT prog={prog} chips={act.size} self_checks={if r.ok then "ALL OK" else "FAILED"} wall_ms={t1 - t0} {← peakRss}"
    pure (if r.ok then 0 else 1)
  | _ =>
    IO.eprintln "usage: nockvm-e2e-prove [--check-coins] [--tamper-pub t:slot] [--tamper-pre t:c:row] [--family j8|j9a|j9al] <emitted-dir> <prog> <out-dir>"
    pure 2
