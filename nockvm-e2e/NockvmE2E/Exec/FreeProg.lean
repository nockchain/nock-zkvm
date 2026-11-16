/-
  NockvmE2E/Exec/FreeProg.lean   (UNTRUSTED tooling, no theorem)

  The free-program front end shared by `nockvm-e2e-j9alemit2` and `nockvm-e2e-j9al-prove`:
  * flags `--subject S --formula F [--prims id:op,...] [--fuel N]` ↦ the tuple `progOf` returns (the positional program name is
    then only a label for the output files); without `--subject` and `--formula` the positional name is looked up in `progOf` unchanged;
  * `sideErrors`: the side conditions of `genJ9ALXJ_honest_at'` / `complJ9AL_closed_of` that can be tested before proving
    (`hnoDec`, `hnd`, `h31A`/`h31L` (table heights < 2^31), `hlimb` = `PrimLimbs62`), plus the chip-literal check of LIMITS row 7
    (the verifier accepts a walk chip only for a numeral in `famJ9AL.lits`).
-/
import NockvmE2E.Exec.J9ALConv
import NockvmE2E.Exec.J9ALChipsFam
import NockvmE2E.Exec.NounText

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.FreeProg
open Nock NockvmE2E.Exec.NounText

structure FreeOpts where
  subject : Option String := none
  formula : Option String := none
  prims : Option String := none
  fuel : Option String := none
  /-- `--allow-unverifiable`: print the chip-literal errors as WARNINGs and continue (the verifier will then REJECT) -/
  force : Bool := false

/-- pull the free-program flags out of an argument list (anywhere); the rest is returned in order -/
def extractFree (o : FreeOpts) : List String → Except String (FreeOpts × List String)
  | [] => pure (o, [])
  | "--allow-unverifiable" :: r => extractFree { o with force := true } r
  | "--subject" :: v :: r => extractFree { o with subject := some v } r
  | "--formula" :: v :: r => extractFree { o with formula := some v } r
  | "--prims" :: v :: r => extractFree { o with prims := some v } r
  | "--fuel" :: v :: r => extractFree { o with fuel := some v } r
  | [fl] =>
    if fl == "--subject" || fl == "--formula" || fl == "--prims" || fl == "--fuel" then
      throw s!"{fl} needs a value"
    else pure (o, [fl])
  | a :: r => do
    let (o', r') ← extractFree o r
    pure (o', a :: r')

def FreeOpts.any (o : FreeOpts) : Bool := o.subject.isSome || o.formula.isSome || o.prims.isSome || o.fuel.isSome

def okLabel (s : String) : Bool := !s.isEmpty && s.all fun c => c.isAlphanum || c == '_' || c == '-'

/-- the program: `(subject, formula, prims, fuel)` -/
def resolveProg (name : String) (o : FreeOpts) :
    Except String (Noun × Noun × List (ℕ × Nock.Jet.Prim.PrimOp) × ℕ) :=
  match o.subject, o.formula with
  | none, none =>
    if o.prims.isSome || o.fuel.isSome then
      .error "--prims / --fuel are only used together with --subject and --formula (they do not modify the built-in programs)"
    else match progOf name with
      | some p => .ok p
      | none => .error s!"unknown program '{name}' (built-in: add | mul | toy | absent | jp; or give --subject S --formula F)"
  | some s, some f => do
    unless okLabel name do
      throw s!"program label '{name}' must be non-empty letters, digits, '-' or '_' (it names the output files)"
    let sN ← parseNounFlag "--subject" s
    let fN ← parseNounFlag "--formula" f
    let ps ← match o.prims with | some t => parsePrims t | none => pure []
    let fuel ← match o.fuel with
      | some t => match (trimS t).toNat? with
        | some n => pure n
        | none => throw s!"--fuel: '{t}' is not a decimal number"
      | none => pure 1000
    pure (sN, fN, ps, fuel)
  | some _, none => .error "--subject given without --formula (both are needed)"
  | none, some _ => .error "--formula given without --subject (both are needed)"

def limbs62Bound : Nat := 2 ^ (32 * 62)

/-- the program-level side conditions that need no generator run -/
def progErrors (primsR : List (ℕ × Nock.Jet.Prim.PrimOp)) : List String :=
  (primsR.filterMap fun q =>
    if q.2 == .dec then
      some s!"prim {q.1}:dec is excluded by the theorem (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec); use sub/lt/add/mul/div/mod"
    else none) ++
  (if (primsR.map Prod.fst).Nodup then [] else
    [s!"prim ids {primsR.map Prod.fst} contain a duplicate (hnd : (prims.map Prod.fst).Nodup)"])

/-- the chip-literal check (LIMITS row 7): the walk chips are verifier-accepted only for the numerals of `famJ9AL.lits` -/
def chipErrors (I : Nock.V1J9AL.CheckJ9AL.InJ9AL) : List String :=
  let nums (id : String) : List Nat := (NockvmE2E.Exec.J9ALChips.famJ9AL.lits id).map (·.1)
  -- mirrors `BndJ9AL.numOkB`: numeral ∈ lits, and for the walk tables numeral ≤ rows
  let one (id tab : String) (k rows : Nat) (walk : Bool) : List String :=
    (if (nums id).contains k then [] else
      [s!"CHIP-LITERAL MISSING: table {tab} ({id}) needs numeral {k} but the verifier's literal list has only {nums id}; " ++
       s!"the verifier will REJECT this program (LIMITS row 7: every chip must equal a literal in famJ9AL.lits). " ++
       s!"Needs: a new Exec/J9ALChipsK_* literal for {id} with numeral {k} and its tie_* theorem, then a rebuilt verifier"]) ++
    (if walk && k > rows then
      [s!"CHIP-LITERAL MISSING: table {tab} ({id}) has numeral {k} > its {rows} rows (numOkB needs numeral ≤ rows); the verifier will REJECT this program"]
     else [])
  (one "walkChipJ8" "W (walk, kroots)" I.kroots I.W.n true) ++
  (if I.krootsV == 0 then [] else one "walkChipHQK" "V (walk, krootsV)" I.krootsV I.V.n true) ++
  (if I.spOn then one "splitChipJ9" "SP (split, A.n)" I.A.n I.A.n false else [])

/-- the post-generation side conditions on the instance record `I` of the run `(R, fuel, s, f)` -/
def sideErrors (R : Nock.Jet.Registry) (primsR : List (ℕ × Nock.Jet.Prim.PrimOp)) (fuel : ℕ) (s f : Noun)
    (I : Nock.V1J9AL.CheckJ9AL.InJ9AL) : List String :=
  let bound := 2 ^ 31
  let hs : List (String × Nat) := [("X", I.X.n), ("C", I.C.n), ("W", I.W.n), ("J", I.J.n), ("A", I.A.n), ("V", I.V.n),
    ("AX", I.AX.n), ("SP", I.SP.n), ("AL", I.AL.n)]
  let rowErrs := hs.filterMap fun (nm, n) =>
    if n < bound then none else
      some s!"table {nm} has {n} rows >= 2^31 (h31A / h31L: Rows31A and aluLen < 2^31)"
  let limbErrs : List String :=
    match Nock.V1J8.Gen.runX R fuel s f with
    | none => []
    | some Rn =>
      let pids := primsR.map Prod.fst
      (Nock.V1J8.Gen.callsOf Rn.rows).filterMap fun (id, subj) =>
        if !pids.contains id then none else
        match subj with
        | .cell (.atom a) (.atom b) =>
          if a < limbs62Bound && b < limbs62Bound then none else
            some s!"prim call id {id}: operand has more than 62 limbs of 2^32 (PrimLimbs62): {if a < limbs62Bound then "second" else "first"} operand too large"
        | _ => some s!"prim call id {id}: operands are not two atoms (the ALU chip needs atom operands)"
  rowErrs ++ limbErrs ++ chipErrors I

end NockvmE2E.Exec.FreeProg
