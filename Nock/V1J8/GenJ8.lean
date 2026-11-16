/-
  Nock/V1J8/GenJ8.lean

  **The general J-8 tracegen, assembled.**

  `genJ8 R fuel s f χe : Option InJ8` runs `genX R fuel s f`, then
  * compute (`compGen`, 123 columns, `ρ₃ ρ₄ ρ_S` from the accumulator totals),
  * cells (`cellsOfRoots`: the claim's nouns and every row's six handle nouns, first-occurrence pre-order; the
    handle map `hdl`), walk (`walkGen` over the path reads), multiplicities (`mvCounts`, `mxCounts`, `mhCounts`),
    the cell KW rows (`cellGen`) and the walk J8 rows (`walkGenRows`),
  * the atom table as the inert pad row (`FillMem.Atom`, B4753), the atom walk absent (`krootsV = 0`), J absent,
  * orbit heights: the least `h ≥ 1` with `rows ≤ 3·2^h`, generators `ω6g` at `h = 1`, `7^((p−1)/(3·2^h))` above,
  * budgets `RowsJ8` all `max 10 (2·(largest table))`.
  **Scope (stated, checked at run time):** no big atom in any handle noun, no jet call (`R` may be non-empty; a
  run that calls a jet or touches a big atom is refused, `none`).
-/
import Nock.V1J8.GenMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-- The least `h ≥ 1` with `n ≤ 3·2^h` (fuel `64`). -/
def hOf (n : ℕ) : ℕ := go 64 1
where
  go : ℕ → ℕ → ℕ
    | 0, h => h
    | k + 1, h => if n ≤ 3 * 2 ^ h then h else go k (h + 1)

/-- An element of exact order `3·2^h` (`ω6g` at `h ≤ 1`; `7` generates `𝔽_p^×`). -/
def ωOf (h : ℕ) : Gold :=
  if h ≤ 1 then Example.ω6g else Gold.pow (Gold.ofU64 7) ((P - 1) / (3 * 2 ^ h))

/-- A chip input from a row table. -/
def chipOf (tbl : Array (Array (ZMod P))) : ChipIn :=
  ⟨hOf tbl.size, tbl.size, ωOf (hOf tbl.size), colsOf tbl tbl.size⟩

/-- The budgets: every field `max 10 (2·m)`, `m` the largest table. -/
def budget (m : ℕ) : RowsJ8 :=
  let B := max 10 (2 * m)
  ⟨B, B, B, B, B, B, B, B, B, B, B, B, B, B, B⟩

/-- Every handle noun's atoms are small (`< p`). -/
def smallAtoms (rows : Array RowNX) : Bool :=
  (rows.toList.flatMap fun r => (rowHandleNounsX r).flatMap leavesOf).all fun a => decide (a < P)

/-- No row is a jet call. -/
def noJets (rows : Array RowNX) : Bool := rows.toList.all fun r => !(decide (r.st = .s11j))

/-- **The J-8 tracegen.** -/
def genJ8 (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) : Option InJ8 :=
  match runX R fuel s f with
  | none => none
  | some Rn =>
    if !(smallAtoms Rn.rows && noJets Rn.rows) then none else
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let cs := cellsOfRoots (rootsOf c Rn.rows)
    let H := hdl cs
    let comp := compGen c H Rn χe
    let (ws, kr) := walkGen (cs.headD (.atom 0)) (pathReads Rn.rows)
    let mv := mvCounts cs c
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := mhCounts cs comp.bases ws
    let k := coOf χe
    let (cR, cP) := cellGen k (yE χe) cs mv mx mx1 mh
    let (wR, wP) := walkGenRows k (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) cs ws kr
    let m := max comp.rows.size (max cR.size wR.size)
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cP, pubsW := wP,
               pubsJ := fun _ => 0, pubsA := fun _ => 0, pubsV := fun _ => 0 }
        χ := χe
        r := budget m
        g := 0
        X := chipOf comp.rows
        C := chipOf cR
        W := chipOf wR
        J := ⟨1, 0, Example.ω6g, fun _ => Fin.elim0⟩
        A := ⟨1, 1, Example.ω6g, Atom.cols (coOfA χe) (zE χe)⟩
        V := ⟨1, 1, Example.ω6g, fun _ _ => 0⟩
        kroots := kr
        krootsV := 0
        lay := Fin.elim0
        Rt := Example.RtG
        regs := []
        ids := []
        idx := fun _ => 0
        rk := fun _ => (0, 0) }

/-- A deterministic pseudo-random coin vector (splitmix-style mixing of `(seed, i, limb)` into `[0, p)`).  `χ0` is
degenerate for runs of more than one row (its walk coin `χ₁₃ = 1` has order `1`, so `count − ln = 0`); the
generated programs are checked at these coins (any coin outside the honest bad events is accepted). -/
def mixU (x : ℕ) : ℕ :=
  let x := (x + 0x9E3779B97F4A7C15) % 2 ^ 64
  let x := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9 % 2 ^ 64
  let x := (x ^^^ (x >>> 27)) * 0x94D049BB133111EB % 2 ^ 64
  x ^^^ (x >>> 31)

def prngCoins (seed : ℕ) : CoinsE := fun i =>
  ⟨natG (mixU (seed * 1000 + 3 * (i : ℕ)) % P), natG (mixU (seed * 1000 + 3 * (i : ℕ) + 1) % P),
   natG (mixU (seed * 1000 + 3 * (i : ℕ) + 2) % P)⟩

/-- Bump one column of one row of a chip. -/
def bumpCol (q : ChipIn) (c : ℕ) (i : ℕ) : ChipIn :=
  ⟨q.h, q.n, q.ω, fun c' i' => if c' = c ∧ (i' : ℕ) = i then q.cols c' i' + 1 else q.cols c' i'⟩

def cellTamper (I : InJ8) : String × InJ8 :=
  match (List.finRange I.C.n).find? (fun i => I.C.cols 6 i == 0) with
  | some i => (s!"cell base column 8 (row {i.val} right atom)", { I with C := bumpCol I.C 8 i })
  | none => ("cell base column 4 (row 0 right serial idR)", { I with C := bumpCol I.C 4 0 })

/-- **Ten one-change tampers of any input** (each must be rejected). -/
def tampersOf (I : InJ8) : List (String × InJ8) :=
  [("coin chi4 changed at the check (traces fixed)", { I with χ := Example.bump I.χ }),
   cellTamper I,
   ("compute rho3 public", { I with M := { I.M with ρ := fun i => if (i : ℕ) = 3 then I.M.ρ i + 1 else I.M.ρ i } }),
   ("walk import public", { I with M := { I.M with pubsW := fun j => if j = 0 then I.M.pubsW 0 + 1 else I.M.pubsW j } }),
   ("atom column (mb inverse limb)", { I with A := bumpCol I.A 313 0 }),
   ("orbit generator of the wrong order", { I with C := ⟨I.C.h, I.C.n, Gold.ofU64 7, I.C.cols⟩ }),
   ("zero row budget", { I with r := { I.r with N := 0 } }),
   ("compute walk column (ln, last row)", { I with X := bumpCol I.X 111 (I.X.n - 1) }),
   ("atom-walk dispatch krootsV = 1", { I with krootsV := 1 }),
   ("wrong claimed result", { I with c := ⟨I.c.subject, I.c.formula, .cell I.c.result (.atom 0)⟩ })]

end Nock.V1J8.Gen
