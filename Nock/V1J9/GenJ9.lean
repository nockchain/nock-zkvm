/-
  Nock/V1J9/GenJ9.lean

`genJ9A R fuel s f χe` is `genJ8A` with exactly two changes (the honest J-9 prover):
  * **the compute publics are `pubVJ9E`** (`compGenB9`): the claim label carries the J-9 handle (`claimKH`: a big
    claim atom is `(2, atom-table root serial)`, the handle `hdlB` already gives every big atom), and the walk seed is
    `seedJ9E` over that label;
  * **the atom table exports every big claim atom** (`mbCounts9`): `mb` at an atom root is the number of cell-table
    big children (J-8, `mbCounts`) PLUS the number of claim positions holding that big atom (`claimBigs`), so the
    verifier's big-leaf claim records `claimVec (E (atom n)) idx 0 0` (`claimRecsJ9`, `hsumC'`) are served by the g5
    terminal even when no cell row references the atom.
  Everything else (handles, cells, walks, the inc chain, the atom walk) is `genJ8A`'s.

-/
import Nock.V1J8.GenAtomBig
import Nock.V1J9.CheckJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9.Gen9

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs)
open Nock.V1J9.Check9

/-- **The J-9 compute tracegen**: `compGenB` at the J-9 publics `pubVJ9E`. -/
def compGenB9 (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (Rn : RunX)
    (χe : CoinsE) : CompOut :=
  let m := mOf c H
  let bs := basesOfB H pd Rn
  let ρ := rhoOfB χe bs
  let pub0 := pubVJ9E c m ρ 0 χe
  let tot := (prefixSums 18 (bs.map fun b => termRow b (invsOf (envX b pub0 χe)))).2
  let ρS : K6 := ⟨CompX.readK (fun c => tot.getD c 0) 12, CompX.readK (fun c => tot.getD c 0) 15⟩
  ⟨compTable H Rn (pubVJ9E c m ρ ρS χe) χe bs, ρ, ρS, bs⟩

/-- **`mb` with the claim's big atoms**: `mbCounts` plus one per claim position holding a big atom (at its root). -/
def mbCounts9 (acsL cs : List Noun) (c : P8PublicClaim) : Array ℕ :=
  ((claimBigs P c).map fun k => FrameVS.claimNoun c k).foldl (fun a n => match bigIdOf acsL n with
    | some i => bump a i 1
    | none => a) (mbCounts acsL cs)

/-- **The J-9 tracegen** (`genJ8A` with `compGenB9` and `mbCounts9`). -/
def genJ9A (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) : Option InJ8 :=
  match runX R fuel s f with
  | none => none
  | some Rn =>
    if !(noJets Rn.rows) then none else
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let roots := rootsOf c Rn.rows
    let cs := cellsOfRoots roots
    let acsL := acsOfD (bigsOf roots Rn.rows) ((incOps Rn.rows).any fun x => x.1 + 1 = P)
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges Rn.rows)
    let pd := HonestPairX.pdX (sxE pt)
    let comp := compGenB9 c H pd Rn χe
    let (ws, kr) := walkGen (cs.headD (.atom 0)) (pathReads Rn.rows)
    let mv := mvCounts cs c
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := mhCounts cs comp.bases ws
    let k := coOf χe
    let α := chalsMJ8E χe 0
    let γ := chalsMJ8E χe 1
    let (cR, cP) := cellGenB k (yE χe) H (bigIdOf acsL) cs mv mx mx1 mh
    let (wR, wP) := walkGenRowsB k (yE χe) α γ H (idxN cs) HonestK8.certB8 cs ws kr
    let reads := pairReads H pd Rn.rows
    let (vs, krV) := if reads.isEmpty then ([], 0) else walkGen padN reads
    let HA := hdl acsL
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    let (aR, aP) := atomGenE pt χe acsL (infoOfE acsL pt Rn.rows) (mbCounts9 acsL cs c) (wCounts rIA acsL vs)
      (wCounts rIA acsL vs)
    let (vR, vP) : Array (Array (ZMod P)) × (ℕ → K3) := if krV = 0 then (#[Array.replicate 166 0], fun _ => 0)
      else walkGenRowsBE pt (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1) HA rIA WalkJ8.certB acsL vs krV
    let m := max comp.rows.size (max cR.size (max wR.size (max aR.size vR.size)))
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cP, pubsW := wP,
               pubsJ := fun _ => 0, pubsA := aP, pubsV := vP }
        χ := χe
        r := budget m
        g := 0
        X := chipOf comp.rows
        C := chipOf cR
        W := chipOf wR
        J := ⟨1, 0, Example.ω6g, fun _ => Fin.elim0⟩
        A := chipOf aR
        V := chipOf vR
        kroots := kr
        krootsV := krV
        lay := Fin.elim0
        Rt := Example.RtG
        regs := []
        ids := []
        idx := fun _ => 0
        rk := fun _ => (0, 0) }

/-- The J-9 demo claim's subject `[(p+5) 0]` and formula `[0 2]` (`*[[(p+5) 0] [0 2]] = p+5`). -/
def demoS : Noun := .cell (.atom (P + 5)) (.atom 0)
def demoF : Noun := .cell (.atom 0) (.atom 2)

end Nock.V1J9.Gen9
