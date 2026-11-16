/-
  Nock/DriverJ8/TranscriptJ8.lean

  **The J-8 Fiat-Shamir transcript, pure.**

  The sponge is the generic driver's Tip5 (`Nock/Driver/Tip5.lean`, verbatim, with its test vectors).  A transcript is a
  chain state `s` (5 limbs); an `absorb label data` event replaces `s` by `H[tAbs] ++ s ++ bytes7 label ++ [|data|] ++
  data`; a `squeeze idx` event reads the coins `idx` from `s` (`coinsOf`, three limbs per coin) and replaces `s`
  by `H[tSqz] ++ s ++ [|idx|] ++ idx`.  Every encoding is length-prefixed.

  **Order (`sched`).**  domain tag, the FULL public record `Pb`, the claim, and only then the round-0 commitment
  and the first squeeze (the coins of `frameJ8` with `sampledAfter = 0`, drawn after round 0), then the round-1
  commitment and the squeeze of the coins with `sampledAfter = 1`, then the round-2 commitment and the prover's
  public messages (nothing is sampled after round 1).  `pub_before_first_squeeze` is the structural receipt.

  ASSUMPTION (named, not proved): `Tip5.hashVarlen` behaves as a random oracle.
-/
import Nock.Driver.Transcript

set_option autoImplicit false

namespace Nock.DriverJ8.TranscriptJ8

open Nock.Driver.Tip5 Nock.Driver.Transcript

def tAbs : Nat := asciiTag "j8/abs"
def tSqz : Nat := asciiTag "j8/sqz"
def tIni : Nat := asciiTag "j8/ini"

/-- The domain tag absorbed first. -/
def domainTag : String := "nockvm/j8/fs/v1"

/-- The coins of `frameJ8` with `sampledAfter = 0` (drawn after the round-0 commitment). -/
def idxS0 : List Nat := [2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
/-- The coins of `frameJ8` with `sampledAfter = 1` (drawn after the round-1 commitment). -/
def idxS1 : List Nat := [0, 1, 4, 5, 6, 7]

inductive Ev where
  | absorb (label : String) (data : List Nat)
  | squeeze (idx : List Nat)

def Ev.isAbsorb : Ev → Bool
  | .absorb _ _ => true
  | .squeeze _ => false

def Ev.isSqueeze (e : Ev) : Bool := !e.isAbsorb

abbrev Cfg := List Nat × List (Nat × Coin)

def initCfg : Cfg := (hashVarlen [tIni], [])

def absorbSt (s : List Nat) (label : String) (data : List Nat) : List Nat :=
  hashVarlen ([tAbs] ++ s ++ bytes7 (bytesOf label) ++ [data.length] ++ data)

def squeezeSt (s : List Nat) (idx : List Nat) : List (Nat × Coin) × List Nat :=
  (coinsOf s idx, hashVarlen ([tSqz] ++ s ++ [idx.length] ++ idx))

def step (c : Cfg) : Ev → Cfg
  | .absorb l d => (absorbSt c.1 l d, c.2)
  | .squeeze idx => let r := squeezeSt c.1 idx; (r.2, c.2 ++ r.1)

def runFrom (c : Cfg) (evs : List Ev) : Cfg := evs.foldl step c

def run (evs : List Ev) : Cfg := runFrom initCfg evs

/-- The header: the domain tag, the public record, the claim (each field one absorb). -/
def hdrEvents (pub claim : List (String × List Nat)) : List Ev :=
  Ev.absorb "domain" (bytes7 (bytesOf domainTag)) ::
    ((pub ++ claim).map fun f => Ev.absorb f.1 f.2)

/-- The whole schedule, `c0 c1 c2` the round commitments and `mm` the prover's public messages. -/
def sched (pub claim : List (String × List Nat)) (c0 c1 c2 mm : List Nat) : List Ev :=
  hdrEvents pub claim ++
    [.absorb "commit/r0" c0, .squeeze idxS0, .absorb "commit/r1" c1, .squeeze idxS1,
     .absorb "commit/r2" c2, .absorb "msg" mm]

/-- Every header event of the transcript (`hdrEvents`) is an absorb event. -/
theorem hdr_absorbs (pub claim : List (String × List Nat)) : ∀ e ∈ hdrEvents pub claim, e.isAbsorb = true := by
  intro e he
  simp only [hdrEvents, List.mem_cons, List.mem_map, List.mem_append] at he
  rcases he with rfl | ⟨f, _, rfl⟩ <;> rfl

/-- **Order receipt.**  The schedule splits at its first squeeze: everything before it is an absorb, and that prefix
begins with the header, i.e. the domain tag, EVERY field of the public record and EVERY claim field. -/
theorem pub_before_first_squeeze (pub claim : List (String × List Nat)) (c0 c1 c2 mm : List Nat) :
    ∃ pre post, sched pub claim c0 c1 c2 mm = pre ++ Ev.squeeze idxS0 :: post ∧
      (∀ e ∈ pre, e.isAbsorb = true) ∧ hdrEvents pub claim <+: pre ∧
      (∀ f ∈ pub ++ claim, Ev.absorb f.1 f.2 ∈ pre) := by
  refine ⟨hdrEvents pub claim ++ [.absorb "commit/r0" c0],
    [.absorb "commit/r1" c1, .squeeze idxS1, .absorb "commit/r2" c2, .absorb "msg" mm], by simp [sched], ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with h | h
    · exact hdr_absorbs pub claim e h
    · simp at h; subst h; rfl
  · exact List.prefix_append _ _
  · intro f hf
    refine List.mem_append_left _ ?_
    simp only [hdrEvents, List.mem_cons, List.mem_map]
    exact Or.inr ⟨f, hf, rfl⟩

/-- Exactly two squeezes, in the order `S0` then `S1`, each preceded by its round's commitment. -/
theorem squeezes_of_sched (pub claim : List (String × List Nat)) (c0 c1 c2 mm : List Nat) :
    ((sched pub claim c0 c1 c2 mm).filter Ev.isSqueeze).length = 2 := by
  have h : ∀ e ∈ hdrEvents pub claim, e.isSqueeze = false := by
    intro e he; simp [Ev.isSqueeze, hdr_absorbs pub claim e he]
  simp only [sched, List.filter_append]
  rw [List.filter_eq_nil_iff.mpr (fun e he => by simp [h e he])]
  simp [Ev.isSqueeze, Ev.isAbsorb]

end Nock.DriverJ8.TranscriptJ8
