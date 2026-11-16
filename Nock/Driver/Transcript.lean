/-
  Nock/Driver/Transcript.lean

  **The commitment hash, the Fiat-Shamir transcript and the
  coin derivation.**  Pure (no IO); `Nock/Driver/Driver.lean` streams files through the same step
  functions.

  ## What is hashed (all through `Tip5.hashVarlen`, limbs `< p`)

  * **bytes -> limbs** (`bytes7`): `[len] ++ groups`, each group of 7 little-endian bytes read as a
    number `< 2^56 < p`.  Used for names, the canonical `header.json` and the claim.
  * **chain hash of a limb stream** (`chainDigest tag chunks`): `d := H[tInit, tag]`; per chunk `c`
    `d := H[tChunk] ++ d ++ [|c|] ++ c`; finally `H[tFin] ++ d ++ [#chunks, total]`.  Chunks are
    `chunkLimbs = 1024` limbs (the file reader produces exactly these); the first chunk of a file is
    its NAME (`bytes7`).  The chain is a length-prefixed Merkle-Damgard over the Tip5 sponge, so it
    streams in constant memory.

  ## The coins (`frameVSQ`, `FrameVSQ.lean`)

  `Coins frameVSQ K` has 17 coordinates, each an element of `𝕂` (3 Goldilocks limbs).  A column of
  round `r` is a function of the coins with `sampledAfter < r` (`StagedCols`), so:

  * **round-1 coins** (`sampledAfter = 0`, drawn after the round-0 commitment, read by the round-1
    columns): `2 3 8 9 10 11 12 13 14 15 16` = `z₁ z₂ a b c γH ρH αW γW Im γH Im ρH`;
  * **round-2 coins** (`sampledAfter = 1`, drawn after the round-1 columns are committed, read by the
    round-2 columns): `0 1 4 5 6 7` = `αC γ IOγ₀ IOρ₀ IOγ₁ IOρ₁`.

  (`CoinFrame.lean` proves the two index lists are exactly the `sampledAfter = 0 / 1` fibres.)
  `𝕂′` coins are pairs of `𝕂` coins: `γH′ = (11, 15)`, `ρH′ = (12, 16)`, `IOγ′ = (4, 6)`,
  `IOρ′ = (5, 7)`, i.e. 6 limbs each.

  Derivation (Fiat-Shamir):
  * `squeeze seed n` = the first `n` limbs of `H[tSq] ++ seed ++ [k]` for `k = 0, 1,..` (5 limbs each);
  * coin `idx_j` (the `j`-th index of the round's list, ascending) = limbs `3j, 3j+1, 3j+2`.

  ## Assumptions (NAMED, not proved)

  * `Tip5.hashVarlen` behaves as a random oracle (`RO`).  Under `RO`, with `seed1 / seed2` hashes of
    the committed data, the coins are uniform and independent of anything the prover fixed before
    committing: the standard Fiat-Shamir transform of the 2-round (3-message) interaction.  Round
    ORDER is what the soundness statement needs (`StagedVSQ`); the driver implements it.
-/
import Nock.Driver.Tip5

set_option autoImplicit false

namespace Nock.Driver.Transcript

open Nock.Driver.Tip5

/-! ## Encodings -/

/-- ASCII tag (at most 7 bytes) as a number `< 2^56`. -/
def asciiTag (s : String) : Nat := s.toUTF8.toList.foldl (fun a b => a * 256 + b.toNat) 0

def tInit : Nat := asciiTag "drv/ini"
def tChunk : Nat := asciiTag "drv/chk"
def tFin : Nat := asciiTag "drv/fin"
def tFile : Nat := asciiTag "drv/fil"
def tRound : Nat := asciiTag "drv/rnd"
def tClaim : Nat := asciiTag "drv/clm"
def tC1 : Nat := asciiTag "drv/cn1"
def tC2 : Nat := asciiTag "drv/cn2"
def tSq : Nat := asciiTag "drv/sqz"

/-- The UTF-8 bytes of a string as numbers. -/
def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- Chunking helper (structural on fuel). -/
def chunkAux {α : Type} (n : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | f + 1, l => if l.isEmpty then [] else l.take n :: chunkAux n f (l.drop n)

def chunks {α : Type} (n : Nat) (l : List α) : List (List α) := chunkAux n (l.length + 1) l

/-- 7 little-endian bytes as a number. -/
def le7 (g : List Nat) : Nat := g.foldr (fun x acc => x + 256 * acc) 0

/-- **bytes -> limbs**: the length, then the 7-byte groups (each `< 2^56 < p`). -/
def bytes7 (b : List Nat) : List Nat := b.length :: (chunks 7 b).map le7

/-- The chunk size of the chain hash, in limbs. -/
def chunkLimbs : Nat := 1024

/-! ## The chain hash -/

def chainInit (t : Nat) : List Nat := hashVarlen [tInit, t]
def chainStep (d c : List Nat) : List Nat := hashVarlen ([tChunk] ++ d ++ [c.length] ++ c)
def chainFin (d : List Nat) (nch total : Nat) : List Nat := hashVarlen ([tFin] ++ d ++ [nch, total])

/-- The chain digest of a list of chunks. -/
def chainDigest (t : Nat) (cs : List (List Nat)) : List Nat :=
  chainFin (cs.foldl chainStep (chainInit t)) cs.length (cs.map List.length).sum

/-- **File digest**: the chain over `[bytes7 name] ++ chunks of the limbs`. -/
def fileDigest (name : String) (limbs : List Nat) : List Nat :=
  chainDigest tFile (bytes7 (bytesOf name) :: chunks chunkLimbs limbs)

/-- **Round digest** over the files' digests (each 5 limbs), in layout order. -/
def roundDigest (r : Nat) (fds : List (List Nat)) : List Nat :=
  hashVarlen ([tRound, r, fds.length] ++ fds.flatten)

/-- **Claim digest** of the canonical claim bytes. -/
def claimDigest (claimBytes : List Nat) : List Nat := hashVarlen (tClaim :: bytes7 claimBytes)

/-! ## The coins -/

/-- Round-1 coin indices (`frameVSQ.sampledAfter = 0`), ascending. -/
def coinIdxRound1 : List Nat := [2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16]
/-- Round-2 coin indices (`frameVSQ.sampledAfter = 1`), ascending. -/
def coinIdxRound2 : List Nat := [0, 1, 4, 5, 6, 7]

/-- The first limbs of the squeeze of a seed. -/
def squeeze (seed : List Nat) (n : Nat) : List Nat :=
  ((List.range ((n + 4) / 5)).flatMap fun k => hashVarlen ([tSq] ++ seed ++ [k])).take n

def seed1 (d0 claimD : List Nat) : List Nat := hashVarlen ([tC1] ++ d0 ++ claimD)
def seed2 (s1 d1 : List Nat) : List Nat := hashVarlen ([tC2] ++ s1 ++ d1)

/-- A `𝕂` coin: three limbs. -/
abbrev Coin := List Nat

/-- The coins of one round from a seed: `(index, 3 limbs)` for each index, in list order. -/
def coinsOf (seed : List Nat) (idx : List Nat) : List (Nat × Coin) :=
  let l := squeeze seed (3 * idx.length)
  (List.range idx.length).map fun j => (idx.getD j 0, (l.drop (3 * j)).take 3)

/-- The round-1 coins, drawn from the seed of the first digest and the claim digest. -/
def coins1 (d0 claimD : List Nat) : List (Nat × Coin) := coinsOf (seed1 d0 claimD) coinIdxRound1

/-- The round-2 coins, drawn from the round-2 seed (which absorbs the second round digest). -/
def coins2 (d0 claimD d1 : List Nat) : List (Nat × Coin) :=
  coinsOf (seed2 (seed1 d0 claimD) d1) coinIdxRound2

/-- All 17 coins, by index (`none` if the two lists do not cover `0..16` exactly once). -/
def assemble (c1 c2 : List (Nat × Coin)) : Option (List Coin) :=
  let all := c1 ++ c2
  if (all.map Prod.fst).Nodup ∧ all.length = 17 ∧ ∀ i ∈ all.map Prod.fst, i < 17 then
    some ((List.range 17).map fun i => ((all.find? fun p => p.1 = i).map Prod.snd).getD [])
  else none

/-! ## Basic facts -/

theorem digestOf_based (s : List Nat) : Based (digestOf s) := by
  intro x hx
  unfold digestOf at hx
  simp only [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact Nat.mod_lt _ (by decide)

theorem hashVarlen_based (inp : List Nat) : Based (hashVarlen inp) := digestOf_based _

theorem hash10_based (inp : List Nat) : Based (hash10 inp) := digestOf_based _

theorem round_lists_partition : coinIdxRound1.length + coinIdxRound2.length = 17 ∧
    (coinIdxRound1 ++ coinIdxRound2).Nodup ∧ ∀ i ∈ coinIdxRound1 ++ coinIdxRound2, i < 17 := by
  decide

end Nock.Driver.Transcript
