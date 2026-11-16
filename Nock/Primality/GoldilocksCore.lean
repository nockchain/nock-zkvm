/-
  Nock/Primality/GoldilocksCore.lean

  Moved verbatim out of
  `Goldilocks.lean` (same namespace, same names).
-/
import Nock.Primality.Pratt

set_option autoImplicit false

namespace Nock.Primality

def goldilocksCert : List Entry := [
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨257, 3, [(2, 8)]⟩,
  ⟨65537, 3, [(2, 16)]⟩,
  ⟨18446744069414584321, 7, [(2, 32), (3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)]⟩,
  ⟨13, 2, [(2, 2), (3, 1)]⟩,
  ⟨937, 5, [(2, 3), (3, 2), (13, 1)]⟩,
  ⟨7, 3, [(2, 1), (3, 1)]⟩,
  ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
  ⟨53, 2, [(2, 2), (13, 1)]⟩,
  ⟨724723, 2, [(2, 1), (3, 1), (43, 1), (53, 2)]⟩,
  ⟨97, 5, [(2, 5), (3, 1)]⟩,
  ⟨5821, 6, [(2, 2), (3, 1), (5, 1), (97, 1)]⟩,
  ⟨37, 2, [(2, 2), (3, 2)]⟩,
  ⟨14431, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (37, 1)]⟩,
  ⟨1039033, 10, [(2, 3), (3, 2), (14431, 1)]⟩,
  ⟨19, 2, [(2, 1), (3, 2)]⟩,
  ⟨113, 3, [(2, 4), (7, 1)]⟩,
  ⟨227, 2, [(2, 1), (113, 1)]⟩,
  ⟨8627, 2, [(2, 1), (19, 1), (227, 1)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨73, 5, [(2, 3), (3, 2)]⟩,
  ⟨107, 2, [(2, 1), (53, 1)]⟩,
  ⟨29, 2, [(2, 2), (7, 1)]⟩,
  ⟨233, 3, [(2, 3), (29, 1)]⟩,
  ⟨467, 2, [(2, 1), (233, 1)]⟩,
  ⟨3852010273, 5, [(2, 5), (3, 1), (11, 1), (73, 1), (107, 1), (467, 1)]⟩,
  ⟨11365102077808483, 3, [(2, 1), (3, 2), (19, 1), (8627, 1), (3852010273, 1)]⟩,
  ⟨167034643597991036904547663171, 2, [(2, 1), (3, 5), (5, 1), (5821, 1), (1039033, 1), (11365102077808483, 1)]⟩]


theorem goldilocksCert_ok : checkAll goldilocksCert [2] = true := by decide +kernel

theorem cert_prime {n : ℕ} (hn : n ∈ goldilocksCert.map Entry.n) : n.Prime :=
  prime_of_cert goldilocksCert_ok hn

/-- **`2^64 - 2^32 + 1` is prime**, in the kernel, numeral form (no `Nock.Field`). -/
theorem goldilocks_prime_nat : Nat.Prime (2 ^ 64 - 2 ^ 32 + 1) := by
  have h : (18446744069414584321 : ℕ) ∈ goldilocksCert.map Entry.n := by decide +kernel
  have := cert_prime h
  norm_num
  exact this

end Nock.Primality
