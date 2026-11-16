/-
  NockvmE2E/Exec/Dag.lean   (executed, Mathlib-free)

  `evalDag`: the emitted `j8_<chip>.json` constraint DAG (parsed by `Tr.loadChip`/`Tr.parseEx`, re-used from Trace.lean) evaluated over
  `VF.K3` (the verifier's field, not the prover's `PF.E3`).  Semantics as `Tr.ev`: `ext_var` reads columns `bc + 3e + t` as `Σ_t v_t x^t`;
  `public_val i` is the flat public slot `i` (base); `ext_chal i` is coin/derived slot `i`.
-/
import NockvmE2E.Exec.VField
import NockvmE2E.Exec.Trace
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.Tr

structure DEnv where
  cur : Array K3
  next : Array K3
  pub : Array G
  chal : Array K3
  bc : Nat

@[inline] def extV (a : Array K3) (bc e : Nat) : K3 :=
  K3.add (K3.add a[bc + 3 * e]! (K3.mul a[bc + 3 * e + 1]! K3.gen)) (K3.mul a[bc + 3 * e + 2]! (K3.mul K3.gen K3.gen))

def evK (env : DEnv) (memo : Array K3) : Ex → K3
  | .var 0 i => env.cur[i]!
  | .var 1 i => env.next[i]!
  | .var _ i => K3.ofG env.pub[i]!
  | .cF v => K3.ofG v
  | .add a b => K3.add (evK env memo a) (evK env memo b)
  | .sub a b => K3.sub (evK env memo a) (evK env memo b)
  | .mul a b => K3.mul (evK env memo a) (evK env memo b)
  | .neg a => K3.neg (evK env memo a)
  | .pow a n => K3.pow (evK env memo a) n
  | .extVar 0 e => extV env.cur env.bc e
  | .extVar 1 e => extV env.next env.bc e
  | .extVar _ e => ⟨env.pub[3 * e]!, env.pub[3 * e + 1]!, env.pub[3 * e + 2]!⟩
  | .chal i => env.chal[i]!
  | .ref i => memo[i]!

/-- All constraint values of the chip DAG (one `K3` per constraint, in document order). -/
def evalDag (ch : Chip) (env : DEnv) : Array K3 :=
  let memo := ch.shared.toList.foldl (fun (memo : Array K3) s => memo.push (evK env memo s)) (Array.mkEmpty ch.shared.size)
  ch.cons.map fun c => evK env memo c.e

end NockvmE2E.Exec.V
