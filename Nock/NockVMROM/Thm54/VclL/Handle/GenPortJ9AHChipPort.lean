import Nock.V1J8.CheckJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

/-! No AcceptsJ9A import. -/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort
open Nock Nock.Field Polynomial
open Nock.V1J8.Check
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (powN)

/-- A chip's acceptance predicate, abstracted over row count, nodes, orbit, coins, publics and trace. -/
structure ChipPort (K : Type) (w : ℕ) where
  Ok : ∀ {n : ℕ}, 0 < n → (Fin n → ZMod p) → ∀ {h : ℕ}, StrictOrbitDomain (ZMod p) 3 h →
    (ℕ → K) → (ℕ → K) → (Fin w → (ZMod p)[X]) → Prop

variable {K : Type} {w : ℕ}

/-- Re-indexing along `n = m` with matching nodes (generic `cellOK_reidx`). -/
theorem ChipPort.reidx (S : ChipPort K w) {n m : ℕ} (e : n = m) (hn : 0 < n) (hm : 0 < m)
    (ν : Fin n → ZMod p) (μ : Fin m → ZMod p) (hνμ : ∀ i : Fin n, ν i = μ (Fin.cast e i))
    {h : ℕ} (O : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) (T : Fin w → (ZMod p)[X])
    (H : S.Ok hm μ O chals pubs T) : S.Ok hn ν O chals pubs T := by
  subst e
  obtain rfl : ν = μ := funext hνμ
  exact H

/-- **`chipAt_of_cols_pubs`**: run-level acceptance at every orbit with injective nodes, the exec columns'
interpolants at the exec orbit, and the exec publics give acceptance at the exec chip input `q`. -/
theorem chipAt_of_cols_pubs (S : ChipPort K w) (q : ChipIn) (hoq : OrbOK q) (hnq : 0 < q.n)
    (hinj0 : Function.Injective (nodesOf q))
    {m : ℕ} (hm : 0 < m) (hn : q.n = m) (chals : ℕ → K)
    (pubsR : ∀ {h : ℕ}, StrictOrbitDomain (ZMod p) 3 h → ℕ → K)
    (TrR : ∀ {h : ℕ}, StrictOrbitDomain (ZMod p) 3 h → Fin w → (ZMod p)[X])
    (hrun : ∀ {h : ℕ} (O : StrictOrbitDomain (ZMod p) 3 h), Function.Injective (powN O m) →
      (∀ (i : Fin m) (hi : (i : ℕ) + 1 < m), powN O m ⟨(i : ℕ) + 1, hi⟩ = powN O m i * O.ω) →
      S.Ok hm (powN O m) O chals (pubsR O) (TrR O))
    (pubs : ℕ → K) (hpubs : pubs = pubsR (mkOrbit q hoq))
    (T : Fin w → (ZMod p)[X]) (hcols : T = TrR (mkOrbit q hoq)) :
    S.Ok hnq (nodesOf q) (mkOrbit q hoq) chals pubs T := by
  subst hpubs hcols
  have hnodes : ∀ i : Fin q.n, nodesOf q i = powN (mkOrbit q hoq) m (Fin.cast hn i) :=
    fun i => nodesOf_eq q i
  have hinjN : Function.Injective (powN (mkOrbit q hoq) m) := by
    intro a c hac
    have := hinj0 (a₁ := Fin.cast hn.symm a) (a₂ := Fin.cast hn.symm c)
      (by rw [hnodes, hnodes]; simpa using hac)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  exact S.reidx hn hnq hm _ _ hnodes _ _ _ _
    (hrun _ hinjN (fun i hi => pow_succ _ _))

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort in
#print axioms ChipPort.reidx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipPort in
#print axioms chipAt_of_cols_pubs
