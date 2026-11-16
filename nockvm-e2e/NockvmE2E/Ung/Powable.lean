/-
the `PowablePcs` extension of the PCS base class.

`PowablePcs Φ F B` extends the real `PcsBase Φ F B` (`Succ/PcsBase.lean`). The base has only the
compiler-form soundness data (`Params`, `Adv`, `bad`, `ε`, `sound`), so `PowablePcs` adds, indexed by the DeepRap bundle
`D` and `pp : Params D`: the commitment alphabet `Dg`, the path type and `accept : Bool`, the log-reading extractor
`ext`, the projections of an accepted path (`coms`, `claims`, `pf`), the two uniqueness slots
(`Collide`/`unique_com`, `CollidePf`/`unique_pf`, the shape of `UniqueCommitment`, `Succ/Commitment.lean:99`, as
events on paths; no `εuniq` field), and a deterministic canonical proof per (block, nonce).

RESULTS. `PowablePcs` (class); `iopPowable` (non-vacuity: over `iopPcs`, the `iopUnique` shape, `Collide = CollidePf = False`);
`friMerklePcs_not_powable` (a `PowablePcs` over `friMerklePcs` whose commitments project onto a word commitment has a
non-trivial `Collide` pair; from `no_unique_of_wordCommit`). The projection `ProjectsOnto` is a HYPOTHESIS: `FriParams`
has no `CommitScheme` and the `Path` of an arbitrary `PowablePcs` is abstract, so it cannot be constructed here (this is
the standalone-model gap).

ncc plan-A slots (to be filled from ncc):
  1. `proj`: what the PoW digest hashes (options (a), (b), (c)).
  2. `Nonce`, the target `T`, the digest hash, and the binding `GlobalSalt := Nonce`.
  3. The PCS instance (a lattice PCS, WARP `V_full`, or another) and its `unique_com` canonicity argument.
  4. `AirDet` for the PoW AIR (per-column survey, UNG-2).
  5. `εuniq` and how it is priced (`HUniq` hypothesis, `Ung/Defs.lean:122`).
  6. Whether `canon` must be a function (unique honest proof) or unique up to `CollidePf`.
-/
import NockvmE2E.Ung.Defs
import NockvmE2E.Ung.MerkleCompose
import NockvmE2E.Succ.PcsIop
import NockvmE2E.Succ.PcsFri

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NNReal ENNReal

namespace NockvmE2E.Ung

open NockvmE2E.Succ NockvmE2E.Succ.Pcs NockvmE2E.Deep NockvmE2E.Rap

section Powable

variable (Φ : CoinFrame) (F B : Type) [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- **`PowablePcs`**: a `PcsBase` whose commitments are canonical (extracted data determines the commitments, except on
a `Collide` event) and whose accepted proofs of the same commitments and claims are unique (except on `CollidePf`),
with a deterministic canonical prover per (block, nonce). -/
class PowablePcs extends PcsBase Φ F B where
  /-- commitment alphabet (Merkle digest; lattice commitment) -/
  Dg : DeepRap Φ F B → Type
  /-- column index type of a commitment tuple -/
  Idx : DeepRap Φ F B → Type
  /-- a path of the compiled experiment -/
  Path : (D : DeepRap Φ F B) → Params D → Type
  Cl : (D : DeepRap Φ F B) → Params D → Type
  Pf : (D : DeepRap Φ F B) → Params D → Type
  Log : (D : DeepRap Φ F B) → Params D → Type
  ExtD : (D : DeepRap Φ F B) → Params D → Type
  accept : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Bool
  ext : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Log D pp → ExtD D pp
  coms : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Idx D → Dg D
  claims : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Cl D pp
  pf : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Pf D pp
  Collide : (D : DeepRap Φ F B) → Dg D → Dg D → Prop
  unique_com : ∀ D pp (p p' : Path D pp) (l l' : Log D pp), ext D pp p l = ext D pp p' l' →
    coms D pp p = coms D pp p' ∨ ∃ j, Collide D (coms D pp p j) (coms D pp p' j)
  CollidePf : (D : DeepRap Φ F B) → (pp : Params D) → Path D pp → Path D pp → Prop
  unique_pf : ∀ D pp (p p' : Path D pp), accept D pp p = true → accept D pp p' = true →
    coms D pp p = coms D pp p' → claims D pp p = claims D pp p' → pf D pp p = pf D pp p' ∨ CollidePf D pp p p'
  Block : Type
  Nonce : Type
  Statement : Type
  Witness : Type
  Rel : Statement → Witness → Prop
  stmt : Block → Nonce → Statement
  /-- the deterministic honest prover (no salt) -/
  canon : (D : DeepRap Φ F B) → (pp : Params D) → Block → Nonce → Witness → Path D pp
  canon_accepts : ∀ D pp blk nonce w, Rel (stmt blk nonce) w → accept D pp (canon D pp blk nonce w) = true

/-! ### Toy instance (non-vacuity): over `iopPcs` -/

open Classical in
/-- `iopPcs` as a powable PCS: commitments are the column words (`deepCS`), a path is `(commitments, claims)`,
accepted iff the claims hold of the data. `Collide = CollidePf = False` (the `iopUnique` shape). -/
noncomputable def iopPowable : PowablePcs Φ F B where
  toPcsBase := iopPcs
  Dg D := Fin (2 ^ D.n) → B
  Idx _ := Unit
  Path D _ := (Unit → (Fin (2 ^ D.n) → B)) × Claims (deepOI D.P) Unit × Unit
  Cl D _ := Claims (deepOI D.P) Unit
  Pf _ _ := Unit
  Log _ _ := Unit
  ExtD D _ := Fin (2 ^ D.n) → B
  accept D _ p := decide (SatClaims (deepOI D.P) p.1 p.2.1)
  ext _ _ p _ := p.1 ()
  coms _ _ p := p.1
  claims _ _ p := p.2.1
  pf _ _ p := p.2.2
  Collide _ _ _ := False
  unique_com _ _ _ _ _ _ h := Or.inl (funext fun u => by cases u; exact h)
  CollidePf _ _ _ _ := False
  unique_pf _ _ p p' _ _ _ _ := Or.inl (Unit.ext (x := p.2.2) (y := p'.2.2))
  Block := Unit
  Nonce := Unit
  Statement := Unit
  Witness := Unit
  Rel _ _ := True
  stmt _ _ := ()
  canon D _ _ _ _ := (fun _ => 0, [], ())
  canon_accepts D _ _ _ _ _ := by simp [SatClaims]

/-- The toy instance has empty `Collide`, as it must (identity commitment). -/
theorem iopPowable_collide_empty (D : DeepRap Φ F B) (a b : Fin (2 ^ D.n) → B) :
    ¬ (iopPowable Φ F B).Collide D a b := fun h => h

/-- The toy instance is over `iopPcs`. -/
theorem iopPowable_base : (iopPowable Φ F B).toPcsBase = (iopPcs (Φ := Φ) (F := F) (B := B)) := rfl

end Powable

/-! ### Negative: word-commitment (FRI+Merkle) PCSs are not powable with negligible `Collide` -/

section Negative

variable {Φ : CoinFrame} {F B : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- A `PowablePcs` *projects onto* a word commitment `CS` at `(D, pp)`: every `CS`-commitment `c` is the (every-column)
commitment of a path `pth c` extracting `CS.ext c`, and `dg` is injective. This is the standalone-model level of UNG-B
(`Ung/MerkleCompose.lean`); it is a hypothesis, not constructed (see the file header). -/
structure ProjectsOnto (P : PowablePcs Φ F B) (D : DeepRap Φ F B) (pp : P.Params D) {β : Type}
    {O : OracleInterface β} (CS : CommitScheme β O) where
  i0 : P.Idx D
  dg : CS.Com → P.Dg D
  dg_inj : Function.Injective dg
  pth : CS.Com → P.Path D pp
  lg : CS.Com → P.Log D pp
  ext_eq : ∀ c c', CS.ext c = CS.ext c' → P.ext D pp (pth c) (lg c) = P.ext D pp (pth c') (lg c')
  coms_pth : ∀ c j, P.coms D pp (pth c) j = dg c

/-- The projection turns a `PowablePcs` into a `UniqueCommitment` on `CS` (`Collide` pulled back along `dg`). -/
def ProjectsOnto.toUnique {P : PowablePcs Φ F B} {D : DeepRap Φ F B} {pp : P.Params D} {β : Type}
    {O : OracleInterface β} {CS : CommitScheme β O} (h : ProjectsOnto P D pp CS) :
    UniqueCommitment β O (CS := CS) where
  Collide c c' := P.Collide D (h.dg c) (h.dg c')
  unique_com c c' e := by
    rcases P.unique_com D pp _ _ _ _ (h.ext_eq c c' e) with hc | ⟨j, hj⟩
    · left
      have := congrFun hc h.i0
      rw [h.coms_pth, h.coms_pth] at this
      exact h.dg_inj this
    · right
      rwa [h.coms_pth, h.coms_pth] at hj
  CollidePf _ _ _ _ := True
  unique_pf _ _ _ _ _ _ := Or.inr trivial

/-- **`friMerklePcs_not_powable`**: a `PowablePcs` whose base is `friMerklePcs` and whose commitments project onto a word
commitment (collision-free roots of a codeword, one-symbol-correcting decoder: the hypotheses of
`no_unique_of_wordCommit`, discharged for `merkleCS` by `merkle_no_unique`) has a non-empty `Collide`: two distinct
commitments are declared colliding. With `merkle_ungrind_negative` (`merkle_compose`) the pair is realised by an
accepted proof with probability `≥ 1 − l/2^n`, so `εuniq ≥ 1 − l/N`. `hbase` records which base this is about; the
argument uses only `proj`. -/
theorem friMerklePcs_not_powable (P : PowablePcs Φ F B) (hbase : P.toPcsBase = (friMerklePcs (Φ := Φ) (F := F) (B := B)))
    (D : DeepRap Φ F B) (pp : P.Params D) {α β : Type} {O : OracleInterface β}
    {CS : CommitScheme β O} (proj : ProjectsOnto P D pp CS)
    {n : ℕ} (enc : β → ℕ → α) (dec : (ℕ → α) → β) (rt : (ℕ → α) → CS.Com)
    (hcommit : ∀ b, CS.commit b = rt (enc b))
    (hrt : ∀ w w', rt w = rt w' → ∀ i, i < 2 ^ n → w i = w' i)
    (hext : ∀ w, CS.ext (rt w) = dec w)
    (hdec : ∀ b j a, dec (Function.update (enc b) j a) = b)
    (b : β) {j : ℕ} (hj : j < 2 ^ n) {a : α} (ha : a ≠ enc b j) :
    ∃ d d' : P.Dg D, d ≠ d' ∧ P.Collide D d d' := by
  let _ := proj.toUnique
  obtain ⟨hne, hc⟩ := no_unique_of_wordCommit CS enc dec rt hcommit hrt hext hdec b hj ha
  exact ⟨proj.dg (CS.commit b), proj.dg _, fun e => hne (proj.dg_inj e).symm, hc⟩

end Negative

end NockvmE2E.Ung

#print axioms NockvmE2E.Ung.iopPowable
#print axioms NockvmE2E.Ung.iopPowable_collide_empty
#print axioms NockvmE2E.Ung.iopPowable_base
#print axioms NockvmE2E.Ung.friMerklePcs_not_powable
