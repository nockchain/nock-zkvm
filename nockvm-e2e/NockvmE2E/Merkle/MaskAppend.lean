/-
Merkle (B) e2e row 1: appending masks.

A combined mask `a ++ b` (e.g. the RAP mask followed by the batched-FRI mask) has base rounds, paired
rounds, skeletons and merkle counts that split along the append. Paths and openings are split NATIVELY,
by recursion on the first mask (no casts: `(x :: a) ++ b` reduces to `x :: (a ++ b)`), and the split
commutes with `forgetPath`, `pathRootsK` and `Agrees`. The only cast statement is the comparison with
`Succ.App.fstPath/sndPath` along `pairedRoundsK_append` (resp. `baseRounds_append`).
-/
import NockvmE2E.Merkle.FriGlue
import NockvmE2E.Succ.Append

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open BinaryTree InductiveMerkleTree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.MA

open NockvmE2E.Merkle NockvmE2E.Merkle.Fri

/-! ## 1. Round-list equalities -/

section Rounds
variable (Dg : Type) [Finite Dg] [DecidableEq Dg]

theorem baseRounds_append : (a b : MRounds Dg) →
    baseRounds Dg (a ++ b) = baseRounds Dg a ++ baseRounds Dg b
  | [], _ => rfl
  | ⟨_, _⟩ :: a, b => congrArg (_ :: ·) (baseRounds_append a b)

theorem pairedRoundsK_append : (a b : MRounds Dg) →
    pairedRoundsK Dg (a ++ b) = pairedRoundsK Dg a ++ pairedRoundsK Dg b
  | [], _ => rfl
  | ⟨_, .clear⟩ :: a, b => congrArg (_ :: ·) (pairedRoundsK_append a b)
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b => congrArg (_ :: ·) (pairedRoundsK_append a b)

theorem merkleSkels_append : (a b : MRounds Dg) →
    merkleSkels (a ++ b) = merkleSkels a ++ merkleSkels b
  | [], _ => rfl
  | ⟨_, .clear⟩ :: a, b => merkleSkels_append a b
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b => congrArg (_ :: ·) (merkleSkels_append a b)

theorem merkleCount_append : (a b : MRounds Dg) →
    merkleCount Dg (a ++ b) = merkleCount Dg a + merkleCount Dg b
  | [], _ => by simp [merkleCount]
  | ⟨_, .clear⟩ :: a, b => by simp [merkleCount, merkleCount_append a b]
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b => by simp [merkleCount, merkleCount_append a b]; omega

end Rounds

/-! ## 2. Native splits of paths and openings -/

section Split
variable (Dg : Type) [Finite Dg] [DecidableEq Dg]

/-- The prefix of a base path of `a ++ b`. -/
def fstB : (a b : MRounds Dg) → (protocol (baseRounds Dg (a ++ b))).tree.ExecutionPath →
    (protocol (baseRounds Dg a)).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | ⟨_, _⟩ :: a, b, p => ⟨p.1, p.2.1, fstB a b p.2.2⟩

/-- The suffix of a base path of `a ++ b`. -/
def sndB : (a b : MRounds Dg) → (protocol (baseRounds Dg (a ++ b))).tree.ExecutionPath →
    (protocol (baseRounds Dg b)).tree.ExecutionPath
  | [], _, p => p
  | ⟨_, _⟩ :: a, b, p => sndB a b p.2.2

/-- The prefix of a paired path of `a ++ b`. -/
def fstP : (a b : MRounds Dg) → (protocol (pairedRoundsK Dg (a ++ b))).tree.ExecutionPath →
    (protocol (pairedRoundsK Dg a)).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: a, b, p => ⟨p.1, p.2.1, fstP a b p.2.2⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => ⟨p.1, p.2.1, fstP a b p.2.2⟩

/-- The suffix of a paired path of `a ++ b`. -/
def sndP : (a b : MRounds Dg) → (protocol (pairedRoundsK Dg (a ++ b))).tree.ExecutionPath →
    (protocol (pairedRoundsK Dg b)).tree.ExecutionPath
  | [], _, p => p
  | ⟨_, .clear⟩ :: a, b, p => sndP a b p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => sndP a b p.2.2

/-- The prefix of the compiled rounds of a mask: everything except the final opening round. -/
def preRoundsK : MRounds Dg → List Round
  | [] => []
  | ⟨r, .clear⟩ :: ms => r :: preRoundsK ms
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms => rootRound Dg r :: preRoundsK ms

variable (Op : Type) [Finite Op] [DecidableEq Op]

/-- The prefix of a compiled path of `a ++ b`. -/
def fstK : (a b : MRounds Dg) → (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath →
    (protocol (preRoundsK Dg a)).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: a, b, p => ⟨p.1, p.2.1, fstK a b p.2.2⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => ⟨p.1, p.2.1, fstK a b p.2.2⟩

/-- The suffix (including the opening round) of a compiled path of `a ++ b`. -/
def sndK : (a b : MRounds Dg) → (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath →
    (protocol (compiledRoundsK Dg Op b)).tree.ExecutionPath
  | [], _, p => p
  | ⟨_, .clear⟩ :: a, b, p => sndK a b p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => sndK a b p.2.2

/-- The roots (merkle rounds only) of a compiled prefix path. -/
def preRoots : (a : MRounds Dg) → (protocol (preRoundsK Dg a)).tree.ExecutionPath → List Dg
  | [], _ => []
  | ⟨_, .clear⟩ :: a, p => preRoots a p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, p => p.1 :: preRoots a p.2.2

/-- The roots and terminal opening of a compiled path of `a ++ b`, from the split path. -/
theorem pathRootsK_append : (a b : MRounds Dg) →
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) →
    pathRootsK Dg Op (a ++ b) p =
      (preRoots Dg a (fstK Dg Op a b p) ++ (pathRootsK Dg Op b (sndK Dg Op a b p)).1,
        (pathRootsK Dg Op b (sndK Dg Op a b p)).2)
  | [], _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, p => pathRootsK_append a b p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => by
      have ih := pathRootsK_append a b p.2.2
      show (p.1 :: (pathRootsK Dg Op (a ++ b) p.2.2).1, (pathRootsK Dg Op (a ++ b) p.2.2).2) = _
      rw [ih]
      rfl

theorem pathRootsK_append_fst (a b : MRounds Dg)
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) :
    (pathRootsK Dg Op (a ++ b) p).1 =
      preRoots Dg a (fstK Dg Op a b p) ++ (pathRootsK Dg Op b (sndK Dg Op a b p)).1 :=
  by rw [pathRootsK_append Dg Op a b p]

theorem pathRootsK_append_snd (a b : MRounds Dg)
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) :
    (pathRootsK Dg Op (a ++ b) p).2 = (pathRootsK Dg Op b (sndK Dg Op a b p)).2 :=
  by rw [pathRootsK_append Dg Op a b p]

end Split

/-! ## 3. Splitting the openings -/

section Open
variable {Dg : Type}

/-- The openings of the first mask. -/
def fstOpen : (a b : MRounds Dg) → OpenAll Dg (merkleSkels (a ++ b)) → OpenAll Dg (merkleSkels a)
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: a, b, os => fstOpen a b os
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os) => (o, fstOpen a b os)

/-- The openings of the second mask. -/
def sndOpen : (a b : MRounds Dg) → OpenAll Dg (merkleSkels (a ++ b)) → OpenAll Dg (merkleSkels b)
  | [], _, os => os
  | ⟨_, .clear⟩ :: a, b, os => sndOpen a b os
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (_, os) => sndOpen a b os

/-- Joining the openings of two masks. -/
def joinOpen : (a b : MRounds Dg) → OpenAll Dg (merkleSkels a) → OpenAll Dg (merkleSkels b) →
    OpenAll Dg (merkleSkels (a ++ b))
  | [], _, _, os2 => os2
  | ⟨_, .clear⟩ :: a, b, os1, os2 => joinOpen a b os1 os2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os1), os2 => (o, joinOpen a b os1 os2)

theorem fstOpen_join : (a b : MRounds Dg) → (os1 : OpenAll Dg (merkleSkels a)) →
    (os2 : OpenAll Dg (merkleSkels b)) → fstOpen a b (joinOpen a b os1 os2) = os1
  | [], _, _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, os1, os2 => fstOpen_join a b os1 os2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os1), os2 => by
      show (o, fstOpen a b (joinOpen a b os1 os2)) = (o, os1)
      rw [fstOpen_join a b os1 os2]

theorem sndOpen_join : (a b : MRounds Dg) → (os1 : OpenAll Dg (merkleSkels a)) →
    (os2 : OpenAll Dg (merkleSkels b)) → sndOpen a b (joinOpen a b os1 os2) = os2
  | [], _, _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, os1, os2 => sndOpen_join a b os1 os2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os1), os2 => sndOpen_join a b os1 os2

theorem join_fst_snd : (a b : MRounds Dg) → (os : OpenAll Dg (merkleSkels (a ++ b))) →
    joinOpen a b (fstOpen a b os) (sndOpen a b os) = os
  | [], _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, os => join_fst_snd a b os
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os) => by
      show (o, joinOpen a b (fstOpen a b os) (sndOpen a b os)) = (o, os)
      rw [join_fst_snd a b os]

end Open

/-! ## 4. `Agrees` along the append -/

section AgreesSec
variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]

/-- `Agrees` for a compiled prefix path (no opening round). -/
def AgreesPre : (a : MRounds Dg) → OpenAll Dg (merkleSkels a) →
    (protocol (preRoundsK Dg a)).tree.ExecutionPath →
    (protocol (baseRounds Dg a)).tree.ExecutionPath → Prop
  | [], _, _, _ => True
  | ⟨_, .clear⟩ :: ms, os, p, q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ AgreesPre ms os p.2.2 q.2.2
  | ⟨_, .merkle _ _ ne enc words⟩ :: ms, (o, os), p, q =>
      p.2.1 = q.2.1 ∧
        o.values.map (codecDec ne enc) = selectedValues (words q.1) o.selector ∧
        AgreesPre ms os p.2.2 q.2.2

theorem Agrees_append : (a b : MRounds Dg) → (os : OpenAll Dg (merkleSkels (a ++ b))) →
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) →
    (q : (protocol (baseRounds Dg (a ++ b))).tree.ExecutionPath) →
    (Agrees (a ++ b) os p q ↔
      AgreesPre a (fstOpen a b os) (fstK Dg Op a b p) (fstB Dg a b q) ∧
        Agrees b (sndOpen a b os) (sndK Dg Op a b p) (sndB Dg a b q))
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | ⟨_, .clear⟩ :: a, b, os, p, q => by
      have ih := Agrees_append a b os p.2.2 q.2.2
      show (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ Agrees (a ++ b) os p.2.2 q.2.2) ↔
        ((p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ AgreesPre a (fstOpen a b os) (fstK Dg Op a b p.2.2) (fstB Dg a b q.2.2)) ∧
          Agrees b (sndOpen a b os) (sndK Dg Op a b p.2.2) (sndB Dg a b q.2.2))
      rw [ih]
      tauto
  | ⟨_, .merkle _ _ ne enc words⟩ :: a, b, (o, os), p, q => by
      have ih := Agrees_append a b os p.2.2 q.2.2
      show (p.2.1 = q.2.1 ∧ o.values.map (codecDec ne enc) = selectedValues (words q.1) o.selector ∧
          Agrees (a ++ b) os p.2.2 q.2.2) ↔
        ((p.2.1 = q.2.1 ∧ o.values.map (codecDec ne enc) = selectedValues (words q.1) o.selector ∧
            AgreesPre a (fstOpen a b os) (fstK Dg Op a b p.2.2) (fstB Dg a b q.2.2)) ∧
          Agrees b (sndOpen a b os) (sndK Dg Op a b p.2.2) (sndB Dg a b q.2.2))
      rw [ih]
      tauto

end AgreesSec

/-! ## 5. `forgetPath` along the append -/

section Forget
variable (Dg : Type) [Finite Dg] [DecidableEq Dg]

theorem fstB_forgetPath : (a b : MRounds Dg) →
    (p : (protocol (pairedRoundsK Dg (a ++ b))).tree.ExecutionPath) →
    fstB Dg a b (forgetPath Dg (a ++ b) p) = forgetPath Dg a (fstP Dg a b p)
  | [], _, _ => rfl
  | ⟨r, .clear⟩ :: a, b, p =>
      congrArg (fun t => (⟨p.1, p.2.1, t⟩ : (protocol (baseRounds Dg (⟨r, .clear⟩ :: a))).tree.ExecutionPath))
        (fstB_forgetPath a b p.2.2)
  | ⟨r, .merkle sk F' ne' enc' w'⟩ :: a, b, p =>
      congrArg (fun t => (⟨p.1.1, p.2.1, t⟩ :
        (protocol (baseRounds Dg (⟨r, .merkle sk F' ne' enc' w'⟩ :: a))).tree.ExecutionPath))
        (fstB_forgetPath a b p.2.2)

theorem sndB_forgetPath : (a b : MRounds Dg) →
    (p : (protocol (pairedRoundsK Dg (a ++ b))).tree.ExecutionPath) →
    sndB Dg a b (forgetPath Dg (a ++ b) p) = forgetPath Dg b (sndP Dg a b p)
  | [], _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, p => sndB_forgetPath a b p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, p => sndB_forgetPath a b p.2.2

end Forget

/-! ## 6. Comparison with `Succ.App.fstPath` / `sndPath` along the round equalities -/

section Cast
variable (Dg : Type) [Finite Dg] [DecidableEq Dg]

open NockvmE2E.Succ.App

theorem castPath_paired_append : (a b : MRounds Dg) →
    (p : (protocol (pairedRoundsK Dg (a ++ b))).tree.ExecutionPath) →
    (q : (protocol (pairedRoundsK Dg a ++ pairedRoundsK Dg b)).tree.ExecutionPath) →
    castPath (pairedRoundsK_append Dg a b) p = q →
    fstPath (pairedRoundsK Dg a) q = fstP Dg a b p ∧ sndPath (pairedRoundsK Dg a) q = sndP Dg a b p
  | [], b, p, q, h => by
      have hq : q = p := by
        rw [← h]; rfl
      subst hq
      exact ⟨rfl, rfl⟩
  | ⟨r, .clear⟩ :: a, b, p, q, h => by
      obtain ⟨h1, h2, h3⟩ := castPath_cons (r := r) (r' := r) rfl (pairedRoundsK_append Dg a b) _ p q h
      obtain ⟨ih1, ih2⟩ := castPath_paired_append a b p.2.2 q.2.2 h3
      refine ⟨?_, ih2⟩
      show fstPath (r :: pairedRoundsK Dg a) q = (⟨p.1, p.2.1, fstP Dg a b p.2.2⟩ : (protocol (r :: pairedRoundsK Dg a)).tree.ExecutionPath)
      have key : fstPath (r :: pairedRoundsK Dg a) q =
          (⟨q.1, q.2.1, fstPath (pairedRoundsK Dg a) q.2.2⟩ : (protocol (r :: pairedRoundsK Dg a)).tree.ExecutionPath) := rfl
      rw [key, ih1, ← eq_of_heq h1, ← eq_of_heq h2]
  | ⟨r, .merkle _ _ _ _ _⟩ :: a, b, p, q, h => by
      obtain ⟨h1, h2, h3⟩ := castPath_cons (r := pairedRound Dg r) (r' := pairedRound Dg r) rfl
        (pairedRoundsK_append Dg a b) _ p q h
      obtain ⟨ih1, ih2⟩ := castPath_paired_append a b p.2.2 q.2.2 h3
      refine ⟨?_, ih2⟩
      show fstPath (pairedRound Dg r :: pairedRoundsK Dg a) q = (⟨p.1, p.2.1, fstP Dg a b p.2.2⟩ : (protocol (pairedRound Dg r :: pairedRoundsK Dg a)).tree.ExecutionPath)
      have key : fstPath (pairedRound Dg r :: pairedRoundsK Dg a) q =
          (⟨q.1, q.2.1, fstPath (pairedRoundsK Dg a) q.2.2⟩ : (protocol (pairedRound Dg r :: pairedRoundsK Dg a)).tree.ExecutionPath) := rfl
      rw [key, ih1, ← eq_of_heq h1, ← eq_of_heq h2]

theorem castPath_base_append : (a b : MRounds Dg) →
    (p : (protocol (baseRounds Dg (a ++ b))).tree.ExecutionPath) →
    (q : (protocol (baseRounds Dg a ++ baseRounds Dg b)).tree.ExecutionPath) →
    castPath (baseRounds_append Dg a b) p = q →
    fstPath (baseRounds Dg a) q = fstB Dg a b p ∧ sndPath (baseRounds Dg a) q = sndB Dg a b p
  | [], b, p, q, h => by
      have hq : q = p := by
        rw [← h]; rfl
      subst hq
      exact ⟨rfl, rfl⟩
  | ⟨r, _⟩ :: a, b, p, q, h => by
      obtain ⟨h1, h2, h3⟩ := castPath_cons (r := r) (r' := r) rfl (baseRounds_append Dg a b) _ p q h
      obtain ⟨ih1, ih2⟩ := castPath_base_append a b p.2.2 q.2.2 h3
      refine ⟨?_, ih2⟩
      show fstPath (r :: baseRounds Dg a) q = (⟨p.1, p.2.1, fstB Dg a b p.2.2⟩ : (protocol (r :: baseRounds Dg a)).tree.ExecutionPath)
      have key : fstPath (r :: baseRounds Dg a) q =
          (⟨q.1, q.2.1, fstPath (baseRounds Dg a) q.2.2⟩ : (protocol (r :: baseRounds Dg a)).tree.ExecutionPath) := rfl
      rw [key, ih1, ← eq_of_heq h1, ← eq_of_heq h2]

end Cast

end NockvmE2E.Merkle.MA
