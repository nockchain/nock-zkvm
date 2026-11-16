/-
sequential append of round extractors at
the level of Quang Dao's fixed round lists (`StateRestoration.protocol (r₁ ++ r₂)`).

ArkLib has the tree-level version (`RoundExtractor.append`, `Security/KnowledgeAppend.lean`), stated
on `PFunctor.FreeM.append`; `protocol (r₁ ++ r₂)` is not syntactically such an append, so the same
construction is redone here by recursion on `r₁` (every step is definitional). The suffix extractor may
depend on the whole prefix path and starts in the prefix's terminal knowledge state.

* `appExt`, `appExt_terminal`, `appExt_preserving`, `appExt_bounded`: the join and its three laws.
* `appErr`, `sum_appErr`, `appErr_le`: the joined error vector, its sum and maximum.
* `constExt`: the constant-state extractor (error `0`); `reroot`: change the input state of an
  extractor whose first node is an oracle message.
-/
import NockvmE2E.Rap.Bridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped ENNReal

namespace NockvmE2E.Succ.App

open NockvmE2E.Rap

/-! ## Paths of `r₁ ++ r₂` -/

/-- The prefix part of a path of `r₁ ++ r₂`. -/
def fstPath : (r1 : List Round) → {r2 : List Round} →
    (protocol (r1 ++ r2)).tree.ExecutionPath → (protocol r1).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | _ :: r1, _, p => ⟨p.1, p.2.1, fstPath r1 p.2.2⟩

/-- The suffix part of a path of `r₁ ++ r₂`. -/
def sndPath : (r1 : List Round) → {r2 : List Round} →
    (protocol (r1 ++ r2)).tree.ExecutionPath → (protocol r2).tree.ExecutionPath
  | [], _, p => p
  | _ :: r1, _, p => sndPath r1 p.2.2

/-! ## The joined extractor -/

/-- **Join** a prefix extractor and a prefix-path-dependent suffix extractor (which starts in the
prefix's terminal state). -/
def appExt : (r1 : List Round) → {r2 : List Round} → {st : KnowledgeState.{0}} →
    (E1 : RoundExtractor (protocol r1).tree st) →
    (E2 : (p : (protocol r1).tree.ExecutionPath) →
      RoundExtractor (protocol r2).tree (E1.terminalState p)) →
    RoundExtractor (protocol (r1 ++ r2)).tree st
  | [], _, _, _, E2 => E2 PUnit.unit
  | _ :: r1, _, _, E1, E2 => fun msg =>
      ⟨(E1 msg).1, (E1 msg).2.1, fun ch =>
        ⟨((E1 msg).2.2 ch).1, ((E1 msg).2.2 ch).2.1,
          appExt r1 ((E1 msg).2.2 ch).2.2 (fun p => E2 ⟨msg, ch, p⟩)⟩⟩

theorem appExt_terminal : (r1 : List Round) → {r2 : List Round} → {st : KnowledgeState.{0}} →
    (E1 : RoundExtractor (protocol r1).tree st) →
    (E2 : (p : (protocol r1).tree.ExecutionPath) →
      RoundExtractor (protocol r2).tree (E1.terminalState p)) →
    (p : (protocol (r1 ++ r2)).tree.ExecutionPath) →
    (appExt r1 E1 E2).terminalState p = (E2 (fstPath r1 p)).terminalState (sndPath r1 p)
  | [], _, _, _, _, _ => rfl
  | _ :: r1, _, _, E1, E2, p =>
      appExt_terminal r1 ((E1 p.1).2.2 p.2.1).2.2 (fun q => E2 ⟨p.1, p.2.1, q⟩) p.2.2

theorem appExt_preserving : (r1 : List Round) → {r2 : List Round} → {st : KnowledgeState.{0}} →
    (E1 : RoundExtractor (protocol r1).tree st) →
    (E2 : (p : (protocol r1).tree.ExecutionPath) →
      RoundExtractor (protocol r2).tree (E1.terminalState p)) →
    E1.IsProverPreserving (protocol r1).roles →
    (∀ p, (E2 p).IsProverPreserving (protocol r2).roles) →
    (appExt r1 E1 E2).IsProverPreserving (protocol (r1 ++ r2)).roles
  | [], _, _, _, _, _, h2 => h2 PUnit.unit
  | _ :: r1, _, _, E1, E2, h1, h2 => ⟨fun msg w h => h1.1 msg w h, fun msg =>
      ⟨fun _ hrole => (nomatch hrole), fun ch =>
        appExt_preserving r1 ((E1 msg).2.2 ch).2.2 (fun p => E2 ⟨msg, ch, p⟩) ((h1.2 msg).2 ch)
          (fun _ => h2 _)⟩⟩

/-- The joined error vector. -/
def appErr : (r1 : List Round) → {r2 : List Round} → RoundErrors r1 → RoundErrors r2 →
    RoundErrors (r1 ++ r2)
  | [], _, _, e2 => e2
  | _ :: r1, _, e1, e2 => fun j => Fin.cases (e1 0) (appErr r1 (fun j => e1 j.succ) e2) j

theorem appExt_bounded : (r1 : List Round) → {r2 : List Round} → {st : KnowledgeState.{0}} →
    (E1 : RoundExtractor (protocol r1).tree st) →
    (E2 : (p : (protocol r1).tree.ExecutionPath) →
      RoundExtractor (protocol r2).tree (E1.terminalState p)) →
    (e1 : RoundErrors r1) → (e2 : RoundErrors r2) →
    E1.IsLocallyBounded (protocol r1).roles (roundErrorSchedule r1 e1) →
    (∀ p, (E2 p).IsLocallyBounded (protocol r2).roles (roundErrorSchedule r2 e2)) →
    (appExt r1 E1 E2).IsLocallyBounded (protocol (r1 ++ r2)).roles
      (roundErrorSchedule (r1 ++ r2) (appErr r1 e1 e2))
  | [], _, _, _, _, _, _, _, h2 => h2 PUnit.unit
  | _ :: r1, _, _, E1, E2, e1, e2, h1, h2 => fun msg =>
      ⟨(h1 msg).1, fun ch => appExt_bounded r1 ((E1 msg).2.2 ch).2.2 (fun p => E2 ⟨msg, ch, p⟩)
        (fun j => e1 j.succ) e2 ((h1 msg).2 ch) (fun _ => h2 _)⟩

theorem sum_appErr : (r1 : List Round) → {r2 : List Round} → (e1 : RoundErrors r1) →
    (e2 : RoundErrors r2) → ∑ j, appErr r1 e1 e2 j = ∑ j, e1 j + ∑ j, e2 j
  | [], _, e1, e2 => by
    show ∑ j, e2 j = ∑ j : Fin 0, e1 j + ∑ j, e2 j
    simp
  | _ :: r1, r2, e1, e2 => by
    show ∑ j : Fin ((r1 ++ r2).length + 1), Fin.cases (e1 0) (appErr r1 (fun j => e1 j.succ) e2) j =
      ∑ j : Fin (r1.length + 1), e1 j + ∑ j, e2 j
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := e1)]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [sum_appErr r1 (fun j => e1 j.succ) e2, add_assoc]

theorem appErr_le : (r1 : List Round) → {r2 : List Round} → (e1 : RoundErrors r1) →
    (e2 : RoundErrors r2) → ∀ j, appErr r1 e1 e2 j ≤ Finset.univ.sup e1 ⊔ Finset.univ.sup e2
  | [], _, _, e2, j => le_sup_of_le_right (Finset.le_sup (f := e2) (Finset.mem_univ j))
  | _ :: r1, r2, e1, e2, j => by
    refine Fin.cases ?_ (fun t => ?_) j
    · exact le_sup_of_le_left (Finset.le_sup (f := e1) (Finset.mem_univ _))
    · show appErr r1 (fun j => e1 j.succ) e2 t ≤ _
      refine (appErr_le r1 (fun j => e1 j.succ) e2 t).trans (sup_le_sup_right ?_ _)
      exact Finset.sup_le (fun i _ => Finset.le_sup (f := e1) (Finset.mem_univ _))

theorem sup_appErr_le (r1 : List Round) {r2 : List Round} (e1 : RoundErrors r1)
    (e2 : RoundErrors r2) :
    Finset.univ.sup (appErr r1 e1 e2) ≤ Finset.univ.sup e1 ⊔ Finset.univ.sup e2 :=
  Finset.sup_le (fun j _ => appErr_le r1 e1 e2 j)

/-! ## Constant state and re-rooting -/

/-- The extractor whose state is the constant `ks P` (no challenge can change it). -/
def constExt (P : Prop) : (rs : List Round) → RoundExtractor (protocol rs).tree (ks P)
  | [] => PUnit.unit
  | _ :: rs => fun _ => ⟨ks P, id, fun _ => ⟨ks P, id, constExt P rs⟩⟩

theorem constExt_terminal (P : Prop) : (rs : List Round) →
    (p : (protocol rs).tree.ExecutionPath) → (constExt P rs).terminalState p = ks P
  | [], _ => rfl
  | _ :: rs, p => constExt_terminal P rs p.2.2

theorem constExt_preserving (P : Prop) : (rs : List Round) →
    (constExt P rs).IsProverPreserving (protocol rs).roles
  | [] => trivial
  | _ :: rs => ⟨fun _ _ h => h, fun _ => ⟨fun _ hrole => (nomatch hrole), fun _ =>
      constExt_preserving P rs⟩⟩

theorem constExt_bounded (P : Prop) : (rs : List Round) → (e : RoundErrors rs) →
    (constExt P rs).IsLocallyBounded (protocol rs).roles (roundErrorSchedule rs e)
  | [], _ => trivial
  | _ :: rs, e => fun _ => by
    refine ⟨?_, fun _ => constExt_bounded P rs (fun j => e j.succ)⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ (fun _ ⟨_, h0, h1⟩ => h0 h1)

/-- Change the input state of an extractor whose first node is an oracle message. -/
def reroot {r : Round} {rs : List Round} {st' : KnowledgeState.{0}}
    (E : RoundExtractor (protocol (r :: rs)).tree st') (st : KnowledgeState.{0})
    (f : st'.Witness → st.Witness) : RoundExtractor (protocol (r :: rs)).tree st :=
  fun msg => ⟨(E msg).1, fun w => f ((E msg).2.1 w), (E msg).2.2⟩

theorem reroot_terminal {r : Round} {rs : List Round} {st' : KnowledgeState.{0}}
    (E : RoundExtractor (protocol (r :: rs)).tree st') (st : KnowledgeState.{0})
    (f : st'.Witness → st.Witness) (p : (protocol (r :: rs)).tree.ExecutionPath) :
    (reroot E st f).terminalState p = E.terminalState p := rfl

theorem reroot_preserving {r : Round} {rs : List Round} {st' : KnowledgeState.{0}}
    (E : RoundExtractor (protocol (r :: rs)).tree st') (st : KnowledgeState.{0})
    (f : st'.Witness → st.Witness) (hf : ∀ w, st'.holds w → st.holds (f w))
    (hE : E.IsProverPreserving (protocol (r :: rs)).roles) :
    (reroot E st f).IsProverPreserving (protocol (r :: rs)).roles :=
  ⟨fun msg w h => hf _ (hE.1 msg w h), hE.2⟩

theorem reroot_bounded {r : Round} {rs : List Round} {st' : KnowledgeState.{0}}
    (E : RoundExtractor (protocol (r :: rs)).tree st') (st : KnowledgeState.{0})
    (f : st'.Witness → st.Witness) (e : RoundErrors (r :: rs))
    (hE : E.IsLocallyBounded (protocol (r :: rs)).roles (roundErrorSchedule (r :: rs) e)) :
    (reroot E st f).IsLocallyBounded (protocol (r :: rs)).roles (roundErrorSchedule (r :: rs) e) :=
  hE

end NockvmE2E.Succ.App
