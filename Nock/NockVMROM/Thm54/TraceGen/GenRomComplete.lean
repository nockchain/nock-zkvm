/-
  Nock/NockVMROM/Thm54/TraceGen/GenRomComplete.lean

  **Generator completeness on the ROM: every terminating `NockVMROM` program is accepted.**

  The tree already had the SOUNDNESS direction — `genComputeSkeleton_evalN`
  (`GenMatmulBounded.lean:334`): whatever the generator accepts, the reference interpreter agrees
  with.

  **It is false as stated at `Nock.evalN`.**  `evalN` implements `OP_10`
  (`Reference.lean:133-140`, the `#` edit) and `OP_11` (`:141-147`, hints), while
  `genComputeSkeleton` answers `.error.notROM` for both (`Gen.lean:750-751`).  So `evalN` success
  does not imply acceptance and a restriction is unavoidable.

  **The restriction is the paper's own, and it is an execution-level condition, not a syntactic
  one.**  `Def:Nock`'s opcode set is `𝒪𝒫 = {OP_0, …, OP_10}`, and the paper defines

  > `NockVMROM^Λ` as in Definition~\ref{Def:Nock} but **without** `OP_10`

  so the paper's ROM transition function is exactly `OP_0 … OP_9` together with `cons` — which is
  exactly `genComputeSkeleton`'s accepted opcode set.  `evalRom` below is `Nock.evalN` with those
  two arms replaced by `none`, i.e. the ROM transition function of the paper, and
  `evalRom … = some result` is the statement "this program terminates *inside the ROM*".

  A **syntactic** no-`OP_10` condition on the source formula would not do, and the reason is
  structural rather than incidental: `OP_2` evaluates `*[*[a b] *[a c]]`, so the formula its third
  sub-evaluation runs is a computed noun, and `OP_9` fetches its formula out of the subject with
  `slot`.  Neither is bounded by anything syntactic about the source.  `evalRom` is confined to the
  execution because it recurses exactly where `evalN` recurses.

  Three results:

  * `gen_ok_of_evalRom` — **completeness**: `evalRom fuel subject formula = some result` gives an
    accepted tree returning that very `result`.
  * `evalRom_of_gen_ok` — and the converse, so acceptance and ROM termination are the *same*
    condition: `genComputeSkeleton` recognises precisely `NockVMROM`.

  **Not claimed.**  Nothing here removes a side condition of `nockCompiles_of_accepted`
  (`GenNockCompiles.lean`): the emitted tree `t` still has to be named before `hseed`, `hcoins`,
  `hconf`, `hb`, `haxis`, `hbad`, `hout` and the capacity bounds can be stated about it, and
  completeness supplies `t` rather than discharging those.  No §J box moves.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk

/-! ## The ROM transition function

`Nock.evalN` (`Reference.lean:76`) with the two out-of-ROM arms answering `none`.  Every other arm
is character-for-character `evalN`'s, so the two agree wherever `evalRom` succeeds
(`evalRom_evalN`) -/

/-- **`*[subject formula]` in `NockVMROM^Λ`** — fuel-indexed, `OP_10` and above rejected. -/
def evalRom : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalRom fuel subj (.cell b c), evalRom fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => Noun.slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalRom fuel subj b, evalRom fuel subj c with
             | some sb, some sc => evalRom fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalRom fuel subj tail).map Noun.wut
    | 4 => (evalRom fuel subj tail).bind Noun.lus
    | 5 => match tail with
           | .cell b c =>
             match evalRom fuel subj b, evalRom fuel subj c with
             | some sb, some sc => some (Noun.tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalRom fuel subj b with
             | some (.atom 0) => evalRom fuel subj c
             | some (.atom 1) => evalRom fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalRom fuel subj b with
             | some sb => evalRom fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalRom fuel subj b with
             | some sb => evalRom fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalRom fuel subj c with
             | some core =>
               match Noun.slot ax core with
               | some arm => evalRom fuel core arm
               | none => none
             | none => none
           | _ => none
    | _ => none

/-! ## The ROM semantics refines the full semantics -/

/-- **`evalRom` ≤ `evalN`.**  Every arm but `OP_10`/`OP_11` is `evalN`'s own, so a ROM run is a
Nock run. -/
theorem evalRom_evalN :
    ∀ {fuel : ℕ} {subject formula result : Noun},
      evalRom fuel subject formula = some result →
      Nock.evalN fuel subject formula = some result := by
  intro fuel
  induction fuel with
  | zero => intro subject formula result h; simp [evalRom] at h
  | succ n ih =>
    intro subject formula result h
    cases formula with
    | atom _ => simp [evalRom] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : evalRom n subject (.cell lh lt) with
        | none => simp [evalRom, hL] at h
        | some l =>
          cases hR : evalRom n subject tl with
          | none => simp [evalRom, hL, hR] at h
          | some r =>
            simp [evalRom, hL, hR] at h
            simp [Nock.evalN, ih hL, ih hR, h]
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        -- OP_0
        · cases tl with
          | cell _ _ => simp [evalRom] at h
          | atom ax => simpa [evalRom, Nock.evalN] using h
        -- OP_1
        · simpa [evalRom, Nock.evalN] using h
        -- OP_2
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hB, hC] at h
              | some sc =>
                simp only [evalRom, hB, hC] at h
                simp [Nock.evalN, ih hB, ih hC, ih h]
        -- OP_3
        · cases hcall : evalRom n subject tl with
          | none => simp [evalRom, hcall] at h
          | some v =>
            simp only [evalRom, hcall, Option.map_some] at h
            simp [Nock.evalN, ih hcall, h]
        -- OP_4
        · cases hcall : evalRom n subject tl with
          | none => simp [evalRom, hcall] at h
          | some v =>
            simp only [evalRom, hcall, Option.bind_some] at h
            simp [Nock.evalN, ih hcall, h]
        -- OP_5
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hB, hC] at h
              | some sc =>
                simp only [evalRom, hB, hC, Option.some_inj] at h
                simp [Nock.evalN, ih hB, ih hC, h]
        -- OP_6
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [evalRom] at h
            | cell c d =>
              cases hcond : evalRom n subject b with
              | none => simp [evalRom, hcond] at h
              | some cond =>
                cases cond with
                | cell _ _ => simp [evalRom, hcond] at h
                | atom cv =>
                  match cv with
                  | 0 =>
                    simp only [evalRom, hcond] at h
                    simp [Nock.evalN, ih hcond, ih h]
                  | 1 =>
                    simp only [evalRom, hcond] at h
                    simp [Nock.evalN, ih hcond, ih h]
                  | (m + 2) => simp [evalRom, hcond] at h
        -- OP_7
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              simp only [evalRom, hB] at h
              simp [Nock.evalN, ih hB, ih h]
        -- OP_8
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              simp only [evalRom, hB] at h
              simp [Nock.evalN, ih hB, ih h]
        -- OP_9
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell ax0 c =>
            cases ax0 with
            | cell _ _ => simp [evalRom] at h
            | atom ax =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hC] at h
              | some core =>
                cases harm : Noun.slot ax core with
                | none => simp [evalRom, hC, harm] at h
                | some arm =>
                  simp only [evalRom, hC, harm] at h
                  simp [Nock.evalN, ih hC, harm, ih h]
        -- OP_10
        · simp [evalRom] at h
        -- OP_11
        · simp [evalRom] at h
        -- op ≥ 12
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [evalRom] at h
          split at h <;> first | omega | contradiction


/-! ## Completeness

`genComputeSkeleton_evalN` (`GenMatmulBounded.lean:334`) plus `evalRom_evalN` pin every
intermediate value the generator computes to the value the ROM semantics computes, so the
induction below only has to show that the generator does not *error*. -/

section Complete

variable {K : Type} [Field K]

/-- **An accepted subcall returns the ROM value.**  Soundness composed with the refinement, so no
induction: it is available at every fuel and every node. -/
theorem gen_result_eq_of_evalRom {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {r r' : Noun}
    (hg : genComputeSkeleton (K := K) fuel subject formula = .ok (t, r))
    (hr : evalRom fuel subject formula = some r') : r = r' :=
  Option.some.inj ((genComputeSkeleton_evalN hg).symm.trans (evalRom_evalN hr))

/-- **The generator never errors on a terminating ROM program.**  Each arm of `evalRom` is the arm
of `genComputeSkeleton` that emits the corresponding row, and `gen_result_eq_of_evalRom` identifies
the computed subject/formula/condition each value-dependent match consults. -/
theorem gen_not_error_of_evalRom :
    ∀ (fuel : ℕ) (subject formula result : Noun) (e : GenError),
      evalRom fuel subject formula = some result →
      genComputeSkeleton (K := K) fuel subject formula = .error e → False := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h _; simp [evalRom] at h
  | succ n ih =>
    intro subject formula result e h hg
    cases formula with
    | atom _ => simp [evalRom] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : evalRom n subject (.cell lh lt) with
        | none => simp [evalRom, hL] at h
        | some l =>
          cases hR : evalRom n subject tl with
          | none => simp [evalRom, hL, hR] at h
          | some r =>
            cases hgL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
            | error e' => exact ih _ _ _ _ hL hgL
            | ok pL =>
              cases hgR : genComputeSkeleton (K := K) n subject tl with
              | error e' => exact ih _ _ _ _ hR hgR
              | ok pR => simp [genComputeSkeleton, hgL, hgR] at hg
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        -- OP_0: the axis read
        · cases tl with
          | cell _ _ => simp [evalRom] at h
          | atom ax =>
            simp only [evalRom] at h
            simp [genComputeSkeleton, h] at hg
        -- OP_1: the constant
        · simp [genComputeSkeleton] at hg
        -- OP_2: eval, whose third subcall's SUBJECT and FORMULA are both computed
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hB, hC] at h
              | some sc =>
                simp only [evalRom, hB, hC] at h
                cases hgB : genComputeSkeleton (K := K) n subject b with
                | error e' => exact ih _ _ _ _ hB hgB
                | ok pB =>
                  obtain ⟨tB, rB⟩ := pB
                  cases hgC : genComputeSkeleton (K := K) n subject c with
                  | error e' => exact ih _ _ _ _ hC hgC
                  | ok pC =>
                    obtain ⟨tC, rC⟩ := pC
                    have hb2 : rB = sb := gen_result_eq_of_evalRom hgB hB
                    have hc2 : rC = sc := gen_result_eq_of_evalRom hgC hC
                    cases hgM : genComputeSkeleton (K := K) n rB rC with
                    | error e' =>
                      rw [hb2, hc2] at hgM
                      exact ih _ _ _ _ h hgM
                    | ok pM => simp [genComputeSkeleton, hgB, hgC, hgM] at hg
        -- OP_3: the cell test
        · cases hcall : evalRom n subject tl with
          | none => simp [evalRom, hcall] at h
          | some v =>
            cases hgc : genComputeSkeleton (K := K) n subject tl with
            | error e' => exact ih _ _ _ _ hcall hgc
            | ok p => simp [genComputeSkeleton, hgc] at hg
        -- OP_4: the increment
        · cases hcall : evalRom n subject tl with
          | none => simp [evalRom, hcall] at h
          | some v =>
            simp only [evalRom, hcall, Option.bind_some] at h
            cases hgc : genComputeSkeleton (K := K) n subject tl with
            | error e' => exact ih _ _ _ _ hcall hgc
            | ok p =>
              obtain ⟨tp, rp⟩ := p
              have hp2 : rp = v := gen_result_eq_of_evalRom hgc hcall
              rw [hp2] at hgc
              simp [genComputeSkeleton, hgc, h] at hg
        -- OP_5: the equality gate
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hB, hC] at h
              | some sc =>
                cases hgB : genComputeSkeleton (K := K) n subject b with
                | error e' => exact ih _ _ _ _ hB hgB
                | ok pB =>
                  cases hgC : genComputeSkeleton (K := K) n subject c with
                  | error e' => exact ih _ _ _ _ hC hgC
                  | ok pC => simp [genComputeSkeleton, hgB, hgC] at hg
        -- OP_6: the branch, whose tree SHAPE depends on the computed condition
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [evalRom] at h
            | cell c d =>
              cases hcond : evalRom n subject b with
              | none => simp [evalRom, hcond] at h
              | some cond =>
                cases hgCond : genComputeSkeleton (K := K) n subject b with
                | error e' => exact ih _ _ _ _ hcond hgCond
                | ok pCond =>
                  obtain ⟨tCond, rCond⟩ := pCond
                  have hcv : rCond = cond := gen_result_eq_of_evalRom hgCond hcond
                  cases cond with
                  | cell _ _ => simp [evalRom, hcond] at h
                  | atom cv =>
                    match cv with
                    | 0 =>
                      simp only [evalRom, hcond] at h
                      cases hgT : genComputeSkeleton (K := K) n subject c with
                      | error e' => exact ih _ _ _ _ h hgT
                      | ok pT => simp [genComputeSkeleton, hgCond, hcv, hgT] at hg
                    | 1 =>
                      simp only [evalRom, hcond] at h
                      cases hgT : genComputeSkeleton (K := K) n subject d with
                      | error e' => exact ih _ _ _ _ h hgT
                      | ok pT => simp [genComputeSkeleton, hgCond, hcv, hgT] at hg
                    | (m + 2) => simp [evalRom, hcond] at h
        -- OP_7: compose, whose second subcall's SUBJECT is computed
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              simp only [evalRom, hB] at h
              cases hgB : genComputeSkeleton (K := K) n subject b with
              | error e' => exact ih _ _ _ _ hB hgB
              | ok pB =>
                obtain ⟨tB, rB⟩ := pB
                have hb2 : rB = sb := gen_result_eq_of_evalRom hgB hB
                cases hgC : genComputeSkeleton (K := K) n rB c with
                | error e' =>
                  rw [hb2] at hgC
                  exact ih _ _ _ _ h hgC
                | ok pC => simp [genComputeSkeleton, hgB, hgC] at hg
        -- OP_8: push, whose second subcall's SUBJECT is the computed pair
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell b c =>
            cases hB : evalRom n subject b with
            | none => simp [evalRom, hB] at h
            | some sb =>
              simp only [evalRom, hB] at h
              cases hgB : genComputeSkeleton (K := K) n subject b with
              | error e' => exact ih _ _ _ _ hB hgB
              | ok pB =>
                obtain ⟨tB, rB⟩ := pB
                have hb2 : rB = sb := gen_result_eq_of_evalRom hgB hB
                cases hgC : genComputeSkeleton (K := K) n (.cell rB subject) c with
                | error e' =>
                  rw [hb2] at hgC
                  exact ih _ _ _ _ h hgC
                | ok pC => simp [genComputeSkeleton, hgB, hgC] at hg
        -- OP_9: invoke, whose FORMULA is fetched out of the computed core
        · cases tl with
          | atom _ => simp [evalRom] at h
          | cell ax0 c =>
            cases ax0 with
            | cell _ _ => simp [evalRom] at h
            | atom ax =>
              cases hC : evalRom n subject c with
              | none => simp [evalRom, hC] at h
              | some core =>
                cases harm : Noun.slot ax core with
                | none => simp [evalRom, hC, harm] at h
                | some arm =>
                  simp only [evalRom, hC, harm] at h
                  cases hgCore : genComputeSkeleton (K := K) n subject c with
                  | error e' => exact ih _ _ _ _ hC hgCore
                  | ok pCore =>
                    obtain ⟨tCore, rCore⟩ := pCore
                    have hcore2 : rCore = core := gen_result_eq_of_evalRom hgCore hC
                    cases hgInv : genComputeSkeleton (K := K) n rCore arm with
                    | error e' =>
                      rw [hcore2] at hgInv
                      exact ih _ _ _ _ h hgInv
                    | ok pInv =>
                      rw [hcore2] at hgInv
                      simp [genComputeSkeleton, hgCore, hcore2, harm, hgInv] at hg
        -- OP_10: outside the ROM
        · simp [evalRom] at h
        -- OP_11: not a paper opcode at all
        · simp [evalRom] at h
        -- op ≥ 12: crash
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [evalRom] at h
          split at h <;> first | omega | contradiction

/-- **Generator completeness on the ROM.**  Every program that terminates inside `NockVMROM` is accepted by `genComputeSkeleton`, and the tree it emits carries exactly the
ROM result. -/
theorem gen_ok_of_evalRom {fuel : ℕ} {subject formula result : Noun}
    (h : evalRom fuel subject formula = some result) :
    ∃ t : NTree (GenComputeRow K),
      genComputeSkeleton (K := K) fuel subject formula = .ok (t, result) := by
  cases hgg : genComputeSkeleton (K := K) fuel subject formula with
  | error e => exact absurd hgg (fun hh => gen_not_error_of_evalRom fuel subject formula result e h hh)
  | ok p =>
    obtain ⟨t, r⟩ := p
    have hr : r = result := gen_result_eq_of_evalRom hgg h
    exact ⟨t, by rw [hr]⟩

/-- **The converse: an accepted program terminates inside the ROM.**  Mirror of
`genComputeSkeleton_evalN` (`GenMatmulBounded.lean:334`) against `evalRom` instead of `evalN`;
the `OP_10`/`OP_11` arms are unchanged because the generator already declines both.  With
`gen_ok_of_evalRom` this says `genComputeSkeleton` recognises **exactly** the terminating
`NockVMROM` programs. -/
theorem evalRom_of_gen_ok
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    evalRom fuel subject formula = some result := by
  induction fuel generalizing subject formula t result with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ =>
          simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [evalRom, ih hL, ih hR]
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · cases tl with
          | cell _ _ =>
            simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none =>
              simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [evalRom, hslot]
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [evalRom]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ =>
                  simp [genComputeSkeleton, hBcall, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hBcall, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp [evalRom, ih hBcall, ih hC, ih hM]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [evalRom, ih hcall]
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none =>
              simp [genComputeSkeleton, hcall, hlus] at h
            | some lusR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [evalRom, ih hcall, hlus]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [evalRom, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ =>
              simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ =>
                simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ =>
                  simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp [evalRom, ih hcond, hval, ih htaken]
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp [evalRom, ih hcond, hval, ih htaken]
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [evalRom, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hBcall : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hBcall] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ =>
                simp [genComputeSkeleton, hBcall, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hBcall, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [evalRom, ih hBcall, ih hC]
        · cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ =>
              simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none =>
                  simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    simp [evalRom, ih hcore, hslot, ih hinv]
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-- The compute tree the generator emits on a terminating ROM program.  Total by completeness
(`gen_ok_of_evalRom`); `romTree_spec` is the defining equation. -/
noncomputable def romTree {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result) : NTree (GenComputeRow K) :=
  (gen_ok_of_evalRom (K := K) hrom).choose

/-- `romTree` is the accepted tree, and the generator's result on it is the ROM result. -/
theorem romTree_spec {fuel : ℕ} {subject formula result : Noun}
    (hrom : evalRom fuel subject formula = some result) :
    genComputeSkeleton (K := K) fuel subject formula = .ok (romTree (K := K) hrom, result) :=
  (gen_ok_of_evalRom (K := K) hrom).choose_spec

/-- **Acceptance and ROM termination are the same condition.** -/
theorem gen_ok_iff_evalRom {fuel : ℕ} {subject formula result : Noun} :
    (∃ t : NTree (GenComputeRow K),
        genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
      ↔ evalRom fuel subject formula = some result :=
  ⟨fun ⟨_, hg⟩ => evalRom_of_gen_ok hg, fun h => gen_ok_of_evalRom h⟩

end Complete

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.evalRom_evalN
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_result_eq_of_evalRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_not_error_of_evalRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_ok_of_evalRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.evalRom_of_gen_ok
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_ok_iff_evalRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.romTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.romTree_spec
