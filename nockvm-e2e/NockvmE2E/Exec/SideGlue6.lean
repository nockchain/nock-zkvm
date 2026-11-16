/-
 conjunct 5, step "FS agreement".
Generic part: decoders that agree on the first `n` rounds (`DAgree`), `msgsDec_of_agree` (messages decoded with `ds` are `MsgsDec` for any `ds'`
agreeing as far as `fm` goes), `mDecs_agree` (the compiled decoders differ only in the opening round).
Side part: `length_friMerkleMask`, `length_SMSg`, `fs_side` (the side FS key/answer at flat prefix `z :: ctx :: fm.take i`
is the encoded challenge `i-1` of the path of the side messages).  `hglue_J8` is NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue6` is complete.
-/
import NockvmE2E.Exec.SideGlue5

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue
open NockvmE2E.Exec NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Exec.V NockvmE2E.Merkle NockvmE2E.Exec.SideInst NockvmE2E.Exec.Emb
  NockvmE2E.Merkle.Fri

/-- two decoder lists agree (on `decM`) for the first `n` rounds -/
def DAgree : (rounds : List Round) → Decs rounds → Decs rounds → ℕ → Prop
  | _, _, _, 0 => True
  | [], _, _, _ + 1 => True
  | _ :: rs, (d, ds), (d', ds'), n + 1 => d.decM = d'.decM ∧ DAgree rs ds ds' n

theorem msgsDec_of_agree : (rounds : List Round) → (d d' : Decs rounds) → (fm : List (List ℕ)) →
    DAgree rounds d d' fm.length → MsgsDec rounds d' fm (decMsgs rounds d fm)
  | [], _, _, _, _ => trivial
  | r :: rs, (d, ds), (d', ds'), [], _ => by
      refine ⟨fun h => absurd rfl h, ?_⟩
      exact msgsDec_of_agree rs ds ds' [] (by simp [DAgree])
  | r :: rs, (d, ds), (d', ds'), m :: t, h => by
      obtain ⟨h1, h2⟩ := h
      refine ⟨fun _ => ?_, msgsDec_of_agree rs ds ds' t h2⟩
      simp only [List.headD_cons]
      show d.decM m = d'.decM m
      rw [h1]

theorem DAgree_mono : (rounds : List Round) → (d d' : Decs rounds) → {n m : ℕ} → n ≤ m →
    DAgree rounds d d' m → DAgree rounds d d' n
  | _, _, _, 0, _, _, _ => by simp [DAgree]
  | [], _, _, _ + 1, _, _, _ => trivial
  | _ :: _, _, _, _ + 1, 0, h, _ => by omega
  | r :: rs, (d, ds), (d', ds'), n + 1, m + 1, h, hh =>
      ⟨hh.1, DAgree_mono rs ds ds' (by omega) hh.2⟩

section Gen
variable {Yd : Type} [Finite Yd] [DecidableEq Yd] (dY : List ℕ → Yd) {Op : Type} [Finite Op] [DecidableEq Op]

theorem mDecs_agree : (ms : MRounds Yd) → (ds : MDec ms) → (ω ω' : Op) →
    DAgree (compiledRoundsK Yd Op ms) (mDecs dY ms ds ω) (mDecs dY ms ds ω') ms.length
  | [], _, _, _ => by simp [DAgree]
  | ⟨r, .clear⟩ :: ms, (d, ds), ω, ω' => by
      refine ⟨rfl, ?_⟩
      exact mDecs_agree ms ds ω ω'
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms, (c, ds), ω, ω' => by
      refine ⟨rfl, ?_⟩
      exact mDecs_agree ms ds ω ω'

end Gen

section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

theorem length_friMerkleMask : (i c : ℕ) → (h : i + c = k) →
    (friMerkleMask s 1 l L DgJ8 E2EResid.encK i c h).length = c + 1
  | _, 0, _ => rfl
  | i, c + 1, h => by
      show (friMerkleMask s 1 l L DgJ8 E2EResid.encK i.succ c _).length + 1 = c + 1 + 1
      rw [length_friMerkleMask i.succ c (by omega)]

theorem length_SMSg : (SMSg s l L).length = k + 3 := by
  unfold SMSg NockvmE2E.Merkle.SideMerkle.bMask friMask
  show (friMerkleMask s 1 l L DgJ8 E2EResid.encK 0 k (by omega)).length + 1 + 1 = k + 3
  rw [length_friMerkleMask s l L 0 k (by omega)]

variable (XI : ExecInst) {Statement Salt : Type} (decZ : List ℕ → Statement × Salt)
  (encZ : Statement × Salt → List ℕ)

theorem length_keysOf {Input : Type} (z : Input) : (rounds : List Round) → (ms : PublicMessages rounds) →
    (keysOf z rounds ms).length = rounds.length
  | [], _ => rfl
  | _ :: rs, (m, ms) => by simp [keysOf, length_keysOf z rs ms]

/-- **FS agreement** (side): at the flat prefix `z :: ctx :: fm.take i` (`1 ≤ i ≤ fm.length`, `fm.length ≤ k + 3`) the side FS key readout
gives the encoded challenge `i-1` of the path of the messages decoded from `fm` (with any opening `ω`). -/
theorem fs_side (hz : ∀ x, decZ (encZ x) = x) {Op : Type} [Finite Op] [DecidableEq Op] (ω0 ω : Op)
    (gk : (kk : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) → kk.Challenge)
    (z0 : Statement × Salt) (ctx : List ℕ) (fm : List (List ℕ)) (hfm : fm.length ≤ k + 3)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ fm.length) (nn : ℕ) :
    frOfX s l L XI ω0 (fkOfX s l L XI decZ ω0 (encZ z0 :: ctx :: fm.take i)) (gk _) nn =
      (encPathD _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω0)
        (pathOf (stF XI ctx (fm.headD []), z0) _ gk
          (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω) fm))).getD (i - 1) [] := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, t, rfl⟩ : ∃ m t, fm = m :: t := by
    cases fm with
    | nil => simp at hi
    | cons m t => exact ⟨m, t, rfl⟩
  have hj : j < (m :: t).length := by simp at hi ⊢; omega
  have hag : DAgree _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω) (mDecs dgOf (SMSg s l L) (dsS s l L) ω0) (m :: t).length := by
    have h1 := mDecs_agree dgOf (SMSg s l L) (dsS s l L) ω ω0
    rw [length_SMSg s l L] at h1
    exact DAgree_mono _ _ _ hfm h1
  have hms := msgsDec_of_agree _ _ _ (m :: t) hag
  set zI : SStmt XI × (Statement × Salt) := (stF XI ctx m, z0) with hzI
  have hk := decKeyA_keysOf zI _ _ (m :: t) _ hms j hj
  rw [List.take_succ_cons] at hk
  have hlen : j < (keysOf zI (compiledRoundsK DgJ8 Op (SMSg s l L))
      (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω) (m :: t))).length := by
    rw [length_keysOf, compiledRoundsK_length, length_SMSg s l L]; simp at hj; omega
  obtain ⟨kk, hkk⟩ : ∃ kk, (keysOf zI (compiledRoundsK DgJ8 Op (SMSg s l L))
      (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω) (m :: t)))[j]? = some kk :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  rw [hkk] at hk
  simp only [frOfX, fkOfX, List.take_succ_cons, List.headD_cons]
  rw [hz z0, hk]
  simp only [Option.getD_some]
  rw [Nat.add_sub_cancel, encPathD_pathOf, List.getD_eq_getElem?_getD, List.getElem?_map, hkk]
  simp

end Side

end NockvmE2E.Exec.SideGlue

#print axioms NockvmE2E.Exec.SideGlue.msgsDec_of_agree
#print axioms NockvmE2E.Exec.SideGlue.mDecs_agree
#print axioms NockvmE2E.Exec.SideGlue.length_SMSg
#print axioms NockvmE2E.Exec.SideGlue.fs_side
