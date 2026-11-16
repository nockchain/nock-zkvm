import Nock.NockVMROM.Thm54.ExprSubstitution
import Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace

/-!
# Decoder-expression substitution for the optimized compute row

Target trace layout is the normalized physical row: base columns `0..12`, then the 58 extension
columns `13..70`. Source compute columns that remain stored are projections. The erased first
memory record is replaced by its exact decoder expressions from the paper.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeSubstitution

open Nock
open Nock.Reified
open ComputeTable

deriving instance DecidableEq for Expr

/-- First optimized extension trace column. -/
def ext0 : ℕ := 13

/-! ## Final compiler namespaces

The source compute AIR owns challenge indices `0..5`.  The walk AIR is translated to index `6`,
and sampled program IO owns indices `7..8`.  Indices `9..11` remain compiler-only folding
challenges.  Public walk endpoints stay at `0..1`; the compute AIR has no public inputs, and the
fixed first/last selector vectors occupy `20..41`.
-/

def tableChallengeBase : ℕ := 0
def tableChallengeCount : ℕ := 6
def walkChallengeBase : ℕ := 6
def walkChallengeCount : ℕ := 1
def sampledChallengeBase : ℕ := 7
def sampledChallengeCount : ℕ := 2
def compilerChallengeBase : ℕ := 9
def compilerChallengeCount : ℕ := 3
/-- First raw base-field challenge index after cubic expansion of all twelve `K` challenges. -/
def finalScalarChallengeBase : ℕ := 36

def tableChallenge (i : ℕ) : Expr := .Var .challenge (tableChallengeBase + i)
def walkChallenge (i : ℕ) : Expr := .Var .challenge (walkChallengeBase + i)
def sampledChallenge (i : ℕ) : Expr := .Var .challenge (sampledChallengeBase + i)

theorem final_challenge_namespace_partition :
    tableChallengeBase + tableChallengeCount ≤ walkChallengeBase ∧
      walkChallengeBase + walkChallengeCount ≤ sampledChallengeBase ∧
      sampledChallengeBase + sampledChallengeCount ≤ compilerChallengeBase ∧
      compilerChallengeBase + compilerChallengeCount = 12 := by
  decide

theorem final_coordinate_challenges_disjoint_scalar :
    3 * (compilerChallengeBase + compilerChallengeCount) ≤ finalScalarChallengeBase := by
  decide

/-- Physical projection of public fingerprint coordinate `role,coord`. -/
def pubFP (kind : VarKind) (role coord : ℕ) : Expr :=
  .Var kind (ext0 + 3 * role + coord)

/-- Physical projection of decomposition fingerprint coordinate `role,coord`. -/
def decFP (kind : VarKind) (role coord : ℕ) : Expr :=
  .Var kind (ext0 + 36 + 3 * role + coord)

def lnPrev (kind : VarKind) : Expr := .Var kind (ext0 + 54)
def lnCur (kind : VarKind) : Expr := .Var kind (ext0 + 55)
def consInv (kind : VarKind) : Expr := .Var kind (ext0 + 56)
def invGen (kind : VarKind) : Expr := .Var kind (ext0 + 57)

/-- Physical role occupied by the first dynamic walk overlay. -/
def overlayANat : State → ℕ
  | .s0 => 3 | .s1 => 2 | .s2 => 3 | .s3 | .s4 => 6
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 9

/-- Physical role occupied by the second dynamic walk overlay. -/
def overlayBNat : State → ℕ
  | .s0 => 4 | .s1 => 3 | .s2 => 4 | .s3 | .s4 => 7
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 10

def restoredAField (kind : VarKind) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s1 => decFP kind 1 coord
  | .s2 => pubFP kind 0 coord
  | _ => .Const 0

def restoredBField (kind : VarKind) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s2 => decFP kind 2 coord
  | _ => .Const 0

def restoredIOHostField (kind : VarKind) (st : State) : Expr :=
  match st with
  | .s2 => pubFP kind 8 2
  | _ => .Const 0

def restoredDenomHostField (kind : VarKind) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s2 => pubFP kind 2 coord
  | _ => .Const 0

def sourcePubAt (kind : VarKind) (st : State) (role coord : ℕ) : Expr :=
  if role = 10 ∧ coord = 2 then restoredIOHostField kind st
  else if role = 11 then restoredDenomHostField kind st coord
  else if role = overlayANat st then restoredAField kind st coord
  else if role = overlayBNat st ∧ coord < 2 then restoredBField kind st coord
  else pubFP kind role coord

/-- Restore every overwritten source fingerprint coordinate by one-hot selection. -/
def restoredPub (kind : VarKind) (role coord : ℕ) : Expr :=
  Nock.Reified.allStates.foldr
    (fun st acc => .Add (.Mul (.Var kind (Nock.Reified.opCol st))
      (sourcePubAt kind st role coord)) acc) (.Const 0)

/-- Exactly the dynamic/fixed host roles use restoration. -/
def semanticPub (kind : VarKind) (role coord : ℕ) : Expr :=
  if role = 2 ∨ role = 3 ∨ role = 4 ∨ role = 6 ∨ role = 7 ∨
      role = 9 ∨ role = 10 ∨ role = 11
  then restoredPub kind role coord
  else pubFP kind role coord

/-- Hybrid overlay: five dynamic walk coordinates followed by four fixed sampled-IO coordinates. -/
def overlayCoord (kind : VarKind) (coord : ℕ) : Expr :=
  if coord < 3 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (.Var kind (Nock.Reified.opCol st))
        (pubFP kind (overlayANat st) coord)) acc) (.Const 0)
  else if coord < 5 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (.Var kind (Nock.Reified.opCol st))
        (pubFP kind (overlayBNat st) (coord - 3))) acc) (.Const 0)
  else if coord = 5 then pubFP kind 10 2
  else pubFP kind 11 (coord - 6)

/-- Its line alias is retained only for regression
artifacts; the production final compiler uses `finalWalkSubst` below. -/
def walkSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => lnCur .traceCur
  | .traceCur, i + 1 => overlayCoord .traceCur i
  | .traceNext, 0 => lnCur .traceNext
  | .traceNext, i + 1 => overlayCoord .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

def finalWalkLineRole : ℕ := 61

/-- Mixed-layout index of the dedicated final walk-line extension role. -/
def finalWalkLineIndex : ℕ := ext0 + finalWalkLineRole

def finalWalkLine (kind : VarKind) : Expr := .Var kind finalWalkLineIndex

def walkInvRole : ℕ := 62

/-- Mixed-layout index of the queue-inverse extension role. -/
def walkInvIndex : ℕ := ext0 + walkInvRole

def walkInv (kind : VarKind) : Expr := .Var kind walkInvIndex

/-- Production six-column walk substitution into the direct 13-base/62-extension layout. -/
def finalWalkSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => finalWalkLine .traceCur
  | .traceCur, i + 1 => overlayCoord .traceCur i
  | .traceNext, 0 => finalWalkLine .traceNext
  | .traceNext, i + 1 => overlayCoord .traceNext i
  | .challenge, i => walkChallenge i
  | .publicVal, i => .Var .publicVal i

/-- All five non-line walk roles occupy exactly overlay coordinates `0..4`. -/
theorem walkSubst_roles (kind : VarKind)
    (hkind : kind = .traceCur ∨ kind = .traceNext) :
    walkSubst kind 1 = overlayCoord kind 0 ∧
      walkSubst kind 2 = overlayCoord kind 1 ∧
      walkSubst kind 3 = overlayCoord kind 2 ∧
      walkSubst kind 4 = overlayCoord kind 3 ∧
      walkSubst kind 5 = overlayCoord kind 4 := by
  rcases hkind with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Sum of state selectors used by `mr2` in states 2 and 5--9. -/
def mr2Group (kind : VarKind) : Expr :=
  .Add (.Var kind 2) (.Add (.Var kind 5) (.Add (.Var kind 6)
    (.Add (.Var kind 7) (.Add (.Var kind 8) (.Var kind 9)))))

/-- Selector sum for the two states carrying `mr3`. -/
def mr3Group (kind : VarKind) : Expr := .Add (.Var kind 6) (.Var kind 9)

/-- State-selected decoder for the eight source `mr2` fields. -/
def mr2Field (kind : VarKind) : ℕ → Expr
  | 0 => .Add (.Mul (.Var kind 0) (pubFP kind 0 0))
      (.Mul (mr2Group kind) (decFP kind 1 0))
  | 1 => .Add (.Mul (.Var kind 0) (pubFP kind 0 1))
      (.Mul (mr2Group kind) (decFP kind 1 1))
  | 2 => .Add (.Mul (.Var kind 0) (pubFP kind 0 2))
      (.Mul (mr2Group kind) (decFP kind 1 2))
  | 3 => .Add (.Mul (.Var kind 0) (pubFP kind 2 0))
      (.Mul (mr2Group kind) (decFP kind 2 0))
  | 4 => .Add (.Mul (.Var kind 0) (pubFP kind 2 1))
      (.Mul (mr2Group kind) (decFP kind 2 1))
  | 5 => .Add (.Mul (.Var kind 0) (pubFP kind 2 2))
      (.Mul (mr2Group kind) (decFP kind 2 2))
  | 6 => .Add (.Mul (.Var kind 0) (decFP kind 1 2))
      (.Mul (mr2Group kind) (.Const 2))
  | 7 => .Mul (.Add (.Var kind 0) (mr2Group kind))
      (.Mul (lnPrev kind) (.Pow (.Var .challenge 0) 2))
  | _ => .Const 0

/-- State-selected decoder for the eight source `mr3` fields. -/
def mr3Field (kind : VarKind) : ℕ → Expr
  | 0 => .Add (.Mul (.Var kind 6) (decFP kind 3 0))
      (.Mul (.Var kind 9) (pubFP kind 5 0))
  | 1 => .Add (.Mul (.Var kind 6) (decFP kind 3 1))
      (.Mul (.Var kind 9) (pubFP kind 5 1))
  | 2 => .Add (.Mul (.Var kind 6) (decFP kind 3 2))
      (.Mul (.Var kind 9) (pubFP kind 5 2))
  | 3 => .Add (.Mul (.Var kind 6) (decFP kind 4 0))
      (.Mul (.Var kind 9) (pubFP kind 7 0))
  | 4 => .Add (.Mul (.Var kind 6) (decFP kind 4 1))
      (.Mul (.Var kind 9) (pubFP kind 7 1))
  | 5 => .Add (.Mul (.Var kind 6) (decFP kind 4 2))
      (.Mul (.Var kind 9) (pubFP kind 7 2))
  | 6 => .Add (.Mul (.Var kind 6) (.Const 2))
      (.Mul (.Var kind 9) (decFP kind 2 2))
  | 7 => .Mul (mr3Group kind)
      (.Mul (lnPrev kind) (.Pow (.Var .challenge 0) 3))
  | _ => .Const 0

/-- Current/next substitution for the source 94-column compute layout. The first memory record is
decoder-generated; `mr2` and `mr3` use the one-hot state-selected decoder equations. -/
def computeTraceSubst (kind : VarKind) : ℕ → Expr
  | i =>
      if i < 11 then .Var kind i
      else if i < 47 then semanticPub kind ((i - 11) / 3) ((i - 11) % 3)
      else if i < 65 then decFP kind ((i - 47) / 3) ((i - 47) % 3)
      else if i = 65 then lnPrev kind
      else if i = 66 then lnCur kind
      else if i < 70 then pubFP kind 1 (i - 67)
      else if i < 73 then decFP kind 1 (i - 70)
      else if i = 73 then .Const 3
      else if i = 74 then .Mul (lnPrev kind) (.Var .challenge 0)
      else if i < 83 then mr2Field kind (i - 75)
      else if i < 91 then mr3Field kind (i - 83)
      else if i = 91 then consInv kind
      else if i = 92 then invGen kind
      else if i = 93 then .Var .challenge 5
      else .Var kind i

/-- Complete symbolic substitution. Challenges/public values remain symbolic and field-free. -/
def computeSubst : VarKind → ℕ → Expr
  | .traceCur => computeTraceSubst .traceCur
  | .traceNext => computeTraceSubst .traceNext
  | .challenge => fun i => .Var .challenge i
  | .publicVal => fun i => .Var .publicVal i

theorem final_walk_line_disjoint_table_lines :
    finalWalkSubst .traceCur 0 ≠ computeTraceSubst .traceCur 65 ∧
      finalWalkSubst .traceCur 0 ≠ computeTraceSubst .traceCur 66 ∧
      finalWalkSubst .traceNext 0 ≠ computeTraceSubst .traceNext 65 ∧
      finalWalkSubst .traceNext 0 ≠ computeTraceSubst .traceNext 66 := by
  decide

theorem final_walk_challenge_disjoint_table (i : ℕ) (hi : i < tableChallengeCount) :
    finalWalkSubst .challenge 0 ≠ computeSubst .challenge i := by
  intro h
  have heq : walkChallengeBase = i := by injection h
  norm_num [tableChallengeCount, walkChallengeBase] at hi heq
  omega

theorem final_public_namespace_partition :
    2 ≤ 20 ∧ 20 + 11 ≤ 31 ∧ 31 + 11 = 42 := by
  decide

theorem final_walk_line_disjoint_overlays (i : Fin 9) :
    finalWalkSubst .traceCur 0 ≠ overlayCoord .traceCur i ∧
      finalWalkSubst .traceNext 0 ≠ overlayCoord .traceNext i := by
  fin_cases i <;> decide

/-! ## Sampled finite-IO semantic decoder -/

def sampledGamma : Expr := .Var .challenge 6

def sampledPole : Expr := .Var .challenge 7

/-- Production sampled challenges after the dedicated walk namespace. -/
def finalSampledGamma : Expr := sampledChallenge 0
def finalSampledPole : Expr := sampledChallenge 1

def finalSampledNamespace : VarKind → ℕ → Expr
  | .challenge, 6 => finalSampledGamma
  | .challenge, 7 => finalSampledPole
  | kind, i => .Var kind i

/-! The compute request records carry the Form R `(T, C')` in place of the address and of `C' = 1`,
as in-gate expressions over existing columns and the `𝕂` coin `λ` (compute challenge `9`):
`mr₁` `(λ, λ^{n−1} + λ^{n−2})`; `mr₂` `T_slot = op₀·T + G·λ`, `C_slot = op₀·C' + G·λ^{n−1}`,
`G = op₂+op₅+op₆+op₇+op₈+op₉`; `mr₃` `op₆·λ + op₉·T`, `op₆·λ^{n−1} + op₉·C'`, with
`C' = λ^{n−1} + Σ_{j=1}^{n−1} c_j λ^{n−1−j}` (certificate bits `c_j` at columns `202 + j − 1`)
and `T` the certificate `𝕂` column (limbs `299..301`).  No new column. -/

/-- The `𝕂` coin `λ` (compute challenge `9`, raw slots `27..29`). -/
def sampledLam : Expr := .Var .challenge 9

/-- `λ^{(n−1) − d}` (`0` if `d > n − 1`): source challenge `100 + d`, lowered to
`CorrectedFinalTypedExpr.lamPow d`. -/
def lamPowVar (d : ℕ) : Expr := .Var .challenge (100 + d)

/-- Certificate bit `c_{j+1}` (column `202 + j`). -/
def certCVar (kind : VarKind) (j : ℕ) : Expr := .Var kind (202 + j)

/-- The certificate `𝕂` helper `T` (limbs `299..301`). -/
def certTVar (kind : VarKind) : Expr := .Var kind 299

/-- `C' = λ^{n−1} + Σ_{j<63} c_{j+1} λ^{n−1−(j+1)}` (terms with `j + 1 > n − 1` vanish). -/
def sampledCprime (kind : VarKind) : Expr :=
  (List.range 63).foldr
    (fun j acc => .Add (.Mul (certCVar kind j) (lamPowVar (j + 1))) acc)
    (lamPowVar 0)

/-- `G = op₂ + op₅ + op₆ + op₇ + op₈ + op₉` (states whose `mr₂` axis is `2`). -/
def sampledGSel (kind : VarKind) : Expr :=
  .Add (.Var kind 2) (.Add (.Var kind 5) (.Add (.Var kind 6)
    (.Add (.Var kind 7) (.Add (.Var kind 8) (.Var kind 9)))))

/-- Record slot `6` (`T_slot`) of the request record at source base `67`/`75`/`83`. -/
def sampledSlotT (kind : VarKind) : ℕ → Expr
  | 67 => sampledLam
  | 75 => .Add (.Mul (.Var kind 0) (certTVar kind)) (.Mul (sampledGSel kind) sampledLam)
  | 83 => .Add (.Mul (.Var kind 6) sampledLam) (.Mul (.Var kind 9) (certTVar kind))
  | _ => .Const 0

/-- Record slot `8` (`C_slot`) of the request record at source base `67`/`75`/`83`. -/
def sampledSlotC (kind : VarKind) : ℕ → Expr
  | 67 => .Add (lamPowVar 0) (lamPowVar 1)
  | 75 => .Add (.Mul (.Var kind 0) (sampledCprime kind)) (.Mul (sampledGSel kind) (lamPowVar 0))
  | 83 => .Add (.Mul (.Var kind 6) (lamPowVar 0)) (.Mul (.Var kind 9) (sampledCprime kind))
  | _ => .Const 0

def sampledSlotE (kind : VarKind) : ℕ → Expr
  | 67 => .Add (.Var kind 302) (.Const 1)
  | 75 => .Add (.Var kind 302) (.Const 2)
  | 83 => .Add (.Var kind 302) (.Const 3)
  | _ => .Const 0

/-- RLC of one reconstructed ten-scalar Form R request record (`encRecFormR _ λ` on honest
rows, with the exponent slot). -/
def sampledRecordRLC (kind : VarKind) (base : ℕ) : Expr :=
  (List.range 8).foldr
    (fun c acc =>
      .Add (.Mul (.Pow sampledGamma c)
        (if c = 6 then sampledSlotT kind base else computeTraceSubst kind (base + c))) acc)
    (.Add (.Mul (.Pow sampledGamma 8) (sampledSlotC kind base))
      (.Mul (.Pow sampledGamma 9) (sampledSlotE kind base)))

/-- Semantic sampled denominator `pole + RLC^gamma(record)` reconstructed from the co-resident
compute row.  No raw physical selector slot is interpreted as a denominator. -/
def sampledDenom (kind : VarKind) : ℕ → Expr
  | 0 => .Add sampledPole (sampledRecordRLC kind 67)
  | 1 => .Add sampledPole (sampledRecordRLC kind 75)
  | 2 => .Add sampledPole (sampledRecordRLC kind 83)
  | _ => .Const 1

/-- Active request-slot indicators derived from the one-hot opcode selector.  Slot zero is always
the formula-opening request; slot one is active exactly for record-count two or three states; slot
two is active exactly for OP6/OP9. -/
def sampledActive (kind : VarKind) : ℕ → Expr
  | 0 => .Const 1
  | 1 => .Add (.Var kind 0) (.Add (.Var kind 2) (.Add (.Var kind 5)
      (.Add (.Var kind 6) (.Add (.Var kind 7) (.Add (.Var kind 8) (.Var kind 9))))))
  | 2 => .Add (.Var kind 6) (.Var kind 9)
  | _ => .Const 0

/-- Inactive-safe sampled denominator.  An active slot uses its actual compressed record;
an inactive slot is normalized to one and therefore cannot zero the product fold. -/
def sampledSafeDenom (kind : VarKind) (j : ℕ) : Expr :=
  .Add (.Mul (sampledActive kind j) (sampledDenom kind j))
    (.Sub (.Const 1) (sampledActive kind j))

/-- Dedicated fixed inactive-safe-denominator witness in the third overlaid fingerprint. -/
def sampledDenomWitness (kind : VarKind) (j : ℕ) : Expr :=
  overlayCoord kind (6 + j)

/-- Load-bearing pin from one committed witness to the inactive-safe semantic decoder. -/
def sampledDenomPin (kind : VarKind) (j : ℕ) : Expr :=
  .Sub (sampledDenomWitness kind j) (sampledSafeDenom kind j)

/-! The deployed chip reads the Form R
record slots above (`sampledRecordRLC`). -/

def legacySampledRecordRLC (kind : VarKind) (base : ℕ) : Expr :=
  (List.range 8).foldr
    (fun c acc =>
      .Add (.Mul (.Pow sampledGamma c) (computeTraceSubst kind (base + c))) acc)
    (.Mul (.Pow sampledGamma 8) (.Const 1))

def legacySampledDenom (kind : VarKind) : ℕ → Expr
  | 0 => .Add sampledPole (legacySampledRecordRLC kind 67)
  | 1 => .Add sampledPole (legacySampledRecordRLC kind 75)
  | 2 => .Add sampledPole (legacySampledRecordRLC kind 83)
  | _ => .Const 1

def legacySampledSafeDenom (kind : VarKind) (j : ℕ) : Expr :=
  .Add (.Mul (sampledActive kind j) (legacySampledDenom kind j))
    (.Sub (.Const 1) (sampledActive kind j))

def legacySampledDenomPin (kind : VarKind) (j : ℕ) : Expr :=
  .Sub (sampledDenomWitness kind j) (legacySampledSafeDenom kind j)

/-- Sampled finite-IO source environment. The accumulator and three denominator witnesses occupy
fixed overlay coordinates; separate load-bearing pins identify each witness with the semantic
record/coin decoder. Active indicators are derived from the one-hot selector. -/
def sampledIOSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => overlayCoord .traceCur 5
  | .traceCur, 1 => sampledDenomWitness .traceCur 0
  | .traceCur, 2 => sampledDenomWitness .traceCur 1
  | .traceCur, 3 => sampledDenomWitness .traceCur 2
  | .traceCur, 4 => sampledActive .traceCur 0
  | .traceCur, 5 => sampledActive .traceCur 1
  | .traceCur, 6 => sampledActive .traceCur 2
  | .traceNext, 0 => overlayCoord .traceNext 5
  | .traceNext, 1 => sampledDenomWitness .traceNext 0
  | .traceNext, 2 => sampledDenomWitness .traceNext 1
  | .traceNext, 3 => sampledDenomWitness .traceNext 2
  | .traceNext, 4 => sampledActive .traceNext 0
  | .traceNext, 5 => sampledActive .traceNext 1
  | .traceNext, 6 => sampledActive .traceNext 2
  | .traceCur, i => .Var .traceCur i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

/-- The sampled accumulator occupies the sole remaining overlay coordinate, on both row phases. -/
theorem sampledIOSubst_acc_roles :
    sampledIOSubst .traceCur 0 = overlayCoord .traceCur 5 ∧
      sampledIOSubst .traceNext 0 = overlayCoord .traceNext 5 :=
  ⟨rfl, rfl⟩

/-- All six non-accumulator roles use dedicated denominator witnesses or semantic active
decoders, never physical selector columns masquerading as denominators. -/
theorem sampledIOSubst_semantic_roles (kind : VarKind)
    (hkind : kind = .traceCur ∨ kind = .traceNext) :
    sampledIOSubst kind 1 = sampledDenomWitness kind 0 ∧
      sampledIOSubst kind 2 = sampledDenomWitness kind 1 ∧
      sampledIOSubst kind 3 = sampledDenomWitness kind 2 ∧
      sampledIOSubst kind 4 = sampledActive kind 0 ∧
      sampledIOSubst kind 5 = sampledActive kind 1 ∧
      sampledIOSubst kind 6 = sampledActive kind 2 := by
  rcases hkind with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem final_semantic_challenge_indices :
    computeSubst .challenge 0 = .Var .challenge 0 ∧
      computeSubst .challenge 5 = .Var .challenge 5 ∧
      finalWalkSubst .challenge 0 = .Var .challenge 6 ∧
      finalSampledGamma = .Var .challenge 7 ∧
      finalSampledPole = .Var .challenge 8 := by
  decide

theorem final_walk_challenge_disjoint_sampled :
    finalWalkSubst .challenge 0 ≠ finalSampledGamma ∧
      finalWalkSubst .challenge 0 ≠ finalSampledPole ∧
      finalSampledGamma ≠ finalSampledPole := by
  decide

theorem final_walk_line_disjoint_sampledIO (i : Fin 7) :
    finalWalkSubst .traceCur 0 ≠ sampledIOSubst .traceCur i ∧
      finalWalkSubst .traceNext 0 ≠ sampledIOSubst .traceNext i := by
  fin_cases i <;> decide

/-- Vanishing denominator pins are exactly equality with all three inactive-safe decoders. -/
theorem sampledDenomPins_eval_iff {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) :
    (∀ j : Fin 3, (sampledDenomPin kind j).eval env = 0) ↔
      ∀ j : Fin 3,
        (sampledDenomWitness kind j).eval env = (sampledSafeDenom kind j).eval env := by
  constructor <;> intro h j
  · simpa [sampledDenomPin, Expr.eval] using sub_eq_zero.mp (h j)
  · simpa [sampledDenomPin, Expr.eval, sub_eq_zero] using h j

/-- Read one variable kind uniformly from an environment. -/
def envValue {K : Type*} (env : Env K) : VarKind → ℕ → K
  | .traceCur => env.trace
  | .traceNext => env.traceNext
  | .challenge => env.chal
  | .publicVal => env.pub

/-- A claimed inactive-safe denominator different from its semantic decoder cannot be replayed as
the induced sampled-IO source column. -/
theorem malformed_sampledDenom_rejected {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (hpins : ∀ j : Fin 3, (sampledDenomPin kind j).eval env = 0)
    (j : Fin 3) (bad : K)
    (hbad : bad ≠ (sampledSafeDenom kind j).eval env) :
    envValue (Env.ofSubst sampledIOSubst env) kind (1 + j) ≠ bad := by
  have hpin := (sampledDenomPins_eval_iff env kind).1 hpins j
  rcases hkind with rfl | rfl <;> fin_cases j <;>
    simp only [envValue, Env.ofSubst, sampledIOSubst]
  all_goals
    intro h
    apply hbad
    rw [← hpin]
    exact h.symm

/-- Likewise an active-slot value cannot be supplied independently of the one-hot state decoder. -/
theorem malformed_sampledActive_rejected {K : Type*} [Field K]
    (env : Env K) (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (j : Fin 3) (bad : K)
    (hbad : bad ≠ (sampledActive kind j).eval env) :
    envValue (Env.ofSubst sampledIOSubst env) kind (4 + j) ≠ bad := by
  rcases hkind with rfl | rfl <;> fin_cases j <;>
    simpa [envValue, Env.ofSubst, sampledIOSubst] using hbad.symm

/- Exact one-hot state selectors force every derived request mask to be boolean.  Because
`sampledActive` is defined from the state/request-count partition, this also ties the masks to the
row's opcode rather than accepting independent witness values. -/
set_option linter.unusedSimpArgs false in
theorem sampledActive_boolean_of_oneHot {K : Type*} [Field K] (env : Env K)
    (kind : VarKind) (hkind : kind = .traceCur ∨ kind = .traceNext)
    (active : State)
    (hsel : ∀ st, envValue env kind (Nock.Reified.opCol st) =
      if st = active then 1 else 0)
    (j : Fin 3) :
    (sampledActive kind j).eval env = 0 ∨
      (sampledActive kind j).eval env = 1 := by
  rcases hkind with rfl | rfl
  · have h0 := hsel .s0; have h1 := hsel .s1; have h2 := hsel .s2
    have h3 := hsel .s3; have h4 := hsel .s4; have h5 := hsel .s5
    have h6 := hsel .s6; have h7 := hsel .s7; have h8 := hsel .s8
    have h9 := hsel .s9; have hc := hsel .cons
    fin_cases active <;> fin_cases j <;>
      simp [envValue, Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
      simp [sampledActive, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]
  · have h0 := hsel .s0; have h1 := hsel .s1; have h2 := hsel .s2
    have h3 := hsel .s3; have h4 := hsel .s4; have h5 := hsel .s5
    have h6 := hsel .s6; have h7 := hsel .s7; have h8 := hsel .s8
    have h9 := hsel .s9; have hc := hsel .cons
    fin_cases active <;> fin_cases j <;>
      simp [envValue, Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
      simp [sampledActive, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

/-- Walk multiplier and sampled accumulator are different
overlay coordinates in both row phases. -/
theorem walkMultiplier_ne_sampledAcc :
    walkSubst .traceCur 5 ≠ sampledIOSubst .traceCur 0 ∧
      walkSubst .traceNext 5 ≠ sampledIOSubst .traceNext 0 := by
  constructor
  · intro h
    have h' := congrArg (fun e => e.eval ({
      trace := fun i => if i = 1 then 1 else if i = 23 then 1 else 0
      traceNext := fun _ => 0
      chal := fun _ => 0
      pub := fun _ => 0 } : Env ℚ)) h
    norm_num [walkSubst, sampledIOSubst, overlayCoord, Nock.Reified.allStates,
      overlayBNat, pubFP, ext0, Nock.Reified.opCol, Expr.eval] at h'
  · intro h
    have h' := congrArg (fun e => e.eval ({
      trace := fun _ => 0
      traceNext := fun i => if i = 1 then 1 else if i = 23 then 1 else 0
      chal := fun _ => 0
      pub := fun _ => 0 } : Env ℚ)) h
    norm_num [walkSubst, sampledIOSubst, overlayCoord, Nock.Reified.allStates,
      overlayBNat, pubFP, ext0, Nock.Reified.opCol, Expr.eval] at h'

@[simp] theorem subst_tc67 :
    Expr.subst computeSubst (tc 67) = pubFP .traceCur 1 0 := by
  change computeTraceSubst .traceCur 67 = _
  norm_num [computeTraceSubst, pubFP, ext0]
@[simp] theorem subst_tc68 :
    Expr.subst computeSubst (tc 68) = pubFP .traceCur 1 1 := by
  change computeTraceSubst .traceCur 68 = _
  norm_num [computeTraceSubst, pubFP, ext0]
@[simp] theorem subst_tc69 :
    Expr.subst computeSubst (tc 69) = pubFP .traceCur 1 2 := by
  change computeTraceSubst .traceCur 69 = _
  norm_num [computeTraceSubst, pubFP, ext0]
@[simp] theorem subst_tc70 :
    Expr.subst computeSubst (tc 70) = decFP .traceCur 1 0 := by
  change computeTraceSubst .traceCur 70 = _
  norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc71 :
    Expr.subst computeSubst (tc 71) = decFP .traceCur 1 1 := by
  change computeTraceSubst .traceCur 71 = _
  norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc72 :
    Expr.subst computeSubst (tc 72) = decFP .traceCur 1 2 := by
  change computeTraceSubst .traceCur 72 = _
  norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc73 :
    Expr.subst computeSubst (tc 73) = .Const 3 := by
  change computeTraceSubst .traceCur 73 = _
  norm_num [computeTraceSubst]
@[simp] theorem subst_tc74 :
    Expr.subst computeSubst (tc 74) =
      .Mul (lnPrev .traceCur) (.Var .challenge 0) := by
  change computeTraceSubst .traceCur 74 = _
  norm_num [computeTraceSubst]

@[simp] theorem subst_tc14 : Expr.subst computeSubst (tc 14) = pubFP .traceCur 1 0 := by
  change computeTraceSubst .traceCur 14 = _; norm_num [computeTraceSubst, semanticPub, pubFP, ext0]
@[simp] theorem subst_tc15 : Expr.subst computeSubst (tc 15) = pubFP .traceCur 1 1 := by
  change computeTraceSubst .traceCur 15 = _; norm_num [computeTraceSubst, semanticPub, pubFP, ext0]
@[simp] theorem subst_tc16 : Expr.subst computeSubst (tc 16) = pubFP .traceCur 1 2 := by
  change computeTraceSubst .traceCur 16 = _; norm_num [computeTraceSubst, semanticPub, pubFP, ext0]
@[simp] theorem subst_tc50 : Expr.subst computeSubst (tc 50) = decFP .traceCur 1 0 := by
  change computeTraceSubst .traceCur 50 = _; norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc51 : Expr.subst computeSubst (tc 51) = decFP .traceCur 1 1 := by
  change computeTraceSubst .traceCur 51 = _; norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc52 : Expr.subst computeSubst (tc 52) = decFP .traceCur 1 2 := by
  change computeTraceSubst .traceCur 52 = _; norm_num [computeTraceSubst, decFP, ext0]
@[simp] theorem subst_tc65 : Expr.subst computeSubst (tc 65) = lnPrev .traceCur := by
  change computeTraceSubst .traceCur 65 = _; norm_num [computeTraceSubst, lnPrev, ext0]
@[simp] theorem subst_chl0 : Expr.subst computeSubst (chl 0) = chl 0 := rfl

/-- Every source expression evaluates under substitution exactly in the decoder-induced source
environment. -/
theorem eval_computeSubst {K : Type*} [Field K] (e : Expr) (env : Env K) :
    (e.subst computeSubst).eval env =
      e.eval (Env.ofSubst computeSubst env) :=
  Expr.eval_subst computeSubst e env

/-- Blockwise evaluation commutation, used for SV/formula/memory/per-state lists. -/
theorem eval_computeSubst_block {K : Type*} [Field K]
    (block : List Expr) (env : Env K) :
    (∀ e ∈ block, (e.subst computeSubst).eval env = 0) ↔
      (∀ e ∈ block, e.eval (Env.ofSubst computeSubst env) = 0) := by
  constructor <;> intro h e he
  · rw [← eval_computeSubst]
    exact h e he
  · rw [eval_computeSubst]
    exact h e he

/-- The reconstructed first-record block becomes definitionally true after substitution: those
eight source columns are not committed physical degrees of freedom. Therefore they must not be
inserted as inert members of the future 21-gate list. -/
theorem mr1Exprs_subst_vanish {K : Type*} [Field K] (env : Env K) :
    ∀ e ∈ Nock.Reified.mr1Exprs,
      (e.subst computeSubst).eval env = 0 := by
  intro e he
  simp [Nock.Reified.mr1Exprs, Nock.Reified.memEqC,
    Nock.Reified.fpEqC] at he
  rcases he with h | h | h | h | h | h | h | h <;> subst e <;>
    simp [Expr.subst, Expr.eval, computeSubst, pubFP, decFP, lnPrev, ext0,
      Nock.Reified.cMr1, Nock.Reified.mr1Target, Nock.Reified.cF, Nock.Reified.cFt,
      Nock.Reified.mrCol, Nock.Reified.chl,
      Nock.Reified.fpCol]

/-- The direct SV block commutes through substitution. -/
theorem svExprs_subst_iff {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ Nock.Reified.svExprs, (e.subst computeSubst).eval env = 0) ↔
      (∀ e ∈ Nock.Reified.svExprs,
        e.eval (Env.ofSubst computeSubst env) = 0) :=
  eval_computeSubst_block _ _

/-- The direct formula block commutes through substitution. -/
theorem formulaExprs_subst_iff {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ Nock.Reified.formulaExprs, (e.subst computeSubst).eval env = 0) ↔
      (∀ e ∈ Nock.Reified.formulaExprs,
        e.eval (Env.ofSubst computeSubst env) = 0) :=
  eval_computeSubst_block _ _

/-- Every gated memory/evaluation source constraint commutes through the decoder substitution. -/
theorem perStateGated_subst_iff {K : Type*} [Field K] (env : Env K) :
    (∀ e ∈ Nock.Reified.perStateGated, (e.subst computeSubst).eval env = 0) ↔
      (∀ e ∈ Nock.Reified.perStateGated,
        e.eval (Env.ofSubst computeSubst env) = 0) :=
  eval_computeSubst_block _ _

/-- The former OP3/OP5 degree-five bodies now read the fixed stored `e` role directly. -/
def op3ELeafBool : Expr :=
  Nock.Reified.gateBy .s3
    (.Mul Nock.Reified.cE.leaf (.Sub (.Const 1) Nock.Reified.cE.leaf))

def op5ELeafBool : Expr :=
  Nock.Reified.gateBy .s5
    (.Mul Nock.Reified.cE.leaf (.Sub (.Const 1) Nock.Reified.cE.leaf))

set_option maxRecDepth 10000 in
theorem fixed_overlay_leaf_booleanity_degrees :
    Nock.Reified.perStateGated.get ⟨177, by decide⟩ = op3ELeafBool ∧
      Nock.Reified.perStateGated.get ⟨270, by decide⟩ = op5ELeafBool ∧
      (op3ELeafBool.subst computeSubst).degree = 5 ∧
      (op5ELeafBool.subst computeSubst).degree = 5 := by
  exact ⟨rfl, rfl, by decide, by decide⟩

/-- Direct fixed-role refolds of the two selector-gated output-bit booleanity bodies. -/
def op3ELeafBoolRefold : Expr :=
  .Mul (.Var .traceCur 3)
    (.Mul (pubFP .traceCur 2 2) (.Sub (.Const 1) (pubFP .traceCur 2 2)))

def op5ELeafBoolRefold : Expr :=
  .Mul (.Var .traceCur 5)
    (.Mul (pubFP .traceCur 2 2) (.Sub (.Const 1) (pubFP .traceCur 2 2)))

theorem leaf_booleanity_refold_degrees :
    op3ELeafBoolRefold.degree = 3 ∧ op5ELeafBoolRefold.degree = 3 := by
  decide

set_option linter.unusedSimpArgs false in
theorem op3ELeafBool_refold_eval {K : Type*} [Field K] (env : Env K)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = .s3 then 1 else 0) :
    (op3ELeafBool.subst computeSubst).eval env =
      op3ELeafBoolRefold.eval env := by
  have h0 := hsel .s0; have h1 := hsel .s1; have h2 := hsel .s2
  have h3 := hsel .s3; have h4 := hsel .s4; have h5 := hsel .s5
  have h6 := hsel .s6; have h7 := hsel .s7; have h8 := hsel .s8
  have h9 := hsel .s9; have hc := hsel .cons
  simp [Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc
  simp [op3ELeafBool, op3ELeafBoolRefold, Nock.Reified.gateBy,
    Nock.Reified.cE, Nock.Reified.fpCol, computeSubst, computeTraceSubst,
    semanticPub, restoredPub, Nock.Reified.allStates, sourcePubAt,
    restoredAField, restoredBField, restoredIOHostField, restoredDenomHostField,
    overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Nock.Reified.tc,
    Expr.subst, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

set_option linter.unusedSimpArgs false in
theorem op5ELeafBool_refold_eval {K : Type*} [Field K] (env : Env K)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = .s5 then 1 else 0) :
    (op5ELeafBool.subst computeSubst).eval env =
      op5ELeafBoolRefold.eval env := by
  have h0 := hsel .s0; have h1 := hsel .s1; have h2 := hsel .s2
  have h3 := hsel .s3; have h4 := hsel .s4; have h5 := hsel .s5
  have h6 := hsel .s6; have h7 := hsel .s7; have h8 := hsel .s8
  have h9 := hsel .s9; have hc := hsel .cons
  simp [Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc
  simp [op5ELeafBool, op5ELeafBoolRefold, Nock.Reified.gateBy,
    Nock.Reified.cE, Nock.Reified.fpCol, computeSubst, computeTraceSubst,
    semanticPub, restoredPub, Nock.Reified.allStates, sourcePubAt,
    restoredAField, restoredBField, restoredIOHostField, restoredDenomHostField,
    overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Nock.Reified.tc,
    Expr.subst, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

/- The OP3 refold is not restricted to an OP3 row: it agrees with the source gate on every
exactly-one-hot compute row.  On non-OP3 rows both sides vanish; on an OP3 row the overlay decoder
restores the fixed `e` role. -/
set_option linter.unusedSimpArgs false in
theorem op3ELeafBool_refold_eval_oneHot {K : Type*} [Field K] (env : Env K)
    (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0) :
    (op3ELeafBool.subst computeSubst).eval env =
      op3ELeafBoolRefold.eval env := by
  fin_cases active <;>
    have h0 := hsel .s0 <;> have h1 := hsel .s1 <;> have h2 := hsel .s2 <;>
    have h3 := hsel .s3 <;> have h4 := hsel .s4 <;> have h5 := hsel .s5 <;>
    have h6 := hsel .s6 <;> have h7 := hsel .s7 <;> have h8 := hsel .s8 <;>
    have h9 := hsel .s9 <;> have hc := hsel .cons <;>
    simp [Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
    simp [op3ELeafBool, op3ELeafBoolRefold, Nock.Reified.gateBy,
      Nock.Reified.cE, Nock.Reified.fpCol, computeSubst, computeTraceSubst,
      semanticPub, restoredPub, Nock.Reified.allStates, sourcePubAt,
      restoredAField, restoredBField, restoredIOHostField, restoredDenomHostField,
      overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Nock.Reified.tc,
      Expr.subst, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

/- The OP5 refold likewise agrees with the source gate on every exactly-one-hot compute row. -/
set_option linter.unusedSimpArgs false in
theorem op5ELeafBool_refold_eval_oneHot {K : Type*} [Field K] (env : Env K)
    (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0) :
    (op5ELeafBool.subst computeSubst).eval env =
      op5ELeafBoolRefold.eval env := by
  fin_cases active <;>
    have h0 := hsel .s0 <;> have h1 := hsel .s1 <;> have h2 := hsel .s2 <;>
    have h3 := hsel .s3 <;> have h4 := hsel .s4 <;> have h5 := hsel .s5 <;>
    have h6 := hsel .s6 <;> have h7 := hsel .s7 <;> have h8 := hsel .s8 <;>
    have h9 := hsel .s9 <;> have hc := hsel .cons <;>
    simp [Nock.Reified.opCol] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
    simp [op5ELeafBool, op5ELeafBoolRefold, Nock.Reified.gateBy,
      Nock.Reified.cE, Nock.Reified.fpCol, computeSubst, computeTraceSubst,
      semanticPub, restoredPub, Nock.Reified.allStates, sourcePubAt,
      restoredAField, restoredBField, restoredIOHostField, restoredDenomHostField,
      overlayANat, overlayBNat, pubFP, ext0, Nock.Reified.opCol, Nock.Reified.tc,
      Expr.subst, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

/-- Production per-state list with exactly the two degree-five bodies replaced by their direct
fixed-role refolds. -/
def refoldedPerStateGates : List Expr :=
  ((Nock.Reified.perStateGated.map (fun e => e.subst computeSubst)).set
    177 op3ELeafBoolRefold).set 270 op5ELeafBoolRefold

theorem refoldedPerStateGates_length :
    refoldedPerStateGates.length = Nock.Reified.perStateGated.length := by
  simp [refoldedPerStateGates]

set_option maxRecDepth 10000 in
theorem refoldedPerStateGates_max_degree :
    (refoldedPerStateGates.map Expr.degree).foldr Nat.max 0 = 4 := by
  decide

/-- The compute log-nonce cross-row gate commutes through the decoder substitution. -/
theorem lnChain_subst_eval {K : Type*} [Field K] (env : Env K) :
    (Expr.subst computeSubst Nock.Reified.Trans.lnChainExpr).eval env =
      Expr.eval Nock.Reified.Trans.lnChainExpr (Env.ofSubst computeSubst env) :=
  Expr.eval_subst computeSubst _ _

/-- All walk gates commute through the state-selected overlay substitution. -/
theorem walk_block_subst_iff {K : Type*} [Field K] (block : List Expr) (env : Env K) :
    (∀ e ∈ block, (e.subst walkSubst).eval env = 0) ↔
      (∀ e ∈ block, e.eval (Env.ofSubst walkSubst env) = 0) := by
  constructor <;> intro h e he
  · rw [← Expr.eval_subst]
    exact h e he
  · rw [Expr.eval_subst]
    exact h e he

/-- Every sampled finite-IO source block commutes through its overlay-accumulator substitution. -/
theorem sampledIO_block_subst_iff {K : Type*} [Field K] (block : List Expr) (env : Env K) :
    (∀ e ∈ block, (e.subst sampledIOSubst).eval env = 0) ↔
      (∀ e ∈ block, e.eval (Env.ofSubst sampledIOSubst env) = 0) := by
  constructor <;> intro h e he
  · rw [← Expr.eval_subst]
    exact h e he
  · rw [Expr.eval_subst]
    exact h e he

/-- Dynamic walk projections cost one selector multiplication; fixed IO projections are linear. -/
theorem overlayCoord_degree (kind : VarKind) (coord : ℕ) :
    (overlayCoord kind coord).degree ≤ 2 := by
  by_cases h3 : coord < 3
  · cases kind <;> simp [overlayCoord, h3, Nock.Reified.allStates,
      overlayANat, pubFP, Nock.Reified.opCol, Expr.degree]
  by_cases h5 : coord < 5
  · cases kind <;> simp [overlayCoord, h3, h5, Nock.Reified.allStates,
      overlayBNat, pubFP, Nock.Reified.opCol, Expr.degree]
  by_cases heq : coord = 5 <;>
    cases kind <;> simp [overlayCoord, h3, h5, heq, pubFP, Expr.degree]

theorem walkSubst_degree : Expr.SubstDegreeLE walkSubst 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | zero => simp [walkSubst, lnCur, Expr.degree]
    | succ i => simpa [walkSubst] using overlayCoord_degree .traceCur i
  · intro i
    cases i with
    | zero => simp [walkSubst, lnCur, Expr.degree]
    | succ i => simpa [walkSubst] using overlayCoord_degree .traceNext i
  · intro i; rfl
  · intro i; rfl

set_option linter.unusedSimpArgs false in
theorem sampledIOSubst_degree : Expr.SubstDegreeLE sampledIOSubst 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h0 : i = 0
    · subst i; decide
    by_cases h1 : i = 1
    · subst i; decide
    by_cases h2 : i = 2
    · subst i; decide
    by_cases h3 : i = 3
    · subst i; decide
    by_cases h4 : i = 4
    · subst i; decide
    by_cases h5 : i = 5
    · subst i; decide
    by_cases h6 : i = 6
    · subst i; decide
    simp [sampledIOSubst, h0, h1, h2, h3, h4, h5, h6, Expr.degree]
  · intro i
    by_cases h0 : i = 0
    · subst i; decide
    by_cases h1 : i = 1
    · subst i; decide
    by_cases h2 : i = 2
    · subst i; decide
    by_cases h3 : i = 3
    · subst i; decide
    by_cases h4 : i = 4
    · subst i; decide
    by_cases h5 : i = 5
    · subst i; decide
    by_cases h6 : i = 6
    · subst i; decide
    simp [sampledIOSubst, h0, h1, h2, h3, h4, h5, h6, Expr.degree]
  · intro i; rfl
  · intro i; rfl

/-- Late-role restoration costs at most one selector multiplication. -/
theorem semanticPub_degree (kind : VarKind) (role coord : ℕ) :
    (semanticPub kind role coord).degree ≤ 2 := by
  have hrest : (restoredPub kind role coord).degree ≤ 2 := by
    cases kind <;>
      simp [restoredPub, Nock.Reified.allStates, sourcePubAt, restoredAField,
        restoredBField, restoredIOHostField, restoredDenomHostField,
        overlayANat, overlayBNat, pubFP, decFP, Nock.Reified.opCol, Expr.degree] <;>
      repeat' first | split | simp_all [Expr.degree]
  by_cases h :
      role = 2 ∨ role = 3 ∨ role = 4 ∨ role = 6 ∨ role = 7 ∨
        role = 9 ∨ role = 10 ∨ role = 11
  · simpa [semanticPub, h] using hrest
  · cases kind <;> simp [semanticPub, h, pubFP, Expr.degree]

/- The substitution is degree one on stored/reconstructed trace fields and degree zero on
challenges/public values. -/
set_option linter.unusedSimpArgs false in
theorem computeSubst_degree : Expr.SubstDegreeLE computeSubst 2 := by
  have htrace : ∀ (k : VarKind) (i : ℕ), (computeTraceSubst k i).degree ≤ 2 := by
    intro k i
    by_cases h0 : i < 11
    · cases k <;> simp [computeTraceSubst, h0, Expr.degree]
    by_cases h1 : i < 47
    · simpa [computeTraceSubst, h0, h1] using
        semanticPub_degree k ((i - 11) / 3) ((i - 11) % 3)
    by_cases h2 : i < 65
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, decFP, Expr.degree]
    by_cases h3 : i = 65
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, lnPrev, Expr.degree]
    by_cases h4 : i = 66
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, lnCur, Expr.degree]
    by_cases h5 : i < 70
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, pubFP, Expr.degree]
    by_cases h6 : i < 73
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, decFP, Expr.degree]
    by_cases h7 : i = 73
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, Expr.degree]
    by_cases h8 : i = 74
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, h8, lnPrev,
        Expr.degree]
    by_cases h9a : i < 83
    · interval_cases i <;> cases k <;>
        norm_num [computeTraceSubst, mr2Field, mr2Group, pubFP, decFP, lnPrev, Expr.degree,
          Expr.powDegree]
    by_cases h9 : i < 91
    · interval_cases i <;> cases k <;>
        norm_num [computeTraceSubst, mr3Field, mr3Group, pubFP, decFP, lnPrev, Expr.degree,
          Expr.powDegree]
    by_cases h10 : i = 91
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9a, h9, h10,
        consInv, Expr.degree]
    by_cases h11 : i = 92
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9a, h9, h10,
        h11, invGen, Expr.degree]
    by_cases h12 : i = 93
    · cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h9a, h10, h11, h12, Expr.degree]
    cases k <;> simp [computeTraceSubst, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h9a, h11, h12, Expr.degree]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact htrace .traceCur
  · exact htrace .traceNext
  · intro i; rfl
  · intro i; rfl

/-- Individual blocks are subsequently refolded to remain at degree four. -/
theorem degree_computeSubst_le (e : Expr) :
    (e.subst computeSubst).degree ≤ e.degree * 2 :=
  Expr.degree_subst_le computeSubst 2 computeSubst_degree e

#print axioms eval_computeSubst
#print axioms eval_computeSubst_block
#print axioms mr1Exprs_subst_vanish
#print axioms svExprs_subst_iff
#print axioms formulaExprs_subst_iff
#print axioms walkSubst_roles
#print axioms sampledIOSubst_acc_roles
#print axioms sampledIOSubst_semantic_roles
#print axioms malformed_sampledDenom_rejected
#print axioms malformed_sampledActive_rejected
#print axioms sampledActive_boolean_of_oneHot
#print axioms walkMultiplier_ne_sampledAcc
#print axioms perStateGated_subst_iff
#print axioms fixed_overlay_leaf_booleanity_degrees
#print axioms op3ELeafBool_refold_eval
#print axioms op5ELeafBool_refold_eval
#print axioms op3ELeafBool_refold_eval_oneHot
#print axioms op5ELeafBool_refold_eval_oneHot
#print axioms refoldedPerStateGates_max_degree
#print axioms lnChain_subst_eval
#print axioms walk_block_subst_iff
#print axioms sampledIO_block_subst_iff
#print axioms walkSubst_degree
#print axioms sampledIOSubst_degree
#print axioms degree_computeSubst_le

end OptimizedComputeSubstitution
end Nock.NockVMROM.Thm54
