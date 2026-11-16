import Nock.NockVMROM.Thm54.ExprReindex
import Nock.NockVMROM.Thm54.OptimizedComputeOverlay

/-!
# Obstruction to a pure `ExprReindex` map for the normalized compute codec

The normalized 13/58 codec deliberately erases the three committed memory records and reconstructs
them from `Inputs` during decode.  In particular, changing only
`pub.mr1.ts` does not change the physical row.

`Expr.mapVars` can only rename a source trace variable to one target trace variable.  Its
environment is a deterministic function of the physical row, so it cannot recover an erased
source variable whose value is supplied only by the external `Inputs`.  The theorem below compiles
this obstruction for source compute column 74, `pub.mr1.ts`.

This does not obstruct an optimized chip in principle: a substitution reifier may replace the
source expression `mr1.ts` by `ln_prev * alpha`.  It does contradict the requested implementation
route “reindex the existing `mr1Exprs` with `ExprReindex` and prove evaluation commutes” on the
current record-free codec.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeReindexObstruction

open Nock
open Nock.ComputeTable
open Nock.Reified

noncomputable section

variable {F K : Type*} [Field F] [Field K]

/-- Change only the source row's first-record timestamp. -/
def withMr1Timestamp (pub : Pub K) (timestamp : K) : Pub K :=
  { pub with mr1 := { pub.mr1 with ts := timestamp } }

omit [Field K] in
/-- The record-free 13/58 physical encoding erases `mr1.ts`. -/
theorem encode_withMr1Timestamp_eq
    (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OptimizedComputeOverlay.OverlayValues K) (t₀ t₁ : K) :
    OptimizedComputeOverlay.encode (F := F)
        (withMr1Timestamp pub t₀) dec ex v =
      OptimizedComputeOverlay.encode (F := F)
        (withMr1Timestamp pub t₁) dec ex v := by
  cases pub
  rfl

omit [Field K] in
@[simp] theorem withMr1Timestamp_ts (pub : Pub K) (timestamp : K) :
    (withMr1Timestamp pub timestamp).mr1.ts = timestamp :=
  rfl

/-- No deterministic function of the physical 13/58 row can recover the erased source
`mr1.ts` on all source rows. -/
theorem no_input_free_mr1Timestamp_decoder
    (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OptimizedComputeOverlay.OverlayValues K) :
    ¬ ∃ read : OptimizedComputeCodec.Row F K → K,
      ∀ source : Pub K,
        read (OptimizedComputeOverlay.encode (F := F) source dec ex v) =
          source.mr1.ts := by
  rintro ⟨read, hread⟩
  have hrow := encode_withMr1Timestamp_eq (F := F) pub dec ex v (0 : K) (1 : K)
  have h0 := hread (withMr1Timestamp pub 0)
  have h1 := hread (withMr1Timestamp pub 1)
  have hz : (0 : K) = 1 := by
    calc
      (0 : K) = read (OptimizedComputeOverlay.encode (F := F)
          (withMr1Timestamp pub 0) dec ex v) := h0.symm
      _ = read (OptimizedComputeOverlay.encode (F := F)
          (withMr1Timestamp pub 1) dec ex v) := congrArg read hrow
      _ = 1 := h1
  exact zero_ne_one hz

/-- A proposed pure `ExprReindex` implementation of source trace column 74. `rowEnv` may choose any
layout of the 13 base and 58 extension values, but it may depend only on the physical row. -/
structure Mr1TimestampExprReindex
    (dec : Dec K) (ex : Extra K)
    (v : OptimizedComputeOverlay.OverlayValues K) where
  rename : VarKind → ℕ → ℕ
  rowEnv : OptimizedComputeCodec.Row F K → Env K
  commutes :
    ∀ source : Pub K,
      ((tc 74).mapVars rename).eval
          (rowEnv (OptimizedComputeOverlay.encode (F := F) source dec ex v)) =
        source.mr1.ts

/-- **Compiled obstruction.** No pure variable-renaming map can make source column 74 commute with
the current record-free codec. This is stronger than failure of one provisional 94→58 index
assignment: `rename` and the physical-row environment are arbitrary. -/
theorem no_mr1Timestamp_exprReindex
    (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (v : OptimizedComputeOverlay.OverlayValues K) :
    IsEmpty (Mr1TimestampExprReindex (F := F) dec ex v) := by
  constructor
  intro R
  apply no_input_free_mr1Timestamp_decoder (F := F) pub dec ex v
  refine ⟨fun row => ((tc 74).mapVars R.rename).eval (R.rowEnv row), ?_⟩
  exact R.commutes

/-- `Expr.mapVars` exposes why: a trace variable remains a single trace projection after
reindexing; it is never replaced by a composite expression such as `ln_prev * alpha`. -/
theorem mapVars_mr1Timestamp_is_projection
    (rename : VarKind → ℕ → ℕ) (env : Env K) :
    ((tc 74).mapVars rename).eval env =
      env.trace (rename .traceCur 74) :=
  rfl

#print axioms encode_withMr1Timestamp_eq
#print axioms no_input_free_mr1Timestamp_decoder
#print axioms no_mr1Timestamp_exprReindex
#print axioms mapVars_mr1Timestamp_is_projection

end
end OptimizedComputeReindexObstruction
end Nock.NockVMROM.Thm54
