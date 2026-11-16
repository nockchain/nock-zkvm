/-
  Lane values in ℕ: `laneL` (the 32-bit limb `Σ 2^t b_t`), `laneO`
    (the high half `Σ 2^t b_{16+t}`), `laneBits` (the 32 packed `Q` carries).
  * §2 **The fuel-bounded atom walk** `atomLimbs` over the atom table's `idx/idR/wR/aL/aR` (positional, as
    `decodeB0`; the `Denotes` comb: `wR` steps to `idR`, `¬wR` ends with `[aL, aR]`), fuel `nA` = the table
    length; `atomPoly t v` is the limb polynomial of the walk from serial `v`, **`0` when the fuel runs out**
    (or the serial is out of range), so the event is well-defined on hostile (cyclic) tables.
  * §3 **The polynomial mirror of the chip's round-1 identity columns** (`identQ`, chip §3): Horner `hornerP`
    (the `H`/`HO` gates of `mS mV mW mQM` slots), packed `hpackP` (the `mQ1` gate, `y^32` per row), `Lp`
    (`qVal`: atom read on `mR mV`, `(Y − B)·H` on Q blocks, `H` on `mS mW`), the factor value `Lf`, the
    latches `RLp`/`ROp` (`qLatch`), the contributions `D1p`/`D2p` (`qContr`) and the block sums `blockSum`
    (`qSum`: `Σ_{rows of the block} D = 0`), the view links `linkP` (`H − A` on `mV` first rows).  Per call
    (`hdr` row `h`): `callPolys h = [Σ D1, Σ D2] ++ links`; **`arithPolys = hdrs.flatMap callPolys`**.  All are
    functions of ROUND-0 data only (base columns, atom limbs); `y` enters only as the evaluation point.
  * §4 Degrees: every call polynomial has `natDegree ≤ 2·nA + 32·nAL + 2` (`callPolys_natDegree_le`).
  * §5 **Bad sets and cards.**
    - `arithBad` (the literal form): `⋃_{P ∈ arithPolys} roots_{𝕂′}(P)` (zero polys have no roots),
      `arithBad_card_le`: `≤ calls·(nAL + 2)·(2·nA + 32·nAL + 2)`.
    - `arithBadC` (per call): `⋃_{calls} {y | every call polynomial vanishes at y}`, nonempty
      only when some call polynomial is nonzero; `arithBadC_card_le`: `≤ calls·(2·nA + 32·nAL + 2)`.
  * §6 Summands on `frameJ8` coins `{17, 18}` (`y`) via `towerSeedSummand` (`P8Core/VclL/DyckRoot.lean`):
    `arithSZ` (per call, weight `C·(2A + 32·AL + 2) ≤ C·(3A + 32·AL + 2)`, `arithSZ_weight_le`) and `arithSZP`
    (per polynomial, weight `C·(AL + 2)·(2A + 32·AL + 2)`); `hconst` = constancy of the two round-0 readouts.
    `outside_arithSZ`: outside the event, for every call, **if every call polynomial vanishes at `y` then
    every call polynomial is `0`**; `outside_arithSZP`: `∀ P ∈ arithPolys, aeval y P = 0 → P = 0`.
  * §7 The concrete ALU readout `aluRowsOf` from a column family (`natOf` of the base columns at the row
    nodes, as `rowsB0`), with `aluRowsOf_congr` and `aluRowsOf_const` (base columns of round 0 ⇒ coin-free).

  ## Deviation from the naive weight bound
  The target weight bound is `W ≤ calls·(3·r.A + 32·AL + 2)`.  For the per-polynomial union the bound is FALSE in
  general (by a hand argument, not formalised here): one call's polynomials (the main identity, of degree up to `2A`, the second
  identity and the view links, `A` each) can have disjoint root sets, total `≈ 5A` (more with hostile blocks
  carrying many `mV` slots), which exceeds `3A + 32·AL + 2` once `A ≫ AL`.  The per-call common-root event
  `arithBadC` has card `≤` ONE nonzero polynomial's degree, so it meets `C·(2A + 32·AL + 2)` (tighter than
  the target bound).  Its outside statement is per call ("all of a call's identities vanish at `y` ⇒ all are zero"),
  which is what the soundness proof consumes (the gates of one call block make every identity of that call vanish
  at `y`).  Both summands are built; `arithSZ` is the per-call one.  Not proved in this module (both are part of the
  J-9 AL soundness proof in `J9AL/`): that the mirror is faithful under the gates, and that the chip's `y` is
  `Quad.mk δ (χ 17) (χ 18)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.Atoms.Fingerprint

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent

open Nock Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
  (sH sL fst eos f1 f2 mR mS mV mW mQ1 mQM bt0 sv cf1 cf2 oLt oDiv oMod lb)

noncomputable section

/-! ## 1. The round-0 readout -/

section Readout
variable {q : ℕ}

/-- One ALU base row as values: column ↦ value (only base columns `< 94` are read). -/
abbrev ARow (q : ℕ) := ℕ → ZMod q

/-- Row `i` (the zero row past the end). -/
def rowAt (al : List (ARow q)) (i : ℕ) : ARow q := al.getD i (fun _ => 0)

/-- The value of column `j` at row `i`. -/
def cl (al : List (ARow q)) (i j : ℕ) : ZMod q := rowAt al i j

/-- The flag test `col = 1`. -/
def onb (al : List (ARow q)) (i j : ℕ) : Bool := decide (cl al i j = 1)

/-- The lane's 32-bit limb `ℓ = Σ_{t<32} 2^t b_t` (in ℕ). -/
def laneL (al : List (ARow q)) (i : ℕ) : ℕ := ∑ t ∈ Finset.range 32, 2 ^ t * (cl al i (bt0 + t)).val

/-- The lane's high half `o = Σ_{t<16} 2^t b_{16+t}` (in ℕ). -/
def laneO (al : List (ARow q)) (i : ℕ) : ℕ := ∑ t ∈ Finset.range 16, 2 ^ t * (cl al i (bt0 + 16 + t)).val

/-- The lane's 32 bits (the packed `Q` carries of an `mQ1` row). -/
def laneBits (al : List (ARow q)) (i : ℕ) : List ℕ := (List.range 32).map fun t => (cl al i (bt0 + t)).val

end Readout

/-! ## 2. Limb polynomials and the fuel-bounded atom walk -/

section Atom
variable {q : ℕ}

/-- The limb polynomial `Σ lᵢ Xⁱ` over `ZMod q` (`= Atoms.limbPoly` at `q = p`). -/
def limbPolyQ (l : List ℕ) : (ZMod q)[X] := (Atoms.natPoly l).map (Nat.castRingHom (ZMod q))

theorem limbPolyQ_natDegree_le (l : List ℕ) : (limbPolyQ (q := q) l).natDegree ≤ l.length := by
  induction l with
  | nil => simp [limbPolyQ, Atoms.natPoly]
  | cons a l ih =>
    simp only [limbPolyQ, Atoms.natPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X] at ih ⊢
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    have := natDegree_X_le (R := ZMod q)
    simp only [List.length_cons]
    omega

/-- **The atom walk** from serial `i` with fuel `f`: `¬wR` ⇒ `[aL, aR]`; `wR` ⇒ `aL ::` the walk from `idR`;
`none` on fuel exhaustion or an out-of-range serial. -/
def atomLimbs (t : List (CellRowB0 q)) : ℕ → ℕ → Option (List ℕ)
  | 0, _ => none
  | f + 1, i =>
    match t[i]? with
    | none => none
    | some c => if c.wR then (atomLimbs t f c.idR).map (c.aL.val :: ·) else some [c.aL.val, c.aR.val]

theorem atomLimbs_length_le (t : List (CellRowB0 q)) :
    ∀ f i l, atomLimbs t f i = some l → l.length ≤ f + 1
  | 0, _, _, h => by simp [atomLimbs] at h
  | f + 1, i, l, h => by
    simp only [atomLimbs] at h
    split at h
    · simp at h
    · split_ifs at h
      · obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        have := atomLimbs_length_le t f _ l' hl'
        simp only [List.length_cons]; omega
      · simp only [Option.some.injEq] at h; subst h; simp

/-- **The atom polynomial of serial `v`**: the limb polynomial of the walk at fuel `nA = |t|`; `0` if the
walk fails (fuel exhausted on a hostile cycle, or `v` out of range). -/
def atomPoly (t : List (CellRowB0 q)) (v : ℕ) : (ZMod q)[X] :=
  match atomLimbs t t.length v with
  | some l => limbPolyQ l
  | none => 0

theorem atomPoly_natDegree_le (t : List (CellRowB0 q)) (v : ℕ) : (atomPoly t v).natDegree ≤ t.length + 1 := by
  unfold atomPoly
  split
  · next l hl => exact (limbPolyQ_natDegree_le l).trans (atomLimbs_length_le t _ _ _ hl)
  · simp

end Atom

/-! ## 3. The polynomial mirror of the identity columns -/

section Mirror
variable {q : ℕ}

/-- `Y − B` (`B = 2^32`). -/
def BX : (ZMod q)[X] := X - C ((2 : ZMod q) ^ 32)

/-- **Horner along a slot** (the `H` / `HO` gates): `lane i + X·(next)` until `eos` (fuel `f`). -/
def hornerP (al : List (ARow q)) (lane : ℕ → ℕ) : ℕ → ℕ → (ZMod q)[X]
  | 0, _ => 0
  | f + 1, i => if onb al i eos then C (lane i : ZMod q) else C (lane i : ZMod q) + X * hornerP al lane f (i + 1)

/-- One packed row `Σ_{t<32} b_t X^t`. -/
def packP (al : List (ARow q)) (i : ℕ) : (ZMod q)[X] := limbPolyQ (laneBits al i)

/-- **Packed Horner** (the `mQ1` gate): `pack i + X^32·(next)` until `eos`. -/
def hpackP (al : List (ARow q)) : ℕ → ℕ → (ZMod q)[X]
  | 0, _ => 0
  | f + 1, i => if onb al i eos then packP al i else packP al i + X ^ 32 * hpackP al f (i + 1)

/-- The slot's `H` (limb Horner) at full fuel. -/
def Hp (al : List (ARow q)) (i : ℕ) : (ZMod q)[X] := hornerP al (laneL al) al.length i

/-- The slot's `HO` (high-half Horner) at full fuel. -/
def HOp (al : List (ARow q)) (i : ℕ) : (ZMod q)[X] := hornerP al (laneO al) al.length i

/-- **`L` at a first row** (`qVal` + the validity read): the atom polynomial of the slot serial on `mR mV`,
`(Y − B)·H` on Q blocks, `H` on `mS mW`. -/
def Lp (al : List (ARow q)) (t : List (CellRowB0 q)) (i : ℕ) : (ZMod q)[X] :=
  if onb al i mR || onb al i mV then atomPoly t (cl al i sv).val
  else if onb al i mQ1 then BX * hpackP al al.length i
  else if onb al i mQM then BX * Hp al i
  else if onb al i mS || onb al i mW then Hp al i
  else 0

/-- **A factor's `L`** (`Lp` restricted to the factor modes `mR mV mS mW`; equal to `Lp` there). -/
def Lf (al : List (ARow q)) (t : List (CellRowB0 q)) (i : ℕ) : (ZMod q)[X] :=
  if onb al i mR || onb al i mV then atomPoly t (cl al i sv).val
  else if onb al i mS || onb al i mW then Hp al i
  else 0

/-- **The latch `RL`** (`qLatch`): `L` of the last `f1` row, carried along lane rows. -/
def RLp (al : List (ARow q)) (t : List (CellRowB0 q)) : ℕ → (ZMod q)[X]
  | 0 => if onb al 0 f1 then Lf al t 0 else 0
  | i + 1 => if onb al (i + 1) f1 then Lf al t (i + 1) else if onb al (i + 1) sL then RLp al t i else 0

/-- **The latch `RO`**: `HO` of the last `f1` row, carried along lane rows. -/
def ROp (al : List (ARow q)) : ℕ → (ZMod q)[X]
  | 0 => if onb al 0 f1 then HOp al 0 else 0
  | i + 1 => if onb al (i + 1) f1 then HOp al (i + 1) else if onb al (i + 1) sL then ROp al i else 0

/-- **`D1`** (`qContr`): hdr `oLt·(1 − lb)`; `f2` the product `RL·L + (Y − B)·RO·HO`; other first rows
`cf1·L`; `0` elsewhere. -/
def D1p (al : List (ARow q)) (t : List (CellRowB0 q)) (i : ℕ) : (ZMod q)[X] :=
  if onb al i sH then C (cl al i oLt * (1 - cl al i lb))
  else if onb al i fst then
    (if onb al i f2 then RLp al t i * Lf al t i + BX * (ROp al i * HOp al i)
     else C (cl al i cf1) * Lp al t i)
  else 0

/-- **`D2`**: hdr `oDiv + oMod`; first rows `cf2·L`; `0` elsewhere. -/
def D2p (al : List (ARow q)) (t : List (CellRowB0 q)) (i : ℕ) : (ZMod q)[X] :=
  if onb al i sH then C (cl al i oDiv + cl al i oMod)
  else if onb al i fst then C (cl al i cf2) * Lp al t i
  else 0

/-- **The block sum** (`qSum`): `D i + D (i+1) + …` while the next row is a lane row (fuel `f`). -/
def blockSum (al : List (ARow q)) (D : ℕ → (ZMod q)[X]) : ℕ → ℕ → (ZMod q)[X]
  | 0, _ => 0
  | f + 1, i => D i + (if onb al (i + 1) sL then blockSum al D f (i + 1) else 0)

/-- The lane rows of the block after row `i` (fuel `f`). -/
def blockRows (al : List (ARow q)) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, i => if onb al (i + 1) sL then (i + 1) :: blockRows al f (i + 1) else []

/-- **The view link** on an `mV` first row: `H − A` (the gate `L = H` with the read `L = A(y)`). -/
def linkP (al : List (ARow q)) (t : List (CellRowB0 q)) (j : ℕ) : (ZMod q)[X] :=
  if onb al j fst && onb al j mV then Hp al j - atomPoly t (cl al j sv).val else 0

/-- **The polynomials of the call at hdr row `h`**: the two identities and the view links of its block. -/
def callPolys (al : List (ARow q)) (t : List (CellRowB0 q)) (h : ℕ) : List (ZMod q)[X] :=
  [blockSum al (D1p al t) al.length h, blockSum al (D2p al t) al.length h] ++
    (blockRows al al.length h).map (linkP al t)

/-- The hdr rows (the calls). -/
def hdrs (al : List (ARow q)) : List ℕ := (List.range al.length).filter fun i => onb al i sH

/-- **`arithPolys`**: every call's polynomials (functions of round-0 data only). -/
def arithPolys (al : List (ARow q)) (t : List (CellRowB0 q)) : List (ZMod q)[X] :=
  (hdrs al).flatMap (callPolys al t)

theorem hdrs_length_le (al : List (ARow q)) : (hdrs al).length ≤ al.length :=
  (List.length_filter_le _ _).trans (by simp)

theorem blockRows_length_le (al : List (ARow q)) : ∀ f i, (blockRows al f i).length ≤ f
  | 0, _ => by simp [blockRows]
  | f + 1, i => by
    simp only [blockRows]
    split_ifs
    · simp only [List.length_cons]; have := blockRows_length_le al f (i + 1); omega
    · simp

theorem callPolys_length_le (al : List (ARow q)) (t : List (CellRowB0 q)) (h : ℕ) :
    (callPolys al t h).length ≤ al.length + 2 := by
  simp only [callPolys, List.length_append, List.length_cons, List.length_nil, List.length_map]
  have := blockRows_length_le al al.length h
  omega

end Mirror

/-! ## 4. Degrees -/

section Degree
variable {q : ℕ}

theorem BX_natDegree_le : (BX : (ZMod q)[X]).natDegree ≤ 1 := natDegree_X_sub_C_le _

theorem natDegree_BX_mul_le {P : (ZMod q)[X]} {d : ℕ} (h : P.natDegree ≤ d) :
    (BX * P).natDegree ≤ d + 1 := by
  have := BX_natDegree_le (q := q)
  exact natDegree_mul_le.trans (by omega)

theorem hornerP_natDegree_le (al : List (ARow q)) (lane : ℕ → ℕ) :
    ∀ f i, (hornerP al lane f i).natDegree ≤ f
  | 0, _ => by simp [hornerP]
  | f + 1, i => by
    simp only [hornerP]
    split_ifs
    · simp
    · refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      have h1 := natDegree_X_le (R := ZMod q)
      have h2 := hornerP_natDegree_le al lane f (i + 1)
      exact natDegree_mul_le.trans (by omega)

theorem packP_natDegree_le (al : List (ARow q)) (i : ℕ) : (packP al i).natDegree ≤ 32 :=
  (limbPolyQ_natDegree_le _).trans (by simp [laneBits])

theorem hpackP_natDegree_le (al : List (ARow q)) : ∀ f i, (hpackP al f i).natDegree ≤ 32 * f
  | 0, _ => by simp [hpackP]
  | f + 1, i => by
    simp only [hpackP]
    have hp := packP_natDegree_le al i
    split_ifs
    · omega
    · refine (natDegree_add_le _ _).trans (max_le (by omega) ?_)
      have h1 : (X ^ 32 : (ZMod q)[X]).natDegree ≤ 32 := natDegree_X_pow_le 32
      have h2 := hpackP_natDegree_le al f (i + 1)
      exact natDegree_mul_le.trans (by omega)

variable (al : List (ARow q)) (t : List (CellRowB0 q))

theorem Hp_natDegree_le (i : ℕ) : (Hp al i).natDegree ≤ al.length := hornerP_natDegree_le _ _ _ _
theorem HOp_natDegree_le (i : ℕ) : (HOp al i).natDegree ≤ al.length := hornerP_natDegree_le _ _ _ _

/-- `Lp ≤ nA + 32·nAL + 1`. -/
theorem Lp_natDegree_le (i : ℕ) : (Lp al t i).natDegree ≤ t.length + 32 * al.length + 1 := by
  have ha := atomPoly_natDegree_le t (cl al i sv).val
  have hh := Hp_natDegree_le al i
  have hk := hpackP_natDegree_le al al.length i
  unfold Lp
  split_ifs
  · omega
  · exact (natDegree_BX_mul_le hk).trans (by omega)
  · exact (natDegree_BX_mul_le hh).trans (by omega)
  · omega
  · simp

/-- `Lf ≤ nA + nAL + 1`. -/
theorem Lf_natDegree_le (i : ℕ) : (Lf al t i).natDegree ≤ t.length + al.length + 1 := by
  have ha := atomPoly_natDegree_le t (cl al i sv).val
  have hh := Hp_natDegree_le al i
  unfold Lf
  split_ifs
  · omega
  · omega
  · simp

theorem RLp_natDegree_le : ∀ i, (RLp al t i).natDegree ≤ t.length + al.length + 1
  | 0 => by
    simp only [RLp]; split_ifs
    · exact Lf_natDegree_le al t 0
    · simp
  | i + 1 => by
    simp only [RLp]; split_ifs
    · exact Lf_natDegree_le al t _
    · exact RLp_natDegree_le i
    · simp

theorem ROp_natDegree_le : ∀ i, (ROp al i).natDegree ≤ al.length
  | 0 => by
    simp only [ROp]; split_ifs
    · exact HOp_natDegree_le al 0
    · simp
  | i + 1 => by
    simp only [ROp]; split_ifs
    · exact HOp_natDegree_le al _
    · exact ROp_natDegree_le i
    · simp

/-- **The per-call degree bound** `dB = 2·nA + 32·nAL + 2`. -/
def dB : ℕ := 2 * t.length + 32 * al.length + 2

theorem D1p_natDegree_le (i : ℕ) : (D1p al t i).natDegree ≤ dB al t := by
  unfold D1p dB
  split_ifs
  · exact (natDegree_C _).trans_le (Nat.zero_le _)
  · have hR := RLp_natDegree_le al t i
    have hL := Lf_natDegree_le al t i
    have hO := ROp_natDegree_le al i
    have hH := HOp_natDegree_le al i
    refine (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (by omega)) ?_)
    have : (ROp al i * HOp al i).natDegree ≤ 2 * al.length := natDegree_mul_le.trans (by omega)
    exact (natDegree_BX_mul_le this).trans (by omega)
  · have := Lp_natDegree_le al t i
    exact natDegree_C_mul_le _ _ |>.trans (by omega)
  · simp

theorem D2p_natDegree_le (i : ℕ) : (D2p al t i).natDegree ≤ dB al t := by
  unfold D2p dB
  split_ifs
  · simp
  · have := Lp_natDegree_le al t i
    exact natDegree_C_mul_le _ _ |>.trans (by omega)
  · simp

theorem blockSum_natDegree_le (D : ℕ → (ZMod q)[X]) {d : ℕ} (hD : ∀ i, (D i).natDegree ≤ d) :
    ∀ f i, (blockSum al D f i).natDegree ≤ d
  | 0, _ => by simp [blockSum]
  | f + 1, i => by
    simp only [blockSum]
    refine (natDegree_add_le _ _).trans (max_le (hD i) ?_)
    split_ifs
    · exact blockSum_natDegree_le D hD f (i + 1)
    · simp

theorem linkP_natDegree_le (j : ℕ) : (linkP al t j).natDegree ≤ dB al t := by
  unfold linkP dB
  split_ifs
  · have ha := atomPoly_natDegree_le t (cl al j sv).val
    have hh := Hp_natDegree_le al j
    exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
  · simp

/-- **Every call polynomial has `natDegree ≤ 2·nA + 32·nAL + 2`.** -/
theorem callPolys_natDegree_le (h : ℕ) : ∀ P ∈ callPolys al t h, P.natDegree ≤ dB al t := by
  intro P hP
  simp only [callPolys, List.mem_append, List.mem_cons, List.mem_map, List.mem_nil_iff, or_false] at hP
  rcases hP with (rfl | rfl) | ⟨j, -, rfl⟩
  · exact blockSum_natDegree_le al _ (D1p_natDegree_le al t) _ _
  · exact blockSum_natDegree_le al _ (D2p_natDegree_le al t) _ _
  · exact linkP_natDegree_le al t j

theorem arithPolys_natDegree_le : ∀ P ∈ arithPolys al t, P.natDegree ≤ dB al t := by
  intro P hP
  obtain ⟨h, -, hP⟩ := List.mem_flatMap.mp hP
  exact callPolys_natDegree_le al t h P hP

end Degree

/-! ## 5. Bad sets and their cards -/

section Bad
open scoped Classical
variable {q : ℕ} [Fact q.Prime] {Kq : Type} [Field Kq] [Algebra (ZMod q) Kq]

/-- The roots in `Kq` of an `𝔽_q` polynomial (`∅` for the zero polynomial). -/
def rootsQ (P : (ZMod q)[X]) : Finset Kq := (P.map (algebraMap (ZMod q) Kq)).roots.toFinset

theorem card_rootsQ_le (P : (ZMod q)[X]) : (rootsQ (Kq := Kq) P).card ≤ P.natDegree :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_map_le))

theorem mem_rootsQ {P : (ZMod q)[X]} {y : Kq} : y ∈ rootsQ P ↔ P ≠ 0 ∧ aeval y P = 0 := by
  have hinj : Function.Injective (algebraMap (ZMod q) Kq) := (algebraMap (ZMod q) Kq).injective
  unfold rootsQ
  rw [Multiset.mem_toFinset]
  by_cases hP : P = 0
  · subst hP; simp
  · have hm : P.map (algebraMap (ZMod q) Kq) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    rw [mem_roots hm, IsRoot.def, eval_map_algebraMap]
    exact ⟨fun h => ⟨hP, h⟩, fun h => h.2⟩

/-- A union of root sets along a list, card `≤ Σ natDegree`. -/
def rootsList (ps : List (ZMod q)[X]) : Finset Kq := (ps.map rootsQ).foldr (· ∪ ·) ∅

theorem mem_rootsList {ps : List (ZMod q)[X]} {y : Kq} : y ∈ rootsList ps ↔ ∃ P ∈ ps, P ≠ 0 ∧ aeval y P = 0 := by
  induction ps with
  | nil => simp [rootsList]
  | cons P ps ih =>
    simp only [rootsList, List.map_cons, List.foldr_cons, Finset.mem_union] at ih ⊢
    rw [ih, mem_rootsQ]
    simp

theorem card_rootsList_le {ps : List (ZMod q)[X]} {d : ℕ} (hd : ∀ P ∈ ps, P.natDegree ≤ d) :
    (rootsList (Kq := Kq) ps).card ≤ ps.length * d := by
  induction ps with
  | nil => simp [rootsList]
  | cons P ps ih =>
    simp only [rootsList, List.map_cons, List.foldr_cons] at ih ⊢
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := (card_rootsQ_le (Kq := Kq) P).trans (hd P (by simp))
    have h2 := ih (fun Q hQ => hd Q (by simp [hQ]))
    simp only [List.length_cons, add_mul, one_mul]
    omega

/-- **The common roots of a list**: the `y` at which EVERY polynomial of the list vanishes, empty when all are
zero (card `≤` the degree of the first nonzero one). -/
def commonRoots (ps : List (ZMod q)[X]) : Finset Kq :=
  match ps.find? (fun P => decide (P ≠ 0)) with
  | none => ∅
  | some P => (rootsQ P).filter fun y => ∀ Q ∈ ps, aeval y Q = 0

theorem card_commonRoots_le {ps : List (ZMod q)[X]} {d : ℕ} (hd : ∀ P ∈ ps, P.natDegree ≤ d) :
    (commonRoots (Kq := Kq) ps).card ≤ d := by
  unfold commonRoots
  split
  · simp
  · next P hP =>
    exact (Finset.card_filter_le _ _).trans ((card_rootsQ_le P).trans (hd P (List.mem_of_find?_eq_some hP)))

theorem eq_zero_of_not_mem_commonRoots {ps : List (ZMod q)[X]} {y : Kq} (hy : y ∉ commonRoots ps)
    (h0 : ∀ P ∈ ps, aeval y P = 0) : ∀ P ∈ ps, P = 0 := by
  unfold commonRoots at hy
  split at hy
  · next hn =>
    intro P hP
    have := List.find?_eq_none.mp hn P hP
    simpa using this
  · next P hP =>
    exfalso
    apply hy
    have hne : P ≠ 0 := by simpa using List.find?_some hP
    rw [Finset.mem_filter, mem_rootsQ]
    exact ⟨⟨hne, h0 P (List.mem_of_find?_eq_some hP)⟩, h0⟩

/-- A union over a list of indices. -/
theorem mem_foldr_union {hs : List ℕ} {g : ℕ → Finset Kq} {y : Kq} :
    y ∈ (hs.map g).foldr (· ∪ ·) ∅ ↔ ∃ h ∈ hs, y ∈ g h := by
  induction hs with
  | nil => simp
  | cons h hs ih => simp [ih]

theorem card_foldr_union_le {hs : List ℕ} {g : ℕ → Finset Kq} {d : ℕ} (hd : ∀ h, (g h).card ≤ d) :
    ((hs.map g).foldr (· ∪ ·) ∅).card ≤ hs.length * d := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons, add_mul, one_mul]
    have := hd h
    exact (Finset.card_union_le _ _).trans (by omega)

variable (al : List (ARow q)) (t : List (CellRowB0 q))

/-- **`arithBad`** (the literal form): every root in `Kq` of every nonzero arithmetic polynomial. -/
def arithBad : Finset Kq := rootsList (arithPolys al t)

theorem mem_arithBad {y : Kq} : y ∈ arithBad al t ↔ ∃ P ∈ arithPolys al t, P ≠ 0 ∧ aeval y P = 0 :=
  mem_rootsList

theorem arithPolys_length_le : (arithPolys al t).length ≤ (hdrs al).length * (al.length + 2) := by
  unfold arithPolys
  rw [List.length_flatMap]
  refine (List.sum_le_length_nsmul _ (al.length + 2) ?_).trans (by simp)
  intro x hx
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hx
  exact callPolys_length_le al t h

/-- **Card of `arithBad`**: `≤ calls·(nAL + 2)·(2·nA + 32·nAL + 2)`. -/
theorem arithBad_card_le : (arithBad (Kq := Kq) al t).card ≤ (hdrs al).length * (al.length + 2) * dB al t :=
  (card_rootsList_le (arithPolys_natDegree_le al t)).trans
    (Nat.mul_le_mul_right _ (arithPolys_length_le al t))

/-- **`arithBadC`** (per call): the `y` at which every polynomial of some call vanishes, that call
having a nonzero polynomial. -/
def arithBadC : Finset Kq := ((hdrs al).map fun h => commonRoots (callPolys al t h)).foldr (· ∪ ·) ∅

theorem mem_arithBadC {y : Kq} : y ∈ arithBadC al t ↔ ∃ h ∈ hdrs al, y ∈ commonRoots (callPolys al t h) := by
  unfold arithBadC
  exact mem_foldr_union

/-- **Card of `arithBadC`**: `≤ calls·(2·nA + 32·nAL + 2)`. -/
theorem arithBadC_card_le : (arithBadC (Kq := Kq) al t).card ≤ (hdrs al).length * dB al t := by
  unfold arithBadC
  exact card_foldr_union_le fun h => card_commonRoots_le (callPolys_natDegree_le al t h)

/-- **Outside `arithBadC`, per call**: if every polynomial of a call vanishes at `y`, all are zero. -/
theorem eq_zero_of_not_mem_arithBadC {y : Kq} (hy : y ∉ arithBadC al t) {h : ℕ} (hh : h ∈ hdrs al)
    (h0 : ∀ P ∈ callPolys al t h, aeval y P = 0) : ∀ P ∈ callPolys al t h, P = 0 :=
  eq_zero_of_not_mem_commonRoots (fun hm => hy ((mem_arithBadC al t).mpr ⟨h, hh, hm⟩)) h0

/-- **Outside `arithBad`**: every arithmetic polynomial vanishing at `y` is zero. -/
theorem eq_zero_of_not_mem_arithBad {y : Kq} (hy : y ∉ arithBad al t) :
    ∀ P ∈ arithPolys al t, aeval y P = 0 → P = 0 := by
  intro P hP h0
  by_contra hne
  exact hy ((mem_arithBad al t).mpr ⟨P, hP, hne, h0⟩)

end Bad

/-! ## 6. The summands on `frameJ8`'s limb coin `y = (χ₁₇, χ₁₈)` -/

section Summand
open scoped Classical
variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [Fintype K] [DecidableEq K] (δ : K) [Fact (¬ IsSquare δ)]
  [Algebra (ZMod q) (Quad δ)]
variable {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
  (alu : Tr → List (ARow q)) (atom : Tr → List (CellRowB0 q)) (C A AL : ℕ)
  (hC : ∀ tr, (hdrs (alu tr)).length ≤ C) (hA : ∀ tr, (atom tr).length ≤ A) (hAL : ∀ tr, (alu tr).length ≤ AL)
  (hc : ∀ Q, St Q → ∀ χ χ', alu (Q χ) = alu (Q χ') ∧ atom (Q χ) = atom (Q χ'))

/-- The per-call weight `C·(2A + 32·AL + 2)`. -/
def weightC : ℕ := C * (2 * A + 32 * AL + 2)

include hA hAL in
theorem dB_le (tr : Tr) : dB (alu tr) (atom tr) ≤ 2 * A + 32 * AL + 2 := by
  unfold dB; have := hA tr; have := hAL tr; omega

/-- **`arithSZ`** — the arithmetic SZ summand (per call): coins `{17, 18}`, `dep = ∅`, weight
`C·(2A + 32·AL + 2)`. -/
def arithSZ : BadSummand frameJ8 K Tr St :=
  towerSeedSummand δ frameJ8 cY1 cY2 St (fun tr => arithBadC (Kq := Quad δ) (alu tr) (atom tr)) (weightC C A AL)
    (fun tr => (arithBadC_card_le _ _).trans (Nat.mul_le_mul (hC tr) (dB_le alu atom A AL hA hAL tr)))
    (fun Q hQ χ χ' => by simp only [(hc Q hQ χ χ').1, (hc Q hQ χ χ').2])

include hC hA hAL in
/-- **The card lemma**: `arithSZ`'s bad set at every trace has card `≤ C·(2A + 32·AL + 2)`. -/
theorem arithSZ_card_le (tr : Tr) :
    (arithBadC (Kq := Quad δ) (alu tr) (atom tr)).card ≤ weightC C A AL :=
  (arithBadC_card_le _ _).trans (Nat.mul_le_mul (hC tr) (dB_le alu atom A AL hA hAL tr))

theorem arithSZ_weight : (arithSZ δ St alu atom C A AL hC hA hAL hc).weight = C * (2 * A + 32 * AL + 2) := rfl

theorem arithSZ_coins : (arithSZ δ St alu atom C A AL hC hA hAL hc).coins = {cY1, cY2} := rfl

theorem arithSZ_dep : (arithSZ δ St alu atom C A AL hC hA hAL hc).dep = ∅ := rfl

theorem arithSZ_mem_iff (tr : Tr) (χ : Coins frameJ8 K) :
    (arithSZ δ St alu atom C A AL hC hA hAL hc).mem tr χ ↔
      Quad.mk δ (χ cY1) (χ cY2) ∈ arithBadC (Kq := Quad δ) (alu tr) (atom tr) := by
  unfold arithSZ
  exact towerSeedSummand_mem_iff δ _ _ _ _ _ _ _ _ tr χ

/-- **`outside_arithSZ`**: outside the summand, for every call of the trace, if every call polynomial vanishes
at `y = Quad.mk δ χ₁₇ χ₁₈` then every call polynomial is the zero polynomial. -/
theorem outside_arithSZ (tr : Tr) (χ : Coins frameJ8 K) (hχ : ¬ (arithSZ δ St alu atom C A AL hC hA hAL hc).mem tr χ)
    {h : ℕ} (hh : h ∈ hdrs (alu tr))
    (h0 : ∀ P ∈ callPolys (alu tr) (atom tr) h, aeval (Quad.mk δ (χ cY1) (χ cY2)) P = 0) :
    ∀ P ∈ callPolys (alu tr) (atom tr) h, P = 0 :=
  eq_zero_of_not_mem_arithBadC _ _ (fun hm => hχ ((arithSZ_mem_iff δ St alu atom C A AL hC hA hAL hc tr χ).mpr hm))
    hh h0

/-- **The weight bound**: the per-call weight is within `C·(3A + 32·AL + 2)`. -/
theorem weightC_le_FSZ2 : weightC C A AL ≤ C * (3 * A + 32 * AL + 2) :=
  Nat.mul_le_mul_left _ (by omega)

/-- The per-polynomial weight `C·(AL + 2)·(2A + 32·AL + 2)`. -/
def weightP : ℕ := C * (AL + 2) * (2 * A + 32 * AL + 2)

/-- **`arithSZP`** — the literal per-polynomial summand (weight `C·(AL + 2)·(2A + 32·AL + 2)`). -/
def arithSZP : BadSummand frameJ8 K Tr St :=
  towerSeedSummand δ frameJ8 cY1 cY2 St (fun tr => arithBad (Kq := Quad δ) (alu tr) (atom tr)) (weightP C A AL)
    (fun tr => (arithBad_card_le _ _).trans
      (Nat.mul_le_mul (Nat.mul_le_mul (hC tr) (by have := hAL tr; omega)) (dB_le alu atom A AL hA hAL tr)))
    (fun Q hQ χ χ' => by simp only [(hc Q hQ χ χ').1, (hc Q hQ χ χ').2])

include hC hA hAL in
theorem arithSZP_card_le (tr : Tr) :
    (arithBad (Kq := Quad δ) (alu tr) (atom tr)).card ≤ weightP C A AL :=
  (arithBad_card_le _ _).trans
    (Nat.mul_le_mul (Nat.mul_le_mul (hC tr) (by have := hAL tr; omega)) (dB_le alu atom A AL hA hAL tr))

/-- **`outside_arithSZP`**: outside the per-polynomial summand, `∀ P ∈ arithPolys, aeval y P = 0 → P = 0`. -/
theorem outside_arithSZP (tr : Tr) (χ : Coins frameJ8 K)
    (hχ : ¬ (arithSZP δ St alu atom C A AL hC hA hAL hc).mem tr χ) :
    ∀ P ∈ arithPolys (alu tr) (atom tr), aeval (Quad.mk δ (χ cY1) (χ cY2)) P = 0 → P = 0 :=
  eq_zero_of_not_mem_arithBad _ _ fun hm => by
    unfold arithSZP at hχ
    exact hχ ((towerSeedSummand_mem_iff δ _ _ _ _ _ _ _ _ tr χ).mpr hm)

end Summand

/-! ## 7. The concrete ALU readout -/

section Concrete
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (natOf)
variable {F : Type} [Field F]

/-- **The ALU's round-0 rows** from a column family (base columns `< 94` at the row nodes, through `natOf`). -/
def aluRowsOf {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (cols : Fin w → F[X]) :
    List (ARow (ringChar F)) :=
  List.ofFn fun i : Fin n => fun j =>
    if j < 94 then (natOf ((Framework.Reify.envOfTrace cols orbit.ω (nodes i) (fun _ => 0) (fun _ => 0)).trace j) :
      ZMod (ringChar F)) else 0

theorem aluRowsOf_length {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (cols : Fin w → F[X]) :
    (aluRowsOf nodes orbit cols).length = n := by simp [aluRowsOf]

/-- Only the base columns are read. -/
theorem aluRowsOf_congr {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) {cols cols' : Fin w → F[X]}
    (hq : ∀ (j : ℕ) (hj : j < w), j < 94 → cols ⟨j, hj⟩ = cols' ⟨j, hj⟩) :
    aluRowsOf nodes orbit cols = aluRowsOf nodes orbit cols' := by
  unfold aluRowsOf
  congr 1
  funext i j
  split_ifs with hj
  · congr 2
    simp only [Framework.Reify.envOfTrace]
    split_ifs with hw
    · rw [hq j hw hj]
    · rfl
  · rfl

/-- **Coin-freeness** (the `hconst` source): if the base columns `< 94` are staged at round 0, the readout is
the same at every coin vector. -/
theorem aluRowsOf_const {K : Type} {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (cr : Fin w → ℕ) (hcr : ∀ j : Fin w, (j : ℕ) < 94 → cr j = 0)
    (Q : Coins frameJ8 K → Fin w → F[X]) (hQ : StagedCols frameJ8 cr Q) (χ χ' : Coins frameJ8 K) :
    aluRowsOf nodes orbit (Q χ) = aluRowsOf nodes orbit (Q χ') :=
  aluRowsOf_congr nodes orbit fun j hj hj94 =>
    hQ ⟨j, hj⟩ χ χ' fun i hi => absurd hi (by rw [hcr ⟨j, hj⟩ hj94]; omega)

end Concrete

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent
