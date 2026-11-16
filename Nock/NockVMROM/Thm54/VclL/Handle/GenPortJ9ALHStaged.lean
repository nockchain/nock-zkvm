/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHStaged.lean

  **The staged J-9 AL generator composes to `genJ9ALXJ`.**

  * coins: `c0_assemble`, `c1_assemble`, `assemble_c`, `s0_round` / `s1_round` (`c0`/`c1` are exactly the
    `sampledAfter = 0` / `= 1` coins of `frameJ8`, in `TranscriptJ8`'s squeeze order);
  * per chip, from the generators: round-0 entries read no coin, round-1 entries read only the round-0 coins
    (`cellGenB_ent`, `walkGenRowsB_ent`, `walkGenRowsBE_ent`, `atomGenE_ent`, `jGen_ent0` / `jGen_eq`,
    `compGenX9_ent0` / `compGenX9_eq`, `axGenOf_ent`, `spGenE_ent`, `aluGenE_ent`);
  * `staged_rec` (generic assembly `assembleI_blankL` over a variable record), `runStaged_assemble`,
    **`runStaged_eq`**: for EVERY `χe`, `runStaged … (c0 χe) (c1 χe) = genJ9ALXJ … χe`;
  * **`checkJ9ALX_staged`**: `checkJ9ALX` accepts the staged output at `assemble coins0 coins1` under the binders of
    `GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ`.
-/
import Nock.V1J9AL.GenJ9ALXJStaged
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHonestJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonestJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun (recJ9ALXJRn)
open Nock.DriverJ8.TranscriptJ8 (idxS0 idxS1)
open Nock.V1J9AL.CheckJ9AL
open Nock.V1J8.FillMem
open Nock.V1J9A Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54 Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c2 c3)
open Nock.Jet.Prim (PrimOp)
open Nock.V1J9AL.GenJ9ALXJStaged
open Nock.V1J9AL
open Nock.NockVMROM.Thm54.T0Tower

/-! ## 1. Coins -/

theorem c0_assemble (a : Coins0) (b : Coins1) : c0 (assemble a b) = a := by
  funext k; fin_cases k <;> rfl

theorem c1_assemble (a : Coins0) (b : Coins1) : c1 (assemble a b) = b := by
  funext k; fin_cases k <;> rfl

theorem assemble_c (χe : CoinsE) : assemble (c0 χe) (c1 χe) = χe := by
  funext i; fin_cases i <;> rfl

theorem s0_val (k : Fin 13) : (s0 k : ℕ) = idxS0.getD k 0 := by fin_cases k <;> rfl
theorem s1_val (k : Fin 6) : (s1 k : ℕ) = idxS1.getD k 0 := by fin_cases k <;> rfl
theorem s0_round (k : Fin 13) : frameJ8.sampledAfter (s0 k) = 0 := by fin_cases k <;> rfl
theorem s1_round (k : Fin 6) : frameJ8.sampledAfter (s1 k) = 1 := by fin_cases k <;> rfl

/-! ## 4. Generic lemmas -/

theorem getN_maskC (a b r : ℕ) (q : ChipIn) (c i : ℕ) :
    getN (maskC a b r q) c i = if cr3 a b c = r then getN q c i else 0 := by
  unfold getN maskC; dsimp only; split_ifs <;> rfl

theorem getN_fin (q : ChipIn) (c : ℕ) (i : Fin q.n) : getN q c i = q.cols c i := by
  unfold getN; rw [dif_pos i.isLt]

theorem mergeCols_eq (a b : ℕ) (q0 q1 q2 q : ChipIn)
    (h0 : ∀ c i, cr3 a b c = 0 → getN q0 c i = getN q c i)
    (h1 : ∀ c i, cr3 a b c = 1 → getN q1 c i = getN q c i)
    (h2 : ∀ c i, cr3 a b c = 2 → getN q2 c i = getN q c i) :
    mergeCols a b q0 q1 q2 q.n = q.cols := by
  funext c i
  unfold mergeCols
  have hr : cr3 a b c = 0 ∨ cr3 a b c = 1 ∨ cr3 a b c = 2 := by unfold cr3; split_ifs <;> simp
  rcases hr with h | h | h
  · rw [if_pos h, h0 c i h, getN_fin]
  · rw [if_neg (by omega), if_pos h, h1 c i h, getN_fin]
  · rw [if_neg (by omega), if_neg (by omega), h2 c i h, getN_fin]

/-- The three masked blocks of chips `q0 q1 q2` merge to `q` when `q0`/`q1` agree with `q` on their rounds and
`q2 = q`. -/
theorem mergeCols_blk (a b : ℕ) (q0 q1 q : ChipIn)
    (h0 : ∀ c i, cr3 a b c = 0 → getN q0 c i = getN q c i)
    (h1 : ∀ c i, cr3 a b c = 1 → getN q1 c i = getN q c i) :
    mergeCols a b (maskC a b 0 q0) (maskC a b 1 q1) (maskC a b 2 q) q.n = q.cols :=
  mergeCols_eq a b _ _ _ q (fun c i h => by rw [getN_maskC, if_pos h, h0 c i h])
    (fun c i h => by rw [getN_maskC, if_pos h, h1 c i h])
    (fun c i h => by rw [getN_maskC, if_pos h])

/-- **The assembly is the record** when each chip's merged columns are its columns (generic in the record). -/
theorem assembleI_blankL (I : InJ9AL) (b0 b1 b2 : BlkL)
    (hX : mergeCols 83 137 b0.X b1.X b2.X I.X.n = I.X.cols)
    (hC : mergeCols 134 188 b0.C b1.C b2.C I.C.n = I.C.cols)
    (hW : mergeCols 25 97 b0.W b1.W b2.W I.W.n = I.W.cols)
    (hJ : mergeCols 29 71 b0.J b1.J b2.J I.J.n = I.J.cols)
    (hA : mergeCols 205 259 b0.A b1.A b2.A I.A.n = I.A.cols)
    (hV : mergeCols 25 97 b0.V b1.V b2.V I.V.n = I.V.cols)
    (hAX : mergeCols 22 22 b0.AX b1.AX b2.AX I.AX.n = I.AX.cols)
    (hSP : mergeCols 72 72 b0.SP b1.SP b2.SP I.SP.n = I.SP.cols)
    (hAL : mergeCols 94 148 b0.AL b1.AL b2.AL I.AL.n = I.AL.cols) :
    assembleI b0 b1 b2 (blankL I) = I := by
  obtain ⟨⟨⟨c, M, χ, r, g, X, C, W, J, A, V, kr, krV, lay, Rt, regs, ids, idx, rk⟩, AX, SP, pX, pS, axOn, spOn,
    rAX, rSP⟩, AL, pL, aluOn, prims, idxP, rkP, rAL⟩ := I
  obtain ⟨Xh, Xn, Xω, Xc⟩ := X
  obtain ⟨Ch, Cn, Cω, Cc⟩ := C
  obtain ⟨Wh, Wn, Wω, Wc⟩ := W
  obtain ⟨Jh, Jn, Jω, Jc⟩ := J
  obtain ⟨Ah, An, Aω, Ac⟩ := A
  obtain ⟨Vh, Vn, Vω, Vc⟩ := V
  obtain ⟨AXh, AXn, AXω, AXc⟩ := AX
  obtain ⟨SPh, SPn, SPω, SPc⟩ := SP
  obtain ⟨ALh, ALn, ALω, ALc⟩ := AL
  dsimp only at hX hC hW hJ hA hV hAX hSP hAL
  unfold assembleI blankL mergeC blankC
  dsimp only
  rw [hX, hC, hW, hJ, hA, hV, hAX, hSP, hAL]


/-! ## 5. Table entries -/

/-- Entry `(i, c)` of a row table (`0` off it). -/
def ent (tbl : Array (Array (ZMod p))) (i c : ℕ) : ZMod p := (tbl.getD i #[]).getD c 0

theorem getN_chipOf (tbl : Array (Array (ZMod p))) (c i : ℕ) : getN (chipOf tbl) c i = ent tbl i c := by
  unfold getN chipOf ent colsOf
  dsimp only
  split_ifs with h
  · rfl
  · simp [Array.getD, h]

theorem getN_colsOf (tbl : Array (Array (ZMod p))) (h : ℕ) (ω : Gold) (n c i : ℕ) :
    getN ⟨h, n, ω, colsOf tbl n⟩ c i = if i < n then ent tbl i c else 0 := by
  unfold getN ent colsOf
  dsimp only
  split_ifs <;> rfl

theorem ent_congr {α β : Type} (l : List α) (l' : List β) (g : α → Array (ZMod p)) (g' : β → Array (ZMod p))
    (i c : ℕ) (hlen : l.length = l'.length)
    (h : ∀ (h1 : i < l.length) (h2 : i < l'.length), (g l[i]).getD c 0 = (g' l'[i]).getD c 0) :
    ent (l.map g).toArray i c = ent (l'.map g').toArray i c := by
  unfold ent
  by_cases hi : i < l.length
  · have hi' : i < l'.length := hlen ▸ hi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
    simpa [Array.getD_eq_getD_getElem?] using h hi hi'
  · have hi' : ¬ i < l'.length := hlen ▸ hi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_none (by omega : l.length ≤ i), List.getElem?_eq_none (by omega : l'.length ≤ i),
      Option.map_none, Option.getD_none]

theorem getD_ofFn {W : ℕ} (f : Fin W → ZMod p) (c : ℕ) :
    (Array.ofFn f).getD c 0 = if h : c < W then f ⟨c, h⟩ else 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs <;> simp_all

theorem getD_map_P {α β γ : Type} (l : List α) (f g : α → β) (P : β → γ) (dl dr : β) (hd : P dl = P dr)
    (h : ∀ a, P (f a) = P (g a)) (j : ℕ) : P ((l.map f).getD j dl) = P ((l.map g).getD j dr) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [h, hd]

/-! ## 6. The cell table -/

def cbD (d : CellD) := (d.j, d.l, d.r, d.mu, d.muL, d.muR, d.idL, d.idR)
def cfD (d : CellD) := (d.pE, d.lE, d.rE)

theorem qslotD_lo (d d' : CellD) (va xa va' xa' : K6) (hf : cfD d = cfD d') (s : ℕ) (hs : s ≤ 8) :
    qslotD d va xa s = qslotD d' va' xa' s := by
  obtain ⟨_, _, _, pE, lE, rE, _⟩ := d
  obtain ⟨_, _, _, pE', lE', rE', _⟩ := d'
  simp only [cfD, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  interval_cases s <;> rfl

/-- Columns `< 134` of a cell row (the prefix of `cellColD`'s chain). -/
def cellLo (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (c : ℕ) : ZMod p :=
  if c = 0 then flag (d.j == 0) else if c = 1 then flag (d.j + 1 == D)
  else if c < 129 then cellBaseD mv mx mx1 d c
  else if c = 129 then (mh.getD d.j 0 : ZMod P)
  else if c < 132 then 0
  else if c = 132 then ((d.muL % two62 + d.muL / two62 : ℕ) : ZMod P)⁻¹
  else ((d.muR % two62 + d.muR / two62 : ℕ) : ZMod P)⁻¹

theorem cellColD_lo (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ) (hc : c < 134) :
    cellColD D mv mx mx1 mh d va xa ha c = cellLo D mv mx mx1 mh d c := by
  rw [cellColD, cellLo]
  by_cases h0 : c = 0
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : c = 1
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : c < 129
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : c = 129
  · rw [if_pos h3, if_pos h3]
  rw [if_neg h3, if_neg h3]
  by_cases h4 : c < 132
  · rw [if_pos h4, if_pos h4]
  rw [if_neg h4, if_neg h4]
  by_cases h5 : c = 132
  · rw [if_pos h5, if_pos h5]
  rw [if_neg h5, if_neg h5, if_pos (by omega : c = 133)]

theorem cellColD_mid (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ) (hc0 : 134 ≤ c)
    (hc : c < 230) :
    cellColD D mv mx mx1 mh d va xa ha c =
      limbZ (if (c - 134) / 3 % 2 = 0 then (qslotD d va xa ((c - 134) / 3 / 2)).re
        else (qslotD d va xa ((c - 134) / 3 / 2)).im) ((c - 134) % 3) := by
  rw [cellColD, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hc]

theorem cellColD_r0 (D : ℕ) (mv mx mx1 mh : Array ℕ) (d d' : CellD) (va xa ha va' xa' ha' : K6) (c : ℕ)
    (hc : c < 134) (h : cbD d = cbD d') :
    cellColD D mv mx mx1 mh d va xa ha c = cellColD D mv mx mx1 mh d' va' xa' ha' c := by
  rw [cellColD_lo _ _ _ _ _ _ _ _ _ _ hc, cellColD_lo _ _ _ _ _ _ _ _ _ _ hc]
  obtain ⟨j, l, r, pE, lE, rE, mu, muL, muR, idL, idR, _⟩ := d
  obtain ⟨j', l', r', pE', lE', rE', mu', muL', muR', idL', idR', _⟩ := d'
  simp only [cbD, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem cellColD_r1 (D : ℕ) (mv mx mx1 mh : Array ℕ) (d d' : CellD) (va xa ha va' xa' ha' : K6) (c : ℕ)
    (hc : c < 188) (h : cbD d = cbD d') (hf : cfD d = cfD d') :
    cellColD D mv mx mx1 mh d va xa ha c = cellColD D mv mx mx1 mh d' va' xa' ha' c := by
  by_cases h0 : c < 134
  · exact cellColD_r0 D mv mx mx1 mh d d' va xa ha va' xa' ha' c h0 h
  rw [cellColD_mid _ _ _ _ _ _ _ _ _ _ (by omega) (by omega), cellColD_mid _ _ _ _ _ _ _ _ _ _ (by omega) (by omega),
    qslotD_lo d d' va xa va' xa' hf ((c - 134) / 3 / 2) (by omega)]

theorem cellColDB_r0 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d d' : CellD)
    (va xa ha va' xa' ha' : K6) (c : ℕ) (hc : c < 134) (h : cbD d = cbD d') :
    cellColDB big D mv mx mx1 mh d va xa ha c = cellColDB big D mv mx mx1 mh d' va' xa' ha' c := by
  have h0 := cellColD_r0 D mv mx mx1 mh d d' va xa ha va' xa' ha' c hc h
  obtain ⟨j, l, r, pE, lE, rE, mu, muL, muR, idL, idR, _⟩ := d
  obtain ⟨j', l', r', pE', lE', rE', mu', muL', muR', idL', idR', _⟩ := d'
  simp only [cbD, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  unfold cellColDB
  split_ifs <;> first | exact h0 | rfl

theorem cellColDB_r1 (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d d' : CellD)
    (va xa ha va' xa' ha' : K6) (c : ℕ) (hc : c < 188) (h : cbD d = cbD d') (hf : cfD d = cfD d') :
    cellColDB big D mv mx mx1 mh d va xa ha c = cellColDB big D mv mx mx1 mh d' va' xa' ha' c := by
  have h0 := cellColD_r1 D mv mx mx1 mh d d' va xa ha va' xa' ha' c hc h hf
  obtain ⟨j, l, r, pE, lE, rE, mu, muL, muR, idL, idR, _⟩ := d
  obtain ⟨j', l', r', pE', lE', rE', mu', muL', muR', idL', idR', _⟩ := d'
  simp only [cbD, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  unfold cellColDB
  split_ifs <;> first | exact h0 | rfl

theorem cbD_cellDB (k k' : Co) (y y' : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun)
    (n : Noun) (j : ℕ) : cbD (cellDB k y H big cs n j) = cbD (cellDB k' y' H big cs n j) := rfl

theorem cfD_cellDB (k k' : Co) (y y' : K6) (hz : k.z = k'.z) (hy : y = y') (H : Noun → ℕ × ℕ)
    (big : Noun → Option ℕ) (cs : List Noun) (n : Noun) (j : ℕ) :
    cfD (cellDB k y H big cs n j) = cfD (cellDB k' y' H big cs n j) := by
  unfold cfD cellDB; rw [hz, hy]

/-- The cell table's entries in columns `< 188` read only `(k.z, y)`; in columns `< 134` nothing. -/
theorem cellGenB_ent (k k' : Co) (y y' : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun)
    (mv mx mx1 mh : Array ℕ) (i c : ℕ) (hc : c < 134 ∨ (c < 188 ∧ k.z = k'.z ∧ y = y')) :
    ent (cellGenB k y H big cs mv mx mx1 mh).1 i c = ent (cellGenB k' y' H big cs mv mx mx1 mh).1 i c := by
  unfold cellGenB
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  split_ifs with hw
  · have hb := getD_map_P ((cs.zipIdx 0)) (fun x => cellDB k y H big cs x.1 x.2)
      (fun x => cellDB k' y' H big cs x.1 x.2) cbD (cellDB k y H big cs (.atom 0) ((List.range cs.length)[i]))
      (cellDB k' y' H big cs (.atom 0) ((List.range cs.length)[i])) (cbD_cellDB _ _ _ _ _ _ _ _ _)
      (fun a => cbD_cellDB _ _ _ _ _ _ _ _ _) ((List.range cs.length)[i])
    rcases hc with hc | ⟨hc, hz, hy⟩
    · exact cellColDB_r0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ c hc hb
    · have hf := getD_map_P ((cs.zipIdx 0)) (fun x => cellDB k y H big cs x.1 x.2)
        (fun x => cellDB k' y' H big cs x.1 x.2) cfD (cellDB k y H big cs (.atom 0) ((List.range cs.length)[i]))
        (cellDB k' y' H big cs (.atom 0) ((List.range cs.length)[i])) (cfD_cellDB _ _ _ _ hz hy _ _ _ _ _)
        (fun a => cfD_cellDB _ _ _ _ hz hy _ _ _ _ _) ((List.range cs.length)[i])
      exact cellColDB_r1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ c hc hb hf
  · rfl

/-! ## 7. The walk tables -/

def wbD (d : WalkD) := (d.w, d.j, d.idx, d.ridx)
def wfD (d : WalkD) := (d.pE, d.lE, d.rE, d.rootE)

theorem walkColDB_r1 (cert : ℕ → ℕ → ℕ) (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d d' : WalkD) (ln cnt acc ln' cnt' acc' : K3)
    (xa pa hxa hpa xa' pa' hxa' hpa' : K6) (c : ℕ) (hc : c < 25 ∨ (c < 97 ∧ wfD d = wfD d')) (h : wbD d = wbD d') :
    walkColDB cert H N kr q d ln cnt acc xa pa hxa hpa c =
      walkColDB cert H N kr q d' ln' cnt' acc' xa' pa' hxa' hpa' c := by
  obtain ⟨w, j, pE, lE, rE, rootE, idx, ridx, _⟩ := d
  obtain ⟨w', j', pE', lE', rE', rootE', idx', ridx', _⟩ := d'
  simp only [wbD, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rcases hc with hc | ⟨hc, hf⟩
  · interval_cases c <;> rfl
  · simp only [wfD, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    interval_cases c <;> rfl

theorem wbD_walkDB (k k' : Co) (y y' : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (w : WRow)
    (j : ℕ) : wbD (walkDB k y H rI cs w j) = wbD (walkDB k' y' H rI cs w j) := rfl

theorem wfD_walkDB (k k' : Co) (y y' : K6) (hz : k.z = k'.z) (hy : y = y') (H : Noun → ℕ × ℕ) (rI : Noun → ℕ)
    (cs : List Noun) (w : WRow) (j : ℕ) : wfD (walkDB k y H rI cs w j) = wfD (walkDB k' y' H rI cs w j) := by
  unfold wfD walkDB; rw [hz, hy]

theorem walkDBE_w (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).w = (walkDB k y H rI cs w j).w := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_j (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).j = (walkDB k y H rI cs w j).j := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_idx (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).idx = (walkDB k y H rI cs w j).idx := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_ridx (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).ridx = (walkDB k y H rI cs w j).ridx := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_pE (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).pE = (walkDB k y H rI cs w j).pE := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_lE (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).lE = (walkDB k y H rI cs w j).lE := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_rE (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).rE = (walkDB k y H rI cs w j).rE := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem walkDBE_rootE (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : (walkDBE ptr k y H rI cs w j).rootE = (walkDB k y H rI cs w j).rootE := by
  unfold walkDBE; split
  · rfl
  · rfl

theorem wbD_walkDBE_eq (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : wbD (walkDBE ptr k y H rI cs w j) = wbD (walkDB k y H rI cs w j) := by
  unfold wbD; rw [walkDBE_w, walkDBE_j, walkDBE_idx, walkDBE_ridx]

theorem wfD_walkDBE_eq (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : wfD (walkDBE ptr k y H rI cs w j) = wfD (walkDB k y H rI cs w j) := by
  unfold wfD; rw [walkDBE_pE, walkDBE_lE, walkDBE_rE, walkDBE_rootE]

theorem wbD_walkDBE (ptr : Noun → ℕ) (k k' : Co) (y y' : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (w : WRow) (j : ℕ) : wbD (walkDBE ptr k y H rI cs w j) = wbD (walkDBE ptr k' y' H rI cs w j) := by
  rw [wbD_walkDBE_eq, wbD_walkDBE_eq]; rfl

theorem wfD_walkDBE (ptr : Noun → ℕ) (k k' : Co) (y y' : K6) (hz : k.z = k'.z) (hy : y = y')
    (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (w : WRow) (j : ℕ) :
    wfD (walkDBE ptr k y H rI cs w j) = wfD (walkDBE ptr k' y' H rI cs w j) := by
  rw [wfD_walkDBE_eq, wfD_walkDBE_eq]; exact wfD_walkDB k k' y y' hz hy H rI cs w j

/-- One atom-walk column (`walkGenRowsBE`'s cell-tail override at `24`). -/
theorem walkColBE_r1 (ptr : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d d' : WalkD)
    (ln cnt acc ln' cnt' acc' : K3) (xa pa hxa hpa xa' pa' hxa' hpa' : K6) (c : Fin 166)
    (hc : (c : ℕ) < 25 ∨ ((c : ℕ) < 97 ∧ wfD d = wfD d')) (h : wbD d = wbD d') :
    (if c = 24 ∧ (tlN' d.w.node).isCell then ((ptr d.w.node : ℕ) : ZMod P) else
      walkColDB cert H N kr q d ln cnt acc xa pa hxa hpa c) =
    (if c = 24 ∧ (tlN' d'.w.node).isCell then ((ptr d'.w.node : ℕ) : ZMod P) else
      walkColDB cert H N kr q d' ln' cnt' acc' xa' pa' hxa' hpa' c) := by
  have h0 := walkColDB_r1 cert H N kr q d d' ln cnt acc ln' cnt' acc' xa pa hxa hpa xa' pa' hxa' hpa' c hc h
  have hw : d.w = d'.w := congrArg Prod.fst h
  rw [hw]
  split_ifs
  · rfl
  · exact h0

/-- The walk table's entries in columns `< 97` read only `(k.z, y)`; in columns `< 25` nothing. -/
theorem walkGenRowsB_ent (k k' : Co) (y y' : K6) (α γ α' γ' : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ)
    (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr i c : ℕ)
    (hc : c < 25 ∨ (c < 97 ∧ k.z = k'.z ∧ y = y')) :
    ent (walkGenRowsB k y α γ H rI cert cs ws kr).1 i c =
      ent (walkGenRowsB k' y' α' γ' H rI cert cs ws kr).1 i c := by
  unfold walkGenRowsB
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  split_ifs with hw
  · have hb := getD_map_P (ws.zipIdx 0) (fun x => walkDB k y H rI cs x.1 x.2)
      (fun x => walkDB k' y' H rI cs x.1 x.2) wbD
      (walkDB k y H rI cs (ws.getD ((List.range ws.length)[i]) ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩)
        ((List.range ws.length)[i]))
      (walkDB k' y' H rI cs (ws.getD ((List.range ws.length)[i]) ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩)
        ((List.range ws.length)[i])) (wbD_walkDB _ _ _ _ _ _ _ _ _)
      (fun a => wbD_walkDB _ _ _ _ _ _ _ _ _) ((List.range ws.length)[i])
    refine walkColDB_r1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c ?_ hb
    rcases hc with hc | ⟨hc, hz, hy⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, getD_map_P (ws.zipIdx 0) (fun x => walkDB k y H rI cs x.1 x.2)
        (fun x => walkDB k' y' H rI cs x.1 x.2) wfD _ _ (wfD_walkDB _ _ _ _ hz hy _ _ _ _ _)
        (fun a => wfD_walkDB _ _ _ _ hz hy _ _ _ _ _) _⟩
  · rfl

/-- The atom walk's entries (as `walkGenRowsB_ent`). -/
theorem walkGenRowsBE_ent (ptr : Noun → ℕ) (k k' : Co) (y y' : K6) (α γ α' γ' : K3) (H : Noun → ℕ × ℕ)
    (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr i c : ℕ)
    (hc : c < 25 ∨ (c < 97 ∧ k.z = k'.z ∧ y = y')) :
    ent (walkGenRowsBE ptr k y α γ H rI cert cs ws kr).1 i c =
      ent (walkGenRowsBE ptr k' y' α' γ' H rI cert cs ws kr).1 i c := by
  unfold walkGenRowsBE
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  by_cases hw : c < 166
  · rw [dif_pos hw, dif_pos hw]
    have hb := getD_map_P (ws.zipIdx 0) (fun x => walkDBE ptr k y H rI cs x.1 x.2)
      (fun x => walkDBE ptr k' y' H rI cs x.1 x.2) wbD
      (walkDBE ptr k y H rI cs (ws.getD ((List.range ws.length)[i]) ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩)
        ((List.range ws.length)[i]))
      (walkDBE ptr k' y' H rI cs (ws.getD ((List.range ws.length)[i]) ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩)
        ((List.range ws.length)[i])) (wbD_walkDBE _ _ _ _ _ _ _ _ _ _)
      (fun a => wbD_walkDBE _ _ _ _ _ _ _ _ _ _) ((List.range ws.length)[i])
    refine walkColBE_r1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨c, hw⟩ ?_ hb
    rcases hc with hc | ⟨hc, hz, hy⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, getD_map_P (ws.zipIdx 0) (fun x => walkDBE ptr k y H rI cs x.1 x.2)
        (fun x => walkDBE ptr k' y' H rI cs x.1 x.2) wfD _ _ (wfD_walkDBE _ _ _ _ _ hz hy _ _ _ _ _)
        (fun a => wfD_walkDBE _ _ _ _ _ hz hy _ _ _ _ _) _⟩
  · rw [dif_neg hw, dif_neg hw]

/-! ## 8. The atom table -/

theorem atomColD_eq (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d : CellD) (va xa ha : K6) (ai : AInfo)
    (roles : ℕ → K3) (c : ℕ) :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c =
      if c < 130 then cellColD D mv mx mx1 mh d va xa ha c
      else if c < 162 then bitZ (atomV d.l) (c - 130)
      else if c < 194 then bitZ (if d.r.isCell then 0 else atomV d.r) (c - 162)
      else if c = 194 then (if d.r.isCell then 0 else (((if d.r.isCell then 0 else atomV d.r : ℕ)) : ZMod P)⁻¹)
      else if c = 195 then ((atomV d.l : ℕ) : ZMod P)⁻¹
      else if c = 196 then (mb : ZMod P)
      else if c = 197 then flag ai.inc else if c = 198 then flag ai.conv else if c = 199 then flag ai.cout
      else if c = 200 then (ai.idxO : ZMod P) else if c = 201 then (ai.lO : ZMod P)
      else if c = 202 then (ai.kRO : ZMod P) else if c = 203 then (ai.vRO : ZMod P)
      else if c = 204 then (ai.mi : ZMod P)
      else if c < 301 then cellColD D mv mx mx1 mh d va xa ha (c - 205 + 134)
      else if c < 313 then cellColD D mv mx mx1 mh d va xa ha (c - 301 + 230)
      else if c < 349 then limbZ (roles ((c - 313) / 3)) ((c - 313) % 3)
      else 0 := rfl

theorem atomColD_r0 (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d d' : CellD) (va xa ha va' xa' ha' : K6)
    (ai : AInfo) (roles roles' : ℕ → K3) (c : ℕ) (hc : c < 205) (h : cbD d = cbD d') :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c = atomColD D mv mx mx1 mh mb d' va' xa' ha' ai roles' c := by
  rw [atomColD_eq, atomColD_eq]
  by_cases h1 : c < 130
  · rw [if_pos h1, if_pos h1]; exact cellColD_r0 D mv mx mx1 mh d d' va xa ha va' xa' ha' c (by omega) h
  rw [if_neg h1, if_neg h1]
  obtain ⟨j, l, r, pE, lE, rE, mu, muL, muR, idL, idR, _⟩ := d
  obtain ⟨j', l', r', pE', lE', rE', mu', muL', muR', idL', idR', _⟩ := d'
  simp only [cbD, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  iterate 13 refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  exact absurd hc (by omega)

theorem atomColD_r1 (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d d' : CellD) (va xa ha va' xa' ha' : K6)
    (ai : AInfo) (roles roles' : ℕ → K3) (c : ℕ) (hc : c < 205 ∨ (c < 259 ∧ cfD d = cfD d'))
    (h : cbD d = cbD d') :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c = atomColD D mv mx mx1 mh mb d' va' xa' ha' ai roles' c := by
  rcases hc with hc | ⟨hc, hf⟩
  · exact atomColD_r0 D mv mx mx1 mh mb d d' va xa ha va' xa' ha' ai roles roles' c hc h
  by_cases h0 : c < 205
  · exact atomColD_r0 D mv mx mx1 mh mb d d' va xa ha va' xa' ha' ai roles roles' c h0 h
  rw [atomColD_eq, atomColD_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  exact cellColD_r1 D mv mx mx1 mh d d' va xa ha va' xa' ha' _ (by omega) h hf

theorem cbD_cellDE (ptr : Noun → ℕ) (k k' : Co) (y y' : K6) (acsL : List Noun) (n : Noun) (j : ℕ) :
    cbD (cellDE ptr k y acsL n j) = cbD (cellDE ptr k' y' acsL n j) := by
  unfold cellDE; split_ifs <;> rfl

theorem cfD_cellDE (ptr : Noun → ℕ) (k k' : Co) (y y' : K6) (hz : k.z = k'.z) (hy : y = y') (acsL : List Noun)
    (n : Noun) (j : ℕ) : cfD (cellDE ptr k y acsL n j) = cfD (cellDE ptr k' y' acsL n j) := by
  have e : ∀ (k : Co) (y : K6), cfD (cellDE ptr k y acsL n j) = cfD (cellD k y acsL n j) := fun k y => by
    unfold cellDE; split <;> rfl
  rw [e, e]; unfold cfD cellD; rw [hz, hy]

/-- The atom table's entries in columns `< 259` read only the fingerprint coins `((coOfA χ).z, yE χ)`; in columns
`< 205` nothing. -/
theorem atomGenE_ent (ptr : Noun → ℕ) (χ χ' : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ)
    (i c : ℕ) (hc : c < 205 ∨ (c < 259 ∧ yE χ = yE χ')) :
    ent (atomGenE ptr χ acsL info mb mxA mhA).1 i c = ent (atomGenE ptr χ' acsL info mb mxA mhA).1 i c := by
  unfold atomGenE
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  split_ifs with hw
  · have hb := getD_map_P (acsL.zipIdx 0) (fun x => cellDE ptr (coOfA χ) (yE χ) acsL x.1 x.2)
      (fun x => cellDE ptr (coOfA χ') (yE χ') acsL x.1 x.2) cbD
      (cellDE ptr (coOfA χ) (yE χ) acsL (.atom 0) ((List.range acsL.length)[i]))
      (cellDE ptr (coOfA χ') (yE χ') acsL (.atom 0) ((List.range acsL.length)[i])) (cbD_cellDE _ _ _ _ _ _ _ _)
      (fun a => cbD_cellDE _ _ _ _ _ _ _ _) ((List.range acsL.length)[i])
    refine atomColD_r1 (c := c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ hb
    rcases hc with hc | ⟨hc, hy⟩
    · exact Or.inl hc
    · have hz : (coOfA χ).z = (coOfA χ').z := hy
      exact Or.inr ⟨hc, getD_map_P (acsL.zipIdx 0) (fun x => cellDE ptr (coOfA χ) (yE χ) acsL x.1 x.2)
        (fun x => cellDE ptr (coOfA χ') (yE χ') acsL x.1 x.2) cfD _ _ (cfD_cellDE _ _ _ _ _ hz hy _ _ _)
        (fun a => cfD_cellDE _ _ _ _ _ hz hy _ _ _) _⟩
  · rfl

/-! ## 9. The axis and split chips (round 0 only) -/

theorem getD_toArray_append_left (l1 l2 : List (ZMod p)) (c : ℕ) (h : c < l1.length) :
    (l1 ++ l2).toArray.getD c 0 = l1.getD c 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left h, List.getD_eq_getElem?_getD]

theorem getD_toArray_append_right (l1 l2 : List (ZMod p)) (c : ℕ) (h : l1.length ≤ c) :
    (l1 ++ l2).toArray.getD c 0 = l2.getD (c - l1.length) 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right h, List.getD_eq_getElem?_getD]

theorem axRows_ent (χ χ' : CoinsE) (rows : List (ComplJ9AAxisRows.ARow (ZMod p))) (i c : ℕ) (hc : c < 22) :
    ent (GenAxE.axRows χ rows) i c = ent (GenAxE.axRows χ' rows) i c := by
  unfold GenAxE.axRows
  rw [List.map_toArray, List.map_toArray]
  refine ent_congr _ _ _ _ i c (by simp [GenAxE.qvRows]) fun h1 h2 => ?_
  rw [List.getElem_zip, List.getElem_zip]
  dsimp only
  rw [getD_toArray_append_left _ _ _ (by simpa using hc), getD_toArray_append_left _ _ _ (by simpa using hc)]

theorem axGenOf_ent (χ χ' : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ) (rows9 : Array ComplJ9AGen.LX9) (on : Bool)
    (i c : ℕ) (hc : c < 22) :
    ent (GenAxE.axGenOf χ nA H rows9 on).1 i c = ent (GenAxE.axGenOf χ' nA H rows9 on).1 i c := by
  unfold GenAxE.axGenOf
  split
  · exact axRows_ent χ χ' _ i c hc
  · rfl

theorem spGenE_ent (χ χ' : CoinsE) (nA : ℕ) (vS mS : List ℕ) (i c : ℕ) (hc : c < 72) :
    ent (GenSpE.spGenE χ nA vS mS).1 i c = ent (GenSpE.spGenE χ' nA vS mS).1 i c := by
  unfold GenSpE.spGenE
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  by_cases hw : c < 90
  · rw [dif_pos hw, dif_pos hw, if_pos (show ((⟨c, hw⟩ : Fin 90) : ℕ) < 72 from hc),
      if_pos (show ((⟨c, hw⟩ : Fin 90) : ℕ) < 72 from hc)]
  · rw [dif_neg hw, dif_neg hw]

/-! ## 10. The ALU chip -/

theorem roleLimbs_append (l1 l2 : List K6) :
    GenAxE.roleLimbs l1 ++ GenAxE.roleLimbs l2 = GenAxE.roleLimbs (l1 ++ l2) := by
  unfold GenAxE.roleLimbs; rw [List.flatMap_append, List.flatMap_append]

theorem roleLimbs9 (a1 a2 a3 a4 a5 a6 a7 a8 a9 : K6) (t t' : List K6) (j : ℕ) (hj : j < 54) :
    (GenAxE.roleLimbs (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: t)).getD j 0 =
      (GenAxE.roleLimbs (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: t')).getD j 0 := by
  have hl : (GenAxE.roleLimbs [a1, a2, a3, a4, a5, a6, a7, a8, a9]).length = 54 := rfl
  change (GenAxE.roleLimbs ([a1, a2, a3, a4, a5, a6, a7, a8, a9] ++ t)).getD j 0 =
    (GenAxE.roleLimbs ([a1, a2, a3, a4, a5, a6, a7, a8, a9] ++ t')).getD j 0
  rw [← roleLimbs_append, ← roleLimbs_append, List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega)]

/-- The ALU table's entries in columns `< 148` read only `yE χ`; in columns `< 94` nothing. -/
theorem aluGenE_ent (χ χ' : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (prims : List (ℕ × PrimOp))
    (ids : List ℕ) (pc : List (ℕ × Noun × Noun)) (i c : ℕ) (hc : c < 94 ∨ (c < 148 ∧ yE χ = yE χ')) :
    ent (GenAluE.aluGenE χ cs Hm prims ids pc).1 i c = ent (GenAluE.aluGenE χ' cs Hm prims ids pc).1 i c := by
  unfold GenAluE.aluGenE
  dsimp only
  rcases hc with hc | ⟨hc, hy⟩
  · rw [List.map_toArray, List.map_toArray]
    refine ent_congr _ _ _ _ i c (by simp) fun h1 h2 => ?_
    rw [List.getElem_zip, List.getElem_zip]
    dsimp only
    rw [getD_toArray_append_left _ _ _ (by simpa using hc), getD_toArray_append_left _ _ _ (by simpa using hc)]
  · by_cases h0 : c < 94
    · rw [List.map_toArray, List.map_toArray]
      refine ent_congr _ _ _ _ i c (by simp) fun h1 h2 => ?_
      rw [List.getElem_zip, List.getElem_zip]
      dsimp only
      rw [getD_toArray_append_left _ _ _ (by simpa using h0), getD_toArray_append_left _ _ _ (by simpa using h0)]
    rw [hy, List.map_toArray, List.map_toArray]
    refine ent_congr _ _ _ _ i c (by simp) fun h1 h2 => ?_
    rw [List.getElem_zip, List.getElem_zip]
    dsimp only
    rw [getD_toArray_append_right _ _ _ (by simp; omega), getD_toArray_append_right _ _ _ (by simp; omega)]
    exact roleLimbs9 _ _ _ _ _ _ _ _ _ _ _ _ (by simp; omega)

/-! ## 11. The J chip -/

theorem jColD_lo (χ χ' : CoinsE) (n i : ℕ) (r : Nock.Jet.ChipJ8.CRow (ZMod P)) (aT aX aT' aX' : K6) (c : ℕ) (hc : c < 29) :
    jColD χ n i r aT aX c = jColD χ' n i r aT' aX' c := by
  rw [jColD, jColD]
  by_cases h : c < 18
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_pos hc, if_pos hc]

theorem jGen_ent0 (χ χ' : CoinsE) (rows : List (Nock.Jet.ChipJ8.CRow (ZMod P))) (i c : ℕ) (hc : c < 29) :
    ent (jGen χ rows).1 i c = ent (jGen χ' rows).1 i c := by
  unfold jGen
  dsimp only
  refine ent_congr _ _ _ _ i c rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  by_cases hw : c < 71
  · rw [dif_pos hw, dif_pos hw]; exact jColD_lo _ _ _ _ _ _ _ _ _ _ hc
  · rw [dif_neg hw, dif_neg hw]

theorem jGen_eq (χ χ' : CoinsE) (hγ : γHE χ = γHE χ') (hρ : ρHE χ = ρHE χ') (rows : List (Nock.Jet.ChipJ8.CRow (ZMod P))) :
    jGen χ rows = jGen χ' rows := by
  have hd : dKey χ = dKey χ' := by funext m κ; unfold dKey; rw [hγ, hρ]
  have hs : sTE χ = sTE χ' := by funext es r; unfold sTE; rw [hd]
  have hx : sXE χ = sXE χ' := by funext r; unfold sXE; rw [hd]
  have ht : termE χ = termE χ' := by funext r; unfold termE; rw [hs]
  have hq : qvE χ = qvE χ' := by funext r aT aX t; unfold qvE; rw [hs, hx]
  have hj : jColD χ = jColD χ' := by funext n i r aT aX c; unfold jColD; rw [hq]
  unfold jGen; rw [ht, hx, hj]

/-! ## 12. The compute twin -/

theorem compColD9_lo (b : ℕ → ZMod P) (iv : Array K6) (a : Array (ZMod P)) (v : K3 × K3 × K3 × K3) (d : ℕ)
    (hd : d < 83) : GenCompX9.compColD9 b iv a v (ComplJ9ACompRow.invPermX9 d) = b (ComplJ9ACompRow.invPermX9 d) := by
  have h : ComplJ9ACompRow.invPermX9 d < 69 ∨ 123 ≤ ComplJ9ACompRow.invPermX9 d := by
    unfold ComplJ9ACompRow.invPermX9; split_ifs <;> omega
  rw [GenCompX9.compColD9, if_pos h]

theorem compGenX9_ent0 (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idOf : ℕ → ℕ) (W : List (NTree ComplJ9AGen.LX9)) (χ χ' : CoinsE) (i d : ℕ) (hd : d < 83) :
    ent (GenCompX9.compGenX9 c H pd idOf W χ).rows i d = ent (GenCompX9.compGenX9 c H pd idOf W χ').rows i d := by
  unfold GenCompX9.compGenX9 GenCompX9.compTable9
  dsimp only
  refine ent_congr _ _ _ _ i d rfl fun h1 h2 => ?_
  rw [getD_ofFn, getD_ofFn]
  by_cases hw : d < 137
  · rw [dif_pos hw, dif_pos hw, compColD9_lo _ _ _ _ _ hd, compColD9_lo _ _ _ _ _ hd]
  · rw [dif_neg hw, dif_neg hw]

theorem compGenX9_eq (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idOf : ℕ → ℕ) (W : List (NTree ComplJ9AGen.LX9)) (χ χ' : CoinsE)
    (h11 : χ ⟨11, by decide⟩ = χ' ⟨11, by decide⟩) (h12 : χ ⟨12, by decide⟩ = χ' ⟨12, by decide⟩)
    (h13 : χ ⟨13, by decide⟩ = χ' ⟨13, by decide⟩) (h14 : χ ⟨14, by decide⟩ = χ' ⟨14, by decide⟩)
    (h15 : χ ⟨15, by decide⟩ = χ' ⟨15, by decide⟩) (h16 : χ ⟨16, by decide⟩ = χ' ⟨16, by decide⟩) :
    GenCompX9.compGenX9 c H pd idOf W χ = GenCompX9.compGenX9 c H pd idOf W χ' := by
  have hcoin : coinHQE χ = coinHQE χ' := by funext q; unfold coinHQE; rw [h11, h12, h13, h14, h15, h16]
  have hc : Example.chalE χ = Example.chalE χ' := by funext j; unfold Example.chalE chalVJ8E; rw [hcoin]
  have hp : ∀ m r1 r2, Nock.V1J9.Check9.pubVJ9E c m r1 r2 χ = Nock.V1J9.Check9.pubVJ9E c m r1 r2 χ' := by
    intro m r1 r2; funext j
    unfold Nock.V1J9.Check9.pubVJ9E Nock.V1J9.Check9.seedJ9E pubVJ8E seedE
    rw [h13, h14]
  unfold GenCompX9.compGenX9 GenCompX9.compTable9 GenCompX9.totals9 GenCompX9.envX9
  simp only [hc, hp, h13, h14]

/-! ## 13. Coins agreeing on the round-0 squeeze -/

/-- `χ` and `χ'` agree on the coins drawn after round 0 (`idxS0`). -/
def Agree0 (χ χ' : CoinsE) : Prop := ∀ k : Fin 13, χ (s0 k) = χ' (s0 k)

section Agree
variable {χ χ' : CoinsE}

theorem agree0_zE (h : Agree0 χ χ') : zE χ = zE χ' := by
  unfold zE; rw [show χ c2 = χ' c2 from h 0, show χ c3 = χ' c3 from h 1]
theorem agree0_yE (h : Agree0 χ χ') : yE χ = yE χ' := by
  unfold yE; rw [show χ cY1 = χ' cY1 from h 11, show χ cY2 = χ' cY2 from h 12]
theorem agree0_γHE (h : Agree0 χ χ') : γHE χ = γHE χ' := by
  unfold γHE; rw [show χ ⟨11, by decide⟩ = χ' ⟨11, by decide⟩ from h 5,
    show χ ⟨15, by decide⟩ = χ' ⟨15, by decide⟩ from h 9]
theorem agree0_ρHE (h : Agree0 χ χ') : ρHE χ = ρHE χ' := by
  unfold ρHE; rw [show χ ⟨12, by decide⟩ = χ' ⟨12, by decide⟩ from h 6,
    show χ ⟨16, by decide⟩ = χ' ⟨16, by decide⟩ from h 10]

end Agree

theorem cr3_zero {a b c : ℕ} (h : cr3 a b c = 0) : c < a := by
  unfold cr3 at h; split_ifs at h with h1 h2 <;> first | assumption | simp at h
theorem cr3_one {a b c : ℕ} (h : cr3 a b c = 1) : c < b := by
  unfold cr3 at h; split_ifs at h with h1 h2 <;> first | omega | simp at h

/-! ## 14. The record's chips -/

section Rec
open GenPortJ9AHJRun GenPortJ9ALHJRun
variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (Rn : RunX)

theorem recX (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).X = chipOf (compK Rt s f χ Rn).rows := rfl
theorem recC (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).C = chipOf (cRPLK Rt prims s f χ Rn).1 := rfl
theorem recW (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).W = chipOf (wRPK Rt s f χ Rn).1 := rfl
theorem recJ (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).J =
    ⟨hOf (layLK Rt prims s f χ Rn).length, (layLK Rt prims s f χ Rn).length,
      ωOf (hOf (layLK Rt prims s f χ Rn).length), colsOf (jgLK Rt prims s f χ Rn).1 (layLK Rt prims s f χ Rn).length⟩ :=
  rfl
theorem recA (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).A = chipOf (aRPLK Rt prims s f χ Rn).1 := rfl
theorem recV (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).V = chipOf (vRPK Rt s f χ Rn).1 := rfl
theorem recAX (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).AX = chipOf (xRPK Rt s f χ Rn).1 := rfl
theorem recSP (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).SP = chipOf (sRPK Rt s f χ Rn).1 := rfl
theorem recAL (χ : CoinsE) : (recJ9ALXJRn Rt prims s f χ Rn).AL = chipOf (lRPLK Rt prims s f χ Rn).1 := rfl

theorem compK_bases (χ χ' : CoinsE) : (compK Rt s f χ Rn).bases = (compK Rt s f χ' Rn).bases := rfl

theorem mhLK_coin (χ χ' : CoinsE) : mhLK Rt prims s f χ Rn = mhLK Rt prims s f χ' Rn := by
  unfold mhLK; rw [compK_bases Rt s f Rn χ χ']; rfl

/-! Per chip: round 0 coin-free, round 1 fixed by the round-0 squeeze. -/

theorem X_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 83) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).X c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).X c i := by
  rw [recX, recX, getN_chipOf, getN_chipOf]; unfold compK; exact compGenX9_ent0 _ _ _ _ _ _ _ i c hc

theorem X_r1 (χ χ' : CoinsE) (h : Agree0 χ χ') (c i : ℕ) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).X c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).X c i := by
  rw [recX, recX]; unfold compK
  rw [compGenX9_eq _ _ _ _ _ χ χ' (h 5) (h 6) (h 7) (h 8) (h 9) (h 10)]
  rfl

theorem C_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 134 ∨ (c < 188 ∧ Agree0 χ χ')) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).C c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).C c i := by
  rw [recC, recC, getN_chipOf, getN_chipOf]; unfold cRPLK
  rw [mhLK_coin Rt prims s f Rn χ χ']
  refine cellGenB_ent _ _ _ _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_zE h, agree0_yE h⟩

theorem W_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 25 ∨ (c < 97 ∧ Agree0 χ χ')) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).W c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).W c i := by
  rw [recW, recW, getN_chipOf, getN_chipOf]; unfold wRPK
  refine walkGenRowsB_ent _ _ _ _ _ _ _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_zE h, agree0_yE h⟩

theorem J_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 29) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).J c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).J c i := by
  rw [recJ, recJ, getN_colsOf, getN_colsOf]
  show (if i < (layLK Rt prims s f χ Rn).length then ent (jgLK Rt prims s f χ Rn).1 i c else 0) =
    (if i < (layLK Rt prims s f χ Rn).length then ent (jgLK Rt prims s f χ' Rn).1 i c else 0)
  unfold jgLK
  rw [jGen_ent0 χ χ' _ i c hc]
  rfl

theorem J_r1 (χ χ' : CoinsE) (h : Agree0 χ χ') (c i : ℕ) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).J c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).J c i := by
  rw [recJ, recJ]; unfold jgLK
  rw [jGen_eq χ χ' (agree0_γHE h) (agree0_ρHE h)]
  rfl

theorem A_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 205 ∨ (c < 259 ∧ Agree0 χ χ')) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).A c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).A c i := by
  rw [recA, recA, getN_chipOf, getN_chipOf]; unfold aRPLK
  refine atomGenE_ent _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_yE h⟩

theorem V_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 25 ∨ (c < 97 ∧ Agree0 χ χ')) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).V c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).V c i := by
  rw [recV, recV, getN_chipOf, getN_chipOf]; unfold vRPK
  rw [show vsKrVK Rt s f χ' Rn = vsKrVK Rt s f χ Rn from rfl]
  split
  · rfl
  · refine walkGenRowsBE_ent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i c ?_
    rcases hc with hc | ⟨hc, h⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, agree0_yE h, agree0_yE h⟩

theorem AX_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 22) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).AX c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).AX c i := by
  rw [recAX, recAX, getN_chipOf, getN_chipOf]; unfold xRPK
  exact axGenOf_ent _ _ _ _ _ _ i c hc

theorem SP_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 72) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).SP c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).SP c i := by
  rw [recSP, recSP, getN_chipOf, getN_chipOf]; unfold sRPK
  rw [show GenPortJ9AHProj.spOnJ s f χ' Rn = GenPortJ9AHProj.spOnJ s f χ Rn from rfl]
  split
  · exact spGenE_ent _ _ _ _ _ i c hc
  · rfl

theorem AL_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 94 ∨ (c < 148 ∧ Agree0 χ χ')) :
    getN (recJ9ALXJRn Rt prims s f χ Rn).AL c i = getN (recJ9ALXJRn Rt prims s f χ' Rn).AL c i := by
  rw [recAL, recAL, getN_chipOf, getN_chipOf]; unfold lRPLK
  rw [show aluOnLK Rt prims s f χ' Rn = aluOnLK Rt prims s f χ Rn from rfl]
  split
  · refine aluGenE_ent _ _ _ _ _ _ _ i c ?_
    rcases hc with hc | ⟨hc, h⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, agree0_yE h⟩
  · rfl

/-- **The staged record**: the three round blocks at `assemble 0 0`, `assemble a 0`, `assemble a b` and the rest
at `assemble a b` assemble to the record at `assemble a b`. -/
theorem staged_rec (a : Coins0) (b : Coins1) :
    assembleI (blkOf 0 (recJ9ALXJRn Rt prims s f (assemble 0 0) Rn))
      (blkOf 1 (recJ9ALXJRn Rt prims s f (assemble a 0) Rn))
      (blkOf 2 (recJ9ALXJRn Rt prims s f (assemble a b) Rn))
      (blankL (recJ9ALXJRn Rt prims s f (assemble a b) Rn)) = recJ9ALXJRn Rt prims s f (assemble a b) Rn := by
  have hA : Agree0 (assemble a 0) (assemble a b) := fun k => by
    have e1 := congrFun (c0_assemble a 0) k
    have e2 := congrFun (c0_assemble a b) k
    exact e1.trans e2.symm
  refine assembleI_blankL _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => X_r0 Rt prims s f Rn _ _ c i (cr3_zero h))
      (fun c i h => X_r1 Rt prims s f Rn _ _ hA c i)
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => C_r1 Rt prims s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => C_r1 Rt prims s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => W_r1 Rt prims s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => W_r1 Rt prims s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => J_r0 Rt prims s f Rn _ _ c i (cr3_zero h))
      (fun c i h => J_r1 Rt prims s f Rn _ _ hA c i)
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => A_r1 Rt prims s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => A_r1 Rt prims s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => V_r1 Rt prims s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => V_r1 Rt prims s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_r0 Rt prims s f Rn _ _ c i (cr3_zero h))
      (fun c i h => absurd (cr3_one h) (by unfold cr3 at h; split_ifs at h <;> simp_all))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => SP_r0 Rt prims s f Rn _ _ c i (cr3_zero h))
      (fun c i h => absurd (cr3_one h) (by unfold cr3 at h; split_ifs at h <;> simp_all))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AL_r1 Rt prims s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => AL_r1 Rt prims s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))

end Rec

/-! ## 15. The composition theorem -/

/-- **`runStaged_assemble`: the staged J-9 AL generator at any pair of coin stages `(a, b)` equals the one-shot
generator `genJ9ALXJ` at the coin vector `assemble a b`.**  The staged generator runs the program once, then
builds the round-0 blocks from the stage-0 coins `a` only and the round-1 blocks from `a` and the stage-1 coins `b`;
the equality holds as `Option`s (both fail together, or both return the same input), for every registry, template
table, primitive list, fuel and initial subject and formula. -/
theorem runStaged_assemble (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp))
    (fuel : ℕ) (s f : Noun) (a : Coins0) (b : Coins1) :
    runStaged R Rt prims fuel s f a b = GenJ9ALXJ.genJ9ALXJ R Rt prims fuel s f (assemble a b) := by
  rw [GenPortJ9ALHJRun.genJ9ALXJ_eq]
  unfold runStaged gen0
  cases runX R fuel s f with
  | none => rfl
  | some Rn =>
    show some _ = some _
    congr 1
    exact staged_rec Rt prims s f Rn a b

/-- **`runStaged_eq`: the staged J-9 AL generator, fed the stage-0 and stage-1 slices of any coin vector `χe`,
returns exactly what the one-shot generator `genJ9ALXJ` returns at `χe`.**  Stage 0 takes the coins sampled before
the first commitment round and stage 1 those sampled after it; the equality holds as `Option`s, for every
registry, template table, primitive list, fuel, subject and formula. -/
theorem runStaged_eq (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp))
    (fuel : ℕ) (s f : Noun) (χe : CoinsE) :
    runStaged R Rt prims fuel s f (c0 χe) (c1 χe) = GenJ9ALXJ.genJ9ALXJ R Rt prims fuel s f χe := by
  rw [runStaged_assemble, assemble_c]

/-! ## 16. The corollary: the checker accepts the staged output -/

/-- **`checkJ9ALX_staged`: the executable J-9 AL checker accepts the staged generator's output.**
Under the hypotheses of `checkJ9ALX_genJ9ALXJ` (Goldilocks prime, J-9 A axis, op-5, leaf and walk-depth conditions,
`CompiledByP` with distinct primitive ids, every table of at most `2^31` rows (ALU length `< 2^31`), primitive operands within 62 limbs,
no decrement primitive), if the staged generator returns `I` from the stage coins `(a, b)` and the assembled coin
vector `assemble a b` is good, then `checkJ9ALX I = true`. -/
theorem checkJ9ALX_staged [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
    [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
    {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : P = Nock.Atoms.p) {Rt0 : ℕ → Nock.Jet.Autogen.Tpl} {prims : List (ℕ × PrimOp)}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg (ComplJ9ALData.rtP Rt0 prims) hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg (ComplJ9ALData.rtP Rt0 prims) hgen).preads)
    (hC : CheckedRegistryP.CompiledByP P Rg Rt0 prims) (hnd : (prims.map Prod.fst).Nodup)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg (ComplJ9ALData.rtP Rt0 prims) hgen))
    (h31L : ComplJ9ALRun.aluLen (K := KC) deltaF (ComplJ9ALData.rtP Rt0 prims) hgen prims < 2 ^ 31)
    (hlimb : AluCallOK.PrimLimbs62 (prims.map Prod.fst) t) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    {a : Coins0} {b : Coins1} {I : InJ9AL}
    (hI : runStaged Rg.R (ComplJ9ALData.rtP Rt0 prims) prims fuel s f a b = some I)
    (hχ : (ComplJ9ALClosed.BRun9AL deltaF powerBasis3 (ComplJ9ALData.rtP Rt0 prims) hgen prims hpG h31A).Good
      (toχ (assemble a b))) :
    checkJ9ALX I = true :=
  GenPortJ9ALHonestJ.checkJ9ALX_genJ9ALXJ hgen hpG hax9 hop5 hleaf hwalk9 hwalkA hC hnd h31A h31L hlimb hnoDec
    ((runStaged_assemble _ _ _ _ _ _ a b).symm.trans hI) hχ

open Nock.V1J9A.CheckJ9A (InJ9A)

/-! ## 17. The same for J-9 A (`genJ9AXJ`) -/

theorem assembleIA_blankA (I : InJ9A) (b0 b1 b2 : BlkA)
    (hX : mergeCols 83 137 b0.X b1.X b2.X I.X.n = I.X.cols)
    (hC : mergeCols 134 188 b0.C b1.C b2.C I.C.n = I.C.cols)
    (hW : mergeCols 25 97 b0.W b1.W b2.W I.W.n = I.W.cols)
    (hJ : mergeCols 29 71 b0.J b1.J b2.J I.J.n = I.J.cols)
    (hA : mergeCols 205 259 b0.A b1.A b2.A I.A.n = I.A.cols)
    (hV : mergeCols 25 97 b0.V b1.V b2.V I.V.n = I.V.cols)
    (hAX : mergeCols 22 22 b0.AX b1.AX b2.AX I.AX.n = I.AX.cols)
    (hSP : mergeCols 72 72 b0.SP b1.SP b2.SP I.SP.n = I.SP.cols) :
    assembleIA b0 b1 b2 (blankA I) = I := by
  obtain ⟨⟨c, M, χ, r, g, X, C, W, J, A, V, kr, krV, lay, Rt, regs, ids, idx, rk⟩, AX, SP, pX, pS, axOn, spOn,
    rAX, rSP⟩ := I
  obtain ⟨Xh, Xn, Xω, Xc⟩ := X
  obtain ⟨Ch, Cn, Cω, Cc⟩ := C
  obtain ⟨Wh, Wn, Wω, Wc⟩ := W
  obtain ⟨Jh, Jn, Jω, Jc⟩ := J
  obtain ⟨Ah, An, Aω, Ac⟩ := A
  obtain ⟨Vh, Vn, Vω, Vc⟩ := V
  obtain ⟨AXh, AXn, AXω, AXc⟩ := AX
  obtain ⟨SPh, SPn, SPω, SPc⟩ := SP
  dsimp only at hX hC hW hJ hA hV hAX hSP
  unfold assembleIA blankA mergeC blankC
  dsimp only
  rw [hX, hC, hW, hJ, hA, hV, hAX, hSP]

section RecA
open GenPortJ9AHJRun
variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) (s f : Noun) (Rn : RunX)

theorem recAX' (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).X = chipOf (compK Rt s f χ Rn).rows := rfl
theorem recAC (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).C = chipOf (cRPK Rt s f χ Rn).1 := rfl
theorem recAW (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).W = chipOf (wRPK Rt s f χ Rn).1 := rfl
theorem recAJ (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).J =
    ⟨hOf (layK Rt s f χ Rn).length, (layK Rt s f χ Rn).length,
      ωOf (hOf (layK Rt s f χ Rn).length), colsOf (jgK Rt s f χ Rn).1 (layK Rt s f χ Rn).length⟩ := rfl
theorem recAA (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).A = chipOf (aRPK Rt s f χ Rn).1 := rfl
theorem recAV (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).V = chipOf (vRPK Rt s f χ Rn).1 := rfl
theorem recAAX (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).AX = chipOf (xRPK Rt s f χ Rn).1 := rfl
theorem recASP (χ : CoinsE) : (recJ9AXJRn Rt s f χ Rn).SP = chipOf (sRPK Rt s f χ Rn).1 := rfl

theorem mhK_coin (χ χ' : CoinsE) : mhK Rt s f χ Rn = mhK Rt s f χ' Rn := by
  unfold mhK; rw [compK_bases Rt s f Rn χ χ']; rfl

theorem AX_X_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 83) :
    getN (recJ9AXJRn Rt s f χ Rn).X c i = getN (recJ9AXJRn Rt s f χ' Rn).X c i := by
  rw [recAX', recAX', getN_chipOf, getN_chipOf]; unfold compK; exact compGenX9_ent0 _ _ _ _ _ _ _ i c hc

theorem AX_X_r1 (χ χ' : CoinsE) (h : Agree0 χ χ') (c i : ℕ) :
    getN (recJ9AXJRn Rt s f χ Rn).X c i = getN (recJ9AXJRn Rt s f χ' Rn).X c i := by
  rw [recAX', recAX']; unfold compK
  rw [compGenX9_eq _ _ _ _ _ χ χ' (h 5) (h 6) (h 7) (h 8) (h 9) (h 10)]
  rfl

theorem AX_C_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 134 ∨ (c < 188 ∧ Agree0 χ χ')) :
    getN (recJ9AXJRn Rt s f χ Rn).C c i = getN (recJ9AXJRn Rt s f χ' Rn).C c i := by
  rw [recAC, recAC, getN_chipOf, getN_chipOf]; unfold cRPK
  rw [mhK_coin Rt s f Rn χ χ']
  refine cellGenB_ent _ _ _ _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_zE h, agree0_yE h⟩

theorem AX_W_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 25 ∨ (c < 97 ∧ Agree0 χ χ')) :
    getN (recJ9AXJRn Rt s f χ Rn).W c i = getN (recJ9AXJRn Rt s f χ' Rn).W c i := by
  rw [recAW, recAW, getN_chipOf, getN_chipOf]; unfold wRPK
  refine walkGenRowsB_ent _ _ _ _ _ _ _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_zE h, agree0_yE h⟩

theorem AX_J_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 29) :
    getN (recJ9AXJRn Rt s f χ Rn).J c i = getN (recJ9AXJRn Rt s f χ' Rn).J c i := by
  rw [recAJ, recAJ, getN_colsOf, getN_colsOf]
  show (if i < (layK Rt s f χ Rn).length then ent (jgK Rt s f χ Rn).1 i c else 0) =
    (if i < (layK Rt s f χ Rn).length then ent (jgK Rt s f χ' Rn).1 i c else 0)
  unfold jgK
  rw [jGen_ent0 χ χ' _ i c hc]
  rfl

theorem AX_J_r1 (χ χ' : CoinsE) (h : Agree0 χ χ') (c i : ℕ) :
    getN (recJ9AXJRn Rt s f χ Rn).J c i = getN (recJ9AXJRn Rt s f χ' Rn).J c i := by
  rw [recAJ, recAJ]; unfold jgK
  rw [jGen_eq χ χ' (agree0_γHE h) (agree0_ρHE h)]
  rfl

theorem AX_A_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 205 ∨ (c < 259 ∧ Agree0 χ χ')) :
    getN (recJ9AXJRn Rt s f χ Rn).A c i = getN (recJ9AXJRn Rt s f χ' Rn).A c i := by
  rw [recAA, recAA, getN_chipOf, getN_chipOf]; unfold aRPK
  refine atomGenE_ent _ _ _ _ _ _ _ _ i c ?_
  rcases hc with hc | ⟨hc, h⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, agree0_yE h⟩

theorem AX_V_r1 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 25 ∨ (c < 97 ∧ Agree0 χ χ')) :
    getN (recJ9AXJRn Rt s f χ Rn).V c i = getN (recJ9AXJRn Rt s f χ' Rn).V c i := by
  rw [recAV, recAV, getN_chipOf, getN_chipOf]; unfold vRPK
  rw [show vsKrVK Rt s f χ' Rn = vsKrVK Rt s f χ Rn from rfl]
  split
  · rfl
  · refine walkGenRowsBE_ent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i c ?_
    rcases hc with hc | ⟨hc, h⟩
    · exact Or.inl hc
    · exact Or.inr ⟨hc, agree0_yE h, agree0_yE h⟩

theorem AX_AX_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 22) :
    getN (recJ9AXJRn Rt s f χ Rn).AX c i = getN (recJ9AXJRn Rt s f χ' Rn).AX c i := by
  rw [recAAX, recAAX, getN_chipOf, getN_chipOf]; unfold xRPK
  exact axGenOf_ent _ _ _ _ _ _ i c hc

theorem AX_SP_r0 (χ χ' : CoinsE) (c i : ℕ) (hc : c < 72) :
    getN (recJ9AXJRn Rt s f χ Rn).SP c i = getN (recJ9AXJRn Rt s f χ' Rn).SP c i := by
  rw [recASP, recASP, getN_chipOf, getN_chipOf]; unfold sRPK
  rw [show GenPortJ9AHProj.spOnJ s f χ' Rn = GenPortJ9AHProj.spOnJ s f χ Rn from rfl]
  split
  · exact spGenE_ent _ _ _ _ _ i c hc
  · rfl

theorem staged_recA (a : Coins0) (b : Coins1) :
    assembleIA (blkOfA 0 (recJ9AXJRn Rt s f (assemble 0 0) Rn))
      (blkOfA 1 (recJ9AXJRn Rt s f (assemble a 0) Rn))
      (blkOfA 2 (recJ9AXJRn Rt s f (assemble a b) Rn))
      (blankA (recJ9AXJRn Rt s f (assemble a b) Rn)) = recJ9AXJRn Rt s f (assemble a b) Rn := by
  have hA : Agree0 (assemble a 0) (assemble a b) := fun k => by
    have e1 := congrFun (c0_assemble a 0) k
    have e2 := congrFun (c0_assemble a b) k
    exact e1.trans e2.symm
  refine assembleIA_blankA _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_X_r0 Rt s f Rn _ _ c i (cr3_zero h))
      (fun c i h => AX_X_r1 Rt s f Rn _ _ hA c i)
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_C_r1 Rt s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => AX_C_r1 Rt s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_W_r1 Rt s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => AX_W_r1 Rt s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_J_r0 Rt s f Rn _ _ c i (cr3_zero h))
      (fun c i h => AX_J_r1 Rt s f Rn _ _ hA c i)
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_A_r1 Rt s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => AX_A_r1 Rt s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_V_r1 Rt s f Rn _ _ c i (Or.inl (cr3_zero h)))
      (fun c i h => AX_V_r1 Rt s f Rn _ _ c i (Or.inr ⟨cr3_one h, hA⟩))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_AX_r0 Rt s f Rn _ _ c i (cr3_zero h))
      (fun c i h => absurd (cr3_one h) (by unfold cr3 at h; split_ifs at h <;> simp_all))
  · exact mergeCols_blk _ _ _ _ _ (fun c i h => AX_SP_r0 Rt s f Rn _ _ c i (cr3_zero h))
      (fun c i h => absurd (cr3_one h) (by unfold cr3 at h; split_ifs at h <;> simp_all))

end RecA

theorem runStagedA_assemble (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (fuel : ℕ) (s f : Noun)
    (a : Coins0) (b : Coins1) :
    runStagedA R Rt fuel s f a b = GenJ9AXJ.genJ9AXJ R Rt fuel s f (assemble a b) := by
  rw [GenPortJ9AHJRun.genJ9AXJ_eq]
  unfold runStagedA gen0A
  cases runX R fuel s f with
  | none => rfl
  | some Rn =>
    show some _ = some _
    congr 1
    exact staged_recA Rt s f Rn a b

/-- **`runStagedA_eq`: the staged J-9 A generator, fed the stage-0 and stage-1 slices of any coin vector `χe`,
returns exactly what the one-shot generator `genJ9AXJ` returns at `χe`** (as `Option`s, for every registry,
template table, fuel, subject and formula). -/
theorem runStagedA_eq (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (fuel : ℕ) (s f : Noun)
    (χe : CoinsE) :
    runStagedA R Rt fuel s f (c0 χe) (c1 χe) = GenJ9AXJ.genJ9AXJ R Rt fuel s f χe := by
  rw [runStagedA_assemble, assemble_c]

/-- **`checkJ9AX_stagedA`: the executable J-9 A checker accepts the staged J-9 A generator's output.**
Under the hypotheses of `checkJ9AX_genJ9AXJ` (Goldilocks prime, J-9 A axis, op-5, leaf and walk-depth conditions,
every table of at most `2^31` rows (ALU length `< 2^31`), registry compiled from `Rt`), if the staged generator returns `I` from the stage
coins `(a, b)` and the assembled coin vector `assemble a b` is good, then `checkJ9AX I = true`. -/
theorem checkJ9AX_stagedA [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
    [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]
    {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : P = Nock.Atoms.p) {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt)
    {a : Coins0} {b : Coins1} {I : InJ9A} (hI : runStagedA Rg.R Rt fuel s f a b = some I)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ (assemble a b))) :
    GenJ9AX.checkJ9AX I = true :=
  GenPortJ9AHonestJ.checkJ9AX_genJ9AXJ hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC
    ((runStagedA_assemble _ _ _ _ _ a b).symm.trans hI) hχ

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged

section Axioms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStaged_assemble
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9ALX_staged
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.runStagedA_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHStaged.checkJ9AX_stagedA
end Axioms
