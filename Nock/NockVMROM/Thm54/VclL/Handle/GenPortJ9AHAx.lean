/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAx.lean

* `axRows_size`, `chipOf_axGenE_n`, `chipOf_zero_n`: row counts (`I.AX.n = nXOf …`);
  * `fullCol_colAx`, `interp_eq_polyAx`: the checker's `interpOf q j` IS `polyAx` at `nodesOf q` (any orbit, any chals),
    for `q = chipOf (axGenE χe cs).1` (rows `i < n` only);
  * `axChipOK_exec`: `AXChipOK` present, by `axChipOK_honest` at `nodesOf q` / `mkOrbit q ho` (never `oA`);
  * `axChipOK_absent`: absent chip, four publics `0`;
  * `axChipOK_genOf`: both cases for `axGenOf χe nA H rows9 on`;
  * `axOK_I`: the statement in the exact shape of `AcceptsJ9A.hAXk` at `mkPbA I hv`, `I.toMsg`, `I.toTr`;
  * `pubsXA_eq`: `pubsXA = K3.toK ∘ (axGenOf …).2` at `toχ χe` (honest data `DA`), `axOn = axOnA t` by `rfl`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK)
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Polynomial
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows (ChainSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH (polyAx colAx)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-! ## 1. Row counts -/

theorem axRows_size (χe : CoinsE) (rows : List (ComplJ9AAxisRows.ARow (ZMod p))) :
    (GenAxE.axRows χe rows).size = rows.length := by
  unfold GenAxE.axRows GenAxE.qvRows
  simp

theorem chipOf_axGenE_n (χe : CoinsE) (cs : List (ChainSpec (ZMod p))) :
    (chipOf (GenAxE.axGenE χe cs).1).n = (ComplJ9AAxisRows.tableRows cs).length := by
  show (GenAxE.axGenE χe cs).1.size = _
  unfold GenAxE.axGenE
  exact axRows_size _ _

theorem chipOf_zero_n :
    (chipOf (GenAxE.zeroChip : Array (Array (ZMod p)) × (ℕ → K3)).1).n = 1 := rfl

/-- `I.AX.n = nXOf …`: the exec axis chip has the honest row count (`nXA = nXOf p (DA).acs.length (DA).H t`). -/
theorem chipOf_axGenOf_n (χe : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ) (t : NTree SkelX) :
    (chipOf (GenAxE.axGenOf χe nA H (ComplJ9AGen.rowsOfT9 t) (ComplJ9ARun.axOnA t)).1).n =
      ComplJ9ARun.nXOf p nA H t := by
  unfold GenAxE.axGenOf ComplJ9ARun.nXOf
  by_cases h : ComplJ9ARun.axOnA t = true
  · rw [if_pos h, if_pos h]
    exact chipOf_axGenE_n _ _
  · rw [if_neg h, if_neg h]
    exact chipOf_zero_n

/-! ## 2. The interpolants -/

/-- `fullCol` of the honest axis column is the column itself (the masks are the first two table columns). -/
theorem fullCol_colAx (χe : CoinsE) (rows : List (ComplJ9AAxisRows.ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n)
    (hn : n = rows.length) (chals : ℕ → KC) (j : ℕ) (hj : j < 52) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol hn0 (colAx deltaF powerBasis3 chals hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn)) j i =
      colAx deltaF powerBasis3 chals hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) j i := by
  by_cases h2 : 2 ≤ j
  · unfold Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol
    rw [if_neg (by omega), if_neg (by omega)]
  · have e : Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol hn0 (colAx deltaF powerBasis3 chals hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn)) j i =
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) j i := by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol]
    rw [e, fullCol_eq_colAt rows hn0 hn]
    unfold colAx
    rw [if_pos (by omega), tableCol_eq_fullCol rows hn0 hn]

/-! ## 3. `AXChipOK` at an arbitrary exec orbit -/

/-- **The present axis chip at the exec orbit.**  `q = chipOf (axGenE χe cs).1`, nodes `nodesOf q`, orbit
`mkOrbit q ho` (whatever `ωOf` is: no `oA`, no choice); the trace is the checker's interpolant of the exec rows. -/
theorem axChipOK_exec (χe : CoinsE) (cs : List (ChainSpec (ZMod p))) (hcs : ∀ c ∈ cs, c.OK)
    (q : ChipIn) (hqc : q = chipOf (GenAxE.axGenE χe cs).1) (ho : OrbOK q) (hn0 : 0 < q.n)
    (hn : q.n = (ComplJ9AAxisRows.tableRows cs).length) (hs : (GenAxE.axGenE χe cs).1.size ≤ 2 ^ 31)
    (hg : ∀ e ∈ ComplJ9AChipsOK.famAX deltaF hn0 cs hn (K := KC), toχ χe ∉ e.ev)
    (chals pubs : ℕ → KC) (hch : chals = VerJ8.chalsMJ8 deltaF (toχ χe))
    (hpub : pubs = fun j => K3.toK (GenAxE.pubsXE χe (ComplJ9AAxisRows.tableRows cs) j))
    (P : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w → (ZMod p)[X])
    (hP : ∀ j, P j = interpOf q (j : ℕ)) :
    AXChipOK deltaF powerBasis3 true hn0 (nodesOf q) (mkOrbit q ho) chals pubs P := by
  have hq3 : q.n ≤ 3 * 2 ^ q.h := by rw [hqc]; exact chipOf_n_le _ hs
  have hinj : Function.Injective (nodesOf q) := nodesOf_inj q ho hq3
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [nodesOf_adj q i hi, mul_comm]; rfl
  have hnp : q.n < p := by
    have h1 : q.n ≤ 2 ^ 31 := by rw [hqc]; exact hs
    have h2 : (2 : ℕ) ^ 31 < p := by norm_num [Nock.Field.p]
    omega
  have hpubs : pubs = ComplJ9AChipsOK.pubsXOf deltaF hn0 cs hn (toχ χe) :=
    hpub.trans (funext fun j => pubsXE_eq χe cs hn0 hn j)
  have hcolq : ∀ (c : ℕ) (i : Fin q.n), c < 52 → q.cols c i =
      colAx deltaF powerBasis3 chals hn0
        (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) c i := by
    intro c i hc
    subst hch
    subst hqc
    exact axGenE_cols χe cs (n := (chipOf (GenAxE.axGenE χe cs).1).n) hn0 hn i c hc
  have hint : ∀ j : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w,
      interpOf q (j : ℕ) = polyAx deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs
        (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) j := by
    intro j
    have hj : (j : ℕ) < 52 := j.2
    unfold polyAx Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.honestQ interpOf
    congr 1
    funext i
    rw [fullCol_colAx χe (ComplJ9AAxisRows.tableRows cs) hn0 hn chals j hj i]
    exact hcolq j i hj
  have hPe : P = polyAx deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs
      (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) := funext fun j => (hP j).trans (hint j)
  rw [hPe]
  subst hch
  subst hpubs
  exact ComplJ9AChipsOK.axChipOK_honest deltaF powerBasis3 hn0 cs hn hcs (nodesOf q) (mkOrbit q ho) hinj hadj hnp
    (toχ χe) hg

/-- **The absent axis chip**: `axOn = false` and the four publics are `0`. -/
theorem axChipOK_absent (q : ChipIn) (ho : OrbOK q) (hn0 : 0 < q.n) (chals pubs : ℕ → KC)
    (hpub : ∀ j, pubs j = 0)
    (P : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w → (ZMod p)[X]) :
    AXChipOK deltaF powerBasis3 false hn0 (nodesOf q) (mkOrbit q ho) chals pubs P :=
  Or.inr ⟨rfl, hpub _, hpub _, hpub _, hpub _⟩

/-! ## 4. Both cases, in the shape of `AcceptsJ9A.hAXk` -/

/-- **`AXChipOK` for `genJ9AX`'s axis chip, present or absent**, at `mkPbA I hv`, `I.toMsg`, `I.toTr`. -/
theorem axOK_I (I : InJ9A) (hv : ValidJ9A I) (χe : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ)
    (rows9 : Array ComplJ9AGen.LX9) (on : Bool)
    (hAX : I.AX = chipOf (GenAxE.axGenOf χe nA H rows9 on).1)
    (hpub : I.pubsX = (GenAxE.axGenOf χe nA H rows9 on).2) (hon : I.axOn = on) (hχ : I.χ = χe)
    (hs : on = true → (GenAxE.axGenOf χe nA H rows9 on).1.size ≤ 2 ^ 31)
    (hcs : on = true → ∀ c ∈ ComplJ9AChainsRun.axChains9 p nA H rows9, c.OK)
    (hg : on = true → ∀ (hn0 : 0 < I.AX.n)
      (hn : I.AX.n = (ComplJ9AAxisRows.tableRows (ComplJ9AChainsRun.axChains9 p nA H rows9)).length),
      ∀ e ∈ ComplJ9AChipsOK.famAX deltaF hn0 (ComplJ9AChainsRun.axChains9 p nA H rows9) hn (K := KC),
        toχ χe ∉ e.ev) :
    AXChipOK deltaF powerBasis3 (mkPbA I hv).axOn (mkPbA I hv).hnX (mkPbA I hv).nodesX (mkPbA I hv).orbitX
      (VerJ8.chalsMJ8 deltaF (toχ I.χ)) I.toMsg.pubsX
      (fun j => I.toTr.X (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 hv.nAX (nodesOf I.AX)
        (mkOrbit I.AX hv.oAX) (VerJ8.chalsMJ8 deltaF (toχ I.χ)) I.toMsg.pubsX) j)) := by
  have hch : VerJ8.chalsMJ8 deltaF (toχ I.χ) = VerJ8.chalsMJ8 deltaF (toχ χe) := by rw [hχ]
  show AXChipOK deltaF powerBasis3 I.axOn hv.nAX (nodesOf I.AX) (mkOrbit I.AX hv.oAX)
      (VerJ8.chalsMJ8 deltaF (toχ I.χ)) (fun i => K3.toK (I.pubsX i)) _
  rw [hon]
  cases hon' : on
  · have hz : ∀ j, K3.toK (I.pubsX j) = 0 := by
      intro j
      rw [hpub]
      simp [GenAxE.axGenOf, hon', GenAxE.zeroChip, K3.toK_zero]
    exact axChipOK_absent I.AX hv.oAX hv.nAX _ _ hz _
  · rw [hon'] at hAX hpub hs hcs hg
    have hs' : (GenAxE.axGenE χe (ComplJ9AChainsRun.axChains9 p nA H rows9)).1.size ≤ 2 ^ 31 := by
      simpa [GenAxE.axGenOf] using hs rfl
    simp only [GenAxE.axGenOf, if_true] at hAX hpub
    have hn : I.AX.n = (ComplJ9AAxisRows.tableRows (ComplJ9AChainsRun.axChains9 p nA H rows9)).length := by
      rw [hAX]; exact chipOf_axGenE_n _ _
    exact axChipOK_exec χe _ (hcs rfl) I.AX hAX hv.oAX hv.nAX hn hs' (hg rfl hv.nAX hn) _ _ hch
      (by funext j; rw [hpub]; rfl) _ (fun j => rfl)

/-! ## 5. The honest names -/

section Honest
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (axOnA pubsXA nXOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)

variable {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`pubsX = pubsXA`**, through `K3.toK`, at the honest data `DA`, present or absent. -/
theorem pubsXA_eq (χe : CoinsE) (j : ℕ) :
    pubsXA deltaF Rt hgen (toχ χe) j =
      K3.toK ((GenAxE.axGenOf χe (j9aDataOf p Rg Rt hgen).acs.length (j9aDataOf p Rg Rt hgen).H
        (ComplJ9AGen.rowsOfT9 t) (axOnA t)).2 j) := by
  unfold pubsXA
  by_cases h : axOnA t = true
  · rw [dif_pos h]
    simp only [GenAxE.axGenOf, h, if_true]
    exact (pubsXE_eq χe _ _ _ j).symm
  · rw [dif_neg h]
    have h' : axOnA t = false := by simpa using h
    simp [GenAxE.axGenOf, h', GenAxE.zeroChip, K3.toK_zero]

/-- **`axOn = axOnA t`**: by unfolding (`genJ9AX`'s `!(axKeys9 rows9).isEmpty`). -/
theorem axOn_eq (t : NTree SkelX) : (!(ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 t)).isEmpty) = axOnA t := rfl

/-- **`I.AX.n = nXA`**. -/
theorem axn_eq (χe : CoinsE) :
    (chipOf (GenAxE.axGenOf χe (j9aDataOf p Rg Rt hgen).acs.length (j9aDataOf p Rg Rt hgen).H
      (ComplJ9AGen.rowsOfT9 t) (axOnA t)).1).n = ComplJ9ARun.nXA (p := p) Rt hgen :=
  chipOf_axGenOf_n _ _ _ _

end Honest

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx
#print axioms axRows_size
#print axioms chipOf_axGenE_n
#print axioms chipOf_zero_n
#print axioms chipOf_axGenOf_n
#print axioms fullCol_colAx
#print axioms axChipOK_exec
#print axioms axChipOK_absent
#print axioms axOK_I
#print axioms pubsXA_eq
#print axioms axOn_eq
#print axioms axn_eq
end Axioms
