/-
the AIR-side bridge of J-9 AL, over a VARIABLE instance `XI` (no literal file is imported).
Twin of `J9A/LinkJ9AToy.lean` §3 (`mkPbA_withOrb_eq`):
  * `orbSh XI`: every one of the nine chips on the shared orbit `(k+1, ofU64 hGen)` (the datum's orbit, `PbOfX9L`);
  * `preL_interp_eq`: the verifier's `preL` of nock's `mkPbAL` (Lagrange interpolation of the `preg` columns at the nodes `hGen^i`) IS the loaded
    preprocessed-column polynomial `preLOfX XI` of the datum (both have degree `< nL` and agree on `nL` distinct nodes; `MaskOkK.eq_interp`);
  * `mkPbAL_withOrbL_eq`: `mkPbAL (withOrbL I (orbSh XI)) hv = PbOfX9L XI …`, field by field, generic in `I`, from the table sizes, flags and `prims` of `I`.
Not zero-knowledge.
-/
import NockvmE2E.J9AL.DatX9LOk
import NockvmE2E.J9AL.PregJ9AL
import NockvmE2E.J9AL.AccMonoJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb
import Nock.V1J9AL.CheckJ9ALIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.LinkJ9ALBridge

open Polynomial
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Check
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9AL.CheckJ9AL Nock.V1J9AL.CheckJ9ALIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbFits withOrb reorb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrb (OrbJ9AL withOrbL OrbAdmL)
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9ALChips
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open NockvmE2E.J9A.PbOfX9 (nOpt)
open NockvmE2E.J9AL.PbOfX9L

noncomputable section

/-! ## 1. the shared orbit assignment -/

/-- the orbit every chip sits on in the datum: `(k+1, ofU64 hGen)` -/
def orbSh (XI : ExecInst) : OrbJ9AL :=
  ⟨⟨⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩,
    ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩, ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩⟩,
    ⟨XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen⟩⟩

theorem nodesOf_eq_pow (h n : ℕ) (ω : Nock.TraceGenExe.Gold) (cols : ℕ → Fin n → ZMod P) (z : ZMod P) (hz : ω.toZ = z) :
    nodesOf ⟨h, n, ω, cols⟩ = fun i : Fin n => z ^ (i : ℕ) := by
  funext i; rw [nodesOf_eq]; simp [hz]

theorem nodes_hGen (XI : ExecInst) (n : ℕ) (cols : ℕ → Fin n → ZMod P) :
    nodesOf ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩ = fun i : Fin n => zv XI.hGen ^ (i : ℕ) :=
  nodesOf_eq_pow _ _ _ _ _ (Nock.TraceGenExe.Gold.ofU64_toZ _)

theorem orbit_hGen (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (n : ℕ) (cols : ℕ → Fin n → ZMod P)
    (ho : OrbOK ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩) :
    mkOrbit ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩ ho = orbX9L XI h := by
  unfold mkOrbit orbX9L
  congr 1
  exact Nock.TraceGenExe.Gold.ofU64_toZ _

theorem heq_of_zero {α : Type} (n m : ℕ) (hn : n = 0) (hm : m = 0) (f : Fin n → α) (g : Fin m → α) : HEq f g := by
  subst hn; subst hm; exact heq_of_eq (funext fun i => i.elim0)

/-! ## 2. `preL`: Lagrange interpolation of the `preg` columns is the loaded column polynomial -/

/-- **`preL_interp_eq`** [kernel, modulo the instance gates `hsh`, `hpreg`, `hrt`]: at an instance with an ALU table, nock's `preL` of `mkPbAL`
(`Lagrange.interpolate` of `pregCol (primsOf XI) k` at the nodes `hGen^i`, `i < nL`) IS the datum's `preLOfX XI k` (the loaded column `2 + k` of the ALU). -/
theorem preL_interp_eq (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (hpreg : NockvmE2E.J9A.RunGate9L.pregOkF XI = true)
    (hrt : NockvmE2E.J9A.RunGate9L.primsRoundTrip XI.pubIn.prims = true) (hon : (tabOf XI "aluChipJ9").isSome = true) (k : Fin 3) :
    Lagrange.interpolate Finset.univ (fun i : Fin (nOpt XI "aluChipJ9") => zv XI.hGen ^ (i : ℕ))
      (fun i => (pregCol (primsOf XI) (k : ℕ) (i : ℕ) : ZMod P)) = preLOfX XI k := by
  obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp hon
  have hmem : tab ∈ XI.tabs.toList := List.mem_of_find?_eq_some htab
  have hid : tab.chip.id = "aluChipJ9" := by
    have := List.find?_some htab
    simpa using this
  have hn : nOpt XI "aluChipJ9" = tab.hN := by
    simp [nOpt, hNof, htab]
  have hpre : preLOfX XI k = NockvmE2E.Exec.MaskOkK.polyOfArr (XI.pre[tab.col0 + 2 + (k : ℕ)]!) := by
    simp [preLOfX, aluCol0, htab]
    rfl
  obtain ⟨hl, hv⟩ := NockvmE2E.J9AL.PregJ9AL.pregCol_of_pregOkF XI hsh hpreg hrt tab hmem hid
  have hsz := NockvmE2E.J9AL.PregJ9AL.preL_size_of_pregOkF XI hpreg tab hmem hid k
  have hdeg : (NockvmE2E.Exec.MaskOkK.polyOfArr (XI.pre[tab.col0 + 2 + (k : ℕ)]!)).degree < ((nOpt XI "aluChipJ9" : ℕ) : WithBot ℕ) := by
    have h0 := NockvmE2E.Exec.MaskOkK.degree_polyOfList (XI.pre[tab.col0 + 2 + (k : ℕ)]!).toList
    have hle : (((XI.pre[tab.col0 + 2 + (k : ℕ)]!).toList.length : ℕ) : WithBot ℕ) ≤ ((nOpt XI "aluChipJ9" : ℕ) : WithBot ℕ) := by
      rw [hn]; exact_mod_cast (by simpa using hsz)
    exact lt_of_lt_of_le h0 hle
  have hinj : Function.Injective (fun i : Fin (nOpt XI "aluChipJ9") => zv XI.hGen ^ (i : ℕ)) :=
    inj_pows_L hsh (nOpt_leL hsh "aluChipJ9")
  rw [hpre]
  exact (NockvmE2E.Exec.MaskOkK.eq_interp _ hinj _ hdeg _ (fun i => hv k i (hn ▸ i.2))).symm

/-! ## 3. the bridge `mkPbAL (withOrbL I (orbSh XI)) hv = PbOfX9L XI …` -/

/-- **The bridge, generic in `I`** [kernel]: if the row counts, root counts, registry data, layout, presence flags, primitive table and pin data of `I` are those
`PbOfX9L` prescribes (`hNof` / `nOpt` of the instance), and the loaded `preL` is the Lagrange interpolant of the `preg` columns (`preL_interp_eq`), then nock's
`mkPbAL` of the record moved onto the shared orbit `orbSh XI` IS `PbOfX9L XI …` (field by field; the proof fields are irrelevant, the nodes are `ω^i`). -/
theorem mkPbAL_withOrbL_eq (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow)
    (I : InJ9AL) (hv : ValidJ9AL (withOrbL I (orbSh XI)))
    (hX : I.X.n = hNof XI "computeChipVCLHX9") (hC : I.C.n = hNof XI "cellChipHQKW") (hW : I.W.n = hNof XI "walkChipJ8")
    (hJ : I.J.n = hNof XI "jetChipJ8") (hA : I.A.n = hNof XI "atomChipHQL") (hV : I.V.n = nOpt XI "walkChipHQK")
    (hAX : I.AX.n = nOpt XI "axisChipJ9") (hSP : I.SP.n = nOpt XI "splitChipJ9") (hAL : I.AL.n = nOpt XI "aluChipJ9")
    (hk : I.kroots = kroots) (hkV : I.krootsV = if (tabOf XI "walkChipHQK").isSome then krootsV else 0)
    (hRt : I.Rt = Rt) (hr : I.regs = regs) (hi : I.ids = ids) (hx : I.idx = idx) (hrk : I.rk = rk)
    (hlay : HEq I.lay lay) (hax : I.axOn = (tabOf XI "axisChipJ9").isSome) (hsp : I.spOn = (tabOf XI "splitChipJ9").isSome)
    (hon : I.aluOn = (tabOf XI "aluChipJ9").isSome) (hpr : I.prims = primsOf XI)
    (hpre : ∀ k : Fin 3, Lagrange.interpolate Finset.univ (fun i : Fin (nOpt XI "aluChipJ9") => zv XI.hGen ^ (i : ℕ))
      (fun i => (pregCol (primsOf XI) (k : ℕ) (i : ℕ) : ZMod P)) = preLOfX XI k) :
    mkPbAL (withOrbL I (orbSh XI)) hv =
      { PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay with idxP := I.idxP, rkP := I.rkP } := by
  obtain ⟨⟨⟨c, M, χ, r, g, «X», C, W, J, A, V, kr, krV, lay', Rt', regs', ids', idx', rk'⟩, AX, SP, pX, pS, aX, aS, rX, rS⟩,
    AL, pL, aO, pr, iP, rP, rAL⟩ := I
  obtain ⟨hX0, nX, wX, cX⟩ := «X»
  obtain ⟨hC0, nC, wC, cC⟩ := C
  obtain ⟨hW0, nW, wW, cW⟩ := W
  obtain ⟨hJ0, nJ, wJ, cJ⟩ := J
  obtain ⟨hA0, nA, wA, cA⟩ := A
  obtain ⟨hV0, nV, wV, cV⟩ := V
  obtain ⟨hAX0, nAX, wAX, cAX⟩ := AX
  obtain ⟨hSP0, nSP, wSP, cSP⟩ := SP
  obtain ⟨hAL0, nAL, wAL, cAL⟩ := AL
  dsimp only at *
  subst hX hC hW hJ hA hV hAX hSP hAL hk hkV hRt hr hi hx hrk hon hpr
  have hlay' := eq_of_heq hlay
  subst hlay'
  simp only [mkPbAL, mkPbA, mkPb, PbOfX9L, withOrbL, withOrb, orbSh, reorb]
  congr 3 <;> first | exact nodes_hGen _ _ _ | exact orbit_hGen _ _ _ _ _ | (funext k; rw [nodes_hGen]; exact hpre k)

end

end NockvmE2E.J9AL.LinkJ9ALBridge

#print axioms NockvmE2E.J9AL.LinkJ9ALBridge.nodes_hGen
#print axioms NockvmE2E.J9AL.LinkJ9ALBridge.orbit_hGen
#print axioms NockvmE2E.J9AL.LinkJ9ALBridge.preL_interp_eq
#print axioms NockvmE2E.J9AL.LinkJ9ALBridge.mkPbAL_withOrbL_eq
