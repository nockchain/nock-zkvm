/-
  NockvmE2E/Exec/SoundFlat.lean   (proof-only)

  L6 (verifier-side coverage), L10 (`localFlat_sound`) and L11 (`verifyFlat_sound`): assembly of `cLocal` (the audited local check, in the
  full J-8 context) from the flat verifier's acceptance.
-/
import NockvmE2E.Merkle.RapFriQueryOnly
import NockvmE2E.Exec.SoundLocal
import NockvmE2E.Exec.Inst
import NockvmE2E.Exec.SoundFlatFri

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.VL

/-- **`OffDom` for any audited domain** whose coset generator is the verifier's `dShift` and whose size exponent is the verifier's `nD`:
no opening point of the verifier is a point of the domain (from the verifier's power test (v)). -/
theorem offDom_gen (XI : ExecInst) (H : HFn) (FS : FSFn) (z : List Nat) (π : FlatProof) (hok : FlatOk XI H FS z π)
    {n : ℕ} (ω : Domain.SmoothCosetFftDomain n KC) (hnD : XI.nD = n)
    (hcg : ((ω.cosetGenerator : KCˣ) : KC) = psiV XI.dShift) :
    ∀ pt ∈ (openPts XI (zetaOf XI FS z π)).toList, ∀ i : Fin (2 ^ n), ω i ≠ toKV pt := by
  subst hnD
  intro pt hpt i h
  have hv := flatOk_offdom XI H FS z π hok pt hpt
  have hne : pt.pow (2 ^ XI.nD) ≠ VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD)) := by
    intro he
    have h1 : (pt.pow (2 ^ XI.nD) == VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD))) = true := (K3_beq_iff _ _).mpr he
    simp [bne, h1] at hv
  apply hne
  apply toKV_inj _ _ (canon3_pow _ _) (canon3_ofG _ (Inst.canon_pow _ _))
  rw [toKV_pow, toKV_ofG, psiV_pow, ← hcg, ← h, Inst.smooth_pow]

end NockvmE2E.Exec.V

namespace NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle
section Deep

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC}
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)


variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
variable (Op : Type) [Finite Op] [DecidableEq Op]

set_option hygiene false in
local notation "PS" => P.statement R0 Rest
set_option hygiene false in
local notation "PL" => friPlan (ω := ω) P A R0 Rest RestV e
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ω) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s d l Dg enc L
set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)


/-- the final message of `q0`'s RAP prefix (traces, coins, `Mfin`), as `cAcceptB` reads it -/
noncomputable abbrev finQ (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath) :=
  RapP.finalOfBK md.toRapMaskData (Rok (PS) (PL)) I Ifin 0 nb (fun _ => default) (fun _ => default) (MA.fstB Dg (RM) (BM) q).2.2

/-- **`cAcceptB` from its two parts** (the plan's residual check, FRI acceptance on the combined DEEP statement). -/
theorem cAcceptB_of_parts {Input Salt : Type} (z : Input × Salt)
    (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath)
    (hchk : (PL).check (MA.fstB Dg (RM) (BM) q).1 (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.2
      (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.1)
    (hfri : Fri.friAccepts' s d l L Dg enc hdom
      (combinedStmt s m G (MA.sndB Dg (RM) (BM) q).2.1
        (deepStmt (ω := ω) P A R0 e (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).1
          (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.2
          (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.1), z.2)
      (MA.sndB Dg (RM) (BM) q).2.2 = true) :
    cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom z q = true := by
  classical
  unfold cAcceptB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hchk, hfri⟩

/-- **`cLocal` from its parts** (generic in the whole audited context): selectors cover the read set, and the `q0` built from the openings
(`q0Of`, which agrees with them: `SL.agree_q0`) passes the in-the-clear combined check. -/
theorem cLocal_of_parts (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type}
    (z : Input × Salt) (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (hcov : CoversC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (round_bound hdom)
      (xsC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L Op p) (decode (pathRootsK Dg Op (MC) p).2))
    (hacc : cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom z
      (NockvmE2E.Exec.SL.q0Of (MC) (decode (pathRootsK Dg Op (MC) p).2) p) = true) :
    cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode z p = true := by
  classical
  unfold cLocal
  simp only [decide_eq_true_eq]
  exact ⟨hcov, _, NockvmE2E.Exec.SL.agree_q0 _ _ _, hacc⟩


/-- the compiled-path-independent `q0` the local check is witnessed by -/
noncomputable abbrev q0P (decode : Op → OpenAll Dg (merkleSkels (MC)))
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath) :=
  NockvmE2E.Exec.SL.q0Of (MC) (decode (pathRootsK Dg Op (MC) p).2) p

/-- the hypotheses of `SF.friAccepts_of_flat` on one decoded native path, bundled: the committed-history link `Link` (the audited oracle
history of `path` is the flat words / challenges / points / final polynomial) and the final degree bound -/
structure FriLinkAt {Salt : Type} (zS : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath)
    (c γ : KC) (pos : Fin l → ℕ) (W : ℕ → ℕ → KC) (Pf : KC → KC) (αN : ℕ → KC) : Prop where
  link : SF.Link s
    (SF.qO s l (initialOracle s zS.1)
      (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega) (friTranscript s d l path)))
    (SF.qA s l (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega) (friTranscript s d l path)))
    (SF.qX s l (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega) (friTranscript s d l path)))
    c γ pos W Pf αN
  hdeg : (finalPolynomial s (SF.qO s l (initialOracle s zS.1)
      (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega) (friTranscript s d l path)))).natDegree
    < d.val

/-- the coins, the clear final message and the traces of `q0`'s RAP prefix -/
noncomputable abbrev chiQ (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath) :=
  (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.1
noncomputable abbrev finMQ (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath) :=
  (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).2.2
noncomputable abbrev trQ (q : (protocol (baseRounds Dg (MC))).tree.ExecutionPath) :=
  (finQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q).1

structure LocalLinks (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof)
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (q0 : (protocol (baseRounds Dg (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop) : Prop where
  hnD : XI.nD = n
  hk : XI.k = k
  hl : XI.l = l
  hcg : ((ω.cosetGenerator : KCˣ) : KC) = psiV XI.dShift
  hs1 : ∀ i, (s i).val = 1
  hq0 : q0 = q0P P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L Op decode p
  hcov : CoversC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (round_bound hdom)
      (xsC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L Op p) (decode (pathRootsK Dg Op (MC) p).2)
  hD : DeepLink XI H FS zF π P A (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0 P.a) (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0 P.z)
      (finMQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0).2.1 (finMQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0).2.2
  hpts : ∀ j, ∃ pt ∈ (openPts XI (zetaOf XI FS zF π)).toList,
      toKV pt = ptOf P A e (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0) j
  hPub : XI.pubCheck (slotsOf XI FS zF π) (pubOfProof XI π) = true → PubRel (slotsOf XI FS zF π) (pubOfProof XI π)
  hRV : PubRel (slotsOf XI FS zF π) (pubOfProof XI π) →
      RestV (MA.fstB Dg (RM) (BM) q0).1 (finMQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)
        (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)
  hF : FriLinkAt s d l
      ((combinedStmt s m G (MA.sndB Dg (RM) (BM) q0).2.1
        (deepStmt (ω := ω) P A R0 e (trQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)
          (finMQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0) (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)), z.2))
      (Fri.toFriPath s d l L Dg enc (MA.sndB Dg (RM) (BM) q0).2.2)
      (homV.ψ XI.dShift) (homV.ψ XI.dGen) (fun j => π.pos[j.1]!)
      (fun w i => homV.φ (SF.Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
      (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) (fun i => homV.φ (alphasOf XI FS zF π)[i]!)

/-- **L10 (`localFlat_sound`)**: the flat verifier accepts ⇒ the audited local check `cLocal` accepts the compiled path `p`, and the cross-table
public relation holds.  Everything derivable is derived from `FlatOk`: the DEEP check (`deepCheck_of_flatOk'`), `OffDom` (`offDom_gen`), the FRI
folds (`flatOk_flatFri`), canonicity.  REMAINING hypotheses, by name:
* `hcov` (L6, the layout link `md`/`L`: the selectors of `decode`'s openings cover the read set);
* `hD : DeepLink` (audited coins/values = decoded flat ones, `hdag`, `hH`/`hinj`, `he`/`hnq`/`hcw`/`hQ`);
* `hpts` (every audited opening point is one of the verifier's `openPts`), `hcg` (the audited domain's coset generator is `dShift`);
* `hPub` (`pubCheck_sound` shape: `pubCheck = true → PubRel`), `hRV` (`PubRel → RestV`);
* `hF : FriLinkAt` (`SF.Link` + `hdeg`), `hs1`, and the parameter agreements `hnD`/`hk`/`hl`. -/
theorem localFlat_sound (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hok : FlatOk XI H FS zF π)
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (q0 : (protocol (baseRounds Dg (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop)
    (Ls : LocalLinks P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op XI H FS zF π decode z p q0 PubRel) :
    cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode z p = true ∧
      PubRel (slotsOf XI FS zF π) (pubOfProof XI π) := by
  obtain ⟨hnD, hk, hl, hcg, hs1, hq0, hcov, hD, hpts, hPub, hRV, hF⟩ := Ls
  subst hnD hk
  have hdc := deepCheck_of_link XI H FS zF π P A _ _ _ _ _ hok hD
  have hoff : OffDom (ω := ω) P A e (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0) := by
    intro j i
    obtain ⟨pt, hpt, he⟩ := hpts j
    rw [← he]
    exact offDom_gen XI H FS zF π hok ω rfl hcg pt hpt i
  have hrel := hPub (flatOk_pub XI H FS zF π hok)
  have hchk : (PL).check (MA.fstB Dg (RM) (BM) q0).1 (finMQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0)
      (chiQ P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L q0) := by
    show DeepCheck P A _ _ _ _ _ ∧ _ ∧ _
    exact ⟨hdc, hoff, hRV hrel⟩
  have hsz : π.pos.size = l := by
    obtain ⟨_, _, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    rw [h5.2, hl]
  have hflat : ∀ j : Fin l, SF.FlatFri (homV.ψ XI.dShift) (homV.ψ XI.dGen) XI.nD XI.k
      (fun w i => homV.φ (SF.Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
      (fun i => homV.φ (alphasOf XI FS zF π)[i]!)
      (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) (π.pos[j.1]!) := by
    intro j
    refine flatOk_flatFri XI FS zF π H hok _ ?_
    have hj : j.1 < π.pos.size := by rw [hsz]; exact j.2
    rw [getElem!_pos π.pos j.1 hj]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hj)
  have hfri : Fri.friAccepts' s d l L Dg enc hdom _ _ = true :=
    SF.friAccepts_of_flat s d l hdom hs1 _ _ hF.link hF.hdeg hflat
  have hacc := cAcceptB_of_parts P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom z q0 hchk hfri
  rw [hq0] at hacc
  exact ⟨cLocal_of_parts P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode z p hcov hacc, hrel⟩

/-- **the Merkle part of L11**: tree `j`'s root, recomputed by the audited `getPutativeBatchRootAddressedWithHash` from the opening embedded from
the flat streams (`SM.mkOpening`), is the committed root `π.roots[j]` (L3: `flatOk_merkle'`). -/
def MerkleRootOk (XI : ExecInst) (H : HFn) (π : FlatProof) (j : ℕ) : Prop :=
  let W := (blockLayout XI).1
  let sel := (selsOf XI π)[j]!
  let sp := if j < 4 then ragSpec W[j]! (2 ^ (XI.nD - 1)) else friSpec (2 ^ (XI.nD - (j - 3)))
  let vs := π.vals[j]!
  let leaf (r : Nat) : Dg5 :=
    if j < 4 then [vs[r]!, 0, 0, 0, 0] else [vs[3 * r]!, vs[3 * r + 1]!, vs[3 * r + 2]!, 0, 0]
  AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
    (fun a l r' => (fun i l r => H ([tagNode, j, i] ++ l ++ r)) (SM.heapIdx a 1) l r')
    (SM.mkOpening (fun i => sel[lb sel i]? == some i)
      (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).values
    (SM.mkOpening (fun i => sel[lb sel i]? == some i)
      (fun i => leaf (lb sel i)) (SM.skelOf sp sp.total sp.total) (π.sibs[j]!).toList).proof
    = π.roots[j]!

/-- **L11 (`verifyFlat_sound`)**: the executable flat verifier accepts ⇒ (a) every non-empty tree's root is reproduced by the audited Merkle
recomputation (L3), (b) the audited local check `cLocal` accepts the compiled path (L10), (c) the cross-table public relation holds.
Remaining hypotheses: exactly the fields of `LocalLinks` (see `localFlat_sound`). -/
theorem verifyFlat_sound (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof)
    (hv : verifyFlat XI H FS zF π = true)
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (q0 : (protocol (baseRounds Dg (MC))).tree.ExecutionPath)
    (PubRel : Array VF.K3 → Array VF.G → Prop)
    (Ls : LocalLinks P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op XI H FS zF π decode z p q0 PubRel) :
    (∀ j, j < 4 + XI.k → ¬ (j < 4 ∧ (blockLayout XI).1[j]! = 0) → MerkleRootOk XI H π j) ∧
    cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode z p = true ∧
      PubRel (slotsOf XI FS zF π) (pubOfProof XI π) := by
  have hok := (verifyFlat_iff XI H FS zF π).mp hv
  exact ⟨fun j hj hne => flatOk_merkle' XI H FS zF π hok j hj hne,
    localFlat_sound P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op XI H FS zF π hok decode z p q0 PubRel Ls⟩


end Deep

end NockvmE2E.Merkle.RapFriQ

#print axioms NockvmE2E.Merkle.RapFriQ.cAcceptB_of_parts
#print axioms NockvmE2E.Merkle.RapFriQ.cLocal_of_parts
#print axioms NockvmE2E.Merkle.RapFriQ.localFlat_sound
#print axioms NockvmE2E.Merkle.RapFriQ.verifyFlat_sound
