/-
 the concrete side protocol, definitions only.

Contents:
  * `skelVKl`, `friSkel`, `skelsSide X k` = `skelVKl X :: .leaf :: .leaf :: .leaf :: (finRange k).map (friSkel X)`;
    `skelsSide_get0` (`rfl`), `skelsSide_get_fri`, `friSkel_eq_skelFlat`, `skelsSide_drop4`;
  * `shiftModel` : the tag-shifted `NodeQueryModel (NQuery sk) (MAddress skM) DgJ8` (address `<w,a>` of the merkle part <-> tree `4+w` of `sk`),
    generic in `sk`, `skM`; `skelsSide_shift` instantiates it at `skelsSide X k` / `(finRange k).map (friSkel X)` (= `merkleSkels (bMask ..)` by
    `SideMerkle.merkleSkels_bMask_eq` and `LX` skel = `friSkel`);
  * `Stmt'` encoding: `SStmt X` = ((Fin 23 -> ZMod p) x (Fin nC -> Fin Rm -> Fin 3 -> ZMod p)) with `Finite`/`DecidableEq`, `decSX : SStmt X -> SideStmt`,
    `encSX : List Nat -> Array (Array K3) -> SStmt X`, shape lemmas;
  * `localAccepts := bLocal` and `guards := trueGuards` need no definition here (they are the existing `SideMerkle.bLocal`, `trueGuards`; `hlocal` is
    `SideMerkle.bMask_queryOnly`).

NOT in this file: `sideOf`, `decodeS` (`openAllOf` over the FRI trees), `fkOf`, `frOf`, the generator `G`
(needs the layout check of `G` against `fixOps`).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideInst` is complete.
-/
import NockvmE2E.Exec.E2EEmbed
import NockvmE2E.Exec.VKBind
import NockvmE2E.Merkle.SideMerkle
import NockvmE2E.Exec.E2EFinal

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideInst
open NockvmE2E.Exec NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Exec.V NockvmE2E.Merkle

/-! ## 1. skeletons -/

/-- the VK rag tree skeleton (tree 0 of the side oracle); restated locally (= `VKTrace.skelVK` by `rfl`) -/
def skelVKl (XI : ExecInst) : Skeleton :=
  skelOf (VKBind.vkSp XI) (VKBind.vkSp XI).total (VKBind.vkSp XI).total

/-- the skeleton of FRI layer `w` (`= LX.skel w`, `= skelFlat XI (4+w)`) -/
def friSkel (XI : ExecInst) (w : Fin XI.k) : Skeleton :=
  skelOf (friSpec (2 ^ (XI.nD - (w.1 + 1)))) (2 ^ (XI.nD - (w.1 + 1))) (2 ^ (XI.nD - (w.1 + 1)))

/-- the side oracle's tree list: the VK tree, three never-hashed one-leaf tags, then the `XI.k` FRI layer trees -/
def skelsSide (XI : ExecInst) : List Skeleton :=
  skelVKl XI :: .leaf :: .leaf :: .leaf :: (List.finRange XI.k).map (friSkel XI)

theorem skelsSide_get0 (XI : ExecInst) : (skelsSide XI)[0]? = some (skelVKl XI) := rfl

theorem friSkel_eq_skelFlat (XI : ExecInst) (w : Fin XI.k) : friSkel XI w = skelFlat XI (4 + w.1) := by
  unfold friSkel skelFlat
  have h1 : ¬ (4 + w.1 < 4) := by omega
  have h2 : 4 + w.1 - 3 = w.1 + 1 := by omega
  simp [h1, h2] <;> rfl

theorem skelsSide_length (XI : ExecInst) : (skelsSide XI).length = 4 + XI.k := by
  simp [skelsSide]; omega

theorem skelsSide_get_fri (XI : ExecInst) (w : ℕ) (hw : w < XI.k) (hj : 4 + w < (skelsSide XI).length) :
    (skelsSide XI).get ⟨4 + w, hj⟩ = ((List.finRange XI.k).map (friSkel XI)).get ⟨w, by simpa using hw⟩ := by
  simp [skelsSide, List.getElem_cons, List.getElem_map, List.getElem_finRange]


/-! ## 2. the tag-shifted node-query model -/

/-- transport of an internal index along an equality of skeletons -/
def trI {s t : Skeleton} (h : s = t) (a : SkeletonInternalIndex s) : SkeletonInternalIndex t := h ▸ a

theorem heq_trI {s t : Skeleton} (h : s = t) (a : SkeletonInternalIndex s) : HEq (trI h a) a := by
  subst h; exact HEq.rfl

theorem sig_eq {skM : List Skeleton} (w w' : Fin skM.length) (hww : w = w') (a : SkeletonInternalIndex (skM.get w))
    (b : SkeletonInternalIndex (skM.get w')) (hab : HEq a b) : (⟨w, a⟩ : MAddress skM) = ⟨w', b⟩ := by
  subst hww
  have hh := eq_of_heq hab
  subst hh
  rfl

/-- **the tag-shifted model**: addresses `<w, a>` of the merkle part `skM` are the queries of tree `4 + w` of `sk`; queries of the trees `< 4`
(the VK tree and the never-hashed tags) are viewed at the fallback address `dflt` (the model must be total on `NQuery sk`). -/
def shiftModel (sk skM : List Skeleton) (hlen : 4 + skM.length ≤ sk.length)
    (hget : ∀ w (hw : w < skM.length) (hj : 4 + w < sk.length), sk.get ⟨4 + w, hj⟩ = skM.get ⟨w, hw⟩)
    (dflt : MAddress skM) : MerkleTreeExtractability.NodeQueryModel (NQuery sk) (MAddress skM) DgJ8 where
  view :=
    { address := fun q =>
        if h : 4 ≤ q.1.1.1 ∧ q.1.1.1 - 4 < skM.length then
          ⟨⟨q.1.1.1 - 4, h.2⟩, trI (by
            have h1 := hget (q.1.1.1 - 4) h.2 (by have := q.1.1.2; omega)
            have h2 : (⟨4 + (q.1.1.1 - 4), by have := q.1.1.2; omega⟩ : Fin sk.length) = q.1.1 := Fin.ext (by simp; omega)
            rw [h2] at h1; exact h1) q.1.2⟩
        else dflt
      input := fun q => q.2 }
  mkQuery a lr := (⟨⟨4 + a.1.1, by have := a.1.2; omega⟩, trI (hget a.1.1 a.1.2 (by have := a.1.2; omega)).symm a.2⟩, lr)
  address_mkQuery a lr := by
    have hc : 4 ≤ 4 + a.1.1 ∧ 4 + a.1.1 - 4 < skM.length := ⟨by omega, by have := a.1.2; omega⟩
    show (if h : 4 ≤ (4 + a.1.1) ∧ (4 + a.1.1) - 4 < skM.length then _ else dflt) = a
    rw [dif_pos hc]
    exact sig_eq _ _ (Fin.ext (by simp)) _ _ ((heq_trI _ _).trans (heq_trI _ _))
  input_mkQuery _ _ := rfl

/-- the instantiation of `shiftModel`: the merkle part is `(finRange k).map (friSkel XI)` (= `merkleSkels (bMask ..)`) -/
def modelS (XI : ExecInst) (dflt : MAddress ((List.finRange XI.k).map (friSkel XI))) :
    MerkleTreeExtractability.NodeQueryModel (NQuery (skelsSide XI)) (MAddress ((List.finRange XI.k).map (friSkel XI))) DgJ8 :=
  shiftModel (skelsSide XI) _ (by rw [skelsSide_length]; simp) (fun w hw hj => skelsSide_get_fri XI w (by simpa using hw) hj) dflt

/-! ## 3. the finite `Stmt'` encoding -/

open NockvmE2E.Exec.VF in
/-- finite encoding of the side statement `(ctx, vF)`: `ctx` as a LENGTH TAG (`≤ 23`) plus 23 limbs (4 roots x 5 + zeta's 3; the tag is needed because
`FixFailR` does not force `π.roots.size ≥ 4`, so `fixCtx` has `5·min(4,size)+3 ∈ {3,8,13,18,23}` limbs:  section 3), `vF` as `Fin 3` limbs per opened value -/
abbrev SStmt (XI : ExecInst) : Type :=
  (Fin 24 × (Fin 23 → ZMod NockvmE2E.Exec.p)) × (Fin (fixCols XI).size → Fin (max XI.r 1) → Fin 3 → ZMod NockvmE2E.Exec.p)

/-- length-tagged ctx encoding -/
def encCtx (ctx : List ℕ) : Fin 24 × (Fin 23 → ZMod NockvmE2E.Exec.p) :=
  (⟨min ctx.length 23, by omega⟩, fun i => ((ctx.getD i.1 0 : ℕ) : ZMod NockvmE2E.Exec.p))

def decCtx (c : Fin 24 × (Fin 23 → ZMod NockvmE2E.Exec.p)) : List ℕ :=
  (List.ofFn fun i => (c.2 i).val).take c.1

theorem decCtx_encCtx (ctx : List ℕ) (hl : ctx.length ≤ 23) (hb : ∀ x ∈ ctx, x < NockvmE2E.Exec.p) :
    decCtx (encCtx ctx) = ctx := by
  apply List.ext_getElem
  · simp [decCtx, encCtx]; omega
  · intro i h1 h2
    simp only [decCtx, encCtx, List.getElem_take, List.getElem_ofFn]
    have hi : i < ctx.length := h2
    rw [List.getD_eq_getElem _ _ hi, ZMod.val_natCast, Nat.mod_eq_of_lt (hb _ (List.getElem_mem hi))]

/-- ζ round-trips through its limbs -/
theorem ofLimbs_limbs (z : VF.K3) : VF.K3.ofLimbs (VF.K3.limbs z) = z := by
  cases z; simp [VF.K3.ofLimbs, VF.K3.limbs]

/-- ζ is the LAST 3 limbs of `fixCtx π ζ`, whatever `π` (this is what makes `hC2` hold for all `π`) -/
theorem ctx_tail (π : FlatProof) (z : VF.K3) :
    VF.K3.ofLimbs ((fixCtx π z).drop ((fixCtx π z).length - 3)) = z := by
  have h3 : (VF.K3.limbs z).length = 3 := rfl
  unfold fixCtx
  rw [List.length_append, h3, Nat.add_sub_cancel, List.drop_left]
  exact ofLimbs_limbs z

instance (XI : ExecInst) : Finite (SStmt XI) := inferInstance
instance (XI : ExecInst) : DecidableEq (SStmt XI) := inferInstance

open NockvmE2E.Exec.VF in
/-- decode: `z = []`, `ctx` = the 23 limbs, `vF[j]` = the first `fixLen` values of column `j`, each from its 3 limbs -/
def decSX (XI : ExecInst) (st : SStmt XI) : SideStmt where
  z := []
  ctx := decCtx st.1
  vF := Array.ofFn (fun j : Fin (fixCols XI).size =>
    (Array.ofFn (fun o : Fin (max XI.r 1) => VF.K3.ofLimbs (List.ofFn (fun c : Fin 3 => (st.2 j o c).val)))).extract 0
      (fixLen XI (fixCols XI)[j.1]!))

theorem decSX_z (XI : ExecInst) (st : SStmt XI) : (decSX XI st).z = [] := rfl

theorem decSX_ctx_length (XI : ExecInst) (st : SStmt XI) : (decSX XI st).ctx.length ≤ 23 := by
  simp [decSX, decCtx]

/-! ## 4. the statement map `stF` (ONE function of the flat messages, used by `sideOfX` and `fkOfX`) -/

/-- start offset (in values) of column `j` in the flat `vF` limb list -/
def offX (XI : ExecInst) (j : ℕ) : ℕ := ((List.range j).map fun j' => fixLen XI (fixCols XI)[j']!).sum

/-- the side statement read off the flat messages: `ctx` and the flat `vF` limbs (`fixMsgs` slot 1) -/
def stF (XI : ExecInst) (ctx vFl : List ℕ) : SStmt XI :=
  (encCtx ctx, fun j o c =>
    if o.1 < fixLen XI (fixCols XI)[j.1]! then ((vFl.getD (3 * (offX XI j.1 + o.1) + c.1) 0 : ℕ) : ZMod NockvmE2E.Exec.p) else 0)

/-! ## 5. the flat power generator and the opening layout (`fixOps` order) -/

/-- the openings of the side proof in `fixOps` order -/
def opList (XI : ExecInst) : List (ℕ × ℕ) :=
  (List.range (fixCols XI).size).flatMap fun j => (List.range (fixLen XI (fixCols XI)[j]!)).map (j, ·)

def mSX (XI : ExecInst) : ℕ := (opList XI).length - 1

def opIdxX (XI : ExecInst) (i : Fin (mSX XI + 1)) : ℕ × ℕ := (opList XI)[i.1]!

abbrev SSX : Type := KC

/-- `G := univariatePowersGenerator KC (mSX XI)` (flat batching: coefficient of the `i`-th opening is `cs^i`) -/
noncomputable abbrev GX (XI : ExecInst) : CoreDefinitions.Generator SSX (Fin (mSX XI + 1)) KC :=
  CoreDefinitions.univariatePowersGenerator KC (mSX XI)

/-- the point of opening `i`: `ζ` is read from the LAST 3 ctx limbs -/
def ptKX (XI : ExecInst) (ctx : List ℕ) (i : Fin (mSX XI + 1)) : VF.K3 :=
  (openPts XI (VF.K3.ofLimbs (ctx.drop (ctx.length - 3))))[(opIdxX XI i).2]!

/-- `hC2` for all `π ζ` (via `ctx_tail`): ptKX of `fixCtx π ζ` is the true opening point -/
theorem hC2X (XI : ExecInst) (π : FlatProof) (ζ : VF.K3) (i : Fin (mSX XI + 1)) :
    ptKX XI (fixCtx π ζ) i = (openPts XI ζ)[(opIdxX XI i).2]! := by
  unfold ptKX; rw [ctx_tail]

/-! ## 6. FS keys, readout and `sideOf` of the side protocol -/

section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- the side compiled mask `bMask` at `S := KC`, `d = 1` -/
noncomputable abbrev SMSg : MRounds DgJ8 := NockvmE2E.Merkle.SideMerkle.bMask (S := KC) s 1 l L DgJ8 E2EResid.encK

/-- the decoders of `bMask`: `(dsbC, dsmC ..)` -/
noncomputable def dsS : MDec (SMSg s l L) := by
  unfold SMSg NockvmE2E.Merkle.SideMerkle.bMask
  exact (E2EFinal.dsbC, E2EResid.dsmC s 1 l L E2EResid.encK)

/-- the fixed opening used for decoding (the opening round gets no flat challenge, so it is irrelevant) -/
noncomputable def ω0S : OpenAll DgJ8 (merkleSkels (SMSg s l L)) := openAllOf _ []

/-- the side proof of `fixAdapt`, with tree 0's root replaced by a dummy (the FRI trees `≥ 4` do not read it) -/
def fixAdaptD (XI : ExecInst) (πF : FixProof) : FlatProof :=
  let z5 : Dg5 := [0, 0, 0, 0, 0]
  { roots := #[z5, z5, z5, z5] ++ πF.roots, vT := #[], vQ := #[], pfinal := πF.pfinal, pos := πF.pos,
    vals := #[πF.vals[0]!, #[], #[], #[]] ++ πF.vals.extract 1 (1 + XI.k),
    sibs := #[πF.sibs[0]!, #[], #[], #[]] ++ πF.sibs.extract 1 (1 + XI.k) }

/-- the opening of the FRI trees of the side proof -/
noncomputable def openAllS (XI : ExecInst) (πF : FixProof) : OpenAll DgJ8 (merkleSkels (SMSg s l L)) :=
  openAllOf _ ((flatTrees XI (fixAdaptD XI πF)).drop 4)

variable (XI : ExecInst) {Statement Salt : Type} (decZ : List ℕ → Statement × Salt)

/-- the default key -/
noncomputable def k0X {Op : Type} [Finite Op] [DecidableEq Op] (ω0 : Op) :
    Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L)) :=
  Key.here (stF XI [] [], decZ []) ((mDecs dgOf (SMSg s l L) (dsS s l L) ω0).1.decM []) PUnit.unit

/-- the side FS key from the flat transcript prefix `z :: ctx :: fm.take i` -/
noncomputable def fkOfX {Op : Type} [Finite Op] [DecidableEq Op] (ω0 : Op) :
    List (List ℕ) → Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))
  | z :: ctx :: fm =>
      (decKeyA (stF XI ctx (fm.headD []), decZ z) _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω0) fm).getD (k0X s l L XI decZ ω0)
  | _ => k0X s l L XI decZ ω0

noncomputable def frOfX {Op : Type} [Finite Op] [DecidableEq Op] (ω0 : Op)
    (k : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) (c : Key.Challenge k) (_ : ℕ) : List ℕ :=
  encChalD _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω0) k c

/-- the side statement, salt and public messages extracted from the adversary's output -/
noncomputable def sideOfX {W : Type} (FS : FSFn) (encZ : Statement × Salt → List ℕ)
    (o : Statement × Salt × FlatProof × FixProof × W) :
    SStmt XI × (Statement × Salt) × PublicMessages (compiledRoundsK DgJ8 (OpenAll DgJ8 (merkleSkels (SMSg s l L))) (SMSg s l L)) :=
  let π := o.2.2.1
  let πF := o.2.2.2.1
  let ζ := zetaOf XI FS (encZ (o.1, o.2.1)) π
  let fm := (fixMsgs XI.k (fixCtx π ζ) πF.vF πF.roots πF.pfinal).toList.drop 1
  (stF XI (fixCtx π ζ) (fm.headD []), (o.1, o.2.1),
    decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) (openAllS s l L XI πF)) fm)

end Side

/-! ## 7. the fallback address of the tag-shifted model -/

theorem skelOf_internal (sp : TSpec) (N : ℕ) (h : 2 ≤ N) : ∃ a b, skelOf sp N N = .internal a b := by
  obtain ⟨f, rfl⟩ : ∃ f, N = f + 1 := ⟨N - 1, by omega⟩
  refine ⟨skelOf sp f (sp.split (f + 1)), skelOf sp f (f + 1 - sp.split (f + 1)), ?_⟩
  rw [skelOf, if_neg (by simp <;> omega)]

theorem nD_of_gates (XI : ExecInst) (hg : setupGates XI = true) : XI.k + 1 ≤ XI.nD := by
  unfold setupGates at hg
  simp only [Bool.and_eq_true, ge_iff_le, decide_eq_true_eq, beq_iff_eq] at hg
  omega

/-- the root of a non-leaf skeleton -/
def rootIdx : (s : Skeleton) → s ≠ .leaf → SkeletonInternalIndex s
  | .leaf, h => absurd rfl h
  | .internal _ _, _ => .ofInternal

/-- an internal index of the first FRI layer's skeleton: its root (`nD ≥ k + 1 ≥ 2`) -/
def dfltX (XI : ExecInst) (hg : setupGates XI = true) (hk : 1 ≤ XI.k) :
    MAddress ((List.finRange XI.k).map (friSkel XI)) :=
  ⟨⟨0, by simp; omega⟩, rootIdx _ (by
    have hnD := nD_of_gates XI hg
    have h2 : 2 ≤ 2 ^ (XI.nD - (0 + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (XI.nD - (0 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨a, b, hab⟩ := skelOf_internal (friSpec (2 ^ (XI.nD - (0 + 1)))) _ h2
    have hh : ((List.finRange XI.k).map (friSkel XI)).get ⟨0, by simp; omega⟩ = .internal a b := by
      simpa [friSkel, List.getElem_map, List.getElem_finRange] using hab
    rw [hh]; intro h; cases h)⟩

end NockvmE2E.Exec.SideInst

#print axioms NockvmE2E.Exec.SideInst.skelsSide_get0
#print axioms NockvmE2E.Exec.SideInst.friSkel_eq_skelFlat
#print axioms NockvmE2E.Exec.SideInst.skelsSide_get_fri
#print axioms NockvmE2E.Exec.SideInst.modelS
#print axioms NockvmE2E.Exec.SideInst.decSX_ctx_length
#print axioms NockvmE2E.Exec.SideInst.decCtx_encCtx
#print axioms NockvmE2E.Exec.SideInst.ctx_tail
#print axioms NockvmE2E.Exec.SideInst.hC2X
#print axioms NockvmE2E.Exec.SideInst.dfltX
#print axioms NockvmE2E.Exec.SideInst.sideOfX
#print axioms NockvmE2E.Exec.SideInst.fkOfX
#print axioms NockvmE2E.Exec.SideInst.GX
