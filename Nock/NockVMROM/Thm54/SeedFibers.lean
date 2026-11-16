import Nock.NockVM

/-!
# Exact finite seed-fiber counting for Theorem 5.4

The NPR seed changes the committed fingerprints and therefore changes the labels seen by the walk
argument.  The finite experiment is consequently a family of fixed-label walk events indexed by
the seed, followed by cardinality summation over those fibers.  Nothing below asserts independence
between the seed and the walk labels.

This module closes only that finite counting layer.
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical

noncomputable section

open Nock Nock.Walk

/-! ## Generic finite fiber counting -/

/-- A finite event whose fiber over `a` is `bad a`. -/
def fiberEvent {A Ω : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq Ω]
    (seeds : Finset A) (bad : A → Finset Ω) : Finset (A × Ω) :=
  (seeds.product Finset.univ).filter (fun x => x.2 ∈ bad x.1)

/-- Finite fiber summation.  This is a counting argument, not an independence argument. -/
theorem fiberEvent_card_le {A Ω : Type*} [Fintype Ω] [DecidableEq A] [DecidableEq Ω]
    (seeds : Finset A) (bad : A → Finset Ω) (B : ℕ)
    (hB : ∀ a ∈ seeds, (bad a).card ≤ B) :
    (fiberEvent seeds bad).card ≤ seeds.card * B := by
  classical
  let U : Finset (A × Ω) :=
    seeds.biUnion (fun a => (bad a).image (fun ω => (a, ω)))
  calc
    (fiberEvent seeds bad).card ≤ U.card := Finset.card_le_card (by
      intro x hx
      rw [fiberEvent] at hx
      obtain ⟨hprod, hbad⟩ := Finset.mem_filter.mp hx
      have hseed : x.1 ∈ seeds := (Finset.mem_product.mp hprod).1
      exact Finset.mem_biUnion.mpr
        ⟨x.1, hseed, Finset.mem_image.mpr ⟨x.2, hbad, rfl⟩⟩)
    _ ≤ ∑ a ∈ seeds, ((bad a).image (fun ω => (a, ω))).card := by
      dsimp only [U]
      exact Finset.card_biUnion_le
    _ ≤ ∑ a ∈ seeds, (bad a).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ _a ∈ seeds, B := Finset.sum_le_sum hB
    _ = seeds.card * B := by rw [Finset.sum_const, smul_eq_mul]

/-! ## Nonzero-seed and all-seed sample spaces -/

/-- Seeds admitted by `ComputeTable.computeAIR`'s `z * zinv = 1` gate. -/
def validSeeds (K : Type*) [Fintype K] [Zero K] [DecidableEq K] : Finset K :=
  Finset.univ.erase 0

@[simp]
theorem mem_validSeeds {K : Type*} [Fintype K] [Zero K] [DecidableEq K] (z : K) :
    z ∈ validSeeds K ↔ z ≠ 0 := by
  simp [validSeeds]

@[simp]
theorem validSeeds_card {K : Type*} [Fintype K] [Zero K] [DecidableEq K] :
    (validSeeds K).card = Fintype.card K - 1 := by
  simp [validSeeds]

/-- Joint coin space for a valid nonzero seed `z` and walk coins `(α, γ)`. -/
def validCoinSpace (K : Type*) [Fintype K] [Zero K] [DecidableEq K] :
    Finset (K × (K × K)) :=
  (validSeeds K).product Finset.univ

/-- The exact valid-seed denominator is `(|K| - 1)|K|²`. -/
@[simp]
theorem validCoinSpace_card {K : Type*} [Fintype K] [Zero K] [DecidableEq K] :
    (validCoinSpace K).card =
      (Fintype.card K - 1) * (Fintype.card K * Fintype.card K) := by
  simp [validCoinSpace]

/-- Joint coin space when zero is sampled as well. -/
def allCoinSpace (K : Type*) [Fintype K] [DecidableEq K] : Finset (K × (K × K)) :=
  Finset.univ.product Finset.univ

/-- The exact all-seed denominator is `|K|³`. -/
@[simp]
theorem allCoinSpace_card {K : Type*} [Fintype K] [DecidableEq K] :
    (allCoinSpace K).card =
      Fintype.card K * (Fintype.card K * Fintype.card K) := by
  simp [allCoinSpace]

/-- If all field elements are sampled, the entire `z = 0` fiber is explicitly bad. -/
def fiberEventWithZero {K Ω : Type*} [Fintype K] [Fintype Ω]
    [Zero K] [DecidableEq K] [DecidableEq Ω] (bad : K → Finset Ω) : Finset (K × Ω) :=
  (({0} : Finset K).product Finset.univ) ∪ fiberEvent (validSeeds K) bad

/-- All-seed bound: one full zero fiber plus the sum over the `|K| - 1` valid fibers. -/
theorem fiberEventWithZero_card_le {K Ω : Type*} [Fintype K] [Fintype Ω]
    [Zero K] [DecidableEq K] [DecidableEq Ω] (bad : K → Finset Ω) (B : ℕ)
    (hB : ∀ z ∈ validSeeds K, (bad z).card ≤ B) :
    (fiberEventWithZero bad).card ≤
      Fintype.card Ω + (Fintype.card K - 1) * B := by
  unfold fiberEventWithZero
  calc
    (({0} : Finset K).product Finset.univ ∪ fiberEvent (validSeeds K) bad).card
        ≤ (({0} : Finset K).product Finset.univ).card
            + (fiberEvent (validSeeds K) bad).card := Finset.card_union_le _ _
    _ ≤ Fintype.card Ω + (Fintype.card K - 1) * B :=
      Nat.add_le_add (by simp) (by
        simpa using fiberEvent_card_le (validSeeds K) bad B hB)

/-! ## Seed-indexed walk-label families -/

/-- Rows and child rows are regenerated at each NPR seed rather than held fixed across seeds. -/
structure ZLabelFamily (K S DT : Type*) where
  row : K → ℕ → S × DT
  child : K → ℕ → ℕ → S × DT

/-- Replacing `Inputs.z` drives a seed-indexed compute-label generator. -/
def computeInputsAtZ {K : Type*} (inp : ComputeTable.Inputs K) (z : K) :
    ComputeTable.Inputs K :=
  { inp with z := z }

@[simp]
theorem computeInputsAtZ_z {K : Type*} (inp : ComputeTable.Inputs K) (z : K) :
    (computeInputsAtZ inp z).z = z :=
  rfl

/-- The fixed-seed walk bad event.  Its labels are fixed after selecting `z`. -/
def walkBadFiber {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ) (h : ℕ) (z : K) : Finset (K × K) :=
  NockVM.walkBad St enc (labels.row z) (labels.child z) fo h

/-- `walkBad_prob` applies after fixing `z`; no relation between distinct fibers is used. -/
theorem walkBadFiber_prob {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    ((walkBadFiber St enc labels fo h z).card : ℚ) /
        ((Fintype.card K : ℚ) * Fintype.card K) ≤
      (h : ℚ) / Fintype.card K +
        ((h * (node_size - 1) : ℕ) : ℚ) / Fintype.card K :=
  NockVM.walkBad_prob St enc hEnc (labels.row z) (labels.child z) fo
    hSf hvalid harity (hfo z) (hF z)

/-- Cardinality form of the fixed-seed walk application. -/
theorem walkBadFiber_card_le {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    (walkBadFiber St enc labels fo h z).card ≤
      Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  simpa only [walkBadFiber, NockVM.walkBad] using
    Walk_IOP_final_card St enc hEnc (labels.row z) (labels.child z) fo
      hSf hvalid harity (hfo z) (hF z)

/-- Nonzero-seed joint walk event in the finite coin space `(z, α, γ)`. -/
def walkBadJoint {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ) (h : ℕ) : Finset (K × (K × K)) :=
  fiberEvent (validSeeds K) (walkBadFiber St enc labels fo h)

/-- Honest fiber-summed walk bound over nonzero seeds. -/
theorem walkBadJoint_card_le {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadJoint St enc labels fo h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) := by
  unfold walkBadJoint
  simpa using fiberEvent_card_le (validSeeds K) (walkBadFiber St enc labels fo h)
    (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) (by
      intro z _
      exact walkBadFiber_card_le St enc hEnc labels fo hSf hvalid harity hfo hF z)

theorem walkBadFiber_card_le_of_label {K S DT L : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    (walkBadFiber St enc labels fo h z).card ≤
      Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  simpa only [walkBadFiber, NockVM.walkBad] using
    Walk_IOP_final_card_of_label St labelOf hResp enc hEnc (labels.row z) (labels.child z) fo
      hSf hvalid harity (hfo z) (hF z)

theorem walkBadJoint_card_le_of_label {K S DT L : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadJoint St enc labels fo h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) := by
  unfold walkBadJoint
  simpa using fiberEvent_card_le (validSeeds K) (walkBadFiber St enc labels fo h)
    (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) (by
      intro z _
      exact walkBadFiber_card_le_of_label St labelOf hResp enc hEnc labels fo hSf hvalid harity
        hfo hF z)

/-! ## Forest slices -/

/-- The fixed-seed forest walk bad event. -/
def walkBadForestFiber {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ) (kroots h : ℕ) (z : K) :
    Finset (K × K) :=
  NockVM.walkBadForest St enc (labels.row z) (labels.child z) fo kroots h

/-- `walkBadForest_prob` applies independently to every fixed-seed label slice. -/
theorem walkBadForestFiber_prob {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    ((walkBadForestFiber St enc labels fo kroots h z).card : ℚ) /
        ((Fintype.card K : ℚ) * Fintype.card K) ≤
      (h : ℚ) / Fintype.card K +
        ((h * (node_size - 1) : ℕ) : ℚ) / Fintype.card K :=
  NockVM.walkBadForest_prob St enc hEnc (labels.row z) (labels.child z) fo
    hk hSf hvalid harity (hfo z) (hF z)

/-- Cardinality form of the fixed-seed forest application. -/
theorem walkBadForestFiber_card_le
    {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    (walkBadForestFiber St enc labels fo kroots h z).card ≤
      Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  simpa only [walkBadForestFiber, NockVM.walkBadForest] using
    Walk_IOP_forest_final_card St enc hEnc (labels.row z) (labels.child z) fo
      hk hSf hvalid harity (hfo z) (hF z)

theorem walkBadForestFiber_card_le_of_label
    {K S DT L : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (z : K) :
    (walkBadForestFiber St enc labels fo kroots h z).card ≤
      Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  simpa only [walkBadForestFiber, NockVM.walkBadForest] using
    Walk_IOP_forest_final_card_of_label St labelOf hResp enc hEnc (labels.row z)
      (labels.child z) fo hk hSf hvalid harity (hfo z) (hF z)

/-- Nonzero-seed joint forest event in the finite coin space `(z, α, γ)`. -/
def walkBadForestJoint {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ) (kroots h : ℕ) :
    Finset (K × (K × K)) :=
  fiberEvent (validSeeds K) (walkBadForestFiber St enc labels fo kroots h)

/-- Honest fiber-summed forest bound over nonzero seeds. -/
theorem walkBadForestJoint_card_le
    {K S DT : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadForestJoint St enc labels fo kroots h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) := by
  unfold walkBadForestJoint
  simpa using fiberEvent_card_le (validSeeds K)
    (walkBadForestFiber St enc labels fo kroots h)
    (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) (by
      intro z _
      exact walkBadForestFiber_card_le St enc hEnc labels fo
        hk hSf hvalid harity hfo hF z)

theorem walkBadForestJoint_card_le_of_label
    {K S DT L : Type*} [Field K] [Fintype K] [DecidableEq K]
    {n node_size : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (labels : ZLabelFamily K S DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h → fo i = St.fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      F (labels.row z i)
        (fun j : Fin n => if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none)) :
    (walkBadForestJoint St enc labels fo kroots h).card ≤
      (Fintype.card K - 1) *
        (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) := by
  unfold walkBadForestJoint
  simpa using fiberEvent_card_le (validSeeds K)
    (walkBadForestFiber St enc labels fo kroots h)
    (Fintype.card K * h + Fintype.card K * (h * (node_size - 1))) (by
      intro z _
      exact walkBadForestFiber_card_le_of_label St labelOf hResp enc hEnc labels fo
        hk hSf hvalid harity hfo hF z)

/-! ## Import-independent NPR collision lift -/

/-- Lift a finite set of bad seeds to all auxiliary coins over every bad seed. -/
def seedBadJoint {K Ω : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq Ω]
    (badSeeds : Finset K) : Finset (K × Ω) :=
  fiberEvent badSeeds (fun _ => Finset.univ)

/-- A seed-cardinality bound lifts by the exact size of the auxiliary coin space. -/
theorem seedBadJoint_card_le {K Ω : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq Ω]
    (badSeeds : Finset K) (B : ℕ) (hbad : badSeeds.card ≤ B) :
    (seedBadJoint (Ω := Ω) badSeeds).card ≤ B * Fintype.card Ω := by
  unfold seedBadJoint
  refine le_trans
    (fiberEvent_card_le badSeeds (fun _ => Finset.univ) (Fintype.card Ω) ?_) ?_
  · intro z hz
    simp
  · exact Nat.mul_le_mul_right _ hbad

/-- Lift failures of an NPR separating-seed predicate to all walk coins `(α, γ)`.

`SepSeed` is an explicit interface so this production module does not depend on a scratch
recognizer.  A production recognizer can specialize it with its own separating predicate.
-/
def sepSeedJointBad {K : Type*} [Fintype K] [DecidableEq K]
    (SepSeed : K → Noun → Noun → Prop) (P Q : Noun) : Finset (K × (K × K)) :=
  seedBadJoint
    (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q))

/-- Any NPR bad-seed bound `≤ 2Λ - 1` lifts to the joint bound `(2Λ - 1)|K|²`.

The hypothesis is exactly the import-independent seam to the production global-carry recognizer's
Schwartz--Zippel theorem.
-/
theorem sepSeedJointBad_card_le {K : Type*} [Fintype K] [DecidableEq K]
    (SepSeed : K → Noun → Noun → Prop) (Λ : ℕ) (P Q : Noun)
    (hsep :
      (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q)).card ≤ 2 * Λ - 1) :
    (sepSeedJointBad SepSeed P Q).card ≤
      (2 * Λ - 1) * (Fintype.card K * Fintype.card K) := by
  unfold sepSeedJointBad
  simpa using seedBadJoint_card_le
    (Ω := K × K)
    (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q))
    (2 * Λ - 1) hsep

/-!
The counting layer is closed.

1. the explicit zero fiber when zero is sampled;
2. the corresponding fixed-seed walk bad fiber; and
3. the relevant finite union of `sepSeedJointBad` collision events.

No false-acceptance containment theorem is claimed here.
-/

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.fiberEvent_card_le
#print axioms Nock.NockVMROM.Thm54.validCoinSpace_card
#print axioms Nock.NockVMROM.Thm54.fiberEventWithZero_card_le
#print axioms Nock.NockVMROM.Thm54.walkBadFiber_prob
#print axioms Nock.NockVMROM.Thm54.walkBadJoint_card_le
#print axioms Nock.NockVMROM.Thm54.walkBadForestFiber_prob
#print axioms Nock.NockVMROM.Thm54.walkBadForestJoint_card_le
#print axioms Nock.NockVMROM.Thm54.sepSeedJointBad_card_le
