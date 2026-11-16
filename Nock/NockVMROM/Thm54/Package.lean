import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.CanonicalRAP

/-!
# Parameterized exact-package spine

This is an assembly interface, not a statement or proof of paper Theorem 5.4.  The S1, S2, S3,
and S4 objects are indices supplied to the package, rather than user-selectable structure fields.
Every later clause is evaluated at those same four objects.

The six proof fields are explicit placeholders:

* `p10_costs` is refined by P10's AIR-linked final-layer cost certificate.

The language is also an index, and `language_nonempty` mentions it at the supplied S1 object.
Consequently the old G2 shape, in which a package never refers to its language, is unavailable.

This does not repair a self-justifying S2
interface by itself: `HasCanonicalRAP2` separately fixes its AIRs, parameter families, auxiliary
types, and encoders as type indices before an `s2` proof can be supplied here.
-/

namespace Nock.NockVMROM.Thm54

universe uStmt uS1 uS2 uS3 uS4

/-- Dependency-preserving spine for the future exact Theorem 5.4 package.

This declaration intentionally does not bear a theorem alias.
-/
structure NockVMROMThm54Package
    {Statement : Type uStmt}
    {S1 : Type uS1} {S2 : Type uS2} {S3 : Type uS3} {S4 : Type uS4}
    (language : S1 → Statement → Prop)
    (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4)
    (P5Clause P6Clause P7Clause P8Clause P9Clause P10Clause :
      S1 → S2 → S3 → S4 → Prop) : Prop where
  /-- The selected S1 language has a genuine member; the language parameter is load-bearing. -/
  language_nonempty : ∃ x, language s1 x
  p5_oneHot : P5Clause s1 s2 s3 s4
  p6_traversal : P6Clause s1 s2 s3 s4
  p7_jointVerification : P7Clause s1 s2 s3 s4
  p8_concreteSoundness : P8Clause s1 s2 s3 s4
  p9_asymptotic : P9Clause s1 s2 s3 s4
  /-- Placeholder for P10's AIR-linked cost result at the same objects. -/
  p10_costs : P10Clause s1 s2 s3 s4

namespace NockVMROMThm54Package

variable
    {Statement : Type uStmt}
    {S1 : Type uS1} {S2 : Type uS2} {S3 : Type uS3} {S4 : Type uS4}
    {language : S1 → Statement → Prop}
    {s1 : S1} {s2 : S2} {s3 : S3} {s4 : S4}
    {P5Clause P6Clause P7Clause P8Clause P9Clause P10Clause :
      S1 → S2 → S3 → S4 → Prop}

/-- Public projection of the language-referencing nonvacuity obligation. -/
theorem package_language_nonempty
    (pkg : NockVMROMThm54Package language s1 s2 s3 s4
      P5Clause P6Clause P7Clause P8Clause P9Clause P10Clause) :
    ∃ x, language s1 x :=
  pkg.language_nonempty

theorem noPackage_of_language_empty
    (hempty : ∀ x, ¬ language s1 x) :
    ¬ NockVMROMThm54Package language s1 s2 s3 s4
      P5Clause P6Clause P7Clause P8Clause P9Clause P10Clause := by
  intro pkg
  obtain ⟨x, hx⟩ := pkg.language_nonempty
  exact hempty x hx

end NockVMROMThm54Package

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.NockVMROMThm54Package.package_language_nonempty
#print axioms Nock.NockVMROM.Thm54.NockVMROMThm54Package.noPackage_of_language_empty
