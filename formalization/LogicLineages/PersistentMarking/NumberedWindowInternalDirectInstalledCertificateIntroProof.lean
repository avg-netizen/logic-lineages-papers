module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledCertificateIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectCoreTargets (Cut dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalDirectCoreIntroProof (exact_OriginalDCoreFromCut)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules)

/-- Introduce the actual odd certificate judgment of the freshly installed
original body, at the same raw source and target and the genuine tagged
witness, from its four actual physical checker reports. -/
theorem exact_LiteralInstalledOddCertificateIntro (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (s t kept removed inserted : OTerm α)
    (reports : Cut i r permutation (sourceBody (literalData i r) c) Γ s t kept removed inserted) :
    Nonempty (Derivation (sourceBody (literalData i r) c) Γ
      (certificate (literalData i r) true c s t (tripleTerm 5 kept removed inserted))) :=
  (exact_CertificateRules i (jRaw i) r (dCore i r permutation) true c
    (sourceBody (literalData i r) c) α Γ s t (tripleTerm 5 kept removed inserted)).2
    (exact_OriginalDCoreFromCut i r permutation s t kept removed inserted reports)

#print axioms exact_LiteralInstalledOddCertificateIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledCertificateIntroProof
