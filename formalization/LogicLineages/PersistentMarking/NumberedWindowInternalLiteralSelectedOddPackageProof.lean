module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountInstallChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalCertifiedUnionStepProof (CertifiedOriginSplit Pr unionGraph)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers LiteralEmptyMembership)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalLiteralCertifiedOriginSplitProof (exact_LiteralCertifiedOriginSplit)
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralJUnion exact_LiteralIToSingletonJ exact_LiteralParsedJ)
open NumberedWindowInternalLiteralJEmptySpecializedProof (exact_LiteralSelectedEmptyJ)
open NumberedWindowInternalAccessibilityChecks (exact_ConcreteInternalAccessibility)
open NumberedWindowInternalLiteralRefinedScalarInstallProof (exact_ReinstallLiteralRefinedScalar)
open NumberedWindowInternalLiteralCountInstallChecks (exact_SelectedLiteralCountTypedListInstall)

structure OriginalOddRules (i : Program 1) (r : Program 3) (c : Nat) : Prop where
  split : CertifiedOriginSplit (literalData i r) c permutation
  zero : LiteralEmptyMembership i r c
  sameUnion : ∀ (α : Type) (Γ : List (Formula α)) (a b u : OTerm α),
    Pr (literalData i r) c Γ (membership true a) →
    Pr (literalData i r) c Γ (membership true b) →
    Pr (literalData i r) c Γ (unionGraph permutation a b u) →
    Pr (literalData i r) c Γ (membership true u)
  singleton : ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    Pr (literalData i r) c Γ ((membership false q).imp (singletonJ q))
  parsed : ∀ (α : Type) (Γ : List (Formula α)) (raw scratch : OTerm α),
    Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![raw] →
    Pr (literalData i r) c Γ (typedAt i scratch) →
    Pr (literalData i r) c Γ (scalarMembers scratch) →
    Pr (literalData i r) c Γ (membership true raw)

theorem exact_OriginalOddRules (i : Program 1) (r : Program 3) (c : Nat) :
    OriginalOddRules i r c :=
  ⟨exact_LiteralCertifiedOriginSplit i r c,exact_LiteralSelectedEmptyJ i r c,
    exact_LiteralJUnion i r c,exact_LiteralIToSingletonJ i r c,exact_LiteralParsedJ i r c⟩

/-- The literal evaluator, interpretation, (A) rules and full J package
are for the exact same freshly selected programs, not separate choices. -/
theorem exact_SelectedLiteralOddPackage (xs : Entries) (s : Settings) :
    ∃ (i : Program 1) (r : Program 3),
      Reinstalled xs s i (jRaw i) r permutation ∧ (∀ c, OriginalOddRules i r c) := by
  obtain ⟨i,r,run⟩ := exact_SelectedLiteralCountTypedListInstall xs s
  exact ⟨i,r,run,exact_OriginalOddRules i r⟩

/-- Same exact package after selecting the original ordinary scalar
refinement, in which typed open bottom/free accessibility is checked. -/
theorem exact_SelectedRefinedLiteralOddPackage (xs : Entries) (s : Settings) :
    ∃ (i : Program 1) (r : Program 3),
      Reinstalled xs s i (jRaw i) (refined i r) permutation ∧
        (∀ c, OriginalOddRules i (refined i r) c) := by
  obtain ⟨i,_j,r,_d,fit,_,_⟩ := exact_ConcreteInternalAccessibility xs s
  exact ⟨i,r,exact_ReinstallLiteralRefinedScalar xs s i r fit.1 fit.2.2.1,
    exact_OriginalOddRules i (refined i r)⟩

#print axioms exact_OriginalOddRules
#print axioms exact_SelectedLiteralOddPackage
#print axioms exact_SelectedRefinedLiteralOddPackage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSelectedOddPackageProof
