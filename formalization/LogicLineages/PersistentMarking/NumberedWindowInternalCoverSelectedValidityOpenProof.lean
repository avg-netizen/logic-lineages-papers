module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem observeHeaders (xs : List (Nat × Nat)) (q : OTerm α)
    (actual : Nonempty (Derivation body Γ (unary (headerAny xs) (suc z) q))) :
    Nonempty (Derivation body Γ (headersAt xs q)) := by
  induction xs generalizing Γ with
  | nil =>
    exact valueUnique (constantZero 1) (suc z) z ![q] actual (zeroConstantValue ![q])
  | cons part rest ih =>
    obtain ⟨tag, arity⟩ := part
    let A := headerAt tag arity q
    change Nonempty (Derivation body Γ (A ⊔ headersAt rest q))
    apply formulaCases A _
    · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
    · have reject := normalizeReject (body := body) (Gamma := A.not :: Γ) (header tag arity)
        ![q] ⟨Derivation.hypothesis List.mem_cons_self⟩
      have next := zeroBranchElim _ (headerAny rest) (constantOne 1) (suc z) ![q]
        reject (withHyp actual A.not)
      obtain ⟨row⟩ := ih next
      exact ⟨orRight row⟩

theorem exact_OpenCoverSelectedValidityHeaders : ExactOpenCoverSelectedValidityHeaders := by
  intro V body α Γ q actual
  obtain ⟨parts⟩ := conjunctionRecover V (headerAny layout) ![q] actual
  obtain ⟨headers⟩ := observeHeaders layout q ⟨Derivation.conjunctionRight parts⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft parts) headers⟩

#print axioms exact_OpenCoverSelectedValidityHeaders

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityOpenProof
