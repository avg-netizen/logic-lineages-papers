module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputability
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication OriginalVariableObject
open SourceComputabilityFormulaSupportProof (numeral)

/-- Genuine original C, including arrow C, for every typed original variable
Object. Gamma stays internal; neither type-window membership nor an assumed
accessibility/neutral expansion principle is added to the antecedent. -/
def VariableComputable (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (tau : Ty) (alpha : Type) (Gamma : List (Formula alpha)) (object : OTerm alpha),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    ((typed comp tau (numeral context) object ⊓ variableObject object).imp
      (computable comp tau (numeral context) object)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputability
