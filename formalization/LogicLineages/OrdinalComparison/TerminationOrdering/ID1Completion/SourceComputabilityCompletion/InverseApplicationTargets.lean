module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward SourceComputabilityCompletion.InverseApplication

/-- An internal inverse-application derivation in the original scalar slice.
The four premises are local arithmetic rules about the literal original
program graphs. Concrete source assembly must discharge them; this relative
component alone is not paper06 accessibility, neutral saturation or C-to-I. -/
def ActualOriginalInverseApplication : Prop :=
  ∀ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (context : Nat),
  ArithmeticRules src comp context → ApplicationCompatibility src comp context →
  DomainCarrier src comp context → DomainForward src comp context →
  ∀ (α : Type) (Gamma : List (Formula α)) (sigma tau : Ty) (f a out : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (domain comp context sigma tau f a)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (accepted comp sigma tau (numeral context) f a out)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (membership false out)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (membership false f))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationTargets
