module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof
open InternalAdditionLawsProof (add)
open InternalUnpairArithmeticProof (leftWeakAdd)
open InternalSquareRootArithmeticSupportProof (rightSuccessor)
open InternalRecursionGraphExtensionSupportProof (successorOrder)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroChildren (count nodes : OTerm alpha) :
 Nonempty (Derivation body Delta (ltF count (suc (suc (suc (mass count nodes)))))) :=
 rightSuccessor count (suc (suc (mass count nodes)))
   (rightSuccessor count (suc (mass count nodes)) (leftWeakAdd count (add nodes nodes)))

theorem oneChild (count nodes : OTerm alpha) :
 Nonempty (Derivation body Delta (ltF (suc count) (suc (suc (suc (mass count nodes)))))) :=
 rightSuccessor (suc count) (suc (suc (mass count nodes)))
   (successorOrder count (suc (mass count nodes)) (leftWeakAdd count (add nodes nodes)))

theorem twoChildren (count nodes : OTerm alpha) :
 Nonempty (Derivation body Delta (ltF (suc (suc count)) (suc (suc (suc (mass count nodes)))))) :=
 successorOrder (suc count) (suc (suc (mass count nodes)))
   (successorOrder count (suc (mass count nodes)) (leftWeakAdd count (add nodes nodes)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthArithmeticProof
