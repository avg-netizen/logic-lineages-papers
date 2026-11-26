module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAlgebraTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortStabilityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort
/-- Actual sorting commutes with actual insertion, on arbitrary raw numeric
lists and actual output graphs. No sortedness or native semantics premise. -/
def Absorption : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (raw x inserted sorted left right : OTerm alpha),
 Nonempty (Derivation body []
 ((graph2 insert inserted raw x ⊓ (graph1 sort sorted raw ⊓
 (graph1 sort left inserted ⊓ graph2 insert right sorted x))).imp (equal left right)))
/-- Two actual runs of the unchanged sort, on arbitrary numeric inputs. -/
def Idempotence : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (raw sorted again : OTerm alpha),
 Nonempty (Derivation body []
 ((graph1 sort sorted raw ⊓ graph1 sort again sorted).imp (equal again sorted)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortStabilityTargets
