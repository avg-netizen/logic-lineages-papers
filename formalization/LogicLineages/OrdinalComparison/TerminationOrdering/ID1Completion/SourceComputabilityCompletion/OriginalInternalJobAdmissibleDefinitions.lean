module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissible
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalUniverseDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ArgumentsMatrix {alpha : Type} (H : Program 1) (M W : Program 2)
 (raw gamma c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 ArgumentsAccepted H M W (.var (.inr 0)) (raw.relabel Sum.inl) (gamma.relabel Sum.inl) (c.relabel Sum.inl)
def ArgumentsWitness {alpha : Type} (H : Program 1) (M W : Program 2)
 (raw gamma c : OTerm alpha) : Formula alpha := existsOne (ArgumentsMatrix H M W raw gamma c)
/-- Role-one jobs store type zero, but acceptance retains an existential actual
argument-types code. Fixed original context c is never replaced by Gamma. -/
def Admissible {alpha : Type} (H : Program 1) (M W : Program 2)
 (role typ raw gamma c : OTerm alpha) : Formula alpha :=
 (equal role (numeral 0) ⊓ TermAccepted H M W typ raw gamma c) ⊔
 (equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓ ArgumentsWitness H M W raw gamma c))
def ReturnShape {alpha : Type} (role typ tag : OTerm alpha) : Formula alpha :=
 equal role (numeral 0) ⊔
 (equal role (numeral 1) ⊓ (equal typ (numeral 0) ⊓
  (equal tag (numeral 6) ⊔ equal tag (numeral 7))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissible
