module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomy
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact certificate code AND acceptance by the same supplied leaf. -/
def WitnessFields (leaf : Program 4) {alpha : Type} (s t parameter cert : OTerm alpha) : Formula alpha :=
  graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓
    graph4 leaf InternalOriginalStepGuard.one s t cert parameter

def WitnessMatrix (leaf : Program 4) {alpha : Type} (s t parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  WitnessFields leaf (s.relabel Sum.inl) (t.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0))

def Witness (leaf : Program 4) {alpha : Type} (s t parameter : OTerm alpha) : Formula alpha :=
  existsOne (WitnessMatrix leaf s t parameter)

/-- Root direct-bottom dichotomy only. No strict rank statement in either
branch, no quotient equality, and no general erasure transformer is asserted. -/
def Result (leaf : Program 4) {alpha : Type} (s t parameter : OTerm alpha) : Formula alpha :=
  equal s t ⊔ Witness leaf s t parameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomy
