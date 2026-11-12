module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTail
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The once-guarded OBSERVED minimum, not any later final fold/tuple. All
Objects, context cons and erasure outputs are literal original Program graphs. -/
def Premises (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    {alpha : Type} (seed out parameter context extended d gamma tailParameter
      seedObject outObject erasedSeedObject erasedOutObject erasedSeed erasedOut : OTerm alpha) : Formula alpha :=
  OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
    (graph2 InternalPairing.pairing parameter context extended ⊓
      (graph2 InternalListCodec.consCode extended d gamma ⊓
        (graph2 (OriginalClassContextObserverSelection.inputs p H G W P).base.oldRepresentative out seed parameter ⊓
          (graph2 InternalPairing.pairing seedObject extended seed ⊓
            (graph2 InternalPairing.pairing outObject extended out ⊓
              (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSeedObject seedObject ⊓
                (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedOutObject outObject ⊓
                  (graph2 InternalPairing.pairing erasedSeedObject gamma erasedSeed ⊓
                    (graph2 InternalPairing.pairing erasedOutObject gamma erasedOut ⊓
                      graph2 InternalPairing.pairing tailParameter context gamma)))))))))

def Result (R : Program 2) {alpha : Type} (erasedSeed erasedOut tailParameter key rank : OTerm alpha) : Formula alpha :=
  ((graph2 R key erasedSeed tailParameter).iff (graph2 R key erasedOut tailParameter)) ⊓
    ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedSeed).iff
      (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTail
