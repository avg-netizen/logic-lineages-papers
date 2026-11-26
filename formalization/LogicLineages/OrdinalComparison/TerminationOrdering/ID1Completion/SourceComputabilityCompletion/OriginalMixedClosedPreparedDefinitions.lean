module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrepared
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedPrepared (prepared member)
/-- Explicit new closed checker over the literal prepared raw leaf. No selected final checker identity. -/
def checker (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 4 :=
 OriginalHereditaryLambdaGlobal.closedLeaf (OriginalMixedLiteralEndpointDefinitions.endpoint H G (member p) W)
  (prepared p H G W).window (prepared p H G W).oldStep
/-- Internal closed-output restricted trace with literal prepared raw input. No later final leaf is named. -/
def ClosedTrace (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop := ∀
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (prepared p H G W).base.oldSource (numeral 1) s oldParam ⊓
   (graph4 (prepared p H G W).oldStep (numeral 1) s t cert oldParam ⊓
   (graph4 (OriginalMixedDirectBottomTrace.recognizes (prepared p H G W).base.oldSource (prepared p H G W).oldStep) (numeral 1) s t cert oldParam ⊓
   (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
   (graph2 InternalPairing.pairing oldParam c extended ⊓
   (graph2 InternalPairing.pairing newParam c gamma ⊓
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
    graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))))).imp
   (graph2 (prepared p H G W).base.oldSource (numeral 1) erasedS newParam ⊓
    OriginalExistentialRankResultDefinitions.Result (checker p H G W) erasedS erasedT newParam s t)))

def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
 OriginalMixedPrepared.Properties n arity p H G W P ∧ ClosedTrace p H G W
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrepared
