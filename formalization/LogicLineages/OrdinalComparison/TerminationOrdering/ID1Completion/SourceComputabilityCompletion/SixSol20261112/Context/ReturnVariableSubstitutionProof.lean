module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph OriginalRootObservation.rootObservation
  OriginalHereditaryReturn.returnRoot InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListCodec.consCode OriginalNumericListSort.sort
  OriginalHeadClassNumber.classNumber OriginalTypedArgumentObservations.argumentObservations

theorem variableSubstitution : ReturnSubstitutionTargets.Variable := by
  intro Q body alpha Delta input parameter typ raw index first second returned h0 h1 h2
  let p0 : Program 2 := pairOf (.projection 0) (.projection 1)
  let p1 : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (p0)
  let qs : Fin 2 → Program 2 := ![p0,p1]
  let xs : Fin 2 → OTerm alpha := Fin.cons typ (Fin.cons index (Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 2 → OTerm beta := Fin.cons (typ.relabel j) (Fin.cons (index.relabel j) (Fin.elim0))
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ (fun k => Fin.elim0 k) i
      rfl
  rw [hx] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph p0 (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph p1 (ys 1) xx)) := hq 1
  have h0 := renameInto h0 j Theta hj
  have h1 := renameInto h1 j Theta hj
  have h2 := renameInto h2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at h0 h1 h2
  have b0 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (typ.relabel j) (index.relabel j) xx q0 (projectionValue 0 xx) (projectionValue 1 xx)
  have b1 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (p0)
    (ys 1) (numeral 0) (ys 0) xx q1 (constantValue 0 xx) q0
  have returnedGraph := OriginalHereditaryReturnInternalStatementChecks.exactVariable
    body beta Theta (input.relabel j) (first.relabel j) (second.relabel j) (typ.relabel j) (raw.relabel j) (index.relabel j) (ys 0) (ys 1)
    h0 h1 b0 b1
  have observationGraph := OriginalRootObservationInternalProof.variableLaw Q
    body beta Theta (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (index.relabel j) (ys 0) (ys 1)
    h0 h1 b0 b1
  exact finish Q (input.relabel j) (parameter.relabel j) (first.relabel j) (second.relabel j)
    (ys 1) (returned.relabel j) returnedGraph h2 observationGraph


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.variableSubstitution
