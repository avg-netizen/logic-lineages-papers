module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionSupportProof
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
theorem applicationSubstitution : ReturnSubstitutionTargets.Application := by
  intro Q body alpha Delta input parameter typ raw payload domain children fnRaw argRaw fnType fnPacked argPacked first second returned h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  let p0 : Program 5 := pairOf (.projection 0) (.projection 1)
  let p1 : Program 5 := pairOf (.projection 2) (.projection 3)
  let p2 : Program 5 := pairOf (p0) (p1)
  let p3 : Program 5 := pairOf (.projection 4) (p2)
  let p4 : Program 5 := pairOf (.projection 2) (p3)
  let p5 : Program 5 := pairOf (OriginalRawSyntaxTransport.constant 5 2) (p4)
  let qs : Fin 6 → Program 5 := ![p0,p1,p2,p3,p4,p5]
  let xs : Fin 5 → OTerm alpha := Fin.cons fnType (Fin.cons first (Fin.cons domain (Fin.cons second (Fin.cons typ (Fin.elim0)))))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 5 → OTerm beta := Fin.cons (fnType.relabel j) (Fin.cons (first.relabel j) (Fin.cons (domain.relabel j) (Fin.cons (second.relabel j) (Fin.cons (typ.relabel j) (Fin.elim0)))))
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
  rw [hx] at hq
  have h0 := renameInto h0 j Theta hj
  have h1 := renameInto h1 j Theta hj
  have h2 := renameInto h2 j Theta hj
  have h3 := renameInto h3 j Theta hj
  have h4 := renameInto h4 j Theta hj
  have h5 := renameInto h5 j Theta hj
  have h6 := renameInto h6 j Theta hj
  have h7 := renameInto h7 j Theta hj
  have h8 := renameInto h8 j Theta hj
  have h9 := renameInto h9 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have b0 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (fnType.relabel j) (first.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have b1 := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 1) (domain.relabel j) (second.relabel j) xx (hq 1) (projectionValue 2 xx) (projectionValue 3 xx)
  have b2 := binaryRecover InternalPairing.pairing (p0) (p1)
    (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
  have b3 := binaryRecover InternalPairing.pairing (.projection 4) (p2)
    (ys 3) (typ.relabel j) (ys 2) xx (hq 3) (projectionValue 4 xx) (hq 2)
  have b4 := binaryRecover InternalPairing.pairing (.projection 2) (p3)
    (ys 4) (domain.relabel j) (ys 3) xx (hq 4) (projectionValue 2 xx) (hq 3)
  have b5 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 5 2) (p4)
    (ys 5) (numeral 2) (ys 4) xx (hq 5) (constantValue 2 xx) (hq 4)
  have returnedGraph := OriginalHereditaryReturnInternalStatementChecks.exactApplication
    body beta Theta (input.relabel j) (first.relabel j) (second.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (domain.relabel j) (children.relabel j) (fnRaw.relabel j) (argRaw.relabel j) (fnType.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    h0 h1 h2 h3 h4 b0 b1 b2 b3 b4 b5
  have observationGraph := OriginalRootObservationInternalProof.applicationLaw Q
    body beta Theta (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (children.relabel j) (payload.relabel j) (fnRaw.relabel j) (argRaw.relabel j) (fnType.relabel j) (fnPacked.relabel j) (argPacked.relabel j) (first.relabel j) (second.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    h0 h1 h2 h3 h4 h5 h6 h7 h8 b0 b1 b2 b3 b4 b5
  exact finish Q (input.relabel j) (parameter.relabel j) (first.relabel j) (second.relabel j)
    (ys 5) (returned.relabel j) returnedGraph h9 observationGraph


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.applicationSubstitution
