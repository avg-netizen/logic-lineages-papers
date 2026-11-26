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

theorem lambdaSubstitution : ReturnSubstitutionTargets.Lambda := by
  intro Q body alpha Delta input parameter typ raw payload domain childRaw codomain childPacked context gamma extended childParam first second returned h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  let p0 : Program 3 := pairOf (.projection 0) (.projection 1)
  let p1 : Program 3 := pairOf (.projection 0) (p0)
  let p2 : Program 3 := pairOf (.projection 2) (p1)
  let p3 : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 1) (p2)
  let qs : Fin 4 → Program 3 := ![p0,p1,p2,p3]
  let xs : Fin 3 → OTerm alpha := Fin.cons codomain (Fin.cons first (Fin.cons domain (Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 3 → OTerm beta := Fin.cons (codomain.relabel j) (Fin.cons (first.relabel j) (Fin.cons (domain.relabel j) (Fin.elim0)))
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ (fun k => Fin.elim0 k) i
        rfl
  rw [hx] at hq
  have q0 : Nonempty (Derivation body Theta (programGraph p0 (ys 0) xx)) := hq 0
  have q1 : Nonempty (Derivation body Theta (programGraph p1 (ys 1) xx)) := hq 1
  have q2 : Nonempty (Derivation body Theta (programGraph p2 (ys 2) xx)) := hq 2
  have q3 : Nonempty (Derivation body Theta (programGraph p3 (ys 3) xx)) := hq 3
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
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have b0 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (codomain.relabel j) (first.relabel j) xx q0 (projectionValue 0 xx) (projectionValue 1 xx)
  have b1 := binaryRecover InternalPairing.pairing (.projection 0) (p0)
    (ys 1) (codomain.relabel j) (ys 0) xx q1 (projectionValue 0 xx) q0
  have b2 := binaryRecover InternalPairing.pairing (.projection 2) (p1)
    (ys 2) (domain.relabel j) (ys 1) xx q2 (projectionValue 2 xx) q1
  have b3 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 1) (p2)
    (ys 3) (numeral 1) (ys 2) xx q3 (constantValue 1 xx) q2
  have returnedGraph := OriginalHereditaryReturnInternalStatementChecks.exactLambda
    body beta Theta (input.relabel j) (first.relabel j) (second.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (domain.relabel j) (childRaw.relabel j) (codomain.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    h0 h1 h2 h3 b0 b1 b2 b3
  have observationGraph := OriginalRootObservationInternalProof.lambdaLaw Q
    body beta Theta (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (codomain.relabel j) (payload.relabel j) (childRaw.relabel j) (childPacked.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j) (childParam.relabel j) (first.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    h0 h1 h2 h3 h4 h5 h6 h7 h8 b0 b1 b2 b3
  exact finish Q (input.relabel j) (parameter.relabel j) (first.relabel j) (second.relabel j)
    (ys 3) (returned.relabel j) returnedGraph h9 observationGraph


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.lambdaSubstitution
