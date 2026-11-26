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
attribute [local irreducible] programGraph OriginalRootObservation.rootObservation
  OriginalHereditaryReturn.returnRoot InternalPairing.pairing InternalUnpair.left
  InternalUnpair.right InternalListCodec.consCode OriginalNumericListSort.sort
  OriginalHeadClassNumber.classNumber OriginalTypedArgumentObservations.argumentObservations

theorem ordinarySubstitution : ReturnSubstitutionTargets.Ordinary := by
  intro Q body alpha Delta input parameter typ raw payload head base first second returned h0 h1 h2 h3 h4
  let p0 : Program 3 := .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => .projection 0)
  let p1 : Program 3 := .composition OriginalNumericListSort.sort (fun _ : Fin 1 => .projection 1)
  let p2 : Program 3 := pairOf (p0) (p1)
  let p3 : Program 3 := pairOf (.projection 2) (p2)
  let p4 : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 4) (p3)
  let qs : Fin 5 → Program 3 := ![p0,p1,p2,p3,p4]
  let xs : Fin 3 → OTerm alpha := Fin.cons head (Fin.cons first (Fin.cons typ (Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 3 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (first.relabel j) (Fin.cons (typ.relabel j) (Fin.elim0)))
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
  have q4 : Nonempty (Derivation body Theta (programGraph p4 (ys 4) xx)) := hq 4
  have h0 := renameInto h0 j Theta hj
  have h1 := renameInto h1 j Theta hj
  have h2 := renameInto h2 j Theta hj
  have h3 := renameInto h3 j Theta hj
  have h4 := renameInto h4 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename] at h0 h1 h2 h3 h4
  have b0 := unaryRecover OriginalHeadClassNumber.classNumber (.projection 0) (ys 0) (head.relabel j) xx q0 (projectionValue 0 xx)
  have b1 := unaryRecover OriginalNumericListSort.sort (.projection 1) (ys 1) (first.relabel j) xx q1 (projectionValue 1 xx)
  have b2 := binaryRecover InternalPairing.pairing (p0) (p1)
    (ys 2) (ys 0) (ys 1) xx q2 q0 q1
  have b3 := binaryRecover InternalPairing.pairing (.projection 2) (p2)
    (ys 3) (typ.relabel j) (ys 2) xx q3 (projectionValue 2 xx) q2
  have b4 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 4) (p3)
    (ys 4) (numeral 4) (ys 3) xx q4 (constantValue 4 xx) q3
  have returnedGraph := OriginalHereditaryReturnInternalStatementChecks.exactOrdinary
    body beta Theta (input.relabel j) (first.relabel j) (second.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (head.relabel j) (base.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    h0 h1 h2 b0 b1 b2 b3 b4
  have observationGraph := OriginalRootObservationComplexProof.ordinaryLaw Q
    body beta Theta (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (head.relabel j) (base.relabel j) (ys 0) (first.relabel j) (ys 1) (ys 2) (ys 3) (ys 4)
    h0 h1 h2 b0 h3 b1 b2 b3 b4
  exact finish Q (input.relabel j) (parameter.relabel j) (first.relabel j) (second.relabel j)
    (ys 4) (returned.relabel j) returnedGraph h4 observationGraph


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.ordinarySubstitution
