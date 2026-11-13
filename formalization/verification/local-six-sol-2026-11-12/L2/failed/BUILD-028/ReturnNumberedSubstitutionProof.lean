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

theorem numberedSubstitution : ReturnSubstitutionTargets.Numbered := by
  intro Q body alpha Delta input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields base afterBase extraTypes extras first second returned h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  let p0 : Program 5 := .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => .projection 0)
  let p1 : Program 5 := .composition OriginalNumericListSort.sort (fun _ : Fin 1 => .projection 1)
  let p2 : Program 5 := pairOf (p1) (.projection 2)
  let p3 : Program 5 := pairOf (p0) (p2)
  let p4 : Program 5 := pairOf (.projection 3) (p3)
  let p5 : Program 5 := pairOf (.projection 4) (p4)
  let p6 : Program 5 := pairOf (OriginalRawSyntaxTransport.constant 5 5) (p5)
  let qs : Fin 7 → Program 5 := ![p0,p1,p2,p3,p4,p5,p6]
  let xs : Fin 5 → OTerm alpha := Fin.cons head (Fin.cons first (Fin.cons second (Fin.cons typ (Fin.cons label (Fin.elim0)))))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename]
  let xx : Fin 5 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (first.relabel j) (Fin.cons (second.relabel j) (Fin.cons (typ.relabel j) (Fin.cons (label.relabel j) (Fin.elim0)))))
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
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
  have q5 : Nonempty (Derivation body Theta (programGraph p5 (ys 5) xx)) := hq 5
  have q6 : Nonempty (Derivation body Theta (programGraph p6 (ys 6) xx)) := hq 6
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
  have b0 := unaryRecover OriginalHeadClassNumber.classNumber (.projection 0) (ys 0) (head.relabel j) xx q0 (projectionValue 0 xx)
  have b1 := unaryRecover OriginalNumericListSort.sort (.projection 1) (ys 1) (first.relabel j) xx q1 (projectionValue 1 xx)
  have b2 := binaryRecover InternalPairing.pairing (p1) (.projection 2)
    (ys 2) (ys 1) (second.relabel j) xx q2 q1 (projectionValue 2 xx)
  have b3 := binaryRecover InternalPairing.pairing (p0) (p2)
    (ys 3) (ys 0) (ys 2) xx q3 q0 q2
  have b4 := binaryRecover InternalPairing.pairing (.projection 3) (p3)
    (ys 4) (typ.relabel j) (ys 3) xx q4 (projectionValue 3 xx) q3
  have b5 := binaryRecover InternalPairing.pairing (.projection 4) (p4)
    (ys 5) (label.relabel j) (ys 4) xx q5 (projectionValue 4 xx) q4
  have b6 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 5 5) (p5)
    (ys 6) (numeral 5) (ys 5) xx q6 (constantValue 5 xx) q5
  have returnedGraph := OriginalHereditaryReturnInternalStatementChecks.exactNumbered
    body beta Theta (input.relabel j) (first.relabel j) (second.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (label.relabel j) (afterLabel.relabel j) (head.relabel j) (afterHead.relabel j) (encodedType.relabel j) (numberedFields.relabel j) (base.relabel j) (afterBase.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)
    h0 h1 h2 h3 h4 h5 b0 b1 b2 b3 b4 b5 b6
  have observationGraph := OriginalRootObservationComplexProof.numberedLaw Q
    body beta Theta (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (label.relabel j) (afterLabel.relabel j) (head.relabel j) (afterHead.relabel j) (encodedType.relabel j) (numberedFields.relabel j) (base.relabel j) (afterBase.relabel j) (extraTypes.relabel j) (extras.relabel j) (ys 0) (first.relabel j) (ys 1) (second.relabel j) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6)
    h0 h1 h2 h3 h4 h5 h6 b0 h7 b1 h8 b2 b3 b4 b5 b6
  exact finish Q (input.relabel j) (parameter.relabel j) (first.relabel j) (second.relabel j)
    (ys 6) (returned.relabel j) returnedGraph h9 observationGraph

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.numberedSubstitution
