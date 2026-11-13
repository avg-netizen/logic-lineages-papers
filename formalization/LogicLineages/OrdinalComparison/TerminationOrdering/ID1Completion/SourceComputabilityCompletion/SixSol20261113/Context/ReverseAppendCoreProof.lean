module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl symm)
open OriginalLambdaTraversalLambdaRootProof (binaryInputs)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open ReverseAppendSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCore (right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields z right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined)) := by
  obtain ⟨hj⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined right (andLeft hf)
  obtain ⟨hl⟩ := valueUnique OriginalTypedArgumentObservations.reverse mappedLeft z ![z]
    (andLeft (andRight hf)) OriginalReverseConsProof.zero
  have ha := binaryInputs InternalApplicationValidityStackAppend.append out mappedRight mappedLeft mappedRight z
    ⟨refl mappedRight⟩ ⟨hl⟩ (andRight (andRight (andRight hf)))
  obtain ⟨ho⟩ := valueUnique InternalApplicationValidityStackAppend.append out mappedRight ![mappedRight,z] ha
    (SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta mappedRight)
  have hv := headTransport OriginalTypedArgumentObservations.reverse mappedRight right joined Fin.elim0
    ⟨symm hj⟩ (andLeft (andRight (andRight hf)))
  exact outputTransport OriginalTypedArgumentObservations.reverse mappedRight out ![joined] ⟨symm ho⟩ hv

theorem consAtValues
    (code head tail right joined parameter mappedLeft mappedRight out tailJoined reverseTail singleton leftCandidate tailOut finalOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row tail)))
    (hf : Nonempty (Derivation body Delta (fields code right joined parameter mappedLeft mappedRight out)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailJoined tail right)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reverseTail tail)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton head z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append leftCandidate reverseTail singleton)))
    (hto : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailOut mappedRight reverseTail)))
    (hfo : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append finalOut tailOut singleton))) :
    Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined)) := by
  have hjc := InternalApplicationValidityStackAppendListProof.consForward code head tail right tailJoined joined hc hj (andLeft hf)
  have hleft := OriginalReverseConsProof.actualCons body alpha Delta code head tail singleton reverseTail leftCandidate hc hs ht hl
  have he := valueUnique OriginalTypedArgumentObservations.reverse mappedLeft leftCandidate ![code] (andLeft (andRight hf)) hleft
  have hout := binaryInputs InternalApplicationValidityStackAppend.append out mappedRight mappedLeft mappedRight leftCandidate
    ⟨refl mappedRight⟩ he (andRight (andRight (andRight hf)))
  have htail := rowApply tail right tailJoined parameter reverseTail mappedRight tailOut hi
    (andIntro hj (andIntro ht (andIntro (andLeft (andRight (andRight hf))) hto)))
  have hfinal := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation body alpha Delta
    mappedRight reverseTail singleton tailOut leftCandidate finalOut hto hl hfo
  have heout := valueUnique InternalApplicationValidityStackAppend.append finalOut out ![mappedRight,leftCandidate] hfinal hout
  have hrev := OriginalReverseConsProof.actualCons body alpha Delta joined head tailJoined singleton tailOut finalOut hjc hs htail hfo
  exact outputTransport OriginalTypedArgumentObservations.reverse finalOut out ![joined] heout hrev

theorem consCore (code head tail right joined parameter mappedLeft mappedRight out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hi : Nonempty (Derivation body Delta (row tail)))
    (hf : Nonempty (Derivation body Delta (fields code right joined parameter mappedLeft mappedRight out))) :
    Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined)) := by
  let q0 : Program 4 := .composition InternalApplicationValidityStackAppend.append ![.projection 1,.projection 2]
  let q1 : Program 4 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => .projection 1)
  let q2 : Program 4 := consOf (.projection 0) (OriginalRawSyntaxTransport.constant 4 0)
  let q3 : Program 4 := .composition InternalApplicationValidityStackAppend.append ![q1,q2]
  let q4 : Program 4 := .composition InternalApplicationValidityStackAppend.append ![.projection 3,q1]
  let q5 : Program 4 := .composition InternalApplicationValidityStackAppend.append ![q4,q2]
  let qs : Fin 6 → Program 4 := ![q0,q1,q2,q3,q4,q5]
  let xs : Fin 4 → OTerm alpha := ![head,tail,right,mappedRight]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph1Rename]
  let xx : Fin 4 → OTerm beta := ![head.relabel j,tail.relabel j,right.relabel j,mappedRight.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i <;> rfl
  rw [hx] at hq
  have h0 : Nonempty (Derivation body Theta (programGraph q0 (ys 0) xx)) := hq 0
  have h1 : Nonempty (Derivation body Theta (programGraph q1 (ys 1) xx)) := hq 1
  have h2 : Nonempty (Derivation body Theta (programGraph q2 (ys 2) xx)) := hq 2
  have h3 : Nonempty (Derivation body Theta (programGraph q3 (ys 3) xx)) := hq 3
  have h4 : Nonempty (Derivation body Theta (programGraph q4 (ys 4) xx)) := hq 4
  have h5 : Nonempty (Derivation body Theta (programGraph q5 (ys 5) xx)) := hq 5
  have hv0 := binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) (.projection 2)
    (ys 0) (tail.relabel j) (right.relabel j) xx h0 (projectionValue 1 xx) (projectionValue 2 xx)
  have hv1 := unaryRecover OriginalTypedArgumentObservations.reverse (.projection 1)
    (ys 1) (tail.relabel j) xx h1 (projectionValue 1 xx)
  have hv2 := binaryRecover InternalListCodec.consCode (.projection 0) (OriginalRawSyntaxTransport.constant 4 0)
    (ys 2) (head.relabel j) z xx h2 (projectionValue 0 xx)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx)
  have hv3 := binaryRecover InternalApplicationValidityStackAppend.append q1 q2 (ys 3) (ys 1) (ys 2) xx h3 h1 h2
  have hv4 := binaryRecover InternalApplicationValidityStackAppend.append (.projection 3) q1
    (ys 4) (mappedRight.relabel j) (ys 1) xx h4 (projectionValue 3 xx) h1
  have hv5 := binaryRecover InternalApplicationValidityStackAppend.append q4 q2 (ys 5) (ys 4) (ys 2) xx h5 h4 h2
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  simp only [graph2Rename,rowRename,fieldsRename] at hc' hi' hf'
  exact consAtValues (code.relabel j) (head.relabel j) (tail.relabel j) (right.relabel j)
    (joined.relabel j) (parameter.relabel j) (mappedLeft.relabel j) (mappedRight.relabel j) (out.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hc' hi' hf' hv0 hv1 hv2 hv3 hv4 hv5
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseAppendCoreProof
