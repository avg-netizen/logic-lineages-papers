module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def visitPayloadQ : Program 4 := pairOf (.projection 0) (.projection 1)
def visitFrameQ : Program 4 := visitOf (.projection 0) (.projection 1)
def visitWorkQ : Program 4 := consOf visitFrameQ (.projection 2)
def visitPackedQ : Program 4 := pairOf visitWorkQ (.projection 3)
def visitQueries : Fin 4 → Program 4 := ![visitPayloadQ,visitFrameQ,visitWorkQ,visitPackedQ]

def OpenedVisit (state value parameter suffix stack codedWork : OTerm alpha) : Formula alpha :=
  graph1 status (suc z) state ⊓ (graph1 OriginalLambdaTraversal.work codedWork state ⊓
    ((eqn codedWork z).not ⊓ (graph1 frameTag z state ⊓
      (graph1 currentRaw value state ⊓ (graph1 currentParameter parameter state ⊓
        (graph1 rest suffix state ⊓ graph1 OriginalLambdaTraversal.results stack state))))))

theorem negationRename {beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

@[simp] theorem openedVisitRename {beta : Type}
    (state value parameter suffix stack codedWork : OTerm alpha) (j : alpha → beta) :
    (OpenedVisit state value parameter suffix stack codedWork).relabel j =
      OpenedVisit (state.relabel j) (value.relabel j) (parameter.relabel j)
        (suffix.relabel j) (stack.relabel j) (codedWork.relabel j) := by
  simp only [OpenedVisit,conjunctionRename,graph1Rename,negationRename,
    InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel,zRelabel]

theorem visitAtQueries (state value parameter suffix stack : OTerm alpha)
    (ys : Fin 4 → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (hq : ∀ i, Nonempty (Derivation positive Delta (programGraph (visitQueries i) (ys i)
      (Fin.cons value (Fin.cons parameter (Fin.cons suffix (Fin.cons stack Fin.elim0))))))) :
    Nonempty (Derivation positive Delta (OpenedVisit state value parameter suffix stack (ys 2))) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons value (Fin.cons parameter (Fin.cons suffix (Fin.cons stack Fin.elim0)))
  let ss : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hp := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) value parameter xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 4) visitPayloadQ
    (ys 1) z (ys 0) xs (hq 1) (InternalLessThanSupportProof.zeroConstantValue xs) (hq 0)
  have hw := binaryRecover InternalListCodec.consCode visitFrameQ (.projection 2)
    (ys 2) (ys 1) suffix xs (hq 2) (hq 1) (projectionValue 2 xs)
  have ht := binaryRecover InternalPairing.pairing visitWorkQ (.projection 3)
    (ys 3) (ys 2) stack xs (hq 3) (hq 2) (projectionValue 3 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 4) visitPackedQ
    state (suc z) (ys 3) xs hs (InternalLessThanSupportProof.oneConstantValue xs) (hq 3)
  have hstatus : Nonempty (Derivation positive Delta (graph1 status (suc z) state)) :=
    pairLeft state (suc z) (ys 3) ho
  have hpacked := pairRight state (suc z) (ys 3) ho
  have hwork : Nonempty (Derivation positive Delta (graph1 OriginalLambdaTraversal.work (ys 2) state)) :=
    unaryValue InternalUnpair.left InternalUnpair.right (ys 2) (ys 3) ss
      (pairLeft (ys 3) (ys 2) stack ht) hpacked
  have hresults : Nonempty (Derivation positive Delta (graph1 OriginalLambdaTraversal.results stack state)) :=
    unaryValue InternalUnpair.right InternalUnpair.right stack (ys 3) ss
      (pairRight (ys 3) (ys 2) stack ht) hpacked
  have hc := InternalListCodecSupportProof.consDestruction (ys 2) (ys 1) suffix hw
  have hframe : Nonempty (Derivation positive Delta (graph1 currentFrame (ys 1) state)) :=
    unaryValue InternalListCodec.headCode OriginalLambdaTraversal.work (ys 1) (ys 2) ss (andLeft hc) hwork
  have hrest : Nonempty (Derivation positive Delta (graph1 rest suffix state)) :=
    unaryValue InternalListCodec.tailCode OriginalLambdaTraversal.work suffix (ys 2) ss (andLeft (andRight hc)) hwork
  have htag : Nonempty (Derivation positive Delta (graph1 frameTag z state)) :=
    unaryValue InternalUnpair.left currentFrame z (ys 1) ss (pairLeft (ys 1) z (ys 0) hf) hframe
  have hpayload : Nonempty (Derivation positive Delta (graph1 framePayload (ys 0) state)) :=
    unaryValue InternalUnpair.right currentFrame (ys 0) (ys 1) ss (pairRight (ys 1) z (ys 0) hf) hframe
  have hraw : Nonempty (Derivation positive Delta (graph1 currentRaw value state)) :=
    unaryValue InternalUnpair.left framePayload value (ys 0) ss (pairLeft (ys 0) value parameter hp) hpayload
  have hparameter : Nonempty (Derivation positive Delta (graph1 currentParameter parameter state)) :=
    unaryValue InternalUnpair.right framePayload parameter (ys 0) ss (pairRight (ys 0) value parameter hp) hpayload
  exact andIntro hstatus (andIntro hwork (andIntro (andRight (andRight hc))
    (andIntro htag (andIntro hraw (andIntro hparameter (andIntro hrest hresults))))))

theorem visitCases (state value parameter suffix stack : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (codedWork : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (OpenedVisit (state.relabel j) (value.relabel j)
        (parameter.relabel j) (suffix.relabel j) (stack.relabel j) codedWork)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) : Nonempty (Derivation positive Delta psi) := by
  apply queryCases visitQueries (Fin.cons value (Fin.cons parameter (Fin.cons suffix (Fin.cons stack Fin.elim0)))) _
  intro beta j ys Theta hj hq
  have hs' := renameInto hs j Theta hj
  rw [graph4Rename] at hs'
  simp only [consTermRename,emptyRename] at hq
  exact k beta j Theta (ys 2) hj
    (visitAtQueries (state.relabel j) (value.relabel j) (parameter.relabel j)
      (suffix.relabel j) (stack.relabel j) ys hs' hq)

def stateInputs : Fin 4 → Program 1 := ![currentRaw,currentParameter,rest,OriginalLambdaTraversal.results]

theorem openedInputs (state value parameter suffix stack codedWork : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state value parameter suffix stack codedWork))) :
    ∀ i, Nonempty (Derivation positive Delta (programGraph (stateInputs i)
      (![value,parameter,suffix,stack] i) (Fin.cons state Fin.elim0))) := by
  have hr := andRight (andRight (andRight (andRight h)))
  exact fun i => Fin.cases (andLeft hr) (Fin.cases (andLeft (andRight hr))
    (Fin.cases (andLeft (andRight (andRight hr)))
      (Fin.cases (andRight (andRight (andRight hr))) (fun j => Fin.elim0 j)))) i

theorem applicationExpandedSubstitution :
    Substitutes stateInputs applicationExpandedState applicationExpanded := by
  apply liveSubstitution _ (.projection 3)
  apply consSubstitution _ (consSubstitution _ (consSubstitution _ (.projection 2)))
  · exact visitSubstitution (unarySubstitution rawFunction (.projection 0)) (.projection 1)
  · exact visitSubstitution (unarySubstitution rawArgument (.projection 0)) (.projection 1)
  · exact applicationReturnSubstitution (unarySubstitution rawDomain (.projection 0))
      (unarySubstitution rawType (.projection 0))

theorem lambdaExpandedSubstitution :
    Substitutes stateInputs lambdaExpandedState lambdaExpanded := by
  apply liveSubstitution _ (.projection 3)
  apply consSubstitution _ (consSubstitution _ (.projection 2))
  · exact visitSubstitution (unarySubstitution rawBody (.projection 0))
      (binarySubstitution childParameter (.projection 0) (.projection 1))
  · exact lambdaReturnSubstitution (unarySubstitution rawDomain (.projection 0))
      (unarySubstitution rawCodomain (.projection 0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitSyntaxProof
