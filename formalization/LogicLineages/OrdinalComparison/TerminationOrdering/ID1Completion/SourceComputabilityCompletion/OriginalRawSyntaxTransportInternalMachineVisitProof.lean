module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def visitInnerQ : Program 5 := pairOf (.projection 1) (.projection 2)
def visitPayloadQ : Program 5 := pairOf (.projection 0) visitInnerQ
def visitFrameQ : Program 5 := visitOf (.projection 0) (.projection 1) (.projection 2)
def visitWorkQ : Program 5 := consOf visitFrameQ (.projection 3)
def visitPackedQ : Program 5 := pairOf visitWorkQ (.projection 4)
def visitQueries : Fin 5 → Program 5 := ![visitInnerQ,visitPayloadQ,visitFrameQ,visitWorkQ,visitPackedQ]

def OpenedVisit (state d k value suffix stack codedWork : OTerm alpha) : Formula alpha :=
  graph1 status (suc z) state ⊓ (graph1 OriginalRawSyntaxTransport.work codedWork state ⊓
    ((eqn codedWork z).not ⊓ (graph1 frameTag z state ⊓
      (graph1 currentType d state ⊓ (graph1 currentCutoff k state ⊓
        (graph1 currentRaw value state ⊓
          (graph1 rest suffix state ⊓ graph1 OriginalRawSyntaxTransport.results stack state)))))))

theorem negationRename {beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

@[simp] theorem openedVisitRename {beta : Type}
    (state d k value suffix stack codedWork : OTerm alpha) (j : alpha → beta) :
    (OpenedVisit state d k value suffix stack codedWork).relabel j =
      OpenedVisit (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
        (suffix.relabel j) (stack.relabel j) (codedWork.relabel j) := by
  simp only [OpenedVisit,conjunctionRename,graph1Rename,negationRename,
    InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel,zRelabel]

theorem visitAtQueries (state d k value suffix stack : OTerm alpha)
    (ys : Fin 5 → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (hq : ∀ i, Nonempty (Derivation positive Delta (programGraph (visitQueries i) (ys i)
      ![d,k,value,suffix,stack]))) :
    Nonempty (Derivation positive Delta (OpenedVisit state d k value suffix stack (ys 3))) := by
  let xs : Fin 5 → OTerm alpha := ![d,k,value,suffix,stack]
  let ss : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hp0 := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 0) k value xs (hq 0) (projectionValue 1 xs) (projectionValue 2 xs)
  have hp := binaryRecover InternalPairing.pairing (.projection 0) visitInnerQ
    (ys 1) d (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hf := binaryRecover InternalPairing.pairing (constant 5 0) visitPayloadQ
    (ys 2) z (ys 1) xs (hq 2) (InternalLessThanSupportProof.zeroConstantValue xs) (hq 1)
  have hw := binaryRecover InternalListCodec.consCode visitFrameQ (.projection 3)
    (ys 3) (ys 2) suffix xs (hq 3) (hq 2) (projectionValue 3 xs)
  have ht := binaryRecover InternalPairing.pairing visitWorkQ (.projection 4)
    (ys 4) (ys 3) stack xs (hq 4) (hq 3) (projectionValue 4 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) visitPackedQ
    state (suc z) (ys 4) xs hs (InternalLessThanSupportProof.oneConstantValue xs) (hq 4)
  have hstatus : Nonempty (Derivation positive Delta (graph1 status (suc z) state)) :=
    pairLeft state (suc z) (ys 4) ho
  have hpacked := pairRight state (suc z) (ys 4) ho
  have hwork : Nonempty (Derivation positive Delta (graph1 OriginalRawSyntaxTransport.work (ys 3) state)) :=
    unaryValue InternalUnpair.left InternalUnpair.right (ys 3) (ys 4) ss
      (pairLeft (ys 4) (ys 3) stack ht) hpacked
  have hresults : Nonempty (Derivation positive Delta (graph1 OriginalRawSyntaxTransport.results stack state)) :=
    unaryValue InternalUnpair.right InternalUnpair.right stack (ys 4) ss
      (pairRight (ys 4) (ys 3) stack ht) hpacked
  have hc := InternalListCodecSupportProof.consDestruction (ys 3) (ys 2) suffix hw
  have hframe : Nonempty (Derivation positive Delta (graph1 frame (ys 2) state)) :=
    unaryValue InternalListCodec.headCode OriginalRawSyntaxTransport.work (ys 2) (ys 3) ss (andLeft hc) hwork
  have hrest : Nonempty (Derivation positive Delta (graph1 rest suffix state)) :=
    unaryValue InternalListCodec.tailCode OriginalRawSyntaxTransport.work suffix (ys 3) ss (andLeft (andRight hc)) hwork
  have htag : Nonempty (Derivation positive Delta (graph1 frameTag z state)) :=
    unaryValue InternalUnpair.left frame z (ys 2) ss (pairLeft (ys 2) z (ys 1) hf) hframe
  have hpayload : Nonempty (Derivation positive Delta (graph1 framePayload (ys 1) state)) :=
    unaryValue InternalUnpair.right frame (ys 1) (ys 2) ss (pairRight (ys 2) z (ys 1) hf) hframe
  have htype : Nonempty (Derivation positive Delta (graph1 currentType d state)) :=
    unaryValue InternalUnpair.left framePayload d (ys 1) ss (pairLeft (ys 1) d (ys 0) hp) hpayload
  have hinner : Nonempty (Derivation positive Delta (graph1 (rightOf framePayload) (ys 0) state)) :=
    unaryValue InternalUnpair.right framePayload (ys 0) (ys 1) ss (pairRight (ys 1) d (ys 0) hp) hpayload
  have hcutoff : Nonempty (Derivation positive Delta (graph1 currentCutoff k state)) :=
    unaryValue InternalUnpair.left (rightOf framePayload) k (ys 0) ss (pairLeft (ys 0) k value hp0) hinner
  have hraw : Nonempty (Derivation positive Delta (graph1 currentRaw value state)) :=
    unaryValue InternalUnpair.right (rightOf framePayload) value (ys 0) ss (pairRight (ys 0) k value hp0) hinner
  exact andIntro hstatus (andIntro hwork (andIntro (andRight (andRight hc))
    (andIntro htag (andIntro htype (andIntro hcutoff (andIntro hraw (andIntro hrest hresults)))))))

theorem visitCases (state d k value suffix stack : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k value suffix stack)))
    (cont : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (codedWork : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta (OpenedVisit (state.relabel j) (d.relabel j)
        (k.relabel j) (value.relabel j) (suffix.relabel j) (stack.relabel j) codedWork)) →
      Nonempty (Derivation positive Theta (psi.relabel j))) : Nonempty (Derivation positive Delta psi) := by
  apply queryCases visitQueries
    (Fin.cons d (Fin.cons k (Fin.cons value (Fin.cons suffix (Fin.cons stack Fin.elim0))))) _
  intro beta j ys Theta hj hq
  have hs' := renameInto hs j Theta hj
  rw [graph5Rename] at hs'
  simp only [consTermRename,emptyRename] at hq
  exact cont beta j Theta (ys 3) hj
    (visitAtQueries (state.relabel j) (d.relabel j) (k.relabel j) (value.relabel j)
      (suffix.relabel j) (stack.relabel j) ys hs' hq)

def stateInputs : Fin 5 → Program 1 := ![currentType,currentCutoff,currentRaw,rest,OriginalRawSyntaxTransport.results]

theorem openedInputs (state d k value suffix stack codedWork : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state d k value suffix stack codedWork))) :
    ∀ i, Nonempty (Derivation positive Delta (programGraph (stateInputs i)
      (![d,k,value,suffix,stack] i) (Fin.cons state Fin.elim0))) := by
  have hr := andRight (andRight (andRight (andRight h)))
  exact fun i => Fin.cases (andLeft hr) (Fin.cases (andLeft (andRight hr))
    (Fin.cases (andLeft (andRight (andRight hr)))
      (Fin.cases (andLeft (andRight (andRight (andRight hr))))
        (Fin.cases (andRight (andRight (andRight (andRight hr)))) (fun j => Fin.elim0 j))))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineVisitProof
