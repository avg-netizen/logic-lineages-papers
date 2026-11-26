module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (pairRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedArgumentObservations (reverseRun)
open OriginalTypedArgumentObservationsReverseInternalStepProof
open OriginalTypedArgumentObservationsReverseInternalBoundProof
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zero (acc : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 accumulated acc z acc)) := by
 apply programCases InternalPairing.pairing ![z,acc] _
 intro beta rho Theta state hrho hp
 rw [binaryVectorRename] at hp
 simp only [graph2Rename,zRelabel]
 simp only [zRelabel] at hp
 exact value z (acc.relabel rho) state state (acc.relabel rho) hp
   (stopped (suc z) state (acc.relabel rho) hp) (pairRight state z (acc.relabel rho) hp)

theorem consValues (raw head tail acc nextAcc result state next terminal : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result tail nextAcc)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc tail) next))) :
 Nonempty (Derivation body Delta (graph2 accumulated result raw acc)) := by
 have hterminal := terminalPair tail nextAcc next terminal result hn hr hv
 have hstep := stepCons state raw acc head tail nextAcc next hp hc ha hn
 have hrun := consFinish raw head tail state next terminal result hc hstep hr hterminal
 exact value raw acc state terminal result hp hrun (pairRight terminal z result hterminal)

theorem consAt2 (raw head tail acc nextAcc result state next : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result tail nextAcc)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc)))
 : Nonempty (Derivation body Delta (graph2 accumulated result raw acc)) := by
  apply programCases reverseRun ![suc tail,next] _
  intro beta rho Theta terminal hrho hr
  rw [binaryVectorRename] at hr
  simp only [graph2Rename]
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename] at ha'
  have hv' := renameInto hv rho Theta hrho
  simp only [graph2Rename] at hv'
  have hp' := renameInto hp rho Theta hrho
  simp only [graph2Rename] at hp'
  have hn' := renameInto hn rho Theta hrho
  simp only [graph2Rename] at hn'
  simp only [sucRelabel] at hr
  exact consValues (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (acc.relabel rho) (nextAcc.relabel rho) (result.relabel rho) (state.relabel rho) (next.relabel rho) terminal hc' ha' hv' hp' hn' hr

theorem consAt1 (raw head tail acc nextAcc result state : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result tail nextAcc)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 : Nonempty (Derivation body Delta (graph2 accumulated result raw acc)) := by
  apply programCases InternalPairing.pairing ![tail,nextAcc] _
  intro beta rho Theta next hrho hn
  rw [binaryVectorRename] at hn
  simp only [graph2Rename]
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename] at ha'
  have hv' := renameInto hv rho Theta hrho
  simp only [graph2Rename] at hv'
  have hp' := renameInto hp rho Theta hrho
  simp only [graph2Rename] at hp'
  exact consAt2 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (acc.relabel rho) (nextAcc.relabel rho) (result.relabel rho) (state.relabel rho) next hc' ha' hv' hp' hn

theorem consValue (raw head tail acc nextAcc result : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result tail nextAcc)))
 : Nonempty (Derivation body Delta (graph2 accumulated result raw acc)) := by
  apply programCases InternalPairing.pairing ![raw,acc] _
  intro beta rho Theta state hrho hp
  rw [binaryVectorRename] at hp
  simp only [graph2Rename]
  have hc' := renameInto hc rho Theta hrho
  simp only [graph2Rename] at hc'
  have ha' := renameInto ha rho Theta hrho
  simp only [graph2Rename] at ha'
  have hv' := renameInto hv rho Theta hrho
  simp only [graph2Rename] at hv'
  exact consAt1 (raw.relabel rho) (head.relabel rho) (tail.relabel rho) (acc.relabel rho) (nextAcc.relabel rho) (result.relabel rho) state hc' ha' hv' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorConsProof
