module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsReverseInternalStepProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atGap (raw tail gap state next out result : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn (add tail (suc gap)) raw)))
 (hs : Nonempty (Derivation body Delta (graph1 reverseStep next state)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun out (suc tail) next)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z result))) :
 Nonempty (Derivation body Delta (graph2 reverseRun out (suc raw) state)) := by
 have hf := afterFirst (suc tail) state next out hs hr
 have hh := padding (suc (suc tail)) gap state out result hf hp
 obtain ⟨he⟩ := he
 have heq : Derivation body Delta (eqn (add (suc (suc tail)) gap) (suc raw)) :=
   trans (leftSuccessor (suc tail) gap)
     (trans (congSuc (leftSuccessor tail gap))
       (trans (congSuc (symm (addSucc tail gap))) (congSuc he)))
 exact headTransport reverseRun out (add (suc (suc tail)) gap) (suc raw) ![state] ⟨heq⟩ hh

/-- Numeric cons descent pays the actual fixed input+1 fuel. The child run
and terminal pair are graph premises, not a native termination assertion. -/
theorem consFinish (raw head tail state next out result : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hs : Nonempty (Derivation body Delta (graph1 reverseStep next state)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun out (suc tail) next)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z result))) :
 Nonempty (Derivation body Delta (graph2 reverseRun out (suc raw) state)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 apply orderCases Delta tail raw _ hb
 intro beta rho Theta gap hrho he
 simp only [graph2Rename,sucRelabel]
 have hs' := renameInto hs rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hp' := renameInto hp rho Theta hrho
 simp only [graph1Rename] at hs'
 simp only [graph2Rename,sucRelabel] at hr'
 simp only [graph2Rename,zRelabel] at hp'
 exact atGap (raw.relabel rho) (tail.relabel rho) gap (state.relabel rho) (next.relabel rho)
   (out.relabel rho) (result.relabel rho) he hs' hr' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalBoundProof
