module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoverageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalTagArithmeticSyntaxProof (sucRelabel)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem weightAtIndex (stage tab typed typ child rank index : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hb : Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound child stage)))
 (hr : Nonempty (Derivation body Delta (graph1 decoder rank child)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract index child stage))) :
 Nonempty (Derivation body Delta (programGraph lookupWeight rank
   (Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0))))) := by
 let xs := Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0))
 have hc := unaryValue InternalUnpair.right (.projection 0) child typed xs (pairRight typed typ child hp)
   (projectionValue 0 xs)
 have hi := binaryValue InternalEqualityTest.subtract (rightOf (.projection 0)) (.projection 1)
   index child stage xs hs hc (projectionValue 1 xs)
 exact binaryValue InternalRawListRecursion.lookup
   (.composition InternalEqualityTest.subtract ![rightOf (.projection 0),.projection 1]) (.projection 2)
   rank index tab xs (RankMemoCoverageProof.actualLookupCoverage body alpha Delta stage tab child rank index ht hb hr hs)
   hi (projectionValue 2 xs)

theorem actualWeight (stage tab typed typ child rank : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hb : Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound child stage)))
 (hr : Nonempty (Derivation body Delta (graph1 decoder rank child)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child))) :
 Nonempty (Derivation body Delta (programGraph lookupWeight rank
   (Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0))))) := by
 apply programCases InternalEqualityTest.subtract (Fin.cons child (Fin.cons stage Fin.elim0)) _
 intro beta j Theta index hj hs
 simp only [programRename,consTermRename,emptyRename]
 simp only [consTermRename,emptyRename] at hs
 have ht' := renameInto ht j Theta hj
 have hr' := renameInto hr j Theta hj
 have hp' := renameInto hp j Theta hj
 have hb' := renameInto hb j Theta hj
 rw [graph1Rename] at ht' hr'
 rw [graph2Rename] at hp'
 simp only [InternalPairingSumBounds.weakBound,InternalLessThan.strictLess,orderRename,sucRelabel] at hb'
 exact weightAtIndex (stage.relabel j) (tab.relabel j) (typed.relabel j) (typ.relabel j)
   (child.relabel j) (rank.relabel j) index ht' hb' hr' hp' hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoWeightProof
