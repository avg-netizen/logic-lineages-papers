module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoverageProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm refl)
open InternalSourceInversionSupportProof (onEquality)
open InternalGraphCompositionEqualityProof (graphInputTransport)
open InternalAdditionLawsProof (add)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem subtractionAtSum (child gap stage : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn (add child gap) stage))) :
 Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract gap child stage)) := by
 apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula InternalEqualityTest.subtract)
   gap (Fin.cons child (Fin.cons (add child gap) Fin.elim0))
   (Fin.cons child (Fin.cons stage Fin.elim0)) _ (InternalEqualityTestSubtractionProof.diagonal child gap)
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i
 · rw [onEquality]; exact ⟨refl child⟩
 · rw [onEquality]; exact he

theorem coverageAt (stage tab child rank index gap : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hr : Nonempty (Derivation body Delta (graph1 decoder rank child)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract index child stage)))
 (he : Nonempty (Derivation body Delta (eqn (add child gap) stage))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rank index tab)) := by
 obtain ⟨he⟩ := he
 have ht' := headTransport table tab stage (add child gap) Fin.elim0 ⟨symm he⟩ ht
 have hl := RankMemoTableProof.tableLookup rank child gap tab hr ht'
 have hi := valueUnique InternalEqualityTest.subtract gap index (Fin.cons child (Fin.cons stage Fin.elim0))
   (subtractionAtSum child gap stage ⟨he⟩) hs
 exact headTransport InternalRawListRecursion.lookup rank gap index (Fin.cons tab Fin.elim0) hi hl

theorem actualLookupCoverage : RankMemoTargets.ActualLookupCoverage := by
 intro body alpha Delta stage tab child rank index ht hb hr hs
 apply InternalUnpairReverseSyntaxProof.weakOrderCases Delta child stage _ hb
 intro beta j Theta gap hj he
 rw [graph2Rename]
 have ht' := renameInto ht j Theta hj
 have hr' := renameInto hr j Theta hj
 have hs' := renameInto hs j Theta hj
 rw [graph1Rename] at ht' hr'
 rw [graph2Rename] at hs'
 exact coverageAt (stage.relabel j) (tab.relabel j) (child.relabel j) (rank.relabel j)
   (index.relabel j) gap ht' hr' hs' he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoverageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoverageProof
