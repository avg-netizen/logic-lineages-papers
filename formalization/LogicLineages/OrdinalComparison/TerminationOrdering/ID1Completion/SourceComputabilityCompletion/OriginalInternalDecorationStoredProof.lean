module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationStoredProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem forgetOfPairs (child role typed typ rawJob : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawJob child)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons child Fin.elim0
 have hinner := unaryValue InternalUnpair.right (.projection 0) typed child xs (pairRight child role typed hp) (projectionValue 0 xs)
 exact unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob typed xs
  (pairRight typed typ rawJob ht) hinner
theorem coordinates (index role typ raw rawCell child childRole childType typed stored annotation : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType))) :
 Nonempty (Derivation body Delta
  (eqn rawCell stored ⊓ graph4 OriginalHereditaryAnnotatedExpansion.annotation annotation index role typ raw)) := by
 have hf := OriginalHereditaryInternalExpansionDecorationProof.decorateForget index role typ raw rawCell child hd
 have hs := forgetOfPairs child childRole typed childType stored hp ht
 obtain ⟨he⟩ := valueUnique OriginalHereditaryAnnotatedExpansion.forget rawCell stored (Fin.cons child Fin.elim0) hf hs
 have hr := outputTransport InternalUnpair.right stored rawCell (Fin.cons typed Fin.elim0) ⟨symm he⟩
  (pairRight typed childType stored ht)
 have ht' := reconstructPair typed childType rawCell (pairLeft typed childType stored ht) hr
 obtain ⟨h⟩ := OriginalInternalDecorationCoordinatesProof.actualCoordinates body alpha Delta
  index role typ raw rawCell child childRole childType typed annotation hd hp ht' ha
 exact ⟨Derivation.conjunctionIntroduction he h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationStoredProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationStoredProof
