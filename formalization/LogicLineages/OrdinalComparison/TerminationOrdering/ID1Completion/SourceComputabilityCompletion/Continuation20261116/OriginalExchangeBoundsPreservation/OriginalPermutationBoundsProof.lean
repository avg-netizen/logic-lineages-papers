module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryFoldPairQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalEntryPermutationFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalPermutationBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (trans symm)
open Continuation20261114 Continuation20261115

theorem atEntries (n : Nat) (left right leftEntries rightEntries lv rv : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) left right)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hle : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc leftEntries) left z)))
    (hre : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc rightEntries) right z)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (EntryFoldPairQueriesProof.queries n) ![leftEntries,rightEntries] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![leftEntries,rightEntries] i).relabel j) = ![leftEntries.relabel j,rightEntries.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  obtain ⟨hlf,hrf⟩ := EntryFoldPairQueriesProof.recover n (leftEntries.relabel j) (rightEntries.relabel j) ys hq
  have haj := renameInto ha j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hlej := renameInto hle j Theta hj
  have hrej := renameInto hre j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at haj hlej hrej
  simp only [graph1Rename,sucRelabel,zRelabel] at hlgj hrgj hlvj hrvj
  have hlb := EntryBoundsProof.actualBounds n (left.relabel j) z (leftEntries.relabel j) (ys 0) hlgj hlej hlf
  have hrb := EntryBoundsProof.actualBounds n (right.relabel j) z (rightEntries.relabel j) (ys 1) hrgj hrej hrf
  obtain ⟨hel⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (lv.relabel j) (ys 0) ![left.relabel j] hlvj hlb
  obtain ⟨her⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (rv.relabel j) (ys 1) ![right.relabel j] hrvj hrb
  obtain ⟨hem⟩ := OriginalEntryPermutationFoldProof.actualFold (Fold.entryWeight n) (left.relabel j) (right.relabel j)
    (leftEntries.relabel j) (rightEntries.relabel j) (ys 0) (ys 1) haj hlej hrej hlf hrf
  exact ⟨trans hel (trans hem (symm her))⟩

theorem preserved (n : Nat) (left right lv rv : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) left right)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalArgumentPermutationClosure.OptionProof.bothCases left right _ ha
  intro beta j Theta leftEntries rightEntries hj hle hre _hperm
  rw [eqnRelabel]
  have haj := renameInto ha j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at haj
  simp only [graph1Rename,sucRelabel,zRelabel] at hlgj hrgj hlvj hrvj
  exact atEntries n (left.relabel j) (right.relabel j) leftEntries rightEntries (lv.relabel j) (rv.relabel j)
    haj hlgj hrgj hle hre hlvj hrvj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalPermutationBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OriginalPermutationBoundsProof
