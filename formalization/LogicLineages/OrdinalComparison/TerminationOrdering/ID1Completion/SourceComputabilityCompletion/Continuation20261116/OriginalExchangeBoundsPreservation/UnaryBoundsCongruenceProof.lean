module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsCongruenceProof
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
open Continuation20261115
open OriginalCodeBoundsConstructors.UnaryValueProof (constructor)

theorem sameChildValue (ordinary : Bool) (n : Nat) (left right lm rm lc rc value lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) right rm rc)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hlch : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value lc)))
    (hrch : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value rc)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases UnaryBoundsQueriesProof.queries ![value] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![value] i).relabel j) = ![value.relabel j] := by
    funext i; fin_cases i; rfl
  rw [hx] at hq
  rw [eqnRelabel]
  obtain ⟨hp,hn⟩ := UnaryBoundsQueriesProof.recover (value.relabel j) ys hq
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hlgj := renameInto hlg j Theta hj
  have hrgj := renameInto hrg j Theta hj
  have hlchj := renameInto hlch j Theta hj
  have hrchj := renameInto hrch j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  rw [graph2Rename] at hlcj hrcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hlgj hrgj hlchj hrchj hlvj hrvj
  have hl := OriginalCodeBoundsConstructors.UnaryValueProof.value ordinary n (left.relabel j) (lm.relabel j) (lc.relabel j)
    (value.relabel j) (ys 0) (ys 1) (ys 2) hlcj hlgj hlchj hp hn
  have hr := OriginalCodeBoundsConstructors.UnaryValueProof.value ordinary n (right.relabel j) (rm.relabel j) (rc.relabel j)
    (value.relabel j) (ys 0) (ys 1) (ys 2) hrcj hrgj hrchj hp hn
  obtain ⟨hel⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (lv.relabel j) (ys 2) ![left.relabel j] hlvj hl
  obtain ⟨her⟩ := valueUnique (OriginalCodeBoundsRecursion.bounds n) (rv.relabel j) (ys 2) ![right.relabel j] hrvj hr
  exact ⟨trans hel (symm her)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsCongruenceProof
