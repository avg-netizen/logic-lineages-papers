module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceConsumerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof
open InternalOrientedBezoutSyntaxProof InternalOrientedBezoutArithmeticProof
open InternalLinearCombinationSyntaxProof InternalBezoutExistenceConsumerProof
open InternalBezoutExistenceTargets
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem signedToOriented (a b : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (cf (suc a) (suc b) (suc z)))) :
    Nonempty (Derivation body Gamma (of a b)) := by
  apply combinationCases Gamma (suc a) (suc b) (suc z) _ h
  intro β j Delta x y z' w _ he
  rw [orientedRename]
  simp only [equationEmbedding,sucRelabel,zRelabel] at he
  obtain ⟨he⟩ := he
  apply orientedIntroduction _ _ (InternalOrientedBezout.leftCoefficient (b.relabel j) x z' w)
    (InternalOrientedBezout.rightCoefficient (a.relabel j) x y w)
  unfold InternalBezoutCRT.certificate
  rw [onEquality]
  exact ⟨conversion (a.relabel j) (b.relabel j) x y z' w he⟩

theorem actualOrientedBezoutFromCoprimality :
    InternalOrientedBezoutTargets.ActualOrientedBezoutFromCoprimality := by
  intro body α a b
  obtain ⟨hs⟩ := actualSignedBezoutFromCoprimality body α a (suc b)
  let p := coprime (suc a) (suc b)
  have hp : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  have hc := Derivation.implicationElimination (weakenClosed hs [p]) hp
  obtain ⟨ho⟩ := signedToOriented a b ⟨hc⟩
  exact ⟨Derivation.implicationIntroduction ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutProof
