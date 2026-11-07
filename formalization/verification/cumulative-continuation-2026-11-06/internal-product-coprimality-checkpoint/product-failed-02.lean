module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof
open InternalBetaDivisionSyntaxProof
open InternalOriginalOrderProof InternalPositiveUnfoldingSupportProof
open InternalOrientedBezoutSyntaxProof InternalOrientedBezoutProof InternalDivisibilityProof
open InternalBezoutExistenceTargets InternalProductCoprimalityArithmeticProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem positiveProductCoprimality (m a b : OTerm α)
    (ha : Nonempty (Derivation body Gamma (coprime (suc m) (suc a))))
    (hb : Nonempty (Derivation body Gamma (coprime (suc m) (suc b)))) :
    Nonempty (Derivation body Gamma (coprime (suc m) (mul (suc a) (suc b)))) := by
  obtain ⟨ca⟩ := actualOrientedBezoutFromCoprimality body α m a
  obtain ⟨cb⟩ := actualOrientedBezoutFromCoprimality body α m b
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  have hoa := Derivation.implicationElimination (weakenClosed ca Gamma) ha
  have hob := Derivation.implicationElimination (weakenClosed cb Gamma) hb
  apply orientedCases Gamma m a _ ⟨hoa⟩
  intro β j Delta u v hj hu
  simp only [coprimeRename,sucRelabel,mulRelabel]
  have hb' := renameInto ⟨hob⟩ j Delta hj
  rw [orientedRename] at hb'
  apply orientedCases Delta (m.relabel j) (b.relabel j) _ hb'
  intro γ k Theta w z' hk hw
  simp only [coprimeRename,sucRelabel,mulRelabel]
  have hu' := renameInto hu k Theta hk
  unfold InternalBezoutCRT.certificate at hu' hw
  simp only [onEquality,eqnRelabel,sucRelabel,mulRelabel] at hu' hw
  obtain ⟨hu'⟩ := hu'
  obtain ⟨hw⟩ := hw
  exact certificateCoprimality _ _ _ _ ⟨certificateProduct _ _ _ _ _ _ _ hu' hw⟩
theorem actualPositiveProductCoprimality :
    InternalProductCoprimalityTargets.ActualPositiveProductCoprimality := by
  intro body α m a b
  have h := Derivation.hypothesis (body := body)
    (List.mem_cons_self (a := coprime (suc m) (suc a) ⊓ coprime (suc m) (suc b)) (l := []))
  obtain ⟨h⟩ := positiveProductCoprimality m a b
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalProductCoprimalityProof
