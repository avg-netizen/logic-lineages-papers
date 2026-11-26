module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConsAgreementProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppendListProof (consForward)
open NumberedWindowInternalLiteralCountConsAgreementProof (exact_LiteralConsCongruence)
open NumberedWindowInternalProjectedCountLeftTargets

private theorem tapeTwo {α : Type} (a b : OTerm α) :
    (![a,b] : Fin 2 → OTerm α) = Fin.cons a (Fin.cons b Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem exact_OpenProjectedCountLeft : ExactOpenProjectedCountLeft := by
  intro B α Γ head oldTail leftTail right old left joinedTail joined original side pre post invariant
  have pre' := pre
  have post' := post
  simp only [NumberedWindowInternalScratchAppendOpenTargets.appendGraph,tapeTwo] at pre' post'
  have joinCons := consForward left head leftTail right joinedTail joined side pre' post'
  exact exact_LiteralConsCongruence head oldTail joinedTail old joined original joinCons invariant

#print axioms exact_OpenProjectedCountLeft

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftProof
