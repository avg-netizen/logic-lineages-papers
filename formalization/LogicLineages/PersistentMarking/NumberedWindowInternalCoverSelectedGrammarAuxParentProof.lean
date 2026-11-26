module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxPredecessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundProof (exact_OpenSelectedGrammarCrossBound)
open NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
open NumberedWindowInternalCoverSelectedGrammarAuxPredecessorProof (exact_OpenSelectedGrammarAuxAtPredecessor)

private theorem atChild {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (before after key : OTerm α)
    (inc : Derivation body Γ (axisInclusion before after))
    (hit : Nonempty (Derivation body Γ (memberGraph before key))) :
    Nonempty (Derivation body Γ (memberGraph after key)) := by
  have chosen := Derivation.universalElimination (emb key) inc
  have law : Derivation body Γ ((memberGraph before key).imp (memberGraph after key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using chosen
  obtain ⟨hit⟩ := hit
  exact ⟨Derivation.implicationElimination law hit⟩

theorem exact_OpenSelectedGrammarAuxParent : ExactOpenSelectedGrammarAuxParent := by
  intro body α Γ d H K M df mf da ma fState fTerms fArgs aState aTerms aArgs
    prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg
    fReport aReport fHit aHit dfBound mfBound daBound maBound pReport nReport hd hc
  obtain ⟨left⟩ := exact_OpenSelectedGrammarCrossBound body α Γ df d H K mf M
    fState fTerms fArgs prev prevTerms prevArgs dfBound mfBound fReport pReport
  obtain ⟨right⟩ := exact_OpenSelectedGrammarCrossBound body α Γ da d H K ma M
    aState aTerms aArgs prev prevTerms prevArgs daBound maBound aReport pReport
  have fPrev := atChild fTerms prevTerms fn (Derivation.conjunctionLeft left) fHit
  have aPrev := atChild aTerms prevTerms arg (Derivation.conjunctionLeft right) aHit
  exact exact_OpenSelectedGrammarAuxAtPredecessor body α Γ d H K M
    prev prevTerms prevArgs next nextTerms nextArgs dom cod fn arg pReport nReport hd hc fPrev aPrev

#print axioms exact_OpenSelectedGrammarAuxParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentProof
