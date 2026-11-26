module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsBoundsProof
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
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof (exact_OpenSelectedNonemptyArgsFromPredecessor)
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets

private theorem transfer {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (old next key : OTerm α)
    (inc : Derivation body Γ (axisInclusion old next))
    (hit : Nonempty (Derivation body Γ (memberGraph old key))) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  have law : Derivation body Γ ((memberGraph old key).imp (memberGraph next key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb key) inc)
  obtain ⟨hit⟩ := hit
  exact ⟨Derivation.implicationElimination law hit⟩

theorem exact_OpenSelectedNonemptyArgsAtBounds : ExactOpenSelectedNonemptyArgsAtBounds := by
  intro W body α Γ d H K M dq Mq da Ma qState qTerms qArgs aState aTerms aArgs
    prev prevTerms prevArgs next nextTerms nextArgs ctx ty q tail typed ih
    headScope tailScope tailHit qDepth qWidth aDepth aWidth before after
  obtain ⟨typed⟩ := typed
  obtain ⟨ih⟩ := ih
  have headHit := Nonempty.intro (Derivation.implicationElimination ih typed)
  obtain ⟨f⟩ := exact_OpenSelectedGrammarCrossBound body α Γ dq d H K Mq M
    qState qTerms qArgs prev prevTerms prevArgs qDepth qWidth headScope before
  obtain ⟨a⟩ := exact_OpenSelectedGrammarCrossBound body α Γ da d H K Ma M
    aState aTerms aArgs prev prevTerms prevArgs aDepth aWidth tailScope before
  have onTerms := transfer qTerms prevTerms q (Derivation.conjunctionLeft f) headHit
  have onArgs := transfer aArgs prevArgs tail (Derivation.conjunctionRight a) tailHit
  exact exact_OpenSelectedNonemptyArgsFromPredecessor body α Γ d H K M
    prev prevTerms prevArgs next nextTerms nextArgs q tail before after onTerms onArgs

#print axioms exact_OpenSelectedNonemptyArgsAtBounds

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsBoundsProof
