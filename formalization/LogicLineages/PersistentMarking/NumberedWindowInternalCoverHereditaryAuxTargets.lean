module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverStrictAuxForwardTargets (ChildWindowForward)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- An externally presented finite tree of actual symbolic raw terms.
Only the aux recursion edges are traversed. At a leaf, the actual two
physical decisions reject λ and aux on this exact nonzero key. -/
inductive HereditaryAuxTree (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) :
    OTerm α → Prop
  | terminal (prior : OTerm α) :
      Nonempty (Derivation body Γ (unary (header 2 2) z (suc prior))) →
      Nonempty (Derivation body Γ (unary termShape z (suc prior))) →
      HereditaryAuxTree body Γ (suc prior)
  | fork (dom cod fn arg : OTerm α) :
      Nonempty (Derivation body Γ (ltF fn (auxiliaryTerm dom cod fn arg))) →
      Nonempty (Derivation body Γ (ltF arg (auxiliaryTerm dom cod fn arg))) →
      HereditaryAuxTree body Γ fn →
      HereditaryAuxTree body Γ arg →
      HereditaryAuxTree body Γ (auxiliaryTerm dom cod fn arg)

def ExactOpenCoverHereditaryAuxWindowForward : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx raw : OTerm α),
    HereditaryAuxTree body Γ raw →
    ∀ (result : OTerm α), ChildWindowForward (numberedTypeWindow s B T) (lambdaLexicalWindow s B T)
      body Γ ctx result raw

def ExactOpenCoverLambdaHereditaryAuxOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom q p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ (lambdaTerm dom q) p vertices ctx result →
    HereditaryAuxTree body Γ q →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm dom q)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTargets
