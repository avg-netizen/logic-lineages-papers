module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBranchWrappersForwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedHeadBaseForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedGrammarType)
open NumberedWindowInternalCoverHeadWindowTargets (headBaseAt grammarHeadBase headArity headTag storedHeadInGrammar)
open NumberedWindowInternalCoverLocalGraphForwardTargets (TapeForward)
open NumberedWindowInternalCoverFittedBranchWrappersForwardProof (carryGuardWrapper)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} {xs : Fin 2 → OTerm α}

theorem numberedBaseForward (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (numberedTypeBase s P) (numberedTypeBase s Q) body Γ xs :=
  carryGuardWrapper (onRaw (header 5 5)) (normalize (onRaw (numberedGrammarType s))) P Q pq

theorem headAtForward (b : Bool) (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (headBaseAt b s P) (headBaseAt b s Q) body Γ xs :=
  carryGuardWrapper (onRaw (header (headTag b) (headArity b)))
    (normalize (onRaw (storedHeadInGrammar s))) P Q pq

theorem headBaseForward (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (grammarHeadBase s P) (grammarHeadBase s Q) body Γ xs :=
  headAtForward false s _ _ (headAtForward true s P Q pq)

#print axioms numberedBaseForward
#print axioms headAtForward
#print axioms headBaseForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedHeadBaseForwardProof
