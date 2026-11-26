module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBranchWrappersForwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedAtomicBaseForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarAt namedGrammarBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultAt namedResultBase storedTypeResult)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase lexicalGuard)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalCoverLocalGraphForwardTargets (TapeForward)
open NumberedWindowInternalCoverFittedBranchWrappersForwardProof (carryGuardWrapper carryOutputWrapper)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} {xs : Fin 2 → OTerm α}

private theorem namedResultAtForward (b : Bool) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (namedResultAt b P) (namedResultAt b Q) body Γ xs :=
  carryOutputWrapper (onRaw (header b.toNat 2)) (constantZero 2) storedTypeResult P Q pq

private theorem namedGrammarAtForward (s : Settings) (b : Bool) (P Q : Program 2)
    (pq : TapeForward P Q body Γ xs) :
    TapeForward (namedGrammarAt b s P) (namedGrammarAt b s Q) body Γ xs :=
  carryGuardWrapper (onRaw (header b.toNat 2)) (normalize (onRaw (leafTypeTest s))) P Q pq

private theorem namedResultForward (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (namedResultBase P) (namedResultBase Q) body Γ xs :=
  namedResultAtForward false _ _ (namedResultAtForward true P Q pq)

private theorem lexicalForward (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (lexicalBoundBase P) (lexicalBoundBase Q) body Γ xs :=
  carryGuardWrapper (onRaw (header 1 2)) (normalize lexicalGuard) P Q pq

private theorem nameGrammarForward (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (namedGrammarBase s P) (namedGrammarBase s Q) body Γ xs :=
  namedGrammarAtForward s false _ _ (namedGrammarAtForward s true P Q pq)

private theorem typeLeafForward (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (leafIntrinsicBase s P) (leafIntrinsicBase s Q) body Γ xs :=
  carryGuardWrapper (onRaw (header 3 1)) (normalize (onRaw (leafTypeTest s))) P Q pq

theorem fittedAtomicForward (s : Settings) (P Q : Program 2) (pq : TapeForward P Q body Γ xs) :
    TapeForward (fittedWindowBase s P) (fittedWindowBase s Q) body Γ xs :=
  typeLeafForward s _ _ (nameGrammarForward s _ _ (lexicalForward _ _ (namedResultForward P Q pq)))

#print axioms fittedAtomicForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedAtomicBaseForwardProof
