module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputWalkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTestProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (chosenWalk)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePositiveOutputWalkProof (succAt succAtValue)

attribute [local irreducible] programGraph chosenWalk equalityTest

abbrev components (raw : Program 5) (least : Program 3) : Fin 2 → Program 5 :=
  ![chosenWalk raw least, succAt 4]
abbrev compareTarget (raw : Program 5) (least : Program 3) : Program 5 :=
  .composition equalityTest (components raw least)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem componentsKnown (raw : Program 5) (least : Program 3)
    (ctx ty source cert target current : OTerm α)
    (walk : Nonempty (Derivation body Γ
      (programGraph (chosenWalk raw least) current (args5 ctx ty source cert target)))) (i : Fin 2) :
    Nonempty (Derivation body Γ (programGraph (components raw least i)
      (Fin.cons current (Fin.cons (suc target) Fin.elim0) i) (args5 ctx ty source cert target))) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact walk
  · exact succAtValue (4 : Fin 5) (args5 ctx ty source cert target)

theorem matchOfEqual (raw : Program 5) (least : Program 3)
    (ctx ty source cert target current : OTerm α)
    (walk : Nonempty (Derivation body Γ
      (programGraph (chosenWalk raw least) current (args5 ctx ty source cert target))))
    (eq : Nonempty (Derivation body Γ (eqn current (suc target)))) :
    Nonempty (Derivation body Γ (programGraph (compareTarget raw least) (suc z)
      (args5 ctx ty source cert target))) :=
  compositionValue equalityTest (components raw least) (suc z) (args5 ctx ty source cert target)
    (Fin.cons current (Fin.cons (suc target) Fin.elim0)) (equalityOfEqual current (suc target) eq)
    (componentsKnown raw least ctx ty source cert target current walk)

theorem equalOfMatch (raw : Program 5) (least : Program 3)
    (ctx ty source cert target current : OTerm α)
    (walk : Nonempty (Derivation body Γ
      (programGraph (chosenWalk raw least) current (args5 ctx ty source cert target))))
    (matched : Nonempty (Derivation body Γ (programGraph (compareTarget raw least) (suc z)
      (args5 ctx ty source cert target)))) :
    Nonempty (Derivation body Γ (eqn current (suc target))) :=
  equalityOfAcceptance current (suc target)
    (compositionRecover equalityTest (components raw least) (suc z) (args5 ctx ty source cert target)
      (Fin.cons current (Fin.cons (suc target) Fin.elim0)) matched
      (componentsKnown raw least ctx ty source cert target current walk))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTestProof
