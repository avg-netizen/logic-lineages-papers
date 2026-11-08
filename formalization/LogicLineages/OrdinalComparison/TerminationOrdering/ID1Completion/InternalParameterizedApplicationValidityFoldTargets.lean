module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalParameterizedApplicationValidityFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- EXTERNAL numeric recurrence for the actual bounded result-fold AST, on
ALL raw inputs and arbitrary p, node and leaf Programs. Every tag-two root
recurses even when node rejects; every other root normalizes the WHOLE old
leaf output. No validity, successful decoding or Boolean callback premise. -/
def ActualOriginalParameterizedValidityFoldRecurrence : Prop :=
  ∀ (node oldLeaf : Program 2) (value parameter : Nat),
  evaluate (validatorP node oldLeaf) (List.Vector.ofFn ![value,parameter]) =
    if tagValue value = 2 then
      (if evaluate node (List.Vector.ofFn ![resultTypeValue value,parameter]) = 1 ∧
          evaluate (validatorP node oldLeaf)
            (List.Vector.ofFn ![functionChildValue value,parameter]) = 1 ∧
          evaluate (validatorP node oldLeaf)
            (List.Vector.ofFn ![argumentChildValue value,parameter]) = 1 then 1 else 0)
    else if evaluate oldLeaf (List.Vector.ofFn ![value,parameter]) = 1 then 1 else 0

/-- EXTERNAL semantic agreement with the unchanged ORIGINAL predicates on
all raw values at one arbitrary p. The supplied binary leaves and membership
need calibration only at that p. This does not assert existence of globally
selected uniform binary leaves, and introduces no target universe filter. -/
def ActualOriginalParameterizedValidityFoldCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (oldSource oldTarget member : Program 2) (parameter : Nat),
  (∀ value : Nat, evaluate oldSource (List.Vector.ofFn ![value,parameter]) =
    InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value) →
  (∀ value : Nat, evaluate oldTarget (List.Vector.ofFn ![value,parameter]) =
    InternalOriginalStepGuard.targetValidityValue n arity Gamma value) →
  (∀ value : Nat, evaluate member (List.Vector.ofFn ![value,parameter]) =
    InternalStructuralEndpointGuard.membershipValue S value) →
  ∀ value : Nat,
    evaluate (targetP oldTarget) (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value ∧
    evaluate (universeP oldSource member) (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value ∧
    evaluate (sourceP oldSource oldTarget member) (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value

/-- INTERNAL closure for actual Programs, arbitrary context and original
constructor graphs. The node gets e,p and both children and parent retain p.
No supplied goodRunP=1, semantic calibration, validity or fuel premise occurs;
the pending original parameterized totality/application equation must supply
machine success internally. -/
def ActualOriginalParameterizedValidityFoldApplicationClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (node oldLeaf : Program 2) (α : Type)
    (Gamma : List (Formula α))
    (arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 node InternalOriginalStepGuard.one e parameter ⊓
        (graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one fn parameter ⊓
          graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one arg parameter))).imp
      (graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one parent parameter)))

/-- INTERNAL source-to-target acceptance is a direct consequence of the
actual source conjunction, for arbitrary binary Programs and symbolic p.
No external old-leaf calibration or source-implies-target fact is a premise. -/
def ActualOriginalParameterizedValidityFoldSourceImpliesTarget : Prop :=
  ∀ (body : Positive (Fin 1)) (oldSource oldTarget member : Program 2) (α : Type)
    (Gamma : List (Formula α)) (value parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((graph2 (sourceP oldSource oldTarget member) InternalOriginalStepGuard.one value parameter).imp
      (graph2 (targetP oldTarget) InternalOriginalStepGuard.one value parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldTargets
