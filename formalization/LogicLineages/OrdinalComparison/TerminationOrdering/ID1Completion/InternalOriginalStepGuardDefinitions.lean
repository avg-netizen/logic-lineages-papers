module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuard
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL raw source-universe test, including the window filter. -/
def sourceValidityValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) : Nat :=
  (NumberedNumericCarrier.rawCarrierTest n arity symbols S Gamma value).toNat

/-- The ORIGINAL packed target decoder. There is deliberately no universe
filter or subtype-closure hypothesis on the target. -/
def targetValidityValue (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (value : Nat) : Nat :=
  (NumberedNumericDecoding.decodePackedNumber n arity Gamma value).isSome.toNat

/-- Only two finite Program ASTs, with no correctness or derivability fields.
The same source-validity AST can later be shared by typed and endpoint wrappers. -/
structure Data where
  sourceValid : Program 1
  targetValid : Program 1

/-- All natural inputs, including failed decodes and arbitrary windows.
This is external evaluation calibration, never an internal proof rule. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (data : Data) : Prop :=
  (∀ v : List.Vector Nat 1, evaluate data.sourceValid v =
    sourceValidityValue n arity symbols S Gamma (v.get 0)) ∧
  (∀ v : List.Vector Nat 1, evaluate data.targetValid v =
    targetValidityValue n arity Gamma (v.get 0))

/-- Input coordinates remain [raw source, raw target, raw step certificate]. -/
def sourceAt (data : Data) : Program 3 :=
  .composition data.sourceValid (fun _ : Fin 1 => .projection 0)

def targetAt (data : Data) : Program 3 :=
  .composition data.targetValid (fun _ : Fin 1 => .projection 1)

/-- Literal numeric equality of the ORIGINAL outer packed type fields. -/
def sameOuterTypes : Program 3 :=
  InternalApplicationStepPeel.same (leftOf (.projection 0)) (leftOf (.projection 1))

/-- Every conjunct accepts exactly at one. A failed guard returns zero. -/
def guards (data : Data) : Program 3 :=
  InternalAcceptance.conjunction (sourceAt data)
    (InternalAcceptance.conjunction (targetAt data) sameOuterTypes)

/-- A concrete guard-normalized wrapper around the supplied old checker.
No checker is replaced solely on the basis of equal natural evaluations. -/
def checker (data : Data) (oldChecker : Program 3) : Program 3 :=
  InternalAcceptance.conjunction (guards data) oldChecker

abbrev one {α : Type} : OTerm α :=
  OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm

def accepted {α : Type} (data : Data) (oldChecker : Program 3)
    (s t k : OTerm α) : Formula α :=
  graph3 (checker data oldChecker) one s t k

/-- Independent supplied outputs of the actual original unpair-left program.
Equality of these outputs is a conclusion of acceptance, not a premise. -/
def tagGraphs {α : Type} (sourceTag targetTag s t : OTerm α) : Formula α :=
  graph1 InternalUnpair.left sourceTag s ⊓ graph1 InternalUnpair.left targetTag t

def requirements {α : Type} (data : Data) (oldChecker : Program 3)
    (sourceTag targetTag s t k : OTerm α) : Formula α :=
  graph1 data.sourceValid one s ⊓
    (graph1 data.targetValid one t ⊓
      (equal sourceTag targetTag ⊓ graph3 oldChecker one s t k))

/-- At a supplied SOURCE type tag, the target tag graph is derived rather
than assumed. The raw source and packed target validity graphs are retained. -/
def taggedRequirements {α : Type} (data : Data) (oldChecker : Program 3)
    (tag s t k : OTerm α) : Formula α :=
  graph1 data.sourceValid one s ⊓
    (graph1 data.targetValid one t ⊓
      (graph1 InternalUnpair.left tag t ⊓ graph3 oldChecker one s t k))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuard
