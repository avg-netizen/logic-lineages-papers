module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (applications)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)

def reorder {m n : Nat} (P : Program m) (slots : Fin m → Fin n) : Program n :=
  .composition P (fun i => .projection (slots i))

def binary {n : Nat} (P : Program 2) (a b : Program n) : Program n :=
  .composition P (Fin.cons a (Fin.cons b Fin.elim0))

/-- Field tape [argument, domain, codomain, function]. The inner node uses
the sparse number codec, while its containing list uses standard cons. -/
def auxCode : Program 4 :=
  binary fieldCons (literal 4 6)
    (binary fieldCons (.projection 1)
      (binary fieldCons (.projection 2)
        (binary fieldCons (.projection 3) (binary fieldCons (.projection 0) (constantZero 4)))))

def singletonAux : Program 4 := binary consCode auxCode (constantZero 4)

/-- Input [function, terms, domain, codomain]. -/
def argAxis : Program 4 := reorder (flatMap singletonAux) ![1,2,3,0]

/-- Input [codomain, types, terms, domain]. -/
def fnAxis : Program 4 := reorder (flatMap argAxis) ![2,2,3,0]

/-- Input [domain, types, terms]. -/
def codAxis : Program 3 := reorder (flatMap fnAxis) ![1,1,2,0]

/-- Input [types, terms]. All source occurrences are retained, in order. -/
def auxApplications : Program 2 := reorder (flatMap codAxis) ![0,0,1]

def ExactAuxApplicationsValue : Prop := ∀ K ts : List Nat,
  evaluate auxApplications (numbersNumber K ::ᵥ numbersNumber ts ::ᵥ nil) = numbersNumber (applications K ts)

def ExactOpenAuxApplicationsMember : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (K ts dom cod fn arg out : OTerm α),
    Nonempty (Derivation body Γ (memberGraph K dom)) →
    Nonempty (Derivation body Γ (memberGraph K cod)) →
    Nonempty (Derivation body Γ (memberGraph ts fn)) →
    Nonempty (Derivation body Γ (memberGraph ts arg)) →
    Nonempty (Derivation body Γ (programGraph auxApplications out ![K,ts])) →
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
