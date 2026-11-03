module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBitsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecision
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations
open FiniteObservationBits ConfinedStructuralInterpretation TypedValueEnvironment
open SourceConstructorIteration TypedObservationAccess RecursiveComparison

/-- The literal empty port world belongs to the actual input enumeration. -/
def emptyWorld {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : World I :=
  ⟨[],(FiniteObservationBitsProof.worldCalibration Symbol arity I []).mpr (by
    simp [ValidPorts])⟩

/-- Original ordinary syntax has the actual source type/head confinement. -/
def inputSource {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) : ConfinedTerm I I.context I.sourceType :=
  ⟨embed I.source,ConfinedStructuralInterpretationProof.frameConfinement Symbol
    inferInstance arity I (FiniteQueryPrimitives.initial I.source I.target)
    (FiniteQueryPrimitivesProof.initialFrame Symbol arity I.context I.sourceType
      I.targetType I.source I.target).2⟩

/-- The target itself, without opening, renaming or a substituted surrogate. -/
def rootObservation {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) :
    Observation Symbol arity I.context (budget I) := ⟨[],I.targetType,I.target⟩

/-- The actual finite-cardinality-fuel constructor iteration followed by one
literal empty-world evaluation and the guarded original target root read.
No proof search, classical proposition decider or supplied algorithm is used. -/
def compare {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) [DecidableRel above]
    (strict : Bool) : Bool :=
  readBit strict
    (interpret (inputSource I) (limit I above) (emptyWorld I) (identity I (emptyWorld I)))
    (rootObservation I)

def OriginalWeak {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) : Prop :=
  Weak Symbol arity above I.context ⟨I.sourceType,embed I.source⟩ ⟨I.targetType,embed I.target⟩

def OriginalStrict {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) : Prop :=
  Strict Symbol arity above I.context ⟨I.sourceType,embed I.source⟩ ⟨I.targetType,embed I.target⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecision
