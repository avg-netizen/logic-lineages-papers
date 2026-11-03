module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValue
open Source Source.SourceTypedPorts Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom

abbrev Name (B : Nat) := Sum (Fin B) Nat

def variableName {B : Nat} (Γ : List Ty) : (P : PortContext B) → {τ : Ty} → Variable (portTypes P ++ Γ) τ → Name B
  | [], _, v => Sum.inr (variableIndex v)
  | p :: P, _, .here => Sum.inl p.1
  | _ :: P, _, .there v => variableName Γ P v

def portVariable {B : Nat} (Γ : List Ty) (p : Fin B × Ty) :
    (P : PortContext B) → p ∈ P → Variable (portTypes P ++ Γ) p.2
  | [], h => False.elim (List.not_mem_nil h)
  | q :: P, h => if he : p=q then by cases he; exact .here
    else .there (portVariable Γ p P ((List.mem_cons.mp h).resolve_left he))

/-- Actual typed renaming, allowing the target port list to reorder existing names. -/
def extendVariables {B : Nat} (Γ : List Ty) (Q : PortContext B) :
    (P : PortContext B) → (∀ p ∈ P,p ∈ Q) → Renaming (portTypes P ++ Γ) (portTypes Q ++ Γ)
  | [], _ => fun v => shiftVariable (portTypes Q) v
  | p :: P, h => fun v => match v with
    | .here => portVariable Γ p Q (h p (List.mem_cons_self))
    | .there v => extendVariables Γ Q P (fun p hp => h p (List.mem_cons_of_mem _ hp)) v

def observationName {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (o : Observation Symbol arity Γ B) : Option (Name B) :=
  match o.body with
  | .var v => some (variableName Γ o.ports v)
  | _ => none

def variableBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {τ : Ty} {P : World I} (v : Variable (portTypes P.val ++ I.context) τ) : Bits I τ P :=
  fun _ => ⟨true,(fun o => decide (observationName o.val=some (variableName I.context P.val v))),(fun _ => false)⟩

def variableRaw {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {τ : Ty} {P : World I} (v : Variable (portTypes P.val ++ I.context) τ) : NaturalTupleLayer.Raw I τ (lower I τ) P :=
  ⟨variableBits v,fun Q s _ => bottomValue I s.val.2 Q.val⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValue
