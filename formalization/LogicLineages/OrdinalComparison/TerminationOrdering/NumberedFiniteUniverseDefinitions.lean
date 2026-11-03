module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationProof

@[expose] public section
/-! Actual finite head window for the source's fixed-type auxiliary universe.
A finite retyped output does not bound a native head's former annotation.
The window checks ORIGINAL result/base types; these guards are derived for
ordinary source embeddings rather than added to the original comparison.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverse
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax

def RankedCovered {Symbol : Type} (symbols : List Symbol) : Head Symbol → Prop
  | .ranked s => s∈symbols
  | _ => True

def HeadInWindow {Symbol : Type} (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (f : Head Symbol) : Prop :=
  RankedCovered symbols f ∧ headResult f∈S ∧ ∀ tau∈headArguments arity f,tau∈S

instance headInWindowDecidable {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (f : Head Symbol) : Decidable (HeadInWindow arity symbols S f) := by
  unfold HeadInWindow
  cases f <;> unfold RankedCovered <;> infer_instance

def rawHeadWindow {Symbol : Type} (symbols : List Symbol) (S : List Ty) : List (Head Symbol) :=
  [.zero,.succ] ++ (S.flatMap fun tau => [.cases tau,.recursor tau]) ++
    (S.flatMap fun sigma => S.map fun tau => .application sigma tau) ++ symbols.map .ranked

def headWindow {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) : List (Head Symbol) :=
  (rawHeadWindow symbols S).filter (fun f => decide (HeadInWindow arity symbols S f))

mutual
def auxTypesAllowed {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Prop
  | .var _ => K tau
  | @AuxTerm.lam _ _ _ sigma _ body => K tau ∧ K sigma ∧ auxTypesAllowed K body
  | .app q a => K tau ∧ auxTypesAllowed K q ∧ auxTypesAllowed K a
  | .bottom _ => K tau
  | .ordinary _ base => K tau ∧ auxArgumentTypesAllowed K base
  | .numbered _ _ _ base _ extras => K tau ∧ auxArgumentTypesAllowed K base ∧ auxArgumentTypesAllowed K extras
def auxArgumentTypesAllowed {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) {Gamma types : List Ty} : AuxArguments Symbol arity Gamma types → Prop
  | .nil => True
  | .cons q rest => auxTypesAllowed K q ∧ auxArgumentTypesAllowed K rest
end

mutual
def auxHeadsAllowed {Symbol : Type} {arity : Symbol → Nat} (H : Head Symbol → Prop) {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Prop
  | .var _ | .bottom _ => True
  | .lam body => auxHeadsAllowed H body
  | .app q a => auxHeadsAllowed H q ∧ auxHeadsAllowed H a
  | .ordinary f base => H f ∧ auxArgumentsAllowed H base
  | .numbered _ f _ base _ extras => H f ∧ auxArgumentsAllowed H base ∧ auxArgumentsAllowed H extras
def auxArgumentsAllowed {Symbol : Type} {arity : Symbol → Nat} (H : Head Symbol → Prop) {Gamma types : List Ty} : AuxArguments Symbol arity Gamma types → Prop
  | .nil => True
  | .cons q rest => auxHeadsAllowed H q ∧ auxArgumentsAllowed H rest
end

def InUniverse {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) : Prop :=
  auxTypesAllowed (fun t => t∈S) q ∧ auxHeadsAllowed (HeadInWindow arity symbols S) q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverse
