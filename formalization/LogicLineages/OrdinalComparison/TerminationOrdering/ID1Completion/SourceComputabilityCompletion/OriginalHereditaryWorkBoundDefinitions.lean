module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeNativeSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBound
open Source NumberedAuxiliaryCoding OriginalStructuralNodeSize OriginalRawSyntaxTransport
/-- Native work state. Raw argument-list nodes are counted too; this is an
over-enumeration for typed-child observations, not a semantic BASE ordering. -/
structure State (Symbol : Type) where
  context : List Ty
  code : Code Symbol

def weight {Symbol : Type} (s : State Symbol) : Nat := s.context.length + 2 * nodeCount s.code

def children {Symbol : Type} (Gamma : List Ty) : Code Symbol → List (State Symbol)
 | .var _ => []
 | .bottom _ => []
 | .argumentsNil => []
 | .lam sigma q => [⟨sigma::Gamma,q⟩]
 | .app sigma f a => [⟨Gamma,f⟩,⟨Gamma,a⟩]
 | .ordinary head base => [⟨Gamma,base⟩]
 | .numbered label head tau base types extras => [⟨Gamma,base⟩,⟨Gamma,extras⟩]
 | .argumentsCons tau q rest => [⟨Gamma,q⟩,⟨Gamma,rest⟩]

/-- One branch per context occurrence, even equal entries. Zero is included
at every state, in particular at a lambda child's newly extended context. -/
def deletionsFrom {Symbol : Type} (code : Code Symbol) (initialContext : List Ty) : List Ty → List (State Symbol)
 | [] => []
 | sigma :: tail => ⟨initialContext ++ tail,eraseCode sigma initialContext.length code⟩ ::
     deletionsFrom code (initialContext ++ [sigma]) tail

def successors {Symbol : Type} (s : State Symbol) : List (State Symbol) :=
  children s.context s.code ++ deletionsFrom s.code [] s.context

/-- Count every visit and duplicate branch in a finite expansion. No deduplication. -/
def visits {Symbol : Type} : Nat → State Symbol → Nat
 | 0, _ => 1
 | depth+1, s => 1 + ((successors s).map (visits depth)).sum
/-- Explicit primitive-recursive geometric-series budget. -/
def budget (branching : Nat) : Nat → Nat
 | 0 => 1
 | depth+1 => 1 + branching * budget branching depth

def totalWork {Symbol : Type} (s : State Symbol) := visits (weight s) s
inductive Path {Symbol : Type} : Nat → State Symbol → State Symbol → Prop where
 | refl (s) : Path 0 s s
 | cons {depth s t u} : t ∈ successors s → Path depth t u → Path (depth+1) s u
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBound
