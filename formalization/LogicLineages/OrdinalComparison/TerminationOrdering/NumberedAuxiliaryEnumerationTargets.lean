module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration
def ActualTypeListEnumeration : Prop := ∀ (S : List Ty) (bound : Nat) (types : List Ty),types∈typeLists S bound ↔ types.length≤bound ∧ ∀ tau∈types,tau∈S

def ActualCodeEnumeration : Prop := ∀ (Symbol : Type) (S : List Ty) (H : List (HeadCode Symbol)) (labels tupleBound variableBound fuel : Nat) (c : Code Symbol),
  c∈enumerate S H labels tupleBound variableBound fuel ↔ Fields S H labels tupleBound variableBound c ∧ depth c≤fuel

def ActualSourceDepthBound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
  depth (termCode q)≤2*NumberedPrimaryEquivalence.size q

def ActualSourceCoverage : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau) (L : Nat),
  InUniverse symbols S q → LabelsAtMost L q →
  termCode q∈enumerate S (sourceHeads arity symbols S) L (NumberedPrimaryEquivalence.size q) Gamma.length (2*NumberedPrimaryEquivalence.size q)

def ActualPrimaryClassCoverage : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  InUniverse symbols S q.2 → WindowPrimary Symbol arity symbols S Gamma q r → packedCode r∈classCodes symbols S q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationTargets
