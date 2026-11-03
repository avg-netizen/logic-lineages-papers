module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets

def PackedGood {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (K : Ty → Prop) (H : Head Symbol → Prop) (q : NumberedRewriteReduction.Packed Symbol arity Gamma) : Prop := Good K H q.2

def ActualArgumentOccurrences : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop) (H : Head Symbol → Prop)
    (Gamma types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    GoodArguments K H args ↔ ∀ q∈NumberedRewriteReduction.argumentList args,PackedGood K H q

def ActualArgumentAppend : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop) (H : Head Symbol → Prop)
    (Gamma xs ys : List Ty) (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys),
    GoodArguments K H a → GoodArguments K H b → GoodArguments K H (NumberedRewriteSyntax.appendArguments a b)

def ActualCompleteApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop) (H : Head Symbol → Prop),SubtypeClosed K →
    ∀ (Gamma types : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types),
    Good K H q → GoodArguments K H args → Good K H (NumberedRewriteReduction.applyArguments q args)

def ActualPrimitiveMultiset : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop) (H : Head Symbol → Prop)
    (Gamma : List Ty) (ss ts : List (NumberedRewriteReduction.Packed Symbol arity Gamma)),
    PrimitiveMultiset ss ts → (∀ q∈ss,PackedGood K H q) → ∀ q∈ts,PackedGood K H q

def ActualSelect : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop) (H : Head Symbol → Prop),SubtypeClosed K →
    ∀ (n : Nat) (Gamma : List Ty) (f : Head Symbol) (tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
    (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty)
    (selected : AuxTerm Symbol arity Gamma (arrows types tau)),
    (⟨arrows types tau,selected⟩ : NumberedRewriteReduction.Packed Symbol arity Gamma)∈
      NumberedRewriteReduction.argumentList base++NumberedRewriteReduction.argumentList extras →
    Good K H (.numbered (n+1) f tau base extraTypes extras) →
    Good K H (NumberedRewriteReduction.applyArguments selected
      (NumberedRewriteReduction.selfArguments n f base extraTypes extras types))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsTargets
