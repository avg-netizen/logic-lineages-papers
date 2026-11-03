module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedSyntaxBoundsPrimrec

/-- Exact agreement with both original term measurements. -/
def ActualTermBoundsCalibration : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty)
    (q : AuxTerm Symbol arity Gamma tau),
    codeBounds (termCode q) = (NumberedPrimaryEquivalence.size q, maxLabel q)

/-- Exact agreement with both original argument-list measurements. -/
def ActualArgumentsBoundsCalibration : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty)
    (args : AuxArguments Symbol arity Gamma types),
    codeBounds (argumentsCode args) =
      (NumberedPrimaryEquivalence.argumentsSize args, argumentsMaxLabel args)

/-- Both literal measurements are primitive recursive on every syntax code. -/
def ActualCodeBoundsPrimitive : Prop :=
  ∀ n : Nat, Primrec (@codeBounds (Fin n))

/-- The original measurements on genuinely presented packed typed syntax. -/
def ActualPackedBoundsPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun q : Packed (Fin n) arity Gamma =>
      (NumberedPrimaryEquivalence.size q.2, maxLabel q.2))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecTargets
