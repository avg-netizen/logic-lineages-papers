module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedMarkCertificate NumberedFiniteMarkPrimrec

/-- Exact original finite marking, including arbitrary initial lambda nesting. -/
def ActualFiniteMarkCodeCalibration : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty)
    (label : Nat) (q : AuxTerm Symbol arity Gamma tau),
    finiteMarkCode label (termCode q) = (finiteMark label q).map termCode

/-- Primitive recursion is joint in the literal mark label and every raw code. -/
def ActualFiniteMarkCodePrimitive : Prop :=
  ∀ n : Nat,
    Primrec (fun p : Nat × Code (Fin n) => finiteMarkCode p.1 p.2)

/-- The original packed partial marking operation under its genuine presentation. -/
def ActualMarkTargetPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : Nat × Packed (Fin n) arity Gamma => markTarget p.1 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecTargets
