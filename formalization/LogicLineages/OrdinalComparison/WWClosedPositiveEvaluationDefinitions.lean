module
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions
public import LogicLineages.OrdinalComparison.NaturalProduct

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- Literal closed positive ordinal syntax retained by the forward translation.
Unlike finite-natural expression syntax, this includes actual Omega. -/
inductive ClosedPositive where
  | one
  | omega
  | add : ClosedPositive → ClosedPositive → ClosedPositive
  | emul : ClosedPositive → ClosedPositive → ClosedPositive

/-- Total executable evaluation into verified normal ordinal notations.
Exponentiation is genuine ordinal exponentiation, not natural exponentiation
or an AST-size surrogate. The operation is independent of any policy oracle. -/
def ClosedPositive.evaluate : ClosedPositive → NONote
  | .one => ⟨1, ONote.nf_one⟩
  | .omega => ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  | .add a b => naturalSum a.evaluate b.evaluate
  | .emul a b => naturalProduct (NONote.opow ⟨ONote.ofNat 2, inferInstance⟩ a.evaluate) b.evaluate

/-- Refusing structural extraction: variables, Zero and every collapse are
rejected rather than evaluated or silently replaced. -/
def extractPositive {Γ : List Ty} : OrdinalExpression Γ → Option ClosedPositive
  | .one => some .one
  | .omega => some .omega
  | .add a b => do
      let x ← extractPositive a
      let y ← extractPositive b
      pure (.add x y)
  | .emul a b => do
      let x ← extractPositive a
      let y ← extractPositive b
      pure (.emul x y)
  | .var _ | .zero | .collapse _ _ => none

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
