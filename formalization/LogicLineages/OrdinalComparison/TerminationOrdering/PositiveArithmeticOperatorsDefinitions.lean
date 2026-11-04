module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperators
open FirstOrder Language
open OrdinaryArithmetic

inductive RelationSymbol : Nat → Type where
  | predicate : RelationSymbol 1

def language : Language := ⟨FunctionSymbol,RelationSymbol⟩

def arithmeticEmbedding : arithmeticLanguage →ᴸ language where
  onFunction := fun _ f => f
  onRelation := fun _ r => nomatch r

@[reducible] def naturalStructure (P : Nat → Prop) : language.Structure Nat where
  funMap := fun {_} f v => match f with
    | .zero => 0
    | .succ => Nat.succ (v 0)
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
  RelMap := fun {_} r v => match r with
    | .predicate => P (v 0)

def realize {α : Type} (P : Nat → Prop) (phi : language.Formula α) (v : α → Nat) : Prop :=
  letI := naturalStructure P
  phi.Realize v

/-- Grammar allowing the new predicate only positively; arithmetic antecedents contain no predicate. -/
inductive Positive : Type → Type 1 where
  | arithmetic {α : Type} : OrdinaryArithmetic.Formula α → Positive α
  | predicate {α : Type} : OrdinaryArithmetic.Term α → Positive α
  | conj {α : Type} : Positive α → Positive α → Positive α
  | guarded {α : Type} : OrdinaryArithmetic.Formula α → Positive α → Positive α
  | all {α : Type} : Positive (α ⊕ Fin 1) → Positive α

def Positive.formula : {α : Type} → Positive α → language.Formula α
  | _, .arithmetic phi => arithmeticEmbedding.onFormula phi
  | _, .predicate t => Relations.formula₁ (L := language) RelationSymbol.predicate (arithmeticEmbedding.onTerm t)
  | _, .conj p q => p.formula ⊓ q.formula
  | _, .guarded guard p => (arithmeticEmbedding.onFormula guard).imp p.formula
  | _, .all p => (BoundedFormula.relabel (id : _ → _) p.formula).alls

/-- Free variables are shared context and current object; the bound variable is a successor. -/
def accessibilityOperator (carrier : OrdinaryArithmetic.Formula (Fin 2))
    (edge : OrdinaryArithmetic.Formula (Fin 3)) : Positive (Fin 2) :=
  .conj (.arithmetic carrier) (.all (.guarded
    (edge.subst ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))])
    (.predicate (.var (.inr (0 : Fin 1))))))

def encodedR (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty) (context x y : Nat) : Prop :=
  ∃ ctx : OrdinaryArithmeticQuotient.Context n, Encodable.decode context = some ctx ∧
    NumberedQuotientPaths.PositivePath (NumberedQuotientPaths.QuotientEdge n arity ctx.1.1 ctx.1.2
      (NumberedCopyCertificate.tableAbove ctx.2) Gamma) x y

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperators
