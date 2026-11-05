module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionDefinitions
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVector
open Source Source.ForwardTranslation CommonLayerSyntax

/-- Modes 0, 1, and all remaining codes mean weak, WW-strict, and equality.
Strictness is confined to coordinate zero; positive coordinates stay weak. -/
def scalarRelation (mode a b : Nat) : Prop :=
  if mode = 0 then a ≤ b else if mode = 1 then a < b else a = b

def scalarFormula (mode : Nat) (a b : BaseTerm) : BaseFormula.Formula :=
  if mode = 0 then .negative (.less b a)
  else if mode = 1 then .less a b else .equal a b

def formula (n mode : Nat) (a b : BaseTerm) : BaseFormula.Formula :=
  .disjunction (.negative (BalancedClosureDecision.positiveFormula (List.range n)))
    (scalarFormula mode a b)

def positiveFlag (mode : Nat) (a b : EncodedVector) : Bool :=
  let ab := positiveComparison (a.2.map encodedClosedPositive) (b.2.map encodedClosedPositive)
  if mode = 0 then ab else if mode = 1 then ab else
    ab && positiveComparison (b.2.map encodedClosedPositive) (a.2.map encodedClosedPositive)

noncomputable def vectorRelation {ι : Type} {n m : Nat} (mode : Nat)
    (a : CompiledVector ι n) (b : CompiledVector ι m) (ρ : ι → Nat) : Prop :=
  (if mode = 0 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
   else if mode = 1 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
   else ∀ j, positiveNoteAt a.positiveNotes j = positiveNoteAt b.positiveNotes j) ∧
  scalarRelation mode (a.scalar.value ρ) (b.scalar.value ρ)

/-- Actual original assignment relation, with its existing zero padding. -/
noncomputable def sourceRelation {Γ : List Ty} {n m : Nat} (mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m) (ρ : OrdinalComponent Γ → Nat) : Prop :=
  if mode = 0 then SourceComparisonAt false a b ρ
  else if mode = 1 then SourceComparisonAt true a b ρ
  else ∀ j, sourceVectorAtValue a ρ j = sourceVectorAtValue b ρ j

namespace Code
abbrev Input := Nat × Nat × Nat × Nat
abbrev VectorInput := Nat × Nat × EncodedVector × EncodedVector

def formula (n mode a b : Nat) : List CommonHeadCompiler.Instruction :=
  CommonHeadCode.disjunction
    (CommonHeadCode.negative (BalancedClosureDecision.positiveCode (List.range n)))
    (if mode = 0 then CommonHeadCode.negative [(3,b,a)]
     else if mode = 1 then [(3,a,b)] else [(2,a,b)])

def decideVectors (p : VectorInput) : Option Bool := do
  let a ← FiniteCoefficientBase.Code.compile p.2.2.1.1
  let b ← FiniteCoefficientBase.Code.compile p.2.2.2.1
  let answer ← BaseBooleanSource.Code.decideClosureForall (formula p.1 p.2.1 a b)
  return positiveFlag p.2.1 p.2.2.1 p.2.2.2 && answer

/-- Literal original-term-code pipeline: canonical assignment, original vector
compiler, finite-coefficient scalar compiler, closed BASE decision. -/
def decideSource (p : Input) : Option Bool := do
  let a ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)
  let b ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)
  decideVectors (p.1,p.2.1,a,b)
end Code
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVector
