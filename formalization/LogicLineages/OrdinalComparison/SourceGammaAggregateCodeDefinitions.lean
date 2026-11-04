module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode

/-- Actual fresh ground lambda followed by application, in the existing radix-eight codec. -/
def eraserCode (a b : Nat) : Nat :=
  8*Nat.pair (8*Nat.pair 0 (ContextInsertionCode.sourceCode 0 1 a)+6) b+5
def leftCode (a b : Nat) : Nat := eraserCode (eraserCode a a) (eraserCode b b)
def rightCode (a b : Nat) : Nat := eraserCode (eraserCode a b) (eraserCode b a)
def step (p tail : Nat×Nat) : Nat×Nat :=
  (eraserCode (leftCode p.1 p.2) tail.1, eraserCode (rightCode p.1 p.2) tail.2)
def aggregateCode (es : List (Nat×Nat)) : Nat×Nat := es.foldr step (1,1)
def pairCode {Γ} (p : OriginalTerm Γ .ground × OriginalTerm Γ .ground) : Nat×Nat :=
  (SyntaxCode.encodeTerm p.1,SyntaxCode.encodeTerm p.2)
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode
