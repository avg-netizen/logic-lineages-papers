module
public import LogicLineages.OrdinalComparison.ComparisonExpansionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def LiteralSourceEncodingInjective : Prop := Function.Injective oneVariableComparisonEncode

def ComparisonRangePrefixProgram : Prop := Primrec encodedComparisonRangePrefix ∧
  ∀ (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr),
    encodedComparisonRangePrefix (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))=
      oneVariableComparisonEncode (.range w E)

def ComparisonExpansionProgram : Prop := Primrec encodedComparisonWord ∧ Primrec encodedComparisonOuter ∧
  Primrec₂ encodedComparisonPositiveChildren ∧ Primrec₂ encodedComparisonMixedChildren ∧
  Primrec₂ encodedComparisonChildren

/-- Every ACTUAL generated numerical child is an ACTUAL source pair, valid,
still in the SAME initial carrier, and strictly below its original source
parent in the proved well-founded transitive relation. Not a supplied oracle. -/
def ActualComparisonExpansionImage : Prop :=
  ∀ (budget : Nat) (E F : OneVariableComparisonExpr),
    oneVariableComparisonValid E → oneVariableComparisonValid F →
    comparisonSourceBounded budget E → comparisonSourceBounded budget F →
    ∀ p∈encodedComparisonChildren (oneVariableComparisonEncode E) (oneVariableComparisonEncode F),
      ∃ G H : OneVariableComparisonExpr,
        oneVariableComparisonEncode G=p.1 ∧ oneVariableComparisonEncode H=p.2 ∧
        oneVariableComparisonValid G ∧ oneVariableComparisonValid H ∧
        comparisonSourceBounded budget G ∧ comparisonSourceBounded budget H ∧
        Relation.TransGen (comparisonLiteralPairStep budget) (G,H) (E,F)

def FullActualComparisonExpansion : Prop := LiteralSourceEncodingInjective ∧
  ComparisonRangePrefixProgram ∧ ComparisonExpansionProgram ∧ ActualComparisonExpansionImage

end LogicLineages.OrdinalComparison.Targets
