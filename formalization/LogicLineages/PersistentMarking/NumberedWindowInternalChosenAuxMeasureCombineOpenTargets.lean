module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalAdditionLawsProof (add)
open NumberedWindowInternalChosenAuxMeasureCombine

abbrev codePair {α : Type} (m depth numerals : OTerm α) :=
  programGraph ID1Completion.InternalPairing.pairing m ![depth,numerals]

abbrev boundReport {α : Type} (p df da bf ba b : OTerm α) : Formula α :=
  codePair p (suc (add df da)) b ⊓
    ((ltF df (suc (add df da)) ⊓ ltF da (suc (add df da))) ⊓
      (ltF bf (suc b) ⊓ ltF ba (suc b)))

abbrev boundBody {α : Type} (p df da bf ba : OTerm α) : Formula (α ⊕ Fin 1) :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  boundReport (p.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j)
    (.var (.inr 0))

/-- At actual child pair reports and the very same chosen combine graph,
one genuine output pair shares its numeral bound with both weak
numeral inequalities. The two depth comparisons are with the parent's
predecessor depth, using the original less-than-successor form.
No statement about grammar occurrences or stage transport is made. -/
def ExactOpenChosenAuxMeasureCombine : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p mf ma df da bf ba : OTerm α),
    Nonempty (Derivation body Γ (codePair mf df bf)) →
    Nonempty (Derivation body Γ (codePair ma da ba)) →
    Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])) →
    Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba)))

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
