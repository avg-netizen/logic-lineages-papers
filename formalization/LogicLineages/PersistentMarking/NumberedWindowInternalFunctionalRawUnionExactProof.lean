module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackInverseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionExactProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (positiveGraph)
open NumberedWindowInternalDirectTypedListTargets (parsedPayload)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalFunctionalRawRepackInverseProof (exact_FunctionalRawRepackOfParser)
open NumberedWindowInternalFunctionalRawUnion
open NumberedWindowInternalConsUnionReportBuildProof (Report)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem knownSide (i : Fin 2) (xs : Fin 2 → OTerm α) (value : OTerm α)
    (held : Nonempty (Derivation B Γ (positiveGraph (xs i) value))) :
    Report (B := B) (Γ := Γ) (side i) value xs := by
  have p : Report (B := B) (Γ := Γ) parsedPayload value ![xs i] := by
    apply compositionValue predecessor (Fin.cons parser Fin.elim0) value ![xs i] ![suc value]
      (predecessorSuccessor value)
    intro q
    obtain rfl := Fin.eq_zero q
    exact held
  apply compositionValue parsedPayload ![.projection i] value xs ![xs i] p
  intro q
  obtain rfl := Fin.eq_zero q
  exact projectionValue i xs

/-- Define the functional graph from the actual positive parsers and
the exact ordered append. In particular, this does not use an arbitrary
permutation report to equate an unordered output with the fixed output. -/
theorem exact_FunctionalRawUnionOfAppend (a b out sa sb scratch : OTerm α)
    (la : Nonempty (Derivation B Γ (positiveGraph a sa)))
    (rb : Nonempty (Derivation B Γ (positiveGraph b sb)))
    (formed : Report (B := B) (Γ := Γ) append scratch ![sa,sb])
    (parsed : Nonempty (Derivation B Γ (positiveGraph out scratch))) :
    Report (B := B) (Γ := Γ) functionalUnion out ![a,b] := by
  have initial : Report (B := B) (Γ := Γ) joinedScratch scratch ![a,b] := by
    apply compositionValue append ![side 0,side 1] scratch ![a,b] ![sa,sb] formed
    intro i
    exact Fin.cases (knownSide 0 ![a,b] sa la)
      (Fin.cases (knownSide 1 ![a,b] sb rb) (fun j => Fin.elim0 j)) i
  apply compositionValue repack ![joinedScratch] out ![a,b] ![scratch]
    (exact_FunctionalRawRepackOfParser out scratch parsed)
  intro q
  obtain rfl := Fin.eq_zero q
  exact initial

#print axioms exact_FunctionalRawUnionOfAppend
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionExactProof
