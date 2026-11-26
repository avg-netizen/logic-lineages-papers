module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawRepackProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (positiveGraph)
open NumberedWindowInternalDirectTypedListTargets (parsedPayload)
open NumberedWindowInternalFunctionalRawRepack (repack)
open NumberedWindowInternalFunctionalRawRepackProof (repackGraph exact_FunctionalRawRepackParser)
open NumberedWindowInternalFunctionalRawUnion
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralEquivalenceReflexive)
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (unionGraphRename)
open NumberedWindowInternalConsUnionReportBuildProof (Report unionReportOfGraphs)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem vectorOneRename {β : Type} (j : α → β) (a : OTerm α) :
    (fun i : Fin 1 => (![a] i).relabel j) = ![a.relabel j] := by
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

private theorem vectorTwoRename {β : Type} (j : α → β) (a b : OTerm α) :
    (fun i : Fin 2 => (![a,b] i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem positiveRename {β : Type} (j : α → β) (a b : OTerm α) :
    (positiveGraph a b).relabel j = positiveGraph (a.relabel j) (b.relabel j) := by
  simp only [positiveGraph,programRename,ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
    vectorOneRename]

private theorem sideValue (i : Fin 2) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (held : Nonempty (Derivation B Γ (positiveGraph (xs i) out))) :
    Report (B := B) (Γ := Γ) (side i) out xs := by
  have unary : Report (B := B) (Γ := Γ) parsedPayload out ![xs i] := by
    apply compositionValue predecessor (Fin.cons parser Fin.elim0) out ![xs i] ![suc out]
      (predecessorSuccessor out)
    intro q
    obtain rfl := Fin.eq_zero q
    exact held
  apply compositionValue parsedPayload ![.projection i] out xs ![xs i] unary
  intro q
  obtain rfl := Fin.eq_zero q
  exact projectionValue i xs

private theorem joinValue (a b sa sb w : OTerm α)
    (pa : Nonempty (Derivation B Γ (positiveGraph a sa)))
    (pb : Nonempty (Derivation B Γ (positiveGraph b sb)))
    (joined : Report (B := B) (Γ := Γ) append w ![sa,sb]) :
    Report (B := B) (Γ := Γ) joinedScratch w ![a,b] := by
  apply compositionValue append ![side 0,side 1] w ![a,b] ![sa,sb] joined
  intro i
  exact Fin.cases (sideValue 0 ![a,b] sa pa)
    (Fin.cases (sideValue 1 ![a,b] sb pb) (fun k => Fin.elim0 k)) i

/-- On positively parsed inputs the fixed functional union's output is
accepted by the exact original certified-union graph. This is only the
functional-to-certified direction. -/
theorem exact_FunctionalRawUnionReport (a b u sa sb : OTerm α)
    (pa : Nonempty (Derivation B Γ (positiveGraph a sa)))
    (pb : Nonempty (Derivation B Γ (positiveGraph b sb)))
    (given : Report (B := B) (Γ := Γ) functionalUnion u ![a,b]) :
    Nonempty (Derivation B Γ (unionGraph permutation a b u)) := by
  apply programCases append ![sa,sb] _
  intro β j Δ joined keep report
  rw [unionGraphRename]
  have al := renameInto pa j Δ keep
  have bl := renameInto pb j Δ keep
  rw [positiveRename] at al bl
  have moved := renameInto given j Δ keep
  rw [programRename,vectorTwoRename] at moved
  have written : Report (B := B) (Γ := Δ) append joined ![sa.relabel j,sb.relabel j] := by
    simpa only [vectorTwoRename] using report
  have jv := joinValue (a.relabel j) (b.relabel j) (sa.relabel j) (sb.relabel j) joined al bl written
  have captured : Nonempty (Derivation B Δ (repackGraph (u.relabel j) joined)) := by
    apply compositionRecover repack ![joinedScratch] (u.relabel j) ![a.relabel j,b.relabel j] ![joined]
      moved
    intro i
    obtain rfl := Fin.eq_zero i
    exact jv
  have pu := exact_FunctionalRawRepackParser (u.relabel j) joined captured
  exact unionReportOfGraphs permutation (a.relabel j) (b.relabel j) (u.relabel j)
    (sa.relabel j) (sb.relabel j) joined joined ⟨pu,al,bl⟩ written
    (exact_LiteralEquivalenceReflexive B β Δ joined)

#print axioms exact_FunctionalRawUnionReport
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionReportProof
