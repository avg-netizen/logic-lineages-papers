module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consDestruction)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.TableProof
  (internalRowLookup)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairGraph)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable scratchBase scratchStep)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
  (binaryInputsRename tripleInputsRename quadInputsRename)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem selectedReports (a b : OTerm α) :
    ∀ i : Fin 3, Nonempty (Derivation body Γ (programGraph
      ((![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2] : Fin 3 → Program 2) i)
      ((![pairTerm a b,z,z] : Fin 3 → OTerm α) i) ![a,b])) := by
  intro i
  exact Fin.cases (pairGraph a b)
    (Fin.cases (zeroConstantValue ![a,b]) (Fin.cases (zeroConstantValue ![a,b]) (fun k => Fin.elim0 k))) i

theorem exact_OpenSelectedMemoProjection : ExactOpenSelectedMemoProjection := by
  intro R body α Γ out a b
  let parts : Fin 3 → Program 2 := ![NumberedWindowInternalSparsePair.pair,constantZero 2,constantZero 2]
  let values : Fin 3 → OTerm α := ![pairTerm a b,z,z]
  constructor
  · intro h
    exact compositionRecover (scratchRow (constantZero 2) R) parts out ![a,b] values h (selectedReports a b)
  · intro h
    exact compositionValue (scratchRow (constantZero 2) R) parts out ![a,b] values h (selectedReports a b)

private theorem advance (R : Program 4) (out key old next : OTerm α)
    (table : Nonempty (Derivation body Γ (tableAt R old key)))
    (updated : Nonempty (Derivation body Γ (updateAt R out key old)))
    (cons : Nonempty (Derivation body Γ (consGraph next out old))) :
    Nonempty (Derivation body Γ (tableAt R next (suc key))) := by
  have stepGraph : Nonempty (Derivation body Γ
      (programGraph (scratchStep R) next ![key,old,z,z])) := by
    apply compositionValue consCode ![R,.projection 1] next ![key,old,z,z] ![out,old] cons
    intro i
    exact Fin.cases updated
      (Fin.cases (projectionValue (1 : Fin 4) ![key,old,z,z]) (fun k => Fin.elim0 k)) i
  exact recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula (scratchBase (constantZero 2)))
    (OrdinaryArithmetic.graphFormula (scratchStep R)) next key old ![z,z] table stepGraph

private theorem readHead (R : Program 4) (out key tab : OTerm α)
    (table : Nonempty (Derivation body Γ (tableAt R tab key)))
    (head : Nonempty (Derivation body Γ (programGraph headCode out ![tab]))) :
    Nonempty (Derivation body Γ (readRow R out key)) := by
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable (constantZero 2) R)
    out ![key,z,z] ![tab] head
  intro i
  obtain rfl := Fin.eq_zero i
  exact table

theorem exact_OpenSelectedMemoSuccessor : ExactOpenSelectedMemoSuccessor := by
  intro R body α Γ out key old table updated
  apply programCases consCode ![out,old] _
  intro β j Δ next hJ cons
  simp only [readRow,programRename,tripleInputsRename,sucRelabel,zRelabel]
  simp only [binaryInputsRename] at cons
  have table' := renameInto table j Δ hJ
  have updated' := renameInto updated j Δ hJ
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at table'
  simp only [updateAt,programRename,quadInputsRename,zRelabel] at updated'
  obtain ⟨fields⟩ := consDestruction next (out.relabel j) (old.relabel j) cons
  exact readHead R (out.relabel j) (suc (key.relabel j)) next
    (advance R (out.relabel j) (key.relabel j) (old.relabel j) next table' updated' cons)
    ⟨Derivation.conjunctionLeft fields⟩

theorem exact_OpenSelectedMemoLookup : ExactOpenSelectedMemoLookup := by
  intro R body α Γ out key offset old row table
  exact internalRowLookup (constantZero 2) R body α Γ key offset z z out old row table

#print axioms exact_OpenSelectedMemoProjection
#print axioms exact_OpenSelectedMemoSuccessor
#print axioms exact_OpenSelectedMemoLookup

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableChecks
