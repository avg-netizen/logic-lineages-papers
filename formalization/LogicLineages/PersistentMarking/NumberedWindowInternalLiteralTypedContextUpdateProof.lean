module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextMemoProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextUpdateProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consDestruction)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable scratchBase scratchStep)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
  (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalLiteralTypedContextMemoProof
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def contextUpdate {α : Type} (R : Program 4) (out ctx key old : OTerm α) : Formula α :=
  programGraph R out ![key,old,ctx,z]

private theorem advance (R : Program 4) (out ctx key old next : OTerm α)
    (table : D B Γ (contextualTable R old ctx key))
    (updated : D B Γ (contextUpdate R out ctx key old))
    (cons : D B Γ (consGraph next out old)) :
    D B Γ (contextualTable R next ctx (suc key)) := by
  have stepGraph : D B Γ (programGraph (scratchStep R) next ![key,old,ctx,z]) := by
    apply compositionValue consCode ![R,.projection 1] next ![key,old,ctx,z] ![out,old] cons
    intro i
    exact Fin.cases updated
      (Fin.cases (projectionValue (1 : Fin 4) ![key,old,ctx,z]) (fun j => Fin.elim0 j)) i
  exact recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula (scratchBase (constantZero 2)))
    (OrdinaryArithmetic.graphFormula (scratchStep R)) next key old ![ctx,z] table stepGraph

private theorem readHead (R : Program 4) (out ctx key tab : OTerm α)
    (table : D B Γ (contextualTable R tab ctx key))
    (head : D B Γ (programGraph headCode out ![tab])) :
    D B Γ (contextualRow R out ctx key) := by
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable (constantZero 2) R)
    out ![key,ctx,z] ![tab] head
  intro i
  obtain rfl := Fin.eq_zero i
  exact table

/-- Compare the selected next row with the step on the actual previous
scratch table. Both directions use the same contextual table value. -/
theorem exact_OpenContextMemoUpdate (R : Program 4) (out ctx key old : OTerm α)
    (table : D B Γ (contextualTable R old ctx key)) :
    D B Γ (contextUpdate R out ctx key old) ↔ D B Γ (contextualRow R out ctx (suc key)) := by
  have put : ∀ (β : Type) (Δ : List (Formula β)) (v c k t : OTerm β),
      D B Δ (contextualTable R t c k) → D B Δ (contextUpdate R v c k t) →
      D B Δ (contextualRow R v c (suc k)) := by
    intro β Δ v c k t tab update
    apply programCases consCode ![v,t] _
    intro γ n Θ next stay pack
    simp only [contextualRow,programRename,tripleInputsRename,sucRelabel,zRelabel]
    simp only [binaryInputsRename] at pack
    have oldTab := renameInto tab n Θ stay
    have step := renameInto update n Θ stay
    simp only [contextualTable,programRename,tripleInputsRename,zRelabel] at oldTab
    simp only [contextUpdate,programRename,quadInputsRename,zRelabel] at step
    obtain ⟨fields⟩ := consDestruction next (v.relabel n) (t.relabel n) pack
    exact readHead R (v.relabel n) (c.relabel n) (suc (k.relabel n)) next
      (advance R (v.relabel n) (c.relabel n) (k.relabel n) (t.relabel n) next oldTab step pack)
      ⟨Derivation.conjunctionLeft fields⟩
  constructor
  · exact put α Γ out ctx key old table
  · intro row
    apply programCases R ![key,old,ctx,z] _
    intro β j Δ value keep step
    simp only [contextUpdate,programRename,quadInputsRename,zRelabel]
    simp only [quadInputsRename,zRelabel] at step
    have tab := renameInto table j Δ keep
    have result := renameInto row j Δ keep
    simp only [contextualTable,programRename,tripleInputsRename,zRelabel] at tab
    simp only [contextualRow,programRename,tripleInputsRename,sucRelabel,zRelabel] at result
    let c := ctx.relabel j
    let k := key.relabel j
    let t := old.relabel j
    have predicted := put β Δ value c k t tab step
    have eq := valueUnique (scratchRow (constantZero 2) R) value (out.relabel j) ![suc k,c,z]
      predicted result
    exact outputTransport R value (out.relabel j) ![k,t,c,z] eq step

#print axioms exact_OpenContextMemoUpdate
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedContextUpdateProof
