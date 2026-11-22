module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellHead cellGood)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverLexicalSlotTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem sameDrop (i ctx ty rest : OTerm α)
    (found : Nonempty (Derivation body Γ (programGraph dropContext rest ![i,ctx]))) :
    Nonempty (Derivation body Γ (programGraph dropped rest ![i,ctx,ty])) := by
  let xs : Fin 3 → OTerm α := ![i,ctx,ty]
  apply compositionValue dropContext (fun j : Fin 2 => Program.projection ((![0,1] : Fin 2 → Fin 3) j))
    rest xs ![i,ctx] found
  intro j
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k)) j

private theorem slotCell (i ctx ty rest : OTerm α)
    (hit : Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])))
    (dropReport : Nonempty (Derivation body Γ (programGraph dropContext rest ![i,ctx]))) :
    Nonempty (Derivation body Γ (unary cellGood (suc z) rest)) := by
  let xs : Fin 3 → OTerm α := ![i,ctx,ty]
  obtain ⟨ok⟩ := conjunctionRecover inhabited (binary equalityTest atType (.projection 2)) xs hit
  apply compositionRecover cellGood (fun _ : Fin 1 => dropped) (suc z) xs ![rest]
    ⟨Derivation.conjunctionLeft ok⟩
  intro j
  obtain rfl := Fin.eq_zero j
  exact sameDrop i ctx ty rest dropReport

private theorem slotHead (i ctx ty rest reported : OTerm α)
    (hit : Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty])))
    (dropReport : Nonempty (Derivation body Γ (programGraph dropContext rest ![i,ctx])))
    (head : Nonempty (Derivation body Γ (unary cellHead reported rest))) :
    Nonempty (Derivation body Γ (unary cellHead ty rest)) := by
  let xs : Fin 3 → OTerm α := ![i,ctx,ty]
  obtain ⟨ok⟩ := conjunctionRecover inhabited (binary equalityTest atType (.projection 2)) xs hit
  have headAt : Nonempty (Derivation body Γ (programGraph atType reported xs)) := by
    apply compositionValue cellHead (fun _ : Fin 1 => dropped) reported xs ![rest] head
    intro j
    obtain rfl := Fin.eq_zero j
    exact sameDrop i ctx ty rest dropReport
  have equal : Nonempty (Derivation body Γ (programGraph equalityTest (suc z) ![reported,ty])) := by
    apply compositionRecover equalityTest ![atType,.projection 2] (suc z) xs ![reported,ty]
      ⟨Derivation.conjunctionRight ok⟩
    intro j
    exact Fin.cases headAt (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k)) j
  exact outputTransport cellHead reported ty ![rest] (equalityOfAcceptance reported ty equal) head

theorem exact_OpenCoverPhysicalLexicalSlot : ExactOpenCoverPhysicalLexicalSlot := by
  intro body α Γ i ctx ty Q hit next
  apply programCases dropContext ![i,ctx] Q
  intro β j Δ rest keep dropReport
  simp only [binaryInputsRename] at dropReport
  have hit' := renameInto hit j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at hit'
  apply programCases cellHead ![rest] (Q.relabel j)
  intro γ k Ξ actual keep' head
  rw [unaryRename] at head
  have hit'' := renameInto hit' k Ξ keep'
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at hit''
  have drop' := renameInto dropReport k Ξ keep'
  simp only [programRename,binaryInputsRename] at drop'
  have cell := slotCell ((i.relabel j).relabel k) ((ctx.relabel j).relabel k)
    ((ty.relabel j).relabel k) (rest.relabel k) hit'' drop'
  have selected := slotHead ((i.relabel j).relabel k) ((ctx.relabel j).relabel k)
    ((ty.relabel j).relabel k) (rest.relabel k) actual hit'' drop' head
  have retain : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact keep' (f.relabel j) (keep f hf)
  have reports : SlotReports body Ξ (i.relabel (k ∘ j)) (ctx.relabel (k ∘ j))
      (ty.relabel (k ∘ j)) (rest.relabel k) := by
    simpa only [Term.relabel_relabel] using
      (show SlotReports body Ξ ((i.relabel j).relabel k) ((ctx.relabel j).relabel k)
        ((ty.relabel j).relabel k) (rest.relabel k) from ⟨drop',cell,selected⟩)
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ (rest.relabel k) retain reports

#print axioms exact_OpenCoverPhysicalLexicalSlot

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotOpenProof
