module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenTableProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue recursionZeroValue programRename)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode headCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consDestruction)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
open NumberedWindowInternalSparseDecodeSyntaxProof (unary)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem takeHead (o i tab : OTerm α)
    (ht : Nonempty (Derivation body Γ (tableGraph tab i)))
    (hh : Nonempty (Derivation body Γ (unary headCode o tab))) :
    Nonempty (Derivation body Γ (rowGraph o i)) := by
  apply compositionValue headCode (fun _ : Fin 1 => scratchTable parserBase parserStep)
    o ![i,z,z] ![tab] hh
  intro j
  obtain rfl := Fin.eq_zero j
  exact ht

private theorem initTable (tab : OTerm α)
    (hc : Nonempty (Derivation body Γ (consGraph tab (suc z) z))) :
    Nonempty (Derivation body Γ (tableGraph tab z)) := by
  apply recursionZeroValue (scratchBase parserBase) (scratchStep parserStep) tab ![z,z]
  apply compositionValue consCode ![parserBase,ID1Completion.InternalAcceptance.constantZero 2]
    tab ![z,z] ![suc z,z] hc
  intro i
  exact Fin.cases (oneConstantValue ![z,z])
    (Fin.cases (zeroConstantValue ![z,z]) (fun k => Fin.elim0 k)) i

private theorem advance (o i old next : OTerm α)
    (ht : Nonempty (Derivation body Γ (tableGraph old i)))
    (hr : Nonempty (Derivation body Γ (stepGraph o i old)))
    (hc : Nonempty (Derivation body Γ (consGraph next o old))) :
    Nonempty (Derivation body Γ (tableGraph next (suc i))) := by
  have hStep : Nonempty (Derivation body Γ
      (programGraph (scratchStep parserStep) next ![i,old,z,z])) := by
    apply compositionValue consCode ![parserStep,.projection 1] next ![i,old,z,z] ![o,old] hc
    intro j
    exact Fin.cases hr
      (Fin.cases (projectionValue (1 : Fin 4) ![i,old,z,z]) (fun k => Fin.elim0 k)) j
  exact recursionSuccessorIntroduction Γ
    (OrdinaryArithmetic.graphFormula (scratchBase parserBase))
    (OrdinaryArithmetic.graphFormula (scratchStep parserStep)) next i old ![z,z] ht hStep

theorem rowNil : Nonempty (Derivation body Γ (rowGraph (suc (z : OTerm α)) z)) := by
  apply programCases consCode ![suc z,z] _
  intro β j Δ tab _ hc
  simp only [rowRename,sucRelabel,zRelabel]
  simp only [binaryInputsRename,sucRelabel,zRelabel] at hc
  obtain ⟨unpacked⟩ := consDestruction tab (suc z) z hc
  exact takeHead (suc z) z tab (initTable tab hc) ⟨Derivation.conjunctionLeft unpacked⟩

theorem rowFromStep (o i old : OTerm α)
    (ht : Nonempty (Derivation body Γ (tableGraph old i)))
    (hr : Nonempty (Derivation body Γ (stepGraph o i old))) :
    Nonempty (Derivation body Γ (rowGraph o (suc i))) := by
  apply programCases consCode ![o,old] _
  intro β j Δ next hJ hc
  simp only [rowRename,sucRelabel]
  simp only [binaryInputsRename] at hc
  have table := renameInto ht j Δ hJ
  have step := renameInto hr j Δ hJ
  rw [tableRename] at table
  rw [stepRename] at step
  obtain ⟨unpacked⟩ := consDestruction next (o.relabel j) (old.relabel j) hc
  exact takeHead (o.relabel j) (suc (i.relabel j)) next
    (advance (o.relabel j) (i.relabel j) (old.relabel j) next table step hc)
    ⟨Derivation.conjunctionLeft unpacked⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenTableProof
