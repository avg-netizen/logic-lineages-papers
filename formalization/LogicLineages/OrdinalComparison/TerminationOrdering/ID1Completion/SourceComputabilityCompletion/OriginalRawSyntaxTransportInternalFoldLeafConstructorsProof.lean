module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof OriginalRawSyntaxTransportInternalConstructorLeafProof
open OriginalRawSyntaxTransportInternalFoldLeafProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableForward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (graph3 (variableAction mode) out d k i)) :=
  variableActionBackward mode raw out d k i hr
    (leafForward mode d k raw out (variableArity (.projection 0) raw i ![raw] (projectionValue 0 ![raw]) hr) ho)

theorem variableBackward (mode : Mode) (raw out d k i : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph1 variableConstructor raw i)))
    (ho : Nonempty (Derivation positive Delta (graph3 (variableAction mode) out d k i))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  leafBackward mode d k raw out (variableArity (.projection 0) raw i ![raw] (projectionValue 0 ![raw]) hr)
    (variableActionForward mode raw out d k i hr ho)

theorem actualRawSyntaxInternalVariable : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalVariable := by
  intro positive mode alpha Delta raw out d k i
  let C := graph1 variableConstructor raw i
  let G := graph3 (fold mode) out d k raw
  let R := graph3 (variableAction mode) out d k i
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := variableForward mode raw out d k i hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := variableBackward mode raw out d k i hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem unchangedForward (mode : Mode) (raw out d k tag : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z raw)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation positive Delta (equal tag z).not))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw)) :=
  nonzeroLeafForward mode out d k raw tag ht hn (leafForward mode d k raw out ha ho)

theorem unchangedBackward (mode : Mode) (raw out d k tag : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) z raw)))
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag tag raw)))
    (hn : Nonempty (Derivation positive Delta (equal tag z).not))
    (ho : Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  leafBackward mode d k raw out ha (nonzeroLeafBackward mode out d k raw tag ht hn ho)

theorem bottomForward (mode : Mode) (raw out d k tau : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph1 bottomConstructor raw tau)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw)) :=
  unchangedForward mode raw out d k (numeral 3)
    (bottomArity (.projection 0) raw tau ![raw] (projectionValue 0 ![raw]) hr)
    (pairLeft raw (numeral 3) tau (bottomConstructorPair raw tau hr)) (numeralNe 3 0 (by decide)) ho

theorem bottomBackward (mode : Mode) (raw out d k tau : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph1 bottomConstructor raw tau)))
    (ho : Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unchangedBackward mode raw out d k (numeral 3)
    (bottomArity (.projection 0) raw tau ![raw] (projectionValue 0 ![raw]) hr)
    (pairLeft raw (numeral 3) tau (bottomConstructorPair raw tau hr)) (numeralNe 3 0 (by decide)) ho

theorem actualRawSyntaxInternalBottom : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalBottom := by
  intro positive mode alpha Delta raw out d k tau
  let C := graph1 bottomConstructor raw tau
  let G := graph3 (fold mode) out d k raw
  let R := UnchangedLeafResult mode out raw
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := bottomForward mode raw out d k tau hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := bottomBackward mode raw out d k tau hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem nilRawTag (raw : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation positive Delta (graph1 rawTag (numeral 6) raw)) :=
  unaryRecover InternalUnpair.left (.projection 0) (numeral 6) raw ![raw]
    (nilTag (.projection 0) raw ![raw] (projectionValue 0 ![raw]) hr) (projectionValue 0 ![raw])

theorem nilForward (mode : Mode) (raw out d k : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw))) :
    Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw)) :=
  unchangedForward mode raw out d k (numeral 6)
    (nilArity (.projection 0) raw ![raw] (projectionValue 0 ![raw]) hr)
    (nilRawTag raw hr) (numeralNe 6 0 (by decide)) ho

theorem nilBackward (mode : Mode) (raw out d k : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation positive Delta (UnchangedLeafResult mode out raw))) :
    Nonempty (Derivation positive Delta (graph3 (fold mode) out d k raw)) :=
  unchangedBackward mode raw out d k (numeral 6)
    (nilArity (.projection 0) raw ![raw] (projectionValue 0 ![raw]) hr)
    (nilRawTag raw hr) (numeralNe 6 0 (by decide)) ho

theorem actualRawSyntaxInternalNil : OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalNil := by
  intro positive mode alpha Delta raw out d k
  let C := programGraph nilConstructor raw Fin.elim0
  let G := graph3 (fold mode) out d k raw
  let R := UnchangedLeafResult mode out raw
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := nilForward mode raw out d k hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := nilBackward mode raw out d k hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
