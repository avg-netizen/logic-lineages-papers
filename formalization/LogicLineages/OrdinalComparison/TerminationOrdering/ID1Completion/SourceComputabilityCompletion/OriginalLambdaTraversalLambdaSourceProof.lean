module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalQuotientComparisonProof (orLeft)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalTransparentLambdaFinal OriginalTransparentLambdaValidityInternal
open OriginalLambdaTraversalLambdaStateProof OriginalLambdaTraversalLambdaSelectorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A one output in the original full-output Boolean equation has only its
acceptance branch. The zero branch is refuted by internal arithmetic. -/
theorem booleanOneRecover (A : Formula alpha)
    (h : Nonempty (Derivation body Delta (BooleanOutput (numeral 1) A))) :
    Nonempty (Derivation body Delta A) := by
  let L := equal (numeral 1 : OTerm alpha) (numeral 1) ⊓ A
  let R := equal (numeral 1 : OTerm alpha) z ⊓ A.not
  have hl : Derivation body (L :: Delta) A :=
    Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
  have hr : Derivation body (R :: Delta) A := by
    have hh : Derivation body (R :: Delta) R := Derivation.hypothesis List.mem_cons_self
    have he : Derivation body (R :: Delta) (eqn (suc z) z) := by
      simpa only [R,equalEqn,numeral] using Derivation.conjunctionLeft hh
    exact Derivation.explosion (zeroNeSuc (symm he))
  obtain ⟨h⟩ := h
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction hr)⟩

theorem sourceAccepted (data : Data) (law : SourceLambdaLaw data)
    (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (TagIs 1 raw)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity data) (numeral 1) raw parameter))) :
    Nonempty (Derivation body Delta (FinalSourceLambdaFactors data raw parameter)) := by
  obtain ⟨hl⟩ := law body alpha Delta (numeral 1) raw parameter
  obtain ⟨ht⟩ := ht
  obtain ⟨hs⟩ := hs
  exact booleanOneRecover _ ⟨Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination hl ht)) hs⟩

theorem sourceFromFactors (data : Data) (law : SourceLambdaLaw data)
    (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (TagIs 1 raw)))
    (hf : Nonempty (Derivation body Delta (FinalSourceLambdaFactors data raw parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity data) (numeral 1) raw parameter)) := by
  obtain ⟨hl⟩ := law body alpha Delta (numeral 1) raw parameter
  obtain ⟨ht⟩ := ht
  obtain ⟨hf⟩ := hf
  have he : Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1)) := by
    rw [equalEqn]
    exact refl _
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination hl ht))
    (orLeft (Derivation.conjunctionIntroduction he hf))⟩

/-- The requested SAME selected source accepts the actual traversal child.
Its source and type are conclusions from parent acceptance and literal fields. -/
theorem sourceChild (rawData : Data) (window : Program 1)
    (raw d e child parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) raw parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) child bodyParameter ⊓ graph1 InternalUnpair.left e child)) := by
  have ht := andLeft hf
  have he := andLeft (andRight (andRight hf))
  have hb := andLeft (andRight (andRight (andRight hf)))
  have hp := andRight (andRight (andRight (andRight hf)))
  have hsource := sourceAccepted (leafData rawData window)
    (OriginalLambdaTraversalSelectionValidityProof.leafSourceLambda rawData window)
    raw parameter ht hs
  exact andIntro
    (finalChildAtSelectors _ raw e child parameter bodyParameter he hb hp (andRight hsource))
    (bodyType raw e child he hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSourceProof
