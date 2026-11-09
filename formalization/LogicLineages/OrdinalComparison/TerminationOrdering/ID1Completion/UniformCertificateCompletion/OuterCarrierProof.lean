module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationStepPeelSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalGraphCompositionSyntaxProof GuardedSourceSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- The raw scalar checker is the LITERAL RawScalar checker of the SAME
tuple used by typedness. Object coordinates are bound by original totality,
so neither a Gamma decoder nor a parameter witness is added to the rule. -/
theorem typedCarrier (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (tau : Ty) (object : OTerm α)
    (ht : Nonempty (Derivation body Delta
      (typed (Outer.computability oldComp data window oldVertex oldResult) tau (numeral context) object))) :
    Nonempty (Derivation body Delta
      (carrier (Outer.source oldSrc oldComp data
        (SourceComputabilityCompletion.RawScalar.checker data) oldStep bottom measure window)
        false context object)) := by
  let src := Outer.source oldSrc oldComp data
    (SourceComputabilityCompletion.RawScalar.checker data) oldStep bottom measure window
  let comp := Outer.computability oldComp data window oldVertex oldResult
  rw [OuterCarrierSupportProof.carrierGraph]
  change Nonempty (Derivation body Delta
    (graph2 (Outer.scalar (SourceComputabilityCompletion.RawScalar.checker data) window oldSrc.scalar)
      (suc z) (numeral context) object))
  apply OuterCarrierSupportProof.objectCases context object _
  intro β j gammaCode payload parameter Theta hj hg hr hp
  rw [graph2Rename]
  simp only [numeralRename,sucRelabel,zRelabel]
  have ht' := renameInto ht j Theta hj
  rw [typedRename] at ht'
  simp only [numeralRename] at ht'
  have hwindow := GuardedSourceCertificateProof.windowNumeral
    (body := body) (Gamma := Theta) (α := β) window context hw
  have rawTyped := OuterCarrierSupportProof.typedRecover oldComp data window oldVertex oldResult
    context (numeral (typeNumber tau)) (object.relabel j) gammaCode payload parameter
    hwindow hg hr hp ht'
  have rawScalar := SourceComputabilityCompletion.RawScalarInternalProof.typedScalar
    data payload (numeral (typeNumber tau)) parameter rawTyped
  exact OuterCarrierSupportProof.scalarAccept
    (SourceComputabilityCompletion.RawScalar.checker data) oldSrc.scalar window context
    (object.relabel j) gammaCode payload parameter hwindow hg hr hp rawScalar

theorem typedCarrierRule (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1) (α : Type) (tau : Ty) (object : OTerm α) :
    let src := Outer.source oldSrc oldComp data
      (SourceComputabilityCompletion.RawScalar.checker data) oldStep bottom measure window
    let comp := Outer.computability oldComp data window oldVertex oldResult
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      ((typed comp tau (numeral context) object).imp (carrier src false context object))) := by
  let src := Outer.source oldSrc oldComp data
    (SourceComputabilityCompletion.RawScalar.checker data) oldStep bottom measure window
  let comp := Outer.computability oldComp data window oldVertex oldResult
  let P := typed comp tau (numeral context) object
  have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := typedCarrier oldSrc oldComp data oldStep bottom measure window
    oldVertex oldResult context hw tau object hp
  exact ⟨Derivation.implicationIntroduction d⟩

theorem domainCarrier (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (oldStep : Program 4) (bottom measure window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1) :
    SourceComputabilityCompletion.InverseApplication.DomainCarrier
      (Outer.source oldSrc oldComp data (SourceComputabilityCompletion.RawScalar.checker data)
        oldStep bottom measure window)
      (Outer.computability oldComp data window oldVertex oldResult) context := by
  intro α sigma tau f a
  let src := Outer.source oldSrc oldComp data
    (SourceComputabilityCompletion.RawScalar.checker data) oldStep bottom measure window
  let comp := Outer.computability oldComp data window oldVertex oldResult
  let P := domain comp context sigma tau f a
  have hp : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P] P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := typedCarrier oldSrc oldComp data oldStep bottom measure window
    oldVertex oldResult context hw (.arrow sigma tau) f (andLeft (andLeft hp))
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierProof
