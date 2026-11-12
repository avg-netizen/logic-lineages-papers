module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalStructuralNodeSizeInternalErasureDefinitions OriginalStructuralNodeSizeInternalErasureBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem countCases {n : Nat} (xs : Fin n → OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (ys : Fin n → OTerm beta),
      (∀ r ∈ Delta, r.relabel rho ∈ Theta) →
      (∀ i, Nonempty (Derivation body Theta (graph1 OriginalStructuralNodeSize.raw (ys i) ((xs i).relabel rho)))) →
      Nonempty (Derivation body Theta (psi.relabel rho))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin n → Program n := fun i => .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => .projection i)
  apply queryCases qs xs psi
  intro beta rho ys Theta hrho hq
  apply step beta rho Theta ys hrho
  intro i
  exact unaryRecover OriginalStructuralNodeSize.raw (.projection i) (ys i) ((xs i).relabel rho)
    (fun j => (xs j).relabel rho) (hq i) (projectionValue i _)

theorem childCount (input child d k erased before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased d k child)))
    (hb : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before child)))
    (ha : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw after erased))) :
    Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before erased)) := by
  have hh := belowRawApply input child d k erased before after hi hlt (andIntro he (andIntro hb ha))
  have heq : Nonempty (Derivation body Delta (eqn before after)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using hh
  obtain ⟨heq⟩ := heq
  exact outputTransport OriginalStructuralNodeSize.raw after before (Fin.cons erased Fin.elim0) ⟨symm heq⟩ ha

theorem sharedCount (input erased before after common : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before input)))
    (ha : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw after erased)))
    (hcb : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw common input)))
    (hca : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw common erased))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  obtain ⟨hb⟩ := valueUnique OriginalStructuralNodeSize.raw before common (Fin.cons input Fin.elim0) hb hcb
  obtain ⟨ha⟩ := valueUnique OriginalStructuralNodeSize.raw after common (Fin.cons erased Fin.elim0) ha hca
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
    (show Nonempty (Derivation body Delta (eqn before after)) from ⟨trans hb (symm ha)⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureSupportProof
