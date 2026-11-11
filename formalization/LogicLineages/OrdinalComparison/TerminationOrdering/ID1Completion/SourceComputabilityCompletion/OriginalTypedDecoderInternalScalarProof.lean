module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairLeftValue {n : Nat} (p : Program n) (code left right : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hq : Nonempty (Derivation body Delta (StepPair code left right))) :
    Nonempty (Derivation body Delta (programGraph (leftOf p) left xs)) :=
  unaryValue InternalUnpair.left p left code xs (pairLeft code left right hq) hp

theorem pairRightValue {n : Nat} (p : Program n) (code left right : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hq : Nonempty (Derivation body Delta (StepPair code left right))) :
    Nonempty (Derivation body Delta (programGraph (rightOf p) right xs)) :=
  unaryValue InternalUnpair.right p right code xs (pairRight code left right hq) hp

theorem pairFields {n : Nat} (p : Program n) (code left right : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hl : Nonempty (Derivation body Delta (programGraph (leftOf p) left xs)))
    (hr : Nonempty (Derivation body Delta (programGraph (rightOf p) right xs))) :
    Nonempty (Derivation body Delta (StepPair code left right)) :=
  reconstructPair code left right
    (unaryRecover InternalUnpair.left p left code xs hl hp)
    (unaryRecover InternalUnpair.right p right code xs hr hp)

/-- Original predecessor and pair inversion connect the independently opened
fields to the actual nested head selector, at arbitrary raw codes. -/
theorem headValue {n : Nat} (p : Program n) (code domain codomain : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields code domain codomain))) :
    Nonempty (Derivation body Delta (programGraph (headOf p) domain xs)) := by
  apply stepArrowFieldsCases code domain codomain _ hf
  intro beta j Theta previous hj hpred hpair
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun i => (xs i).relabel j
  have hinner := unaryValue InternalEqualityTest.predecessor p previous (code.relabel j) xx hpred hp'
  exact unaryValue InternalUnpair.left (predecessorOf p) (domain.relabel j) previous xx
    (pairLeft previous (domain.relabel j) (codomain.relabel j) hpair) hinner

theorem tailValue {n : Nat} (p : Program n) (code domain codomain : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields code domain codomain))) :
    Nonempty (Derivation body Delta (programGraph (tailOf p) codomain xs)) := by
  apply stepArrowFieldsCases code domain codomain _ hf
  intro beta j Theta previous hj hpred hpair
  rw [programRename]
  have hp' := renameInto hp j Theta hj
  rw [programRename] at hp'
  let xx := fun i => (xs i).relabel j
  have hinner := unaryValue InternalEqualityTest.predecessor p previous (code.relabel j) xx hpred hp'
  exact unaryValue InternalUnpair.right (predecessorOf p) (codomain.relabel j) previous xx
    (pairRight previous (domain.relabel j) (codomain.relabel j) hpair) hinner

/-- The converse uses actual selector graphs and internal predecessor totality.
It supplies the existential predecessor rather than assuming a decomposition. -/
theorem arrowFields {n : Nat} (p : Program n) (code domain codomain : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p code xs)))
    (hl : Nonempty (Derivation body Delta (programGraph (headOf p) domain xs)))
    (hr : Nonempty (Derivation body Delta (programGraph (tailOf p) codomain xs))) :
    Nonempty (Derivation body Delta (StepArrowFields code domain codomain)) := by
  apply programCases InternalEqualityTest.predecessor (Fin.cons code Fin.elim0) _
  intro beta j Theta previous hj hpred
  rw [stepArrowFieldsRename]
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [programRename] at hp' hl' hr'
  simp only [consTermRename,emptyRename] at hpred
  let xx := fun i => (xs i).relabel j
  have hinner := unaryValue InternalEqualityTest.predecessor p previous (code.relabel j) xx hpred hp'
  have hleft := unaryRecover InternalUnpair.left (predecessorOf p)
    (domain.relabel j) previous xx hl' hinner
  have hright := unaryRecover InternalUnpair.right (predecessorOf p)
    (codomain.relabel j) previous xx hr' hinner
  exact stepArrowFieldsIntro _ _ _ previous hpred
    (reconstructPair previous (domain.relabel j) (codomain.relabel j) hleft hright)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
