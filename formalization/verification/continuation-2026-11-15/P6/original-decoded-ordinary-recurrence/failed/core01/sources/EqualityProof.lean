module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def test (P Q : Program 1) : Program 2 :=
  OriginalRawSyntaxTransport.sameOf (.composition P (fun _ : Fin 1 => .projection 0))
    (.composition Q (fun _ : Fin 1 => .projection 1))

theorem recover (P Q : Program 1) (left right x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 P x left)))
    (hq : Nonempty (Derivation body Delta (graph1 Q y right)))
    (h : Nonempty (Derivation body Delta (graph2 (test P Q) (numeral 1) left right))) :
    Nonempty (Derivation body Delta (eqn x y)) := by
  have hl := unaryValue P (.projection 0) x left ![left,right] hp (projectionValue 0 ![left,right])
  have hr := unaryValue Q (.projection 1) y right ![left,right] hq (projectionValue 1 ![left,right])
  exact InternalEqualityTestProof.equalityOfAcceptance x y
    (binaryRecover InternalEqualityTest.equalityTest (.composition P (fun _ : Fin 1 => .projection 0))
      (.composition Q (fun _ : Fin 1 => .projection 1)) (numeral 1) x y ![left,right] h hl hr)

theorem introduce (P Q : Program 1) (left right x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 P x left)))
    (hq : Nonempty (Derivation body Delta (graph1 Q y right)))
    (h : Nonempty (Derivation body Delta (eqn x y))) :
    Nonempty (Derivation body Delta (graph2 (test P Q) (numeral 1) left right)) := by
  have hl := unaryValue P (.projection 0) x left ![left,right] hp (projectionValue 0 ![left,right])
  have hr := unaryValue Q (.projection 1) y right ![left,right] hq (projectionValue 1 ![left,right])
  exact binaryValue InternalEqualityTest.equalityTest (.composition P (fun _ : Fin 1 => .projection 0))
    (.composition Q (fun _ : Fin 1 => .projection 1)) (numeral 1) x y ![left,right]
    (InternalEqualityTestCompositionProof.equalityOfEqual x y h) hl hr

theorem forward (P Q : Program 1) (left right x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 P x left)))
    (hq : Nonempty (Derivation body Delta (graph1 Q y right))) :
    Nonempty (Derivation body Delta ((eqn x y).imp (graph2 (test P Q) (numeral 1) left right))) := by
  let A := eqn x y
  obtain ⟨h⟩ := introduce P Q left right x y (withHyp hp A) (withHyp hq A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem backward (P Q : Program 1) (left right x y : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 P x left)))
    (hq : Nonempty (Derivation body Delta (graph1 Q y right))) :
    Nonempty (Derivation body Delta ((graph2 (test P Q) (numeral 1) left right).imp (eqn x y))) := by
  let A := graph2 (test P Q) (numeral 1) left right
  obtain ⟨h⟩ := recover P Q left right x y (withHyp hp A) (withHyp hq A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.EqualityProof
