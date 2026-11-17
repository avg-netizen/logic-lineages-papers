module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.SignatureCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (refl)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def countQuery (n : Nat) (arity : Fin n → Nat) : Program 1 :=
  .composition InternalRawListRecursion.lookup ![InternalUnpair.right,constant 1 (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))]
def argsQuery (n : Nat) (arity : Fin n → Nat) : Program 1 := .composition groundList (fun _ => countQuery n arity)
def queries (n : Nat) (arity : Fin n → Nat) : Fin 4 → Program 1 :=
  ![InternalUnpair.right,countQuery n arity,argsQuery n arity,pairOf (constant 1 0) (argsQuery n arity)]

theorem cases (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (htag : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 5) raw)))
    (hvalid : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) raw)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count args packed : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 groundList args count)) →
      Nonempty (Derivation body Theta (graph1 (signature n arity) (suc packed) (raw.relabel j))) →
      Nonempty (Derivation body Theta (OriginalTypedDecoderStepSpecification.StepArrowFields (suc packed) z args)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n arity) ![raw] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  have htag' := renameInto htag j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htag'
  have hv' := renameInto hvalid j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hv'
  have hp := reconstructPair (raw.relabel j) (numeral 5) (ys 0) htag' (hq 0)
  have hvb := (OriginalHeadDecoderValidity.SupportProof.tagFactor n (5 : Fin 6) (raw.relabel j)
    (numeral 5) (ys 0) (suc z) hp ⟨refl _⟩).mp hv'
  have hbound := (OriginalHeadDecoderValidity.SupportProof.rankedFactor n (raw.relabel j) (ys 0) (hq 0)).mp hvb
  have hl := binaryRecover InternalRawListRecursion.lookup InternalUnpair.right
    (constant 1 (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))) (ys 1) (ys 0)
    (numeral (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))) ![raw.relabel j] (hq 1) (hq 0)
    (constantValue (NumberedMultisetNumeric.numbersNumber (List.ofFn arity)) ![raw.relabel j])
  have ha := unaryRecover groundList (countQuery n arity) (ys 2) (ys 1) ![raw.relabel j] (hq 2) (hq 1)
  have hk := binaryRecover InternalPairing.pairing (constant 1 0) (argsQuery n arity)
    (ys 3) z (ys 2) ![raw.relabel j] (hq 3) (constantValue 0 ![raw.relabel j]) (hq 2)
  have hs := (Continuation20261117.OriginalConcreteSignatureEquations.Proof.rankedSignature n arity body beta Theta
    (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (suc (ys 3)) hp hbound hl ha hk).mpr ⟨refl _⟩
  have hf := OriginalTypedDecoderInternalScalarSyntaxProof.stepArrowFieldsIntro (suc (ys 3)) z (ys 2) (ys 3)
    (InternalEqualityTestPredecessorProof.predecessorSuccessor (ys 3)) hk
  exact next beta j Theta (ys 1) (ys 2) (ys 3) hj ha hs hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.SignatureCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.SignatureCasesProof
