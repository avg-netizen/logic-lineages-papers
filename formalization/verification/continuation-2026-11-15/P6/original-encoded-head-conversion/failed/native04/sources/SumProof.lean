module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.EvenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open SplitInductionDefinitions
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem outputs (raw state q r : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 split state raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state q r))) :
    Nonempty (Derivation body Delta (graph1 half q raw ⊓ graph1 bit r raw)) :=
  andIntro (unaryValue InternalUnpair.left split q state ![raw] (pairLeft state q r hp) hs)
    (unaryValue InternalUnpair.right split r state ![raw] (pairRight state q r hp) hs)

theorem evenOutputs (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (graph1 half raw (double raw) ⊓ graph1 bit z (double raw))) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing (Fin.cons raw (Fin.cons z Fin.elim0)) _
  intro beta j Theta state hj hp
  simp only [consTermRename,InternalControlGraphSupportProof.emptyRename,zRelabel] at hp
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename,
    double,InternalOriginalOrderSyntaxProof.addRelabel,zRelabel]
  exact outputs (double (raw.relabel j)) state (raw.relabel j) z (EvenProof.evenGraph _ _ hp) hp

theorem oddOutputs (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (graph1 half raw (suc (double raw)) ⊓ graph1 bit (suc z) (suc (double raw)))) := by
  let qs : Fin 2 → Program 1 := ![pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0),
    pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 1)]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename,
    double,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel,zRelabel]
  have hq0 := hq 0
  have hq1 := hq 1
  simp only [consTermRename,InternalControlGraphSupportProof.emptyRename] at hq0 hq1
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have h0 := binaryRecover InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)
    (ys 0) (raw.relabel j) z xs hq0 (projectionValue 0 xs) (constantValue 0 xs)
  have h1 := binaryRecover InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 1 1)
    (ys 1) (raw.relabel j) (suc z) xs hq1 (projectionValue 0 xs) (constantValue 1 xs)
  have he := EvenProof.evenGraph (raw.relabel j) (ys 0) h0
  have ho := StepProof.splitSuccessor (double (raw.relabel j)) (ys 0) (ys 1) he
    (StepProof.advanceZero (double (raw.relabel j)) (ys 0) (ys 1) (raw.relabel j) h0 h1)
  exact outputs (suc (double (raw.relabel j))) (ys 1) (raw.relabel j) (suc z) ho h1

theorem leftValue (left right : Program 1) (raw out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 left out raw))) :
    Nonempty (Derivation body Delta (graph1 (sumCase left right) out (double raw))) := by
  have hs := evenOutputs (body := body) (Delta := Delta) raw
  have hv := unaryValue left half out raw ![double raw] h (andLeft hs)
  exact zeroBranchIntro bit (.composition left (fun _ : Fin 1 => half))
    (.composition right (fun _ : Fin 1 => half)) out ![double raw] (andRight hs) hv

theorem rightValue (left right : Program 1) (raw out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 right out raw))) :
    Nonempty (Derivation body Delta (graph1 (sumCase left right) out (suc (double raw)))) := by
  have hs := oddOutputs (body := body) (Delta := Delta) raw
  have hv := unaryValue right half out raw ![suc (double raw)] h (andLeft hs)
  exact successorBranchIntro bit (.composition left (fun _ : Fin 1 => half))
    (.composition right (fun _ : Fin 1 => half)) out z ![suc (double raw)] (andRight hs) hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SumProof
