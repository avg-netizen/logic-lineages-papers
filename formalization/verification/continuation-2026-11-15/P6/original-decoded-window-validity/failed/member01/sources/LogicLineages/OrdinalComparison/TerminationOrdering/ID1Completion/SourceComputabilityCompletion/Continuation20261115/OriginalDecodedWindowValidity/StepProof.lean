module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalAcceptanceConjunctionProof
open OriginalRawSyntaxTransport

theorem nilAccept (n : Nat) : Nonempty (Derivation body Delta (graph1 (symbols n) (numeral 1) z)) :=
  InternalRawListRecursionProof.nilValue (InternalLessThan.constantOne 0) (symbolStep n)
    (numeral 1) Fin.elim0 (InternalLessThanSupportProof.oneConstantValue Fin.elim0)

theorem stepAccept (n : Nat) (head : OTerm alpha)
    (hh : Nonempty (Derivation body Delta (InternalLessThan.strictLess head (numeral n)))) :
    Nonempty (Derivation body Delta (graph2 (symbolStep n) (numeral 1) head (numeral 1))) := by
  let xs : Fin 2 → OTerm alpha := ![head,numeral 1]
  have hl := InternalLessThanSupportProof.acceptOfLess head (numeral n) hh
  have hp := binaryValue InternalLessThan.ltTest (.projection 0) (constant 2 n)
    (numeral 1) head (numeral n) xs hl (projectionValue 0 xs)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue n xs)
  exact conjunctionAccept _ _ xs hp (projectionValue 1 xs)

theorem stepRecover (n : Nat) (head rest : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (symbolStep n) (numeral 1) head rest))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess head (numeral n) ⊓ eqn rest (numeral 1))) := by
  let xs : Fin 2 → OTerm alpha := ![head,rest]
  have h := conjunctionRecover (.composition InternalLessThan.ltTest ![.projection 0,constant 2 n]) (.projection 1) xs hs
  have hc := andLeft h
  have hv := andRight h
  have hl : Nonempty (Derivation body Delta (graph2 InternalLessThan.ltTest (numeral 1) head (numeral n))) := by
    apply compositionRecover InternalLessThan.ltTest ![.projection 0,constant 2 n]
      (numeral 1) xs ![head,numeral n] hc
    intro i
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => Fin.elim0 j) k) i
    · exact projectionValue 0 xs
    · exact OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue n xs
  have he := valueUnique (.projection (1 : Fin 2)) rest (numeral 1) xs (projectionValue 1 xs) hv
  exact andIntro (InternalLessThanProof.lessOfAcceptance head (numeral n) hl) he

theorem consAccept (n : Nat) (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (InternalLessThan.strictLess head (numeral n))))
    (ht : Nonempty (Derivation body Delta (graph1 (symbols n) (numeral 1) tail))) :
    Nonempty (Derivation body Delta (graph1 (symbols n) (numeral 1) raw)) :=
  InternalRawListRecursionProof.consValue (InternalLessThan.constantOne 0) (symbolStep n)
    raw head tail (numeral 1) (numeral 1) Fin.elim0 hc ht (stepAccept n head hh)

theorem consRecover (n : Nat) (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph1 (symbols n) (numeral 1) raw))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess head (numeral n) ⊓ graph1 (symbols n) (numeral 1) tail)) := by
  have hx := InternalRawListRecursionProof.consForward (InternalLessThan.constantOne 0) (symbolStep n)
    raw head tail (numeral 1) Fin.elim0 hc hv
  apply InternalRawListRecursionProof.stepCases (InternalLessThan.constantOne 0) (symbolStep n)
    (numeral 1) head tail Fin.elim0 _ hx
  intro beta j Theta rest hj hr hs
  simp only [consTermRename,emptyRename,GuardedSourceSyntaxProof.numeralRename] at hr hs
  simp only [conjunctionRename,graph1Rename,InternalLessThan.strictLess,
    InternalOriginalOrderSyntaxProof.orderRename,GuardedSourceSyntaxProof.numeralRename]
  have h := stepRecover n (head.relabel j) rest hs
  have ht := outputTransport (symbols n) rest (numeral 1) (Fin.cons (tail.relabel j) Fin.elim0) (andRight h) hr
  exact andIntro (andLeft h) ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.StepProof
