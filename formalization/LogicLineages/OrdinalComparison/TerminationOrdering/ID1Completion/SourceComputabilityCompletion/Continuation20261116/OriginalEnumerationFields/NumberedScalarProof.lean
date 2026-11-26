module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedControlsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedScalarProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof NumberedControlsProof
open OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem labelSucc (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 (succOf labels) (suc (xs 4)) key answers param)) :=
  unaryValue .succ labels (suc (xs 4)) (xs 4) ![key,answers,param] (successorValue (Fin.cons (xs 4) Fin.elim0))
    (ParameterDeepProof.labelsAt xs key answers param hp)

theorem boundSucc (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 (succOf tupleBound) (suc (xs 5)) key answers param)) :=
  unaryValue .succ tupleBound (suc (xs 5)) (xs 5) ![key,answers,param] (successorValue (Fin.cons (xs 5) Fin.elim0))
    (ParameterDeepProof.tupleBoundAt xs key answers param hp)

theorem labelForward (xs : Fin 6 → OTerm alpha) (key answers param label : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hl : Nonempty (Derivation body Delta (graph3 numberedLabel label key answers param)))
    (hv : Nonempty (Derivation body Delta (graph3 labelTest (suc z) key answers param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc (xs 4)))) :=
  InternalLessThanProof.lessOfAcceptance label (suc (xs 4))
    (binaryRecover InternalLessThan.ltTest numberedLabel (succOf labels) (suc z) label (suc (xs 4)) ![key,answers,param]
      hv hl (labelSucc xs key answers param hp))

theorem labelBackward (xs : Fin 6 → OTerm alpha) (key answers param label : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hl : Nonempty (Derivation body Delta (graph3 numberedLabel label key answers param)))
    (hv : Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc (xs 4))))) :
    Nonempty (Derivation body Delta (graph3 labelTest (suc z) key answers param)) :=
  binaryValue InternalLessThan.ltTest numberedLabel (succOf labels) (suc z) label (suc (xs 4)) ![key,answers,param]
    (InternalLessThanSupportProof.acceptOfLess label (suc (xs 4)) hv) hl (labelSucc xs key answers param hp)

theorem typeForward (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ht : Nonempty (Derivation body Delta (graph3 numberedType typ key answers param)))
    (hv : Nonempty (Derivation body Delta (graph3 typeTest (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)) :=
  binaryRecover contains types numberedType (suc z) (xs 2) typ ![key,answers,param] hv
    (SelectorInputProof.typesAt xs key answers param hp) ht

theorem typeBackward (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ht : Nonempty (Derivation body Delta (graph3 numberedType typ key answers param)))
    (hv : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ))) :
    Nonempty (Derivation body Delta (graph3 typeTest (suc z) key answers param)) :=
  binaryValue contains types numberedType (suc z) (xs 2) typ ![key,answers,param] hv
    (SelectorInputProof.typesAt xs key answers param hp) ht

theorem headForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head mapped : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hh : Nonempty (Derivation body Delta (graph3 numberedHead head key answers param)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hv : Nonempty (Derivation body Delta (graph3 (headTest n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)) :=
  HeadAllowedProof.recover n (xs 3) mapped head hmap
    (binaryRecover contains (.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads]) numberedHead
      (suc z) mapped head ![key,answers,param] hv (OrdinaryChooseProof.mappedAt n xs key answers param mapped hp hmap) hh)

theorem headBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param head mapped : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hh : Nonempty (Derivation body Delta (graph3 numberedHead head key answers param)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hv : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head))) :
    Nonempty (Derivation body Delta (graph3 (headTest n) (suc z) key answers param)) :=
  binaryValue contains (.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) ![heads]) numberedHead
    (suc z) mapped head ![key,answers,param] (HeadAllowedProof.introduce n (xs 3) mapped head hmap hv)
    (OrdinaryChooseProof.mappedAt n xs key answers param mapped hp hmap) hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedScalarProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedScalarProof
