module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedTypesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedChooseProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param label head typ base list extra mapped len : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra])))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (hr : Nonempty (Derivation body Delta (Boolean.PointRange.At firstAnswer ![key,answers,param])))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (((((InternalLessThan.strictLess label (suc (xs 4)) ⊓ Targets.headAllowed n (xs 3) head) ⊓
      graph2 contains (suc z) (xs 2) typ) ⊓ graph3 firstAnswer (suc z) key answers param) ⊓
      Targets.typesAllowed list (xs 2) (xs 5)) ⊓ graph3 secondAnswer (suc z) key answers param)) := by
  have htag := NumberedInputProof.tagAt xs key answers param label head typ base list extra hk hc
  have hlabel := NumberedInputProof.labelAt xs key answers param label head typ base list extra hk hc
  have hhead := NumberedInputProof.headAt xs key answers param label head typ base list extra hk hc
  have htype := NumberedInputProof.typeAt xs key answers param label head typ base list extra hk hc
  have hlist := NumberedInputProof.typesAt xs key answers param label head typ base list extra hk hc
  have hf := NumberedControlsProof.forward n ![key,answers,param] hr
    (ChooseInternalProof.tag5Elim n ![key,answers,param] (suc z) htag hv)
  have h6 := andRight hf
  have t5 := andLeft hf
  have h5 := andRight t5
  have t4 := andLeft t5
  have h4 := andRight t4
  have t3 := andLeft t4
  have h3 := andRight t3
  have t2 := andLeft t3
  have h2 := andRight t2
  have t1 := andLeft t2
  have h1 := andRight t1
  have h0 := andLeft t1
  have p0 := NumberedScalarProof.labelForward xs key answers param label hp hlabel h0
  have p1 := NumberedScalarProof.headForward n xs key answers param head mapped hp hhead hmap h1
  have p2 := NumberedScalarProof.typeForward xs key answers param typ hp htype h2
  have p4 := NumberedTypesProof.forward xs key answers param list len hp hlist hlen h4 h5
  exact andIntro (andIntro (andIntro (andIntro (andIntro p0 p1) p2) h3) p4) h6

theorem backward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param label head typ base list extra mapped len : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra])))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (h0 : Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc (xs 4)))))
    (h1 : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)))
    (h2 : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (h3 : Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param)))
    (h4 : Nonempty (Derivation body Delta (Targets.typesAllowed list (xs 2) (xs 5))))
    (h5 : Nonempty (Derivation body Delta (graph3 secondAnswer (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have htag := NumberedInputProof.tagAt xs key answers param label head typ base list extra hk hc
  have hlabel := NumberedInputProof.labelAt xs key answers param label head typ base list extra hk hc
  have hhead := NumberedInputProof.headAt xs key answers param label head typ base list extra hk hc
  have htype := NumberedInputProof.typeAt xs key answers param label head typ base list extra hk hc
  have hlist := NumberedInputProof.typesAt xs key answers param label head typ base list extra hk hc
  have p0 := NumberedScalarProof.labelBackward xs key answers param label hp hlabel h0
  have p1 := NumberedScalarProof.headBackward n xs key answers param head mapped hp hhead hmap h1
  have p2 := NumberedScalarProof.typeBackward xs key answers param typ hp htype h2
  have p45 := NumberedTypesProof.backward xs key answers param list len hp hlist hlen h4
  exact ChooseInternalProof.tag5Intro n ![key,answers,param] (suc z) htag
    (NumberedControlsProof.backward n ![key,answers,param] p0 p1 p2 h3 (andLeft p45) (andRight p45) h5)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedChooseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedChooseProof
