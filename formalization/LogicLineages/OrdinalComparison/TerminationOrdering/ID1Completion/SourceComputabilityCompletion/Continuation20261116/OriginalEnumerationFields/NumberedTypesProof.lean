module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedTypesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro)
open InputProof NumberedControlsProof NumberedScalarProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lengthAt (key answers param list len : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph3 numberedTypes list key answers param)))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list))) :
    Nonempty (Derivation body Delta (graph3 (.composition OriginalContextInsertion.length ![numberedTypes]) len key answers param)) :=
  LayerGuardProof.unaryVectorValue OriginalContextInsertion.length numberedTypes len list ![key,answers,param] hlen hl

theorem forward (xs : Fin 6 → OTerm alpha) (key answers param list len : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hl : Nonempty (Derivation body Delta (graph3 numberedTypes list key answers param)))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (hbound : Nonempty (Derivation body Delta (graph3 lengthTest (suc z) key answers param)))
    (hall : Nonempty (Derivation body Delta (graph3 typesTest (suc z) key answers param))) :
    Nonempty (Derivation body Delta (Targets.typesAllowed list (xs 2) (xs 5))) := by
  have hb := binaryRecover InternalLessThan.ltTest (.composition OriginalContextInsertion.length ![numberedTypes]) (succOf tupleBound)
    (suc z) len (suc (xs 5)) ![key,answers,param] hbound (lengthAt key answers param list len hl hlen) (boundSucc xs key answers param hp)
  have ha := binaryRecover allTypes numberedTypes types (suc z) list (xs 2) ![key,answers,param] hall hl
    (SelectorInputProof.typesAt xs key answers param hp)
  exact Types.AllowedProof.introduce list (xs 2) (xs 5) len hlen
    (InternalLessThanProof.lessOfAcceptance len (suc (xs 5)) hb) ((Types.Proof.equivalence list (xs 2)).mp ha)

theorem backward (xs : Fin 6 → OTerm alpha) (key answers param list len : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hl : Nonempty (Derivation body Delta (graph3 numberedTypes list key answers param)))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (ha : Nonempty (Derivation body Delta (Targets.typesAllowed list (xs 2) (xs 5)))) :
    Nonempty (Derivation body Delta (graph3 lengthTest (suc z) key answers param ⊓ graph3 typesTest (suc z) key answers param)) := by
  have hb := InternalLessThanSupportProof.acceptOfLess len (suc (xs 5))
    (Types.AllowedProof.lengthBound list (xs 2) (xs 5) len hlen ha)
  have hm := (Types.Proof.equivalence list (xs 2)).mpr (Types.AllowedProof.members list (xs 2) (xs 5) ha)
  exact andIntro
    (binaryValue InternalLessThan.ltTest (.composition OriginalContextInsertion.length ![numberedTypes]) (succOf tupleBound)
      (suc z) len (suc (xs 5)) ![key,answers,param] hb (lengthAt key answers param list len hl hlen) (boundSucc xs key answers param hp))
    (binaryValue allTypes numberedTypes types (suc z) list (xs 2) ![key,answers,param] hm hl (SelectorInputProof.typesAt xs key answers param hp))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedTypesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedTypesProof
