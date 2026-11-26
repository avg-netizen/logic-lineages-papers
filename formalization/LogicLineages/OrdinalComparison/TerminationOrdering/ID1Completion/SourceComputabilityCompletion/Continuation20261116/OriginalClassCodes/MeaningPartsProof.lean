module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningPartsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Meaning
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat) (H : Program 1)
variable (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha)

theorem assemble
    (hroot : Nonempty (Derivation body Delta (graph2 rootType (xs 1) seed param)))
    (htypes : Nonempty (Derivation body Delta (graph2 types (xs 2) seed param)))
    (hheads : Nonempty (Derivation body Delta (graph2 (heads n arity) (xs 3) seed param)))
    (hsize : Nonempty (Derivation body Delta (graph2 (size n) (xs 4) seed param)))
    (hlabels : Nonempty (Derivation body Delta (graph2 (labels n) (xs 5) seed param)))
    (hbound : Nonempty (Derivation body Delta (graph2 bound (xs 6) seed param)))
    (hfuel : Nonempty (Derivation body Delta (graph2 (fuel n) (xs 7) seed param)))
    (hadmission : Nonempty (Derivation body Delta (graph2 (admitted n H) (xs 8) seed param)))
    (hnonzero : Nonempty (Derivation body Delta ((eqn (xs 8) (numeral 0)).not)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (xs 1) (xs 0))))
    (hfields : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.accepted n (xs 0) (xs 6) (xs 2) (xs 3) (xs 5) (xs 4))))
    (hdepth : Nonempty (Derivation body Delta (OriginalEnumerationMembership.Targets.depthBound n (xs 0) (xs 7))))
    : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs)) :=
  andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (hroot) htypes) hheads) hsize) hlabels) hbound) hfuel) hadmission) hnonzero) hpair) hfields) hdepth

theorem rootPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 rootType (xs 1) seed param)) :=
  andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h)))))))))))

theorem typesPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 types (xs 2) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h)))))))))))

theorem headsPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 (heads n arity) (xs 3) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h))))))))))

theorem sizePart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 (size n) (xs 4) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h)))))))))

theorem labelsPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 (labels n) (xs 5) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h))))))))

theorem boundPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 bound (xs 6) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (h)))))))

theorem fuelPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 (fuel n) (xs 7) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (andLeft (h))))))

theorem admissionPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 (admitted n H) (xs 8) seed param)) :=
  andRight (andLeft (andLeft (andLeft (andLeft (h)))))

theorem nonzeroPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta ((eqn (xs 8) (numeral 0)).not)) :=
  andRight (andLeft (andLeft (andLeft (h))))

theorem pairPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (xs 1) (xs 0))) :=
  andRight (andLeft (andLeft (h)))

theorem fieldsPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.accepted n (xs 0) (xs 6) (xs 2) (xs 3) (xs 5) (xs 4))) :=
  andRight (andLeft (h))

theorem depthPart (h : Nonempty (Derivation body Delta (observations n arity H seed param candidate xs))) :
    Nonempty (Derivation body Delta (OriginalEnumerationMembership.Targets.depthBound n (xs 0) (xs 7))) :=
  andRight (h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningPartsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningPartsProof
