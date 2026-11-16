module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof ChildInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param head child childKey value deps values mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hck : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child (xs 1))))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps childKey z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z)))
    (hmap : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head ⊓
      programGraph (fields n) (suc z) (childInputs xs child (xs 1)))) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := UnaryKeyProof.ordinaryDependency key (xs 0) (xs 1) param head child childKey deps hpair hc hck hd
  have ha := singletonAnswers n key param childKey deps value values hdep hd hv hl
  have hfirst := firstValue key param values value z hl
  have hchoose := AcceptanceProof.forward n xs key param values hk hp ha hf
  have hm := OrdinaryChooseProof.acceptedMember n xs key values param head child mapped hk hp hc hmap hchoose
  have hone := OrdinaryChooseProof.elimValue n xs key values param head child mapped hk hp hc hmap hm hchoose
  have he := valueUnique firstAnswer value (suc z) ![key,values,param] hfirst hone
  have hvone := outputTransport (extract n) value (suc z) ![childKey,param] he hv
  exact andIntro hm (fromExtract n xs child (xs 1) childKey param (suc z) hp hck hvone)

theorem backward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param head child childKey value deps values mapped : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child)))
    (hck : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child (xs 1))))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps childKey z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z)))
    (hmap : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (hm : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs child (xs 1))))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := UnaryKeyProof.ordinaryDependency key (xs 0) (xs 1) param head child childKey deps hpair hc hck hd
  have ha := singletonAnswers n key param childKey deps value values hdep hd hv hl
  have hfirst := firstValue key param values value z hl
  have hvone := toExtract n xs child (xs 1) childKey param (suc z) hp hck hf
  have he := valueUnique (extract n) value (suc z) ![childKey,param] hv hvone
  have hone := outputTransport firstAnswer value (suc z) ![key,values,param] he hfirst
  have hchoose := OrdinaryChooseProof.introValue n xs key values param head child mapped hk hp hc hmap hm hone
  exact AcceptanceProof.backward n xs key param values hk hp ha hg hchoose
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryWitnessProof
