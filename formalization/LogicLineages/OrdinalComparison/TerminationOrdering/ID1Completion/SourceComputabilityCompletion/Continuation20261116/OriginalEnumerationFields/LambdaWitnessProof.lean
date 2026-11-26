module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaWitnessProof
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

theorem forward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ child childKey value deps values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) typ child)))
    (hck : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child (suc (xs 1)))))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps childKey z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ ⊓
      programGraph (fields n) (suc z) (childInputs xs child (suc (xs 1))))) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := UnaryKeyProof.lambdaDependency key (xs 0) (xs 1) param typ child childKey deps hpair hc hck hd
  have ha := singletonAnswers n key param childKey deps value values hdep hd hv hl
  have hfirst := firstValue key param values value z hl
  have hchoose := AcceptanceProof.forward n xs key param values hk hp ha hf
  have hm := LambdaChooseProof.acceptedMember n xs key values param typ child hk hp hc hchoose
  have hone := LambdaChooseProof.elimValue n xs key values param typ child (suc z) hk hp hc hm hchoose
  have he := valueUnique firstAnswer value (suc z) ![key,values,param] hfirst hone
  have hvone := outputTransport (extract n) value (suc z) ![childKey,param] he hv
  exact andIntro hm (fromExtract n xs child (suc (xs 1)) childKey param (suc z) hp hck hvone)

theorem backward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ child childKey value deps values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) typ child)))
    (hck : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childKey child (suc (xs 1)))))
    (hv : Nonempty (Derivation body Delta (graph2 (extract n) value childKey param)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps childKey z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values value z)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs child (suc (xs 1)))))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := UnaryKeyProof.lambdaDependency key (xs 0) (xs 1) param typ child childKey deps hpair hc hck hd
  have ha := singletonAnswers n key param childKey deps value values hdep hd hv hl
  have hfirst := firstValue key param values value z hl
  have hvone := toExtract n xs child (suc (xs 1)) childKey param (suc z) hp hck hf
  have he := valueUnique (extract n) value (suc z) ![childKey,param] hv hvone
  have hone := outputTransport firstAnswer value (suc z) ![key,values,param] he hfirst
  have hchoose := LambdaChooseProof.introValue n xs key values param typ child (suc z) hk hp hc hm hone
  exact AcceptanceProof.backward n xs key param values hk hp ha hg hchoose
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaWitnessProof
