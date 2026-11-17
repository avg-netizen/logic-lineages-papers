module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountRemoveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountKeepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseBranchAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro)
open EraseInvariant
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem remove (list head tail needle acc rest out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) rest))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle (suc z) rest)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseValueProof.removeValue head acc needle rest out hp ho he)
  · have hbit : Nonempty (Derivation body Delta (eqn (suc z) z ⊔ eqn (suc z) (suc z))) :=
      ⟨InternalQuotientComparisonProof.orRight (refl (suc z))⟩
    exact andIntro hbit (CountRemoveProof.remove list head tail needle rest hc he hf)

theorem absent (list head tail needle acc rest kept out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z kept))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle z kept)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.absent head acc needle rest kept out hp hk ho he)
  · have hbit : Nonempty (Derivation body Delta (eqn z z ⊔ eqn z (suc z))) :=
      ⟨InternalQuotientComparisonProof.orLeft (refl z)⟩
    exact andIntro hbit (CountKeepProof.keep list kept head tail rest needle z hc hk hf)

theorem found (list head tail needle acc rest kept out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest (suc z))))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) kept))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (result list needle (suc z) kept)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.alreadyFound head acc needle rest kept out hp hk ho)
  · have hbit : Nonempty (Derivation body Delta (eqn (suc z) z ⊔ eqn (suc z) (suc z))) :=
      ⟨InternalQuotientComparisonProof.orRight (refl (suc z))⟩
    exact andIntro hbit (CountKeepProof.keep list kept head tail rest needle (suc z) hc hk hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseBranchAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseBranchAtProof
