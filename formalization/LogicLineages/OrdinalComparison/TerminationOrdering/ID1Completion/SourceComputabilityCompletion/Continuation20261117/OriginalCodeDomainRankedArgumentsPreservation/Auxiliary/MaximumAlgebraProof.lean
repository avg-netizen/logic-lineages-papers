module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumBaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumAlgebraProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum)
open MaximumBaseProof (forward backward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem weakAntisymmetric (a b : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (InternalLessThan.strictLess a (suc b))))
    (hba : Nonempty (Derivation body Delta (InternalLessThan.strictLess b (suc a)))) :
    Nonempty (Derivation body Delta (eqn a b)) := by
  apply InternalOriginalPairingOrderArithmeticProof.weakCases a b _ hab
  · exact InternalOriginalPairingOrderArithmeticProof.strictWeakConflict a b _
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hba _)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem commutative (a b ab ba : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 maximum ab a b)))
    (hba : Nonempty (Derivation body Delta (graph2 maximum ba b a))) :
    Nonempty (Derivation body Delta (eqn ab ba)) := by
  have h1 := forward a b ab ab hab (InternalCoprimeMultipleBoundedProof.selfLtSucc ab)
  have h2 := forward b a ba ba hba (InternalCoprimeMultipleBoundedProof.selfLtSucc ba)
  exact weakAntisymmetric ab ba
    (backward a b ab ba hab (andRight h2) (andLeft h2))
    (backward b a ba ab hba (andRight h1) (andLeft h1))

theorem associative (a b c ab bc left right : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 maximum ab a b)))
    (hbc : Nonempty (Derivation body Delta (graph2 maximum bc b c)))
    (hl : Nonempty (Derivation body Delta (graph2 maximum left ab c)))
    (hr : Nonempty (Derivation body Delta (graph2 maximum right a bc))) :
    Nonempty (Derivation body Delta (eqn left right)) := by
  have hl1 := forward ab c left left hl (InternalCoprimeMultipleBoundedProof.selfLtSucc left)
  have hl2 := forward a b ab left hab (andLeft hl1)
  have hr1 := forward a bc right right hr (InternalCoprimeMultipleBoundedProof.selfLtSucc right)
  have hr2 := forward b c bc right hbc (andRight hr1)
  exact weakAntisymmetric left right
    (backward ab c left right hl
      (backward a b ab right hab (andLeft hr1) (andLeft hr2)) (andRight hr2))
    (backward a bc right left hr (andLeft hl2)
      (backward b c bc left hbc (andRight hl2) (andRight hl1)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumAlgebraProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MaximumAlgebraProof
