module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.MembershipProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalSourceInversionSupportProof (onEquality)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalQuotientComparisonProof (orRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem candidateTransport (list a b : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn a b)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list a))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) list b)) := by
  unfold graph2 programGraph at hm ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta _ (numeral 1)
    ![list,a] ![list,b] _ hm
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun x => Fin.elim0 x) k) i
  · rw [onEquality]
    exact ⟨refl list⟩
  · rw [onEquality]
    exact he

theorem tailMembership (T Q : Program 2) (seed parameter pool tail probe : OTerm alpha)
    (hT : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
    (hQ : Nonempty (Derivation body Delta (graph2 Q tail seed parameter)))
    (hP : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool T Q) pool seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail seed))) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool probe)) ↔
     Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail probe))) := by
  have hc := SeededPrimaryPool.InternalProof.internalPoolCharacterization T Q body alpha Delta
    seed parameter pool tail probe hT hQ hP
  constructor
  · intro hm
    obtain ⟨hd⟩ := hc.mp hm
    let A := eqn probe seed
    let B := graph2 contains (numeral 1) tail probe
    have he : Nonempty (Derivation body (A :: Delta) (eqn seed probe)) :=
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
    obtain ⟨hl⟩ := candidateTransport tail seed probe he (withHyp hs A)
    have hr : Derivation body (B :: Delta) B := Derivation.hypothesis List.mem_cons_self
    exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
      (Derivation.implicationIntroduction hr)⟩
  · rintro ⟨hm⟩
    exact hc.mpr ⟨orRight hm⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.MembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.MembershipProof
