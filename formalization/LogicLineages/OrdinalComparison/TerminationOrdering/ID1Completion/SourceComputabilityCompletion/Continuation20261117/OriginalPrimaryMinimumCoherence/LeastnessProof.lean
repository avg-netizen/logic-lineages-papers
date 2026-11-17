module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.NormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.LeastnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open NormalizationProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)

theorem facts (T : Program 2) (P : Program 3) (root out parameter earlier : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 T (suc z) root parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 (OriginalTransparentMinimum.minimum T P) out root parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.atMost out root ⊓
       (graph3 (OriginalTransparentMinimum.reflexiveClassTest T P) (suc z) root out parameter ⊓
        ((InternalLessThan.strictLess earlier out).imp
         (graph3 (OriginalTransparentMinimum.reflexiveClassTest T P) (suc z) root earlier parameter).not)))) := by
  obtain ⟨ht⟩ := ht
  obtain ⟨hm⟩ := hm
  obtain ⟨law⟩ := OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalMinimum
    T P body alpha Delta out root parameter earlier
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction ht hm)⟩

theorem unique (T : Program 2) (P : Program 3) (left right m k parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 T (suc z) left parameter)))
    (hu : Nonempty (Derivation body Delta (graph2 T (suc z) right parameter)))
    (hlself : Nonempty (Derivation body Delta (graph3 P (suc z) left left parameter)))
    (hrself : Nonempty (Derivation body Delta (graph3 P (suc z) right right parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 (OriginalTransparentMinimum.minimum T P) m left parameter)))
    (hk : Nonempty (Derivation body Delta (graph2 (OriginalTransparentMinimum.minimum T P) k right parameter)))
    (rows : ∀ probe : OTerm alpha, Nonempty (Derivation body Delta
      ((graph3 P (suc z) left probe parameter).imp (graph3 P (suc z) right probe parameter) ⊓
       (graph3 P (suc z) right probe parameter).imp (graph3 P (suc z) left probe parameter)))) :
    Nonempty (Derivation body Delta (equal m k)) := by
  have fm := facts T P left m parameter k ht hm
  have fk := facts T P right k parameter m hu hk
  obtain ⟨hmP⟩ := toClass T P left m parameter hlself (andLeft (andRight fm))
  obtain ⟨hkP⟩ := toClass T P right k parameter hrself (andLeft (andRight fk))
  obtain ⟨rowM⟩ := rows m
  obtain ⟨rowK⟩ := rows k
  obtain ⟨hmOther⟩ := toReflexive T P right m parameter hu
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft rowM) hmP⟩
  obtain ⟨hkOther⟩ := toReflexive T P left k parameter ht
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight rowK) hkP⟩
  obtain ⟨missM⟩ := andRight (andRight fm)
  obtain ⟨missK⟩ := andRight (andRight fk)
  have hmk : Nonempty (Derivation body Delta (InternalLessThan.strictLess m k).not) :=
    ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp missK _) (Derivation.hypothesis List.mem_cons_self))
        (addHyp hmOther _))⟩
  have hkm : Nonempty (Derivation body Delta (InternalLessThan.strictLess k m).not) :=
    ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination
        (Derivation.implicationElimination (addHyp missM _) (Derivation.hypothesis List.mem_cons_self))
        (addHyp hkOther _))⟩
  exact OriginalActiveKernelMinimumSupportProof.equalOfNotLess m k hmk hkm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.LeastnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.LeastnessProof
