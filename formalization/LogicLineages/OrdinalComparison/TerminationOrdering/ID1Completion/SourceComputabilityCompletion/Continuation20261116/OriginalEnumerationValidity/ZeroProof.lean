module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineRecoveryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalEnumerationRecursionInterface
open InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
theorem outputZero (n : Nat) (node param bound out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound z)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (eqn out z)) := by
  have hd : Nonempty (Derivation body Delta (graph2 D z node param)) :=
    zeroBranchIntro R (InternalAcceptance.constantZero 2) positiveDependencies z ![node,param]
      (SelectorProof.rankAt node param bound z hn) (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have ha := AnswersProof.answersAt n node param z z hd (AnswersProof.nilMap n param)
  have hg := (OriginalEnumerationEquation.Proof.exchangeEquation n body alpha Delta node param z out ha).mp he
  exact CombineRecoveryProof.zero n node z param out (SelectorProof.fuelAt node z param bound z hn) hg

theorem atKnown (n : Nat) (node param bound out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound z)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (Lists.AllValid n out)) := by
  have hz := outputZero n node param bound out hn he
  apply ListBindingProof.introduce n out
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let M : Formula (alpha ⊕ Fin 1) := graph2 contains (numeral 1) (out.relabel Sum.inl) (.var (.inr 0))
  let Theta := M :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hzj := renameInto hz (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  simp only [InternalTagArithmeticSyntaxProof.eqnRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hzj
  have hm : Nonempty (Derivation body Theta M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hm0 := headTransport contains (numeral 1) (out.relabel Sum.inl) z
    (Fin.cons (.var (.inr (0 : Fin 1))) Fin.elim0) hzj hm
  exact Derivation.explosion (Classical.choice (OriginalAscendingRange.SupportProof.nilImpossible (.var (.inr 0)) hm0))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ZeroProof
