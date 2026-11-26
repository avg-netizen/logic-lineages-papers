module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open AppendSyntaxProof
open InternalListInduction InternalListInductionProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendListProof
open InternalApplicationStepPeelSupportProof (andIntro)

theorem identity (code : OTerm alpha) :
    Nonempty (Derivation body Delta (appendIdentity code)) := by
  let theta : Formula (alpha ⊕ Fin 1) := appendIdentity (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
    rw [identityAtCode]
    exact appendZeroValue z
  have hs : Nonempty (Derivation body Delta (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Delta
    simp only [constructorBody,theta,identityAtIndex]
    let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := graph2 InternalListCodec.consCode c h t
    let R := appendIdentity t
    have hc : Nonempty (Derivation body (R :: C :: Delta.map (fun p => p.relabel Sum.inl)) C) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have ht : Nonempty (Derivation body (R :: C :: Delta.map (fun p => p.relabel Sum.inl)) R) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := consBackward c h t z t c hc ht hc
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have hh := actualOriginalListInductionAtCode body alpha Delta theta code (andIntro hz hs)
  rw [identityAtCode] at hh
  exact hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendIdentityProof
