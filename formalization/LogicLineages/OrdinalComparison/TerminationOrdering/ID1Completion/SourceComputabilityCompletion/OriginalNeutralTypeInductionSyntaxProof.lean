module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules OriginalNeutralExpansion
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalAccessibilityRulesSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding bindTerm liftBind varBind)
open SourceComputabilityFormulaSupportProof (numeral allOne)
open GuardedSourceSyntaxProof (numeralRename)

/-- Only original binder and term renaming; no source relation changes. -/
theorem successorsRename {alpha beta : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (object : OTerm alpha) (j : alpha → beta) :
    (computableSuccessors src comp context tau object).relabel j =
      computableSuccessors src comp context tau (object.relabel j) := by
  unfold computableSuccessors
  rw [actualUniversalRenaming]
  change allOne (((edge src false context (object.relabel Sum.inl) (.var (.inr 0))).relabel (Sum.map j id)).imp
    ((computable comp tau (numeral context) (.var (.inr 0))).relabel (Sum.map j id))) = _
  rw [edgeRename,computableRename,numeralRename]
  congr 3
  rw [Term.relabel_relabel,Term.relabel_relabel]
  rfl

theorem successorInstance {alpha : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (object target : OTerm alpha) :
    instantiate ((edge src false context (object.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (computable comp tau (numeral context) (.var (.inr (0 : Fin 1))))) (emb target) =
    (edge src false context object target).imp (computable comp tau (numeral context) target) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((edge src false context (object.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).subst
    (fun a => emb (bindTerm target a))).imp
      ((computable comp tau (numeral context) (.var (.inr (0 : Fin 1)))).subst
        (fun a => emb (bindTerm target a))) = _
  rw [edgeSubst,computableSubst,liftBind,varBind,InternalAccessibilityRulesSyntaxProof.numeralSubst]

/-- Consume the original existential source edge, not an unguarded raw edge. -/
theorem successorApply {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (tau : Ty) (object target : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (computableSuccessors src comp context tau object)))
    (he : Nonempty (Derivation body Gamma (edge src false context object target))) :
    Nonempty (Derivation body Gamma (computable comp tau (numeral context) target)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨he⟩ := he
  have hh := Derivation.universalElimination (emb target) hs
  rw [successorInstance] at hh
  exact ⟨Derivation.implicationElimination hh he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionSyntaxProof
