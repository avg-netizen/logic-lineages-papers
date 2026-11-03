module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxVariableProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment
open CoherentConstructorLattice ConfinedStructuralInterpretation OriginalSpineActions FullListValueApplication
open RelatedEnvironments ActualValueLogicalRelation RelationalSyntax RelationalSyntaxSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem variableCase (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma : Ty} (v : Variable Gamma sigma) (hq : Confined I (.var v)) :
    EvaluationRelated I above M ⟨.var v,hq⟩ ∧ ScannerRelated I above M ⟨.var v,hq⟩ := by
  have he : EvaluationRelated I above M ⟨.var v,hq⟩ := fun P rho s hr => hr v
  refine ⟨he,?_⟩
  intro P rho s mask hr types tau values args h hargs
  cases args with
  | nil =>
    cases h
    change Related I above tau P (scan ⟨.var v,hq⟩ M P rho mask [] tau values rfl) (substituteTerm (.var v) s)
    exact emptyScanner above M ⟨.var v,hq⟩ he P rho s mask hr values
  | cons a rest =>
    cases hm : mask v with
    | true =>
      simp only [ProtectedApply.applyWith,hm,↓reduceIte]
      change variableScan v M P rho mask _ tau values h=ExecutableDomainBottom.bottomValue I tau P
      simp only [variableScan,List.cons_ne_nil,↓reduceIte,hm]
    | false =>
      have H := currentTuple above (rho v) (s v) (hr v) _ tau values (.cons a rest) h (by simp) hargs
      simp only [ProtectedApply.applyWith,hm,Bool.false_eq_true,↓reduceIte]
      change (match applyOriginalWith (s v) (fun w => .var w) (.cons a rest) h with
        | none => variableScan v M P rho mask _ tau values h=ExecutableDomainBottom.bottomValue I tau P
        | some result => Related I above tau P (variableScan v M P rho mask _ tau values h) result)
      simp only [variableScan,List.cons_ne_nil,↓reduceIte,hm,Bool.false_eq_true]
      exact H

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxVariableProof
