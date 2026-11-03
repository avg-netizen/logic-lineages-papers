module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaBitsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains
open TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation OriginalSpineActions
open FullListValueApplication RelatedEnvironments ActualValueLogicalRelation ActualComparisonCompleteness
open RelationalSyntax RelationalSyntaxSupportProof LambdaSpineActions LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem consumeRelated (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma upsilon : Ty} (body : ConfinedTerm I (sigma::Gamma) upsilon)
    (hs : ScannerRelated I above M body) (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (mask : Protected Gamma) (hr : EnvironmentRelated I above P rho s)
    (types : List Ty) (tau : Ty) (values : Values I types P)
    (args : Arguments Symbol arity (portTypes P.val++I.context) types)
    (h : Ty.arrow sigma upsilon=arrows types tau) (hn : types≠[])
    (hargs : ∀ i,Related I above (types.get i) P (values i) (argumentAt args i)) :
    match ProtectedApply.applyWith (.lam body.val) mask s args h with
    | none => consumeNonempty (action body) M P rho mask types tau values h hn=ExecutableDomainBottom.bottomValue I tau P
    | some result => Related I above tau P (consumeNonempty (action body) M P rho mask types tau values h hn) result := by
  cases args with
  | nil => exact False.elim (hn rfl)
  | cons a rest =>
    obtain ⟨h1,h2⟩ := Ty.arrow.inj h
    cases h1
    cases h2
    have hhead : Related I above sigma P (values ⟨0,by simp⟩) a := by
      simpa [argumentAt] using hargs ⟨0,by simp⟩
    have henv : EnvironmentRelated I above P (extend (values ⟨0,by simp⟩) rho) (extendEnvironment s a) :=
      RelatedEnvironmentsProof.extension Symbol inferInstance arity I above Gamma P rho s sigma
        (values ⟨0,by simp⟩) a hr hhead
    have hrest : ∀ i,Related I above _ P (tailValues values i) (argumentAt rest i) :=
      fun i => hargs i.succ
    have H := hs P (extend (values ⟨0,by simp⟩) rho) (extendEnvironment s a)
      (protectExtend mask) henv _ tau (tailValues values) rest rfl hrest
    change (match ProtectedApply.applyWith body.val (protectExtend mask) (extendEnvironment s a) rest rfl with
      | none => scan body M P (extend (values ⟨0,by simp⟩) rho) (protectExtend mask) _ tau (tailValues values) rfl=
          ExecutableDomainBottom.bottomValue I tau P
      | some result => Related I above tau P
          (scan body M P (extend (values ⟨0,by simp⟩) rho) (protectExtend mask) _ tau (tailValues values) rfl) result)
    exact H

theorem tupleEquation {Gamma : List Ty} {sigma upsilon : Ty}
    (body : ConfinedTerm I (sigma::Gamma) upsilon) (M : Constructors I) (P : World I)
    (rho : Environment I Gamma P) (suffix : Suffix (.arrow sigma upsilon))
    (values : FullTuple I (.arrow sigma upsilon) suffix P) :
    applyValue (LambdaSpineActionsProof.lambdaValue body.val (action body) M P rho) suffix values=
      consumeNonempty (action body) M P rho (fun _ => false) suffix.val.1 suffix.val.2 values
        ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).2.symm
        ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).1 := by
  unfold applyValue
  rw [LambdaSpineActionsProof.valueLayer]
  change consumeNonempty (action body) M P (restrict (fun _ hp => hp) rho) (fun _ => false)
      suffix.val.1 suffix.val.2 values _ _=_
  rw [TypedValueEnvironmentProof.restrictionIdentity Symbol inferInstance arity I Gamma P rho]

theorem lambdaRelated (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma upsilon : Ty} (body : ConfinedTerm I (sigma::Gamma) upsilon)
    (he : EvaluationRelated I above M body) (hs : ScannerRelated I above M body)
    (P : World I) (rho : Environment I Gamma P)
    (s : MarkedSubstitution Symbol arity Gamma (portTypes P.val++I.context))
    (hr : EnvironmentRelated I above P rho s) :
    Related I above (.arrow sigma upsilon) P
      (LambdaSpineActionsProof.lambdaValue body.val (action body) M P rho) (substituteTerm (.lam body.val) s) := by
  rw [Related]
  constructor
  · exact RelationalSyntaxLambdaBitsProof.bitSound above M body he P rho s hr
  · intro Q h suffix values args hargs
    have henv : EnvironmentRelated I above Q (restrict h rho) (futureSubstitution h s) :=
      RelatedEnvironmentsProof.weakening Symbol inferInstance arity I above Gamma P Q h rho s hr
    have hv := LambdaSpineActionsProof.valueNatural body.val (action body) M P Q h rho
    rw [hv,RelationalSyntaxLambdaBitsProof.futureSubstitute (.lam body.val) h s]
    rw [← ProtectedApplyProof.initialOriginalEquation Symbol arity Gamma (portTypes Q.val++I.context)
      (.arrow sigma upsilon) suffix.val.2 (.lam body.val) (futureSubstitution h s) suffix.val.1 args
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).2.symm]
    rw [tupleEquation body M Q (restrict h rho) suffix values]
    have H := consumeRelated above M body hs Q (restrict h rho) (futureSubstitution h s) (fun _ => false)
      henv suffix.val.1 suffix.val.2 values args
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).2.symm
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).1 hargs
    cases happ : ProtectedApply.applyWith (.lam body.val) (fun _ => false) (futureSubstitution h s) args
        ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp suffix.property).2.symm with
    | none => simp only [happ] at H ⊢; exact H
    | some result => simp only [happ] at H ⊢; exact H

theorem lambdaCase (above : Symbol → Symbol → Prop) (M : Constructors I)
    {Gamma : List Ty} {sigma upsilon : Ty} (body : ConfinedTerm I (sigma::Gamma) upsilon)
    (hlam : Confined I (.lam body.val))
    (he : EvaluationRelated I above M body) (hs : ScannerRelated I above M body) :
    EvaluationRelated I above M ⟨.lam body.val,hlam⟩ ∧ ScannerRelated I above M ⟨.lam body.val,hlam⟩ := by
  have heLam : EvaluationRelated I above M ⟨.lam body.val,hlam⟩ := fun P rho s hr =>
    lambdaRelated above M body he hs P rho s hr
  refine ⟨heLam,?_⟩
  intro P rho s mask hr types tau values args h hargs
  cases args with
  | nil =>
    cases h
    rw [ProtectedApplyBindingProof.emptyTuple Symbol arity Gamma (portTypes P.val++I.context)
      _ (.lam body.val) mask s]
    exact emptyScanner above M ⟨.lam body.val,hlam⟩ heLam P rho s mask hr values
  | cons a rest =>
    exact consumeRelated above M body hs P rho s mask hr _ tau values (.cons a rest) h (by simp) hargs

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxLambdaProof
