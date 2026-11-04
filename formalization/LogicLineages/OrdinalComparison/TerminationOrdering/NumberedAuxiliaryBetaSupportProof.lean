module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliarySubstitution NumberedDirectCertificate
open NumberedOriginalAngle
open Source.SourceTypedPorts (variableIndex)

theorem variableEnvironmentCodes {Symbol : Type} {arity : Symbol → Nat} :
    ∀ (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (offset : Nat),
    (∀ {tau} (v : Variable Gamma tau),variableIndex (rho v)=variableIndex v+offset) →
    substitutionCodes (Symbol := Symbol) (arity := arity) Gamma (fun v => AuxTerm.var (rho v))=
      (List.range Gamma.length).map (fun index => Code.var (index+offset)) := by
  intro Gamma
  induction Gamma with
  | nil => intro Delta rho offset h; rfl
  | cons sigma Gamma ih =>
    intro Delta rho offset h
    have htail : ∀ {tau} (v : Variable Gamma tau),
        variableIndex (rho (.there v))=variableIndex v+(offset+1) := by
      intro tau v
      rw [h (.there v)]
      simp only [variableIndex]
      omega
    have hzero := h (Variable.here : Variable (sigma::Gamma) sigma)
    simp only [substitutionCodes,termCode,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
    rw [hzero,ih Delta (fun v => rho (.there v)) (offset+1) htail]
    simp only [variableIndex,Nat.zero_add]
    congr 1
    apply List.map_congr_left
    intro index hindex
    congr 1
    omega

theorem singleEnvironmentCalibration : NumberedAuxiliarySubstitutionTargets.ActualSingleEnvironmentCalibration := by
  intro Symbol arity Gamma sigma a
  change termCode a :: substitutionCodes Gamma (fun v => AuxTerm.var v)=
    termCode a :: (List.range Gamma.length).map Code.var
  have h := variableEnvironmentCodes (Symbol := Symbol) (arity := arity) Gamma Gamma
    (fun v => v) 0 (by intro tau v; omega)
  simpa only [Nat.add_zero] using congrArg (List.cons (termCode a)) h

theorem lambdaReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau)
    (h : ∃ domain body,termCode q=Code.lam domain body) :
    ∃ (domain result : Ty) (ht : tau=Ty.arrow domain result) (body : AuxTerm Symbol arity (domain::Gamma) result),
      q=transportAux ht.symm (AuxTerm.lam body) := by
  cases q with
  | lam body => exact ⟨_,_,rfl,body,rfl⟩
  | var v => obtain ⟨domain,body,h⟩ := h; cases h
  | app f a => obtain ⟨domain,body,h⟩ := h; cases h
  | bottom tau => obtain ⟨domain,body,h⟩ := h; cases h
  | ordinary f base => obtain ⟨domain,body,h⟩ := h; cases h
  | numbered k f tau base types extras => obtain ⟨domain,body,h⟩ := h; cases h

theorem betaCodeCalibration : NumberedAuxiliarySubstitutionTargets.ActualBetaCodeCalibration := by
  intro n arity Gamma q
  rcases q with ⟨tau,q⟩
  cases q with
  | var v => rfl
  | lam body => rfl
  | app f a =>
    by_cases h : ∃ domain body,termCode f=Code.lam domain body
    · obtain ⟨domain,result,ht,body,hf⟩ := lambdaReflection f h
      rcases Ty.arrow.inj ht with ⟨hd,hr⟩
      cases hd
      cases hr
      have he : ht=rfl := Subsingleton.elim _ _
      rw [he] at hf
      change f=AuxTerm.lam body at hf
      rw [hf]
      simp only [termCode,betaCode,directTarget,Option.map_some]
      rw [NumberedAuxiliarySubstitutionSupportProof.typedSubstitutionCalibration,singleEnvironmentCalibration]
    · have hb : betaCode Gamma.length (termCode (AuxTerm.app f a))=none := by
        change betaCode Gamma.length (Code.app _ (termCode f) (termCode a))=none
        cases hc : termCode f <;> try rfl
        exact False.elim (h ⟨_,_,hc⟩)
      rw [hb]
      unfold directTarget
      split <;> try contradiction <;> try rfl
      next output sigma body arg heRule hePack =>
        exfalso
        apply h
        have hc := congrArg (fun p : Packed (Fin n) arity Gamma => termCode p.2) hePack
        simp only [termCode] at hc
        have hf := (Code.app.inj hc).2.1
        exact ⟨_,_,hf⟩
      all_goals rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | numbered k f tau base types extras => rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaSupportProof
