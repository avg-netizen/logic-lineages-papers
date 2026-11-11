module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableLiftingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableMultisetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction
open NumberedPrimarySubstitution NumberedBottomVariable NumberedBottomVariableProof

theorem packedLambdaShapeInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (ht : BottomOrVariable theta) (q : Packed Symbol arity Gamma)
    (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma :: Delta) tau)
    (h : substitutePacked theta q = ⟨.arrow sigma tau,.lam body⟩) :
    ∃ original : AuxTerm Symbol arity (sigma :: Gamma) tau,
      q = ⟨.arrow sigma tau,.lam original⟩ ∧ substitute original (liftSubstitution theta) = body := by
  rcases q with ⟨rho,q⟩
  cases q with
  | var v =>
    rcases ht v with hb | ⟨w,hw⟩
    · have hh := congrArg NumberedAuxiliaryCoding.packedCode h
      simp [substitutePacked,substitute,hb,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh
    · have hh := congrArg NumberedAuxiliaryCoding.packedCode h
      simp [substitutePacked,substitute,hw,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh
  | @lam _ sigma' tau' original =>
    have htype : Ty.arrow sigma' tau' = Ty.arrow sigma tau := congrArg Sigma.fst h
    obtain ⟨hs,htype⟩ := Ty.arrow.inj htype
    cases hs
    cases htype
    have hh : AuxTerm.lam (substitute original (liftSubstitution theta)) = AuxTerm.lam body :=
      eq_of_heq (Sigma.mk.inj h).2
    exact ⟨original,rfl,by injection hh⟩
  | app f a =>
    have hh := congrArg NumberedAuxiliaryCoding.packedCode h
    simp [substitutePacked,substitute,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh
  | bottom rho =>
    have hh := congrArg NumberedAuxiliaryCoding.packedCode h
    simp [substitutePacked,substitute,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh
  | ordinary f base =>
    have hh := congrArg NumberedAuxiliaryCoding.packedCode h
    simp [substitutePacked,substitute,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh
  | numbered k f rho base types extras =>
    have hh := congrArg NumberedAuxiliaryCoding.packedCode h
    simp [substitutePacked,substitute,NumberedAuxiliaryCoding.packedCode,NumberedAuxiliaryCoding.termCode] at hh

theorem lambdaShapeInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    {sigma tau : Ty} (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (ht : BottomOrVariable theta) (q : AuxTerm Symbol arity Gamma (.arrow sigma tau))
    (body : AuxTerm Symbol arity (sigma :: Delta) tau)
    (h : substitute q theta = .lam body) :
    ∃ original : AuxTerm Symbol arity (sigma :: Gamma) tau,
      q = .lam original ∧ substitute original (liftSubstitution theta) = body := by
  obtain ⟨original,hq,he⟩ := packedLambdaShapeInverse theta ht ⟨_,q⟩ sigma tau body
    (congrArg (fun t => (⟨.arrow sigma tau,t⟩ : Packed Symbol arity Delta)) h)
  exact ⟨original,eq_of_heq (Sigma.mk.inj hq).2,he⟩

theorem applicationStepCases {Symbol : Type} {arity : Symbol → Nat}
    {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {sigma tau : Ty} (f : AuxTerm Symbol arity Gamma (.arrow sigma tau))
    (a : AuxTerm Symbol arity Gamma sigma) (r : AuxTerm Symbol arity Gamma tau)
    (h : WindowStep Symbol arity symbols S above Gamma tau (.app f a) r) :
    (∃ g, WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) f g ∧ r = .app g a) ∨
    (∃ body : AuxTerm Symbol arity (sigma :: Gamma) tau,
      f = .lam body ∧ r = substitute body (singleSubstitution a)) ∨ r = .bottom tau := by
  cases h with
  | appFunction f g a hs => exact Or.inl ⟨g,hs,rfl⟩
  | beta body a => exact Or.inr (Or.inl ⟨body,rfl,rfl⟩)
  | bottom q hn => exact Or.inr (Or.inr rfl)

theorem memberImageInverse {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (values : List (Packed Symbol arity Gamma)) (tau : Ty) (r : AuxTerm Symbol arity Delta tau)
    (h : (⟨tau,r⟩ : Packed Symbol arity Delta) ∈ values.map (substitutePacked theta)) :
    ∃ q : AuxTerm Symbol arity Gamma tau,
      (⟨tau,q⟩ : Packed Symbol arity Gamma) ∈ values ∧ substitute q theta = r := by
  obtain ⟨⟨rho,q⟩,hq,he⟩ := List.mem_map.mp h
  have ht : rho = tau := congrArg Sigma.fst he
  cases ht
  exact ⟨q,hq,by injection he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepSupportProof
