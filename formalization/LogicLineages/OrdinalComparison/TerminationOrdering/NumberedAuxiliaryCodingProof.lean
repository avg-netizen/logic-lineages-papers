module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryCodingSupportProof

theorem headCodeInjective {Symbol : Type} : Function.Injective (@headCode Symbol) := by
  intro f g h
  cases f <;> cases g <;> simp_all [headCode]

theorem termCodeHEq {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (upsilon : Ty) (r : AuxTerm Symbol arity Gamma upsilon),
      tau=upsilon → termCode q=termCode r → HEq q r := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (otherTypes : List Ty) (rest : AuxArguments Symbol arity Gamma otherTypes),
      types=otherTypes → argumentsCode args=argumentsCode rest → HEq args rest)
  case var v =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    cases ht
    rename_i w
    exact heq_of_eq (congrArg AuxTerm.var (SourceObservationCodingProof.variableIndexInjective v w (Code.var.inj h)))
  case lam Gamma sigma tau body ih =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    rename_i sigma' tau' other
    obtain ⟨hd,hb⟩ := Code.lam.inj h
    cases hd
    have hc := (Ty.arrow.inj ht).2
    cases hc
    exact heq_of_eq (congrArg AuxTerm.lam (eq_of_heq (ih _ other rfl hb)))
  case app q a ihq iha =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    rename_i sigma f b
    obtain ⟨he,hf,hb⟩ := Code.app.inj h
    cases he
    cases ht
    exact heq_of_eq (congrArg₂ AuxTerm.app (eq_of_heq (ihq _ _ rfl hf)) (eq_of_heq (iha _ _ rfl hb)))
  case bottom tau =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    cases ht
    rfl
  case ordinary f base ih =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    rename_i g target
    have hg := headCodeInjective (Code.ordinary.inj h).1
    subst g
    exact heq_of_eq (congrArg (AuxTerm.ordinary f) (eq_of_heq (ih _ target rfl (Code.ordinary.inj h).2)))
  case numbered k f tau base types extras ihb ihe =>
    intro upsilon r ht h
    cases r <;> simp only [termCode] at h <;> try contradiction
    obtain ⟨hk,hg,ho,hb,htypes,he⟩ := Code.numbered.inj h
    have hhead := headCodeInjective hg
    cases ho
    cases hk
    cases hhead
    cases htypes
    exact heq_of_eq (congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e)
      (eq_of_heq (ihb _ _ rfl hb)) (eq_of_heq (ihe _ _ rfl he)))
  case nil Gamma otherTypes rest ht h =>
    cases rest <;> simp only [argumentsCode] at h <;> try contradiction
    rfl
  case cons Gamma sigma types q rest ihq ihr otherTypes target ht h =>
    cases target with
    | nil => cases h
    | cons a tail =>
      obtain ⟨hs,hr⟩ := List.cons.inj ht
      cases hs
      cases hr
      have he := Code.argumentsCons.inj h
      exact heq_of_eq (congrArg₂ AuxArguments.cons (eq_of_heq (ihq _ a rfl he.2.1)) (eq_of_heq (ihr _ tail rfl he.2.2)))

theorem termCodeInjective : NumberedAuxiliaryCodingTargets.ActualTermCodeInjective := by
  intro Symbol arity Gamma tau q r h
  exact eq_of_heq (termCodeHEq q tau r rfl h)

theorem argumentCodeInjective : NumberedAuxiliaryCodingTargets.ActualArgumentCodeInjective := by
  intro Symbol arity Gamma types args
  induction types with
  | nil => intro rest h; cases args; cases rest; rfl
  | cons sigma types ih =>
    intro rest h
    cases args with
    | cons q qs => cases rest with
      | cons r rs =>
        have he := Code.argumentsCons.inj h
        exact congrArg₂ AuxArguments.cons (termCodeInjective Symbol arity Gamma sigma he.2.1) (ih he.2.2)

theorem packedCodeInjective : NumberedAuxiliaryCodingTargets.ActualPackedCodeInjective := by
  intro Symbol arity Gamma q r h
  rcases q with ⟨sigma,q⟩
  rcases r with ⟨tau,r⟩
  have he := Prod.mk.inj h
  cases he.1
  have hq := termCodeInjective Symbol arity Gamma sigma he.2
  exact congrArg (Sigma.mk sigma) hq

theorem packedEquality : NumberedAuxiliaryCodingTargets.ActualPackedEquality := by
  intro Symbol inst arity Gamma q r
  simp only [packedEqual,decide_eq_true_eq]
  exact ⟨fun h => packedCodeInjective Symbol arity Gamma h,congrArg packedCode⟩

def packedDecidableEq {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} :
    DecidableEq (Packed Symbol arity Gamma) := fun q r =>
  if h : packedEqual q r=true then isTrue ((packedEquality Symbol inferInstance arity Gamma q r).mp h)
  else isFalse (fun he => h ((packedEquality Symbol inferInstance arity Gamma q r).mpr he))

theorem labelBound : NumberedAuxiliaryCodingTargets.ActualLabelBound := by
  intro Symbol arity Gamma tau q
  exact (labelsIff q (maxLabel q)).mpr (Nat.le_refl _)

theorem primaryClassBounds : NumberedAuxiliaryCodingTargets.ActualPrimaryClassBounds := by
  intro Symbol arity symbols S Gamma q r h
  have he := NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S Gamma q r h
  exact ⟨NumberedPrimaryEquivalenceProof.primarySizePreservation Symbol arity Gamma q r he,
    (primaryLabels (maxLabel q.2) he).mp (labelBound Symbol arity Gamma q.1 q.2)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingProof
