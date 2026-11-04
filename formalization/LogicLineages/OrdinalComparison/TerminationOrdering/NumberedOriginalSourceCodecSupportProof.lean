module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedOriginalSourceCodec

theorem groundArgumentsValues {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (k : Nat) (args : OriginalArguments Symbol arity Gamma (List.replicate k .ground)) :
    NumberedOriginalSourceCodec.groundArguments k (groundValues k args)=args := by
  induction k with
  | zero => cases args; rfl
  | succ k ih => cases args with
    | cons q rest =>
      change OriginalArguments.cons q (NumberedOriginalSourceCodec.groundArguments k (groundValues k rest))=OriginalArguments.cons q rest
      exact congrArg (OriginalArguments.cons q) (ih rest)

theorem groundValuesArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (k : Nat) (f : Fin k → Term Symbol arity Gamma .ground) :
    groundValues k (NumberedOriginalSourceCodec.groundArguments k f)=f := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => f j.succ)) j

theorem translatedGround {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (k : Nat) (f : Fin k → Term Symbol arity Gamma .ground) :
    canonicalArguments 0 (Source.SourceMarkedSyntax.groundArguments k (fun i => embed (f i)))=
      translateArguments (NumberedOriginalSourceCodec.groundArguments k f) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (AuxArguments.cons (translateOriginal (f 0))) (ih (fun i => f i.succ))

theorem translateApp {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (f : Term Symbol arity Gamma (.arrow sigma tau)) (a : Term Symbol arity Gamma sigma) :
    translateOriginal (.app f a)=AuxTerm.ordinary (.application sigma tau)
      (.cons (translateOriginal f) (.cons (translateOriginal a) .nil)) := rfl

theorem translateLam {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (body : Term Symbol arity (sigma::Gamma) tau) : translateOriginal (.lam body)=AuxTerm.lam (translateOriginal body) := rfl

theorem translateRanked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (f : Symbol) (args : Fin (arity f) → Term Symbol arity Gamma .ground) :
    translateOriginal (.ranked f args)=AuxTerm.ordinary (.ranked f)
      (translateArguments (NumberedOriginalSourceCodec.groundArguments (arity f) args)) := by
  exact congrArg (AuxTerm.ordinary (.ranked f)) (translatedGround (arity f) args)

theorem projectionGround {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (k : Nat) (f : Fin k → Term Symbol arity Gamma .ground)
    (h : ∀ i,project (translateOriginal (f i))=some (f i)) :
    projectArguments (translateArguments (NumberedOriginalSourceCodec.groundArguments k f))=
      some (NumberedOriginalSourceCodec.groundArguments k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [NumberedOriginalSourceCodec.groundArguments,translateArguments,projectArguments,h 0,
      headArguments,Option.bind_eq_bind,Option.bind_some,ih (fun i => f i.succ) (fun i => h i.succ),Option.pure_def] <;> rfl

theorem projectionRoundTrip : NumberedOriginalSourceCodecTargets.ActualProjectionRoundTrip := by
  intro Symbol arity Gamma tau s
  induction s with
  | var v => rfl
  | app f a ihf iha =>
    rw [translateApp]
    simp only [project,projectArguments,headArguments,ihf,iha,Option.bind_eq_bind,Option.bind_some,Option.pure_def] <;> rfl
  | lam body ih =>
    rw [translateLam]
    simp only [project,ih,Option.map_some]
  | zeroC => rfl
  | succC => rfl
  | caseC tau => rfl
  | recC tau => rfl
  | ranked f args ih =>
    rw [translateRanked]
    change (projectArguments (translateArguments (NumberedOriginalSourceCodec.groundArguments (arity f) args))).bind
      (fun values => some (Term.ranked f (groundValues (arity f) values)))=some (Term.ranked f args)
    rw [projectionGround (arity f) args ih,Option.bind_some,groundValuesArguments]

theorem argumentProjectionRoundTrip : NumberedOriginalSourceCodecTargets.ActualArgumentProjectionRoundTrip := by
  intro Symbol arity Gamma types args
  induction args with
  | nil => rfl
  | cons q rest ih =>
    simp only [translateArguments,projectArguments,projectionRoundTrip Symbol arity Gamma _ q,ih,Option.bind_eq_bind,Option.bind_some,Option.pure_def] <;> rfl

theorem projectionSound : NumberedOriginalSourceCodecTargets.ActualProjectionSound := by
  intro Symbol arity Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ values : OriginalArguments Symbol arity Gamma types,
      projectArguments args=some values → translateArguments values=args)
  case var v =>
    intro s hs
    have he : Term.var v=s := Option.some.inj hs
    subst s
    rfl
  case lam body ih =>
    intro s hs
    cases hb : project body with
    | none => simp only [project,hb,Option.map_none] at hs; cases hs
    | some b =>
      simp only [project,hb,Option.map_some] at hs
      have he : Term.lam b=s := Option.some.inj hs
      subst s
      rw [translateLam,ih b hb]
  case app => intro s hs; cases hs
  case bottom => intro s hs; cases hs
  case numbered => intro s hs; cases hs
  case ordinary f base ih =>
    cases f with
    | zero =>
      cases base
      intro s hs
      have he : Term.zeroC=s := Option.some.inj hs
      subst s
      rfl
    | succ =>
      cases base
      intro s hs
      have he : Term.succC=s := Option.some.inj hs
      subst s
      rfl
    | cases tau =>
      cases base
      intro s hs
      have he : Term.caseC tau=s := Option.some.inj hs
      subst s
      rfl
    | recursor tau =>
      cases base
      intro s hs
      have he : Term.recC tau=s := Option.some.inj hs
      subst s
      rfl
    | application sigma tau =>
      intro s hs
      cases hb : projectArguments base with
      | none => simp only [project,hb,Option.bind_eq_bind,Option.bind_none] at hs; cases hs
      | some values =>
        have hbase := ih values hb
        cases values with
        | cons f rest => cases rest with
          | cons a rest =>
            cases rest
            simp only [project,hb,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at hs
            have he : Term.app f a=s := Option.some.inj hs
            subst s
            exact congrArg (AuxTerm.ordinary (.application sigma tau)) hbase
    | ranked f =>
      dsimp only [headArguments,headResult] at base ih ⊢
      intro s hs
      change (projectArguments base).bind
        (fun values => some (Term.ranked f (groundValues (arity f) values)))=some s at hs
      cases hb : projectArguments base with
      | none => rw [hb,Option.bind_none] at hs; cases hs
      | some values =>
        have hbase := ih values hb
        rw [hb,Option.bind_some] at hs
        have he : Term.ranked f (groundValues (arity f) values)=s := Option.some.inj hs
        subst s
        rw [translateRanked,groundArgumentsValues]
        exact congrArg (AuxTerm.ordinary (.ranked f)) hbase
  case nil =>
    rename_i Gamma values h
    have he : OriginalArguments.nil=values := Option.some.inj h
    subst values
    rfl
  case cons =>
    rename_i Gamma sigma types q rest ihq ihr values h
    cases hq : project q with
    | none => simp only [projectArguments,hq,Option.bind_eq_bind,Option.bind_none] at h; cases h
    | some q' =>
      cases hr : projectArguments rest with
      | none => simp only [projectArguments,hq,hr,Option.bind_eq_bind,Option.bind_some,Option.bind_eq_bind,Option.bind_none] at h; cases h
      | some rest' =>
        simp only [projectArguments,hq,hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
        have he : OriginalArguments.cons q' rest'=values := Option.some.inj h
        subst values
        exact congrArg₂ AuxArguments.cons (ihq q' hq) (ihr rest' hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecSupportProof
