module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceExtendedTargetDropping
open SourceExtendedTargetDroppingSupportProof SourceSharpeningInversionProof

theorem targetDropping : SourceExtendedTargetDroppingTargets.ActualTargetDropping := by
  intro Symbol arity above Gamma s t h
  induction h using SourceExtendedComparison.Weak.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
  case var v => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case abs s t hw ih => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case fun_ f g ss ts matched he ht hp hm ih => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case put f ss t hw ih =>
    intro g base types moreTypes extras more he
    exact .put f ss (.marked g _ base types extras) (ih g base types moreTypes extras more he)
  case select f ss extraTypes extras requested q r t suffix hm ha hw ih =>
    intro g base types moreTypes pre more he
    exact .select f ss extraTypes extras requested q r (.marked g _ base types pre) suffix hm ha
      (ih g base types moreTypes pre more he)
  case fAbs f ss types extras t hw ih => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case copy f g ss types extras ts hp hw ih => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case stat f g ss types extras ts he hm hw ihm ihw => exact notMarkedEndpoint above _ _ (by intro he; cases he)
  case in_ f g ss ts typesS extrasS typesT extrasT matched he hp hm hx ihm ihx =>
    rename_i Gamma tau
    intro target base types moreTypes extras more htarget
    have hg : g=target := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) htarget)
    cases hg
    have ht : MarkedTerm.marked g tau ts typesT extrasT=MarkedTerm.marked g tau base (types++moreTypes) (appendArguments extras more) := by injection htarget
    cases ht
    exact inDropping above f g ss ts extrasS extras more matched he hp hm hx
  case marked1 f g ss typesS extrasS ts typesT extrasT hp hw ih =>
    rename_i Gamma tau
    intro target base types moreTypes extras more htarget
    have hg : g=target := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) htarget)
    cases hg
    have ht : MarkedTerm.marked g tau ts typesT extrasT=MarkedTerm.marked g tau base (types++moreTypes) (appendArguments extras more) := by injection htarget
    cases ht
    exact .marked1 f g ss typesS extrasS ts types extras hp
      (fun p hmem => hw p (retainedMember ts extras more p hmem))
  case marked2 f g ss typesS extrasS ts typesT extrasT he hm hw ihm ihw =>
    rename_i Gamma tau
    intro target base types moreTypes extras more htarget
    have hg : g=target := Option.some.inj (congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) htarget)
    cases hg
    have ht : MarkedTerm.marked g tau ts typesT extrasT=MarkedTerm.marked g tau base (types++moreTypes) (appendArguments extras more) := by injection htarget
    cases ht
    exact .marked2 f g ss typesS extrasS ts types extras he hm
      (fun p hmem => hw p (retainedMember ts extras more p hmem))
  case dropMore f base types moreTypes extras more t hw ih =>
    intro g targetBase targetTypes targetMoreTypes targetExtras targetMore he
    exact .dropMore f base types moreTypes extras more (.marked g _ targetBase targetTypes targetExtras)
      (ih g targetBase targetTypes targetMoreTypes targetExtras targetMore he)
  case reorder f base typesS typesT extrasS extrasT t hp hw ih =>
    intro g targetBase targetTypes targetMoreTypes targetExtras targetMore he
    exact .reorder f base typesS typesT extrasS extrasT (.marked g _ targetBase targetTypes targetExtras) hp
      (ih g targetBase targetTypes targetMoreTypes targetExtras targetMore he)
  case addPrefixCopies f base types copyTypes extras copies t hp hw ih =>
    intro g targetBase targetTypes targetMoreTypes targetExtras targetMore he
    exact .addPrefixCopies f base types copyTypes extras copies (.marked g _ targetBase targetTypes targetExtras) hp
      (ih g targetBase targetTypes targetMoreTypes targetExtras targetMore he)
  case prefixSelect f base extraTypes types extras copies q r t suffix hm hc ha hw ih =>
    intro g targetBase targetTypes targetMoreTypes targetExtras targetMore he
    exact .prefixSelect f base extraTypes types extras copies q r (.marked g _ targetBase targetTypes targetExtras) suffix hm hc ha
      (ih g targetBase targetTypes targetMoreTypes targetExtras targetMore he)
  all_goals (intros; trivial)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingProof
