module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceExtendedMarking SourceExtendedMarkingSupportProof

theorem marking : SourceExtendedMarkingTargets.ActualMarking := by
  intro Symbol arity above Gamma s t h
  induction h using SourceExtendedComparison.Weak.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
  case var v => exact .var v
  case abs s t hw ih => exact .abs (star s) (star t) ih
  case fun_ f g ss ts matched he ht hp hm ih =>
    change SourceExtendedComparison.Weak Symbol arity above _
      ⟨headResult f,.marked f (headResult f) ss [] .nil⟩ ⟨headResult g,.marked g (headResult g) ts [] .nil⟩
    rw [ht]
    exact .in_ f g ss ts [] .nil [] .nil matched he hp hm .nil
  case put f ss t hw ih => exact ih
  case select f ss types extras requested q r t suffix hm ha hw ih =>
    exact .select f ss types extras requested q r (star t) suffix hm ha (leftUnmark above r (star t) ih)
  case fAbs f ss types extras t hw ih => exact .fAbs f ss types extras (star t) ih
  case copy f g ss types extras ts hp hw ih =>
    apply SourceExtendedComparison.Weak.marked1 f g ss types extras ts [] .nil hp
    intro p hm
    exact hw p (by simpa only [argumentList,List.append_nil] using hm)
  case stat f g ss types extras ts he hm hw ihm ihw =>
    apply SourceExtendedComparison.Weak.marked2 f g ss types extras ts [] .nil he hm
    intro p hp
    exact hw p (by simpa only [argumentList,List.append_nil] using hp)
  case in_ f g ss ts typesS extrasS typesT extrasT matched he hp hm hx ihm ihx =>
    exact .in_ f g ss ts typesS extrasS typesT extrasT matched he hp hm hx
  case marked1 f g ss typesS extrasS ts typesT extrasT hp hw ih =>
    exact .marked1 f g ss typesS extrasS ts typesT extrasT hp hw
  case marked2 f g ss typesS extrasS ts typesT extrasT he hm hw ihm ihw =>
    exact .marked2 f g ss typesS extrasS ts typesT extrasT he hm hw
  case dropMore f base types moreTypes extras more t hw ih => exact .dropMore f base types moreTypes extras more (star t) ih
  case reorder f base typesS typesT extrasS extrasT t hp hw ih => exact .reorder f base typesS typesT extrasS extrasT (star t) hp ih
  case addPrefixCopies f base types copyTypes extras copies t hp hw ih => exact .addPrefixCopies f base types copyTypes extras copies (star t) hp ih
  case prefixSelect f base extraTypes types extras copies q r t suffix hm hc ha hw ih =>
    exact .prefixSelect f base extraTypes types extras copies q r (star t) suffix hm hc ha (leftUnmark above r (star t) ih)
  all_goals (intros; trivial)

theorem actualLeftUnmark : SourceExtendedMarkingTargets.ActualLeftUnmark := by
  intro Symbol arity above Gamma tau s t h
  exact leftUnmark above s t h

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkingProof
