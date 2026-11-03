module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree

theorem groundArgumentInjectivity : RankedTreeInversionTargets.GroundArgumentInjectivity := by
  intro Symbol arity Gamma n
  induction n with
  | zero => intro f g h i; exact Fin.elim0 i
  | succ n ih =>
    intro f g h i
    have hh : f 0=g 0 := by injection h
    have hr : groundArguments n (fun i => f i.succ)=groundArguments n (fun i => g i.succ) := by injection h
    exact Fin.cases hh (fun j => ih _ _ hr j) i

private theorem syntaxInjective {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (s t : Tree Symbol arity Gamma) (h : markedSyntax s=markedSyntax t) : s=t := by
  induction s generalizing t with
  | var v =>
    cases t with
    | var w =>
      have hv : v=w := by injection h
      exact congrArg Tree.var hv
    | node f args => cases h
  | node f ss ih =>
    cases t with
    | var v => cases h
    | node g ts =>
      have hg : f=g := by
        have hh := congrArg spineHead h
        simpa only [markedSyntax,spineHead,Option.some.injEq,Head.ranked.injEq] using hh
      subst g
      have ha : groundArguments (arity f) (fun i => markedSyntax (ss i))=
          groundArguments (arity f) (fun i => markedSyntax (ts i)) := by injection h
      have hc := groundArgumentInjectivity Symbol arity Gamma (arity f) _ _ ha
      have hs : ss=ts := funext (fun i => ih i (ts i) (hc i))
      exact congrArg (Tree.node f) hs

theorem embeddingInjectivity : RankedTreeInversionTargets.EmbeddingInjectivity := by
  intro Symbol arity Gamma s t h
  have hs : markedSyntax s=markedSyntax t := by injection h
  exact syntaxInjective s t hs

theorem ordinaryRootEquality : RankedTreeInversionTargets.OrdinaryRootEquality := by
  intro Symbol arity Gamma f base g args h
  have hf : f=.ranked g := by
    have hh := congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) h
    simpa only [pack,markedSyntax,spineHead,Option.some.injEq] using hh
  cases hf
  have hterm : MarkedTerm.ordinary (.ranked g) base=markedSyntax (.node g args) := by injection h
  have hb : base=groundArguments (arity g) (fun i => markedSyntax (args i)) := by injection hterm
  exact ⟨rfl,heq_of_eq hb⟩

theorem markedRootEquality : RankedTreeInversionTargets.MarkedRootEquality := by
  intro Symbol arity Gamma f tau base types extras g args h
  have ht : tau=Ty.ground := congrArg Sigma.fst h
  cases ht
  have hf : f=.ranked g := by
    have hh := congrArg (fun p : Packed Symbol arity Gamma => spineHead p.2) h
    simpa only [markedRoot,spineHead,Option.some.injEq] using hh
  cases hf
  cases h
  exact ⟨rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeInversionProof
