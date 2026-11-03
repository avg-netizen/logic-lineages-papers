module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedPrefixProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMacroCasesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedRefinementProof SourceExtendedInversionProof

theorem dropCase {Symbol : Type} {arity : Symbol → Nat} {Gamma types moreTypes : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma types)
    (more : Arguments Symbol arity Gamma moreTypes) (t : MarkedTerm Symbol arity Gamma tau)
    (IH : WeakMeaning above ⟨tau,.marked f tau base types extras⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨tau,.marked f tau base (types++moreTypes) (appendArguments extras more)⟩ ⟨tau,t⟩ := by
  intro q hRef hOrd
  apply IH q _ hOrd
  exact transitive hRef (.mk _ _ (SourceSharpeningCompositionProof.additionalExtras Symbol arity Gamma f tau base types moreTypes extras more))

theorem reorderedSharp {Symbol : Type} {arity : Symbol → Nat} {Gamma typesS typesT : List Ty}
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasS : Arguments Symbol arity Gamma typesS) (extrasT : Arguments Symbol arity Gamma typesT)
    (hp : (argumentList extrasS).Perm (argumentList extrasT)) :
    Sharp Symbol arity Gamma (.marked f tau base typesS extrasS) (.marked f tau base typesT extrasT) := by
  apply Sharp.marked f tau base base typesS extrasS typesT extrasT
  · exact SourceSharpeningReflexivityProof.reflexiveArguments base
  · exact SourceSharpeningReflexivityProof.extrasFromArguments f base extrasS extrasT extrasT
      (SourceSharpeningReflexivityProof.reflexiveArguments extrasT) (fun p hp' => hp.symm.subset hp')

theorem reorderCase {Symbol : Type} {arity : Symbol → Nat} {Gamma typesS typesT : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasS : Arguments Symbol arity Gamma typesS) (extrasT : Arguments Symbol arity Gamma typesT)
    (t : MarkedTerm Symbol arity Gamma tau) (hp : (argumentList extrasS).Perm (argumentList extrasT))
    (IH : WeakMeaning above ⟨tau,.marked f tau base typesT extrasT⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨tau,.marked f tau base typesS extrasS⟩ ⟨tau,t⟩ := by
  intro q hRef hOrd
  exact IH q (transitive hRef (.mk _ _ (reorderedSharp f tau base extrasS extrasT hp))) hOrd

theorem prefixCopiesCase {Symbol : Type} {arity : Symbol → Nat} {Gamma types copyTypes : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma types)
    (copies : Arguments Symbol arity Gamma copyTypes) (t : MarkedTerm Symbol arity Gamma tau)
    (hp : SourceExtendedComparison.PrefixCopies f base extras copies)
    (IH : WeakMeaning above ⟨tau,.marked f tau base (types++copyTypes) (appendArguments extras copies)⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨tau,.marked f tau base types extras⟩ ⟨tau,t⟩ := by
  intro q hRef hOrd
  exact IH q (transitive hRef (.mk _ _ (SourceExtendedPrefixProof.copiesExpansion f base extras copies hp tau))) hOrd

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMacroCasesProof
