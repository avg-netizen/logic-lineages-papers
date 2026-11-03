module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedPrefixProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedAbstractionCasesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedRefinementProof SourceExtendedInversionProof

theorem openSharp {Symbol : Type} {arity : Symbol → Nat} {Gamma typesQ typesS : List Ty}
    (f : Head Symbol) (sigma tau : Ty)
    (baseQ baseS : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasQ : Arguments Symbol arity Gamma typesQ) (extrasS : Arguments Symbol arity Gamma typesS)
    (h : Sharp Symbol arity Gamma (.marked f (.arrow sigma tau) baseQ typesQ extrasQ)
      (.marked f (.arrow sigma tau) baseS typesS extrasS)) :
    Sharp Symbol arity (sigma::Gamma) (openMarked f sigma tau baseQ typesQ extrasQ) (openMarked f sigma tau baseS typesS extrasS) := by
  have hw := SourceSharpeningRenameProof.rename h (sigma::Gamma) (Renaming.weaken Gamma sigma)
  have H := SourceSharpeningApplicationProof.fullOriginalApplication Symbol arity (sigma::Gamma) (sigma::Gamma)
    (.arrow sigma tau) tau [sigma] _ _ hw (fun v => .var v) (fun v => .var v)
    (.cons (.var .here) .nil) (.cons (.var .here) .nil) (fun _ v => .var v)
    (.cons (.var .here) (.var .here) .nil .nil (.var .here) .nil) rfl
  simpa only [renameTerm,applyOriginalWith,SourceMarkedBindingProof.markedSubstitutionIdentity.2,
    SourceSharpeningApplication.OutputSharp,openMarked] using H

theorem functionalAbstractionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} {sigma tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma types)
    (t : MarkedTerm Symbol arity (sigma::Gamma) tau)
    (IH : WeakMeaning above ⟨tau,openMarked f sigma tau base types extras⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨.arrow sigma tau,.marked f (.arrow sigma tau) base types extras⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  intro q hRef hOrd
  obtain ⟨src,he,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,typesQ,extrasQ,heq,hbase,hextras⟩ := markedSource src (.marked f (.arrow sigma tau) base types extras) hSharp f base types extras rfl
  have hs : src=MarkedTerm.marked f (.arrow sigma tau) baseQ typesQ extrasQ := by injection heq
  subst src
  apply Weak.fAbs f baseQ typesQ extrasQ t
  exact IH _ (.mk _ _ (openSharp f sigma tau baseQ base extrasQ extras hSharp))
    (unmarkedLambda (.lam t) hOrd sigma tau t rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedAbstractionCasesProof
