module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkedCasesProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedRefinementProof SourceExtendedInversionProof

theorem copyCase {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma types)
    (target : Arguments Symbol arity Gamma (headArguments arity g)) (hp : headAbove above f g)
    (IH : ∀ p∈argumentList target,WeakMeaning above ⟨p.1,.marked f p.1 base types extras⟩ p) :
    WeakMeaning above ⟨headResult g,.marked f (headResult g) base types extras⟩ ⟨headResult g,.ordinary g target⟩ := by
  intro q hRef hOrd
  obtain ⟨src,heq,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,typesQ,extrasQ,hpack,hbase,hextras⟩ := markedSource src _ hSharp f base types extras rfl
  have hs : src=MarkedTerm.marked f (headResult g) baseQ typesQ extrasQ := by injection hpack
  rw [hs]
  apply Weak.copy f g baseQ typesQ extrasQ target hp
  have hAll := allArguments target (unmarkedOrdinary (.ordinary g target) hOrd g target rfl)
  intro p hmem
  exact IH p hmem _ (.mk _ _ (Sharp.marked f p.1 baseQ base typesQ extrasQ types extras hbase hextras)) (hAll p hmem)

theorem statCase {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma types)
    (target : Arguments Symbol arity Gamma (headArguments arity g)) (he : headEquivalent f g)
    (IHm : MultiMeaning above (argumentList base) (argumentList target))
    (IH : ∀ p∈argumentList target,WeakMeaning above ⟨p.1,.marked f p.1 base types extras⟩ p) :
    WeakMeaning above ⟨headResult g,.marked f (headResult g) base types extras⟩ ⟨headResult g,.ordinary g target⟩ := by
  intro q hRef hOrd
  obtain ⟨src,heq,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,typesQ,extrasQ,hpack,hbase,hextras⟩ := markedSource src _ hSharp f base types extras rfl
  have hs : src=MarkedTerm.marked f (headResult g) baseQ typesQ extrasQ := by injection hpack
  rw [hs]
  have hAll := allArguments target (unmarkedOrdinary (.ordinary g target) hOrd g target rfl)
  apply Weak.stat f g baseQ typesQ extrasQ target he
  · exact IHm _ (argumentsRefinement baseQ base hbase) hAll
  · intro p hmem
    exact IH p hmem _ (.mk _ _ (Sharp.marked f p.1 baseQ base typesQ extrasQ types extras hbase hextras)) (hAll p hmem)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkedCasesProof
