module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedPrefixProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSelectionCasesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedRefinementProof SourceExtendedInversionProof

theorem applicationResult {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} {sigma tau : Ty}
    (q s : MarkedTerm Symbol arity Gamma sigma) (h : Sharp Symbol arity Gamma q s)
    (argsQ argsS : Arguments Symbol arity Gamma types) (ha : ArgumentsSharp Symbol arity Gamma argsQ argsS)
    (suffix : sigma=arrows types tau) (r : MarkedTerm Symbol arity Gamma tau)
    (hr : applyOriginalWith s (fun v => .var v) argsS suffix=some r) :
    ∃ rQ,applyOriginalWith q (fun v => .var v) argsQ suffix=some rQ ∧ Sharp Symbol arity Gamma rQ r := by
  have H := SourceSharpeningApplicationProof.fullOriginalApplication Symbol arity Gamma Gamma sigma tau types q s h
    (fun v => .var v) (fun v => .var v) argsQ argsS (fun _ v => .var v) ha suffix
  rw [hr] at H
  cases he : applyOriginalWith q (fun v => .var v) argsQ suffix with
  | none => simp only [he,SourceSharpeningApplication.OutputSharp] at H
  | some rQ => exact ⟨rQ,rfl,by simpa only [he,SourceSharpeningApplication.OutputSharp] using H⟩

theorem prefixSelectionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma extraTypes types : List Ty} {sigma tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma extraTypes)
    (copies : Arguments Symbol arity Gamma types) (s : MarkedTerm Symbol arity Gamma sigma)
    (r t : MarkedTerm Symbol arity Gamma tau) (suffix : sigma=arrows types tau)
    (hm : (⟨sigma,s⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras)
    (hc : SourceExtendedComparison.PrefixCopies f base extras copies)
    (hr : applyOriginalWith s (fun v => .var v) copies suffix=some r)
    (IH : WeakMeaning above ⟨tau,r⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨tau,.marked f tau base extraTypes extras⟩ ⟨tau,t⟩ := by
  intro q hRef hOrd
  obtain ⟨src,he,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,typesQ,extrasQ,heq,hbase,hextras⟩ := markedSource src (.marked f tau base extraTypes extras) hSharp f base extraTypes extras rfl
  have hs : src=MarkedTerm.marked f tau baseQ typesQ extrasQ := by injection heq
  subst src
  have htuple := SourceExtendedPrefixProof.tupleCopies f baseQ base extrasQ extras tau hSharp copies hc
  have existing : ∀ (sQ : MarkedTerm Symbol arity Gamma sigma),
      (⟨sigma,sQ⟩ : Packed Symbol arity Gamma)∈argumentList baseQ++argumentList extrasQ →
      Sharp Symbol arity Gamma sQ s → Weak Symbol arity above Gamma ⟨tau,.marked f tau baseQ typesQ extrasQ⟩ ⟨tau,t⟩ := by
    intro sQ hmem hqs
    obtain ⟨rQ,happly,hqr⟩ := applicationResult sQ s hqs _ copies htuple suffix r hr
    exact .select f baseQ typesQ extrasQ types sQ rQ t suffix hmem happly (IH _ (.mk rQ r hqr) hOrd)
  rcases List.mem_append.mp hm with hb | he
  · obtain ⟨sQ,hmem,hqs⟩ := argumentMember baseQ base hbase s hb
    exact existing sQ (List.mem_append.mpr (.inl hmem)) hqs
  · have hx := SourceSharpeningCompositionSupportProof.extrasMember f baseQ extrasQ extras hextras ⟨sigma,s⟩ he
    cases hx with
    | existing _ _ _ _ _ sQ _ hmem hqs => exact existing sQ (List.mem_append.mpr (.inr hmem)) hqs
    | whole _ _ _ _ _ _ hqs =>
      obtain ⟨rQ,happly,hqr⟩ := applicationResult _ s hqs _ copies htuple suffix r hr
      have hself := SourceExtendedPrefixProof.selfApplicationRefinement f baseQ extrasQ sigma tau types suffix rQ happly
      have hfinal := SourceSharpeningCompositionProof.transitivity Symbol arity Gamma tau _ _ _ hself hqr
      exact IH _ (.mk _ r hfinal) hOrd

theorem selectionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma extraTypes types : List Ty} {sigma tau : Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extras : Arguments Symbol arity Gamma extraTypes)
    (s : MarkedTerm Symbol arity Gamma sigma) (r t : MarkedTerm Symbol arity Gamma tau)
    (suffix : sigma=arrows types tau)
    (hm : (⟨sigma,s⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras)
    (hr : applyOriginalWith s (fun v => .var v) (selfArguments f base extraTypes extras types) suffix=some r)
    (IH : WeakMeaning above ⟨tau,r⟩ ⟨tau,t⟩) :
    WeakMeaning above ⟨tau,.marked f tau base extraTypes extras⟩ ⟨tau,t⟩ :=
  prefixSelectionCase above f base extras _ s r t suffix hm (SourceExtendedPrefixProof.copiesSelf f base extras types) hr IH

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSelectionCasesProof
