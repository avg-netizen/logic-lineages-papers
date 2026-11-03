module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedListProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedRefinementProof SourceExtendedInversionProof

theorem variableCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (v : Variable Gamma tau) :
    WeakMeaning (arity := arity) above ⟨tau,.var v⟩ ⟨tau,.var v⟩ := by
  intro q hRef hOrd
  obtain ⟨src,he,hSharp⟩ := unpack hRef
  subst q
  have hv := SourceSharpeningReflectionProof.unmarkedIdentity Symbol arity Gamma tau src (.var v) (.var v) hSharp
  rw [hv]
  exact .var v

theorem abstractionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (above : Symbol → Symbol → Prop) (s t : MarkedTerm Symbol arity (sigma::Gamma) tau)
    (IH : WeakMeaning above ⟨tau,s⟩ ⟨tau,t⟩) : WeakMeaning above ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  intro q hRef hOrd
  obtain ⟨src,he,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨body,hbodyEq,hbody⟩ := SourceSharpeningInversionProof.lambdaInversion src (.lam s) hSharp sigma tau s rfl
  have heq : src=MarkedTerm.lam body := by injection hbodyEq
  rw [heq]
  exact .abs body t (IH ⟨tau,body⟩ (.mk body s hbody) (unmarkedLambda (.lam t) hOrd sigma tau t rfl))

theorem funCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (matched : List (Packed Symbol arity Gamma))
    (he : headEquivalent f g) (hType : headResult f=headResult g) (hp : (argumentList ts).Perm matched)
    (IH : MatchMeaning above (argumentList ss) matched) :
    WeakMeaning above ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩ := by
  intro q hRef hOrd
  obtain ⟨src,heq,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,hpack,hbase⟩ := SourceSharpeningInversionProof.ordinaryInversion src (.ordinary f ss) hSharp f ss rfl
  have hs : src=MarkedTerm.ordinary f baseQ := by injection hpack
  rw [hs]
  apply Weak.fun_ f g baseQ ts matched he hType hp
  apply IH (argumentList baseQ) (argumentsRefinement baseQ ss hbase)
  have hAll := allArguments ts (unmarkedOrdinary (.ordinary g ts) hOrd g ts rfl)
  exact fun p hp' => hAll p (hp.symm.subset hp')

theorem putCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (t : MarkedTerm Symbol arity Gamma (headResult f))
    (IH : WeakMeaning above ⟨headResult f,.marked f (headResult f) base [] .nil⟩ ⟨headResult f,t⟩) :
    WeakMeaning above ⟨headResult f,.ordinary f base⟩ ⟨headResult f,t⟩ := by
  intro q hRef hOrd
  obtain ⟨src,heq,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨baseQ,hpack,hbase⟩ := SourceSharpeningInversionProof.ordinaryInversion src (.ordinary f base) hSharp f base rfl
  have hs : src=MarkedTerm.ordinary f baseQ := by injection hpack
  rw [hs]
  apply Weak.put f baseQ t
  apply IH _ (.mk _ _ (Sharp.marked f (headResult f) baseQ base [] .nil [] .nil hbase (.nil f baseQ [] .nil))) hOrd

theorem noMarkedTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (above : Symbol → Symbol → Prop) (s : Packed Symbol arity Gamma)
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) : WeakMeaning above s ⟨tau,.marked f tau base types extras⟩ := by
  intro q hRef hOrd
  exact (notMarked f tau base extras hOrd).elim

theorem strictCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (s r t : MarkedTerm Symbol arity Gamma tau)
    (hm : strictMark s=some r) (IH : WeakMeaning above ⟨tau,r⟩ ⟨tau,t⟩) :
    StrictMeaning above ⟨tau,s⟩ ⟨tau,t⟩ := by
  intro q hRef hOrd
  obtain ⟨src,heq,hSharp⟩ := unpack hRef
  subst q
  obtain ⟨marked,hmark,hmarked⟩ := SourceSharpeningReflectionProof.markabilityReflection Symbol arity Gamma tau src s r hSharp hm
  exact .mark src marked t hmark (IH _ (.mk marked r hmarked) hOrd)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedOrdinaryCasesProof
