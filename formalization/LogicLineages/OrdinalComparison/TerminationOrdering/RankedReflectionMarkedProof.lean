module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionOrdinaryProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionMarkedProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison RankedTree RankedPathOrder RankedReflection RankedReflectionSupportProof

theorem markedNotOrdinary {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (f : Head Symbol) (tau : Ty) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types) (a : Tree Symbol arity Gamma)
    (hs : (⟨tau,.marked f tau base types extras⟩ : Packed Symbol arity Gamma)=pack a) : False := by
  have hh := congrArg shape hs
  change 3=shape (pack a) at hh
  exact packShape a hh.symm

theorem selectCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {sigma tau : Ty}
    (f : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Gamma extraTypes) (types : List Ty)
    (q : MarkedTerm Symbol arity Gamma sigma) (r t : MarkedTerm Symbol arity Gamma tau)
    (suffix : sigma=arrows types tau)
    (hm : (⟨sigma,q⟩ : Packed Symbol arity Gamma)∈argumentList ss++argumentList extras)
    (he : applyOriginalWith q (fun v => .var v) (selfArguments f ss extraTypes extras types) suffix=some r)
    (hi : OrdinaryComparison above ⟨tau,r⟩ ⟨tau,t⟩) :
    OrdinaryComparison above ⟨tau,.marked f tau ss extraTypes extras⟩ ⟨tau,t⟩ ∧
    MarkedComparison above ⟨tau,.marked f tau ss extraTypes extras⟩ ⟨tau,t⟩ := by
  constructor
  · intro a b hs ht
    exact (markedNotOrdinary f tau ss extraTypes extras a hs).elim
  · intro fa aa b hs ht
    obtain ⟨hf,htau,htypes,hbase,hextras⟩ := RankedTreeInversionProof.markedRootEquality
      Symbol arity Gamma f tau ss extraTypes extras fa aa hs
    cases hf
    cases htau
    cases htypes
    have hb := eq_of_heq hbase
    subst ss
    cases extras
    obtain ⟨hempty,i,hr⟩ := RankedTreeProof.exactSelectExecution Symbol arity Gamma fa aa sigma
      Ty.ground q types suffix r hm he
    exact .subterm fa aa i b (hi (aa i) b hr ht)

theorem functionalAbstractionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {sigma tau : Ty}
    (f : Head Symbol) (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (t : MarkedTerm Symbol arity (sigma::Gamma) tau) :
    OrdinaryComparison above ⟨.arrow sigma tau,.marked f (.arrow sigma tau) ss types extras⟩ ⟨.arrow sigma tau,.lam t⟩ ∧
    MarkedComparison above ⟨.arrow sigma tau,.marked f (.arrow sigma tau) ss types extras⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  constructor
  · intro a b hs ht
    have he : Ty.arrow sigma tau=Ty.ground := congrArg Sigma.fst hs
    cases he
  · intro fa aa b hs ht
    have he : Ty.arrow sigma tau=Ty.ground := congrArg Sigma.fst hs
    cases he

theorem copyCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (hp : headAbove above f g)
    (hi : ∀ p∈argumentList ts,MarkedComparison above ⟨p.1,.marked f p.1 ss types extras⟩ p) :
    OrdinaryComparison above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ ∧
    MarkedComparison above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  constructor
  · intro a b hs ht
    exact (markedNotOrdinary f (headResult g) ss types extras a hs).elim
  · intro fa aa b hs ht
    obtain ⟨hf,htau,htypes,hbase,hextras⟩ := RankedTreeInversionProof.markedRootEquality
      Symbol arity Gamma f (headResult g) ss types extras fa aa hs
    cases hf
    cases htypes
    have hb := eq_of_heq hbase
    subst ss
    cases extras
    cases b with
    | var v =>
      have hh := congrArg shape ht
      simp [shape,pack,markedSyntax] at hh
    | node fb bb =>
      obtain ⟨hg,hbase⟩ := RankedTreeInversionProof.ordinaryRootEquality Symbol arity Gamma g ts fb bb ht
      cases hg
      have hb := eq_of_heq hbase
      subst ts
      apply Greater.precedence fa fb aa bb hp
      intro i
      apply hi (pack (bb i))
      · change pack (bb i)∈argumentList (types := List.replicate (arity fb) Ty.ground)
          (groundArguments (arity fb) (fun j => markedSyntax (bb j)))
        rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fb) bb]
        exact List.mem_map.mpr ⟨bb i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
      · exact rfl
      · exact rfl

theorem statCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Gamma types)
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (he : headEquivalent f g)
    (hm : StrictMatching above (argumentList ss) (argumentList ts))
    (hi : ∀ p∈argumentList ts,MarkedComparison above ⟨p.1,.marked f p.1 ss types extras⟩ p) :
    OrdinaryComparison above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ ∧
    MarkedComparison above ⟨headResult g,.marked f (headResult g) ss types extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  constructor
  · intro a b hs ht
    exact (markedNotOrdinary f (headResult g) ss types extras a hs).elim
  · intro fa aa b hs ht
    obtain ⟨hf,htau,htypes,hbase,hextras⟩ := RankedTreeInversionProof.markedRootEquality
      Symbol arity Gamma f (headResult g) ss types extras fa aa hs
    cases hf
    cases htypes
    have hb := eq_of_heq hbase
    subst ss
    cases extras
    cases b with
    | var v =>
      have hh := congrArg shape ht
      simp [shape,pack,markedSyntax] at hh
    | node fb bb =>
      obtain ⟨hg,hbase⟩ := RankedTreeInversionProof.ordinaryRootEquality Symbol arity Gamma g ts fb bb ht
      cases hg
      have hb := eq_of_heq hbase
      subst ts
      have hfg : fa=fb := HeadClass.ranked.inj he
      cases hfg
      apply Greater.multiset fa aa bb
      · exact hm (List.ofFn aa) (List.ofFn bb)
          (RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fa) aa)
          (RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fa) bb)
      · intro i
        apply hi (pack (bb i))
        · change pack (bb i)∈argumentList (types := List.replicate (arity fa) Ty.ground)
            (groundArguments (arity fa) (fun j => markedSyntax (bb j)))
          rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fa) bb]
          exact List.mem_map.mpr ⟨bb i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
        · exact rfl
        · exact rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionMarkedProof
