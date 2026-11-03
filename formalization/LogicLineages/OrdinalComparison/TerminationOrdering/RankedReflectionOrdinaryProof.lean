module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionOrdinaryProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder RankedReflection RankedReflectionSupportProof

theorem variableCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {sigma : Ty} (v : Variable Gamma sigma) :
    OrdinaryComparison (arity := arity) above ⟨sigma,.var v⟩ ⟨sigma,.var v⟩ ∧
    MarkedComparison (arity := arity) above ⟨sigma,.var v⟩ ⟨sigma,.var v⟩ := by
  constructor
  · intro a b hs ht
    have he : sigma=Ty.ground := congrArg Sigma.fst hs
    cases he
    cases a with
    | node f args => have hh := congrArg shape hs; simp [shape,pack,markedSyntax,markedRoot] at hh
    | var x =>
      cases b with
      | node f args => have hh := congrArg shape ht; simp [shape,pack,markedSyntax,markedRoot] at hh
      | var y =>
        have hs' : (MarkedTerm.var v : MarkedTerm Symbol arity Gamma .ground)=.var x := by injection hs
        have hxs : v=x := by injection hs'
        have ht' : (MarkedTerm.var v : MarkedTerm Symbol arity Gamma .ground)=.var y := by injection ht
        have hys : v=y := by injection ht'
        cases hxs
        cases hys
        exact .equal _ _ (.var v)
  · intro f args b hs ht
    have hh := congrArg shape hs
    simp [shape,pack,markedSyntax,markedRoot] at hh

theorem abstractionCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {sigma tau : Ty}
    (s t : MarkedTerm Symbol arity (sigma::Gamma) tau) :
    OrdinaryComparison above ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩ ∧
    MarkedComparison above ⟨.arrow sigma tau,.lam s⟩ ⟨.arrow sigma tau,.lam t⟩ := by
  constructor
  · intro a b hs ht
    have he : Ty.arrow sigma tau=Ty.ground := congrArg Sigma.fst hs
    cases he
  · intro f args b hs ht
    have he : Ty.arrow sigma tau=Ty.ground := congrArg Sigma.fst hs
    cases he

theorem funCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f))
    (ts : Arguments Symbol arity Gamma (headArguments arity g)) (matched : List (Packed Symbol arity Gamma))
    (he : headEquivalent f g) (hp : (argumentList ts).Perm matched)
    (him : WeakMatching above (argumentList ss) matched) :
    OrdinaryComparison above ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩ ∧
    MarkedComparison above ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩ := by
  constructor
  · intro a b hs ht
    cases a with
    | var v => have hh := congrArg shape hs; simp [shape,pack,markedSyntax,markedRoot] at hh
    | node fa aa =>
      obtain ⟨hf,hbase⟩ := RankedTreeInversionProof.ordinaryRootEquality Symbol arity Gamma f ss fa aa hs
      cases hf
      have hbase' := eq_of_heq hbase
      subst ss
      cases b with
      | var v => have hh := congrArg shape ht; simp [shape,pack,markedSyntax,markedRoot] at hh
      | node fb bb =>
        obtain ⟨hg,hbase⟩ := RankedTreeInversionProof.ordinaryRootEquality Symbol arity Gamma g ts fb bb ht
        cases hg
        have hbase' := eq_of_heq hbase
        subst ts
        have hfg : fa=fb := HeadClass.ranked.inj he
        cases hfg
        change (argumentList (types := List.replicate (arity fa) Ty.ground)
          (groundArguments (arity fa) (fun i => markedSyntax (bb i)))).Perm matched at hp
        rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fa) bb] at hp
        obtain ⟨ml,hml,hp'⟩ := permutationLift (List.ofFn bb) matched hp
        have hsrc : argumentList (groundArguments (arity fa) (fun i => markedSyntax (aa i)))=
            (List.ofFn aa).map pack := RankedTreeProof.literalArgumentList Symbol arity Gamma (arity fa) aa
        exact funReflection above fa aa bb ml hp' (him _ _ hsrc hml)
  · intro fa aa b hs ht
    have hh := congrArg shape hs
    simp [shape,pack,markedSyntax,markedRoot] at hh

theorem putCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Head Symbol)
    (ss : Arguments Symbol arity Gamma (headArguments arity f)) (t : MarkedTerm Symbol arity Gamma (headResult f))
    (hi : MarkedComparison above ⟨headResult f,.marked f (headResult f) ss [] .nil⟩ ⟨headResult f,t⟩) :
    OrdinaryComparison above ⟨headResult f,.ordinary f ss⟩ ⟨headResult f,t⟩ ∧
    MarkedComparison above ⟨headResult f,.ordinary f ss⟩ ⟨headResult f,t⟩ := by
  constructor
  · intro a b hs ht
    cases a with
    | var v => have hh := congrArg shape hs; simp [shape,pack,markedSyntax,markedRoot] at hh
    | node fa aa =>
      obtain ⟨hf,hbase⟩ := RankedTreeInversionProof.ordinaryRootEquality Symbol arity Gamma f ss fa aa hs
      cases hf
      have hbase' := eq_of_heq hbase
      subst ss
      exact .greater _ _ (hi fa aa b rfl ht)
  · intro fa aa b hs ht
    have hh := congrArg shape hs
    simp [shape,pack,markedSyntax,markedRoot] at hh

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionOrdinaryProof
