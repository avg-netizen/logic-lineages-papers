module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionMarkedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionStrictProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder RankedReflection RankedReflectionSupportProof

theorem markCase {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {tau : Ty} (s r t : MarkedTerm Symbol arity Gamma tau)
    (hm : strictMark s=some r) (hi : MarkedComparison above ⟨tau,r⟩ ⟨tau,t⟩) :
    StrictComparison above ⟨tau,s⟩ ⟨tau,t⟩ := by
  intro a b hs ht
  have htype : tau=Ty.ground := congrArg Sigma.fst hs
  cases htype
  have he : s=markedSyntax a := by injection hs
  cases he
  cases a with
  | var v => cases hm
  | node f args =>
    have hr : (markedRoot f args).2=r := Option.some.inj hm
    subst r
    exact hi f args b rfl ht

theorem replacementNil {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (removed : List (Packed Symbol arity Gamma)) : Replacements above removed [] := by
  intro a b ha hb
  have hbnil : b=[] := by simpa using hb.symm
  subst b
  exact .nil a

theorem replacementCons {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (removed : List (Packed Symbol arity Gamma))
    (s t : Packed Symbol arity Gamma) (rest : List (Packed Symbol arity Gamma))
    (hm : s∈removed) (hs : StrictComparison above s t) (hr : Replacements above removed rest) :
    Replacements above removed (t::rest) := by
  intro a b ha hb
  have hm' : s∈a.map pack := ha ▸ hm
  obtain ⟨x,hx,he⟩ := List.mem_map.mp hm'
  cases b with
  | nil => cases hb
  | cons y ys =>
    have ht : t=pack y := (List.cons.inj hb).1
    have hrest : rest=ys.map pack := (List.cons.inj hb).2
    exact .cons a x y ys hx (hs x y he.symm ht) (hr a ys ha hrest)

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionStrictProof
