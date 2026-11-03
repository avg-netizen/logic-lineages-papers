module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison SourceExtendedTargetDropping

theorem notMarkedEndpoint {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma)
    (h : SourceSharpeningInversionProof.rootShape t≠3) : DropMeaning above s t := by
  intro g base types moreTypes extras more he
  exact (h (congrArg SourceSharpeningInversionProof.rootShape he)).elim

theorem argumentListAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys) :
    argumentList (appendArguments a b)=argumentList a++argumentList b := by
  induction xs with
  | nil => cases a; rfl
  | cons tau xs ih => cases a with
    | cons q rest => exact congrArg (List.cons ⟨tau,q⟩) (ih rest)

theorem splitArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    ∀ (types : List Ty) (args : Arguments Symbol arity Gamma types) (left right : List (Packed Symbol arity Gamma)),
    argumentList args=left++right →
    ∃ (xs ys : List Ty) (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys),
      (⟨types,args⟩ : Sigma (Arguments Symbol arity Gamma))=⟨xs++ys,appendArguments a b⟩ ∧
      argumentList a=left ∧ argumentList b=right := by
  intro types args left
  induction left generalizing types with
  | nil => intro right he; exact ⟨[],types,.nil,args,rfl,rfl,he⟩
  | cons p left ih =>
    intro right he
    cases args with
    | nil => cases he
    | @cons Gamma tau types q rest =>
      obtain ⟨hq,hr⟩ := List.cons.inj he
      obtain ⟨xs,ys,a,b,hs,ha,hb⟩ := ih types rest right hr
      cases hs
      exact ⟨tau::xs,ys,.cons q a,b,rfl,congrArg₂ List.cons hq ha,hb⟩

theorem matchingToForall {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts) :
    List.Forall₂ (SourceExtendedComparison.Weak Symbol arity above Gamma) ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact .nil
  | cons s ss ih => cases h with
    | cons s t ss ts hw hr => exact .cons hw (ih hr)

theorem matchingFromForall {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : List.Forall₂ (SourceExtendedComparison.Weak Symbol arity above Gamma) ss ts) :
    SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts := by
  induction h with
  | nil => exact .nil
  | @cons s t ss ts hw hr ih => exact .cons s t ss ts hw ih

theorem inDropping {Symbol : Type} {arity : Symbol → Nat} {Gamma typesS types moreTypes : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (f g : Head Symbol)
    (baseS : Arguments Symbol arity Gamma (headArguments arity f))
    (baseT : Arguments Symbol arity Gamma (headArguments arity g))
    (extrasS : Arguments Symbol arity Gamma typesS)
    (extras : Arguments Symbol arity Gamma types) (more : Arguments Symbol arity Gamma moreTypes)
    (matched : List (Packed Symbol arity Gamma)) (he : headEquivalent f g)
    (hp : (argumentList baseT).Perm matched)
    (hm : SourceExtendedComparison.WeakMatch Symbol arity above Gamma (argumentList baseS) matched)
    (hx : SourceExtendedComparison.WeakMatch Symbol arity above Gamma (argumentList extrasS) (argumentList (appendArguments extras more))) :
    SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,.marked f tau baseS typesS extrasS⟩ ⟨tau,.marked g tau baseT types extras⟩ := by
  have hf := matchingToForall above hx
  rw [argumentListAppend] at hf
  obtain ⟨left,right,hs,hl,hr⟩ := SourceExtendedListProof.splitRight
    (SourceExtendedComparison.Weak Symbol arity above Gamma) (argumentList extras) (argumentList more) (argumentList extrasS) hf
  obtain ⟨xs,ys,a,b,hargs,ha,hb⟩ := splitArguments typesS extrasS left right hs
  cases hargs
  apply SourceExtendedComparison.Weak.dropMore f baseS xs ys a b _
  apply SourceExtendedComparison.Weak.in_ f g baseS baseT xs a types extras matched he hp hm
  apply matchingFromForall above
  simpa only [ha] using hl

theorem retainedMember {Symbol : Type} {arity : Symbol → Nat} {Gamma baseTypes types moreTypes : List Ty}
    (base : Arguments Symbol arity Gamma baseTypes) (extras : Arguments Symbol arity Gamma types)
    (more : Arguments Symbol arity Gamma moreTypes) (p : Packed Symbol arity Gamma)
    (hp : p∈argumentList base++argumentList extras) :
    p∈argumentList base++argumentList (appendArguments extras more) := by
  rw [argumentListAppend,←List.append_assoc]
  exact List.mem_append_left _ hp

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedTargetDroppingSupportProof
