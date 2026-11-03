module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceUnmarked OrdinarySyntaxCoverage

theorem groundImage {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (args : OrdinaryArguments Symbol arity Gamma (List.replicate n .ground)) :
    groundArguments n (fun i => embed (groundAt n args i))=embedArguments args := by
  induction n with
  | zero => cases args; rfl
  | succ n ih => cases args with
    | cons q rest =>
      simp only [groundArguments,groundAt,Fin.cases_zero,Fin.cases_succ,embedArguments]
      exact congrArg (Arguments.cons (embed q)) (ih rest)

theorem headReconstruction : OrdinarySyntaxCoverageTargets.ActualHeadReconstruction := by
  intro Symbol arity Gamma f args
  cases f with
  | zero => cases args; rfl
  | succ => cases args; rfl
  | cases tau => cases args; rfl
  | recursor tau => cases args; rfl
  | application sigma tau =>
    cases args with
    | cons f rest => cases rest with
      | cons a last => cases last; rfl
  | ranked s => exact congrArg (MarkedTerm.ordinary (.ranked s)) (groundImage (arity s) args)

theorem termWitness {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    {q : MarkedTerm Symbol arity Gamma tau} (h : Unmarked Symbol arity Gamma q) :
    ∃ t : Term Symbol arity Gamma tau,embed t=q := by
  induction h using Unmarked.rec
    (motive_2 := fun Gamma types args _ => ∃ source : OrdinaryArguments Symbol arity Gamma types,embedArguments source=args)
  case var v => exact ⟨.var v,rfl⟩
  case lam body hb ih =>
    obtain ⟨source,hs⟩ := ih
    exact ⟨.lam source,congrArg MarkedTerm.lam hs⟩
  case ordinary f base hb ih =>
    obtain ⟨source,hs⟩ := ih
    exact ⟨buildTerm f source,(headReconstruction Symbol arity _ f source).trans (congrArg (MarkedTerm.ordinary f) hs)⟩
  case nil => exact ⟨.nil,rfl⟩
  case cons q rest hq hr ihq ihr =>
    obtain ⟨source,hs⟩ := ihq
    obtain ⟨sources,hr⟩ := ihr
    exact ⟨.cons source sources,congrArg₂ Arguments.cons hs hr⟩

theorem unmarkedCoverage : OrdinarySyntaxCoverageTargets.ActualUnmarkedCoverage := by
  intro Symbol arity Gamma tau q
  constructor
  · exact termWitness
  · rintro ⟨source,hs⟩
    exact hs ▸ SourceUnmarkedProof.ordinaryEmbedding Symbol arity Gamma tau source

theorem weakTargetSourceWitness : OrdinarySyntaxCoverageTargets.ActualWeakTargetSourceWitness := by
  intro Symbol arity above Gamma s t h
  exact termWitness (OriginalTargetUnmarkedProof.weakTarget above h)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySyntaxCoverageProof
