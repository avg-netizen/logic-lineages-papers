module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedSelectCertificate

theorem selectCertificates : NumberedSelectCertificateTargets.ActualSelectCertificates := by
  intro n arity Gamma q r
  constructor
  · rintro ⟨types,index,h⟩
    obtain ⟨tau,q⟩ := q
    cases q with
    | var => simp [selectTarget] at h
    | lam => simp [selectTarget] at h
    | app => simp [selectTarget] at h
    | bottom => simp [selectTarget] at h
    | ordinary => simp [selectTarget] at h
    | numbered k f tau base extraTypes extras =>
      cases k with
      | zero => simp [selectTarget] at h
      | succ k =>
        cases he : (argumentList base++argumentList extras)[index]? with
        | none => simp [selectTarget,he] at h
        | some selected =>
          obtain ⟨sigma,selected⟩ := selected
          simp only [selectTarget,he] at h
          split at h
          next ht =>
            cases ht
            cases h
            exact .select k f tau base extraTypes extras types selected (List.mem_of_getElem? he)
          next => contradiction
  · intro h
    cases h with
    | select k f tau base extraTypes extras types selected hm =>
      obtain ⟨index,he⟩ := List.mem_iff_getElem?.mp hm
      exact ⟨types,index,by simp [selectTarget,he]⟩

theorem selectCertificateSound : NumberedSelectCertificateTargets.ActualSelectCertificateSound := by
  intro n arity symbols S hc Gamma above types index q r h hq
  have hi := (selectCertificates n arity Gamma q r).mp ⟨types,index,h⟩
  cases hi with
  | select k f tau base extraTypes extras types selected hm =>
    have hs : WindowStep (Fin n) arity symbols S above Gamma tau
        (.numbered (k+1) f tau base extraTypes extras) (applyArguments selected (selfArguments k f base extraTypes extras types)) :=
      .select k f base extraTypes extras types selected hm
    exact ⟨NumberedWindowReductionProof.stepGood symbols S hc hs hq,tau,_,_,rfl,rfl,hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateProof
