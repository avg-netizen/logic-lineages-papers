module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecProof
open Source NumberedAuxiliaryCoding NumberedTypedRequests NumberedRequestPresentation
open NumberedRequestExpansionPrimrecSupportProof

theorem expansionPrimitive : NumberedRequestExpansionPrimrecTargets.ActualRequestExpansionPrimitive := by
  intro n arity
  have ht : Primrec (fun p : List Ty × Ty × Code (Fin n) =>
      expand arity (.term p.1 p.2.1 p.2.2)) := by
    apply ((termViewPrimitive n arity).comp
      ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
        ((NumberedCodeViewProof.viewPrimitive n).comp (Primrec.snd.comp Primrec.snd)))).of_eq
    intro p
    exact termViewExact n arity p.1 p.2.1 p.2.2
  have ha : Primrec (fun p : List Ty × List Ty × Code (Fin n) =>
      expand arity (.arguments p.1 p.2.1 p.2.2)) := by
    apply ((argumentsViewPrimitive n).comp
      ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
        ((NumberedCodeViewProof.viewPrimitive n).comp (Primrec.snd.comp Primrec.snd)))).of_eq
    intro p
    exact argumentsViewExact n arity p.1 p.2.1 p.2.2
  have h : Primrec (fun data : RequestData n => data.elim
      (fun p => expand arity (.term p.1 p.2.1 p.2.2))
      (fun p => expand arity (.arguments p.1 p.2.1 p.2.2))) :=
    NumberedHeadCodecPrimrecSupportProof.sumElim ht ha
  exact (h.comp (requestToPrimitive n)).of_eq (by intro request; cases request <;> rfl)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecProof
