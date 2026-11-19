import LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverPermProof
open NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax

private def weight (Q : NTerm) (b : Bounds) : Bounds :=
  ⟨(termBounds Q).nodes + 1 + b.nodes,max (termBounds Q).numeral b.numeral⟩

private theorem comm (Q R : NTerm) (b : Bounds) :
    weight R (weight Q b) = weight Q (weight R b) := by
  simp only [weight,Bounds.mk.injEq]
  exact ⟨by omega,Nat.max_left_comm ..⟩

private theorem fold : ∀ qs : NArgs,
    argsBounds qs = qs.toList.foldr weight ⟨0,0⟩
  | .nil => rfl
  | .cons Q qs => by simp only [argsBounds,NArgs.toList,List.foldr_cons,← fold qs,weight]

theorem perm {qs rs : NArgs} (h : qs.toList.Perm rs.toList) :
    argsBounds qs = argsBounds rs :=
  (fold qs).trans ((h.foldr_eq' (fun Q _ R _ b => comm Q R b) _).trans (fold rs).symm)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverPermProof
