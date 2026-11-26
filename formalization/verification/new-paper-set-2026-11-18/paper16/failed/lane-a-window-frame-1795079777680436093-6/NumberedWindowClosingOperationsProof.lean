import LogicLineages.PersistentMarking.NumberedWindowClosingInventoryProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingOperationsProof
open NumberedWindowSyntax NumberedWindowClosing
open NumberedWindowClosingInventoryProof (annotation)
open NameBridge (Name)

theorem asList (n : Name) (d : Nat) (As : NArgs) :
    (closeArgsAt n d As).toList = As.toList.map (closeAt n d) := by
  cases As with
  | nil => rfl
  | cons q qs => simp only [closeArgsAt,NArgs.toList,List.map_cons,asList n d qs]
termination_by sizeOf As

theorem atIndex (n : Name) (d : Nat) (As : NArgs) (i : Nat) :
    (closeArgsAt n d As).get i = (As.get i).map (closeAt n d) := by
  cases As with
  | nil => rfl
  | cons q qs =>
    cases i with
    | zero => rfl
    | succ i => exact atIndex n d qs i
termination_by sizeOf As

theorem append (n : Name) (d : Nat) (As Bs : NArgs) :
    closeArgsAt n d (As.append Bs) = (closeArgsAt n d As).append (closeArgsAt n d Bs) := by
  cases As with
  | nil => rfl
  | cons q qs =>
    simp only [NArgs.append,closeArgsAt,append n d qs Bs]
termination_by sizeOf As

theorem copies (n : Name) (d : Nat) (f : Head) (k : Nat) (As Bs : NArgs) (types : List Ty) :
    closeArgsAt n d (ownerCopies f k As Bs types) =
      ownerCopies f k (closeArgsAt n d As) (closeArgsAt n d Bs) types := by
  induction types with
  | nil => rfl
  | cons t ts ih => simp only [ownerCopies,closeArgsAt,closeAt,ih]

theorem applyArgs (n : Name) (d : Nat) (As : NArgs) (q : NTerm) :
    applications (closeAt n d q) (closeArgsAt n d As) =
      (applications q As).map (closeAt n d) := by
  cases As with
  | nil => rfl
  | cons a tail =>
    cases h : q.type with
    | ground =>
      simp only [closeArgsAt,applications,annotation,h,Option.map_none]
    | arrow σ τ =>
      by_cases ha : a.type = σ
      · simp only [closeArgsAt,applications,annotation,h,ha,if_true]
        exact applyArgs n d tail (.auxApp σ τ q a)
      · simp only [closeArgsAt,applications,annotation,h,ha,if_false,Option.map_none]
termination_by sizeOf As

end LogicLineages.PersistentMarking.NumberedWindowClosingOperationsProof
