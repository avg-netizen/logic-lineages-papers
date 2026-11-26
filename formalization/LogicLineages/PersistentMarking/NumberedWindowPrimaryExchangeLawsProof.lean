import LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeHeadProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeLawsProof
open NumberedWindowSyntax NumberedWindowPrimaryExchange
open NumberedWindowPrimaryExchangeTargets NumberedWindowPrimaryExchangeHeadProof
open NumberedWindowTypingBits (annotationList)

theorem termType {S K Q R} (h : ExchangeShape S K Q R) : Q.type = R.type := by
  induction h using ExchangeShape.rec
    (motive_2 := fun qs rs _ => annotationList qs = annotationList rs) with
  | ordinary _ e _ => exact e
  | numbered _ _ => rfl
  | lam _ ih => simp only [NTerm.type,ih]
  | ordinaryBase _ _ => rfl
  | numberedBase _ _ => rfl
  | numberedExtra _ _ => rfl
  | applicationFunction _ _ => rfl
  | applicationArgument _ _ => rfl
  | first _ ih => simp only [annotationList,NArgs.toList,List.map_cons,ih]
  | later _ ih =>
    change _ :: annotationList _ = _ :: annotationList _
    rw [ih]

private theorem argsTypeFixed (S : Spine.Signature) (K : List Ty) (qs rs : NArgs)
    (h : ArgsExchangeShape S K qs rs) : annotationList qs = annotationList rs := by
  cases qs with
  | nil => cases h
  | cons Q qs =>
    cases h with
    | first hQ => simp only [annotationList,NArgs.toList,List.map_cons,termType hQ]
    | later htail =>
      change _ :: annotationList _ = _ :: annotationList _
      rw [argsTypeFixed S K qs _ htail]
termination_by structural qs

theorem argsType {S K qs rs} (h : ArgsExchangeShape S K qs rs) :
    annotationList qs = annotationList rs := argsTypeFixed S K qs rs h

theorem termSymm {S K Q R} (h : ExchangeShape S K Q R) : ExchangeShape S K R Q := by
  induction h using ExchangeShape.rec
    (motive_2 := fun qs rs _ => ArgsExchangeShape S K rs qs) with
  | ordinary hp e hperm => exact .ordinary (headSymm hp) e.symm hperm.symm
  | numbered hp hperm => exact .numbered (headSymm hp) hperm.symm
  | lam _ ih => exact .lam ih
  | ordinaryBase _ ih => exact .ordinaryBase ih
  | numberedBase _ ih => exact .numberedBase ih
  | numberedExtra _ ih => exact .numberedExtra ih
  | applicationFunction _ ih => exact .applicationFunction ih
  | applicationArgument _ ih => exact .applicationArgument ih
  | first _ ih => exact .first ih
  | later _ ih => exact .later ih

private theorem argsSymmFixed (S : Spine.Signature) (K : List Ty) (qs rs : NArgs)
    (h : ArgsExchangeShape S K qs rs) : ArgsExchangeShape S K rs qs := by
  cases qs with
  | nil => cases h
  | cons Q qs =>
    cases h with
    | first hQ => exact .first (termSymm hQ)
    | later ht => exact .later (argsSymmFixed S K qs _ ht)
termination_by structural qs

theorem argsSymm {S K qs rs} (h : ArgsExchangeShape S K qs rs) :
    ArgsExchangeShape S K rs qs := argsSymmFixed S K qs rs h

theorem annotations : ExchangePreservesAnnotations :=
  ⟨fun _ _ _ _ h => termType h,fun _ _ _ _ h => argsType h⟩

theorem symmetric : ExchangeSymmetric :=
  ⟨fun _ _ _ _ h => termSymm h,fun _ _ _ _ h => argsSymm h⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeLawsProof
