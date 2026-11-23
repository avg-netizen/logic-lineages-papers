module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryClassListProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListChecks
open NumberedWindowPrimaryClassListTargets

theorem exact_BoundedFixedPoint : BoundedFixedPoint :=
  NumberedWindowFiniteSaturationBoundProof.bound

theorem exact_BoundedGraphReach : ExactBoundedGraphReach :=
  NumberedWindowFiniteSaturationReachProof.reach

theorem exact_AbstractPrimaryClassList : AbstractExactPrimaryClassList :=
  NumberedWindowPrimaryClassListProof.abstractList

theorem exact_FinitePrimaryClassList : ExactFinitePrimaryClassList :=
  NumberedWindowPrimaryClassListProof.finiteList

theorem exact_FinitePrimaryDecision : ExactFinitePrimaryDecision :=
  NumberedWindowPrimaryClassListProof.decision

#print axioms exact_BoundedFixedPoint
#print axioms exact_BoundedGraphReach
#print axioms exact_AbstractPrimaryClassList
#print axioms exact_FinitePrimaryClassList
#print axioms exact_FinitePrimaryDecision

end LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListChecks
