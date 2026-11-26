import LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextBuild

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessComplete
open NumberedWindowSyntax NumberedWindowRules
open NumberedWindowRawWitnessRootBuild

theorem term {S K Q R} (h : RawStep S K Q R) : TermCert S K Q R := by
  induction h using RawStep.rec (motive_2 := fun qs rs _ => ArgsCert S K qs rs) with
  | mark => exact NumberedWindowRawWitnessRootBuild.mark
  | lower => exact NumberedWindowRawWitnessRootBuild.lower
  | select hg ht ha => exact NumberedWindowRawWitnessRootBuild.select hg ht ha
  | copy hp hg => exact NumberedWindowRawWitnessRootBuild.copy hp hg
  | stat he hg hp => exact NumberedWindowRawWitnessRootBuild.stat he hg hp
  | fabs => exact NumberedWindowRawWitnessRootBuild.fabs
  | beta => exact NumberedWindowRawWitnessRootBuild.beta
  | bottom hn => exact NumberedWindowRawWitnessRootBuild.bottom hn
  | lam _ ih => exact NumberedWindowRawWitnessContextBuild.lam ih
  | ordinaryBase _ ih => exact NumberedWindowRawWitnessContextBuild.ordinaryBase ih
  | numberedBase _ ih => exact NumberedWindowRawWitnessContextBuild.numberedBase ih
  | numberedExtra _ ih => exact NumberedWindowRawWitnessContextBuild.numberedExtra ih
  | auxFunction _ ih => exact NumberedWindowRawWitnessContextBuild.auxFunction ih
  | first _ ih => exact NumberedWindowRawWitnessContextBuild.first ih
  | later _ ih => exact NumberedWindowRawWitnessContextBuild.later ih

theorem args {S K qs rs} (h : RawArgsStep S K qs rs) : ArgsCert S K qs rs := by
  induction h using RawArgsStep.rec (motive_1 := fun Q R _ => TermCert S K Q R) with
  | mark => exact NumberedWindowRawWitnessRootBuild.mark
  | lower => exact NumberedWindowRawWitnessRootBuild.lower
  | select hg ht ha => exact NumberedWindowRawWitnessRootBuild.select hg ht ha
  | copy hp hg => exact NumberedWindowRawWitnessRootBuild.copy hp hg
  | stat he hg hp => exact NumberedWindowRawWitnessRootBuild.stat he hg hp
  | fabs => exact NumberedWindowRawWitnessRootBuild.fabs
  | beta => exact NumberedWindowRawWitnessRootBuild.beta
  | bottom hn => exact NumberedWindowRawWitnessRootBuild.bottom hn
  | lam _ ih => exact NumberedWindowRawWitnessContextBuild.lam ih
  | ordinaryBase _ ih => exact NumberedWindowRawWitnessContextBuild.ordinaryBase ih
  | numberedBase _ ih => exact NumberedWindowRawWitnessContextBuild.numberedBase ih
  | numberedExtra _ ih => exact NumberedWindowRawWitnessContextBuild.numberedExtra ih
  | auxFunction _ ih => exact NumberedWindowRawWitnessContextBuild.auxFunction ih
  | first _ ih => exact NumberedWindowRawWitnessContextBuild.first ih
  | later _ ih => exact NumberedWindowRawWitnessContextBuild.later ih

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessComplete
