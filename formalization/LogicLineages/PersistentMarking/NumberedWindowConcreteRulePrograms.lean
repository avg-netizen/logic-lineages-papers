module
public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSelectProgramProof
import LogicLineages.PersistentMarking.NumberedWindowCopyProgramProof
import LogicLineages.PersistentMarking.NumberedWindowStatRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowBinderRootProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFreshRootPrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteRulePrograms
open NumberedWindowRootDispatchProgramTargets NumberedWindowRootDispatchAlgorithm
open NumberedWindowMarkRootProgramProof

set_option maxHeartbeats 600000 in
theorem primitive (xs heads) : PrimitiveRules (fixed xs heads) where
  mark := markPrim
  lower := lowerPrim
  select := by
    have ex : Primrec (Prod.fst : Selection → Bool) := Primrec.fst
    have idx : Primrec (fun p : Selection => p.2.1) := Primrec.fst.comp Primrec.snd
    have ds : Primrec (fun p : Selection => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have qr : Primrec (fun p : Selection => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact NumberedWindowSelectProgramProof.selectPrim.comp ((ex.pair (idx.pair ds)).pair qr)
  copy := NumberedWindowCopyProgramProof.copyPrim xs heads
  stat := by
    have cert : Primrec (Prod.fst : Key → Nat) := Primrec.fst
    have q : Primrec (fun x : Key => x.2.1) := Primrec.fst.comp Primrec.snd
    have r : Primrec (fun x : Key => x.2.2) := Primrec.snd.comp Primrec.snd
    exact (NumberedWindowStatRootProgramProof.statPrim xs heads).comp (q.pair (cert.pair r))
  fabs := NumberedWindowFreshRootPrograms.fabsPrim
  beta := NumberedWindowBinderRootProgramProof.betaPrim
  bottom := bottomPrim
end LogicLineages.PersistentMarking.NumberedWindowConcreteRulePrograms
