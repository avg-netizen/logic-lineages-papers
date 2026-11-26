module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRootProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRunProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationReductionRootProof (auxRoot)
open NumberedWindowAtomicApplicationReductionContextProof (auxContext)
open NumberedWindowAtomicApplicationReductionWrappedProof (terminal suppliedRoot)
open NumberedWindowAtomicRawStep (bottomRoot)
open NumberedWindowAtomicRawStepChecks (exact_AtomicNoContextDescent exact_ConcreteAtomicRoot)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (next tick iterate run windowStep raw)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

private theorem fromProper (xs : Entries) (s : Settings) (dom cod fn arg witness y fuel tag : Nat)
    (fs : List Nat) (atom : AtomHead fn)
    (seen : unpackNode witness = some (tag,fs))
    (advanced : (iterate (root xs s) fuel (false,next tag fs (auxRaw dom cod fn arg) y)).1 = true) :
    AuxStepShape dom cod fn arg witness y := by
  cases route : next tag fs (auxRaw dom cod fn arg) y with
  | none => simp [route,terminal] at advanced
  | some frame =>
    obtain ⟨child,fnOut,tagMatch,fields,dst,frameMatch⟩ :=
      auxContext tag fs dom cod fn arg y frame route
    subst frame
    have nested : run (root xs s) fuel fn child fnOut = true := by
      simpa only [route,run] using advanced
    have outer : unpackNode witness = some (5,[child]) := by rw [seen,tagMatch,fields]
    cases atom with
    | free stored name =>
      obtain ⟨r,wrapper,actualRoot⟩ :=
        suppliedRoot (root xs s) fuel _ child fnOut
          (fun k ws => exact_AtomicNoContextDescent.1 k ws stored name fnOut) nested
      obtain ⟨bottom,cert⟩ := exact_ConcreteAtomicRoot.1 xs s stored name r fnOut actualRoot
      exact Or.inr ⟨stored,name,child,rfl,outer,by rw [← cert]; exact wrapper,
        by rw [← bottom]; exact dst⟩
    | bottom stored =>
      obtain ⟨r,_,actualRoot⟩ :=
        suppliedRoot (root xs s) fuel _ child fnOut
          (fun k ws => exact_AtomicNoContextDescent.2 k ws stored fnOut) nested
      rw [exact_ConcreteAtomicRoot.2 xs s stored r fnOut] at actualRoot
      cases actualRoot

private theorem suppliedAuxRun (xs : Entries) (s : Settings) (dom cod fn arg witness y fuel : Nat)
    (atom : AtomHead fn) (h : run (root xs s) fuel (auxRaw dom cod fn arg) witness y = true) :
    AuxStepShape dom cod fn arg witness y := by
  cases fuel with
  | zero => simp [run,iterate] at h
  | succ fuel =>
    cases seen : unpackNode witness with
    | none => simp [run,iterate,tick,seen,terminal] at h
    | some node =>
      rcases node with ⟨tag,fs⟩
      cases tag with
      | zero =>
        rcases fs with _ | ⟨w,_ | ⟨a,rest⟩⟩
        · exact fromProper xs s dom cod fn arg witness y fuel 0 [] atom seen
            (by simpa only [run,iterate,tick,seen] using h)
        · have actual : root xs s (auxRaw dom cod fn arg) w y = true := by
            simpa only [run,iterate,tick,seen,terminal] using h
          obtain ⟨target,code⟩ := auxRoot xs s dom cod fn arg w y atom actual
          exact Or.inl ⟨by rw [seen,code],target⟩
        · exact fromProper xs s dom cod fn arg witness y fuel 0 (w::a::rest) atom seen
            (by simpa only [run,iterate,tick,seen] using h)
      | succ tag =>
        exact fromProper xs s dom cod fn arg witness y fuel (tag+1) fs atom seen
          (by simpa only [run,iterate,tick,seen] using h)

theorem concreteStep : ExactAtomicAuxConcreteStep := by
  intro xs s Γ requested dom cod fn arg witness y atom h
  simp only [step,windowStep,raw,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.2.2.2.2,suppliedAuxRun xs s dom cod fn arg witness y witness atom h.2.2.1⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRunProof
