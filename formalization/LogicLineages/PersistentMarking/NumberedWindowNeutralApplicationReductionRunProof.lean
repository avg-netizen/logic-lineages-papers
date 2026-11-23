module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRootProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRootProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRunProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationReductionRootProof (auxRoot)
open NumberedWindowNeutralApplicationReductionRootProof (exact_OriginalNestedAuxRoot)
open NumberedWindowAtomicRawStep (bottomRaw freeRaw)
open NumberedWindowScalarAlgorithm (admitted)
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

/-- Actual whole bottom or an outer tag5 frame on the same raw right
argument. The original residual witness is retained, with the exact two
possible inner auxiliary shapes. -/
def NestedAuxStepShape (D C d t fn a b witness y : Nat) : Prop :=
  (unpackNode witness = some (0,[bottomRoot]) ∧ y = bottomRaw C) ∨
  ∃ child innerOut,
    unpackNode witness = some (5,[child]) ∧
    y = auxRaw D C innerOut b ∧
    AuxStepShape d t fn a child innerOut

private theorem nestedProper (xs : Entries) (s : Settings)
    (D C d t fn a b witness y fuel tag : Nat) (fs : List Nat) (atom : AtomHead fn)
    (seen : unpackNode witness = some (tag,fs))
    (advanced : (iterate (root xs s) fuel
      (false,next tag fs (auxRaw D C (auxRaw d t fn a) b) y)).1 = true) :
    NestedAuxStepShape D C d t fn a b witness y := by
  cases route : next tag fs (auxRaw D C (auxRaw d t fn a) b) y with
  | none => simp [route,terminal] at advanced
  | some frame =>
    obtain ⟨child,target,tagMatch,fields,dst,frameMatch⟩ :=
      auxContext tag fs D C (auxRaw d t fn a) b y frame route
    subst frame
    have inner : run (root xs s) fuel (auxRaw d t fn a) child target = true := by
      simpa only [route,run] using advanced
    have outer : unpackNode witness = some (5,[child]) := by rw [seen,tagMatch,fields]
    exact Or.inr ⟨child,target,outer,dst,suppliedAuxRun xs s d t fn a child target fuel atom inner⟩

theorem exact_OriginalNestedAuxRun (xs : Entries) (s : Settings)
    (D C d t fn a b witness y fuel : Nat) (atom : AtomHead fn)
    (h : run (root xs s) fuel (auxRaw D C (auxRaw d t fn a) b) witness y = true) :
    NestedAuxStepShape D C d t fn a b witness y := by
  cases fuel with
  | zero => simp [run,iterate] at h
  | succ fuel =>
    cases seen : unpackNode witness with
    | none => simp [run,iterate,tick,seen,terminal] at h
    | some node =>
      rcases node with ⟨tag,fs⟩
      cases tag with
      | zero =>
        rcases fs with _ | ⟨w,_ | ⟨a',rest⟩⟩
        · exact nestedProper xs s D C d t fn a b witness y fuel 0 [] atom seen
            (by simpa only [run,iterate,tick,seen] using h)
        · have actual : root xs s (auxRaw D C (auxRaw d t fn a) b) w y = true := by
            simpa only [run,iterate,tick,seen,terminal] using h
          obtain ⟨target,code⟩ := exact_OriginalNestedAuxRoot xs s D C d t fn a b w y actual
          exact Or.inl ⟨by rw [seen,code],target⟩
        · exact nestedProper xs s D C d t fn a b witness y fuel 0 (w::a'::rest) atom seen
            (by simpa only [run,iterate,tick,seen] using h)
      | succ tag =>
        exact nestedProper xs s D C d t fn a b witness y fuel (tag+1) fs atom seen
          (by simpa only [run,iterate,tick,seen] using h)

theorem exact_OriginalNestedAuxStep (xs : Entries) (s : Settings) (Γ : List Nat)
    (requested D C d t fn a b witness y : Nat) (atom : AtomHead fn)
    (h : step xs s Γ requested (auxRaw D C (auxRaw d t fn a) b) witness y = true) :
    admitted s Γ requested y = true ∧ NestedAuxStepShape D C d t fn a b witness y := by
  simp only [step,windowStep,raw,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.2.2.2.2,exact_OriginalNestedAuxRun xs s D C d t fn a b witness y witness atom h.2.2.1⟩

#print axioms exact_OriginalNestedAuxRun
#print axioms exact_OriginalNestedAuxStep
end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRunProof
