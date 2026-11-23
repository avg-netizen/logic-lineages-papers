module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationReductionRootProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionContextProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRawRankProof
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView)
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAtomicRawStepChecks (exact_AtomicNoContextDescent exact_ConcreteAtomicRoot)
open NumberedWindowNeutralApplicationReductionRootProof (exact_OriginalNonLambdaAuxRoot)
open NumberedWindowAtomicApplicationReductionContextProof (auxContext)
open NumberedWindowAtomicApplicationReductionWrappedProof (suppliedRoot terminal)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (next tick iterate run windowStep raw)
open NumberedWindowConcreteCheckers (root step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings admitted)

/-- Rank of the actual raw neutral left spine only. Every auxiliary
adds one; bare free is one and bare bottom zero. Raw right arguments
are kept in the physical code, but do not contribute to this rank. -/
inductive NeutralSpineRank : Nat → Nat → Prop where
  | free (stored name : Nat) : NeutralSpineRank (freeRaw stored name) 1
  | bottom (stored : Nat) : NeutralSpineRank (bottomRaw stored) 0
  | aux {fn n : Nat} (dom cod arg : Nat) :
      NeutralSpineRank fn n → NeutralSpineRank (auxRaw dom cod fn arg) (n+1)

private theorem nonLambda {q rank : Nat} (s : NeutralSpineRank q rank) :
    ∃ tag fs, unpackNode q = some (tag,fs) ∧ tag ≠ 2 := by
  cases s with
  | free stored name => exact ⟨0,[stored,name],freeView stored name,by decide⟩
  | bottom stored => exact ⟨3,[stored],bottomView stored,by decide⟩
  | aux dom cod arg _ => exact ⟨6,_,auxView dom cod _ arg,by decide⟩

private theorem properRank (xs : Entries) (s : Settings)
    (dom cod fn arg y n fuel tag : Nat) (fields : List Nat)
    (lower : ∀ child result residual, run (root xs s) residual fn child result = true →
      ∃ n', NeutralSpineRank result n' ∧ n' < n)
    (h : (iterate (root xs s) fuel
      (false,next tag fields (auxRaw dom cod fn arg) y)).1 = true) :
    ∃ n', NeutralSpineRank y n' ∧ n' < n+1 := by
  cases route : next tag fields (auxRaw dom cod fn arg) y with
  | none => simp [route,terminal] at h
  | some frame =>
    obtain ⟨child,result,_,_,dst,same⟩ := auxContext tag fields dom cod fn arg y frame route
    subst frame
    have runChild : run (root xs s) fuel fn child result = true := by
      simpa only [route,run] using h
    obtain ⟨rank',shape,descending⟩ := lower child result fuel runChild
    rw [dst]
    exact ⟨rank'+1,.aux dom cod arg shape,Nat.succ_lt_succ descending⟩

/-- One accepted actual raw run preserves neutrality of the exact
target raw code and strictly lowers actual finite neutral-spine rank. -/
theorem exact_OriginalNeutralSpineRawRank (xs : Entries) (s : Settings)
    {q rank : Nat} (shape : NeutralSpineRank q rank) :
    ∀ witness y fuel, run (root xs s) fuel q witness y = true →
      ∃ rank', NeutralSpineRank y rank' ∧ rank' < rank := by
  induction shape with
  | free stored name =>
    intro witness y fuel h
    obtain ⟨cert,_,accepted⟩ := suppliedRoot (root xs s) fuel (freeRaw stored name) witness y
      (fun tag fs => exact_AtomicNoContextDescent.1 tag fs stored name y) h
    obtain ⟨dst,_⟩ := exact_ConcreteAtomicRoot.1 xs s stored name cert y accepted
    rw [dst]
    exact ⟨0,.bottom stored,by decide⟩
  | bottom stored =>
    intro witness y fuel h
    obtain ⟨cert,_,accepted⟩ := suppliedRoot (root xs s) fuel (bottomRaw stored) witness y
      (fun tag fs => exact_AtomicNoContextDescent.2 tag fs stored y) h
    rw [exact_ConcreteAtomicRoot.2 xs s stored cert y] at accepted
    cases accepted
  | @aux fn n dom cod arg fnShape ih =>
    intro witness y fuel h
    cases fuel with
    | zero => simp [run,iterate] at h
    | succ fuel =>
      cases seen : unpackNode witness with
      | none => simp [run,iterate,tick,seen,terminal] at h
      | some node =>
        rcases node with ⟨tag,fields⟩
        cases tag with
        | zero =>
          rcases fields with _ | ⟨w,_ | ⟨a,rest⟩⟩
          · exact properRank xs s dom cod fn arg y n fuel 0 [] ih
              (by simpa only [run,iterate,tick,seen] using h)
          · have actual : root xs s (auxRaw dom cod fn arg) w y = true := by
              simpa only [run,iterate,tick,seen,terminal] using h
            obtain ⟨ft,fs,view,notLambda⟩ := nonLambda fnShape
            obtain ⟨dst,_⟩ := exact_OriginalNonLambdaAuxRoot xs s dom cod fn arg w y ft fs view notLambda actual
            rw [dst]
            exact ⟨0,.bottom cod,Nat.zero_lt_succ n⟩
          · exact properRank xs s dom cod fn arg y n fuel 0 (w::a::rest) ih
              (by simpa only [run,iterate,tick,seen] using h)
        | succ tag =>
          exact properRank xs s dom cod fn arg y n fuel (tag+1) fields ih
            (by simpa only [run,iterate,tick,seen] using h)

theorem exact_OriginalNeutralSpineStepRank (xs : Entries) (s : Settings) (Γ : List Nat)
    (requested q witness y rank : Nat) (shape : NeutralSpineRank q rank)
    (h : step xs s Γ requested q witness y = true) :
    admitted s Γ requested y = true ∧ ∃ rank', NeutralSpineRank y rank' ∧ rank' < rank := by
  simp only [step,windowStep,raw,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.2.2.2.2,exact_OriginalNeutralSpineRawRank xs s shape witness y witness h.2.2.1⟩

#print axioms exact_OriginalNeutralSpineRawRank
#print axioms exact_OriginalNeutralSpineStepRank
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRawRankProof
