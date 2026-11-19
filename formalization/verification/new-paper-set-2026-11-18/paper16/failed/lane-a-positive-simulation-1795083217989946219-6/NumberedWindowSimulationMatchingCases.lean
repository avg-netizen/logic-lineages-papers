import LogicLineages.PersistentMarking.NumberedWindowSimulationQuoteSupport
import LogicLineages.PersistentMarking.NumberedWindowSimulationSourceSplitProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementTraces
import LogicLineages.PersistentMarking.NumberedWindowTraceConsProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationMatchingCases
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowOrdinaryTranslation
open NumberedWindowTraceAlgebra NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationSourceSplitProof NumberedWindowSimulationPlacement
open NumberedWindowSimulationQuoteSupport
open NumberedWindowTraceTypingProof (argsStart)

theorem nil (S : Spine.Signature) (K : List Ty) : Job S K .matchingNil := by
  intro h n As hn hA
  cases hA
  exact ⟨.nil,.nil,.nil,rfl,⟨.done .nil⟩⟩

theorem cons (S : Spine.Signature) (K : List Ty)
    (x y : Spine.Expr) (xs targets rest : Spine.Args) (hr : Spine.Remove targets y rest)
    (d : Tree S (.weak x y)) (more : Tree S (.matching xs rest))
    (ih : Job S K d) (ihM : Job S K more) :
    Job S K (.matchingCons x y xs targets rest hr d more) := by
  intro h n As hn hA
  have hb : max (budget d) (budget more) ≤ n := hn
  have hd : Foot K d := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_left _ hp))
  have hm : Foot K more := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  cases hA with
  | cons hq hs =>
    obtain ⟨Y,hY,p,_⟩ := ih hd n _ (Nat.le_trans (Nat.le_max_left _ _) hb) hq
    obtain ⟨beginTail,endTail,permTail,hTail,⟨tPath⟩⟩ :=
      ihM hm n _ (Nat.le_trans (Nat.le_max_right _ _) hb) hs
    have p' := align hY p
    obtain ⟨hPath,_⟩ := NumberedWindowTraceConsProof.cons S K E y.type [] _ Y .nil .nil p'
      (.done .nil)
    obtain ⟨place,hQuote⟩ := quotedPlacement (removeAsSplit hr) (.cons Y .nil) endTail
      (quoteCons hY rfl) hTail
    have placed := NumberedWindowSimulationPlacementTraces.both place hPath tPath
    have hp := NumberedWindowSimulationPlacementProof.permutation place (argsStart hPath) (argsStart tPath)
    exact ⟨_,_,(List.Perm.cons _ permTail).trans hp.symm,hQuote,placed⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationMatchingCases
