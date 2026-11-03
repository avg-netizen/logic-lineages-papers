module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeTargets
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison RankedTree

theorem literalEmbedding : RankedTreeTargets.LiteralEmbedding := by
  intro Symbol arity Gamma t
  induction t with
  | var v => rfl
  | node f args ih =>
    simp only [markedSyntax,ordinary,embed]
    congr 2
    funext i
    exact ih i

theorem literalArgumentList : RankedTreeTargets.LiteralArgumentList := by
  intro Symbol arity Gamma n args
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [groundArguments,argumentList,List.ofFn_succ,List.map_cons]
    exact congrArg (List.cons (pack (args 0))) (ih (fun i => args i.succ))

theorem groundSuffix : RankedTreeTargets.GroundSuffix := by
  intro types tau h
  cases types with
  | nil => exact ⟨rfl,h.symm⟩
  | cons sigma rest => cases h

theorem exactSelectExecution : RankedTreeTargets.ExactSelectExecution := by
  intro Symbol arity Gamma f args sigma tau q types h r hm he
  simp only [argumentList,List.append_nil,literalArgumentList Symbol arity Gamma (arity f) args] at hm
  rcases List.mem_map.mp hm with ⟨child,hchild,hq⟩
  rcases List.mem_ofFn.mp hchild with ⟨i,hi⟩
  subst child
  have hsg : Ty.ground=sigma := congrArg Sigma.fst hq
  cases hsg
  have hq' : markedSyntax (args i)=q := by cases hq; rfl
  cases hq'
  obtain ⟨ht,htau⟩ := groundSuffix types tau h
  subst types
  subst tau
  have hc := Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma
    Ty.ground (markedSyntax (args i))
  have hr : markedSyntax (args i)=r := by
    exact Option.some.inj (hc.symm.trans he)
  exact ⟨rfl,i,congrArg (fun z => (⟨Ty.ground,z⟩ : Packed Symbol arity Gamma)) hr.symm⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeProof
