module
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphCorrectnessProof
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProgramProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof

theorem exactDecreasingGraph : Targets.ExactDecreasingGraph:=by
  intro A B _ _ _ _ children assemble μ hc ha hm f hd hf
  have hroot:∀a,graph children assemble μ a (μ a+1)=[(a,f a)]:=
    graph_root children assemble μ f hd hf
  have hg:Computable (fun a:A=>graph children assemble μ a (μ a+1)):=
    (uniformGraph A B children assemble μ hc ha hm).comp Computable.id
      (Primrec.succ.to_comp.comp hm)
  have hout:Computable (fun a:A=>(graph children assemble μ a (μ a+1)).head?.map Prod.snd):=
    Computable.option_map (Primrec.list_head?.to_comp.comp hg) (Computable.snd.comp Computable.snd)
  have hget:Computable (fun a:A=>((graph children assemble μ a (μ a+1)).head?.map Prod.snd).getD default):=
    Computable.option_getD hout (Computable.const default)
  exact ⟨hroot,hget.of_eq (fun a=>by simp only [hroot,List.head?_cons,Option.map_some,Option.getD_some])⟩
end LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof
