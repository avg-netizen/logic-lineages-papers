module
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof
/-! The finite-frontier argument follows the constructive graph method in
Mathlib.Computability.Primrec.List.nat_omega_rec'; interfaces are kept separate
so genuinely computable closed head evaluations need not be primitive recursive. -/

private theorem frontier_succ {A:Type} (children:A→List A) (a:A) (n:Nat):
    frontier children a (n+1)=(frontier children a n).flatMap children:=
  Function.iterate_succ_apply' _ _ _

private theorem frontier_bound {A:Type} (children:A→List A) (μ:A→Nat)
    (hd:∀a,∀b∈children a,μ b<μ a) (a:A) (n:Nat):
    ∀b∈frontier children a n,μ b<μ a+1-n:=by
  induction n with
  | zero=>
    intro b hb
    have he:b=a:=by simpa [frontier] using hb
    subst b
    omega
  | succ n ih=>
    intro b hb
    rw [frontier_succ] at hb
    obtain ⟨parent,hp,hb⟩:=List.mem_flatMap.mp hb
    have h₁:=ih parent hp
    have h₂:=hd parent b hb
    omega

private theorem frontier_empty {A:Type} (children:A→List A) (μ:A→Nat)
    (hd:∀a,∀b∈children a,μ b<μ a) (a:A):
    frontier children a (μ a+1)=[]:=by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b hb
  have hh:=frontier_bound children μ hd a (μ a+1) b hb
  omega

theorem graph_correct {A B:Type} [DecidableEq A]
    (children:A→List A) (assemble:A→List B→B) (μ:A→Nat) (f:A→B)
    (hd:∀a,∀b∈children a,μ b<μ a)
    (hf:∀a,f a=assemble a ((children a).map f)) (a:A) :
    ∀i,i≤μ a+1→graph children assemble μ a i=
      (frontier children a (μ a+1-i)).map (fun b=>(b,f b)):=by
  intro i
  induction i with
  | zero=>intro hi;simp only [graph,Nat.sub_zero,frontier_empty children μ hd,List.map_nil]
  | succ i ih=>
    intro hi
    have hi':i≤μ a:=by omega
    have he:μ a+1-(i+1)=μ a-i:=by omega
    have he':μ a+1-i=(μ a-i)+1:=by omega
    rw [graph,ih (by omega),he]
    apply List.map_congr_left
    intro b hb
    have has:children b⊆frontier children a (μ a+1-i):=by
      rw [he',frontier_succ]
      exact (List.infix_flatMap_of_mem hb children).subset
    have hlookup:((children b).filterMap (fun c=>
        ((frontier children a (μ a+1-i)).map (fun x=>(x,f x))).lookup c))=
        (children b).map f:=by
      apply List.filterMap_eq_map_iff_forall_eq_some.mpr
      intro c hc
      exact List.lookup_graph f (has hc)
    rw [hlookup,←hf b]

theorem graph_root {A B:Type} [DecidableEq A]
    (children:A→List A) (assemble:A→List B→B) (μ:A→Nat) (f:A→B)
    (hd:∀a,∀b∈children a,μ b<μ a)
    (hf:∀a,f a=assemble a ((children a).map f)) (a:A):
    graph children assemble μ a (μ a+1)=[(a,f a)]:=by
  rw [graph_correct children assemble μ f hd hf a _ le_rfl,Nat.sub_self]
  rfl
end LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof
