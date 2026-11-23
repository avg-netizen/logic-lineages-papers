module
public import LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraphTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraph
open ComputableRankedProof (bindList bindListProgram graph)

private theorem sweepLiteral {A β σ : Type} [Primcodable β]
    {m : β → Nat} {l : β → List β} {layer : Layer A β σ}
    {a : A} {g : β → List σ → Option σ}
    (h : LiteralLayer l layer a g) (b : β) (i : Nat) :
    sweep m l layer a b i = Part.some (graph m l g b i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (sweep m l layer a b i).bind
      (fun prev => layer a (bindList l b (m b-i),prev)) = _
    rw [ih,Part.bind_some,h] <;> rfl

theorem exactPolicyIndexedRankedGraph : ExactPolicyIndexedRankedGraph := by
  intro A β σ _ m l layer a g h
  refine ⟨sweepLiteral h,?_⟩
  intro b
  unfold root
  rw [sweepLiteral h] <;> rfl

private theorem sweepPartrec {A β σ : Type} [Primcodable A] [Primcodable β] [Primcodable σ]
    {m : β → Nat} {l : β → List β} {layer : Layer A β σ}
    (hm : Primrec m) (hl : Primrec l) (hg : Partrec₂ layer) :
    Partrec (fun p : (A × β) × Nat => sweep m l layer p.1.1 p.1.2 p.2) := by
  let T := (A × β) × Nat
  let U := T × (Nat × Matrix β σ)
  have key : Computable (fun p : U => p.1.1.1) := Computable.fst.comp
    (Computable.fst.comp Computable.fst)
  have b : Computable (fun p : U => p.1.1.2) := Computable.snd.comp
    (Computable.fst.comp Computable.fst)
  have i : Computable (fun p : U => p.2.1) := Computable.fst.comp Computable.snd
  have prev : Computable (fun p : U => p.2.2) := Computable.snd.comp Computable.snd
  have depth : Computable (fun p : U => m p.1.1.2 - p.2.1) :=
    Primrec.nat_sub.to_comp.comp (hm.to_comp.comp b) i
  have frontier : Computable (fun p : U => bindList l p.1.1.2 (m p.1.1.2 - p.2.1)) :=
    (bindListProgram hl).to_comp.comp b depth
  have step : Partrec₂ (fun (p : T) (state : Nat × Matrix β σ) =>
      layer p.1.1 (bindList l p.1.2 (m p.1.2-state.1),state.2)) :=
    (hg.comp key (frontier.pair prev)).to₂
  apply (Partrec.nat_rec Computable.snd ((Computable.const ([] : Matrix β σ)).partrec)
    step).of_eq
  intro p
  change p.2.rec (Part.some ([] : Matrix β σ))
    (fun i prev => prev.bind (fun tab => layer p.1.1 (bindList l p.1.2 (m p.1.2-i),tab))) =
      sweep m l layer p.1.1 p.1.2 p.2
  rcases p with ⟨⟨a,b⟩,i⟩
  induction i with
  | zero => rfl
  | succ i ih =>
    exact congrArg (fun tab => tab.bind fun x =>
      layer a (bindList l b (m b-i),x)) ih

theorem policyIndexedRankedEffectivity : PolicyIndexedRankedEffectivity := by
  intro A β σ _ _ _ m l layer hm hl hg
  have hs := sweepPartrec hm hl hg
  refine ⟨hs,?_⟩
  have fuel : Computable (fun p : A × β => m p.2+1) :=
    Computable.succ.comp (hm.to_comp.comp Computable.snd)
  have run : Partrec (fun p : A × β => sweep m l layer p.1 p.2 (m p.2+1)) :=
    hs.comp (Computable.id.pair fuel)
  have read : Computable₂ (fun (_ : A × β) (tab : Matrix β σ) => tab[0]?.map Prod.snd) := by
    have first : Computable (fun p : (A × β) × Matrix β σ => p.2[0]?) :=
      Primrec.list_getElem?.to_comp.comp Computable.snd (Computable.const 0)
    exact (Computable.option_map first (Computable.snd.comp Computable.snd).to₂).to₂
  exact Partrec.map run read

end LogicLineages.StandardControlCurrent.PolicyIndexedRankedGraph
