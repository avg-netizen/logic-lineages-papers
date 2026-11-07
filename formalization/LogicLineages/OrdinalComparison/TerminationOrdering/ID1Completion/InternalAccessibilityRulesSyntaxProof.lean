module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus InternalAccessibilityRules SourceEndpoint SourceComputabilityFormulaSupportProof
open InternalSourceIntroductionSyntaxProof InternalSourceInversionSupportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalGraphCompositionSyntaxProof InternalFiniteBlocksBindingProof
open InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding bindTerm liftBind varBind z suc)
open GuardedSourceSyntaxProof

theorem numeralSubst {α β : Type} (n : Nat) (ts : α → OTerm β) :
    (numeral n : OTerm α).subst ts = numeral n := by
  induction n with
  | zero => exact zeroSubstitution ts
  | succ n ih =>
    simpa only [numeral,InternalTagArithmeticSyntaxProof.sucSubst] using congrArg suc ih

theorem membershipSubst {α β : Type} (odd : Bool) (x : OTerm α) (ts : α → OTerm β) :
    (membership odd x).subst (fun a => emb (ts a)) = membership odd (x.subst ts) := by
  unfold membership
  rw [← predicateSubstitution,tagSubstitution]

theorem edgeSubst {α β : Type} (data : SourcePresentation.Data) (odd : Bool) (context : Nat)
    (x y : OTerm α) (ts : α → OTerm β) :
    (edge data odd context x y).subst (fun a => emb (ts a)) =
      edge data odd context (x.subst ts) (y.subst ts) := by
  unfold edge
  rw [← embedSubst,formulaSubstComposition]
  congr 1
  congr 1
  funext i
  exact Fin.cases (numeralSubst context ts)
    (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

theorem successorInstance {α : Type} (data : SourcePresentation.Data) (odd : Bool)
    (context : Nat) (x y : OTerm α) :
    instantiate ((edge data odd context (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (membership odd (.var (.inr (0 : Fin 1))))) (emb y) =
    (edge data odd context x y).imp (membership odd y) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((edge data odd context (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).subst
    (fun a => emb (bindTerm y a))).imp
      ((membership odd (.var (.inr (0 : Fin 1)))).subst (fun a => emb (bindTerm y a))) = _
  rw [edgeSubst,membershipSubst,liftBind,varBind]

/-- Only binder/substitution normalization of the original positive operator. -/
theorem originalPayload {α : Type} (data : SourcePresentation.Data) (odd : Bool)
    (context : Nat) (x : OTerm α) :
    (substitutePositive ![numeral context,x] (tagPredicate odd
      (accessibilityOperator (SourcePresentation.checkerFormula (carrierProgram data odd))
        (OrdinaryArithmeticQuotient.certificateGraph (edgeProgram data odd))))).formula =
      carrier data odd context x ⊓ successors data odd context x := by
  let sigma : Fin 2 ⊕ Fin 1 → OTerm (α ⊕ Fin 1) :=
    Sum.elim (fun i => (![numeral context,x] i).relabel Sum.inl) (fun i => .var (.inr i))
  change carrier data odd context x ⊓
    allOne ((arithmeticEmbedding.onFormula
      (((OrdinaryArithmeticQuotient.certificateGraph (edgeProgram data odd)).subst
        ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))]).subst sigma)).imp
      (Positive.predicate ((tagTerm odd (.var (.inr (0 : Fin 1)))).subst sigma)).formula) = _
  rw [formulaSubstComposition,tagSubstitution]
  have hs : (fun i : Fin 3 =>
      (![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))] i : OTerm (Fin 2 ⊕ Fin 1)).subst sigma) =
      ![numeral context,x.relabel Sum.inl,.var (.inr (0 : Fin 1))] := by
    funext i
    refine Fin.cases ?_ (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
    exact numeralRename context Sum.inl
  rw [hs]
  rfl

theorem edgeExists {α : Type} (data : SourcePresentation.Data) (odd : Bool)
    (context : Nat) (x y : OTerm α) :
    edge data odd context x y = existsOne
      (certificate data odd context (x.relabel Sum.inl) (y.relabel Sum.inl)
        (.var (.inr (0 : Fin 1)))) := by
  exact literalRGraph { data with positive := edgeProgram data odd } context x y

theorem certificateInstance {α : Type} (data : SourcePresentation.Data) (odd : Bool)
    (context : Nat) (x y witness : OTerm α) :
    instantiate (certificate data odd context (x.relabel Sum.inl) (y.relabel Sum.inl)
      (.var (.inr (0 : Fin 1)))) (emb witness) = certificate data odd context x y witness := by
  unfold instantiate certificate InternalControlGraph.programGraph
  rw [bindEmbedding,graphSubst]
  congr 1
  · simp only [InternalTagArithmeticSyntaxProof.sucSubst,InternalTagArithmeticSyntaxProof.zSubst]
  · funext i
    exact Fin.cases (numeralSubst context (bindTerm witness))
      (Fin.cases (liftBind x witness) (Fin.cases (liftBind y witness)
        (Fin.cases rfl (fun j => Fin.elim0 j)))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
