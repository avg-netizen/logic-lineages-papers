module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus SourceEndpoint TaggedArithmeticOperators SourceComputabilityFormulaSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof

/-- Syntax abbreviation for the unchanged original specialized positive payload. -/
def payload {α : Type} (p : Positive (Fin 2)) (c t : OTerm α) : Formula α :=
  (substitutePositive ![c,t] p).formula

theorem termRelabelAsSubst {L : Language} {α β : Type} (t : L.Term α) (f : α → β) :
    t.relabel f = t.subst (fun a => .var (f a)) := by
  have h := termRelabelSubst t f Term.var
  rw [termSubstVar] at h
  exact h

theorem formulaRelabelAsSubst {α β : Type} (phi : Formula α) (f : α → β) :
    phi.relabel f = phi.subst (fun a => .var (f a)) := by
  have h := actualRelabelSubstitution α β β phi f Term.var
  rw [formulaSubstVar] at h
  exact h

theorem formulaSubstRelabel {α β γ : Type} (phi : Formula α) (ts : α → Term β) (f : β → γ) :
    FirstOrder.Language.Formula.relabel f (phi.subst ts) = phi.subst (fun a => (ts a).relabel f) := by
  rw [formulaRelabelAsSubst,formulaSubstComposition]
  congr 1
  funext a
  exact (termRelabelAsSubst (ts a) f).symm

theorem payloadSubst {α β : Type} (p : Positive (Fin 2)) (c t : OTerm α) (ts : α → OTerm β) :
    (payload p c t).subst (fun a => emb (ts a)) = payload p (c.subst ts) (t.subst ts) := by
  rw [payload,actualPositiveSubstitution,formulaSubstComposition,payload,actualPositiveSubstitution]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact (onTermSubst arithmeticEmbedding c ts).symm
  · exact (onTermSubst arithmeticEmbedding t ts).symm

theorem payloadRelabel {α β : Type} (p : Positive (Fin 2)) (c t : OTerm α) (f : α → β) :
    (payload p c t).relabel f = payload p (c.relabel f) (t.relabel f) := by
  rw [payload,actualPositiveSubstitution,formulaSubstRelabel,payload,actualPositiveSubstitution]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact (onTermRelabel arithmeticEmbedding f c).symm
  · exact (onTermRelabel arithmeticEmbedding f t).symm

theorem payloadInstantiate {α : Type} (p : Positive (Fin 2)) (c t : OTerm α) :
    instantiate (payload p (c.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb t) = payload p c t := by
  rw [instantiate,bindEmbedding,payloadSubst,liftBind,varBind]

theorem tagRelabel {α β : Type} (odd : Bool) (t : OTerm α) (f : α → β) :
    (tagTerm odd t).relabel f = tagTerm odd (t.relabel f) := by
  cases odd with
  | false => exact dblRelabel t f
  | true => exact (sucRelabel (dbl t) f).trans (congrArg suc (dblRelabel t f))

/-- Exact original guarded branch syntax, with its binder made explicit. -/
theorem branchUnfold {α : Type} (odd : Bool) (p : Positive (Fin 2)) (c x : OTerm α) :
    (substitutePositive ![c,x] (taggedBranch odd p)).formula =
    allOne ((eqn (x.relabel Sum.inl) (tagTerm odd (.var (.inr (0 : Fin 1))))).imp
      (payload (tagPredicate odd p) (c.relabel Sum.inl) (.var (.inr (0 : Fin 1))))) := by
  let sigma : Fin 2 ⊕ Fin 1 → OTerm (α ⊕ Fin 1) :=
    Sum.elim (fun i => (![c,x] i).relabel Sum.inl) (fun i => .var (.inr i))
  change allOne (substitutePositive sigma (originalBranchBody odd p)).formula = _
  congr 1
  let guard : OrdinaryArithmetic.Formula (Fin 2 ⊕ Fin 1) :=
    (.var (.inl (1 : Fin 2)) : OTerm (Fin 2 ⊕ Fin 1)).equal (tagTerm odd (.var (.inr 0)))
  change (arithmeticEmbedding.onFormula (guard.subst sigma)).imp
    (substitutePositive sigma
      (PositiveArithmeticTransforms.relabel ![.inl (0 : Fin 2),.inr (0 : Fin 1)] (tagPredicate odd p))).formula = _
  rw [positiveRelabelSubstitution]
  have hf : sigma ∘ ![Sum.inl (0 : Fin 2),Sum.inr (0 : Fin 1)] =
      ![c.relabel Sum.inl, (.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1))] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [hf]
  dsimp only [guard]
  rw [equalitySubstitution,tagSubstitution]
  change (arithmeticEmbedding.onFormula ((x.relabel Sum.inl).equal
    (tagTerm odd (.var (.inr (0 : Fin 1)))))).imp _ = _
  rw [onEquality]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
