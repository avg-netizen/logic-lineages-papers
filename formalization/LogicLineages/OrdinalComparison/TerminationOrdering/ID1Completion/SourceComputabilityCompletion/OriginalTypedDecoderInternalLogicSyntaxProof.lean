module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalRecursionClosureSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqnSubst eqnRelabel sucSubst zSubst)
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalOriginalOrderSyntaxProof (notSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof

theorem orSubst {alpha beta : Type} (p q : Formula alpha) (ts : alpha → Term beta) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

theorem equalSubst {alpha beta : Type} (x y : OTerm alpha) (ts : alpha → OTerm beta) :
    (equal x y).subst (fun a => emb (ts a)) = equal (x.subst ts) (y.subst ts) := by
  simp only [equalEqn,eqnSubst]

@[simp] theorem equalRename {alpha beta : Type} (x y : OTerm alpha) (j : alpha → beta) :
    (equal x y).relabel j = equal (x.relabel j) (y.relabel j) := by
  simp only [equalEqn,eqnRelabel]

theorem numeralSubst {alpha beta : Type} (n : Nat) (ts : alpha → OTerm beta) :
    (numeral n : OTerm alpha).subst ts = numeral n := by
  induction n with
  | zero => exact zSubst ts
  | succ n ih => simpa only [numeral,sucSubst] using congrArg OrdinaryArithmetic.succTerm ih

theorem stepBottomSubst {alpha beta : Type}
    (out typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepBottom out typ payload rest).subst (fun a => emb (ts a)) =
      StepBottom (out.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  simp only [StepBottom,orSubst,conjunctionSubst,notSubst,equalSubst,stepLiveSubst,numeralSubst]

@[simp] theorem stepBottomRename {alpha beta : Type}
    (out typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepBottom out typ payload rest).relabel j =
      StepBottom (out.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepBottom out typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepBottomSubst]
  simp only [← termRelabelAsSubst]

theorem stepArgumentsNilSubst {alpha beta : Type}
    (out typ payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepArgumentsNil out typ payload rest).subst (fun a => emb (ts a)) =
      StepArgumentsNil (out.subst ts) (typ.subst ts) (payload.subst ts) (rest.subst ts) := by
  simp only [StepArgumentsNil,orSubst,conjunctionSubst,notSubst,equalSubst,stepLiveSubst,numeralSubst]

@[simp] theorem stepArgumentsNilRename {alpha beta : Type}
    (out typ payload rest : OTerm alpha) (j : alpha → beta) :
    (StepArgumentsNil out typ payload rest).relabel j =
      StepArgumentsNil (out.relabel j) (typ.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepArgumentsNil out typ payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepArgumentsNilSubst]
  simp only [← termRelabelAsSubst]

theorem stepUnknownTagSubst {alpha beta : Type} (tag : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepUnknownTag tag).subst (fun a => emb (ts a)) = StepUnknownTag (tag.subst ts) := by
  simp only [StepUnknownTag,conjunctionSubst,notSubst,equalSubst,numeralSubst]

@[simp] theorem stepUnknownTagRename {alpha beta : Type} (tag : OTerm alpha) (j : alpha → beta) :
    (StepUnknownTag tag).relabel j = StepUnknownTag (tag.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepUnknownTag tag).subst (fun a => emb (.var (j a))) = _
  rw [stepUnknownTagSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
