module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn eqnRelabel eqnSubst bindEmbedding liftBind varBind sucRelabel sucSubst zSubst zRelabel)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (numeralSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape)

attribute [local irreducible] programGraph

theorem auxiliaryRename {α β : Type} (dom cod fn arg : OTerm α) (j : α → β) :
    (auxiliaryTerm dom cod fn arg).relabel j =
      auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) := by
  simp only [auxiliaryTerm,rawConsRename,numeralRename,zRelabel]

theorem threeRename {α β : Type} (a b c : OTerm α) (j : α → β) :
    (fun i => ((![a,b,c] : Fin 3 → OTerm α) i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

theorem tapeRename {α β : Type} (ctx dom cod fn arg y : OTerm α) (j : α → β) :
    (fun i => (objectTape ctx dom cod fn arg y i).relabel j) =
      objectTape (ctx.relabel j) (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) (y.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) e) d) c) b) a) i <;> rfl

private theorem addressRename {α β : Type} (c t k : OTerm α) (j : α → β) :
    (addressTerm c t k).relabel j = addressTerm (c.relabel j) (t.relabel j) (k.relabel j) := by
  simp only [addressTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

private theorem addressSubst {α β : Type} (c t k : OTerm α) (ts : α → OTerm β) :
    (addressTerm c t k).subst ts = addressTerm (c.subst ts) (t.subst ts) (k.subst ts) := by
  simp only [addressTerm,consTerm,pairTerm,addSubst,mulSubst,sucSubst,zSubst,numeralSubst]

abbrev reportBody {α : Type} (least : Program 3) (ctx cod raw y k : OTerm α) : Formula α :=
  programGraph least (suc k) ![ctx,cod,raw] ⊓ eqn y (addressTerm ctx cod k)

abbrev reportBinder {α : Type} (least : Program 3) (ctx cod raw y : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  reportBody least (ctx.relabel Sum.inl) (cod.relabel Sum.inl)
    (raw.relabel Sum.inl) (y.relabel Sum.inl) (.var (.inr 0))

theorem reportUnfold {α : Type} (least : Program 3) (ctx cod raw y : OTerm α) :
    outputReport least ctx cod raw y = existsOne (reportBinder least ctx cod raw y) := rfl

private theorem bodyRename {α β : Type} (least : Program 3) (ctx cod raw y k : OTerm α) (j : α → β) :
    (reportBody least ctx cod raw y k).relabel j =
      reportBody least (ctx.relabel j) (cod.relabel j) (raw.relabel j) (y.relabel j) (k.relabel j) := by
  simp only [reportBody,conjunctionRename,programRename,sucRelabel,threeRename,eqnRelabel,addressRename]

theorem reportRename {α β : Type} (least : Program 3) (ctx cod raw y : OTerm α) (j : α → β) :
    (outputReport least ctx cod raw y).relabel j =
      outputReport least (ctx.relabel j) (cod.relabel j) (raw.relabel j) (y.relabel j) := by
  rw [reportUnfold,reportUnfold,existsRename]
  unfold reportBinder
  rw [bodyRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem bodySubst {α β : Type} (least : Program 3) (ctx cod raw y k : OTerm α) (ts : α → OTerm β) :
    (reportBody least ctx cod raw y k).subst (fun a => emb (ts a)) =
      reportBody least (ctx.subst ts) (cod.subst ts) (raw.subst ts) (y.subst ts) (k.subst ts) := by
  have args : (fun i => ((![ctx,cod,raw] : Fin 3 → OTerm α) i).subst ts) =
      ![ctx.subst ts,cod.subst ts,raw.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) b) a) i <;> rfl
  simp only [reportBody,conjunctionSubst,programSubst,args,sucSubst,eqnSubst,addressSubst]

theorem reportInstance {α : Type} (least : Program 3) (ctx cod raw y k : OTerm α) :
    instantiate (reportBinder least ctx cod raw y) (emb k) =
      reportBody least ctx cod raw y k := by
  simp only [instantiate,reportBinder,bindEmbedding,bodySubst,liftBind,varBind]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
