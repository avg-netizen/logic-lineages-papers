module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedActivationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalComputabilityApplication SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalControlGraphSupportProof InternalApplicationSyntaxProof
open InternalRecursionClosureSyntaxProof GuardedSourceSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc bindTerm bindEmbedding liftBind varBind zSubst sucSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem numeralSubst {α β : Type} (n : Nat) (ts : α → OTerm β) :
    (numeral n : OTerm α).subst ts = numeral n := by
  induction n with
  | zero => exact zSubst ts
  | succ n ih => simpa only [numeral,sucSubst] using congrArg suc ih

theorem embedPair {α : Type} (s t : OTerm α) :
    (fun i : Fin 2 => emb (![s,t] i)) = ![emb s,emb t] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

def liftTerms {α β : Type} (ts : α → OTerm β) : α ⊕ Fin 1 → OTerm (β ⊕ Fin 1) :=
  Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))

theorem liftEmbedding {α β : Type} (ts : α → OTerm β) :
    Sum.elim (fun a => (emb (ts a)).relabel Sum.inl)
      (fun i : Fin 1 => (.var (.inr i) : Term (β ⊕ Fin 1))) =
    (fun a => emb (liftTerms ts a)) := by
  funext a
  cases a with
  | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
  | inr i => rfl

theorem liftTermSubst {α β : Type} (t : OTerm α) (ts : α → OTerm β) :
    (t.relabel Sum.inl).subst (liftTerms ts) = (t.subst ts).relabel Sum.inl := by
  rw [termRelabelSubst,termSubstRelabel]
  rfl

theorem allEmbeddedSubst {α β : Type} (phi : Formula (α ⊕ Fin 1)) (ts : α → OTerm β) :
    (allOne phi).subst (fun a => emb (ts a)) =
      allOne (phi.subst (fun a => emb (liftTerms ts a))) := by
  rw [actualUniversalSubstitution,liftEmbedding]

theorem existsEmbeddedSubst {α β : Type} (phi : Formula (α ⊕ Fin 1)) (ts : α → OTerm β) :
    (existsOne phi).subst (fun a => emb (ts a)) =
      existsOne (phi.subst (fun a => emb (liftTerms ts a))) := by
  rw [existsSubst,liftEmbedding]

theorem programSubst {α β : Type} {n : Nat} (p : Program n) (out : OTerm α)
    (xs : Fin n → OTerm α) (ts : α → OTerm β) :
    (programGraph p out xs).subst (fun a => emb (ts a)) =
      programGraph p (out.subst ts) (fun i => (xs i).subst ts) :=
  graphSubst _ _ _ _

theorem computableSubst {α β : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) (ts : α → OTerm β) :
    (computable data tau context t).subst (fun a => emb (ts a)) =
      computable data tau (context.subst ts) (t.subst ts) := by
  rw [computable,formulaSubstComposition,computable]
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i
  · exact (onTermSubst arithmeticEmbedding context ts).symm
  · exact (onTermSubst arithmeticEmbedding t ts).symm

theorem computableRename {α β : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) (j : α → β) :
    (computable data tau context t).relabel j =
      computable data tau (context.relabel j) (t.relabel j) := by
  rw [computable,formulaSubstRelabel,computable]
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i
  · exact (onTermRelabel arithmeticEmbedding j context).symm
  · exact (onTermRelabel arithmeticEmbedding j t).symm

theorem computableInstantiate {α : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) :
    instantiate (computable data tau (context.relabel Sum.inl) (.var (.inr 0))) (emb t) =
      computable data tau context t := by
  rw [instantiate,bindEmbedding,computableSubst,liftBind,varBind]

theorem argumentsSubst {α β : Type} (context : OTerm α) (sigma tau : Ty)
    (f a : OTerm α) (ts : α → OTerm β) :
    (fun i => (arguments context sigma tau f a i).subst ts) =
      arguments (context.subst ts) sigma tau (f.subst ts) (a.subst ts) := by
  funext i
  refine Fin.cases rfl (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i
  · exact numeralSubst _ ts
  · exact numeralSubst _ ts

theorem argumentsRename {α β : Type} (context : OTerm α) (sigma tau : Ty)
    (f a : OTerm α) (j : α → β) :
    (fun i => (arguments context sigma tau f a i).relabel j) =
      arguments (context.relabel j) sigma tau (f.relabel j) (a.relabel j) := by
  funext i
  refine Fin.cases rfl (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i
  · exact numeralRename _ j
  · exact numeralRename _ j

theorem guardedSubst {α β : Type} (data : JointGammaComputability.Data)
    (f a : OTerm α) (ts : α → OTerm β) :
    (guarded data f a).subst (fun x => emb (ts x)) = guarded data (f.subst ts) (a.subst ts) := by
  unfold guarded
  rw [programSubst,sucSubst,zSubst]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

theorem acceptedSubst {α β : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a out : OTerm α) (ts : α → OTerm β) :
    (accepted data sigma tau context f a out).subst (fun x => emb (ts x)) =
      accepted data sigma tau (context.subst ts) (f.subst ts) (a.subst ts) (out.subst ts) := by
  unfold accepted
  rw [programSubst,sucSubst,zSubst,
    mapInputs (fun t : OTerm α => t.subst ts) (arguments context sigma tau f a) out,argumentsSubst]

theorem acceptedRename {α β : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a out : OTerm α) (j : α → β) :
    (accepted data sigma tau context f a out).relabel j =
      accepted data sigma tau (context.relabel j) (f.relabel j) (a.relabel j) (out.relabel j) := by
  unfold accepted
  rw [programRename,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel,inputsRename,argumentsRename]

theorem activationRename {α β : Type} (data : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (context : OTerm α) (sigma tau : Ty)
    (f a : OTerm α) (j : α → β) :
    (activationAt data window arrow context sigma tau f a).relabel j =
      activationAt data window arrow (context.relabel j) sigma tau (f.relabel j) (a.relabel j) := by
  unfold activationAt
  rw [programRename,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel,argumentsRename]

theorem resultExistsSubst {α β : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) (ts : α → OTerm β) :
    (resultExists data sigma tau context f a).subst (fun x => emb (ts x)) =
      resultExists data sigma tau (context.subst ts) (f.subst ts) (a.subst ts) := by
  rw [resultExists,existsEmbeddedSubst]
  unfold resultBody
  rw [conjunctionSubst,acceptedSubst,computableSubst]
  simp only [liftTermSubst]
  rfl

theorem typedLiteral {α : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (context t : OTerm α) :
    arithmeticEmbedding.onFormula ((JointGammaTyped.typedFormula data.typed).subst
      ![context,numeral (typeNumber tau),t]) = typed data tau context t := by
  unfold JointGammaTyped.typedFormula typed
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

theorem guardLiteral {α : Type} (data : JointGammaComputability.Data) (f a : OTerm α) :
    arithmeticEmbedding.onFormula ((SourcePresentation.checkerFormula data.guard).subst ![f,a]) =
      guarded data f a :=
  GammaGuardedSourceSyntaxProof.literalGuardGraph data f a

theorem applicationLiteral {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a out : OTerm α) :
    arithmeticEmbedding.onFormula ((JointGammaApplication.applicationFormula data.application).subst
      ![context,numeral (typeNumber sigma),numeral (typeNumber tau),f,a,out]) =
      accepted data sigma tau context f a out := by
  unfold JointGammaApplication.applicationFormula accepted
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

theorem typedInstance {α : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (ts : Fin 2 → OTerm α) :
    (SourceComputabilityFormulaProof.typedAt (JointGammaTyped.typedFormula data.typed) tau).subst
      (fun i => emb (ts i)) = typed data tau (ts 0) (ts 1) := by
  unfold SourceComputabilityFormulaProof.typedAt
  rw [← embedSubst,formulaSubstComposition]
  have hv : (fun i : Fin 3 =>
      (![.var 0,numeral (typeNumber tau),.var 1] i : OTerm (Fin 2)).subst ts) =
      ![ts 0,numeral (typeNumber tau),ts 1] := by
    funext i
    refine Fin.cases rfl (Fin.cases ?_ (Fin.cases rfl (fun q => Fin.elim0 q))) i
    exact numeralSubst _ ts
  rw [hv]
  exact typedLiteral data tau (ts 0) (ts 1)

theorem guardInstance {α : Type} (data : JointGammaComputability.Data)
    (ts : Fin 2 ⊕ Fin 1 → OTerm α) :
    (JointGammaComputability.guardAt data.guard).subst (fun i => emb (ts i)) =
      guarded data (ts (.inl 1)) (ts (.inr 0)) := by
  unfold JointGammaComputability.guardAt
  rw [← embedSubst,formulaSubstComposition]
  have hv : (fun i : Fin 2 =>
      (![.var (.inl 1),.var (.inr 0)] i : OTerm (Fin 2 ⊕ Fin 1)).subst ts) =
      ![ts (.inl 1),ts (.inr 0)] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  rw [hv]
  exact guardLiteral data _ _

theorem applicationInstance {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (ts : (Fin 2 ⊕ Fin 1) ⊕ Fin 1 → OTerm α) :
    (SourceComputabilityFormulaProof.appAt (JointGammaApplication.applicationFormula data.application)
      sigma tau).subst (fun i => emb (ts i)) =
      accepted data sigma tau (ts (.inl (.inl 0))) (ts (.inl (.inl 1)))
        (ts (.inl (.inr 0))) (ts (.inr 0)) := by
  unfold SourceComputabilityFormulaProof.appAt
  rw [← embedSubst,formulaSubstComposition]
  have hv : (fun i : Fin 6 =>
      (![.var (.inl (.inl 0)),numeral (typeNumber sigma),numeral (typeNumber tau),
        .var (.inl (.inl 1)),.var (.inl (.inr 0)),.var (.inr 0)] i :
        OTerm ((Fin 2 ⊕ Fin 1) ⊕ Fin 1)).subst ts) =
      ![ts (.inl (.inl 0)),numeral (typeNumber sigma),numeral (typeNumber tau),
        ts (.inl (.inl 1)),ts (.inl (.inr 0)),ts (.inr 0)] := by
    funext i
    refine Fin.cases rfl (Fin.cases ?_ (Fin.cases ?_ (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i
    · exact numeralSubst _ ts
    · exact numeralSubst _ ts
  rw [hv]
  exact applicationLiteral data sigma tau _ _ _ _

theorem relabeledInstance {α β : Type} (data : JointGammaComputability.Data) (tau : Ty)
    (j : Fin 2 → β) (ts : β → OTerm α) :
    ((JointGammaComputability.formula data tau).relabel j).subst (fun i => emb (ts i)) =
      computable data tau (ts (j 0)) (ts (j 1)) := by
  rw [actualRelabelSubstitution,computable]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

def arrowBody {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f : OTerm α) : Formula (α ⊕ Fin 1) :=
  (guarded data (f.relabel Sum.inl) (.var (.inr 0))).imp
    ((computable data sigma (context.relabel Sum.inl) (.var (.inr 0))).imp
      (resultExists data sigma tau (context.relabel Sum.inl) (f.relabel Sum.inl) (.var (.inr 0))))

theorem computableArrow {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f : OTerm α) :
    computable data (.arrow sigma tau) context f =
      typed data (.arrow sigma tau) context f ⊓ allOne (arrowBody data sigma tau context f) := by
  rw [computable,← embedPair,JointGammaComputability.formula,conjunctionSubst,
    typedInstance,allEmbeddedSubst]
  congr 1
  congr 1
  change ((JointGammaComputability.guardAt data.guard).subst _).imp
    ((((JointGammaComputability.formula data sigma).relabel
      (![Sum.inl (0 : Fin 2),Sum.inr (0 : Fin 1)] : Fin 2 → Fin 2 ⊕ Fin 1)).subst _).imp
      ((existsOne _).subst _)) = _
  rw [guardInstance,relabeledInstance,existsEmbeddedSubst,conjunctionSubst,
    applicationInstance,relabeledInstance]
  rfl

theorem arrowBodyInstantiate {α : Type} (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) :
    instantiate (arrowBody data sigma tau context f) (emb a) =
      (guarded data f a).imp ((computable data sigma context a).imp
        (resultExists data sigma tau context f a)) := by
  rw [instantiate,bindEmbedding]
  change ((guarded data (f.relabel Sum.inl) (.var (.inr 0))).subst _).imp
    (((computable data sigma (context.relabel Sum.inl) (.var (.inr 0))).subst _).imp
      ((resultExists data sigma tau (context.relabel Sum.inl) (f.relabel Sum.inl)
        (.var (.inr 0))).subst _)) = _
  rw [guardedSubst,computableSubst,resultExistsSubst]
  simp only [liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
