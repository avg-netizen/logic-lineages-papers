module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward InternalComputabilityApplicationSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalDerivationRenamingSyntaxProof InternalRecursionClosureSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc bindTerm bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem typedRename {α β : Type} (comp : JointGammaComputability.Data) (tau : Ty)
    (context f : OTerm α) (j : α → β) :
    (typed comp tau context f).relabel j = typed comp tau (context.relabel j) (f.relabel j) := by
  unfold typed
  rw [programRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases (GuardedSourceSyntaxProof.numeralRename _ j)
    (Fin.cases rfl (fun q => Fin.elim0 q))) i

theorem guardedRename {α β : Type} (comp : JointGammaComputability.Data)
    (f a : OTerm α) (j : α → β) :
    (guarded comp f a).relabel j = guarded comp (f.relabel j) (a.relabel j) := by
  unfold guarded
  rw [programRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

theorem edgeRename {α β : Type} (src : SourcePresentation.Data) (context : Nat)
    (f g : OTerm α) (j : α → β) :
    (edge src false context f g).relabel j =
      edge src false context (f.relabel j) (g.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge src false context f g).subst (fun x => emb (.var (j x))) = _
  rw [InternalAccessibilityRulesSyntaxProof.edgeSubst]
  rw [← termRelabelAsSubst,← termRelabelAsSubst]

theorem certificateRename {α β : Type} (src : SourcePresentation.Data) (context : Nat)
    (f g witness : OTerm α) (j : α → β) :
    (certificate src false context f g witness).relabel j =
      certificate src false context (f.relabel j) (g.relabel j) (witness.relabel j) := by
  unfold certificate
  rw [programRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  congr 1
  funext i
  exact Fin.cases (GuardedSourceSyntaxProof.numeralRename _ j)
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

theorem resultExistsRename {α β : Type} (comp : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) (j : α → β) :
    (resultExists comp sigma tau context f a).relabel j =
      resultExists comp sigma tau (context.relabel j) (f.relabel j) (a.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (resultExists comp sigma tau context f a).subst (fun x => emb (.var (j x))) = _
  rw [resultExistsSubst]
  rw [← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem applicationExistsRename {α β : Type} (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty) (f a : OTerm α) (j : α → β) :
    (applicationExists comp context sigma tau f a).relabel j =
      applicationExists comp context sigma tau (f.relabel j) (a.relabel j) := by
  unfold applicationExists
  rw [existsRename,acceptedRename]
  simp only [GuardedSourceSyntaxProof.numeralRename,Term.relabel_relabel]
  rfl

theorem domainRename {α β : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) (j : α → β) :
    (domain comp context sigma tau f a).relabel j =
      domain comp context sigma tau (f.relabel j) (a.relabel j) := by
  change (((typed comp (.arrow sigma tau) (numeral context) f).relabel j ⊓
    (typed comp sigma (numeral context) a).relabel j) ⊓ (guarded comp f a).relabel j) = _
  rw [typedRename,typedRename,guardedRename,GuardedSourceSyntaxProof.numeralRename]
  rfl

theorem liftArgumentsRename {α β : Type} (context : Nat) (sigma tau : Ty)
    (a witness : OTerm α) (j : α → β) :
    (fun i => (liftArguments context sigma tau a witness i).relabel j) =
      liftArguments context sigma tau (a.relabel j) (witness.relabel j) := by
  funext i
  exact Fin.cases (GuardedSourceSyntaxProof.numeralRename _ j)
    (Fin.cases (GuardedSourceSyntaxProof.numeralRename _ j)
      (Fin.cases (GuardedSourceSyntaxProof.numeralRename _ j)
        (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i

theorem computableGround {α : Type} (comp : JointGammaComputability.Data)
    (context f : OTerm α) :
    computable comp .ground context f = typed comp .ground context f ⊓ membership false f := by
  rw [computable,← embedPair,JointGammaComputability.formula,conjunctionSubst,typedInstance]
  congr 1
  change (membership false (.var (1 : Fin 2))).subst (fun i => emb (![context,f] i)) = _
  rw [InternalAccessibilityRulesSyntaxProof.membershipSubst]
  rfl

theorem resultBodyInstantiate {α : Type} (comp : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a out : OTerm α) :
    instantiate (resultBody comp sigma tau context f a) (emb out) =
      accepted comp sigma tau context f a out ⊓ computable comp tau context out := by
  rw [instantiate,bindEmbedding]
  unfold resultBody
  rw [conjunctionSubst,acceptedSubst,computableSubst]
  simp only [liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
