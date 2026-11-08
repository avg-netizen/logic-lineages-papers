module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberCertifiedLift InternalOriginalObjectFiberSourceAssembly
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionSyntaxProof InternalRawListRecursionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalBinderTransportSyntaxProof InternalFiniteBlocksBindingProof InternalFiniteBlocksProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof InternalPathCheckerSyntaxProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative GuardedSourceSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc zSubst sucSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem argumentFiberRename {α β : Type} (Gamma : List Ty) (a : OTerm α) (j : α → β) :
    (argumentFiber Gamma a).relabel j = argumentFiber Gamma (a.relabel j) := by
  simp only [argumentFiber,graph1Rename,numeralRename]

@[simp] theorem coordinatesRename {α β : Type} (Gamma : List Ty)
    (object payload : OTerm α) (j : α → β) :
    (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload).relabel j =
      InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma (object.relabel j) (payload.relabel j) := by
  simp only [InternalOriginalObjectFiberSourceDispatch.objectCoordinates,conjunctionRename,graph1Rename,numeralRename]

@[simp] theorem rawTypedRename {α β : Type} (p : Selection) (tau : Ty) (x : OTerm α) (j : α → β) :
    (rawTyped p tau x).relabel j = rawTyped p tau (x.relabel j) := by
  unfold rawTyped
  rw [InternalCanonicalQuotientEdgeSelectionTypingProof.typedRename,numeralRename]

@[simp] theorem rawPositiveRename {α β : Type} (p : Selection)
    (x y witness : OTerm α) (j : α → β) :
    (rawPositive p x y witness).relabel j =
      rawPositive p (x.relabel j) (y.relabel j) (witness.relabel j) := by
  exact InternalPathCheckerSyntaxProof.positiveRename _ x y witness j

@[simp] theorem originalPremisesRename {α β : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5) (context : Nat)
    (sigma tau : Ty) (f g a out other witness lifted : OTerm α) (j : α → β) :
    (originalPremises src comp lift context sigma tau f g a out other witness lifted).relabel j =
      originalPremises src comp lift context sigma tau (f.relabel j) (g.relabel j)
        (a.relabel j) (out.relabel j) (other.relabel j) (witness.relabel j) (lifted.relabel j) := by
  simp only [originalPremises,conjunctionRename,domainRename,certificateRename,
    acceptedRename,numeralRename,programRename,liftArgumentsRename]

@[simp] theorem fiberPremisesRename {α β : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5) (context : Nat)
    (Gamma : List Ty) (sigma tau : Ty) (f g a out other witness lifted : OTerm α) (j : α → β) :
    (fiberPremises src comp lift context Gamma sigma tau f g a out other witness lifted).relabel j =
      fiberPremises src comp lift context Gamma sigma tau (f.relabel j) (g.relabel j)
        (a.relabel j) (out.relabel j) (other.relabel j) (witness.relabel j) (lifted.relabel j) := by
  simp only [fiberPremises,conjunctionRename,originalPremisesRename,argumentFiberRename]

@[simp] theorem inputDataRename {α β : Type} (Gamma : List Ty) (p : Selection)
    (sigma tau : Ty) (f g a witness x y u : OTerm α) (j : α → β) :
    (inputData Gamma p sigma tau f g a witness x y u).relabel j =
      inputData Gamma p sigma tau (f.relabel j) (g.relabel j) (a.relabel j)
        (witness.relabel j) (x.relabel j) (y.relabel j) (u.relabel j) := by
  simp only [inputData,conjunctionRename,coordinatesRename,rawTypedRename,rawPositiveRename]

@[simp] theorem transportedOutputsRename {α β : Type} (Gamma : List Ty) (p : Selection)
    (tau : Ty) (out other lifted x y : OTerm α) (j : α → β) :
    (transportedOutputs Gamma p tau out other lifted x y).relabel j =
      transportedOutputs Gamma p tau (out.relabel j) (other.relabel j) (lifted.relabel j)
        (x.relabel j) (y.relabel j) := by
  simp only [transportedOutputs,conjunctionRename,coordinatesRename,rawTypedRename,rawPositiveRename]

/-- The existing binder renaming proof for an arbitrary finite block. -/
theorem renameFiniteBind {L : Language} {α β : Type} (f : α → β) {k n : Nat}
    (phi : L.BoundedFormula (α ⊕ Fin n) k) :
    rename f (phi.relabel id) = (rename (Sum.map f id) phi).relabel id := by
  have ht (j : Nat) (t : L.Term ((α ⊕ Fin n) ⊕ Fin j)) :
      (t.relabel (BoundedFormula.relabelAux (id : α ⊕ Fin n → α ⊕ Fin n) j)).relabel (Sum.map f id) =
      (t.relabel (Sum.map (Sum.map f id) id)).relabel
        (BoundedFormula.relabelAux (id : β ⊕ Fin n → β ⊕ Fin n) j) := by
    rw [Term.relabel_relabel,Term.relabel_relabel]
    congr 1
    funext i
    rcases i with (a | x) | y <;> simp [BoundedFormula.relabelAux]
  induction phi with
  | falsum => rfl
  | equal t u => simp only [rename,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | rel r ts => simp only [rename,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih =>
    change (rename f ((p.relabel id).castLE _)).all = _
    rw [renameCast,ih]
    rfl

theorem blockRename {α β : Type} {k : Nat} (phi : Formula (α ⊕ Fin k)) (j : α → β) :
    (InternalFiniteBlocks.block phi).relabel j =
      InternalFiniteBlocks.block (phi.relabel (Sum.map j id)) := by
  rw [formulaRelabel]
  unfold InternalFiniteBlocks.block
  rw [InternalBetaDivisionSyntaxProof.exsRename,renameFiniteBind,← formulaRelabel]

@[simp] theorem inputDataExistsRename {α β : Type} (Gamma : List Ty) (p : Selection)
    (sigma tau : Ty) (f g a witness : OTerm α) (j : α → β) :
    (inputDataExists Gamma p sigma tau f g a witness).relabel j =
      inputDataExists Gamma p sigma tau (f.relabel j) (g.relabel j) (a.relabel j) (witness.relabel j) := by
  simp only [inputDataExists,blockRename,inputDataRename,Term.relabel_relabel,Term.relabel]
  rfl

@[simp] theorem transportedOutputsExistRename {α β : Type} (Gamma : List Ty) (p : Selection)
    (tau : Ty) (out other lifted : OTerm α) (j : α → β) :
    (transportedOutputsExist Gamma p tau out other lifted).relabel j =
      transportedOutputsExist Gamma p tau (out.relabel j) (other.relabel j) (lifted.relabel j) := by
  simp only [transportedOutputsExist,blockRename,transportedOutputsRename,Term.relabel_relabel,Term.relabel]
  rfl

@[simp] theorem coordinatesSubst {α β : Type} (Gamma : List Ty)
    (object payload : OTerm α) (ts : α → OTerm β) :
    (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload).subst (fun a => emb (ts a)) =
      InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma (object.subst ts) (payload.subst ts) := by
  simp only [InternalOriginalObjectFiberSourceDispatch.objectCoordinates,conjunctionSubst,
    graph1,InternalRawListRecursionSyntaxProof.programSubst,consTermSubst,emptySubst,numeralSubst]

@[simp] theorem rawTypedSubst {α β : Type} (p : Selection) (tau : Ty) (x : OTerm α) (ts : α → OTerm β) :
    (rawTyped p tau x).subst (fun a => emb (ts a)) = rawTyped p tau (x.subst ts) := by
  simp only [rawTyped,InternalCanonicalQuotientEdgeSelection.typedAccepted,
    InternalCanonicalDescentSelection.typedAccepted,graph2,InternalRawListRecursionSyntaxProof.programSubst,consTermSubst,
    emptySubst,numeralSubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem rawPositiveSubst {α β : Type} (p : Selection)
    (x y witness : OTerm α) (ts : α → OTerm β) :
    (rawPositive p x y witness).subst (fun a => emb (ts a)) =
      rawPositive p (x.subst ts) (y.subst ts) (witness.subst ts) := by
  simp only [rawPositive,InternalPathChecker.positiveGraph,InternalPathChecker.checkerGraph,
    InternalPathChecker.triple,InternalRawListRecursionSyntaxProof.programSubst,consTermSubst,emptySubst,sucSubst,zSubst]

@[simp] theorem inputDataSubst {α β : Type} (Gamma : List Ty) (p : Selection)
    (sigma tau : Ty) (f g a witness x y u : OTerm α) (ts : α → OTerm β) :
    (inputData Gamma p sigma tau f g a witness x y u).subst (fun a => emb (ts a)) =
      inputData Gamma p sigma tau (f.subst ts) (g.subst ts) (a.subst ts)
        (witness.subst ts) (x.subst ts) (y.subst ts) (u.subst ts) := by
  simp only [inputData,conjunctionSubst,coordinatesSubst,rawTypedSubst,rawPositiveSubst]

@[simp] theorem transportedOutputsSubst {α β : Type} (Gamma : List Ty) (p : Selection)
    (tau : Ty) (out other lifted x y : OTerm α) (ts : α → OTerm β) :
    (transportedOutputs Gamma p tau out other lifted x y).subst (fun a => emb (ts a)) =
      transportedOutputs Gamma p tau (out.subst ts) (other.subst ts) (lifted.subst ts)
        (x.subst ts) (y.subst ts) := by
  simp only [transportedOutputs,conjunctionSubst,coordinatesSubst,rawTypedSubst,rawPositiveSubst]

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem inputIntro (Gamma : List Ty) (p : Selection) (sigma tau : Ty)
    (f g a witness x y u : OTerm α)
    (h : Nonempty (Derivation body Delta (inputData Gamma p sigma tau f g a witness x y u))) :
    Nonempty (Derivation body Delta (inputDataExists Gamma p sigma tau f g a witness)) := by
  apply actualFiniteExistentialIntroduction body α 3 Delta _ (fun i => emb (![x,y,u] i))
  have he : (Sum.elim FirstOrder.Language.Term.var (fun i => emb (![x,y,u] i))) =
      (fun a => emb ((Sum.elim FirstOrder.Language.Term.var ![x,y,u]) a)) := by
    funext a
    cases a <;> rfl
  rw [he,inputDataSubst]
  have ht (t : OTerm α) : (t.relabel Sum.inl).subst (Sum.elim FirstOrder.Language.Term.var ![x,y,u]) = t := by
    rw [termRelabelSubst]
    exact termSubstVar t
  simp only [ht,Term.subst,Sum.elim_inr]
  change Nonempty (Derivation body Delta (inputData Gamma p sigma tau f g a witness x y u))
  exact h

theorem transportedOutputsIntro (Gamma : List Ty) (p : Selection) (tau : Ty)
    (out other lifted x y : OTerm α)
    (h : Nonempty (Derivation body Delta (transportedOutputs Gamma p tau out other lifted x y))) :
    Nonempty (Derivation body Delta (transportedOutputsExist Gamma p tau out other lifted)) := by
  apply actualFiniteExistentialIntroduction body α 2 Delta _ (fun i => emb (![x,y] i))
  have he : (Sum.elim FirstOrder.Language.Term.var (fun i => emb (![x,y] i))) =
      (fun a => emb ((Sum.elim FirstOrder.Language.Term.var ![x,y]) a)) := by
    funext a
    cases a <;> rfl
  rw [he,transportedOutputsSubst]
  have ht (t : OTerm α) : (t.relabel Sum.inl).subst (Sum.elim FirstOrder.Language.Term.var ![x,y]) = t := by
    rw [termRelabelSubst]
    exact termSubstVar t
  simpa only [ht,Term.subst,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem inputCases (Gamma : List Ty) (p : Selection) (sigma tau : Ty)
    (f g a witness : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Delta (inputDataExists Gamma p sigma tau f g a witness)))
    (k : ∀ (β : Type) (j : α → β) (Theta : List (Formula β)) (x y u : OTerm β),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (inputData Gamma p sigma tau
        (f.relabel j) (g.relabel j) (a.relabel j) (witness.relabel j) x y u)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply actualFiniteExistentialElimination body α 3 Delta _ psi h
  apply k (α ⊕ Fin 3) Sum.inl _ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem transportedOutputsCases (Gamma : List Ty) (p : Selection) (tau : Ty)
    (out other lifted : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Delta (transportedOutputsExist Gamma p tau out other lifted)))
    (k : ∀ (β : Type) (j : α → β) (Theta : List (Formula β)) (x y : OTerm β),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (transportedOutputs Gamma p tau
        (out.relabel j) (other.relabel j) (lifted.relabel j) x y)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply actualFiniteExistentialElimination body α 2 Delta _ psi h
  apply k (α ⊕ Fin 2) Sum.inl _ (.var (.inr 0)) (.var (.inr 1))
  · intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

/-- Use the actual source wrapper's certificate closure before raw extraction. -/
theorem certificateTyped (K : Nat) (Gamma : List Ty) (p : Selection)
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1) (tau : Ty)
    (f g witness : OTerm α)
    (ht : Nonempty (Derivation body Delta
      (InternalComputabilityApplication.typed (comp K Gamma p) tau (numeral K) f)))
    (hp : Nonempty (Derivation body Delta
      (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness))) :
    Nonempty (Derivation body Delta
      (InternalComputabilityApplication.typed (comp K Gamma p) tau (numeral K) g)) :=
  GuardedSourceCertificateProof.certificateClosure
    (GammaGuardedSource.baseTyped (patchedComp K Gamma p).typed InternalOriginalObjectFiberSourceDispatch.valid)
    (GammaGuardedSource.basePositive (patchedSource K Gamma p).positive InternalOriginalObjectFiberSourceDispatch.gamma)
    InternalOriginalObjectFiberSourceDispatch.tag p.window (numeral K) (numeral (typeNumber tau)) f g witness
    (GuardedSourceCertificateProof.windowNumeral p.window K hw) ht hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
