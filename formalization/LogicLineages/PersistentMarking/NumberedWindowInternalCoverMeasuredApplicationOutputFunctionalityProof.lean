module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallReportCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z emb eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePair (pairTerm fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitter
  (rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports arrowReports)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (reportUnfold reportInstance auxiliaryRename threeRename)
open NumberedWindowInternalSparseApplicationReinstallReportCasesProof (coherent)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs applicationReport)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (row someRow rowCases)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)
open NumberedWindowInternalCoverCombinedMeasuredInstallProof (exact_InstalledApplicationReport)
open NumberedWindowInternalCoverMeasuredApplicationFrontendAcceptanceProof
  (exact_InstalledApplicationFrontendAcceptance)
open NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityTargets

attribute [local irreducible] programGraph

private theorem addressRename {α β : Type} (c e k : OTerm α) (j : α → β) :
    (addressTerm c e k).relabel j = addressTerm (c.relabel j) (e.relabel j) (k.relabel j) := by
  simp only [addressTerm,consTerm,pairTerm,addRelabel,mulRelabel,sucRelabel,zRelabel,numeralRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Two-argument congruence of the sparse cell constructor, from the actual
constructor graph: move both inputs along the equations, then use that the
constructor program has one value. -/
private theorem consEqual (x y u v : OTerm α)
    (first : Nonempty (Derivation body Γ (eqn x u)))
    (second : Nonempty (Derivation body Γ (eqn y v))) :
    Nonempty (Derivation body Γ (eqn (rawCons x y) (rawCons u v))) := by
  let before : Fin 2 → OTerm α := ![x,y]
  let after : Fin 2 → OTerm α := ![u,v]
  have input (i : Fin 2) :
      Nonempty (Derivation body Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases first (Fin.cases second (fun n => Fin.elim0 n)) i
  have old : Nonempty (Derivation body Γ (programGraph fieldCons (rawCons x y) before)) :=
    consGraph x y
  unfold programGraph at old
  have moved : Nonempty (Derivation body Γ (programGraph fieldCons (rawCons x y) after)) := by
    unfold programGraph
    exact graphInputTransport body α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (rawCons x y) before after input old
  exact valueUnique fieldCons (rawCons x y) (rawCons u v) after moved (consGraph u v)

private theorem auxiliaryEqual (d e l a d' e' l' a' : OTerm α)
    (hd : Nonempty (Derivation body Γ (eqn d d')))
    (he : Nonempty (Derivation body Γ (eqn e e')))
    (hl : Nonempty (Derivation body Γ (eqn l l')))
    (ha : Nonempty (Derivation body Γ (eqn a a'))) :
    Nonempty (Derivation body Γ (eqn (auxiliaryTerm d e l a) (auxiliaryTerm d' e' l' a'))) := by
  have h4 := consEqual a z a' z ha ⟨refl z⟩
  have h3 := consEqual l _ l' _ hl h4
  have h2 := consEqual e _ e' _ he h3
  have h1 := consEqual d _ d' _ hd h2
  exact consEqual _ _ _ _ ⟨refl _⟩ h1

private theorem addressEqual (c e k c' e' k' : OTerm α)
    (hc : Nonempty (Derivation body Γ (eqn c c')))
    (he : Nonempty (Derivation body Γ (eqn e e')))
    (hk : Nonempty (Derivation body Γ (eqn k k'))) :
    Nonempty (Derivation body Γ (eqn (addressTerm c e k) (addressTerm c' e' k'))) := by
  have h3 := consEqual k z k' z hk ⟨refl z⟩
  have h2 := consEqual e _ e' _ he h3
  have h1 := consEqual c _ c' _ hc h2
  exact consEqual _ _ _ _ ⟨refl _⟩ h1

/-- Move all three inputs of one ternary program call along equations. -/
private theorem ternaryTransport (p : Program 3) (out c e raw c' e' raw' : OTerm α)
    (hc : Nonempty (Derivation body Γ (eqn c c')))
    (he : Nonempty (Derivation body Γ (eqn e e')))
    (hr : Nonempty (Derivation body Γ (eqn raw raw')))
    (old : Nonempty (Derivation body Γ (programGraph p out ![c,e,raw]))) :
    Nonempty (Derivation body Γ (programGraph p out ![c',e',raw'])) := by
  let before : Fin 3 → OTerm α := ![c,e,raw]
  let after : Fin 3 → OTerm α := ![c',e',raw']
  have input (i : Fin 3) :
      Nonempty (Derivation body Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases hc (Fin.cases he (Fin.cases hr (fun n => Fin.elim0 n))) i
  have start : Nonempty (Derivation body Γ (programGraph p out before)) := old
  unfold programGraph at start
  have moved : Nonempty (Derivation body Γ (programGraph p out after)) := by
    unfold programGraph
    exact graphInputTransport body α 3 Γ (OrdinaryArithmetic.graphFormula p) out before after input start
  exact moved

/-- The original output report at the literal output address: the supplied
least call is the genuine single witness, and the address equation is
reflexivity. -/
private theorem outputFromLeast (least : Program 3) (ctx cod raw m : OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph least (suc m) ![ctx,cod,raw]))) :
    Nonempty (Derivation body Γ (outputReport least ctx cod raw (addressTerm ctx cod m))) := by
  obtain ⟨actual⟩ := selected
  rw [reportUnfold]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb m)
  rw [reportInstance]
  exact Derivation.conjunctionIntroduction actual (refl (addressTerm ctx cod m))

/-- The five operand fields that pin the block witnesses: context, domain,
codomain and class of the function address, and the class of the argument
address. The domain and codomain fields come from the literal sparse cell in
the function's result slot. -/
private theorem operandFields (qf qa ctx dom cod fn arg : OTerm α)
    (functionReport : Nonempty (Derivation body Γ (addressReport qf ctx (rawCons dom cod) fn)))
    (argumentReport : Nonempty (Derivation body Γ (addressReport qa ctx dom arg))) :
    Nonempty (Derivation body Γ (unary rawContext ctx qf)) ∧
    Nonempty (Derivation body Γ (unary rawDomain dom qf)) ∧
    Nonempty (Derivation body Γ (unary rawCodomain cod qf)) ∧
    Nonempty (Derivation body Γ (unary rawLeast fn qf)) ∧
    Nonempty (Derivation body Γ (unary rawLeast arg qa)) := by
  obtain ⟨fr⟩ := functionReport
  obtain ⟨ar⟩ := argumentReport
  have leftContext : Derivation body Γ (unary rawContext ctx qf) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight fr)
  have leftResult : Derivation body Γ (unary rawResult (rawCons dom cod) qf) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight fr))
  have leftLeast : Derivation body Γ (unary rawLeast fn qf) :=
    Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight fr))
  have rightLeast : Derivation body Γ (unary rawLeast arg qa) :=
    Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight ar))
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) dom cod
  have cellDom : Nonempty (Derivation body Γ (unary cellHead dom (rawCons dom cod))) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have cellCod : Nonempty (Derivation body Γ (unary cellTail cod (rawCons dom cod))) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  have domainField : Nonempty (Derivation body Γ (unary rawDomain dom qf)) :=
    makeUnary cellHead rawResult dom qf (rawCons dom cod) cellDom ⟨leftResult⟩
  have codomainField : Nonempty (Derivation body Γ (unary rawCodomain cod qf)) :=
    makeUnary cellTail rawResult cod qf (rawCons dom cod) cellCod ⟨leftResult⟩
  exact ⟨⟨leftContext⟩,domainField,codomainField,⟨leftLeast⟩,⟨rightLeast⟩⟩

/-- Functionality of the original application row for an arbitrary least
program. Open the six-witness block, identify every fresh witness that the
output report uses with the caller's coordinate by functionality of the five
field programs, move the held least call to the witnesses, and let the
accepted same-input coherence of output reports fix the output. -/
private theorem rowFunctional (least : Program 3) (qf qa y ctx dom cod fn arg m : OTerm α)
    (context : Nonempty (Derivation body Γ (unary rawContext ctx qf)))
    (domain : Nonempty (Derivation body Γ (unary rawDomain dom qf)))
    (codomain : Nonempty (Derivation body Γ (unary rawCodomain cod qf)))
    (fnField : Nonempty (Derivation body Γ (unary rawLeast fn qf)))
    (argField : Nonempty (Derivation body Γ (unary rawLeast arg qa)))
    (selected : Nonempty (Derivation body Γ
      (programGraph least (suc m) ![ctx,cod,auxiliaryTerm dom cod fn arg])))
    (bound : Nonempty (Derivation body Γ (someRow least qf qa y))) :
    Nonempty (Derivation body Γ (eqn y (addressTerm ctx cod m))) := by
  apply rowCases least qf qa y (eqn y (addressTerm ctx cod m)) bound
  intro β j Δ c r d e l a keep known
  rw [eqnRelabel,addressRename]
  have context' := renameInto context j Δ keep
  have domain' := renameInto domain j Δ keep
  have codomain' := renameInto codomain j Δ keep
  have fnField' := renameInto fnField j Δ keep
  have argField' := renameInto argField j Δ keep
  simp only [unaryRename] at context' domain' codomain' fnField' argField'
  have selected' := renameInto selected j Δ keep
  simp only [programRename,threeRename,sucRelabel,auxiliaryRename] at selected'
  obtain ⟨known⟩ := known
  have parsed : Derivation body Δ
      (parsedApplicationInputs (qf.relabel j) (qa.relabel j) c r d e l a) :=
    Derivation.conjunctionLeft known
  have output : Derivation body Δ
      (outputReport least c e (auxiliaryTerm d e l a) (y.relabel j)) :=
    Derivation.conjunctionRight known
  have fields := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight parsed))
  have leftFields : Derivation body Δ (addressReports (qf.relabel j) c r l) :=
    Derivation.conjunctionLeft fields
  have rightFields : Derivation body Δ (addressReports (qa.relabel j) c d a) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight fields)
  have arrowFields : Derivation body Δ (arrowReports (qf.relabel j) d e) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight fields))
  obtain ⟨sameContext⟩ := valueUnique rawContext (ctx.relabel j) c ![qf.relabel j] context'
    ⟨Derivation.conjunctionLeft leftFields⟩
  have sameFunction := valueUnique rawLeast (fn.relabel j) l ![qf.relabel j] fnField'
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight leftFields)⟩
  have sameArgument := valueUnique rawLeast (arg.relabel j) a ![qa.relabel j] argField'
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight rightFields)⟩
  have sameDomain := valueUnique rawDomain (dom.relabel j) d ![qf.relabel j] domain'
    ⟨Derivation.conjunctionLeft arrowFields⟩
  obtain ⟨sameCodomain⟩ := valueUnique rawCodomain (cod.relabel j) e ![qf.relabel j] codomain'
    ⟨Derivation.conjunctionRight arrowFields⟩
  have sameAuxiliary := auxiliaryEqual (dom.relabel j) (cod.relabel j) (fn.relabel j)
    (arg.relabel j) d e l a sameDomain ⟨sameCodomain⟩ sameFunction sameArgument
  have moved := ternaryTransport least (suc (m.relabel j)) (ctx.relabel j) (cod.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j))
    c e (auxiliaryTerm d e l a) ⟨sameContext⟩ ⟨sameCodomain⟩ sameAuxiliary selected'
  have emitted := outputFromLeast least c e (auxiliaryTerm d e l a) (m.relabel j) moved
  obtain ⟨first⟩ := coherent least c e (auxiliaryTerm d e l a) (y.relabel j)
    (addressTerm c e (m.relabel j)) ⟨output⟩ emitted
  obtain ⟨back⟩ := addressEqual c e (m.relabel j) (ctx.relabel j) (cod.relabel j) (m.relabel j)
    ⟨symm sameContext⟩ ⟨symm sameCodomain⟩ ⟨refl (m.relabel j)⟩
  exact ⟨trans first back⟩

theorem exact_InstalledApplicationOutputFunctionality :
    ExactInstalledApplicationOutputFunctionality := by
  intro V TV M M0 B T base s cv tv root other body α Γ qf qa ctx dom cod fn arg m y Q
    functionReport argumentReport least accepted
  obtain ⟨context,domain,codomain,fnField,argField⟩ :=
    operandFields qf qa ctx dom cod fn arg functionReport argumentReport
  obtain ⟨accepted⟩ := accepted
  obtain ⟨law⟩ := exact_InstalledApplicationReport V TV M M0 B T base s cv tv root other
    body α Γ qf qa y
  have reported : Derivation body Γ (applicationReport Q.scalar Q.least qf qa y) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft law) accepted
  have selected : Nonempty (Derivation body Γ
      (programGraph Q.least (suc m) ![ctx,cod,auxiliaryTerm dom cod fn arg])) := least
  exact rowFunctional Q.least qf qa y ctx dom cod fn arg m context domain codomain fnField
    argField selected ⟨Derivation.conjunctionRight (Derivation.conjunctionRight reported)⟩

theorem exact_InstalledApplicationOutputFunctionalityContinuation :
    ExactInstalledApplicationOutputFunctionalityContinuation := by
  intro V TV M M0 B T base s cv tv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty result functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨context,domain,codomain,fnField,argField⟩ :=
    operandFields qf qa ctx dom cod fn arg functionReport argumentReport
  apply exact_InstalledApplicationFrontendAcceptance V TV M M0 B T base s cv tv root other body α Γ
    qf qa ctx dom cod fn arg goal syn ty result functionReport argumentReport
    functionAccepted argumentAccepted
  intro β j Δ m keep least report accepted graph
  apply finish β j Δ m keep least report accepted graph
  intro y
  let call : Formula β := programGraph Q.application (suc z) ![qf.relabel j,qa.relabel j,y]
  have keep' : ∀ p ∈ Γ, p.relabel j ∈ call :: Δ :=
    fun p hp => List.mem_cons_of_mem _ (keep p hp)
  have context' := renameInto context j (call :: Δ) keep'
  have domain' := renameInto domain j (call :: Δ) keep'
  have codomain' := renameInto codomain j (call :: Δ) keep'
  have fnField' := renameInto fnField j (call :: Δ) keep'
  have argField' := renameInto argField j (call :: Δ) keep'
  simp only [unaryRename] at context' domain' codomain' fnField' argField'
  have selected : Nonempty (Derivation body (call :: Δ)
      (programGraph Q.least (suc m) ![ctx.relabel j,cod.relabel j,
        auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)])) := by
    have moved := least
    rw [auxiliaryRename] at moved
    obtain ⟨moved⟩ := moved
    exact ⟨Derivation.weakening (fun p hp => List.mem_cons_of_mem _ hp) moved⟩
  have here : Derivation body (call :: Δ) call := Derivation.hypothesis List.mem_cons_self
  obtain ⟨law⟩ := exact_InstalledApplicationReport V TV M M0 B T base s cv tv root other
    body β (call :: Δ) (qf.relabel j) (qa.relabel j) y
  have reported : Derivation body (call :: Δ)
      (applicationReport Q.scalar Q.least (qf.relabel j) (qa.relabel j) y) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft law) here
  obtain ⟨same⟩ := rowFunctional Q.least (qf.relabel j) (qa.relabel j) y (ctx.relabel j)
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) m
    context' domain' codomain' fnField' argField' selected
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight reported)⟩
  exact ⟨Derivation.implicationIntroduction same⟩

theorem exact_InstalledSyntaxGuardedApplicationOutputFunctionalityContinuation :
    ExactInstalledSyntaxGuardedApplicationOutputFunctionalityContinuation := by
  intro V TV M M0 B T base s cv root other body α Γ qf qa ctx dom cod fn arg goal Q
    syn ty functionReport argumentReport functionAccepted argumentAccepted finish
  obtain ⟨guards⟩ := syn
  exact exact_InstalledApplicationOutputFunctionalityContinuation V TV M M0 B T base s cv TV
    root other body α Γ qf qa ctx dom cod fn arg goal ⟨guards⟩ ty
    ⟨Derivation.conjunctionRight guards⟩ functionReport argumentReport functionAccepted
    argumentAccepted finish

#print axioms exact_InstalledApplicationOutputFunctionality
#print axioms exact_InstalledApplicationOutputFunctionalityContinuation
#print axioms exact_InstalledSyntaxGuardedApplicationOutputFunctionalityContinuation
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationOutputFunctionalityProof
