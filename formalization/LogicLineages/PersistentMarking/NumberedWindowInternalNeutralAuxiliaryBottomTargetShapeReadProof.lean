module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeReadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (outputTransport equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary packedBody unaryRename moveReport inputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood addressTag rawContext rawResult rawLeast)
open NumberedWindowInternalAuxBottomRefinement (sourceFlag auxShell auxHeadBottom resultFits auxFunction auxCodomain)
open NumberedWindowInternalNeutralAuxiliaryRefinement (auxDom auxFnType)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem auxCodomainFromFit (y cod : OTerm α)
    (fit : Nonempty (Derivation B Γ (unary resultFits (suc z) y)))
    (known : Nonempty (Derivation B Γ (unary rawResult cod y))) :
    Nonempty (Derivation B Γ (unary auxCodomain cod y)) := by
  apply programCases auxCodomain ![y] _
  intro β j Δ actual keep current
  rw [inputsRename] at current
  rw [unaryRename]
  have k := moveReport j Δ keep rawResult cod y known
  have f := moveReport j Δ keep resultFits (suc z) y fit
  simp only [sucRelabel,zRelabel,resultFits,exact_DispatchControlAST.2.2.2.1] at f
  let obs := cod.relabel j
  let t := y.relabel j
  have test := compositionRecover equalityTest (Fin.cons rawResult (Fin.cons auxCodomain Fin.elim0))
    (suc z) ![t] ![obs,actual] f
      (fun k' => Fin.cases k (Fin.cases current (fun l => Fin.elim0 l)) k')
  obtain ⟨eq⟩ := equalityOfAcceptance obs actual test
  exact outputTransport auxCodomain actual obs ![t] ⟨symm eq⟩ current

/-- Read the exact open packed shape at held physical selected outputs. -/
theorem readHeld (y c dom cod stored least fn arg : OTerm α)
    (flags : Nonempty (Derivation B Γ
      (unary sourceFlag (suc z) y ⊓
        (sourceFields y c cod ⊓ (unary auxDom dom y ⊓ unary auxFnType stored y)))))
    (leastReport : Nonempty (Derivation B Γ (unary rawLeast least y)))
    (functionReport : Nonempty (Derivation B Γ (unary auxFunction fn y)))
    (argReport : Nonempty (Derivation B Γ (unary (field 3) arg least))) :
    Nonempty (Derivation B Γ (equal y (packedAuxBottomTerm c dom cod stored arg))) := by
  obtain ⟨h⟩ := flags
  have ok : Nonempty (Derivation B Γ (unary sourceFlag (suc z) y)) := ⟨Derivation.conjunctionLeft h⟩
  have fields := Derivation.conjunctionRight h
  have pair := Derivation.conjunctionLeft fields
  have types := Derivation.conjunctionRight fields
  unfold sourceFlag at ok
  rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2] at ok
  obtain ⟨all⟩ := conjunctionRecover addressGood (conjunction auxShell (conjunction auxHeadBottom resultFits)) ![y] ok
  obtain ⟨inner⟩ := conjunctionRecover auxShell (conjunction auxHeadBottom resultFits) ![y] ⟨Derivation.conjunctionRight all⟩
  obtain ⟨last⟩ := conjunctionRecover auxHeadBottom resultFits ![y] ⟨Derivation.conjunctionRight inner⟩
  let three := literal 1 3
  let six := literal 1 6
  let bot := rawCons (numeral 3) (packedBody [stored])
  let raw := rawCons (numeral 6) (packedBody [dom,cod,bot,arg])
  have fnOk := takeUnary (nodeGood three 1) auxFunction (suc z) y fn
    ⟨Derivation.conjunctionLeft last⟩ functionReport
  have fnTy := takeUnary (field 0) auxFunction stored y fn
    ⟨Derivation.conjunctionRight types⟩ functionReport
  have fnEq := readNode three fn (numeral 3) [stored] (literalGraph 3 ![fn]) fnOk ⟨fnTy,True.intro⟩
  have fnBot : Nonempty (Derivation B Γ (unary auxFunction bot y)) :=
    outputTransport auxFunction fn bot ![y] fnEq functionReport
  have srcOk := takeUnary (nodeGood six 4) rawLeast (suc z) y least
    ⟨Derivation.conjunctionLeft inner⟩ leastReport
  have fit : Nonempty (Derivation B Γ (unary resultFits (suc z) y)) := ⟨Derivation.conjunctionRight last⟩
  have rawCod : Nonempty (Derivation B Γ (unary rawResult cod y)) := ⟨Derivation.conjunctionRight pair⟩
  -- resultFits compares rawResult with the physical field1 of the auxiliary.
  have auxCod := auxCodomainFromFit y cod fit rawCod
  have rawEq := readNode six least (numeral 6) [dom,cod,bot,arg] (literalGraph 6 ![least]) srcOk
    ⟨takeUnary (field 0) rawLeast dom y least ⟨Derivation.conjunctionLeft types⟩ leastReport,
      takeUnary (field 1) rawLeast cod y least auxCod leastReport,
      takeUnary (field 2) rawLeast bot y least fnBot leastReport,argReport,True.intro⟩
  have selected : Nonempty (Derivation B Γ (unary rawLeast raw y)) :=
    outputTransport rawLeast least raw ![y] rawEq leastReport
  rw [equalEqn]
  exact readNode addressTag y (numeral 3) [c,cod,raw] (literalGraph 3 ![y])
    ⟨Derivation.conjunctionLeft all⟩
    ⟨⟨Derivation.conjunctionLeft pair⟩,rawCod,selected,True.intro⟩

#print axioms readHeld
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeReadProof
