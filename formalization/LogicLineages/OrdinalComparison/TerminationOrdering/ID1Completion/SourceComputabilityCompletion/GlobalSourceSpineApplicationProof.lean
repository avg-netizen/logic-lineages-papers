module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputCasesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineApplicationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalComputabilityDownward InternalComputabilityDownwardSyntaxProof
open InternalComputabilityApplicationSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof GuardedSourceSyntaxProof
open SourceComputabilityCompletion.TypedSpine GlobalSourceSpineSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem resultComputable {body : Positive (Fin 1)}
    (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hbase : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hwindow : Path.windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S))
    (oldComp : JointGammaComputability.Data) (oldVertex oldResult : Program 5) (sigma tau : Ty) :
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    let comp := OuterSelection.computability oldComp base window oldVertex oldResult
    ∀ (α : Type) (Gamma : List (Formula α)) (f a out functionMark depth : OTerm α),
    (∀ (β : Type) (Delta : List (Formula β)) (x mark depth : OTerm β),
      Nonempty (Derivation body Delta (typed comp tau (numeral context) x)) →
      Nonempty (Derivation body Delta (marked x mark depth)) →
      Nonempty (Derivation body Delta (computable comp tau (numeral context) x))) →
    Nonempty (Derivation body Gamma (domain comp context sigma tau f a)) →
    Nonempty (Derivation body Gamma (accepted comp sigma tau (numeral context) f a out)) →
    Nonempty (Derivation body Gamma (marked f functionMark depth)) →
    Nonempty (Derivation body Gamma (computable comp tau (numeral context) out)) := by
  dsimp only
  intro α Gamma f a out functionMark depth ih hd haccepted hm
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := OuterSelection.data base window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  apply programCases InternalPairing.pairing
    (Fin.cons InternalOriginalStepGuard.one (Fin.cons (suc depth) Fin.elim0)) _
  intro β j Delta resultMark hj hpair
  simp only [computableRename,numeralRename]
  simp only [consTermRename,emptyRename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hpair
  have hd' := renameInto hd j Delta hj
  rw [domainRename] at hd'
  have ha' := renameInto haccepted j Delta hj
  simp only [acceptedRename,numeralRename] at ha'
  have hm' := renameInto hm j Delta hj
  rw [markedRename] at hm'
  apply OuterInputCasesProof.inputCases data window oldVertex context sigma tau
    (f.relabel j) (f.relabel j) (a.relabel j) _
  intro γ k gammaCode function duplicate argument parameter rawOut other Theta hk
    hgamma hfunction hduplicate hargument hparameter hvertex hother
  simp only [computableRename,numeralRename]
  have hdd := renameInto hd' k Theta hk
  rw [domainRename] at hdd
  have haa := renameInto ha' k Theta hk
  simp only [acceptedRename,numeralRename] at haa
  have hmm := renameInto hm' k Theta hk
  rw [markedRename] at hmm
  have hpp := renameInto hpair k Theta hk
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hpp
  exact GlobalSourceSpineApplicationCoreProof.resultAtCoordinates n arity base hbase window hwindow
    symbols S table hS oldComp oldVertex oldResult sigma tau γ Theta
    ((f.relabel j).relabel k) ((a.relabel j).relabel k) ((out.relabel j).relabel k)
    ((functionMark.relabel j).relabel k) ((depth.relabel j).relabel k)
    gammaCode function argument parameter rawOut (resultMark.relabel k)
    (ih γ Theta) hdd haa hmm hgamma hfunction hargument hparameter hvertex hpp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineApplicationProof
