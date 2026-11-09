module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalAcceptanceConjunctionProof
open GammaGuardedSourceGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- An actual original guard gives the argument the function's symbolic
Gamma value. No meta-level Gamma is selected. -/
theorem argumentGamma (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (f a gammaCode : OTerm α)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hg : Nonempty (Derivation body Delta
      (guarded (Outer.computability old data window oldVertex oldResult) f a))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode a)) := by
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons a Fin.elim0)
  have hc := conjunctionRecover (GammaGuardedSource.atInput Outer.valid 0)
    (InternalAcceptance.conjunction (GammaGuardedSource.atInput Outer.valid 1)
      (GammaGuardedSource.sameGamma Outer.gamma 0 1)) xs hg
  have hd := conjunctionRecover (GammaGuardedSource.atInput Outer.valid 1)
    (GammaGuardedSource.sameGamma Outer.gamma 0 1) xs (andRight hc)
  have ha := TypingCoreProof.sameLeftRecover
    (GammaGuardedSource.atInput Outer.gamma 0) (GammaGuardedSource.atInput Outer.gamma 1)
    gammaCode xs (andRight hd) (atInputValue Outer.gamma 0 gammaCode xs hf)
  exact atInputRecover Outer.gamma 1 gammaCode xs ha

/-- Every accepted original source certificate preserves that SAME
symbolic Gamma, including when its typed activation takes either branch. -/
theorem targetGamma (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (context : Nat) (f g witness gammaCode : OTerm α)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hp : Nonempty (Derivation body Delta
      (certificate (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
        false context f g witness))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode g)) := by
  let positive := Outer.positive (Outer.rawPositive data oldStep bottom measure) window oldSrc.positive
  let typed := GammaGuardedSource.baseTyped (Outer.typed data window oldComp.typed) Outer.valid
  let xs : Fin 4 → OTerm α :=
    Fin.cons (numeral context) (Fin.cons f (Fin.cons g (Fin.cons witness Fin.elim0)))
  have hb := GammaGuardedSourceBranchProof.guardedPositiveRecover
    (GammaGuardedSource.basePositive positive Outer.gamma) typed Outer.tag window xs hp
  have hc := conjunctionRecover positive (GammaGuardedSource.sameGamma Outer.gamma 1 2) xs hb
  have hg := TypingCoreProof.sameLeftRecover
    (GammaGuardedSource.atInput Outer.gamma 1) (GammaGuardedSource.atInput Outer.gamma 2)
    gammaCode xs (andRight hc) (atInputValue Outer.gamma 1 gammaCode xs hf)
  exact atInputRecover Outer.gamma 2 gammaCode xs hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
