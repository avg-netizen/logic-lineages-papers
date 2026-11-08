module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Introduction for the unchanged arrow formula, with all original guards
and the computable existential output. The ambient assumptions are retained. -/
def ActualOriginalArrowIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (comp : JointGammaComputability.Data) (α : Type)
    (Gamma : List (Formula α)) (sigma tau : Ty) (context f : OTerm α),
  Nonempty (Derivation body Gamma (typed comp (.arrow sigma tau) context f)) →
  Nonempty (Derivation body
    (computable comp sigma (context.relabel Sum.inl) (.var (.inr 0)) ::
      guarded comp (f.relabel Sum.inl) (.var (.inr 0)) :: Gamma.map weaken)
    (resultExists comp sigma tau (context.relabel Sum.inl) (f.relabel Sum.inl) (.var (.inr 0)))) →
  Nonempty (Derivation body Gamma (computable comp (.arrow sigma tau) context f))

/-- Complete finite type induction for downward closure. The hypotheses are
exactly the displayed local arithmetic derivations; none assumes C closure. -/
def ActualOriginalComputabilityDownward : Prop :=
  ∀ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (context : Nat),
  ArithmeticRules src comp context → ApplicationCompatibility src comp context →
  ∀ (tau : Ty) (α : Type) (Gamma : List (Formula α)) (f g : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (computable comp tau (numeral context) f)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (edge src false context f g)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (computable comp tau (numeral context) g))

/-- Eliminate the input certificate and the original Program's output witness
internally. A concrete certified lift suffices for the local relation rule. -/
def ActualOriginalCertifiedLiftReduction : Prop :=
  ∀ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (lift : Program 5) (context : Nat),
  CertifiedApplicationLift src comp lift context → ApplicationCompatibility src comp context

/-- One calibrated source/computability pair and one calibrated original path
transformer precede every source window. All arithmetic suppliers are proved;
only the explicitly named internal certificate-lift theorem remains conditional.
This is a reduction of the remaining task, not a claim that the lift is proved. -/
def ActualUniformSourceDownwardReduction : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (lift : Program 5),
  ContextUniform.Calibrated src n arity ∧
  JointGammaComputability.Calibrated comp n arity ∧
  (∀ v, evaluate lift v = ApplicationCertificateLiftPath.pathValue n arity v) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    ArithmeticRules src comp context ∧
    (CertifiedApplicationLift src comp lift context →
      ∀ (tau : Ty) (α : Type) (f g : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) []
        ((computable comp tau (numeral context) f ⊓ edge src false context f g).imp
          (computable comp tau (numeral context) g)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardTargets
