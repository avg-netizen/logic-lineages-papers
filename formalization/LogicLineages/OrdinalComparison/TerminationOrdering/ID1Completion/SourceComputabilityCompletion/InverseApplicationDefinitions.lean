module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplication
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original typed/same-Gamma application domain implies membership in
the original scalar carrier. This is an explicit arithmetic rule to prove at
source assembly, not a field of a replacement source presentation. -/
def DomainCarrier (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) : Prop :=
  ∀ (α : Type) (sigma tau : Ty) (f a : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    ((domain comp context sigma tau f a).imp (carrier src false context f)))

/-- Preserve the exact application domain at a source successor, including
the SAME-Gamma guard in the forward direction. The old guardBack theorem
alone does not supply this arithmetic rule. -/
def DomainForward (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) : Prop :=
  ∀ (α : Type) (sigma tau : Ty) (f g a : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    (((domain comp context sigma tau f a) ⊓ edge src false context f g).imp
      (domain comp context sigma tau g a)))

/-- Original-application inverse image used as an arbitrary full-language
invariant of the SAME scalar slice. Its conclusion contains the current I
predicate; it is not a new inductive operator or an accessibility oracle. -/
def inverseInvariant {α : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (a : OTerm α) : Formula (α ⊕ Fin 1) :=
  allOne
    (((domain comp context sigma tau (.var (.inr (0 : Fin 1)))
        ((a.relabel Sum.inl).relabel Sum.inl)) ⊓
      accepted comp sigma tau (numeral context) (.var (.inr (0 : Fin 1)))
        ((a.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr (0 : Fin 1))))).imp
      (membership false (.var (.inr (0 : Fin 1)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplication
