module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineMeasureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineInductionProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalTagArithmeticSyntaxProof (OTerm emb liftBind varBind)
open SourceComputabilityCompletion.TypedSpine TypedSpineSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem belowApply (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty)
    (depth next x mark : OTerm α)
    (hb : Nonempty (Derivation body Gamma
      (below (atDepth comp context tau (.var (.inr 0))) depth)))
    (hl : Nonempty (Derivation body Gamma (InternalOriginalOrderSyntaxProof.ltF next depth)))
    (ht : Nonempty (Derivation body Gamma
      (typed comp tau (SourceComputabilityFormulaSupportProof.numeral context) x)))
    (hm : Nonempty (Derivation body Gamma (marked x mark next))) :
    Nonempty (Derivation body Gamma (membership false x)) := by
  obtain ⟨hb⟩ := hb
  have h := Derivation.universalElimination (emb next) hb
  rw [belowElimSyntax,atDepthInstantiate] at h
  simp only [varBind] at h
  obtain ⟨hl⟩ := hl
  exact atDepthApply comp context tau next x mark
    ⟨Derivation.implicationElimination h hl⟩ ht hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineInductionProof
