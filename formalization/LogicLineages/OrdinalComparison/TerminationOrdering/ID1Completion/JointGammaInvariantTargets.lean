module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantTargets
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open NumberedLeastCodeRepresentative InternalCalculus JointGammaInvariant PositiveArithmeticSchemas

def ActualTaggedInvariantBranches : Prop :=
  ∀ (α : Type) (scalar multiset : Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) (x : Nat),
  (realize P (tagged scalar multiset) (Sum.elim v (fun _ => tagNumber false x)) ↔
    realize P scalar (Sum.elim v (fun _ => x))) ∧
  (realize P (tagged scalar multiset) (Sum.elim v (fun _ => tagNumber true x)) ↔
    realize P multiset (Sum.elim v (fun _ => x)))

def ActualOriginalReplacementBranches : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity →
  ∀ (context : Nat) (α : Type) (scalar multiset : Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat) (x : Nat),
  (realize P (replacedBody (SourcePresentation.sourceBody data context) (tagged scalar multiset))
      (Sum.elim v (fun _ => tagNumber false x)) ↔
    ContextUniform.encodedScalar n arity context x ∧
      ∀ y, ContextUniform.encodedR n arity context x y → realize P scalar (Sum.elim v (fun _ => y))) ∧
  (realize P (replacedBody (SourcePresentation.sourceBody data context) (tagged scalar multiset))
      (Sum.elim v (fun _ => tagNumber true x)) ↔
    ContextUniform.encodedList n arity context x ∧
      ∀ y, ContextUniform.encodedDirect n arity context x y → realize P multiset (Sum.elim v (fun _ => y)))

/-- An equivalence describing the obligation, NOT a proof of the obligation. -/
def ActualOriginalClosurePremise : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity →
  ∀ (context : Nat) (α : Type) (scalar multiset : Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (v : α → Nat),
  realize P (closurePremise (SourcePresentation.sourceBody data context) (tagged scalar multiset)) v ↔
  (∀ x, (ContextUniform.encodedScalar n arity context x ∧
      ∀ y, ContextUniform.encodedR n arity context x y → realize P scalar (Sum.elim v (fun _ => y))) →
    realize P scalar (Sum.elim v (fun _ => x))) ∧
  (∀ x, (ContextUniform.encodedList n arity context x ∧
      ∀ y, ContextUniform.encodedDirect n arity context x y → realize P multiset (Sum.elim v (fun _ => y))) →
    realize P multiset (Sum.elim v (fun _ => x)))

/-- The literal finite-S scalar invariant has the ORIGINAL fixed-Gamma truth.
The multiset invariant remains arbitrary, and has no effect at an even tag. -/
def ActualFiniteSourceInvariant : Prop :=
  ∀ (data : JointGammaComputability.Data) (n : Nat) (arity : Fin n → Nat),
  JointGammaComputability.Calibrated data n arity →
  ∀ (S : List Ty) (multiset : Formula (Fin 2 ⊕ Fin 1)) (P : Nat → Prop)
    (context typ : Nat) (Gamma : List Ty) (x : Nat),
  realize P (tagged (window data S) multiset)
      (Sum.elim ![context,typ] (fun _ => tagNumber false (ContextUniform.objectCode Gamma x))) ↔
    ∃ tau ∈ S, typ = typeNumber tau ∧ SourceComputabilityFormula.Computable n arity Gamma
      (fun a => P (tagNumber false (ContextUniform.objectCode Gamma a))) context tau x

/-- Pure syntactic admissibility. The exact closure DERIVATION is still
required; standard-N truth does not construct it. No positivity of the
invariant is assumed or asserted. The sole inductive body is unchanged. -/
def ActualInternalTaggedInduction : Prop :=
  ∀ (data : SourcePresentation.Data) (context : Nat) (α : Type)
    (Gamma : List (Formula α)) (scalar multiset : Formula (α ⊕ Fin 1)) (t : Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody data context)
    (replacedBody (SourcePresentation.sourceBody data context) (tagged scalar multiset) :: Gamma.map weaken)
    (tagged scalar multiset)) →
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
    (SourceComputabilityFormulaSupportProof.allOne (predicateAtObject.imp (tagged scalar multiset)))) ∧
  Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
    (instantiate (predicateAtObject.imp (tagged scalar multiset)) t))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantTargets
