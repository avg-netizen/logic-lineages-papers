module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.Definitions
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
open OriginalDomain FunctionalDetector SourceCollisionCompletion

def pullback {Γ Δ : List Ty} (r : Renaming Γ Δ) (ρ : AdmissibleSubstitution Δ) :
    AdmissibleSubstitution Γ where
  vector := fun {_} x j => ρ.vector (r x) j
  graded := fun x j => ρ.graded (r x) j
  bounded := fun x j => ρ.bounded (r x) j

def Preserves {Γ Δ : List Ty} (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution Γ) (σ : AdmissibleSubstitution Δ) : Prop :=
  ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), σ.vector (r x) j = ρ.vector x j

structure CompiledSystem (n : Nat) where
  context : List Ty
  original : Renaming (SignedPair.Context n) context
  detectors : List (OriginalTerm context .ground × OriginalTerm context .ground)

/-- Two independent fresh ground alignment witnesses per equation. Every
equation retains the same original functional names through `original`. -/
def compileSystem {n : Nat} : System n → CompiledSystem n
  | [] => ⟨SignedPair.Context n, (fun {_} x => x), []⟩
  | d::ds =>
      let tail := compileSystem ds
      let a := (SignedPair.compile d).pair.1.rename tail.original
      let b := (SignedPair.compile d).pair.2.rename tail.original
      let aa := alignedLeft a
      let bb := alignedRight b
      ⟨.ground::.ground::tail.context,
       (fun {_} x => shiftTwo tail.context (tail.original x)),
       (left aa bb, right aa bb)::
         tail.detectors.map (fun p =>
           (p.1.rename (shiftTwo tail.context), p.2.rename (shiftTwo tail.context)))⟩

def strictSystemPair {n : Nat} (s : System n) :=
  SourceAggregateCompletion.aggregate (compileSystem s).detectors
def weakSystemPair {n : Nat} (s : System n) :=
  (ParametricLiteralWeakWrapper.constantApply (strictSystemPair s).2,
   ParametricLiteralWeakWrapper.identityApply (strictSystemPair s).1)

def universalStrictSystem {n : Nat} (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution (compileSystem s).context,
    rawScalar (valuation ρ) (strictSystemPair s).2 <
      rawScalar (valuation ρ) (strictSystemPair s).1
def universalWeakSystem {n : Nat} (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution (compileSystem s).context,
    rawScalar (valuation ρ) (weakSystemPair s).1 ≤
      rawScalar (valuation ρ) (weakSystemPair s).2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
