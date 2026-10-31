module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanCompiler.Targets
open OriginalDomain GroundEquivalence
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def SourceObservations : Prop :=
  (∀ Γ (t : Input Γ .ground) (ρ : Variable Γ .ground → Nat),
    ∃ v : OrdinalVector Γ 0,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t.term=some v ∧
      denote (valuation (UnitObservation.substitution ρ)) (v 0)=((sourceValue ρ t+1 : Nat) : Ordinal)) ∧
  ∀ Γ (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground),
    (call h x).term=.app (h.term.rename (emptyRename Γ)) (.var x) ∧
    (call h x).specs.length=h.specs.length+2

/-- Whole thm:compiler for a concrete complete finite arithmetic/Boolean DAG
encoding. All five input constructors have executable source lowering; binary
literals carry logarithmic budget; arbitrary supplied source tables and shared
names use the actual full assignment, not an arithmetic oracle. The output is
a literal primitive source DAG in the SAME representation as supplied tables. -/
def FullSourceBooleanCompiler : Prop :=
  SourceObservations ∧
  (∀ Γ (p : Program Γ) (ρ : Variable Γ .ground → Nat),
    Eval ρ p ↔ ExistentialPlan.Eval ρ (lower p)) ∧
  (∀ Γ (p : Program Γ),
    p.load ≤ p.codeSize*(p.sourceMax+1) ∧
    (lower p).vertices ≤ 1000*p.load ∧ (lower p).equations ≤ 1000*p.load ∧
    (lower p).witnesses ≤ 1000*p.load) ∧
  ∀ Γ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (p : Program Γ),
    (Strict (strictPair p).1.term (strictPair p).2.term ↔ ¬ ∃ ρ, Eval ρ p) ∧
    (Weak (weakPair p).1.term (weakPair p).2.term ↔ ¬ ∃ ρ, Eval ρ p) ∧
    (∀ σ ∈ (ExistentialPlan.compile (lower p)).context, σ=Ty.ground) ∧
    (ExistentialPlan.compile (lower p)).context.length ≤ Γ.length+1000*p.codeSize*(p.sourceMax+1) ∧
    (strictPair p).1.specs.length ≤ budget p ∧ (strictPair p).2.specs.length ≤ budget p ∧
    (weakPair p).1.specs.length ≤ budget p ∧ (weakPair p).2.specs.length ≤ budget p
end LogicLineages.OrdinalComparison.Source.BooleanCompiler.Targets
