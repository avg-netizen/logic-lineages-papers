module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxPartialsCodeCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ::Γ) m),
    partialsCode σ.level m (vectorCode h) =
      (AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run allLeftPolicy i.val (h i))).map
        (fun ps => List.ofFn (fun i => List.ofFn (fun j => typedCode (ps i j))))

def OrdinalSyntaxAbstractionCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ::Γ) m),
    abstractionCode σ.level m (vectorCode h) =
      (AdmissibleAssignment.abstraction allLeftPolicy h).map vectorCode

def OrdinalSyntaxAbstractionPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × List Nat => abstractionCode p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.Targets
