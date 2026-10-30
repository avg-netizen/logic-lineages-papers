module
public import LogicLineages.ModelsAlgebra.PGroups.RawSemanticsDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth
universe u

def groupRawCountableConjunction : Prop :=
  ∀ (ι : Type) [Countable ι] (n : ℕ) (m : ι → ℕ)
    (matrix : (i : ι) → Formula (n + m i)) (G : Type u) (R : RawGroupStructure G) (a : Fin n → G),
    (countableConjAll m matrix).RawRealize R a ↔
      ∀ i : ι, ∀ d : Fin (m i) → G, (matrix i).RawRealize R (append a d)

def groupRawPiConjunction : Prop :=
  ∀ (n : ℕ) (φ ψ : Formula n) (G : Type u) (R : RawGroupStructure G) (a : Fin n → G),
    (piConjunction φ ψ).RawRealize R a ↔ φ.RawRealize R a ∧ ψ.RawRealize R a

def groupRawDifferenceAgreement : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (d : DifferenceFormula n),
    d.RawRealize (RawGroupStructure.ofGroup G) a ↔ d.Realize a

end LogicLineages.ModelsAlgebra.PGroups.Targets
