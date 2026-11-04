module
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Targets

def FiniteBoundary : Prop := ∀ G : Nat → Nat,(∀ n : Nat,n≤G n) → ∀ b : Nat,
  ParametricFinitePairCollapse.value G (0,b)=b ∧ formula G (0,b)=b

def ExactMaximizer : Prop := ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat,n≤G n) → ∀ a b : Nat,
  maximizer G a b ∈ ParametricFinitePairCollapse.predecessors G (a+1,b) ∧
  ParametricFinitePairCollapse.pairNorm (maximizer G a b)=G (2*(a+1)+b) ∧
  formula G (maximizer G a b)+1=formula G (a+1,b) ∧
  (∀ q ∈ ParametricFinitePairCollapse.predecessors G (a+1,b),
    formula G q+1 ≤ formula G (a+1,b))

def ExactFiniteCoefficient : Prop := ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat,n≤G n) → ∀ a b : Nat,
  ParametricFinitePairCollapse.value G (a,b)=(G^[a]) (2*a+b)+a
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Targets
