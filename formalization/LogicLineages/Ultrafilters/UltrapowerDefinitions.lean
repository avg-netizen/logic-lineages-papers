module

public import LogicLineages.Ultrafilters.Definitions
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace LogicLineages.Ultrafilters

/-- The actual quotient of real-valued functions by equality modulo p. -/
abbrev RealUltrapower (p : Ultrafilter ℝ) := Filter.Germ (p : Filter ℝ) ℝ

def classOf (p : Ultrafilter ℝ) (f : ℝ → ℝ) : RealUltrapower p := f

def constantClass (p : Ultrafilter ℝ) (r : ℝ) : RealUltrapower p :=
  classOf p (fun _ => r)

/-- The source domain is existential over representatives, not a regularity
test on one distinguished representative of the quotient. -/
def differentiationDomain (p : Ultrafilter ℝ) : Set (RealUltrapower p) :=
  {z | ∃ f : ℝ → ℝ, classOf p f = z ∧ {x | DifferentiableAt ℝ f x} ∈ p}

end LogicLineages.Ultrafilters
