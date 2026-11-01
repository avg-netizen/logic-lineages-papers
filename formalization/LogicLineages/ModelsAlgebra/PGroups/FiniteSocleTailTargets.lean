module
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
/-- Literal ordinary Sigma_(2gamma+1) tuple-orbit definitions when the
actual omega*gamma tail has finite socle. The whole group may have an
arbitrary infinite reduced part below that cut. -/
def finiteSocleTailTupleOrbits : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType], 0<γ →
    (∀x:G,∃k:ℕ,p^k • x=0) →
    Finite (pSocle p (⊤:AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G))) →
    ∀ (n:ℕ) (a:Fin n→G), ∃φ:Formula n, Complexity .sigma (2*γ+1) φ ∧
      ∀b:Fin n→G, φ.Realize b ↔ TupleOrbit a b
/-- Actual lower difference Scott description at every positive-gamma even
index in the finite-socle-tail case; no Miller or orbit premise is input. -/
def finiteSocleTailSigmaLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType], 0<γ →
    (∀x:G,∃k:ℕ,p^k • x=0) →
    Finite (pSocle p (⊤:AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G))) →
    ∀φ:Formula 0, Complexity .sigma (2*γ+2) φ → GroupScottSentence G φ →
      ∃d:DifferenceFormula 0, d.AtLevel (2*γ+1) ∧ DifferenceScottSentence G d
/-- The same conclusion among ALL countable original-signature structures. -/
def finiteSocleTailRawSigmaLowering : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType], 0<γ →
    (∀x:G,∃k:ℕ,p^k • x=0) →
    Finite (pSocle p (⊤:AddSubgroup (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G))) →
    ∀φ:Formula 0, Complexity .sigma (2*γ+2) φ →
      RawScottSentence (RawGroupStructure.ofGroup G) φ →
      ∃d:DifferenceFormula 0, d.AtLevel (2*γ+1) ∧
        RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
end LogicLineages.ModelsAlgebra.PGroups.Targets
