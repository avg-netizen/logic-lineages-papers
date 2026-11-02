module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesProof
open Source Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer NaturalLayerBounds
open RecursiveNaturalDomains RecursiveNaturalLattices

/-- Independent mathematical induction discharges every lower bound supplier.
This data never enters the executable carrier/enumeration construction. -/
noncomputable def bounds {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) : Bounds (family I τ) :=
  Eq.mp (congrArg (fun F : Family I => Bounds F) (familyEquation I τ).symm)
    (NaturalLayerBoundsProof.layerBounds I τ (lower I τ) (fun υ h => bounds I υ))
termination_by typeSize τ
decreasing_by exact h

noncomputable def actualCompleteLattice {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : CompleteLattice (Value I τ P) :=
  @completeLatticeOfSup (Value I τ P) ((family I τ).order P)
    ⟨(bounds I τ).sup P⟩ ((bounds I τ).supSpec P)

theorem completeDomains : RecursiveNaturalLatticesTargets.CompleteDomains := by
  intro Symbol inst arity I τ P
  exact ⟨actualCompleteLattice I τ P,rfl⟩

theorem supremumExistence : RecursiveNaturalLatticesTargets.SupremumExistence := by
  intro Symbol inst arity I τ P S
  exact ⟨(bounds I τ).sup P S,(bounds I τ).supSpec P S⟩

theorem infimumExistence : RecursiveNaturalLatticesTargets.InfimumExistence := by
  intro Symbol inst arity I τ P S
  exact ⟨(bounds I τ).inf P S,(bounds I τ).infSpec P S⟩

theorem weakeningSuprema : RecursiveNaturalLatticesTargets.WeakeningSuprema := by
  intro Symbol inst arity I τ P Q h S a ha
  change IsLUB ((family I τ).restrict h '' S) ((family I τ).restrict h a)
  rw [ha.unique ((bounds I τ).supSpec P S),(bounds I τ).supRestriction]
  exact (bounds I τ).supSpec Q _

theorem weakeningInfima : RecursiveNaturalLatticesTargets.WeakeningInfima := by
  intro Symbol inst arity I τ P Q h S a ha
  change IsGLB ((family I τ).restrict h '' S) ((family I τ).restrict h a)
  rw [ha.unique ((bounds I τ).infSpec P S),(bounds I τ).infRestriction]
  exact (bounds I τ).infSpec Q _

theorem finiteSignatureEffectivity : RecursiveNaturalLatticesTargets.FiniteSignatureEffectivity := by
  intro n arity I τ P
  exact ⟨completeDomains (Fin n) inferInstance arity I τ P,
    fun a => RecursiveNaturalDomainsProof.exhaustiveEnumeration (Fin n) inferInstance arity I τ P a⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesProof
