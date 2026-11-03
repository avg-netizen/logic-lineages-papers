module
public import LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeProof
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice

theorem headBaseTypes : CoherentConstructorLatticeTargets.HeadBaseTypes := CoherentConstructorLatticeSupportProof.headBaseTypes

theorem inputRestrictionCalibration : CoherentConstructorLatticeTargets.InputRestrictionCalibration := by
  intro Symbol inst arity I f P Q h a
  refine ⟨fun _ => rfl,?_⟩
  intro τ b
  exact TypedExtraDownsetsProof.imageMembership h (a.2 τ).val b

theorem exhaustiveEnumeration : CoherentConstructorLatticeTargets.ExhaustiveEnumeration := by
  intro Symbol inst arity I M
  exact Finset.mem_univ M

theorem outputImage {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (S : Set (Constructors I)) (f : HeadIndex I) (τ : TypeIndex I)
    (P Q : World I) (h : Extends P Q) (a : Inputs I f P) :
    RecursiveNaturalDomains.weaken h '' ((fun M : Constructors I => M.val f τ P a) '' S)=
      (fun M : Constructors I => M.val f τ Q ((inputFamily I f).restrict h a)) '' S := by
  ext x
  constructor
  · rintro ⟨y,⟨M,hM,rfl⟩,rfl⟩
    exact ⟨M,hM,(M.property.2 f τ P Q h a).symm⟩
  · rintro ⟨M,hM,rfl⟩
    exact ⟨M.val f τ P a,⟨M,hM,rfl⟩,M.property.2 f τ P Q h a⟩

theorem supCoherent : CoherentConstructorLatticeTargets.SupCoherent := by
  intro Symbol inst arity I S
  constructor
  · intro f τ P a b hab
    apply ((RecursiveNaturalLatticesProof.bounds I τ.val).supSpec P _).2
    rintro x ⟨M,hM,rfl⟩
    exact le_trans (M.property.1 f τ P a b hab)
      (((RecursiveNaturalLatticesProof.bounds I τ.val).supSpec P _).1 ⟨M,hM,rfl⟩)
  · intro f τ P Q h a
    change (family I τ.val).restrict h ((RecursiveNaturalLatticesProof.bounds I τ.val).sup P _)=
      (RecursiveNaturalLatticesProof.bounds I τ.val).sup Q _
    rw [(RecursiveNaturalLatticesProof.bounds I τ.val).supRestriction]
    congr 1
    exact outputImage I S f τ P Q h a

theorem infCoherent : CoherentConstructorLatticeTargets.InfCoherent := by
  intro Symbol inst arity I S
  constructor
  · intro f τ P a b hab
    apply ((RecursiveNaturalLatticesProof.bounds I τ.val).infSpec P _).2
    rintro x ⟨M,hM,rfl⟩
    exact le_trans (((RecursiveNaturalLatticesProof.bounds I τ.val).infSpec P _).1 ⟨M,hM,rfl⟩)
      (M.property.1 f τ P a b hab)
  · intro f τ P Q h a
    change (family I τ.val).restrict h ((RecursiveNaturalLatticesProof.bounds I τ.val).inf P _)=
      (RecursiveNaturalLatticesProof.bounds I τ.val).inf Q _
    rw [(RecursiveNaturalLatticesProof.bounds I τ.val).infRestriction]
    congr 1
    exact outputImage I S f τ P Q h a

theorem supUniversal : CoherentConstructorLatticeTargets.SupUniversal := by
  intro Symbol inst arity I S
  constructor
  · rintro M ⟨N,hN,rfl⟩ f τ P a
    exact ((RecursiveNaturalLatticesProof.bounds I τ.val).supSpec P _).1 ⟨N,hN,rfl⟩
  · intro M hM f τ P a
    apply ((RecursiveNaturalLatticesProof.bounds I τ.val).supSpec P _).2
    rintro b ⟨N,hN,rfl⟩
    exact hM ⟨N,hN,rfl⟩ f τ P a

theorem infUniversal : CoherentConstructorLatticeTargets.InfUniversal := by
  intro Symbol inst arity I S
  constructor
  · rintro M ⟨N,hN,rfl⟩ f τ P a
    exact ((RecursiveNaturalLatticesProof.bounds I τ.val).infSpec P _).1 ⟨N,hN,rfl⟩
  · intro M hM f τ P a
    apply ((RecursiveNaturalLatticesProof.bounds I τ.val).infSpec P _).2
    rintro b ⟨N,hN,rfl⟩
    exact hM ⟨N,hN,rfl⟩ f τ P a

noncomputable def constructorSup {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (S : Set (Constructors I)) : Constructors I :=
  ⟨CoherentConstructorLattice.supRaw I S,supCoherent Symbol inferInstance arity I S⟩

theorem constructorSupSpec {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (S : Set (Constructors I)) : IsLUB S (constructorSup I S) := by
  have hu := supUniversal Symbol inferInstance arity I S
  constructor
  · intro M hM; exact hu.1 ⟨M,hM,rfl⟩
  · intro M hM
    apply hu.2
    rintro N ⟨L,hL,rfl⟩
    exact hM hL

noncomputable def actualCompleteLattice {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) : CompleteLattice (Constructors I) :=
  @completeLatticeOfSup (Constructors I) (constructorOrder I) ⟨constructorSup I⟩ (constructorSupSpec I)

theorem completeConstructors : CoherentConstructorLatticeTargets.CompleteConstructors := by
  intro Symbol inst arity I
  exact ⟨actualCompleteLattice I,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.CoherentConstructorLatticeProof
