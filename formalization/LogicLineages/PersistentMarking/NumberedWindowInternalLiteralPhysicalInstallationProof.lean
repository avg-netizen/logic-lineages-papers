module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalLiteralPresentationReinstallProof (exact_ReinstalledLiteralTupleAndJ)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open ConditionalJUnionTargets (CarrierUnion UnionClosure)

/-- Reinstall both literal multiset programs on a physically selected
ordinary address/application tuple. This keeps the actual context, type,
raw, least, scalar, and guarded application callbacks and constructs
the coordinate report afresh inside the new body. -/
theorem exact_ReinstallPhysicalLiteralMultisets (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i oldJ cv tv : Program 1) (oldD p₀ : Program 3)
    (raw : Program 5) (least : Program 3) (v : Inputs)
    (old : InstalledTupleAt xs s W i oldJ cv tv oldD p₀ raw least v) :
    let r := addressPositive cv tv raw least
    let j := jRaw i
    let d := dCore i r permutation
    InstalledTupleAt xs s W i j cv tv d p₀ raw least v ∧
      ∀ c, CarrierUnion (literalData i r) c functionalUnion ∧ UnionClosure (literalData i r) c functionalUnion := by
  let r := addressPositive cv tv raw least
  let j := jRaw i
  let d := dCore i r permutation
  obtain ⟨fresh,union⟩ := exact_ReinstalledLiteralTupleAndJ xs s W valid i oldJ r oldD v old.1
  exact ⟨⟨fresh,old.2.1,old.2.2.1,NumberedWindowInternalSparseTupleReportProof.installed i j cv tv d raw least⟩,
    union⟩

/-- Given the same original ValidWindow, there is a complete executable
tuple of original checker programs with both literal multiset components
installed, not merely separate witnesses for their evaluation. -/
theorem exact_ConcreteLiteralMultisetInstallation :
    ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (i cv tv : Program 1) (raw : Program 5) (least p₀ : Program 3) (v : Inputs),
        let r := addressPositive cv tv raw least
        let j := jRaw i
        let d := dCore i r permutation
        InstalledTupleAt xs s W i j cv tv d p₀ raw least v ∧
          ∀ c, CarrierUnion (literalData i r) c functionalUnion ∧
            UnionClosure (literalData i r) c functionalUnion := by
  intro xs s W valid
  obtain ⟨i,j,cv,tv,d,p₀,raw,least,v,old⟩ :=
    NumberedWindowInternalSparseTupleChecks.exact_ConcreteInstalledTuple xs s W valid
  exact ⟨i,cv,tv,raw,least,p₀,v,exact_ReinstallPhysicalLiteralMultisets xs s W
    valid i j cv tv d p₀ raw least v old⟩

#print axioms exact_ReinstallPhysicalLiteralMultisets
#print axioms exact_ConcreteLiteralMultisetInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof
