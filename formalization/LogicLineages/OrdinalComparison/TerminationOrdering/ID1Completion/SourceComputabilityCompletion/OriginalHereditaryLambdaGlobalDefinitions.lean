module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobal
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The WHOLE existing effective leaf wrapper, in its literal order: spine,
then neutral, then constructor guards. The endpoint and window are arbitrary
original Programs. None of these three guards refers to oldStep. -/
def wrapper (endpoint : Program 6) (window : Program 1) (oldStep : Program 4) : Program 4 :=
  OriginalConstructorLeaf.refined
    (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))

/-- Hereditary refinement encloses the ENTIRE inner effective leaf. The
outer wrapper is then rebuilt by the unchanged final pipeline. Its child
guards must come from the inner wrapper at the SAME actual child, never from
native equality or merely from the old root's guards. -/
def closedLeaf (endpoint : Program 6) (window : Program 1) (oldStep : Program 4) : Program 4 :=
  wrapper endpoint window (OriginalHereditaryLambda.refined (wrapper endpoint window oldStep))

/-- The exact previously accepted final-tuple pipeline. In particular,
finalInputs does change oldStep by adding neutral and constructor guards;
its output is not merely the input spine-refined leaf. -/
def priorFinal (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalApplicationSidecar.finalInputs (OriginalSpineGuardLeaf.refineInputs p)

/-- The actual neutral guard's endpoint before the final variable-base
refinement. This Program depends only on the original base and window, not
on oldStep, and is unchanged by prepareInputs. -/
def endpoint (p : GlobalSourcePackage.Inputs) : Program 6 :=
  OriginalNeutralLeaf.endpoint
    (OriginalConstructorShape.refineInputs
      (OriginalFunctionNeutrality.refineInputs (OriginalApplicationSidecar.refineInputs p)))

/-- Only oldStep changes, before every source window and runtime Gamma.
The inner priorFinal leaf is formed from the ORIGINAL p, so this finite
construction is acyclic and supplies no internal-law or source-edge oracle. -/
def prepareInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := OriginalHereditaryLambda.refined (priorFinal p).oldStep }

/-- ONE effective final tuple for every retained consumer and the new
same-leaf child law. Both wrapper layers use the same original endpoint and
window Programs, while the final source construction is unchanged. -/
def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  priorFinal (prepareInputs p)

/-- Native calibration is kept separate from every internal graph theorem.
The inner effective leaf, prepared inputs and actual final tuple retain all
original calibration fields. Full-output equality includes malformed and
rejected four-input vectors, not just accepted or well-typed inputs. -/
def NativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (priorFinal p) ∧
    GlobalSourcePackage.InputsCalibrated n arity (prepareInputs p) ∧
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p) ∧
    (∀ v : List.Vector Nat 4,
      evaluate (priorFinal p).oldStep v = evaluate p.oldStep v ∧
        evaluate (prepareInputs p).oldStep v = evaluate p.oldStep v ∧
        evaluate (finalInputs p).oldStep v = evaluate p.oldStep v)

/-- Every field of the previously frozen package is retained at the SAME
prepared selection and hence the SAME effective final tuple. This includes
the complete original Package, child/suffix certificates, all preceding fold
and Object laws, neutral expansion and variable C at every finite type.
The only new internal conclusion is effective-leaf child elimination with
its exact prefix graph, four actual selectors and SAME final leaf graph.

This is NOT original ordinary/quotient source-edge body closure or lambda
computability. Internal source-validity descent, canonical-body coherence,
substitution, constructor/multiset cases and closed accessibility are not
asserted by this supporting conjunction. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  NativePreparation n arity p ∧
    OriginalChildCertificateGlobal.RetainedProperties n arity (prepareInputs p) ∧
    OriginalChildCertificateGlobal.CertificateProperties (prepareInputs p) ∧
    OriginalNeutralComputabilityGlobal.Properties n arity (prepareInputs p) ∧
    OriginalHereditaryLambda.InternalChildElimination (finalInputs p).oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobal
