module

public import LogicLineages.PersistentMarking.NumberedWindowOuterShapeProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowOuterShapeProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowOuterShape NumberedWindowOuterShapeProgramTargets
open NumberedWindowAddressAlgorithm (Address)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowScalarProgramProof (admittedPrim leastPrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)

private theorem nodesPrim : Primrec unpackNode := Primrec.encode_iff.mp
  ((Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

private theorem shapePrim (s : Settings) : Primrec (outerShape s) := by
  have payload : Primrec (fun a : Address => a.2.2) := Primrec.snd.comp Primrec.snd
  have admitted : Primrec (canonical s) :=
    Primrec.and.comp (admittedPrim s) (equalPrim.comp (leastPrim s) (Primrec.option_some.comp payload))
  have tag : Primrec (Prod.fst : Nat × List Nat → Nat) := Primrec.fst
  have code := (Primrec.option_map₁ tag).comp (nodesPrim.comp payload)
  have checked := Primrec.ite (Primrec.eq.comp admitted (Primrec.const true)) code (Primrec.const none)
  exact (Primrec.option_bind₁ checked).comp addressPrim

theorem exact_OuterShapeProgram : OuterShapeProgram := by
  intro s
  exact (Proof.unaryCorrespondence _).mp (Primrec.encode.comp (shapePrim s))

#print axioms exact_OuterShapeProgram

end LogicLineages.PersistentMarking.NumberedWindowOuterShapeProgramChecks
