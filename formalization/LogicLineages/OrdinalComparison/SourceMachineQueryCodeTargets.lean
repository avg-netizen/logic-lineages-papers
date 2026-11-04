module
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Targets
open ExistentialPlan

def ExactPackaging : Prop :=
  (∀ q : Query,unpack (pack q)=some q) ∧
  (∀ b e,
    let q := SourceMachineConjunctionPlan.plan b e
    let es := (compile q).forest.map (fun p => (p.1.term,p.2.term))
    let a := SourceAggregateCompletion.aggregate es
    request b e=((compile q).context.length,SyntaxCode.encodeTerm a.2,SyntaxCode.encodeTerm a.1) ∧
    unpack (output b e)=some (request b e))

def GeneratedSourceValidity : Prop := ∀ b e,
  SyntaxCode.check (List.replicate (request b e).1 (SyntaxCode.typeCode Ty.ground)) (request b e).2.1=some (SyntaxCode.typeCode Ty.ground) ∧
  SyntaxCode.check (List.replicate (request b e).1 (SyntaxCode.typeCode Ty.ground)) (request b e).2.2=some (SyntaxCode.typeCode Ty.ground)

def UniformPrimitiveRecursive : Prop := Primrec pack ∧ Primrec unpack ∧ Primrec₂ request ∧ Primrec₂ output
end LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Targets
