module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation
open BalancedSyntax
abbrev AtomData:=Nat×Nat×Nat×List Nat
abbrev UpperData:=Nat×List Nat×List AtomData
abbrev CertificateData:=Nat×List Nat
abbrev Table:=BaseTermPrograms.Table
abbrev Input:=List Nat×Nat×Nat×Table
abbrev Result:=Nat×List Nat

def upperData (n:Nat):UpperData:=(Encodable.decode n).getD (0,[],[])
def certificateData (n:Nat):CertificateData:=(Encodable.decode n).getD (0,[])
def encodeAtom {k:Nat} (a:Nat×Atom k):AtomData:=
  (a.1,rawNoteEncode a.2.head.1,a.2.offset,List.ofFn a.2.factors)
def encodeSyntax:(Γ:List Nat)→Syntax Γ→Nat
  | [],E=>E.encode
  | _::_,E=>Encodable.encode (E.constant,List.ofFn E.outside,E.atoms.map encodeAtom)
def encodeCertificate:(Γ:List Nat)→Certificate Γ→Nat
  | [],_=>0
  | k::Γ,C=>Encodable.encode (encodeCertificate Γ C.1,List.ofFn (fun j:Fin k=>encodeSyntax Γ (C.2 j)))

/-- Complete numeric norm argument, including actual head norm and ALL basis
entries positively. Raw codes normalize missing factor entries to positive1. -/
noncomputable def atomInput (k:Nat) (a:AtomData) (v:Nat→Nat):Nat:=
  rawNormCode a.2.1+a.2.2.1+
    ((List.range k).map (fun j=>(a.2.2.2.getD j 0+1)*v j)).sum
noncomputable def valueAt (k:Nat) (E:UpperData) (v:Nat→Nat):Nat:=
  E.1+((List.range k).map (fun j=>E.2.1.getD j 0*v j)).sum+
    (E.2.2.map (fun a=>(a.1+1)*CommonHeadSmallFold.closedValueCode a.2.1 (atomInput k a v))).sum

def variablesAt (k:Nat) (E:UpperData) (v:Nat→List Nat):List Nat:=
  (List.range k).flatMap (fun j=>if E.2.1.getD j 0=0 then [] else v j)++
    E.2.2.flatMap (fun _=>(List.range k).flatMap v)

noncomputable def codeValue:List Nat→Nat→Nat→Table→Nat
  | [],_,E,table=>BaseTermPrograms.valueCode E table
  | k::Γ,C,E,table=>valueAt k (upperData E)
      (fun j=>codeValue Γ (certificateData C).1 ((certificateData C).2.getD j 0) table)
def codeVariables:List Nat→Nat→Nat→List Nat
  | [],_,E=>BaseTermPrograms.variablesCode E
  | k::Γ,C,E=>variablesAt k (upperData E)
      (fun j=>codeVariables Γ (certificateData C).1 ((certificateData C).2.getD j 0))

/-- Every actual numeric child drops ONE certificate shape layer. Closed BASE
computation is the ALREADY PROVED real program, not an oracle-valued leaf. -/
def children (p:Input):List Input:=
  match p.1 with
  | []=>[]
  | k::Γ=>(List.range k).map (fun j=>(Γ,(certificateData p.2.1).1,
      (certificateData p.2.1).2.getD j 0,p.2.2.2))
noncomputable def assemble (p:Input) (results:List Result):Result:=
  match p.1 with
  | []=>(BaseTermPrograms.valueCode p.2.2.1 p.2.2.2,BaseTermPrograms.variablesCode p.2.2.1)
  | k::_=>(valueAt k (upperData p.2.2.1) (fun j=>(results.getD j (0,[])).1),
      variablesAt k (upperData p.2.2.1) (fun j=>(results.getD j (0,[])).2))
noncomputable def joint (p:Input):Result:=
  (codeValue p.1 p.2.1 p.2.2.1 p.2.2.2,codeVariables p.1 p.2.1 p.2.2.1)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation
