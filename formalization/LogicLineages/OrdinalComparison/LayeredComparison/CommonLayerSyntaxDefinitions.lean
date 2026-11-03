module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax

/-- Exactly the source A_0 grammar, retaining the SAME raw variable indices.
Fixed numeral constants abbreviate finite0,1,+ terms. Phi is the actual f. -/
inductive BaseTerm where
  | numeral (n:Nat) | variable (i:Nat)
  | add (left right:BaseTerm) | phi (input:BaseTerm)

def BaseTerm.value (ν:Nat→Nat):BaseTerm→Nat
  | .numeral n=>n | .variable i=>ν i
  | .add E F=>E.value ν+F.value ν | .phi E=>Phi (E.value ν)
def BaseTerm.variables:BaseTerm→List Nat
  | .numeral _=>[] | .variable i=>[i]
  | .add E F=>E.variables++F.variables | .phi E=>E.variables

def BaseTerm.encode:BaseTerm→Nat
  | .numeral n=>4*n | .variable i=>4*i+1
  | .add E F=>4*Nat.pair E.encode F.encode+2 | .phi E=>4*E.encode+3

def BaseTerm.decode (n:Nat):BaseTerm:=
  if h0:n%4=0 then .numeral (n/4)
  else if h1:n%4=1 then .variable (n/4)
  else if h2:n%4=2 then .add (decode (n/4).unpair.1) (decode (n/4).unpair.2)
  else .phi (decode (n/4))
termination_by n
decreasing_by
  all_goals
    have hpos:0<n:=by omega
    have hd:n/4<n:=Nat.div_lt_self hpos (by decide)
    have hl:=Nat.unpair_left_le (n/4)
    have hr:=Nat.unpair_right_le (n/4)
    omega

/-- Literal source A_r syntax. At a positive level only a constant and one
common-head sum occur: there is NO open outside remainder. A stored coefficient
a represents positive a+1, giving all and only the source positive multiples. -/
def CommonSyntax:Nat→Type
  | 0=>BaseTerm
  | n+1=>Nat×List (Nat×CommonSyntax n)

def commonVariables:(n:Nat)→CommonSyntax n→List Nat
  | 0,E=>E.variables
  | n+1,E=>E.2.flatMap (fun a=>commonVariables n a.2)

/-- The actual published ordinal-head semantics at EVERY level and ONE raw
valuation. Finite head lists are top-to-bottom, so child certificates use tail. -/
noncomputable def commonValue:(Γ:List NONote)→CommonSyntax Γ.length→(Nat→Nat)→Nat
  | [],E,ν=>E.value ν
  | rho::Γ,E,ν=>E.1+(E.2.map (fun a=>(a.1+1)*actualHeadValue rho.1.repr
      (actualOrdinalNorm rho.1.repr+commonValue Γ a.2 ν))).sum

abbrev Payload:=Nat×List (Nat×Nat)
def payload (code:Nat):Payload:=(Encodable.decode code).getD (0,[])

def encodeCommon:(n:Nat)→CommonSyntax n→Nat
  | 0,E=>E.encode
  | n+1,E=>Encodable.encode (E.1,E.2.map (fun a=>(a.1,encodeCommon n a.2)))
def decodeCommon:(n:Nat)→Nat→CommonSyntax n
  | 0,code=>BaseTerm.decode code
  | n+1,code=>((payload code).1,(payload code).2.map (fun a=>(a.1,decodeCommon n a.2)))

/-- Genuine numeric source evaluation, using the ALREADY PROVED real closed
head algorithm. Every child shares the same original raw valuation. -/
noncomputable def codedValue:(Γ:List Nat)→Nat→(Nat→Nat)→Nat
  | [],code,ν=>(BaseTerm.decode code).value ν
  | head::Γ,code,ν=>(payload code).1+((payload code).2.map (fun a=>
      (a.1+1)*CommonHeadSmallFold.closedValueCode head
        (rawNormCode head+codedValue Γ a.2 ν))).sum

def genuineHeads (Γ:List NONote):Prop:=∀rho∈Γ,Order.IsSuccLimit rho.1.repr

def headCodes (Γ:List NONote):List Nat:=Γ.map (fun rho=>rawNoteEncode rho.1)
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntax
