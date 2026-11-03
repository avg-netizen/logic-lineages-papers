module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison
open CommonLayerSyntax

/-- A numeral is a legal constant expression at EVERY source layer. -/
def constantCode (depth c:Nat):Nat:=
  if depth=0 then BaseTerm.encode (.numeral c)
  else Encodable.encode (c,([]:List (Nat×Nat)))

/-- Concatenate literal positive and negative occurrences. Repeated child codes
remain distinct occurrences until the proved signed row compiler cancels them. -/
def signedAtoms (E F:Nat):List (Int×Nat):=
  (payload E).2.map (fun a=>((a.1+1:Int),a.2))++
  (payload F).2.map (fun a=>(-((a.1+1:Int)),a.2))
def rowCoefficients (E F:Nat):List Int:=(signedAtoms E F).map Prod.fst
def rowArguments (E F:Nat):List Nat:=(signedAtoms E F).map Prod.snd
def rowConstant (E F:Nat):Int:=((payload E).1:Int)-((payload F).1:Int)

/-- The base case uses ACTUAL original BASE terms, under ONE raw valuation. -/
def baseCompare (E F:Nat) (desired:Int):BaseFormula.Formula:=
  if desired=0 then .equal (BaseTerm.decode E) (BaseTerm.decode F)
  else if desired= -1 then .less (BaseTerm.decode E) (BaseTerm.decode F)
  else if desired=1 then .less (BaseTerm.decode F) (BaseTerm.decode E)
  else .falsity

/-- Every guard compares complete actual arguments N+child. Equality and order
cancel the SAME N; a small bound becomes a recursive comparison with the exact
constant c-N. Boolean structure and the original occurrence indices survive. -/
def translateGuard (lower:Nat→Nat→Int→BaseFormula.Formula)
    (depth N:Nat) (args:List Nat):CommonHeadLargeGuards.Formula→BaseFormula.Formula
  | .truth=>.truth | .falsity=>.falsity
  | .eq i j=>lower (args.getD i (constantCode depth 0)) (args.getD j (constantCode depth 0)) 0
  | .lt i j=>lower (args.getD i (constantCode depth 0)) (args.getD j (constantCode depth 0)) (-1)
  | .bound c i=>if c≤N then .truth else
      .negative (lower (args.getD i (constantCode depth 0)) (constantCode depth (c-N)) (-1))
  | .neg p=>.negative (translateGuard lower depth N args p)
  | .conj p q=>.conjunction (translateGuard lower depth N args p) (translateGuard lower depth N args q)
  | .disj p q=>.disjunction (translateGuard lower depth N args p) (translateGuard lower depth N args q)

/-- Literal terminating layer induction. The recursion drops exactly ONE fixed
head and invokes the already proved whole signed row compiler at that layer. -/
noncomputable def compile:List Nat→Nat→Nat→Int→BaseFormula.Formula
  | [],E,F,desired=>baseCompare E F desired
  | h::Γ,E,F,desired=>
      translateGuard (compile Γ) Γ.length (rawNormCode h) (rowArguments E F)
        (CommonHeadCompiler.compile h (rowConstant E F) (rowCoefficients E F) desired)

def codedVariables (depth code:Nat):List Nat:=commonVariables depth (decodeCommon depth code)

noncomputable def compileCode (Γ:List Nat) (E F:Nat) (desired:Int):List CommonHeadCompiler.Instruction:=
  (compile Γ E F desired).encode
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison
