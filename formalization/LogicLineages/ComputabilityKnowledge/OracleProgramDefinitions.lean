module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RecursiveIn

@[expose] public section
/-! Finite oracle-program syntax and actual semantics for arbitrary partial
oracles. This stage does not yet claim a computable universal decoder/evaluator
or define a jump. Numeric specialization is calibrated on valid encodings. -/
namespace LogicLineages.ComputabilityKnowledge.OracleProgram

inductive Program where
  | base : Nat.Partrec.Code → Program
  | query : Program
  | pair : Program → Program → Program
  | comp : Program → Program → Program
  | prec : Program → Program → Program
  | mu : Program → Program

def tagged (tag payload : Nat) : Nat := Nat.pair tag payload + 1

def encode : Program → Nat
  | .base c => tagged 0 (Encodable.encode c)
  | .query => tagged 1 0
  | .pair p q => tagged 2 (Nat.pair (encode p) (encode q))
  | .comp p q => tagged 3 (Nat.pair (encode p) (encode q))
  | .prec p q => tagged 4 (Nat.pair (encode p) (encode q))
  | .mu p => tagged 5 (encode p)

def eval (oracle : Nat → Part Nat) : Program → Nat → Part Nat
  | .base c => Nat.Partrec.Code.eval c
  | .query => oracle
  | .pair p q => fun n => Nat.pair <$> eval oracle p n <*> eval oracle q n
  | .comp p q => fun n => (eval oracle q n).bind (eval oracle p)
  | .prec p q => fun z =>
      let (a, n) := z.unpair
      Nat.rec (eval oracle p a)
        (fun j IH => IH.bind fun v => eval oracle q (Nat.pair a (Nat.pair j v))) n
  | .mu p => fun a => Nat.rfind fun n =>
      (eval oracle p (Nat.pair a n)).map (fun v => decide (v = 0))

def specialize (p : Program) (a : Nat) : Program :=
  .comp p (.pair (.base (Nat.Partrec.Code.const a)) (.base Nat.Partrec.Code.id))

/-- An actual primitive-recursive numeric constructor, defined on every
natural input; its valid-code semantics is proved separately. -/
def specializeIndex (programIndex parameter : Nat) : Nat :=
  tagged 3 (Nat.pair programIndex
    (tagged 2 (Nat.pair (tagged 0 (Encodable.encode (Nat.Partrec.Code.const parameter)))
      (tagged 0 (Encodable.encode Nat.Partrec.Code.id)))))

end LogicLineages.ComputabilityKnowledge.OracleProgram
