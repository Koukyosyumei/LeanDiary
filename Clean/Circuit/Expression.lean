import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget

variable {F: Type}

structure Variable (F : Type) where
  index: ℕ

instance : Repr (Variable F) where
  reprPrec v _ := "x" ++ repr v.index

inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F

export Expression (var const)

structure Environment (F : Type) where
  get: ℕ → F

namespace Expression
variable [Field F]

@[circuit_norm]
def eval (env: Environment F) : Expression F → F
  | var v => env.get v.index
  | const c => c
  | add x y => eval env x + eval env y
  | mul x y => eval env x * eval env y

def toString [Repr F] : Expression F → String
  | var v => "x" ++ reprStr v.index
  | const c => reprStr c
  | add x y => "()" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "()" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e

instance : Zero (Expression F) where
  zero := const 0

instance : One (Expression F) where
  one := const 1

instance : Add (Expression F) where
  add := add

instance : Neg (Expression F) where
  neg e := mul (const (-1)) e

instance : Sub (Expression F) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (Expression F) where
  mul := mul

instance: Coe F (Expression F) where
  coe f := const f

instance : Coe (Variable F) (Expression F) where
  coe x := var x

instance : HMul F (Expression F) (Expression F) where
  hMul := fun f e => mul f e

end Expression

instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env
