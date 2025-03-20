import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Imp

-- A `State` can be modeled as a function mapping variable names
-- to values (e.g., natural numbers in this tutorial)
def State := String -> ℕ

-- Retrive the value of a variable in the State
def get (st: State) (x : String) : ℕ := st x

-- Update the State with a new value for a variable
def set (st: State) (x : String) (v: ℕ) : State :=
  fun y => if y = x then v else st y

-- Syntax of commands
inductive Command: Type
| skip: Command                               -- nop
| assign (x : String) (a: ℕ) : Command        -- x := a
| assignvar (x: String) (y: String) : Command -- x := y
| seq (c1 c2 : Command) : Command                 -- c1; c2
| if_ (b : Bool) (c1 c2 : Command) : Command      -- if b then c1 else c2
| while (b : Bool) (c : Command) : Command        -- while b do c

-- inductive definitions in Lean come with an important implicit principle:
-- ** the only ways to construct proofs of the inductive relation are through its constructors.

-- State transition
inductive CEval : Command -> State -> State -> Prop
| skip (st : State) :
    CEval .skip st st
| assign (st : State) (x : String) (n : ℕ) :
    CEval (.assign x n) st (set st x n)
| assignvar (st : State) (x : String) (y : String) :
    CEval (.assignvar x y) st (set st x (get st y))
| seq (c1 c2 : Command) (st st' st'' : State) :
    CEval c1 st st' → CEval c2 st' st'' → CEval (.seq c1 c2) st st''
| if_true (st st' : State) (c1 c2 : Command) :
    CEval c1 st st' → CEval (.if_ true c1 c2) st st'
| if_false (st st' : State) (b : Bool) (c1 c2 : Command) :
    CEval c2 st st' → CEval (.if_ false c1 c2) st st'
| while_false (st : State) (c : Command) :
    CEval (.while false c) st st
| while_true (st st' st'' : State) (c : Command) :
    CEval c st st' → CEval (.while true c) st' st'' → CEval (.while true c) st st''

end Imp
