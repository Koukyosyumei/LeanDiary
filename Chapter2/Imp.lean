import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
  This module defines a simple imperative language with a state modeled as a mapping
  from variable names to natural numbers. It includes basic commands (e.g., assignment,
  sequence, conditionals, and loops) and an inductively defined evaluation relation
  (`CEval`) that specifies the operational semantics for commands.
-/

namespace Imp

/--
A `State` is modeled as a function mapping variable names (as `String`s) to natural numbers.

This abstraction represents the memory or environment in which commands operate.
-/
def State := String -> ℕ

/--
Retrieves the value associated with a given variable in the state.

- Parameters:
  - `st`: The current state (an environment mapping variable names to natural numbers).
  - `x`: The variable name whose value is to be retrieved.
- Returns: The natural number value associated with `x` in `st`.
-/
def get (st: State) (x : String) : ℕ := st x

/--
Updates the state by assigning a new value to a specified variable.

- Parameters:
  - `st`: The current state.
  - `x`: The variable name to update.
  - `v`: The new natural number value to assign to variable `x`.
- Returns: A new state where variable `x` is updated to `v`, and all other variables remain unchanged.
-/
def set (st: State) (x : String) (v: ℕ) : State :=
  fun y => if y = x then v else st y

/--
Syntax of commands in our simple imperative language.

The inductive type `Command` represents the syntax with the following constructors:
- `skip`: A no-operation command.
- `assign`: Assigns a fixed natural number to a variable (`x := a`).
- `assignvar`: Assigns the value of one variable to another (`x := y`).
- `seq`: Sequential composition of two commands (`c1; c2`).
- `if_`: Conditional command that executes one of two branches based on a boolean condition.
- `while`: A while-loop that repeatedly executes a command as long as the condition is true.
-/
inductive Command: Type
| skip: Command                               -- nop
| assign (x : String) (a: ℕ) : Command        -- x := a
| assignvar (x: String) (y: String) : Command -- x := y
| seq (c1 c2 : Command) : Command                 -- c1; c2
| if_ (b : Bool) (c1 c2 : Command) : Command      -- if b then c1 else c2
| while (b : Bool) (c : Command) : Command        -- while b do c

-- inductive definitions in Lean come with an important implicit principle:
-- ** the only ways to construct proofs of the inductive relation are through its constructors.

/--
Inductive definition of arithmetic expressions (`AExp`).

Constructors:
- `const n`: a constant number
- `var x`: a variable
- `add`, `mul`, and `sub`: standard arithmetic operations.
-/
inductive AExp : Type
| const (n : ℕ) : AExp
| var (x : String) : AExp
| add (a₁ a₂ : AExp) : AExp
| mul (a₁ a₂ : AExp) : AExp
| sub (a₁ a₂ : AExp) : AExp

def AEval : State → AExp → ℕ
| _, .const n   => n
| st, .var x     => st x
| st, .add a₁ a₂ => AEval st a₁ + AEval st a₂
| st, .mul a₁ a₂ => AEval st a₁ * AEval st a₂
| st, .sub a₁ a₂ => AEval st a₁ - AEval st a₂

inductive BExp : Type
| btrue  : BExp
| bfalse : BExp
| eq (a₁ a₂ : AExp) : BExp
| le (a₁ a₂ : AExp) : BExp
| not (b : BExp) : BExp
| and (b₁ b₂ : BExp) : BExp

def BEval : State → BExp → Bool
| _, .btrue       => true
| _, .bfalse      => false
| st, .eq a1 a2    => AEval st a1 = AEval st a2
| st, .le a1 a2    => AEval st a1 ≤ AEval st a2
| st, .not b       => ¬(BEval st b)
| st, .and b1 b2   => (BEval st b1) && (BEval st b2)

/--
Inductive definition of command evaluation (`CEval`).

This inductive relation defines the operational semantics for commands, relating an
initial state `st` to a final state `st'` after executing a command.

Constructors:
- `skip`: Evaluating `skip` leaves the state unchanged.
- `assign`: Evaluating an assignment updates the state with the new value for the variable.
- `assignvar`: Evaluates an assignment where a variable is assigned the value of another variable.
- `seq`: Sequentially composes two command evaluations.
- `if_true`: Evaluates the "then" branch when the condition is true.
- `if_false`: Evaluates the "else" branch when the condition is false.
- `while_false`: A while-loop with a false condition terminates immediately without changing the state.
- `while_true`: A while-loop with a true condition evaluates its body and then continues looping.
-/
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
